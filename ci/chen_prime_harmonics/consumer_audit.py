#!/usr/bin/env python3
"""Owned source/artifact/log gates. Never fetch or execute Lean or foreign code."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys
sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
PLAN = json.loads((HERE / "closure.json").read_text())
BASE_PATH = HERE.parent / "external_bv"
# These are real checks, deliberately not Python assertions removable by -O.
for filename, expected in PLAN["baseAuditFileSha256"].items():
    path = BASE_PATH / filename
    if not path.is_file() or path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit("Pinned inherited audit/support file changed: " + filename)
spec = importlib.util.spec_from_file_location("reviewed_base_gate", BASE_PATH / "cold_source_audit.py")
BASE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(BASE)
FOREIGN = BASE.REVIEW
need, blob, scrub, imports, write = BASE.need, BASE.blob, BASE.scrub, BASE.imports, BASE.write
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TRUSTED_PREFIXES = {"Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq",
                    "Plausible", "ProofWidgets", "LeanSearchClient", "ImportGraph", "Cli", "Lake"}
RUNTIME = re.compile(r"#eval|\brun_cmd\b|\brun_elab\b|\binitialize\b|\bbuiltin_initialize\b|IO\.(?:Process|FS)")
ESCAPES = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular(path, root):
    need(path.is_file() and not path.is_symlink(), "Missing/nonregular file: " + str(path))
    need(root == path or root in path.parents, "File outside selected root: " + str(path))
    need(not any(p.is_symlink() for p in path.parents if p == root or root in p.parents),
         "Symlink parent: " + str(path))


def safe_relative(value):
    p = Path(value)
    need(not p.is_absolute() and ".." not in p.parts and str(p) != ".", "Unsafe manifest path: " + value)
    return p


def module_set(kind):
    return {r["module"] for r in PLAN["sources"] if r["kind"] == kind}


def check_file(path, row, root):
    regular(path, root)
    need(sha256(path) == row["sha256"] and blob(path) == row["gitBlob"], "Pinned source changed: " + str(path))
    need(path.stat().st_size == row["bytes"], "Source byte count changed: " + str(path))
    need(imports(path.read_text()) == row["imports"], "Source import edges changed: " + str(path))


def validate_graph():
    need(len(FOREIGN["modules"]) == 270 and len(FOREIGN["architectModules"]) == 9,
         "Wrong immutable ordinary270 baseline")
    need(sha256(BASE_PATH / "closure.json") == PLAN["foreignClosureSha256"], "Ordinary270 manifest changed")
    need(PLAN["counts"] == {"owned-proof": 49, "supplier": 66, "architect": 9, "audit-tool": 1},
         "Wrong exact harmonic source counts")
    for kind, count in PLAN["counts"].items():
        need(len(module_set(kind)) == count, "Wrong selected count: " + kind)
    known = {r["module"]: r for r in PLAN["sources"]}
    need(len(known) == len(PLAN["sources"]) == 125, "Duplicate/wrong full source count")
    arch = {r["module"]: r["sha"] for r in FOREIGN["architectModules"]}
    for row in PLAN["sources"]:
        safe_relative(row["destination"])
        if "source" in row:
            safe_relative(row["source"])
        m = row["module"]
        if row["kind"] == "supplier":
            need(m in FOREIGN["modules"] and row["gitBlob"] == FOREIGN["gitBlobs"][m],
                 "Supplier outside immutable ordinary270: " + m)
            need(row["imports"] == FOREIGN["imports"][m], "Changed supplier import graph: " + m)
        elif row["kind"] == "architect":
            need(arch.get(m) == row["gitBlob"], "Changed Architect source: " + m)
    seen, active, topo, boundary = set(), set(), [], set()
    def visit(m):
        if m in seen:
            return
        need(m not in active, "Import cycle: " + m)
        active.add(m)
        for dep in known[m]["imports"]:
            if dep in known:
                visit(dep)
            else:
                need(dep.split(".")[0] in TRUSTED_PREFIXES, "Unapproved import: " + dep)
                boundary.add(dep)
        active.remove(m)
        seen.add(m)
        topo.append(m)
    visit("ChenPrimeHarmonicsProbe")
    need(seen == set(known) and topo == PLAN["topologicalOrder"], "Extra/missing/reordered selected closure")
    need(sorted(boundary) == PLAN["boundaryImports"], "Changed trusted import boundary")
    need(PLAN["auditedModules"] == topo[:-1] and len(topo[:-1]) == PLAN["proofModuleCount"] == 124,
         "Incomplete exact proof-origin scope")
    need(PLAN["allowEmptyDeclarationModules"] == ["Architect"], "Changed empty-module exception")
    need(PLAN["ownedBuildOrder"] == [m for m in topo if known[m]["kind"] in {"owned-proof", "audit-tool"}]
         and len(PLAN["ownedBuildOrder"]) == PLAN["ownedBuildModuleCount"] == 50,
         "Wrong exact owned compile order")
    need(PLAN["supplierRoots"] == ["MathlibNt.SieveTheory.Arithmetic.MertensTheorem"],
         "Wrong harmonic supplier root")
    need(PLAN["requiredActualRoots"] == ["ImbalancedChen.ChenPrimeHarmonicAdapter",
         "ImbalancedChen.ChenQuotientMovingPrimeAdapter", "ImbalancedChen.ChenPairHarmonicLimit"],
         "Changed actual consumer roots")
    need(known["ChenPrimeHarmonicsProbe"]["imports"] == PLAN["requiredActualRoots"] + ["Lean.Util.CollectAxioms"],
         "Changed audit probe imports")
    for m, expected in PLAN["reviewedConsumerPins"].items():
        need(known[m]["sha256"] == expected, "Changed reviewed consumer input pin: " + m)
    need(known["ImbalancedChen.ChenPrimeHarmonicFinite"]["sha256"] ==
         "8b7b1d6d7b7b9847ade96917beac79be4d695c2444a27c38b3f9e1b878174f38",
         "Superseded finite one-prime source selected")
    need(len(topo) == len(set(topo)) == PLAN["replayModuleCount"] == 125, "Wrong replay scope")
    need(PLAN["batchSize"] == 12 and PLAN["replayBatchCount"] == 11, "Wrong replay batching")


def validate_owned(consumer):
    validate_graph()
    for row in PLAN["consumerConfigSnapshots"] + [PLAN["license"]]:
        p = consumer / safe_relative(row["source"])
        regular(p, consumer)
        need(sha256(p) == row["sha256"] and blob(p) == row["gitBlob"], "Pinned config/license changed")
    for row in PLAN["sources"]:
        if "source" not in row:
            continue
        path = consumer / row["source"]
        check_file(path, row, consumer)
        if row["kind"] != "audit-tool":
            code = scrub(path.read_text())
            need(not ESCAPES.search(code) and not RUNTIME.search(code), "Unreviewed owned proof/runtime token")


def source_gate(consumer, root, out):
    validate_owned(consumer)
    runtime, arch_tokens, hashes = [], [], {}
    for row in PLAN["sources"]:
        if row["kind"] not in {"supplier", "architect"}:
            continue
        path = root / row["destination"]
        check_file(path, row, root)
        hashes[row["module"]] = row["gitBlob"]
        code = scrub(path.read_text())
        matches = [{"module": row["module"], "token": m.group(), "line": code[:m.start()].count("\n") + 1}
                   for m in ESCAPES.finditer(code)]
        if row["kind"] == "supplier":
            need(not matches, "Forbidden supplier proof token")
        else:
            arch_tokens.extend(matches)
        runtime.extend({"module": row["module"], "token": m.group(), "line": code[:m.start()].count("\n") + 1}
                       for m in RUNTIME.finditer(code))
    need(runtime == PLAN["runtimeEntries"], "Changed reviewed runtime entry points")
    need(arch_tokens == PLAN["architectReviewedTokens"], "Changed reviewed Architect tooling tokens")
    write(out, "harmonic-source-audit.json", {"supplier": 66, "architect": 9, "ownedProof": 49,
         "auditProbe": 1, "ordinary270Subset": True, "gitBlobs": hashes,
         "runtimeEntries": runtime, "architectReviewedTokens": arch_tokens, "issues": []})
    print("PASS: exact 66 ordinary270 + 9 Architect + 49 owned proof + 1 probe source pins")


def stage(consumer, root, out):
    source_gate(consumer, root, out)
    selected = [r for r in PLAN["sources"] if "source" in r]
    for row in selected:
        p = root / row["destination"]
        need(not p.exists() and not p.is_symlink(), "Staging collision: " + str(p))
        need(not any(q.is_symlink() for q in p.parents if q == root or root in q.parents), "Symlink staging parent")
    for row in selected:
        p = root / row["destination"]
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(consumer / row["source"], p)
    shutil.copyfile(HERE / "closure.json", out / "harmonic-closure.json")
    (out / "owned-build-modules.txt").write_text("\n".join(PLAN["ownedBuildOrder"]) + "\n")
    print("STAGED: 49 exact owned proof sources + 1 audit probe; no Lake configuration changes")


def compiled_set(directory):
    files = list(directory.rglob("*.olean")) if directory.exists() else []
    for p in files:
        regular(p, directory)
    return {str(p.relative_to(directory))[:-6].replace("/", ".") for p in files}


def artifact_gate(root, out, owned):
    gate = json.loads((out / "cold-gate.json").read_text())
    need(gate["external_artifacts_before"] == [], "Nonempty cold prebuild gate")
    root_expected = module_set("supplier")
    kinds = {"supplier", "architect"}
    if owned:
        root_expected |= module_set("owned-proof") | module_set("audit-tool")
        kinds |= {"owned-proof", "audit-tool"}
    main = root / ".lake/build/lib/lean"
    arch = root / ".lake/packages/LeanArchitect/.lake/build/lib/lean"
    need(compiled_set(main) == root_expected, "Unexpected/missing root-project compiled module")
    need(compiled_set(arch) == module_set("architect"), "Unexpected/missing Architect compiled module")
    artifacts = []
    for row in PLAN["sources"]:
        if row["kind"] not in kinds:
            continue
        directory = arch if row["kind"] == "architect" else main
        p = directory / (row["module"].replace(".", "/") + ".olean")
        regular(p, directory)
        need(p.stat().st_mtime_ns >= gate["time_ns"], "Artifact predates cold gate: " + row["module"])
        artifacts.append({"module": row["module"], "sha256": sha256(p),
                          "bytes": p.stat().st_size, "mtime_ns": p.stat().st_mtime_ns})
    write(out, "harmonic-built-artifacts.json" if owned else "harmonic-supplier-built-artifacts.json", artifacts)


def after_supplier(consumer, root, out):
    source_gate(consumer, root, out)
    artifact_gate(root, out, False)
    print("PASS: exactly 66+9 fresh foreign oleans, no extra compiled custom module")


def axiom_gate(out):
    text = (out / "chen-prime-harmonics-build.log").read_text()
    need("sorryAx" not in text, "sorryAx in harmonic audit output")
    loaded = re.findall(r"\bHARMONIC_IMPORTED_MODULE (\S+)$", text, re.M)
    need(len(loaded) == len(set(loaded)), "Duplicate loaded-module report")
    audited = set(PLAN["auditedModules"])
    custom = {m for m in loaded if m.split(".")[0] not in TRUSTED_PREFIXES}
    need(custom == audited, "Loaded custom graph differs from exact 49+66+9 origins")
    need(set(PLAN["requiredActualRoots"]) <= set(loaded), "Missing actual arithmetic consumer root")
    rows = re.findall(r"\bHARMONIC_MODULE_AUDIT (\S+) declarations=([0-9]+)$", text, re.M)
    need(len(rows) == len({m for m, _ in rows}) == len(audited) and {m for m, _ in rows} == audited,
         "Incomplete/duplicate exact module-origin audit coverage")
    counts = {m: int(n) for m, n in rows}
    for m, n in counts.items():
        need(n > 0 or m in PLAN["allowEmptyDeclarationModules"], "Missing origin declarations: " + m)
    passes = re.findall(r"\bHARMONIC_AXIOM_AUDIT_PASS declarations=([1-9][0-9]*) modules=124$", text, re.M)
    need(len(passes) == 1 and int(passes[0]) == sum(counts.values()), "Missing/inconsistent full axiom audit")
    named = {}
    for name in PLAN["namedAxiomReports"]:
        hits = re.findall(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", text)
        empty = re.findall(r"'" + re.escape(name) + r"' does not depend on any axioms", text)
        need(len(hits) + len(empty) == 1, "Missing/duplicate named axiom report: " + name)
        axioms = {x.strip() for x in hits[0].split(",") if x.strip()} if hits else set()
        need(axioms <= ALLOWED_AXIOMS, "Forbidden named axiom: " + name)
        named[name] = sorted(axioms)
    write(out, "harmonic-loaded-imports.json", sorted(loaded))
    write(out, "harmonic-module-origin-axiom-audit.json", {"declarationsByModule": counts,
        "totalDeclarations": sum(counts.values()), "namedReports": named, "allowedAxioms": sorted(ALLOWED_AXIOMS)})


def after(consumer, root, out):
    source_gate(consumer, root, out)
    for row in PLAN["sources"]:
        if "source" in row:
            check_file(root / row["destination"], row, root)
    artifact_gate(root, out, True)
    axiom_gate(out)
    (out / "replay-modules.txt").write_text("\n".join(PLAN["topologicalOrder"]) + "\n")
    print("PASS: all 124 exact custom origins axiom-audited; all 125 fresh explicit replay targets")


def replay_gate(out):
    expected = PLAN["topologicalOrder"]
    need((out / "replay-modules.txt").read_text().splitlines() == expected, "Changed exact replay target file")
    batches = [expected[i:i+12] for i in range(0, len(expected), 12)]
    need((out / "replay-batches.txt").read_text().splitlines() == [" ".join(b) for b in batches],
         "Missing/reordered/duplicate replay batch input")
    log = (out / "kernel-replay.log").read_text()
    starts = list(re.finditer(r"^HARMONIC_REPLAY_BEGIN ([1-9][0-9]*) (.+)$", log, re.M))
    ends = list(re.finditer(r"^HARMONIC_REPLAY_END ([1-9][0-9]*) exit=([0-9]+)$", log, re.M))
    need(len(starts) == len(ends) == len(batches) == 11, "Incomplete/duplicate replay framing")
    explicit_all, records = set(), []
    for i, (start, end, batch) in enumerate(zip(starts, ends, batches), 1):
        need(int(start[1]) == int(end[1]) == i and end[2] == "0", "Wrong batch number/exit")
        need(start[2].split() == batch, "Requested ordered replay batch differs")
        need(start.end() < end.start(), "Reversed replay markers")
        need(i == len(batches) or end.end() < starts[i].start(), "Overlapping replay batches")
        chunk = log[start.end():end.start()]
        need(re.findall(r'^\s*Command being timed: "(.+)"$', chunk, re.M) ==
             ["lake env leanchecker --verbose " + " ".join(batch)], "Wrong/missing checker command")
        need(re.findall(r"^\s*Exit status: ([0-9]+)$", chunk, re.M) == ["0"], "Wrong/missing checker exit")
        explicit = re.findall(r"^replaying (\S+)$", chunk, re.M)
        need(set(batch) <= set(explicit), "Requested module not explicitly replayed")
        need(set(explicit) <= set(expected), "Unexpected explicit replay module")
        explicit_all.update(explicit)
        records.append({"index": i, "requested": batch, "explicit": explicit, "exit": 0})
    need(explicit_all == set(expected), "Incomplete explicit replay target coverage")
    outside = log
    for start, end in reversed(list(zip(starts, ends))):
        outside = outside[:start.start()] + outside[end.end():]
    need(not re.search(r"^replaying |Command being timed:|Exit status:|HARMONIC_REPLAY_", outside, re.M),
         "Unframed replay evidence")
    write(out, "harmonic-verified-replay-batches.json", records)
    write(out, "harmonic-replay-verification.json", {"targets": 125, "batches": 11,
        "everyBatchExit0": True, "everyBatchCommandMatches": True, "allTargetsExplicitlyReplayed": True,
        "requiredActualRoots": PLAN["requiredActualRoots"], "fullLogSha256": sha256(out / "kernel-replay.log")})
    print("PASS: all 125 exact ordered targets explicitly kernel-replayed in 11 complete successful batches")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=["manifest", "sources", "stage", "after-supplier", "after", "replay"])
    p.add_argument("consumer", type=Path)
    p.add_argument("root", type=Path)
    p.add_argument("out", type=Path)
    args = p.parse_args()
    if args.mode == "manifest":
        validate_owned(args.consumer)
        print("PASS: immutable support and all owned source/config/license pins before dependency execution")
    elif args.mode == "replay":
        validate_owned(args.consumer)
        replay_gate(args.out)
    else:
        {"sources": source_gate, "stage": stage, "after-supplier": after_supplier, "after": after}[args.mode](
            args.consumer, args.root, args.out)
