"""Compile the fresh classical support closure and replay its two selected modules."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from verify_p34_cusp_normalization import (ALLOWED, CONFIG_SHA256, FORBIDDEN,
                                            validate_import_paths, validate_inventory)
from verify_variable_envelope_boxes import lean_code

ROOT = Path(__file__).resolve().parents[1]
BASE = "2110a6170401bfc0dcaee46f689ee5f705507683"
NEW = "ImbalancedChen.Part3OriginalClassicalCommonPoissonSupport"
REUSED = "ImbalancedChen.Part3OriginalCommonPoissonLanesCore"
TARGETS = (NEW, REUSED)
NAMESPACE = "ImbalancedChen.Part3.OriginalClassicalSpectralSupports20261102"
PUBLIC = ("classicalMScale", "classicalMScale_bounds", "commonMBlock_classical_support",
          "commonPoissonCompleted_classical_support")
DOC = Path("docs/part3-distribution/p34-classical-support-20261127")
CLOSURE = DOC / "PROJECT_SOURCE_CLOSURE.json"
INTAKE = DOC / "SOURCE_INTAKE.json"
AUDIT = Path("verification/P34ClassicalSupportAudit.lean")
BOUNDARY = Path("verification/P34ClassicalSupportBoundary.lean")
TEMPLATE = Path("verification/P34FrickePhaseAudit.lean")
OBJECTS = Path(".lake/build/lib/lean")
SEGMENT = "019b07836c4dbecfe7af2f4f1f61b3bd15dfa0978f5c550c0e63e794fa74ba57"
CORE_HASH = "39b891589946ae686b9944af30847e948df47a1ea0d231f8e7504724e93c9055"
LEAN_COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
TOOL_HASHES = {"lean": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
               "leanchecker": "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"}
EXTERNAL = {"Mathlib", "Lean", "Std", "Init"}
GOLDBACH_MODULE = "MathlibNt.SieveTheory.LiLiuPanBoundedAggregate"
PARTS = ("", ".server", ".private")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_file(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


# Ordinary import parser from the accepted P3.1 continuation gate.
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def source_imports(text: str, source: str) -> tuple[str, ...]:
    """Read the closure's ordinary import headers with the existing Lean lexer.

    Unsupported header syntax fails closed instead of silently dropping an edge.
    Comments and string contents are removed by the same lexer as the source gate.
    """
    imports: list[str] = []
    for line in lean_code(text).splitlines():
        words = line.split()
        if not words:
            continue
        if words[0] != "import":
            if (words[0] in {"prelude", "module", "public", "private", "meta", "all"}
                    or (len(words) == 1 and MODULE_NAME.fullmatch(words[0])
                        and words[0] not in {"section", "noncomputable", "mutual"})):
                raise RuntimeError("Unsupported Lean import header: " + source)
            break
        names = words[1:]
        if not names or any(not MODULE_NAME.fullmatch(name)
                            or name in {"import", "all", "public", "meta", "prelude", "module"}
                            for name in names):
            raise RuntimeError("Unsupported Lean import header: " + source)
        imports.extend(names)
    if len(imports) != len(set(imports)):
        raise RuntimeError("Duplicate Lean import: " + source)
    return tuple(imports)


def render_audit(modules: tuple[str, ...]) -> str:
    """Reuse the entire serialized-inventory and transitive-axiom audit body."""
    source = (ROOT / TEMPLATE).read_text()
    body = source[source.index("\n/-!"):]
    selector = "  let modules := #[" + ",\n    ".join(chr(96) + m for m in modules) + "]\n"
    body, count = re.subn(
        r"  let modules := #\[.*?\]\n(?=  let allowed :=)",
        lambda _: selector, body, flags=re.S)
    if count != 1:
        raise RuntimeError("Could not identify the original audit's single module selector")
    return "\n".join("import " + m for m in modules) + "\nimport Lean.Util.CollectAxioms\n" + body


def module_file(module, suffix):
    return Path(module.replace(".", "/") + suffix)


def project_closure(root, targets=TARGETS):
    sources = {}
    visiting = set()
    external = set()

    def visit(module):
        if module in sources:
            return
        if module in visiting:
            raise RuntimeError("Cyclic import: " + module)
        relative = module_file(module, ".lean")
        path = root / relative
        if path.resolve() != path or not path.is_file():
            raise RuntimeError("Missing or redirected project source: " + str(relative))
        visiting.add(module)
        imports = source_imports(path.read_text(), str(relative))
        for name in imports:
            prefix = name.split(".")[0]
            if prefix == "ImbalancedChen":
                visit(name)
            elif ((prefix in EXTERNAL or name == GOLDBACH_MODULE)
                  and not (root / module_file(name, ".lean")).exists()):
                external.add(name)
            else:
                raise RuntimeError("Unrecognized or shadowed external import: " + name)
        visiting.remove(module)
        sources[module] = {"module": module, "path": relative.as_posix(),
                           "imports": list(imports), "sha256": sha256(path)}

    for module in targets:
        visit(module)
    return {"targets": list(targets), "project_module_count": len(sources),
            "project_sources": list(sources.values()), "topological_order": list(sources),
            "external_imports": sorted(external), "full_external_kernel_replay_claimed": False}


def validate_segment(source, intake):
    lo, hi = intake["consumer"]["segment_lines_inclusive"]
    segment = b"".join(source.splitlines(keepends=True)[lo - 1:hi])
    if (lo < 1 or hi < lo or hashlib.sha256(segment).hexdigest() != SEGMENT
            or intake["donor"]["segment"]["sha256"] != SEGMENT):
        raise RuntimeError("Original classical support segment differs")


def verify_sources():
    closure = project_closure(ROOT)
    if closure["project_module_count"] != 57 or json.loads((ROOT / CLOSURE).read_text()) != closure:
        raise RuntimeError("Committed project closure differs from recomputation")
    intake = json.loads((ROOT / INTAKE).read_text())
    consumer = ROOT / module_file(NEW, ".lean")
    validate_segment(consumer.read_bytes(), intake)
    if sha256(consumer) != intake["consumer"]["sha256"] or sha256(ROOT / module_file(REUSED, ".lean")) != CORE_HASH:
        raise RuntimeError("Consumer or recovered P3.1 source differs")
    comparison = intake["provider_reuse"]["base_comparison"]
    for label in ("distribution_targets", "physical_poisson"):
        provider = comparison[label]
        if sha256(ROOT / provider["path"]) != provider["retained_sha256"]:
            raise RuntimeError("Edit-base provider changed: " + provider["path"])
    if not set(comparison["distribution_targets"]["retained_split_providers"]) <= set(closure["topological_order"]):
        raise RuntimeError("Missing split declaration owner")
    if (ROOT / AUDIT).read_text() != render_audit(TARGETS):
        raise RuntimeError("Owner audit differs from baseline template")
    files = [Path(r["path"]) for r in closure["project_sources"]]
    for path in [*files, AUDIT, BOUNDARY]:
        if FORBIDDEN.search(lean_code((ROOT / path).read_text())):
            raise RuntimeError("Forbidden proof escape: " + str(path))
    files += [AUDIT, BOUNDARY, TEMPLATE, CLOSURE, INTAKE, Path(__file__).resolve().relative_to(ROOT),
              Path("verification/verify_variable_envelope_boxes.py"),
              Path("verification/verify_p34_cusp_normalization.py"), *map(Path, CONFIG_SHA256)]
    hashes = {str(path): sha256(ROOT / path) for path in files}
    if any(hashes[k] != v for k, v in CONFIG_SHA256.items()):
        raise RuntimeError("Pinned source configuration differs")
    return closure, hashes


def expected_deps(source, parsed, fresh, objroot, packages, syslib):
    roots = (objroot, *packages.values(), syslib)
    actual = validate_import_paths(parsed, fresh, (*packages.values(), syslib))
    expected = set()
    for module in {"Init", *source_imports(source.read_text(), str(source))}:
        prefix = module.split(".")[0]
        if prefix == "ImbalancedChen":
            owner = objroot
        elif module == GOLDBACH_MODULE:
            owner = packages["goldbach"]
        elif prefix == "Mathlib":
            owner = packages["mathlib"]
        elif prefix in EXTERNAL:
            owner = syslib
        else:
            raise RuntimeError("Unrecognized external module: " + module)
        rel = module_file(module, ".olean")
        path = owner / rel
        matches = [root / rel for root in roots if (root / rel).exists()]
        if matches != [path] or path.resolve() != path:
            raise RuntimeError("Missing, redirected, or shadowed module: " + module)
        expected.add(str(path))
    if set(actual) != expected:
        raise RuntimeError("Lean parsed import set differs for " + str(source))
    return actual


def bind_object(module, objroot, external):
    relative = module_file(module, ".olean")
    path = objroot / relative
    if not path.is_file() or any((root / relative).exists() for root in external):
        raise RuntimeError("Missing or shadowed compiled project module: " + module)
    parts = {}
    for suffix in PARTS:
        part = Path(str(path) + suffix)
        if part.exists() or part.is_symlink():
            if not part.is_file() or part.resolve() != part:
                raise RuntimeError("Invalid project object part: " + str(part))
            parts[str(part.relative_to(objroot))] = sha256(part)
    return {"resolved_olean": str(path), "parts": parts}


def checkout_object_parts():
    """Ignore external package installations, which are separate source checkouts."""
    found = []
    for folder, dirs, files in os.walk(ROOT):
        parent = Path(folder)
        dirs[:] = [d for d in dirs if d != ".git" and parent / d != ROOT / ".lake/packages"]
        found.extend(str((parent / f).relative_to(ROOT)) for f in files if
                     f.endswith((".olean", ".olean.server", ".olean.private")))
    return sorted(found)


def external_object_parts(path):
    parts = {}
    for suffix in PARTS:
        part = Path(str(path) + suffix)
        if part.exists() or part.is_symlink():
            if not part.is_file() or part.resolve() != part:
                raise RuntimeError("Invalid directly imported external object part: " + str(part))
            parts[str(part)] = sha256(part)
    return parts


def object_parts(objroot):
    return {str(path.relative_to(objroot)) for path in objroot.rglob("*.olean*")}


def now():
    return datetime.now(timezone.utc).isoformat()


class Receipt:
    def __init__(self, out, head):
        self.out = out
        self.data = {"status": "RUNNING", "started_utc": now(), "baseline_commit": BASE,
                     "expected_head": head, "new_module": NEW, "reused_integration_module": REUSED,
                     "replay_targets": list(TARGETS), "full_external_kernel_replay_claimed": False,
                     "trust_mode": "NORMAL_IMPORTED_ENVIRONMENT_TRUST",
                     "allowed_transitive_axioms": sorted(ALLOWED), "stages": []}
        self.env = dict(os.environ)
        self.save()

    def save(self):
        tmp = self.out / "report.json.tmp"
        json_file(tmp, self.data)
        tmp.replace(self.out / "report.json")

    def run(self, name, *args):
        command = list(map(str, args))
        stage = {"name": name, "command": command, "started_utc": now(), "exit_code": None}
        self.data["stages"].append(stage)
        self.save()
        log = self.out / (name + ".log")
        tick = time.monotonic()
        try:
            with log.open("w") as stream:
                stream.write("command=" + json.dumps(command) + "\n")
                stream.flush()
                result = subprocess.run(command, cwd=ROOT, env=self.env, stdout=stream,
                                        stderr=subprocess.STDOUT)
                stage["exit_code"] = result.returncode
        finally:
            stage["elapsed_seconds"] = round(time.monotonic() - tick, 3)
            if log.exists():
                stage["log_sha256"] = sha256(log)
            self.save()
        if result.returncode:
            raise RuntimeError(f"{name} exited {result.returncode}; see {log.name}")
        return log.read_text(errors="replace").split("\n", 1)[1]


def git_checkout(receipt, checkout, label, expected):
    head = receipt.run(label + "-head", "git", "-C", checkout, "rev-parse", "HEAD").strip()
    dirty = receipt.run(label + "-status", "git", "-C", checkout, "status", "--porcelain",
                        "--untracked-files=all").strip()
    toplevel = receipt.run(label + "-root", "git", "-C", checkout, "rev-parse",
                           "--show-toplevel").strip()
    if head != expected or dirty or Path(toplevel).resolve() != checkout:
        raise RuntimeError("Unexpected commit, checkout root or dirty sources: " + label)
    return {"root": str(checkout), "head": head, "working_tree": dirty}

USED_PACKAGES = ("goldbach", "mathlib", "LeanArchitect", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
                 "aesop", "Qq", "batteries", "Cli")


def package_pins(manifest):
    pins = {item["name"]: item["rev"] for item in manifest["packages"]}
    if set(pins) != set(USED_PACKAGES) or len(pins) != len(manifest["packages"]):
        raise RuntimeError("Unexpected package manifest")
    return pins


def prepare_environment(receipt, args, objroot):
    toolchain = args.toolchain_root.resolve(strict=True)
    tools = {name: toolchain / "bin" / name for name in TOOL_HASHES}
    for tool in tools.values():
        if not tool.is_file() or tool.resolve() != tool:
            raise RuntimeError("Invalid bundled tool: " + str(tool))
    tool_hashes = {name: sha256(tool) for name, tool in tools.items()}
    receipt.data.update(tool_paths={k: str(v) for k, v in tools.items()},
                        tool_sha256=tool_hashes,
                        prior_receipt_tool_sha256=TOOL_HASHES,
                        matches_prior_receipt_tool_hashes=(tool_hashes == TOOL_HASHES))
    pins = package_pins(json.loads((ROOT / "lake-manifest.json").read_text()))
    receipt.data["external_scope"] = {
        "configured_package_count": len(pins),
        "direct_goldbach_import": GOLDBACH_MODULE,
        "goldbach_imported_by": "ImbalancedChen.PanProductLiuBridge",
        "external_objects": "Prebuilt objects under pinned package checkouts; direct dependencies hashed.",
        "external_kernel_replay": False,
    }
    packages = {}
    checkouts = receipt.data["package_checkouts"] = {}
    for name in USED_PACKAGES:
        checkout = (args.package_root / name).resolve(strict=True)
        checkouts[name] = git_checkout(receipt, checkout, "package-" + name, pins[name])
        raw = checkout / OBJECTS
        lib = raw.resolve(strict=True)
        if lib != raw or not lib.is_dir():
            raise RuntimeError("Invalid external cache directory: " + str(raw))
        packages[name] = lib
        checkouts[name]["object_root"] = str(lib)
    syslib = (toolchain / "lib/lean").resolve(strict=True)
    roots = (objroot, *packages.values(), syslib)
    if any(a.is_relative_to(b) for i, a in enumerate(roots) for j, b in enumerate(roots) if i != j):
        raise RuntimeError("Overlapping object roots")
    # The bundled sysroot supplies Init/Lean/Std as Lean's built-in last entry.
    # Clear inherited Lean/Elan/Lake overrides, including extra search paths.
    for key in tuple(receipt.env):
        if key.startswith(("LEAN_", "LEAN4_", "ELAN_", "LAKE_")):
            receipt.env.pop(key)
    receipt.env.update(LEAN_PATH=os.pathsep.join(map(str, roots[:-1])), LEAN_SYSROOT=str(toolchain),
                       PATH=str(toolchain / "bin") + os.pathsep + receipt.env.get("PATH", ""))
    receipt.data.update(lean_path=receipt.env["LEAN_PATH"], sysroot=str(toolchain),
                        system_object_root=str(syslib))
    version = receipt.run("lean-version", tools["lean"], "--version").strip()
    prefix = receipt.run("lean-prefix", tools["lean"], "--print-prefix").strip()
    receipt.data["lean_version"] = version
    if (not re.search(r"\bversion 4\.33\.0-rc1,", version)
            or "commit " + LEAN_COMMIT + "," not in version or Path(prefix).resolve() != toolchain):
        raise RuntimeError("Lean toolchain differs from the pinned installation")
    return tools, tool_hashes, packages, syslib


def verify(args, receipt):
    data = receipt.data
    data["initial_checkout"] = git_checkout(receipt, ROOT, "initial", args.expected_head)
    receipt.run("base-ancestor", "git", "merge-base", "--is-ancestor", BASE, args.expected_head)
    closure, hashes = verify_sources()
    data.update(project_import_closure=closure, source_sha256=hashes, segment_sha256=SEGMENT)
    if args.source_only:
        data["final_checkout"] = git_checkout(receipt, ROOT, "final", args.expected_head)
        data.update(status="SOURCE_ONLY_NOT_COMPILED", finished_utc=now())
        receipt.save()
        return

    objroot = ROOT / OBJECTS
    if objroot.resolve() != objroot:
        raise RuntimeError("Object root is redirected")
    objroot.mkdir(parents=True, exist_ok=True)
    initial_parts = checkout_object_parts()
    if initial_parts:
        raise RuntimeError("This checkout already contains project object parts: " + repr(initial_parts[:5]))
    data["initial_project_object_parts"] = 0
    tools, tool_hashes, packages, syslib = prepare_environment(receipt, args, objroot)
    external = (*packages.values(), syslib)
    fresh = set()
    bindings = data["project_object_bindings"] = {}
    parsed = data["parsed_dependencies"] = {}
    external_objects = data["direct_external_object_bindings"] = {}
    lean = tools["lean"]
    flags = ["-t0", "-j1", "-M12000"]
    strict = ["-DwarningAsError=true"]

    def check_imports(key, path, stage):
        log = receipt.run(stage + "-imports", lean, "--deps", path)
        parsed[key] = expected_deps(ROOT / path, log, fresh, objroot, packages, syslib)
        for dependency in parsed[key]:
            dep = Path(dependency)
            if dep not in fresh and dependency not in external_objects:
                external_objects[dependency] = external_object_parts(dep)

    for n, record in enumerate(closure["project_sources"], 1):
        module, path = record["module"], record["path"]
        stage = module.split(".")[-1]
        print(f"COMPILE {n}/{len(closure['project_sources'])} {module}", flush=True)
        obj = objroot / module_file(module, ".olean")
        if obj.parent.resolve() != obj.parent or any(Path(str(obj) + ext).exists() for ext in PARTS):
            raise RuntimeError("Redirected or pre-existing compilation target: " + str(obj))
        obj.parent.mkdir(parents=True, exist_ok=True)
        check_imports(module, path, stage)
        strict_target = module in TARGETS
        receipt.run(stage + ("-strict" if strict_target else "-compile"), lean, *flags,
                    *(strict if strict_target else []), "-o", obj, path)
        bindings[module] = bind_object(module, objroot, external)
        fresh.add(obj)
    for module in TARGETS:
        print("REPLAY " + module, flush=True)
        replay = receipt.run(module.split(".")[-1] + "-replay", tools["leanchecker"], "--verbose", module)
        if "replaying " + module not in replay.splitlines():
            raise RuntimeError("Missing replay evidence for " + module)
    print("BOUNDARY AND OWNER AUDIT", flush=True)
    check_imports(str(BOUNDARY), BOUNDARY, "boundary")
    receipt.run("boundary", lean, *flags, *strict, BOUNDARY)
    check_imports(str(AUDIT), AUDIT, "audit")
    records, counts = validate_inventory(receipt.run("owner-audit", lean, *flags, *strict, AUDIT),
                                         modules=TARGETS)
    owner = {r["name"]: r for r in records if r["module"] == NEW}
    names = [NAMESPACE + "." + n for n in PUBLIC]
    for n, name in enumerate(names):
        if name not in owner or owner[name]["kind"] != ("theorem" if n else "definition"):
            raise RuntimeError("Missing literal declaration: " + name)
    phase_type = " ".join(owner[names[-1]]["type"].split())
    if not re.search(r"\(k1 : (?:Int|ℤ)\)", phase_type):
        raise RuntimeError("Signed arbitrary k1 binder absent from compiler type")
    for r in records:
        r["ownership"] = "new_P3.4_consumer" if r["module"] == NEW else "reused_P3.1_provider"
    if any(sha256(ROOT / path) != expected for path, expected in hashes.items()):
        raise RuntimeError("Source changed during verification")
    if bindings != {m: bind_object(m, objroot, external) for m in bindings}:
        raise RuntimeError("Project object resolution, parts or hashes changed after compilation")
    if object_parts(objroot) != {name for item in bindings.values() for name in item["parts"]}:
        raise RuntimeError("Unexpected file in project object inventory")
    if any(external_object_parts(Path(p)) != parts for p, parts in external_objects.items()):
        raise RuntimeError("Directly imported external object parts changed")
    if {name: sha256(tool) for name, tool in tools.items()} != tool_hashes:
        raise RuntimeError("Tool executable changed")
    for name, entry in data["package_checkouts"].items():
        git_checkout(receipt, Path(entry["root"]), "final-package-" + name, entry["head"])
    data["final_checkout"] = git_checkout(receipt, ROOT, "final", args.expected_head)
    json_file(receipt.out / "declarations.json", records)
    (receipt.out / "theorem-types.txt").write_text("head_commit=" + args.expected_head + "\n\n" +
        "\n\n".join(r["module"] + " [" + r["ownership"] + "]\n" + r["name"] + " :\n" + r["type"]
                   + "\naxioms=" + ",".join(r["axioms"]) for r in records if r["kind"] == "theorem") + "\n")
    data.update(status="PASSED", finished_utc=now(), module_counts=counts,
                declaration_count=len(records), source_declarations_accepted=names,
                strict_targets=list(TARGETS), fresh_compiled_module_count=len(bindings),
                artifacts_sha256={f: sha256(receipt.out / f) for f in ("declarations.json", "theorem-types.txt")})
    receipt.save()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--source-only", action="store_true", help="Clean-checkout source gate without Lean")
    parser.add_argument("--toolchain-root", type=Path, default=Path("/workspace/toolchains/lean-4.33.0-rc1-linux"))
    parser.add_argument("--package-root", type=Path, default=Path("/workspace/blue-member-build/.lake/packages"))
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".lake/p34-classical-support-verification")
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    # Move the whole previous attempt aside before starting a rerun. Its real
    # logs survive, and stale successful inventories cannot accompany a failure.
    if (out / "report.json").exists():
        previous = out / ("previous-" + str(time.time_ns()))
        previous.mkdir()
        for path in out.iterdir():
            if path.is_file() and (path.suffix == ".log" or path.name in
                                   {"report.json", "report.json.tmp", "declarations.json", "theorem-types.txt"}):
                path.rename(previous / path.name)
    for name in ("declarations.json", "theorem-types.txt"):
        (out / name).unlink(missing_ok=True)
    receipt = Receipt(out, args.expected_head)
    try:
        verify(args, receipt)
    except BaseException as error:
        for name in ("declarations.json", "theorem-types.txt"):
            (out / name).unlink(missing_ok=True)
        receipt.data.update(status="FAILED", finished_utc=now(), error=str(error))
        receipt.save()
        raise
    print(receipt.data["status"], flush=True)


if __name__ == "__main__":
    main()
