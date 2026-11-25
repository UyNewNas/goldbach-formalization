#!/usr/bin/env python3
"""Import the P2.1 roots together. This compatibility probe grants zero compile/kernel/audit credit.

Run from the private checkout after the all-module evidence export. It reads the
original ledgers and native providers and creates only a new probe attempt.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from export_winner9_private_evidence import DRIVER_FILES, Evidence, local_path, sha_bytes, validate_receipt
from extend_p21_buchstab_native_snapshot import TARGETS as ADDED, first_root, relative
from qualify_winner9_native_cache import LOAD_SUFFIXES
from run_winner9_private_audit import LEAN, MATHLIB, PIN, project_nodes, run_process, write_json
from run_winner9_private_checks import closure_signature
from inspect_winner9_owner_native import imports as source_imports
from winner9_external_snapshot import ExternalSnapshot, PhysicalHashes, native, require, signature

BUCHSTAB = "ImbalancedChen.P5ZU1011AutomaticBuchstabIntervals"
# These are the declarations published for this batch. Several owners use a
# different declaration namespace, so bind the names to each importing module.
PUBLIC_TARGETS = {
    "ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQueryAllBranches": (
        "ImbalancedChen.P0All40PublicQuery",
        ("query_encloses_all", "query_eq_original_all", "public_query_encloses_all",
         "query_integer_encloses_all", "query_range_encloses_all"),
    ),
    "ImbalancedChen.P0RationalQueryPublicAPI": (
        "ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly",
        ("pointQuery_sound", "pointQuery_int_div", "literalPointQuery_sound",
         "rational_endpoints_sound", "rangeQuery_sound", "rangeQuery_rational_bounds"),
    ),
    "ImbalancedChen.P2HistoricBackendTypeAdapters": (
        "ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters",
        ("sourceSf_delegation", "sourceSf_lo_exact", "sourceSf_hi_exact", "sourceSf_contains_actual",
         "sourceLogI_lo_exact", "sourceLogI_hi_exact", "sourceLogI_contains",
         "sourceLogI_contains_of_one_le", "sourceLogI_ratio_contains"),
    ),
    BUCHSTAB: (
        "ImbalancedChen.P5Z.AutomaticBuchstabIntervals",
        ("actual_interval_bounds", "actual_interval_width"),
    ),
    "ImbalancedChen.P2OriginalCompactQ80Table": (
        "ImbalancedChen.P2OriginalCompactQ80TableSourceOnly",
        ("table12_encloses_actual", "numerator12_contains_actual_L",
         "point12_contains_actual", "sf12_contains_actual"),
    ),
}
INVENTORY = """
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    let path ← liftIO <| Lean.findOLean moduleName
    let row := Json.mkObj [("module", toJson moduleName.toString), ("olean", toJson path.toString)]
    liftIO <| IO.println s!"P21_IMPORT {row.compress}"
"""


def public_targets(roots):
    public = {row["module"]: row["public_theorem_targets"] for row in roots}
    require(len(roots) == len(public) and public.keys() == PUBLIC_TARGETS.keys(),
            "Expected the five published root modules")
    for owner, (namespace, names) in PUBLIC_TARGETS.items():
        expected = {namespace + "." + name for name in names}
        actual = public[owner]
        require(len(actual) == len(expected) and set(actual) == expected,
                "Public targets differ for " + owner)
    return public


def compatible(base, extended):
    require(len(base.modules) == 515 and set(extended.modules) - set(base.modules) == set(ADDED),
            "Unexpected provider scope")
    for key in ("modules", "resolutions", "files"):
        require(all(extended.value[key].get(k) == v for k, v in base.value[key].items()),
                "Extension changed a base " + key + " entry")
    require(base.value["packages"] == extended.value["packages"], "Native packages changed")
    runtime = dict(extended.value["runtime"])
    require(runtime["lean_path"][1:] == base.value["runtime"]["lean_path"],
            "Expected exactly one new highest-priority native search root")
    runtime["lean_path"] = runtime["lean_path"][1:]
    require(runtime == base.value["runtime"], "Toolchain/runtime changed")


def layout(snapshot, name, hashes):
    stem = first_root(snapshot.search_path, name) / relative(name, "")
    public = Path(str(stem) + ".olean").resolve(strict=True)
    expected = snapshot.value["resolutions"].get(name)
    require(not native(name) or (name in snapshot.modules and expected is not None),
            "Missing qualified native resolution: " + name)
    require(expected is None or public == Path(expected), "Unexpected resolved public object: " + name)
    facets = {}
    for suffix in LOAD_SUFFIXES:
        path = Path(str(stem) + suffix)
        if path.is_file():
            physical = path.resolve(strict=True)
            digest = hashes.digest(physical)
            if expected is not None:
                record = snapshot.files.get(str(physical))
                require(record is not None, "Unregistered loadable facet: " + str(path))
                require(record["bytes"] == physical.stat().st_size and record["sha256"] == digest,
                        "Qualified loadable facet differs: " + str(path))
            facets[suffix] = [str(physical), digest]
    return facets


def require_same(before, after):
    require(before == after, "Joint probe input changed during execution")


def frozen_json(path, evidence):
    raw = path.read_bytes()
    require(sha_bytes(raw) == evidence.freeze(path), "JSON changed while loading: " + str(path))
    return json.loads(raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export-manifest", type=Path, required=True)
    parser.add_argument("--targets", type=Path, default=Path("docs/verification/20261125-p2-1/TARGETS.json"))
    parser.add_argument("--memory-mb", type=int, choices=(6144, 11264), default=6144)
    args = parser.parse_args()
    root = Path.cwd().resolve()
    private = root / ".lake/p2-private"
    evidence = Evidence()
    target_path = args.targets.resolve(strict=True)
    targets = frozen_json(target_path, evidence)
    export = frozen_json(args.export_manifest.resolve(strict=True), evidence)
    target_key = "worktree/" + str(target_path.relative_to(root))
    require(export["files"][target_key]["sha256"] == evidence.freeze(target_path),
            "Selected export binds a different target manifest")
    modules = {r["module"]: r for r in targets["modules"]}
    public = public_targets(targets["roots"])
    checks = [name for names in public.values() for name in names]
    require(len(public) == len(targets["roots"]) == 5 and len(modules) == len(targets["modules"]) ==
            targets["project_module_count"] and len(checks) == len(set(checks)) == 26 and
            all(re.fullmatch(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9]*)+", n) for n in [*modules, *checks]),
            "Invalid target manifest")
    root_nodes = {r: set(project_nodes(root, r)) for r in public}
    old = set.union(*(nodes for r, nodes in root_nodes.items() if r != BUCHSTAB))
    new = root_nodes[BUCHSTAB]
    require(len(old) == 132 and len(new) == 8 and not old & new and old | new == set(modules),
            "Five-root project partition differs")
    accepted = export["accepted_modules"]
    require(set(accepted) == set(export["object_manifest"]) == set(modules) and not export["unselected_modules"]
            and not export["duplicate_owned_declarations"] and export["accepted_module_count"] == len(modules),
            "Export does not cover the full selection")
    ext = {}
    for context in export["external_snapshots"].values():
        binding = context["binding"]
        key = evidence.bind_external(root, binding)
        evidence.accepted_external_contexts.add(key)
        size = len(binding["native_modules"])
        require(size not in ext, "Duplicate external context size")
        ext[size] = evidence.external_contexts[key][1]
    require(set(ext) == {515, 518}, "Missing base/extension context")
    base, extended = ext[515], ext[518]
    compatible(base, extended)
    provider = frozen_json(Path(extended.value["qualification"]["path"]), evidence)
    require(provider["parent"] == base.raw_sha256 and
            extended.files[str(base.path)]["sha256"] == base.raw_sha256, "Unbound parent snapshot")

    drivers = {}
    for p in ("docs/verification/20261124-p2-private/driver-v1.py",
              "docs/verification/20261124-p2-private/audit-driver-v2.py",
              "docs/verification/20261125-p2-resume/audit-driver-v3.py",
              "verification/part2/run_winner9_private_audit.py"):
        path = root / p
        if path.is_file() and evidence.freeze(path) in DRIVER_FILES:
            drivers[evidence.freeze(path)] = path
    records_path = private / "records.json"
    def selected():
        records = json.loads(records_path.read_bytes())
        return {name: records[name] for name in modules}
    records = selected()
    observed = set()
    base_observed = set(base.value["resolutions"])
    selected_receipts = {}
    for name, row in modules.items():
        meta = accepted[name]
        receipt_path = local_path(root, meta["receipt_source"])
        receipt = frozen_json(receipt_path, evidence)
        require(evidence.freeze(receipt_path) == meta["receipt_sha256"] and
                receipt["source_sha256"] == row["source_sha256"], "Selected receipt/source differs: " + name)
        selected_receipts[name] = [str(receipt_path), meta["receipt_sha256"]]
        verified = validate_receipt(root, name, receipt, records, evidence, drivers)
        expected = extended if name in new else base
        binding = receipt["input_snapshot"].get("external_snapshot")
        require(binding == (expected.binding() if verified["nodes"][name]["requires_external"] else None),
                "Wrong original receipt context: " + name)
        require(set(public.get(name, [])) <= {r["name"] for r in verified["parsed"]["declarations"]},
                "Public target missing from its owner's audit: " + name)
        observed.update(verified["parsed"]["imports"])
        if name in old:
            base_observed.update(verified["parsed"]["imports"])
    require({x for x in observed if x.startswith("ImbalancedChen.")} == set(modules), "Audit union differs")

    attempt = Path(tempfile.mkdtemp(prefix="p21-joint-", dir=private))
    probe = attempt / "Joint.lean"
    probe.write_text("".join("import " + n + "\n" for n in public) + "import Lean.Elab.Command\nimport Lean.Util.CollectAxioms\n"
                     + "".join("#check " + n + "\n" for n in checks) + INVENTORY)
    for p in (probe, Path(__file__).resolve(), Path(source_imports.__code__.co_filename),
              Path(closure_signature.__code__.co_filename),
              Path(validate_receipt.__code__.co_filename), Path(first_root.__code__.co_filename),
              Path(run_process.__code__.co_filename), Path(ExternalSnapshot.verify.__code__.co_filename)):
        evidence.freeze(p)
    hashes = PhysicalHashes()
    def capture():
        require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN,
                "Live Mathlib pin differs")
        contexts = [s.verify() for s in (base, extended)]
        objects = {n: layout(extended, n, hashes) for n in sorted(observed | base_observed | set(extended.value["resolutions"]))}
        for n in base_observed:
            require(layout(base, n, hashes) == objects[n], "Shared physical provider/facets differ: " + n)
        for n in modules:
            require(objects[n][".olean"] == [str((private / "lib" / relative(n, ".olean")).resolve(strict=True)),
                                               records[n]["object_sha256"]], "Wrong project object: " + n)
        env = extended.environment(os.environ)
        return {"records_sha256": signature(selected()), "snapshots": contexts,
                "lean_path": env["LEAN_PATH"], "lean_sysroot": env["LEAN_SYSROOT"], "objects": objects}

    before = capture()
    require(before["records_sha256"] == signature(records), "Selected records changed before joint probe")
    env = extended.environment(os.environ)
    command = [LEAN, "-t0", "-j1", "-M" + str(args.memory_mb), "-DwarningAsError=true", str(probe.relative_to(root))]
    result = run_process(command, attempt / "joint.log", root, env)
    require(result["exit_code"] == 0, "Joint import or a public #check failed. See " + result["log"])
    actual = {}
    for line in (attempt / "joint.log").read_text().splitlines():
        if line.startswith("P21_IMPORT "):
            entry = json.loads(line.removeprefix("P21_IMPORT "))
            name = entry["module"]
            require(name not in actual, "Duplicate loaded module: " + name)
            actual[name] = str(Path(entry["olean"]).resolve(strict=True))
    require(set(actual) == observed and all(actual[n] == before["objects"][n][".olean"][0] for n in observed),
            "Actual loaded modules or Lean.findOLean paths differ")
    after = capture()
    require_same(before, after)
    evidence.verify_frozen()
    require(sha_bytes((attempt / "joint.log").read_bytes()) == result["log_sha256"], "Joint output log changed")
    receipt = {"status": "JOINT_IMPORT_COMPATIBLE", "compile_credit": False, "kernel_credit": False,
               "audit_credit": False, "probe": str(probe), "public_checks": checks, "roots": list(public),
               "project_modules": sorted(modules), "loaded_modules": actual, "command_result": result,
               "selected_receipts": selected_receipts, "inputs": before, "inputs_unchanged": True,
               "inputs_post_sha256": signature(after),
               "frozen_files": {str(p): h for p, h in evidence.frozen.items()}}
    write_json(attempt / "receipt.json", receipt)
    print(attempt / "receipt.json", flush=True)


if __name__ == "__main__":
    main()
