#!/usr/bin/env python3
"""One-time, evidenced migration of the 2026-11-24 private P2 receipts.

The legacy allowance is deliberately limited to the unchanged ledger/Full87
definition graph. Numerical probes without their actual dependency snapshot
are never migrated. This is receipt migration, not new proof verification.
"""
import argparse
import json
from pathlib import Path
import subprocess

from run_winner9_private_checks import (
    BASELINE, CACHE_SCHEMA, LEAN, MATHLIB, PIN, closure_signature, digest, imports,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fresh_receipt", type=Path)
    parser.add_argument("--fresh-job", required=True)
    args = parser.parse_args()
    root = Path.cwd()
    base = Path("/workspace/goldbach-p2")
    out = root / ".lake/p2-private"
    lib = out / "lib"
    baseline_lib = base / ".lake/build/lib/lean"
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=base, text=True).strip() == BASELINE
    assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                       cwd=base, text=True).strip()
    identity = {
        "lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
        "lean_binary_sha256": digest(Path(LEAN)),
        "mathlib_commit": subprocess.check_output(["git", "rev-parse", "HEAD"],
                                                  cwd=MATHLIB, text=True).strip(),
    }
    assert identity["mathlib_commit"] == PIN
    records_path = out / "records.json"
    old = json.loads(records_path.read_text())
    backup = out / "records.before-schema2.json"
    if not backup.exists():
        backup.write_bytes(records_path.read_bytes())
    accepted = {}
    receipts = []

    def paths(name):
        relative = Path(name.replace(".", "/"))
        return root / relative.with_suffix(".lean"), lib / relative.with_suffix(".olean")

    def matches(record):
        source, obj = paths(record["module"])
        return (record.get("exit_code") == 0 and source.is_file() and obj.is_file()
                and record.get("source_sha256") == digest(source)
                and record.get("object_sha256") == digest(obj))

    def admit(record, basis):
        name = record["module"]
        source, obj = paths(name)
        deps = imports(source)
        assert all(dep in accepted for dep in deps)
        record = dict(record)
        expected = {dep: accepted[dep]["object_sha256"] for dep in deps}
        if "deps" in record:
            assert record["deps"] == expected, name
        record.update({"deps": expected, "object": str(obj), "toolchain": identity,
                       "dependency_signatures": {dep: accepted[dep]["closure_signature"] for dep in deps},
                       "cache_schema": CACHE_SCHEMA, "migration_basis": basis})
        record["closure_signature"] = closure_signature(record)
        accepted[name] = record
        receipts.append({"module": name, "basis": basis, "source_sha256": record["source_sha256"],
                         "object_sha256": record["object_sha256"],
                         "closure_signature": record["closure_signature"]})

    pending = {}
    # Match the complete unchanged historical source/object graph, not only a
    # parent's .olean. No new compilation credit is given to these objects.
    manifest = json.loads((out / "baseline-cache.json").read_text())
    for relative, item in manifest.items():
        name = str(Path(relative).with_suffix("")).replace("/", ".")
        original = base / Path(relative).with_suffix(".lean")
        original_obj = baseline_lib / relative
        record = {"module": name, "source": str(Path(relative).with_suffix(".lean")),
                  "source_sha256": item["source_sha256"], "object_sha256": item["object_sha256"],
                  "exit_code": 0, "new_strict_compile": False, "baseline_commit": BASELINE}
        if (matches(record) and digest(original) == record["source_sha256"]
                and digest(original_obj) == record["object_sha256"]):
            pending[name] = record
    changed = True
    while changed:
        changed = False
        for name, record in list(pending.items()):
            if all(dep in accepted for dep in imports(paths(name)[0])):
                admit(record, "unchanged accepted 8657 source/object dependency graph")
                del pending[name]
                changed = True

    # Historical job membership is fixed; adding a file to an archive must not
    # grant it that job's provenance or bypass the fresh-snapshot requirement.
    definition_names = [
        "OriginalAscendingThirteenRowDefinitions", "OriginalDescendingFifteenRowDefinitions",
        "P2OriginalDescendingEighthCapDefinitions", "P2OriginalThirdMinorantCapDefinitions",
        "P4AOriginalAscendingFourteenSourceDefinitions", "P4AOriginalFull87IntegralDefinitions",
        "P4AOriginalFull87SourceDefinitions", "P4AOriginalH3SourceDefinitions",
        "P4AOriginalH5H7SourceDefinitions", "P4AOriginalRemainingEighthSourceDefinitions",
        "P4AOriginalSeed7Unequal15SourceDefinitions",
    ]
    legacy_jobs = {"ImbalancedChen." + name: "a4a1b513c70f4760a22b7b3e90fdb403"
                   for name in definition_names}
    legacy_jobs["ImbalancedChen.VariableEnvelope"] = "a4a1b513c70f4760a22b7b3e90fdb403"
    legacy_jobs["ImbalancedChen.P2Winner9LedgerBridge"] = "22e78e51e6a34ccc87c82dc801f51407"
    pending = {name: old[name] for name in legacy_jobs if name in old and matches(old[name])}
    while pending:
        progress = False
        for name, record in list(pending.items()):
            assert record["module"] == name, name
            deps = imports(paths(name)[0])
            if not all(dep in accepted for dep in deps):
                continue
            # This restricted graph has not been changed by any numerical
            # experiment. Every historical edge is checked against its saved
            # object hash and each child has its own source/object receipt.
            assert record["deps"] == {dep: accepted[dep]["object_sha256"] for dep in deps}, name
            admit(record, "unchanged strict-compile graph, job " + legacy_jobs[name])
            del pending[name]
            progress = True
        if not progress:
            raise RuntimeError("Historical graph cannot be reconstructed: " + repr(sorted(pending)))

    fresh = json.loads(args.fresh_receipt.read_text())
    pending = {record["module"]: record for record in fresh.values()
               if record.get("module") and record.get("exit_code") == 0}
    while pending:
        progress = False
        for name, record in list(pending.items()):
            assert matches(record), name
            deps = imports(paths(name)[0])
            if not all(dep in accepted for dep in deps):
                continue
            actual = record["identity"]
            assert identity == {"lean_version": actual["lean_version"],
                                "lean_binary_sha256": actual["lean_sha256"],
                                "mathlib_commit": actual["mathlib_commit"]}
            closure = set()

            def visit(dep):
                if dep in closure:
                    return
                closure.add(dep)
                for child in imports(paths(dep)[0]):
                    visit(child)

            for dep in deps:
                visit(dep)
            snapshot = record["dependency_snapshot"]
            assert set(snapshot) == closure, name
            for dep, saved in snapshot.items():
                assert saved["source_sha256"] == accepted[dep]["source_sha256"], (name, dep)
                assert saved["object_sha256"] == accepted[dep]["object_sha256"], (name, dep)
            record = dict(record, new_strict_compile=True)
            admit(record, "frozen pre/post compilation dependency snapshot, job " + args.fresh_job)
            del pending[name]
            progress = True
        if not progress:
            raise RuntimeError("Fresh graph cannot be reconstructed: " + repr(sorted(pending)))
    records_path.write_text(json.dumps({**old, **accepted}, indent=2, sort_keys=True) + "\n")
    report = {"receipt_migration_only": True, "new_kernel_replays": 0,
              "legacy_numeric_probes_adopted": 0, "toolchain": identity, "modules": receipts}
    (out / "schema2-migration.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"migrated": len(accepted), "receipt_migration_only": True,
                      "legacy_numeric_probes_adopted": 0}))


if __name__ == "__main__":
    main()
