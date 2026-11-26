"""Verify received Causal008/Readout archives with original parser, offline only."""
import ast
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile

HERE = Path(__file__).resolve().parent
WORK = HERE.parent
ATLAS = WORK / "p29-atlas-1126"
DRIVER = HERE / "known-drivers/run_winner9_private_audit.py"
CHECKS = HERE / "known-drivers/run_winner9_private_checks.py"
TEMPLATE = ATLAS / "causal007-original-failure/extracted/original-auditor/winner9_private_audit_template.lean"
SCALAR = ATLAS / "scalar-root-evidence"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def original_functions(path, names, namespace):
    tree = ast.parse(path.read_text())
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in names]
    assert {n.name for n in functions} == set(names)
    # Execute the exact, unmodified AST nodes; no compiler/process function is included.
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(path), "exec"), namespace)


assert sha(DRIVER) == "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5"
assert sha(TEMPLATE) == "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b"
ns = dict(Path=Path, json=json, Counter=Counter, hashlib=hashlib,
          AXIOMS={"Classical.choice", "Quot.sound", "propext"}, CACHE_SCHEMA=2, EXTERNAL_CACHE_SCHEMA=3)
original_functions(DRIVER, ["require", "parse_audit", "replay_context"], ns)
original_functions(CHECKS, ["json_digest", "closure_signature"], ns)

reception = read(Path(sys.argv[1]))
scalar_records = read(SCALAR / ".lake/p2-private/records.json")
known = {}
for name, rec in scalar_records.items():
    known[name] = {k: rec[k] for k in ("source_sha256", "object_sha256", "closure_signature")}
pair_base = Path("/dev/shm/p29-atlas-1126/qualified-chain008")
for short in ["Part5OriginalCausalSmoothAtlas", "P2OriginalSmoothReadoutCore"]:
    name = "ImbalancedChen." + short
    rec = read(pair_base / short / ".lake/p2-private/records.json")[name]
    accepted = next(r for r in read(HERE / "CHAIN008_ROOT_COMPLETE_EVIDENCE_REVIEW.json")["results"] if r["module"] == name)
    assert rec["source_sha256"] == accepted["source_sha256"] and rec["object_sha256"] == accepted["object_sha256"]
    known[name] = {k: rec[k] for k in ("source_sha256", "object_sha256", "closure_signature")}
borrowed = read(HERE / "unit-tail-qualified/verification/BORROWED_OBJECTS.json")
for name, row in borrowed.items():
    if "closure_signature" not in row["producer"]:
        continue  # Native/P1 records use a different scheme; none is silently translated.
    candidate = {"source_sha256": row["source_sha256"], "object_sha256": row["object_sha256"], "closure_signature": row["producer"]["closure_signature"]}
    if name in known:
        assert known[name] == candidate, ("Known authorities conflict", name)
    known[name] = candidate
geometry = read(HERE / "PRIOR_GEOMETRIC_FAMILY_ACCEPTANCE.json")
assert geometry["status"] == "FOUR_EXACT_MODULES_ACCEPTED"
for name, row in geometry["accepted_modules"].items():
    candidate = {"source_sha256": row["source_sha256"], "object_sha256": row["object_sha256"], "closure_signature": row["compile_closure_signature"]}
    if name in known:
        assert known[name] == candidate, ("Geometry authority conflict", name)
    known[name] = candidate
chart = HERE / "chart004-evidence/.lake/p2-private/audit/ImbalancedChen.P2OriginalChartDerivativeCore/latest.json"
assert sha(chart) == "0e070aab129854a8730aa065175e553db8ae4013cb9d3faa6ab9cfd510d571c4"
rec = read(chart)
assert rec["accepted"] is True
known[rec["module"]] = {"source_sha256": rec["source_sha256"], "object_sha256": rec["object_sha256"], "closure_signature": rec["compile_closure_signature"]}
# Any newly accepted immediate supplier is identified by its already verified root report.
for extra in reception.get("newly_accepted_suppliers", []):
    prior = read(Path(extra["root_review"]))["results"]
    accepted = next(x for x in prior if x["module"] == extra["module"])
    rec = read(Path(extra["evidence"]) / ".lake/p2-private/records.json")[extra["module"]]
    assert rec["source_sha256"] == accepted["source_sha256"] and rec["object_sha256"] == accepted["object_sha256"]
    known[extra["module"]] = {k: rec[k] for k in ("source_sha256", "object_sha256", "closure_signature")}
completed = {}
for item in reception["archives"]:
    target = item["target"]
    root = Path(item["extracted"])
    archive = Path(item["archive_local"])
    assert archive.stat().st_size == item["archive_bytes"]
    assert sha(archive) == item["archive_sha256"]
    assert git_blob(archive.read_bytes()) == item["git_blob"]
    with tarfile.open(archive, "r:gz") as tf:
        members = tf.getmembers()
        names = [x.name for x in members]
        assert len(names) == len(set(names)) == item["members"]
        assert all(x.isfile() and not PurePosixPath(x.name).is_absolute()
                   and ".." not in PurePosixPath(x.name).parts for x in members)
        manifest_bytes = tf.extractfile("manifest.json").read()
        assert hashlib.sha256(manifest_bytes).hexdigest() == item["manifest_sha256"]
        manifest = json.loads(manifest_bytes)
        assert set(manifest["files"]) == set(names) - {"manifest.json"}
        for member in members:
            data = tf.extractfile(member).read()
            assert len(data) == member.size and (root / member.name).read_bytes() == data
            if member.name != "manifest.json":
                assert manifest["files"][member.name] == {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
    records = read(root / ".lake/p2-private/records.json")
    snapshot = read(root / "normal-snapshots.json")
    source = root / (target.replace(".", "/") + ".lean")
    obj = root / ".lake/p2-private/lib" / (target.replace(".", "/") + ".olean")
    assert git_blob(source.read_bytes()) == manifest["source_blob"] == item["source_blob"]
    assert sha(source) == manifest["source_sha256"] == item["source_sha256"]
    assert sha(obj) == manifest["object_sha256"] == item["object_sha256"]
    selected = read(root / "source-selection.json")
    assert selected[target]["source_blob"] == item["source_blob"]
    assert selected[target]["source_sha256"] == item["source_sha256"]
    assert selected[target]["source_text"].encode() == source.read_bytes()
    assert manifest["normal_compiles"] == [target] and snapshot["provider_recompiles"] == 0
    assert snapshot["before"] == snapshot["after"]
    assert sha(root / "normal-controller.py") == manifest["normal_driver_sha256"] == item["normal_driver_sha256"]
    assert manifest["original_audit_driver_sha256"] == sha(DRIVER)
    assert (root / "LOGBOX_ORIGIN_BINDING.json").read_bytes() == (SCALAR / "LOGBOX_ORIGIN_BINDING.json").read_bytes()
    closure = set(snapshot["real_project_source_closure"])
    assert closure == set(records) == set(manifest["provider_modules"]) | {target}
    assert set(snapshot["before"]["project"]) == closure - {target}
    audit_dir = root / ".lake/p2-private/audit" / target
    receipt = read(audit_dir / "latest.json")
    assert receipt == read(audit_dir / "attempt-001/receipt.json")
    assert sha(audit_dir / "latest.json") == item["receipt_sha256"] == manifest["receipt_sha256"]
    assert receipt["accepted"] is True and receipt["module"] == target
    frozen = receipt["input_snapshot"]
    assert set(frozen["project"]) == closure
    assert ns["json_digest"](frozen) == receipt["input_sha256"]
    assert ns["replay_context"](frozen) == receipt["replay_binding"]
    assert frozen["driver_sha256"] == sha(DRIVER)
    assert frozen["template_sha256"] == sha(TEMPLATE)
    assert frozen["toolchain"] == snapshot["mathlib_boundary"]
    assert frozen["lean_binary_sha256"] == frozen["toolchain"]["lean_binary_sha256"] == "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
    assert frozen["leanchecker_sha256"] == "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
    assert frozen["toolchain"]["mathlib_commit"] == "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
    for name in closure:
        rec = records[name]
        rel = name.replace(".", "/")
        src = root / (rel + ".lean")
        output = root / ".lake/p2-private/lib" / (rel + ".olean")
        actual = frozen["project"][name]
        assert actual["source"] == rel + ".lean"
        assert rec["module"] == name and rec["cache_schema"] == 2 and rec["exit_code"] == 0
        assert rec["toolchain"] == frozen["toolchain"]
        assert sha(src) == rec["source_sha256"] == actual["source_sha256"]
        assert sha(output) == rec["object_sha256"] == actual["object_sha256"]
        deps = re.findall(r"(?m)^import (ImbalancedChen\.[A-Za-z0-9_.]+)\s*$", src.read_text())
        assert rec["deps"] == {n: records[n]["object_sha256"] for n in deps}
        assert rec["dependency_signatures"] == {n: records[n]["closure_signature"] for n in deps}
        assert ns["closure_signature"](rec) == rec["closure_signature"]
        if name != target:
            assert snapshot["before"]["project"][name] == actual
            assert name in known, ("Missing already accepted supplier identity", name)
            assert {k: rec[k] for k in ("source_sha256", "object_sha256", "closure_signature")} == known[name], ("Accepted supplier identity mismatch", name)
    rec = records[target]
    assert rec["new_strict_compile"] is True and len(rec["attempts"]) == 1
    assert rec["command"] == snapshot["compile_command"] == rec["attempts"][0]["command"]
    assert rec["attempts"][0]["exit_code"] == 0
    assert "-DwarningAsError=true" in rec["command"] and "-j1" in rec["command"]
    assert rec["command"][-1] == str(source.relative_to(root))
    assert (root / rec["log"]).read_bytes() == b""
    assert receipt["compile_closure_signature"] == rec["closure_signature"]
    assert receipt["source_sha256"] == rec["source_sha256"]
    assert receipt["object_sha256"] == rec["object_sha256"]
    for stage in ["replay", "audit"]:
        entry = receipt[stage]
        assert entry["exit_code"] == 0 and entry["inputs_unchanged"] is True
        assert sha(root / entry["log"]) == entry["log_sha256"]
    assert receipt["replay"]["command"] == ["/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leanchecker", "--verbose", target]
    assert (root / receipt["replay"]["log"]).read_text() == "replaying " + target + "\n"
    for name, digest in receipt["artifacts"].items():
        assert sha(root / name) == digest
    audit_source = root / receipt["audit"]["source"]
    assert audit_source.read_text() == TEMPLATE.read_text().replace("ImbalancedChen.P2Winner9FiniteMomentKernel", target)
    assert sha(audit_source) == receipt["audit"]["source_sha256"]
    assert "-DwarningAsError=true" in receipt["audit"]["command"]
    parsed = ns["parse_audit"](root / receipt["audit"]["log"], target, closure)
    assert parsed == read(audit_dir / "attempt-001/declarations.json")
    assert parsed["declaration_count"] == item["declarations"] == manifest["declarations"] == receipt["audit"]["declaration_count"]
    assert parsed["axiom_counts"] == receipt["audit"]["axiom_counts"] == manifest["axioms"]
    types = "\n\n".join(d["name"] + "\n" + d["type"] for d in parsed["declarations"]) + "\n"
    assert types == (audit_dir / "attempt-001/types.txt").read_text()
    assert not any("_unsafe_rec" in d["name"] for d in parsed["declarations"])
    summary = read(root / ".lake/p2-private/audit/p29-chart.json")
    assert summary["all_accepted"] and summary["accepted"] == summary["requested"] == 1
    assert summary["modules"][target] == {"accepted": True, "declarations": item["declarations"], "reused": False}
    result = dict(schema="p29_p2_atlas_single_root_full_evidence_review_v1", observed_utc=datetime.now(timezone.utc).isoformat(),
                  status="PASS_ALL_ORIGINAL_ARCHIVE_MEMBERS_SOURCE_NORMAL_KERNEL_AND_COMPLETE_OWNED",
                  module=target, source_blob=item["source_blob"], source_sha256=item["source_sha256"],
                  object_sha256=item["object_sha256"], receipt_sha256=item["receipt_sha256"],
                  archive_git_blob=item["git_blob"], archive_sha256=item["archive_sha256"],
                  archive_bytes=item["archive_bytes"], archive_members=item["members"],
                  manifest_sha256=item["manifest_sha256"], all_members_safe_unique_sizes_hashes_verified=True,
                  normal_exit=0, normal_warningAsError=True, normal_log_bytes=0, named_kernel_exit=0, full_owned_exit=0,
                  owned=item["declarations"], private_owned=sum(d["name"].startswith("_private.") for d in parsed["declarations"]),
                  full_inventory_and_types_reparsed_with_exact_original_parser=True,
                  original_audit_source_exact_target_only_template_substitution=True,
                  original_audit_driver_sha256=sha(DRIVER), original_audit_template_sha256=sha(TEMPLATE),
                  original_audit_format="Complete owned inventory, full pp.all types, unsafe/partial/axiom flags and transitive axiom lists. No separate raw-AST/universe fields claimed.",
                  axioms=sorted(parsed["axiom_counts"]), project_modules=len(closure),
                  exact_old_provider_records_and_source_object_bytes_reused=True,
                  normal_provider_snapshots_unchanged=True, provider_recompiles=0, provider_kernel_owned_replays=0,
                  reviewer_Lean_executions=0, fresh_full_standard_import_kernel_replay=False, full_p2_9_complete=False)
    completed[target] = {"record": rec, "result": result}
    print(json.dumps({"target": target, "members": item["members"], "owned": item["declarations"], "status": result["status"]}), flush=True)

report = {"schema": "p29_p2_atlas_complete_root_review_v1", "results": [v["result"] for v in completed.values()],
          "new_modules": len(completed), "new_owned": sum(v["result"]["owned"] for v in completed.values()), "reviewer_Lean_executions": 0, "full_p2_9_complete": False}
Path(sys.argv[2]).write_text(json.dumps(report, indent=2) + "\n")
