#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'PY'
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path("/workspace")
source = root / "p24-node-proof-blocks-toy-20261126/attempt-005"
previous = root / "p24-node-proof-blocks-toy-owned-20261126/attempt-002"
out = root / "p24-node-proof-blocks-toy-inspector-20261126/attempt-001"
target = "«p24-node-proof-blocks-toy-20261126».«attempt-005».Toy"
prior_task = "job_bcb4aaa3a0234ef7ba0201a5bb38ed02"
lean = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
leanchecker = lean.with_name("leanchecker")
expected_source = "78decf5bb633707f0de05a9b8c4043e2d6b540d1510dc9e654ba4be549d76ed6"
expected_object = "2503293eca9af1efa7a19ccc3a0e8078391f673d926ba52a88210a5f2f7098b0"
expected_receipt = "1b237df51553ed9b61f261dbd2782d66ca92ae215924c5f976b88922d7337a19"
expected_logs = {
    "replay": "257223354882d2523464f2f84e471a62d65be88e66ace9b6a86bcd43ec81f741",
    "audit": "88b57d2296360f0eebcb6ccc6aaf7a3d59b4dc618f45f9bb2d88e6e239ca3c90",
}
expected_old_inspector = "028dc10515cb73d075981d012b19caa94b58ef422ad552dfcaeb25d06dbd78af"
expected_new_inspector = "3f080f0719193359662e515834108e672d86e3427723c82a63f0da0398a2f66f"
template_hash = "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b"
flags = ["-t0", "-j1", "-M6144", "-DwarningAsError=true",
         "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def directory_hashes(directory):
    return {str(p.relative_to(directory)): digest(p)
            for p in sorted(directory.rglob("*")) if p.is_file()}

def snapshot():
    return {
        "source_attempt_files": directory_hashes(source),
        "previous_audit_files": directory_hashes(previous),
        "lean_sha256": digest(lean), "leanchecker_sha256": digest(leanchecker),
    }

def rows(raw, prefix):
    return [json.loads(line[len(prefix):]) for line in raw.decode("utf-8").splitlines()
            if line.startswith(prefix)]

receipt_path = previous / "diagnostic.json"
require(digest(receipt_path) == expected_receipt, "Prior actual receipt changed")
receipt = json.loads(receipt_path.read_text())
require(receipt["target_module"] == target and receipt["source_attempt"] == str(source),
        "Prior receipt covers another target")
require(receipt["original_replay_and_owned_rules_passed"] is True,
        "Prior original replay/audit did not both pass")
require(receipt["source_attempt_and_tools_unchanged"] is True and
        receipt["before"] == receipt["after"], "Prior input stability was not established")
require(receipt["source_sha256"] == expected_source and digest(source / "Toy.lean") == expected_source,
        "Toy source differs from the successful audited source")
require(digest(source / "Toy.olean") == expected_object, "Toy object changed")
require(receipt["template_sha256"] == template_hash, "Prior original template changed")
require(receipt["audit_template_changes"] == "exactly two replacements of the original target module",
        "Unexpected prior template changes")
for stage, expected_log in expected_logs.items():
    row = receipt["stages"][stage]
    require(row["exit_code"] == 0 and row["timed_out"] is False and row["inputs_unchanged"] is True,
            "The prior " + stage + " was not a successful stable stage")
    require(Path(row["log"]) == previous / (stage + ".log") and
            row["log_sha256"] == expected_log and digest(Path(row["log"])) == expected_log,
            "The prior " + stage + " log changed")
require(receipt["stages"]["replay"]["command"] == [str(leanchecker), "--verbose", target],
        "Unexpected prior independent replay command")
require(receipt["stages"]["audit"]["command"] ==
        [str(lean), *flags, str(previous / "Audit.lean")], "Unexpected prior audit command")
audit_source = (previous / "Audit.lean").read_bytes()
require(hashlib.sha256(audit_source).hexdigest() == receipt["audit_source_sha256"],
        "Prior audit source changed")
require(audit_source.count(target.encode()) == 2, "Unexpected target replacement count")
require(hashlib.sha256(audit_source.replace(target.encode(),
        b"ImbalancedChen.P2Winner9FiniteMomentKernel")).hexdigest() == template_hash,
        "Prior audit was not the exact original template")

# Revalidate the already-bound audit output without re-running either Lean stage.
audit_raw = (previous / "audit.log").read_bytes()
imports = rows(audit_raw, "P0_QUEUE_IMPORTS ")
inventories = rows(audit_raw, "P0_QUEUE_INVENTORY ")
declarations = rows(audit_raw, "P0_QUEUE_DECL ")
require(len(imports) == 1 and not any(n.startswith("ImbalancedChen.") for n in imports[0]),
        "Unexpected imported production module")
require(len(inventories) == 1 and inventories[0]["module"] == target, "Wrong owned inventory")
inventory = inventories[0]
serialized, environment = inventory["serialized"], inventory["environment"]
names = [d["name"] for d in declarations]
require(serialized and len(serialized) == len(set(serialized)) and
        sorted(serialized) == sorted(environment), "Serialized/environment mismatch")
require(len(names) == len(set(names)) and sorted(names) == sorted(serialized),
        "Incomplete owned declaration coverage")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for row in declarations:
    require(row["module"] == target and
            all(row.get(k) is False for k in ("unsafe", "partial", "axiom")),
            "Prior owned declaration violates the original safety rules")
    require(isinstance(row.get("type"), str) and row["type"] and "⋯" not in row["type"],
            "Prior complete type is absent/truncated")
    require(isinstance(row.get("axioms"), list) and set(row["axioms"]) <= allowed,
            "Prior owned declaration has a forbidden transitive axiom")
require(len(declarations) == receipt["owned_declaration_count"] == 122, "Owned count changed")
require(sum(len(row["type"].encode()) for row in declarations) ==
        receipt["all_owned_printed_type_utf8_bytes"] == 62640, "Complete type bytes changed")
before = snapshot()
require(before["source_attempt_files"] == receipt["before"]["source_attempt_files"] and
        before["lean_sha256"] == receipt["before"]["lean_sha256"] and
        before["leanchecker_sha256"] == receipt["before"]["leanchecker_sha256"],
        "Source/object/compile evidence/tools changed after the accepted diagnostic stages")
require(before["lean_sha256"] == "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
        "Wrong Lean binary")
require(before["leanchecker_sha256"] == "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
        "Wrong independent checker binary")
require(os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 64 * 1024 * 1024,
        "Less than 64 MiB free space")

old_inspector = (previous / "InspectBlocks.lean").read_bytes()
require(hashlib.sha256(old_inspector).hexdigest() == expected_old_inspector,
        "Prior inspector source changed")
old_line = b"    | _ => none\n"
new_line = b"    | e => Lean.Meta.Sym.getNatValue? e\n"
require(old_inspector.count(old_line) == 1, "Expected exactly one old Nat fallback")
inspector = old_inspector.replace(old_line, new_line)
require(hashlib.sha256(inspector).hexdigest() == expected_new_inspector,
        "The retry contains more than the reviewed single-line Nat parser fix")
out.mkdir(parents=True, exist_ok=False)
inspector_path = out / "InspectBlocks.lean"
inspector_path.write_bytes(inspector)
env = dict(os.environ)
env["LEAN_PATH"] = str(root)
env["LEAN_SYSROOT"] = str(lean.parent.parent)
env.pop("LEAN_SRC_PATH", None)
command = [str(lean), *flags, str(inspector_path)]
result = {
    "diagnostic_only": True, "compile_credit": False, "kernel_credit": False,
    "acceptance_credit": False, "finite_A_credit": False, "full_owned_audit_credit": False,
    "scope": "supplementary block-shape inspection only; original replay/audit reused with exact bindings",
    "target_module": target, "prior_task": prior_task,
    "prior_receipt": str(receipt_path), "prior_receipt_sha256": expected_receipt,
    "source_sha256": expected_source, "object_sha256": expected_object,
    "template_sha256": template_hash, "inspector_source_sha256": expected_new_inspector,
    "original_replay_and_owned_rules_passed": True,
    "prior_stages_reused": {stage: receipt["stages"][stage] for stage in ("replay", "audit")},
    "owned_declaration_count": len(declarations), "all_owned_printed_type_utf8_bytes": 62640,
    "extra_block_shape_checks_passed": False,
    "canonical_P2_touched": False, "existing_P1_project_touched": False,
    "before": before, "command": command,
}
print(json.dumps(result, ensure_ascii=False), flush=True)
try:
    log = out / "blocks.log"
    started = time.monotonic()
    timed_out = False
    with log.open("wb") as stream:
        proc = subprocess.Popen(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
        try:
            rc = proc.wait(timeout=120)
        except subprocess.TimeoutExpired:
            timed_out = True
            proc.kill()
            rc = proc.wait()
    raw = log.read_bytes()
    sys.stdout.buffer.write(raw)
    sys.stdout.buffer.flush()
    result["blocks_stage"] = {
        "command": command, "exit_code": rc, "timed_out": timed_out,
        "elapsed_seconds": time.monotonic() - started,
        "log": str(log), "log_bytes": len(raw), "log_sha256": hashlib.sha256(raw).hexdigest(),
    }
    require(rc == 0 and not timed_out, "Supplementary inspector failed")
    blocks = rows(raw, "P24_TOY_BLOCK ")
    summaries = rows(raw, "P24_TOY_BLOCK_SUMMARY ")
    require(len(summaries) == 1 and summaries[0]["module"] == target and
            summaries[0]["owned_block_count"] == 2 and summaries[0]["shape_checks_passed"] is True,
            "Missing or failed complete block-shape summary")
    require(len(blocks) == 2 and len({b["name"] for b in blocks}) == 2, "Wrong block inventory")
    by_name = {row["name"]: row for row in declarations}
    for block in blocks:
        require(block["name"] in by_name and block["shape_checks_passed"] is True,
                "Block is absent from the bound complete owned audit or fails its shape check")
        block["printed_type_utf8_bytes"] = len(by_name[block["name"]]["type"].encode())
        block["axioms"] = by_name[block["name"]]["axioms"]
    result["blocks"] = blocks
    result["block_summary"] = summaries[0]
    result["total_block_printed_type_utf8_bytes"] = sum(b["printed_type_utf8_bytes"] for b in blocks)
    result["extra_block_shape_checks_passed"] = True
    (out / "blocks.json").write_text(json.dumps(
        {"blocks": blocks, "summary": summaries[0]}, ensure_ascii=False, indent=2) + "\n")
except (OSError, ValueError, KeyError, TypeError) as error:
    result["error"] = str(error)
finally:
    after = snapshot()
    result["after"] = after
    result["all_prior_inputs_and_artifacts_unchanged"] = before == after
    result["new_inspector_source_unchanged"] = digest(inspector_path) == expected_new_inspector
    result["diagnostic_passed"] = (result["extra_block_shape_checks_passed"] and before == after and
                                   result["new_inspector_source_unchanged"])
    (out / "diagnostic.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result, ensure_ascii=False), flush=True)
raise SystemExit(0 if result["diagnostic_passed"] else 1)
PY
