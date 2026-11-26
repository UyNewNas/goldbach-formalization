"""Independent offline review of the received original UnitTailCount evidence."""
from __future__ import annotations

from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE / "unit-tail-root-evidence"
EV = ROOT / "verification"
REMOTE = Path("/workspace/p29-unit-tail-20261126-8131f7d6")
PROJECT = REMOTE / "project"
TARGET = "ImbalancedChen.P2FiniteMarkedGamma5UnitTailCount"
SOURCE_BLOB = "5d33cb4e987efc197536d38f132a22834c3d5e46"
SOURCE_SHA = "45136f0a1ff1c46d426851d4d74e1b2b1226da6bea7522e7e31b9603bc609dde"


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def local(remote):
    return ROOT / Path(remote).relative_to(REMOTE)


transport = read(HERE / "UNIT_TAIL_ROOT_ARCHIVE_TRANSPORT.json")
assert transport["all_member_names_sizes_sha256_verified"]
assert transport["member_count"] == 128
result = read(EV / "VALIDATION_RESULTS.json")
assert result["result"] == "PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED"
assert result["module"] == TARGET
assert result["source_git_blob"] == SOURCE_BLOB and result["source_sha256"] == SOURCE_SHA
assert result["source_bytes"] == 7454 and result["owned_count"] == 26
assert result["borrowed_source_recompilations"] == 0 and result["borrowed_module_count"] == 18
assert result["successful_normal_source_invocations"] == 1
assert result["failed_normal_source_invocations"] == 1
assert result["full_P2_9_complete"] is False
assert result["whole_standard_import_kernel_replay_claim"] is False

tool_hashes = {
    "ci_runtime_guard.py": "837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877",
    "run_guarded.py": "c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526",
    "validate_member_roots_owned.py": "ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201",
}
for name, digest in tool_hashes.items():
    assert sha(ROOT / "original-tools" / name) == digest

prefix = ["python3", str(REMOTE / "original-tools/run_guarded.py"), "--state", str(REMOTE / "verification/runtime-evidence/state.json")]
src_remote = PROJECT / (TARGET.replace(".", "/") + ".lean")
obj_remote = PROJECT / ".lake/build/lib/lean" / (TARGET.replace(".", "/") + ".olean")
ile_remote = obj_remote.with_suffix(".ilean")
source = local(src_remote).read_bytes()
assert len(source) == 7454 and sha(local(src_remote)) == SOURCE_SHA
assert hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest() == SOURCE_BLOB
selected_source = HERE / "UnitTailCount-normalizer-expanded-linter-fix.lean"
if not selected_source.exists():
    selected_source = HERE.parent.parent / "source-only/20261126-p2-9-unit-tail-thin/ImbalancedChen/P2FiniteMarkedGamma5UnitTailCount.lean"
assert source == selected_source.read_bytes()
expected_outputs = {
    str(src_remote): {"bytes": 7454, "sha256": SOURCE_SHA},
    str(obj_remote): {"bytes": 323472, "sha256": "c44907c14ab5879d2217f5aad2d6d2aff3844bf365612f50c3d31726115a2645"},
    str(ile_remote): {"bytes": 38972, "sha256": "bce6f9e52e372e8fe57ef1c18e8368efa6b835f641671f6f8db9192b8eacf147"},
}
assert read(EV / "SOURCE_AND_OUTPUTS_AFTER_NORMAL.json") == expected_outputs
assert read(EV / "SOURCE_AND_OUTPUTS_AFTER.json") == expected_outputs
for name, value in expected_outputs.items():
    assert local(name).stat().st_size == value["bytes"] and sha(local(name)) == value["sha256"]


def stage(label, expected_exit=0):
    record = read(EV / (label + "-process.json"))
    assert record["stage"] == label and record["exit_code"] == expected_exit
    assert record["cwd"] == str(PROJECT) and not record["forbidden_source_calls"]
    assert sha(local(record["log_path"])) == record["log_sha256"]
    return record


normal = stage("normal-build-unused-ring-fix")
assert normal["command"] == prefix + ["lake", "env", "lean", "-DwarningAsError=true", "-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", "-o", str(obj_remote), "-i", str(ile_remote), str(src_remote)]
assert result["normal"] == normal
assert (EV / "normal-build-unused-ring-fix.log").read_bytes() == b""
kernel = stage("named-kernel")
assert kernel["command"] == prefix + ["lake", "env", "leanchecker", "--verbose", TARGET]
replayed = [line.removeprefix("replaying ") for line in (EV / "named-kernel.log").read_text().splitlines() if line.startswith("replaying ")]
assert replayed == [TARGET] and result["kernel"] == kernel
owned = stage("full-owned")
assert owned["command"] == prefix + ["lake", "env", "lean", "-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", "-Dpp.maxSteps=1000000", "--stdin"]
assert result["owned"] == owned
consumer = stage("consumer-actual-imports")
assert consumer["stdin_sha256"] == sha(EV / "consumer-actual-imports.lean")
final_guard = stage("runtime-final-audit")
assert final_guard["command"] == prefix + ["python3", str(REMOTE / "original-tools/ci_runtime_guard.py"), "audit", "--state", str(REMOTE / "verification/runtime-evidence/state.json"), "--probe", "--require-source"]
guard_audit = read(EV / "runtime-evidence/audit.json")
assert guard_audit["status"] == "PASS_RUNTIME_GUARD_ONLY"
assert guard_audit["state_sha256"] == sha(EV / "runtime-evidence/state.json")
assert guard_audit["command_log_sha256"] == sha(EV / "runtime-evidence/compiler-commands.jsonl")
guard_rows = [json.loads(line) for line in (EV / "runtime-evidence/compiler-commands.jsonl").read_text().splitlines() if line]
source_rows = [r for r in guard_rows if r.get("tool") == "lean" and any(a.endswith(".lean") for a in r.get("input_args", []))]
assert len(source_rows) == 2
assert all([a for a in r["input_args"] if a.endswith(".lean")] == [str(src_remote)] and "-DwarningAsError=true" in r["input_args"] for r in source_rows)

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("original_member_owned_validator", ROOT / "original-tools/validate_member_roots_owned.py")
auditor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(auditor)
code = auditor.make_audit_code([TARGET]).encode()
assert code == (EV / "full-owned.lean").read_bytes()
assert hashlib.sha256(code).hexdigest() == owned["stdin_sha256"]
decls, inventory, axioms = auditor.read_audit((EV / "full-owned.log").read_text(), [TARGET], owned["exit_code"])
assert decls == read(EV / "full-owned-DECLARATION_TYPES_AXIOMS.json")
assert inventory == read(EV / "full-owned-INVENTORY_NAME_SET_CHECK.json") == result["inventory"]
assert len(decls) == 26 and all(d["kind"] != "axiom" for d in decls)
assert axioms == ["Classical.choice", "Quot.sound", "propext"] == result["observed_axioms"]

borrows = read(EV / "BORROWED_OBJECTS.json")
assert len(borrows) == 18
for module, record in borrows.items():
    for path_key, hash_key in [("source", "source_sha256"), ("object", "object_sha256")]:
        assert sha(local(record[path_key])) == record[hash_key], (module, path_key)
supply = read(EV / "SUPPLY_QUALIFICATION.json")
assert sha(EV / "SUPPLY_QUALIFICATION.json") == result["current_supply_receipt_sha256"] == "1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21"
assert supply["source_recompilations"] == supply["new_manuscript_credit"] == 0
assert supply["borrowed_modules"] == sorted(borrows) and supply["owned_count"] == 394
assert supply["borrowed_object_records_sha256"] == sha(EV / "BORROWED_OBJECTS.json")
borrowed_kernel = stage("borrowed-named-kernel")
assert borrowed_kernel == supply["named_kernel"]
assert borrowed_kernel["command"] == prefix + ["lake", "env", "leanchecker", "--verbose", *sorted(borrows)]
borrowed_replayed = [line.removeprefix("replaying ") for line in (EV / "borrowed-named-kernel.log").read_text().splitlines() if line.startswith("replaying ")]
assert len(borrowed_replayed) == len(set(borrowed_replayed)) == 18 and set(borrowed_replayed) == set(borrows)
borrowed_owned = stage("borrowed-full-owned-pp1e6")
assert borrowed_owned == supply["full_owned"]
borrowed_code = auditor.make_audit_code(sorted(borrows)).encode()
assert borrowed_code == (EV / "borrowed-full-owned-pp1e6.lean").read_bytes()
assert hashlib.sha256(borrowed_code).hexdigest() == borrowed_owned["stdin_sha256"]
old_decls, old_inventory, old_axioms = auditor.read_audit((EV / "borrowed-full-owned-pp1e6.log").read_text(), sorted(borrows), borrowed_owned["exit_code"])
assert old_decls == read(EV / "borrowed-full-owned-pp1e6-DECLARATION_TYPES_AXIOMS.json")
assert old_inventory == read(EV / "borrowed-full-owned-pp1e6-INVENTORY_NAME_SET_CHECK.json") == supply["inventory"]
assert len(old_decls) == 394 and old_inventory["private_name_count"] == 24
assert old_axioms == axioms
previous = [json.loads(line.removeprefix("MEMBER_OWNED_DECL ")) for line in (EV / "borrowed-full-owned.log").read_text().splitlines() if line.startswith("MEMBER_OWNED_DECL ")]
assert len(previous) == 394
changed_pretty = []
for before, after in zip(previous, old_decls):
    assert {k: v for k, v in before.items() if k != "type"} == {k: v for k, v in after.items() if k != "type"}
    if before["type"] != after["type"]:
        changed_pretty.append(before["name"])
assert changed_pretty == ["ImbalancedChen.P2FiniteMarkedGamma5LogExtension.marginRow.eq_7"]

actual = read(EV / "consumer-actual-imports-bindings.json")
assert sha(EV / "consumer-actual-imports-bindings.json") == result["actual_input_bindings_sha256"]
assert actual["roots"] == [TARGET]
assert actual["module_count"] == 4271 == len(actual["actual_modules"])
assert actual["part_count"] == 21279 == len(actual["parts"])
assert len({(p["module"], p["facet"]) for p in actual["parts"]}) == 21279
assert {r["module"] for r in actual["actual_modules"] if r["module"].startswith("ImbalancedChen.")} == set(borrows) | {TARGET}
assert not any(r["module"].startswith(("MathlibNt.", "PrimeNumberTheoremAnd.", "Architect.")) for r in actual["actual_modules"])
for part in actual["parts"]:
    if part["module"] in borrows:
        assert part["facet"] == ".olean"
        assert part["identity"]["sha256"] == borrows[part["module"]]["object_sha256"]
    elif part["module"] == TARGET:
        assert part["facet"] == ".olean" and part["identity"]["sha256"] == expected_outputs[str(obj_remote)]["sha256"]

failed = stage("normal-build", 1)
assert "error: 'ring' tactic does nothing" in (EV / "normal-build.log").read_text()
preserved = (EV / "failed-target-normal/UnitTailCount-first-normal.lean").read_bytes()
assert len(preserved) == 7463 and hashlib.sha256(preserved).hexdigest() == "58c33dc5a5ae7747a25848c73253f0664956bc88a22bb130de9d1e3a41e19ae9"
assert hashlib.sha1(b"blob " + str(len(preserved)).encode() + b"\0" + preserved).hexdigest() == "f3c41302fc6253c52445ae6f30fdfd3abc41cc5b"
assert preserved.replace(b"      field_simp [h0.ne', (rpow_pos_of_pos h0 saving).ne'] <;> ring", b"      field_simp [h0.ne', (rpow_pos_of_pos h0 saving).ne']") == source
assert result["normal_source_invocations"] == [str(src_remote), str(src_remote)]

types_text = "\n\n".join(d["name"] + "\nkind=" + d["kind"] + "; private=" + str(d["is_private"]) + "; universes=" + json.dumps(d["universe_parameters"]) + "; axioms=" + json.dumps(d["axioms"]) + "\n" + d["type"] for d in decls) + "\n"
(HERE / "UNIT_TAIL_ALL_26_TYPES.txt").write_text(types_text)
review = {
    "schema": "p29_unit_tail_root_received_runtime_and_declaration_review_v1",
    "observed_utc": datetime.now(timezone.utc).isoformat(),
    "status": "ALL_MACHINE_EVIDENCE_CHECKS_PASS_HUMAN_TYPE_REVIEW_PENDING",
    "source_git_blob": SOURCE_BLOB,
    "source_sha256": SOURCE_SHA,
    "source_bytes": len(source),
    "outputs": expected_outputs,
    "complete_archive_members_verified": 128,
    "strict_normal_exit": normal["exit_code"],
    "normal_log_bytes": 0,
    "named_kernel_exit": kernel["exit_code"],
    "full_owned_exit": owned["exit_code"],
    "full_owned_count": len(decls),
    "private_owned_count": inventory["private_name_count"],
    "owned_kind_counts": dict(Counter(d["kind"] for d in decls)),
    "complete_inventory_types_raw_AST_universes_and_axioms_reparsed_with_original_validator": True,
    "observed_axioms": axioms,
    "actual_consumer_modules": actual["module_count"],
    "actual_consumer_facets": actual["part_count"],
    "old_suppliers_currently_qualified": 18,
    "old_supplier_owned_count": 394,
    "old_supplier_new_credit": 0,
    "old_supplier_recompiles": 0,
    "prior_pretty_reprint_changed_only_one_pretty_type": changed_pretty,
    "all_394_prior_raw_AST_universe_owner_kind_axiom_records_preserved": True,
    "failed_and_successful_target_normals": [1, 1],
    "old_source_preserved_and_exact_nine_byte_noop_repair_verified": True,
    "original_guard_runner_validator_hashes": tool_hashes,
    "complete_runtime_guard_log_verified": guard_audit,
    "whole_import_replay_claim": False,
    "full_p2_9_complete": False,
    "reviewer_Lean_executions": 0,
}
(HERE / "UNIT_TAIL_ROOT_EVIDENCE_REVIEW.json").write_text(json.dumps(review, indent=2) + "\n")
print(json.dumps(review, indent=2))
print(json.dumps({"all_owned_names": [d["name"] for d in decls], "full_pretty_types_bytes": len(types_text.encode())}, indent=2))
