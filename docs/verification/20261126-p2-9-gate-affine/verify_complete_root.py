"""Offline root review of the exact GateAffine archive; no Lean execution."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import resource
import sys
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE / "gate-root-evidence"
EV = ROOT / "verification"
REMOTE = Path("/workspace/p29-gate-affine-20261126-ba9b1989")
PROJECT = REMOTE / "project"
OLD = HERE / "unit-tail-root-evidence"
OLD_REMOTE = Path("/workspace/p29-unit-tail-20261126-8131f7d6")
TARGET = "ImbalancedChen.P2FiniteMarkedGamma5GateAffine"
SOURCE_BLOB = "fb1ab9c164ecd705653903a57b9ee53838303de9"
SOURCE_SHA = "18967fcc3ced75318d5b8d7e6ee40153b30d6dfc8678527a6f37753550f9a6db"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def local(remote):
    return ROOT / Path(remote).relative_to(REMOTE)


def checkpoint(label):
    print(json.dumps({"offline_review_stage": label, "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}), flush=True)


archive = Path(sys.argv[1])
assert archive.stat().st_size == 3894004
assert sha(archive) == "eb39540322acb1fc4d19b7a126a80df5430fdaf81208438e6c6f1bcd1eceb99b"
checkpoint("archive_identity")
with tarfile.open(archive, "r:xz") as tar:
    members = tar.getmembers()
    names = [m.name for m in members]
    assert len(names) == len(set(names)) == 76
    assert all(m.isfile() and not PurePosixPath(m.name).is_absolute()
               and ".." not in PurePosixPath(m.name).parts for m in members)
    manifest_bytes = tar.extractfile("FILE_MANIFEST.json").read()
    assert hashlib.sha256(manifest_bytes).hexdigest() == "83c6f183ad9b228961899a842ff5bddb29c4ebabf078d0fe9e079822fe9da106"
    manifest = json.loads(manifest_bytes)
    assert len(manifest["files"]) == 75 and set(manifest["files"]) == set(names) - {"FILE_MANIFEST.json"}
    for member in members:
        data = tar.extractfile(member).read()
        assert len(data) == member.size
        if member.name in manifest["files"]:
            assert manifest["files"][member.name] == {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
        assert (ROOT / member.name).read_bytes() == data

checkpoint("all_76_archive_members")

result = read(EV / "VALIDATION_RESULTS.json")
assert result["result"] == "PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED"
assert result["module"] == TARGET and result["source_git_blob"] == SOURCE_BLOB
assert result["source_sha256"] == SOURCE_SHA and result["source_bytes"] == 10694
assert result["owned_count"] == 81
assert result["borrowed_source_recompilations"] == 0
assert result["borrowed_new_kernel_replays"] == result["borrowed_new_owned_replays"] == 0
assert result["borrowed_module_count"] == 18
assert result["successful_normal_source_invocations"] == 1 and result["failed_normal_source_invocations"] == 2
assert not result["full_P2_9_complete"] and not result["whole_standard_import_kernel_replay_claim"]
assert result["monitored_parts_unchanged"] == 21431

src = ROOT / "project" / (TARGET.replace(".", "/") + ".lean")
source = src.read_bytes()
assert sha(src) == SOURCE_SHA and len(source) == 10694
assert hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest() == SOURCE_BLOB
assert source == (HERE / "GateAffine-constructor-if-repair-v2.lean").read_bytes()
assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", source.decode())
outputs = read(EV / "SOURCE_AND_OUTPUTS_AFTER.json")
assert outputs == read(EV / "SOURCE_AND_OUTPUTS_AFTER_NORMAL.json") and len(outputs) == 3
for path, record in outputs.items():
    assert {"bytes": local(path).stat().st_size, "sha256": sha(local(path))} == record
assert sha(ROOT / "project/.lake/build/lib/lean" / (TARGET.replace(".", "/") + ".olean")) == "375947c766716ad8da5d114c395217f52fc6cc5adbe64327490b1c11aad02944"
assert not list((ROOT / "project").rglob("*.trace")) and not list((ROOT / "project").rglob("*.setup.json"))
checkpoint("source_and_outputs")

tools_expected = {
    "ci_runtime_guard.py": "837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877",
    "run_guarded.py": "c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526",
    "validate_member_roots_owned.py": "ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201",
}
for name, digest in tools_expected.items():
    assert sha(ROOT / "original-tools" / name) == digest
assert {Path(k).name:v for k,v in result["original_guard_runner_validator_unchanged"].items()} == tools_expected
prefix = ["python3", str(REMOTE / "original-tools/run_guarded.py"), "--state", str(REMOTE / "verification/runtime-evidence/state.json")]
src_remote = PROJECT / (TARGET.replace(".", "/") + ".lean")
obj_remote = PROJECT / ".lake/build/lib/lean" / (TARGET.replace(".", "/") + ".olean")
normal_command = prefix + ["lake", "env", "lean", "-DwarningAsError=true", "-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", "-o", str(obj_remote), "-i", str(obj_remote.with_suffix(".ilean")), str(src_remote)]


def stage(label, exit_code=0):
    r = read(EV / (label + "-process.json"))
    assert r["stage"] == label and r["exit_code"] == exit_code
    assert r["cwd"] == str(PROJECT) and not r["forbidden_source_calls"]
    assert sha(local(r["log_path"])) == r["log_sha256"]
    return r


normal = stage("normal-build-constructor-if-repair-v2")
assert normal == result["normal"] and normal["command"] == normal_command
assert (EV / "normal-build-constructor-if-repair-v2.log").read_bytes() == b""
first = stage("normal-build", 1)
second = stage("normal-build-proof-repair-v1", 1)
assert first["command"] == second["command"] == normal_command
assert sha(EV / "normal-build.log") == "ecac80b2a7eb89523a69b9b4eab6c65eca5dc29f91c89c268613bbfcc4fd3409"
assert sha(EV / "normal-build-proof-repair-v1.log") == "5d2382d95be6c81c60fd239bae25ba3f68ece85f44402135710edfcb0b944734"
kernel = stage("named-kernel")
assert kernel == result["kernel"] and kernel["command"] == prefix + ["lake", "env", "leanchecker", "--verbose", TARGET]
assert (EV / "named-kernel.log").read_text().splitlines() == ["replaying " + TARGET]
owned = stage("full-owned")
assert owned == result["owned"]
assert owned["command"] == prefix + ["lake", "env", "lean", "-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", "-Dpp.maxSteps=1000000", "--stdin"]
consumer = stage("consumer-actual-imports")
assert consumer["stdin_sha256"] == sha(EV / "consumer-actual-imports.lean")
direct = stage("gate-direct-imports")
assert direct["stdin_sha256"] == sha(EV / "gate-direct-imports.lean")
for label in ["runtime-initial-audit", "pinned-lean-version", "pinned-lean-prefix", "runtime-final-audit"]:
    stage(label)
checkpoint("original_runtime_stages")

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("gate_original_owned_validator", ROOT / "original-tools/validate_member_roots_owned.py")
auditor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(auditor)
code = auditor.make_audit_code([TARGET]).encode()
assert code == (EV / "full-owned.lean").read_bytes()
assert hashlib.sha256(code).hexdigest() == owned["stdin_sha256"]
decls, inventory, axioms = auditor.read_audit((EV / "full-owned.log").read_text(), [TARGET], 0)
assert decls == read(EV / "full-owned-DECLARATION_TYPES_AXIOMS.json") and len(decls) == 81
assert inventory == read(EV / "full-owned-INVENTORY_NAME_SET_CHECK.json") == result["inventory"]
assert inventory["private_name_count"] == 40
assert Counter(d["kind"] for d in decls) == {"definition": 20, "theorem": 61}
assert axioms == result["observed_axioms"] == ["Classical.choice", "Quot.sound", "propext"]
assert all(d["module"] == TARGET and d["kind"] != "axiom" and d["type_expression"] for d in decls)
assert len({d["name"] for d in decls}) == 81
source_names = re.findall(r"^(?:private )?(?:def|abbrev|theorem)\s+(\w+)", source.decode(), re.M)
assert len(source_names) == 23
explicit_names = []
for name in source_names:
    matches = [d for d in decls if d["name"] == TARGET + "." + name or d["name"] == "_private." + TARGET + ".0." + TARGET + "." + name]
    assert len(matches) == 1
    explicit_names.append(matches[0]["name"])
explicit = [d for d in decls if d["name"] in explicit_names]
generated = [d for d in decls if d["name"] not in explicit_names]
assert Counter(d["kind"] for d in explicit) == {"definition": 10, "theorem": 13}
assert len(generated) == 58
checkpoint("original_parser_81_owned")

reuse = read(EV / "REUSED_SUPPLY_QUALIFICATION.json")
assert reuse["status"] == "REUSED_PRIOR_PASS_BYTES_STABLE_NO_REQUALIFICATION"
assert sha(EV / "REUSED_SUPPLY_QUALIFICATION.json") == result["current_supply_reuse_receipt_sha256"]
assert sha(OLD / "verification/SUPPLY_QUALIFICATION.json") == result["original_supply_receipt_sha256"] == "1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21"
assert reuse["original_supply_receipt"] == read(OLD / "verification/SUPPLY_QUALIFICATION.json")
for path, digest in reuse["original_receipts"].items():
    assert sha(OLD / Path(path).relative_to(OLD_REMOTE)) == digest
old_borrows = read(OLD / "verification/BORROWED_OBJECTS.json")
borrows = read(EV / "BORROWED_OBJECTS.json")
assert set(borrows) == set(old_borrows) and len(borrows) == 18
for m, r in borrows.items():
    assert r["source_sha256"] == old_borrows[m]["source_sha256"]
    assert r["object_sha256"] == old_borrows[m]["object_sha256"]
checkpoint("original_18_supply_receipts")

old_actual = read(OLD / "verification/consumer-actual-imports-bindings.json")
old_parts = {(p["module"],p["facet"]):p["identity"] for p in old_actual["parts"]}
del old_actual
actual = read(EV / "consumer-actual-imports-bindings.json")
before = read(EV / "gate-direct-imports-bindings.json")
assert sha(EV / "consumer-actual-imports-bindings.json") == result["actual_input_bindings_sha256"]
assert sha(EV / "gate-direct-imports-bindings.json") == result["pre_normal_import_bindings_sha256"]
assert actual["roots"] == [TARGET]
assert actual["module_count"] == len(actual["actual_modules"]) == 3700
assert actual["part_count"] == len(actual["parts"]) == 18452
assert len({(p["module"],p["facet"]) for p in actual["parts"]}) == 18452
used_old = 0
for p in actual["parts"]:
    if p["module"] == TARGET:
        assert p["facet"] == ".olean" and p["identity"]["sha256"] == sha(local(obj_remote))
    else:
        v = old_parts[(p["module"],p["facet"])]
        assert (v["bytes"],v["sha256"]) == (p["identity"]["bytes"],p["identity"]["sha256"])
        used_old += 1
assert used_old == result["existing_qualified_input_parts_used"] == 18451
assert len(before["parts"]) == used_old
checkpoint("actual_import_binding_subset")
assert {p["module"] for p in actual["parts"] if p["module"].startswith("ImbalancedChen.")} == set(result["borrowed_modules_actually_used"]) | {TARGET}

guard = read(EV / "runtime-evidence/audit.json")
assert guard["status"] == "PASS_RUNTIME_GUARD_ONLY"
assert guard["state_sha256"] == sha(EV / "runtime-evidence/state.json")
assert guard["command_log_sha256"] == sha(EV / "runtime-evidence/compiler-commands.jsonl")
rows = [json.loads(line) for line in (EV / "runtime-evidence/compiler-commands.jsonl").read_text().splitlines() if line]
source_rows = [r for r in rows if r.get("tool") == "lean" and any(a.endswith(".lean") for a in r.get("input_args", []))]
assert len(source_rows) == 3
assert all([a for a in r["input_args"] if a.endswith(".lean")] == [str(src_remote)] and "-DwarningAsError=true" in r["input_args"] for r in source_rows)
assert result["normal_source_invocations"] == [str(src_remote)] * 3
first_source = (EV / "failed-target-first-normal/GateAffine-first-normal.lean").read_bytes()
second_source = (EV / "failed-target-second-normal/GateAffine-second-normal.lean").read_bytes()
assert hashlib.sha256(first_source).hexdigest() == "ba9b1989c42a681de23ad448749c0f8a1a10ae77160dabc512f664b65cfa2b55"
assert hashlib.sha256(second_source).hexdigest() == "2f9a610f56e0e9bbfc01fbefa3316c3cd1444151140c14fa8ab198a38ffb4022"
for prev, target, review_name in [(first_source,second_source,"PROOF_ONLY_REPAIR_REVIEW.json"),(second_source,source,"CONSTRUCTOR_IF_REPAIR_V2_REVIEW.json")]:
    review = read(EV / review_name)
    expected = prev.decode()
    for replacement in review["exact_replacements"]:
        assert expected.count(replacement["old"]) == 1
        expected = expected.replace(replacement["old"],replacement["new"])
    assert expected.encode() == target

report = {
    "schema": "p29_gate_root_complete_evidence_review_v1",
    "observed_utc": datetime.now(timezone.utc).isoformat(),
    "status": "COMPLETE_ARCHIVE_SOURCE_RUNTIME_AND_ORIGINAL_OWNED_PARSER_PASS",
    "source_blob": SOURCE_BLOB, "source_sha256": SOURCE_SHA,
    "archive_bytes": 3894004, "archive_sha256": sha(archive),
    "archive_members": 76, "manifest_entries": 75,
    "all_members_safe_unique_sizes_hashes_verified": True,
    "normal_exit_code": 0, "warningAsError": True, "successful_normal_log_bytes": 0,
    "normal_history": {"failed": 2, "successful": 1, "old_supplier": 0},
    "named_kernel_exit_code": 0, "full_owned_exit_code": 0,
    "owned_declarations": 81, "owned_kind_counts": dict(Counter(d["kind"] for d in decls)),
    "private_owned_count": 40, "explicit_source_declarations": 23,
    "explicit_source_theorems": 13, "explicit_source_definitions": 10,
    "compiler_generated_declarations": 58,
    "complete_all81_types_raw_expressions_universes_axioms_inventory_reparsed_with_original_validator": True,
    "all_23_source_declarations_found_once_in_owned_inventory": True,
    "observed_axioms": axioms,
    "original_guard_runner_validator_hashes": tools_expected,
    "actual_import_modules": 3700, "actual_import_facets": 18452,
    "existing_qualified_facets_matched_to_original_accepted_archive": used_old,
    "old_supply_modules_reused": 18, "old_supply_owned_reused": 394,
    "old_source_compilations": 0, "old_kernel_replays": 0, "old_owned_replays": 0,
    "source_and_outputs_verified_unchanged_after_success": outputs,
    "two_original_failed_sources_and_logs_preserved": True,
    "exact_proof_only_source_transformations_verified": True,
    "root_complete_233_line_source_and_both_failure_logs_read": True,
    "full_pretty_type_archive": "GATE_ALL_81_TYPES.txt",
    "reviewer_Lean_executions": 0,
    "whole_import_kernel_replay_claim": False,
    "full_p2_9_complete": False,
}
(HERE / "GATE_ROOT_COMPLETE_EVIDENCE_REVIEW.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
