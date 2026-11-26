"""Root offline verification of the original P1 Profile/Natural evidence.

No Lean processes and no remote writes. The unchanged original auditor is
reused from the already accepted UnitTailCount evidence archive.
"""
from __future__ import annotations

from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import lzma
from pathlib import Path, PurePosixPath
import sys
import tarfile
import tempfile
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE / "p1-profile-root-evidence"
EV = ROOT / "evidence"
PROJECT = Path("/workspace/p29-radial-profile-20261125-pinbind-v4")
REMOTE_EV = Path("/workspace/p29-radial-profile-verification-20261125-pinbind-v4")
MODS = ["ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar",
        "ImbalancedChen.P2FiniteMarkedGamma5RadialNaturalMass"]
EXPECTED = {
    MODS[0]: ("33196c7c3fc1c4aeac651871482bb142e55deca8", 7253,
              "64959b49ba41fc30534bcbd7d31d97ba8dd803ff7361ef97b69ec24f3297f93d",
              "8bf33f1accd630a46443e59d76a1d82e4dccdf9f19b65fedcc6a8cd2943d6382"),
    MODS[1]: ("5a22a4e7aeb47b39b7052e9a184703d577e5c112", 4148,
              "4cb852104310b03c4c1941d997558d9997de9ba8fe4cd3f503f00308a9d2affc",
              "c88fabed163ecad1fefefaa237c73a36c4d9e9ce2ba57438c4a174e45a7a9a28"),
}


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text())


def local(remote):
    p = Path(remote)
    if p.is_relative_to(REMOTE_EV):
        return EV / p.relative_to(REMOTE_EV)
    if p.is_relative_to(PROJECT):
        return ROOT / "project" / p.relative_to(PROJECT)
    raise ValueError(f"No archived path mapping: {p}")


archive = Path(sys.argv[1])
assert archive.stat().st_size == 8471860
assert sha(archive) == "7c2c5247f23b5f80627bfb17b13969fd9d1205601d7b6ec215734dfe960e9ccc"
metadata = read(HERE / "P1_COMPLETE_PRESET9_TRANSFER_METADATA.json")
assert metadata["same_original_tar_bytes_verified"] and not metadata["tar_repacked"]
ROOT.mkdir(exist_ok=True)
with tempfile.TemporaryFile(dir=ROOT.resolve().parent) as tar_bytes:
    digest = hashlib.sha256()
    count = 0
    with lzma.open(archive, "rb") as inp:
        while chunk := inp.read(8 * 1024 * 1024):
            count += len(chunk)
            digest.update(chunk)
            tar_bytes.write(chunk)
    assert count == metadata["tar_bytes"] == 186204160
    assert digest.hexdigest() == metadata["tar_sha256"] == "7c2aadacf6124b2b95d17b480633ff79403422e9771eb549887c0be6d8ff646a"
    tar_bytes.seek(0)
    with tarfile.open(fileobj=tar_bytes, mode="r:") as tar:
        members = tar.getmembers()
        names = [m.name for m in members]
        assert len(names) == len(set(names)) == 85
        assert sorted(names) == sorted(metadata["member_names"])
        assert all(m.isfile() and not PurePosixPath(m.name).is_absolute()
                   and ".." not in PurePosixPath(m.name).parts for m in members)
        manifest_bytes = tar.extractfile("COMPLETE_MEMBERS.json").read()
        assert sha_bytes(manifest_bytes) == "a12bacd2b5c944c05487784b298fba9885caaee40d845f62d8591dfebeec8aa4"
        manifest = json.loads(manifest_bytes)
        assert len(manifest) == 84
        assert set(manifest) == set(names) - {"COMPLETE_MEMBERS.json"}
        for m in members:
            data = tar.extractfile(m).read()
            assert len(data) == m.size
            if m.name in manifest:
                assert manifest[m.name] == {"bytes": len(data), "sha256": sha_bytes(data)}, m.name
            path = ROOT / m.name
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.exists():
                assert path.read_bytes() == data, path
            else:
                path.write_bytes(data)

portable = HERE / "p1-profile-qualified-portable"
portable_manifest = read(portable / "MEMBERS.json")
assert len(portable_manifest) == 50
for name, record in portable_manifest.items():
    assert name in manifest and manifest[name] == record
    assert (portable / name).read_bytes() == (ROOT / name).read_bytes()

result = read(EV / "VALIDATION_RESULTS.json")
assert result["result"] == "PASS_TWO_NEW_CONSUMERS_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED"
assert result["modules"] == MODS and result["owned_declarations"] == 21
assert result["owned_declaration_counts"] == {MODS[0]: 14, MODS[1]: 7}
assert result["recompiled_old_project_or_native_sources"] == 0
assert result["monitored_parts_unchanged"] == 30953
assert not result["all_import_replay_claim"]
assert not result["borrowed_kernel_replayed_in_resume"]
assert not result["borrowed_actual_import_probe_repeated"]

outputs = read(EV / "SOURCE_AND_OUTPUTS_AFTER.json")
assert outputs == read(EV / "SOURCE_AND_OUTPUTS_AFTER_NORMAL.json")
assert len(outputs) == 12
for remote, record in outputs.items():
    path = local(remote)
    assert record == {"bytes": path.stat().st_size, "sha256": sha(path)}
for module, (blob, size, digest, object_digest) in EXPECTED.items():
    src = ROOT / "project" / (module.replace(".", "/") + ".lean")
    data = src.read_bytes()
    assert len(data) == size and sha_bytes(data) == digest
    assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == blob
    assert sha(ROOT / "project/.lake/build/lib/lean" / (module.replace(".", "/") + ".olean")) == object_digest

stage_records = {}
for path in EV.glob("*-process.json"):
    rec = read(path)
    if "log_path" in rec:
        assert sha(local(rec["log_path"])) == rec["log_sha256"], path.name
    assert rec["exit_code"] == 0, path.name
    assert not rec.get("forbidden_source_calls", []), path.name
    label = rec.get("stage", path.name.removesuffix("-process.json"))
    if "stage" not in rec:
        assert label == "runtime-setup"
        assert sha(EV / "runtime-setup.log") == rec["log_sha256"]
    stage_records[label] = rec
for key, label in [("normal", "normal-build"), ("kernel", "named-kernel"),
                   ("owned", "full-owned"), ("stock", "final-stock")]:
    assert result[key] == stage_records[label]
normal = stage_records["normal-build"]
normal_log = (EV / "normal-build.log").read_text()
assert normal["command"][-4:] == ["lake", "build", "+" + MODS[0] + ":olean", "+" + MODS[1] + ":olean"]
normal_source_rows = [x for x in normal["guarded_commands"] if x.get("tool") == "lean"
                      and any(a.endswith(".lean") for a in x.get("input_args", []))]
assert len(normal_source_rows) == 2
assert all(not any("warningAsError" in a for a in row["input_args"]) for row in normal_source_rows)
lake = tomllib.loads((ROOT / "config/lakefile.toml").read_text())
assert not any("warningAsError" in str(v) for v in lake.get("moreLeanArgs", []))
warnings = [line for line in normal_log.splitlines() if "warning:" in line.lower()]
assert not any("error:" in line.lower() for line in normal_log.splitlines())
for module in MODS:
    setup = read(ROOT / "project/.lake/build/ir" / (module.replace(".", "/") + ".setup.json"))
    assert setup["name"] == module and setup["options"] == {}

kernel_log = (EV / "named-kernel.log").read_text()
replayed = [line.removeprefix("replaying ") for line in kernel_log.splitlines() if line.startswith("replaying ")]
assert len(replayed) == len(set(replayed)) == 2 and set(replayed) == set(MODS)
assert result["kernel"]["command"][-6:] == ["lake", "env", "leanchecker", "--verbose", *MODS]
assert not any(row.get("tool") == "lean" and ("--stdin" in row.get("input_args", [])
    or any(a.endswith(".lean") for a in row.get("input_args", []))) for row in result["stock"]["guarded_commands"])

tools_expected = {
    "ci_runtime_guard.py": "837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877",
    "run_guarded.py": "c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526",
    "validate_member_roots_owned.py": "ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201",
}
assert {Path(k).name: v for k, v in result["original_audited_tools_unchanged"].items()} == tools_expected
tool_root = HERE / "unit-tail-root-evidence/original-tools"
for name, digest in tools_expected.items():
    assert sha(tool_root / name) == digest
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("profile_original_member_auditor", tool_root / "validate_member_roots_owned.py")
auditor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(auditor)


def audit(label, mods, expected_count):
    process = stage_records[label]
    code = auditor.make_audit_code(mods).encode()
    assert code == (EV / (label + ".lean")).read_bytes()
    assert sha_bytes(code) == process["stdin_sha256"]
    decls, inventory, axioms = auditor.read_audit((EV / (label + ".log")).read_text(), mods, process["exit_code"])
    assert len(decls) == expected_count
    assert decls == read(EV / (label + "-DECLARATION_TYPES_AXIOMS.json"))
    assert inventory == read(EV / (label + "-INVENTORY_NAME_SET_CHECK.json"))
    assert all(d["kind"] != "axiom" for d in decls)
    assert axioms == ["Classical.choice", "Quot.sound", "propext"]
    return decls, inventory, axioms


decls, inventory, axioms = audit("full-owned", MODS, 21)
assert inventory["module_counts"] == result["owned_declaration_counts"]
assert inventory["private_name_count"] == 0
assert Counter(d["kind"] for d in decls) == {"definition": 6, "theorem": 15}
assert axioms == result["observed_axioms"]
supply = read(EV / "P2_CURRENT_P1_QUALIFICATION.json")
assert sha(EV / "P2_CURRENT_P1_QUALIFICATION.json") == result["P2_current_P1_supply_qualification_sha256"]
assert len(supply["borrowed_objects"]) == 17
supply_mods = supply["P2_modules_requalified"]
assert len(supply_mods) == 12 and supply["P1_old_modules_with_changed_actual_inputs_requalified"] == []
old_decls, old_inventory, old_axioms = audit("borrowed-full-owned-pp1e6", supply_mods, 327)
assert supply["owned_declarations"] == 327
assert supply["owned"] == stage_records["borrowed-full-owned-pp1e6"]
assert supply["kernel"] == stage_records["borrowed-named-kernel"]
old_replayed = [line.removeprefix("replaying ") for line in (EV / "borrowed-named-kernel.log").read_text().splitlines() if line.startswith("replaying ")]
assert len(old_replayed) == len(set(old_replayed)) == 12 and set(old_replayed) == set(supply_mods)
original_decls = [json.loads(line.removeprefix("MEMBER_OWNED_DECL ")) for line in (EV / "borrowed-full-owned.log").read_text().splitlines() if line.startswith("MEMBER_OWNED_DECL ")]
assert len(original_decls) == 327
changed = []
for before, after in zip(original_decls, old_decls):
    assert {k:v for k,v in before.items() if k != "type"} == {k:v for k,v in after.items() if k != "type"}
    if before["type"] != after["type"]:
        changed.append(before["name"])
assert changed == ["ImbalancedChen.P2FiniteMarkedGamma5LogExtension.marginRow.eq_7"]
comparison = read(EV / "P1_FIVE_IMPORT_COMPARISON.json")
assert len(comparison["modules"]) == 5 and comparison["affected_modules"] == comparison["drift"] == []
assert comparison["all_original_facet_bytes_preserved"]

guard = read(EV / "runtime-evidence/audit.json")
assert guard["status"] == "PASS_RUNTIME_GUARD_ONLY"
assert guard["state_sha256"] == sha(EV / "runtime-evidence/state.json")
assert guard["command_log_sha256"] == sha(EV / "runtime-evidence/compiler-commands.jsonl")
guard_bytes = (EV / "runtime-evidence/compiler-commands.jsonl").read_bytes()
old_prefix = (EV / "ORIGINAL_GUARD_LOG_PREFIX.jsonl").read_bytes()
assert len(old_prefix) == 5232 and sha_bytes(old_prefix) == "399761ebf8a3f51008311aaaedf3992863bef89eebba4694e89d2c28617d3e29"
assert guard_bytes.startswith(old_prefix)
guard_rows = [json.loads(line) for line in guard_bytes.splitlines() if line]
source_calls = [str(PROJECT / a) if not Path(a).is_absolute() else a for row in guard_rows if row.get("tool") == "lean" for a in row.get("input_args", []) if a.endswith(".lean")]
assert source_calls == result["normal_source_invocations"] == [str(PROJECT / (m.replace(".", "/") + ".lean")) for m in MODS]
assert sha(EV / "driver.py") == "ceb4f796dc7a362e47ae49fb0a2300f425c769500610e7c8baa09a6580b2170e"
assert sha(EV / "driver-pp1e6-resume.py") == "fad03cf7d93979bdaab9dfb681089ea1bc581a31860b0f469b0c59bcb140964a"
context = read(EV / "PP_MAX_STEPS_RESUME_CONTEXT.json")
assert sha(EV / "PP_MAX_STEPS_RESUME_CONTEXT.json") == result["resume_context_sha256"]
assert sha(EV / "PP_MAX_STEPS_RESOLUTION.json") == result["pp_max_steps_resolution_sha256"]
assert sha(EV / "FAILURE.json") == context["original_failure_sha256"]
assert sha(EV / "borrowed-full-owned.log") == context["original_log_sha256"]

actual = read(EV / "consumer-actual-imports-bindings.json")
assert sha(EV / "consumer-actual-imports-bindings.json") == result["actual_import_bindings_sha256"]
assert actual["roots"] == MODS
assert len(actual["parts"]) == actual["part_count"]
assert len(actual["actual_modules"]) == actual["module_count"]
assert len({(x["module"],x["facet"]) for x in actual["parts"]}) == actual["part_count"]
part_by_path = {x["identity"]["path"]: x for x in actual["parts"]}
for match in read(EV / "CONSUMER_SETUP_IMPORT_MATCH.json"):
    path = local(match["setup_path"])
    assert sha(path) == match["setup_sha256"]
    setup = read(path)
    n = 0
    for module, groups in setup["importArts"].items():
        for group in groups:
            for remote in group:
                assert remote in part_by_path and part_by_path[remote]["module"] == module
                if Path(remote).is_relative_to(PROJECT) and local(remote).exists():
                    assert sha(local(remote)) == part_by_path[remote]["identity"]["sha256"]
                n += 1
    assert n == match["explicit_setup_artifact_count"]
assert sha(EV / "CONSUMER_SETUP_IMPORT_MATCH.json") == result["consumer_setup_import_match_sha256"]

report = {
    "schema": "p29_profile_natural_root_complete_evidence_review_v1",
    "observed_utc": datetime.now(timezone.utc).isoformat(),
    "status": "COMPLETE_ARCHIVE_AND_ORIGINAL_PARSER_CHECKS_PASS",
    "transport_archive_bytes": archive.stat().st_size,
    "transport_archive_sha256": sha(archive),
    "original_tar_bytes": count,
    "original_tar_sha256": metadata["tar_sha256"],
    "archive_members": 85, "manifest_entries": 84,
    "all_members_safe_unique_sizes_and_hashes_verified": True,
    "all_50_previously_received_portable_members_identical": True,
    "sources_and_all_twelve_output_facets_verified": True,
    "normal_exit_code": normal["exit_code"],
    "normal_warningAsError_requested": False,
    "normal_log_sha256": sha(EV / "normal-build.log"),
    "normal_warning_lines": warnings,
    "normal_source_calls": len(source_calls),
    "old_source_compilations": 0,
    "named_kernel_exit_code": result["kernel"]["exit_code"],
    "full_owned_exit_code": result["owned"]["exit_code"],
    "owned_declarations": 21,
    "owned_module_counts": inventory["module_counts"],
    "owned_kind_counts": dict(Counter(d["kind"] for d in decls)),
    "private_owned_count": 0,
    "full_types_raw_AST_universes_axioms_inventory_reparsed_with_unchanged_original_validator": True,
    "observed_axioms": axioms,
    "old_borrowed_modules": 17,
    "original_P2_named_roots_replayed_before_resume": 12,
    "old_P1_roots_reused_without_replay": 5,
    "old_P2_owned_records_complete": 327,
    "old_nonpretty_records_identical": 327,
    "old_other_pretty_records_identical": 326,
    "old_changed_pretty_names": changed,
    "no_old_kernel_or_import_probe_repeated_in_resume": True,
    "actual_import_modules": actual["module_count"],
    "actual_import_facets": actual["part_count"],
    "monitored_facets_unchanged": 30953,
    "original_guard_runner_validator_hashes": tools_expected,
    "offline_validator_reused_from_existing_accepted_unit_archive": True,
    "reviewer_Lean_processes": 0,
    "whole_import_fresh_kernel_replay_claim": False,
    "root_full_sources_and_all21_types_previously_read": True,
    "scope": "Original fixed-split ambient profile radial outer mass and exact natural labelled tuple sum transport. Width precedes N and all bounded ranks/logQ; repeats and complete tuple carrier retained. No complete history/J/additive-prime/signed-PP claim.",
    "full_p2_9_complete": False,
}
(HERE / "P1_PROFILE_ROOT_COMPLETE_EVIDENCE_REVIEW.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
print("ORIGINAL_NORMAL_LOG_BEGIN\n" + normal_log + "ORIGINAL_NORMAL_LOG_END")
