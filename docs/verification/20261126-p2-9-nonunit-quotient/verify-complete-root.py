"""Offline verification of the original NonunitQuotient002 evidence.

Use the sole existing extraction. No Lean, remote process, archive repacking,
new extraction, or re-audit of accepted supplier declarations is performed.
"""
from __future__ import annotations

import ast
from collections import Counter
from datetime import datetime, timezone
import gc
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile
import tomllib

HERE = Path(__file__).resolve().parent
ARCHIVE = Path(sys.argv[1])
ROOT = Path(sys.argv[2])
REPORT = Path(sys.argv[3])
EV = ROOT / "evidence"
OLD = ROOT / "original-attempt-001"
PROJECT = Path("/workspace/p29-nonunit-quotient-20261126-0117dd4")
REMOTE_OLD = Path("/workspace/p29-nonunit-quotient-verification-20261126-0117dd4")
REMOTE_EV = REMOTE_OLD / "norm-fqn-002"
MOD = "ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient"
REL = MOD.replace(".", "/")
DIRECT = ["ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass",
          "MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform"]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        while block := f.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()


def read(path):
    with Path(path).open() as f:
        return json.load(f)


def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def local(remote):
    p = Path(remote)
    if p.is_relative_to(REMOTE_EV):
        return EV / p.relative_to(REMOTE_EV)
    if p.is_relative_to(REMOTE_OLD):
        return OLD / p.relative_to(REMOTE_OLD)
    if p.is_relative_to(PROJECT):
        return ROOT / "project" / p.relative_to(PROJECT)
    raise ValueError(f"No original archive path mapping: {p}")


assert ARCHIVE.stat().st_size == 7419000
assert sha(ARCHIVE) == "9db6e95658f7be4377b04f5affa0687df88dce03552863389d8696c6d24641bc"
manifest = read(ROOT / "COMPLETE_MEMBERS.json")
assert sha(ROOT / "COMPLETE_MEMBERS.json") == "9a0cf3eae96fb78bd63d46e4b9df6e68346c03ecaea50a498020ae11675e9de9"
assert len(manifest) == 80
seen = set()
with tarfile.open(ARCHIVE, "r|xz") as tf:
    for member in tf:
        name = member.name
        assert member.isfile() and not PurePosixPath(name).is_absolute()
        assert ".." not in PurePosixPath(name).parts and name not in seen
        seen.add(name)
        original = tf.extractfile(member)
        h = hashlib.sha256()
        total = 0
        with (ROOT / name).open("rb") as current:
            while block := original.read(1024 * 1024):
                assert current.read(len(block)) == block, name
                h.update(block)
                total += len(block)
            assert current.read(1) == b"", name
        assert total == member.size
        if name != "COMPLETE_MEMBERS.json":
            assert manifest[name] == {"bytes": total, "sha256": h.hexdigest()}, name
assert len(seen) == 81 and seen == set(manifest) | {"COMPLETE_MEMBERS.json"}
print("ROOT_PHASE all81_archive_members_verified", flush=True)

result = read(EV / "VALIDATION_RESULTS.json")
assert sha(EV / "VALIDATION_RESULTS.json") == "b818e145c7356d3ce8a5d0e34b887058996ba6a86e9010900ff19536fe83f170"
assert result["result"] == "PASS_ONE_NEW_NONUNIT_QUOTIENT_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED"
assert result["modules"] == [MOD] and result["owned_declarations"] == 17
assert result["owned_declaration_counts"] == {MOD: 17}
assert result["monitored_parts_unchanged"] == 30863
for field in ["old_source_recompilations", "old_kernel_replays", "old_owned_replays",
              "old_supplier_new_formal_credit", "new_actual_external_authorities"]:
    assert result[field] == 0, field
for field in ["supplier_import_probe_repeated", "guard_setup_repeated",
              "normal_warning_as_error_requested"]:
    assert result[field] is False, field
assert result["normal_attempts_total"] == 2
assert result["original_failed_normal_attempts"] == result["new_successful_normal_attempts"] == 1

source = (ROOT / "project" / (REL + ".lean")).read_bytes()
old_source = (EV / "ORIGINAL_SOURCE_001.lean").read_bytes()
assert len(source) == 3431 and digest(source) == "42de161d084cac904775203fb0188bcc7bc5459a9b230b53c5c405e692262d77"
assert git_blob(source) == "eeaf7a2c714da44928cc43e79780846e1e72d23b"
assert len(old_source) == 3380 and git_blob(old_source) == "0117dd4f635e04bed4a5191f06295a442975a0b4"
old_line = b"      unfold norm\n"
new_line = b"      unfold ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass.norm\n"
assert old_source.count(old_line) == source.count(new_line) == 1
assert source.replace(new_line, old_line) == old_source
assert re.findall(r"(?m)^import ([A-Za-z0-9_.]+)$", source.decode()) == DIRECT
assert source == (HERE / "NonunitQuotient-norm-fqn-002.lean").read_bytes()

outputs = read(EV / "SOURCE_AND_OUTPUTS_AFTER.json")
assert outputs == read(EV / "SOURCE_AND_OUTPUTS_AFTER_NORMAL.json") and len(outputs) == 6
for path, rec in outputs.items():
    assert rec == {"bytes": local(path).stat().st_size, "sha256": sha(local(path))}, path
object_path = ROOT / "project/.lake/build/lib/lean" / (REL + ".olean")
assert object_path.stat().st_size == 210800
assert sha(object_path) == "86ade819d9ae33358ea6ea00b419c4ddfb6727b28637145c45b1ca412a849eb8"
setup_path = ROOT / "project/.lake/build/ir" / (REL + ".setup.json")
assert setup_path.read_bytes() == (EV / "ORIGINAL_FAILED_TARGET_SETUP.json").read_bytes()
assert sha(setup_path) == "33c54776d6f0c9a4fc1973e688606a7bc6ed0cad08fbf81b698f75faace91c6c"

context = read(EV / "RESUME_CONTEXT.json")
assert sha(EV / "RESUME_CONTEXT.json") == result["resume_context_sha256"]
assert context["passed_union_modules"] == 6184 and context["passed_union_facets"] == 30820
assert not context["supplier_probe_repeated"] and not context["guard_setup_repeated"]
assert sha(EV / "driver.py") == "239b105f1da467518d3bd2c6de86e0b8934aa2196a4b976afa9566d6ee9a0536"
assert sha(OLD / "driver.py") == "c970948d0848815c2d8dd4462c506e6842efc60415df5b2a9bfc3e14c881ebba"
assert (EV / "driver.py").read_bytes() == (HERE / "nonunit-quotient-p1-norm-fqn-002-resume.py").read_bytes()
new_ast, old_ast = ast.parse((EV / "driver.py").read_text()), ast.parse((OLD / "driver.py").read_text())
def functions(tree):
    return {n.name: ast.dump(n, include_attributes=False) for n in tree.body if isinstance(n, ast.FunctionDef)}
assert functions(new_ast) == functions(old_ast) and len(functions(new_ast)) == 16
pins = context["original_record_pins"]
assert len(pins) == 43
for name, rec in pins.items():
    if name in {"runtime-evidence/compiler-commands.jsonl", "runtime-evidence/audit.json", "runtime-evidence/compiler.lock"}:
        continue
    p = OLD / name
    assert p.stat().st_size == rec["bytes"] and sha(p) == rec["sha256"], name

prefix = (EV / "ORIGINAL_GUARD_PREFIX.jsonl").read_bytes()
assert len(prefix) == 6102 and digest(prefix) == "d4c1c66275a5aeda8ac403bf01c0a2bac001236dcbfb74f90a1bd5f00aff0df1"
assert digest(prefix) == pins["runtime-evidence/compiler-commands.jsonl"]["sha256"]
assert sha(EV / "ORIGINAL_INITIAL_RUNTIME_AUDIT.json") == pins["runtime-evidence/audit.json"]["sha256"]
guard_bytes = (ROOT / "runtime-evidence/final-guard-log.jsonl").read_bytes()
assert guard_bytes.startswith(prefix)
guard = read(ROOT / "runtime-evidence/final-runtime-audit.json")
assert guard["status"] == "PASS_RUNTIME_GUARD_ONLY"
assert guard["command_log_sha256"] == digest(guard_bytes)
state_file = ROOT / "runtime-evidence/final-state.json"
assert guard["state_sha256"] == sha(state_file) == context["original_state_sha256"]
assert state_file.read_bytes() == (OLD / "runtime-evidence/state.json").read_bytes()
state = read(state_file)
assert state["policy"] == result["runtime_policy"] == read(OLD / "ORIGINAL_P1_RUNTIME_STATE.json")["policy"]
for remote, expected in state["input_sha256"].items():
    assert sha(ROOT / "config" / Path(remote).name) == expected

stages = {}
for file in EV.glob("*-process.json"):
    rec = read(file)
    assert rec["stage"] not in stages, file.name
    assert rec["exit_code"] == 0 and rec["forbidden_source_calls"] == [], file.name
    assert sha(local(rec["log_path"])) == rec["log_sha256"], file.name
    assert type(rec["guard_log_start"]) is int and type(rec["guard_log_end"]) is int
    assert 0 <= rec["guard_log_start"] <= rec["guard_log_end"] <= len(guard_bytes), file.name
    for boundary in [rec["guard_log_start"], rec["guard_log_end"]]:
        assert boundary == 0 or guard_bytes[boundary - 1:boundary] == b"\n", file.name
    segment = guard_bytes[rec["guard_log_start"]:rec["guard_log_end"]]
    assert [json.loads(line) for line in segment.splitlines() if line] == rec["guarded_commands"], file.name
    if "stdin_sha256" in rec:
        assert sha(EV / (rec["stage"] + ".lean")) == rec["stdin_sha256"]
    stages[rec["stage"]] = rec
assert set(stages) == {"normal-build", "consumer-actual-imports", "named-kernel", "full-owned", "final-stock", "runtime-final-audit"}
position = len(prefix)
stage_order = ["normal-build", "consumer-actual-imports", "named-kernel", "full-owned", "final-stock", "runtime-final-audit"]
for label in stage_order:
    assert stages[label]["guard_log_start"] == position, label
    position = stages[label]["guard_log_end"]
assert position == len(guard_bytes)
assert [row for label in stage_order for row in stages[label]["guarded_commands"]] == [json.loads(line) for line in guard_bytes[len(prefix):].splitlines() if line]
for key, label in [("normal", "normal-build"), ("kernel", "named-kernel"), ("owned", "full-owned"), ("stock", "final-stock")]:
    assert result[key] == stages[label]
normal = stages["normal-build"]
assert normal["command"][-3:] == ["lake", "build", "+" + MOD + ":olean"]
normal_log = (EV / "normal-build.log").read_text()
warnings = [line for line in normal_log.splitlines() if line.startswith("warning:")]
assert len(warnings) == result["normal_warning_count"] == 3 and warnings == result["normal_warnings"]
assert "error:" not in normal_log.lower()
assert not any("warningAsError" in arg for row in normal["guarded_commands"] for arg in row.get("input_args", []))
lake = tomllib.loads((ROOT / "config/lakefile.toml").read_text())
assert not any("warningAsError" in str(v) for v in lake.get("moreLeanArgs", []))
assert (EV / "named-kernel.log").read_text() == "replaying " + MOD + "\n"
assert stages["named-kernel"]["command"][-5:] == ["lake", "env", "leanchecker", "--verbose", MOD]
assert not any(row.get("tool") == "lean" and ("--stdin" in row.get("input_args", []) or any(a.endswith(".lean") for a in row.get("input_args", []))) for row in stages["final-stock"]["guarded_commands"])
all_rows = [json.loads(line) for line in guard_bytes.splitlines() if line]
source_calls = [str(Path(a) if Path(a).is_absolute() else Path(row["cwd"]) / a)
                for row in all_rows if row.get("tool") == "lean" for a in row.get("input_args", []) if a.endswith(".lean")]
assert source_calls == result["normal_source_invocations"] == [str(PROJECT / (REL + ".lean"))] * 2
old_failure = read(OLD / "FAILURE.json")
assert old_failure["old_evidence_changed"] == old_failure["borrowed_cache_changed"] == []
old_normal = read(OLD / "normal-build-process.json")
assert old_normal["exit_code"] == 1 and old_normal["forbidden_source_calls"] == []
assert old_normal["log_sha256"] == sha(OLD / "normal-build.log") == context["original_normal_failure_sha256"]
assert "ambiguous term" in (OLD / "normal-build.log").read_text()

tools_expected = {
    "ci_runtime_guard.py": "837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877",
    "run_guarded.py": "c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526",
    "validate_member_roots_owned.py": "ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201",
}
assert {Path(k).name: v for k, v in result["original_audited_tools_unchanged"].items()} == tools_expected
tool_root = HERE / "unit-tail-root-evidence/original-tools"
for name, expected in tools_expected.items():
    assert sha(tool_root / name) == expected
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("nonunit_original_owned_auditor", tool_root / "validate_member_roots_owned.py")
auditor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(auditor)
audit_text = auditor.make_audit_code([MOD]).encode()
assert audit_text == (EV / "full-owned.lean").read_bytes()
assert digest(audit_text) == stages["full-owned"]["stdin_sha256"]
decls, inventory, axioms = auditor.read_audit((EV / "full-owned.log").read_text(), [MOD], 0)
assert len(decls) == 17 and decls == read(EV / "full-owned-DECLARATION_TYPES_AXIOMS.json")
assert inventory == read(EV / "full-owned-INVENTORY_NAME_SET_CHECK.json")
assert inventory["module_counts"] == {MOD: 17} and inventory["private_name_count"] == 0
assert axioms == result["observed_axioms"] == ["Classical.choice", "Quot.sound", "propext"]
assert {MOD + ".eventually_nonunit_card_le", MOD + ".eventually_nonunit_quotient_le"} <= {d["name"] for d in decls}
assert all(d["kind"] != "axiom" for d in decls)
print("ROOT_PHASE source_outputs_resume_guard_and_original17_owned_parser_verified", flush=True)


class JsonStream:
    """Use the standard JSON decoder for one bounded graph row at a time."""
    def __init__(self, source):
        self.source = source
        self.buffer = ""
        self.position = 0
        self.eof = False
        self.decoder = json.JSONDecoder()

    def more(self):
        self.buffer = self.buffer[self.position:]
        self.position = 0
        block = self.source.read(65536)
        self.buffer += block
        if not block:
            self.eof = True

    def peek(self):
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position] in " \r\n\t":
                self.position += 1
            if self.position < len(self.buffer):
                return self.buffer[self.position]
            if self.eof:
                return None
            self.more()

    def expect(self, token):
        assert self.peek() == token, ("Unexpected JSON delimiter", token, self.peek())
        self.position += 1

    def value(self):
        assert self.peek() is not None, "Unexpected JSON EOF"
        while True:
            try:
                value, end = self.decoder.raw_decode(self.buffer, self.position)
            except json.JSONDecodeError:
                if self.eof:
                    raise
                self.more()
                continue
            # A scalar number may continue in the next block.
            if end == len(self.buffer) and not self.eof:
                self.more()
                continue
            # raw_decode may accept the integer prefix of a split decimal or
            # exponent (for example, "1." or "1e-"). Wait for a complete value
            # followed by a structural delimiter, rather than accepting it.
            if end < len(self.buffer) and self.buffer[end] not in " \r\n\t,]}:":
                if not self.eof:
                    self.more()
                    continue
                raise json.JSONDecodeError("Invalid value delimiter", self.buffer, end)
            self.position = end
            return value


def graph_events(path):
    with Path(path).open() as source:
        stream = JsonStream(source)
        stream.expect("{")
        seen_keys = set()
        if stream.peek() != "}":
            while True:
                key = stream.value()
                assert isinstance(key, str) and key not in seen_keys
                seen_keys.add(key)
                stream.expect(":")
                if key in {"actual_modules", "parts"}:
                    stream.expect("[")
                    if stream.peek() != "]":
                        while True:
                            yield key, stream.value()
                            if stream.peek() == "]":
                                break
                            stream.expect(",")
                    stream.expect("]")
                else:
                    yield key, stream.value()
                if stream.peek() == "}":
                    break
                stream.expect(",")
        stream.expect("}")
        assert stream.peek() is None, "Trailing JSON data"
        assert {"actual_modules", "parts"} <= seen_keys


def graph(path, expected_roots):
    metadata = {}
    index = {}
    aliases = {}
    global_row_digests = {}
    projected_row_digests = {}
    resolved_paths = set()
    rows_seen = set()
    for field, row in graph_events(path):
        if field == "actual_modules":
            module = row
            assert module["module"] not in rows_seen
            rows_seen.add(module["module"])
            assert len(module["parts"]) == len(module["part_identities"])
            for raw, bound in zip(module["parts"], module["part_identities"]):
                assert raw["path"] == bound["requested_path"]
                assert raw["resolved_path"] == bound["identity"]["path"]
                assert bound["module"] == module["module"]
                key = (bound["module"], bound["facet"])
                assert key not in projected_row_digests
                projected_row_digests[key] = digest(json.dumps(bound, sort_keys=True, separators=(",", ":")).encode())
        elif field == "parts":
            key = (row["module"], row["facet"])
            assert key not in index and not row["authority"].startswith("fresh_")
            p = Path(row["identity"]["path"])
            assert p.name == row["module"].rsplit(".", 1)[-1] + row["facet"]
            index[key] = row["identity"]["sha256"]
            assert str(p) not in resolved_paths
            resolved_paths.add(str(p))
            global_row_digests[key] = digest(json.dumps(row, sort_keys=True, separators=(",", ":")).encode())
            alias_value = {"module": row["module"], "facet": row["facet"], "sha256": row["identity"]["sha256"]}
            for path_alias in {str(p), row["requested_path"]}:
                if path_alias in aliases:
                    assert aliases[path_alias] == alias_value
                else:
                    aliases[path_alias] = alias_value
        else:
            metadata[field] = row
    assert metadata["roots"] == expected_roots
    assert len(index) == metadata["part_count"]
    assert len(rows_seen) == metadata["module_count"]
    assert rows_seen == {module for module, facet in index}
    assert projected_row_digests == global_row_digests
    assert set(projected_row_digests) == set(index)
    summary = {"modules": metadata["module_count"], "facets": metadata["part_count"]}
    gc.collect()
    print("ROOT_PHASE streamed_graph_verified " + json.dumps(summary), flush=True)
    return index, aliases, summary


before_file = OLD / "merged-supplier-actual-imports-bindings.json"
assert sha(before_file) == result["before_actual_import_bindings_sha256"] == "74a28fe0612de36a7d4df66f78af7ad5207288ec2cdf7054fc2112e75b597c69"
reuse = read(OLD / "EXACT_SUPPLIER_REUSE.json")
assert reuse["status"] == "PASS_EXACT_MERGED_INPUTS_WITHOUT_SUPPLIER_REPLAY"
assert reuse["actual_bindings_sha256"] == sha(before_file)
assert sha(OLD / "EXACT_SUPPLIER_REUSE.json") == result["exact_supplier_reuse_receipt_sha256"]
before, before_paths, before_summary = graph(before_file, DIRECT)
assert before_summary == {"modules": 6184, "facets": 30820}
del before_paths
gc.collect()
after_file = EV / "consumer-actual-imports-bindings.json"
assert sha(after_file) == result["actual_import_bindings_sha256"]
after, after_paths, after_summary = graph(after_file, [MOD])
assert {key: value for key, value in after.items() if key[0] != MOD} == before
assert {key: value for key, value in after.items() if key[0] == MOD} == {(MOD, ".olean"): sha(object_path)}
assert after_summary == {"modules": 6185, "facets": 30821}
setup = read(setup_path)
assert setup["name"] == MOD and not setup.get("options", {}).get("warningAsError", False)
matches = read(EV / "CONSUMER_SETUP_IMPORT_MATCH.json")
assert len(matches) == 1 and matches[0]["module"] == MOD
assert matches[0]["setup_sha256"] == sha(setup_path)
checked = 0
for module, groups in setup["importArts"].items():
    for group in groups:
        for path in group:
            assert path in after_paths and after_paths[path]["module"] == module
            checked += 1
assert checked == matches[0]["explicit_setup_artifact_count"] == 19198
assert sha(EV / "CONSUMER_SETUP_IMPORT_MATCH.json") == result["consumer_setup_import_match_sha256"]

# Existing suppliers retain their previously accepted identities. Their old
# declarations are not re-audited, and their evidence format is not upgraded.
assert sha(OLD / "ORIGINAL_NONUNIT_BINDING_RECEIPT.json") == "c70b4abe99b6335384c42c05e241611979a6da1119cf1e4883ee87dee42b3788"
assert sha(OLD / "ORIGINAL_NONUNIT_VALIDATION_RESULTS.json") == "9664afeec28214c01e08d54c36a8effc1259f5beb50e2c00389c58f1b490da29"
assert sha(OLD / "ORIGINAL_NONUNIT_SOURCE_AND_OUTPUTS_AFTER.json") == "94dfaa2d15bb5d4c7687b1289636b207175676f9173a4e41e4759b57616c39bc"
assert read(OLD / "ORIGINAL_NONUNIT_BINDING_RECEIPT.json")["status"] == "PASS_CURRENT_P1_EXISTING_NONUNIT_SUPPLY"
assert before[("MathlibNt.Wu2008DoubleSieve.NonunitRoughUniformCore", ".olean")] == "eb25d766e699e3e43d931758b0aa55a15d8da89b48f256bbee26064e7202713b"
assert before[("MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform", ".olean")] == "d5dcdada890ec4dc434a88a504b217db32372af941be97b722cb077116e3dc5f"
assert sha(OLD / "ORIGINAL_P1_VALIDATION_RESULTS.json") == "5742156c6b46da61149f1355c0bbe33b22cb54d803ad33b4346c1c9d6c42051f"
assert (OLD / "ORIGINAL_P1_VALIDATION_RESULTS.json").read_bytes() == (HERE / "p1-profile-root-evidence/evidence/VALIDATION_RESULTS.json").read_bytes()

report = {
    "schema": "p29_nonunit002_root_complete_evidence_review_v1",
    "observed_utc": datetime.now(timezone.utc).isoformat(),
    "status": "PASS_COMPLETE_81_MEMBERS_EXACT_SOURCE_NORMAL_KERNEL_FULL_OWNED_AND_RESUMED_BINDINGS",
    "archive_bytes": ARCHIVE.stat().st_size, "archive_sha256": sha(ARCHIVE),
    "archive_members": 81, "manifest_entries": 80,
    "manifest_sha256": sha(ROOT / "COMPLETE_MEMBERS.json"),
    "all_original_members_safe_unique_and_byte_identical_to_single_extraction": True,
    "source_blob": git_blob(source), "source_sha256": digest(source),
    "object_bytes": object_path.stat().st_size, "object_sha256": sha(object_path),
    "all_six_source_output_facets_verified": True,
    "original_failure_source_setup_and_log_preserved": True,
    "single_FQN_inverse_recovers_entire_original_source": True,
    "six_resume_stage_exits": {name: rec["exit_code"] for name, rec in stages.items()},
    "normal_warningAsError": False, "normal_warning_count": len(warnings), "normal_warnings": warnings,
    "original_record_pin_count": 43,
    "original_unchanged_archived_files_rechecked": 40,
    "original_guard_prefix_and_initial_runtime_audit_preserved_separately": True,
    "original_empty_compiler_lock_not_archived_or_claimed_reverified": True,
    "original16_controller_helpers_identical": True,
    "original_guard_prefix_bytes": len(prefix), "original_guard_prefix_sha256": digest(prefix),
    "target_source_invocations_total": 2, "failed_target_normals": 1, "successful_target_normals": 1,
    "six_stage_guard_segments_exactly_cover_entire_post_prefix_suffix": True,
    "old_source_compilations": 0, "old_kernel_owned_replays": 0,
    "supplier_union_probe_repeated": False, "guard_setup_repeated": False,
    "owned_declarations": 17, "private_owned": inventory["private_name_count"],
    "kind_counts": dict(Counter(d["kind"] for d in decls)),
    "complete_types_raw_AST_universes_axioms_and_exact_inventory_reparsed_with_unchanged_original_validator": True,
    "original_audited_tool_hashes": tools_expected, "axioms": axioms,
    "before_actual_imports": before_summary, "after_actual_imports": after_summary,
    "only_new_actual_import_part_is_exact_target_object": True,
    "actual_module_part_projections_bijective_with_full_part_inventory": True,
    "actual_graph_JSON_read_incrementally_with_standard_decoder": True,
    "setup_paths_bound_only_through_recorded_requested_or_resolved_aliases": True,
    "setup_explicit_import_artifacts_bound": checked,
    "monitored_parts_unchanged_as_recorded_by_original_controller": 30863,
    "native_original_pp_all_format_preserved_without_new_raw_AST_universe_claim": True,
    "old_supplier_new_formal_credit": 0, "root_Lean_executions": 0,
    "root_entire76_line_source_and_all17_pretty_types_previously_read": True,
    "full_p2_9_complete": False, "board_node_promoted": False,
}
REPORT.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"status": report["status"], "members": 81, "owned": 17, "before": before_summary, "after": after_summary}))
