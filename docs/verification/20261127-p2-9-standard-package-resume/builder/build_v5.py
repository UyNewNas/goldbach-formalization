"""Generate v5 from genuine pinned v4/probe evidence and three reviewed prefixes.

This program never executes a controller, Lean, Git, or a cloud command.
It emits nothing until the actual evidence has passed every local gate.
"""
from __future__ import annotations

import argparse
import ast
import base64
import datetime
import difflib
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import zlib

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
WORK = HERE.parent
OLD = WORK / "audit_remote/docs/verification/20261126-p2-9-omitted-P2-controller/v4-mathlib-resume"
PRIOR = WORK / "p29-observation-resume/docs/verification/20261127-p2-9-omitted-observation-resume"
PACKET = WORK / "p29-package-resume/docs/verification/20261127-p2-9-standard-package-resume"
BASE = PurePosixPath("/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77")
ROOT = BASE / "project"
V3 = BASE / "verification-import-order-resume-v3"
V4 = BASE / "verification-mathlib-path-resume-v4"
V5 = BASE / "verification-standard-package-resume-v5"
V4_VIEW = BASE / "packages-mathlib-resume-v4"
V5_VIEW = BASE / "batteries-native-cache-view-v5"
JOB = "a691a4c888044726ad49f92170e3c8f5"
SOURCE_SHA = "80e8b906621f4aae6b0677c09594618984eb005a236fe8c2432d5fd95757426d"
BOOTSTRAP_SHA = "82c546ac956193fcbcb4aaf62e32725b2ba34b761c9ef69bf9d12ce7934589cd"
CONTRACT_SHA = "1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf"
TARGET_SHA = "4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c"
# Independently supplied by the parent after the completed read-only probe.
ACTUAL_PROBE_PIN = {"bytes": 61269, "sha256": "c564b385882013f021735d18787f20af5160e152893068e8833d64ff157d31e8"}
# Exact previously reviewed, saved-before-submit request for JOB.
ACTUAL_V4_REQUEST_PIN = {"bytes": 23380, "sha256": "8090525631f9f1cb654b33cc644c71066babff815fa64aeca001faf328977fec"}
# Independently supplied after the completed original-cache read-only probe.
ACTUAL_CACHE_PROBE_PIN = {"bytes": 2729017, "sha256": "58688582f77ce9fad0536e4e2077725e9d9b80c238b38d22b686ab377798ff74"}
TARGET_REL = "ImbalancedChen/P2FiniteMarkedGamma5OmittedPrimeWall"
FROZEN_LOG = "original-v3-runtime-stage-evidence/runtime-evidence/compiler-commands.jsonl"
MISSING_LOG = b"<stdin>:29:0: error: object file '/workspace/goldbach-p2/.lake/packages/batteries/.lake/build/lib/lean/Batteries/Tactic/Lemma.olean' of module Batteries.Tactic.Lemma does not exist\n"
LIMITS = {"cwd": "/workspace", "memory_mb": 12800, "cpu_threads": 2, "timeout_seconds": 3600}
REQUIRED_FILES = ["FAILURE.json", "mathlib-package-view-lean-path-process.json", "mathlib-package-view-lean-path.log", "omitted-direct-imports-process.json", "omitted-direct-imports.log", "ACTUAL_FIRST_NAMESPACE_PATHS.json", "PACKAGE_VIEW_REPAIR.json", "runtime-evidence/state.json", FROZEN_LOG, "driver.py", "INPUT_CONTRACT.json", "SERVICE_OBSERVATION.json"]


class BuildError(ValueError):
    pass


def check(condition, message):
    if not condition:
        raise BuildError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pin(data):
    return {"bytes": len(data), "sha256": sha(data), "git_blob": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()}


def verify_bytes(data, row):
    check(isinstance(data, bytes) and isinstance(row, dict), "invalid pinned byte input")
    check(len(data) == row.get("bytes") and sha(data) == row.get("sha256"), "pinned byte length or SHA-256 mismatch")
    if "git_blob" in row:
        check(pin(data)["git_blob"] == row["git_blob"], "pinned Git blob identity mismatch")
    return data


def decode_pinned(row):
    check(isinstance(row, dict) and isinstance(row.get("base64"), str), "pinned base64 payload is required")
    try:
        data = base64.b64decode(row["base64"], validate=True)
    except Exception as error:
        raise BuildError("malformed pinned base64 payload") from error
    return verify_bytes(data, row)


def authenticate_probe(raw):
    return verify_bytes(raw, ACTUAL_PROBE_PIN)


def decode_runtime_file(row, local_bytes=None):
    data = decode_pinned(row) if "base64" in row else verify_bytes(local_bytes, row)
    if local_bytes is not None:
        check(data == local_bytes, "canonical runtime body differs from independently known authority")
    return data


def authenticate_prior_request(raw):
    verify_bytes(raw, ACTUAL_V4_REQUEST_PIN)
    return decode_request(json.loads(raw))


def read_required(path):
    check(path.is_file() and not path.is_symlink(), "required regular input is missing: " + str(path))
    return path.read_bytes()


def no_source_rows(raw):
    check(not raw or raw.endswith(b"\n"), "guard prefix must end at a complete JSONL record")
    try:
        rows = [json.loads(line) for line in raw.splitlines() if line]
    except Exception as error:
        raise BuildError("invalid guard JSONL") from error
    check(all(isinstance(row, dict) and isinstance(row.get("input_args"), list) for row in rows), "malformed guard row")
    check(all(not any(str(a).endswith(".lean") for a in row["input_args"]) for row in rows), "historical guard includes an unauthorized source call")
    return rows


def validate_guard_chain(original, combined, stage_records):
    check(combined.startswith(original), "live guard log rewrites the original v3 prefix")
    no_source_rows(original)
    no_source_rows(combined)
    position = len(original)
    appended_rows = 0
    for record in stage_records:
        check(record.get("forbidden_source_calls") == [], "historical stage has forbidden source calls")
        a, b = record.get("guard_log_start"), record.get("guard_log_end")
        check(type(a) is int and type(b) is int and a == position and a <= b <= len(combined), "historical stage guard slices have a gap or overlap")
        rows = no_source_rows(combined[a:b])
        check(rows == record.get("guarded_commands"), "historical process rows differ from exact raw guard slice")
        position = b
        appended_rows += len(rows)
    check(position == len(combined), "live guard log has an unattributed tail")
    return appended_rows


def select_historical_provider(name, record):
    roots = record.get("historical_roots")
    count = record.get("historical_facet_count")
    check(isinstance(roots, list) and len(roots) == 1 and type(count) is int and count > 0, "package requires one nonempty accepted physical origin: " + name)
    choices = []
    for candidate in record.get("candidates", []):
        if candidate.get("path") != roots[0]:
            continue
        git = candidate.get("git", {})
        top = git.get("toplevel", {})
        head = git.get("HEAD", {})
        if not (candidate.get("exists") is True and candidate.get("lib_exists") is True):
            continue
        if not (top.get("exit_code") == head.get("exit_code") == 0 and top.get("stdout") == candidate.get("resolved") and head.get("stdout") == record.get("manifest_revision")):
            continue
        if PurePosixPath(candidate["resolved"]).name != name:
            continue
        if candidate.get("historical_facets_present_by_metadata") != count or candidate.get("historical_facets_missing_by_metadata") != 0:
            continue
        choices.append(candidate)
    check(len(choices) == 1, "no unique complete pinned provider at accepted physical root: " + name)
    return choices[0]


def validate_main_only(original, changed):
    before, after = ast.parse(original), ast.parse(changed)
    mains_before = [n for n in before.body if isinstance(n, ast.FunctionDef) and n.name == "main"]
    mains_after = [n for n in after.body if isinstance(n, ast.FunctionDef) and n.name == "main"]
    check(len(mains_before) == len(mains_after) == 1, "exactly one main function is required")
    a, b = mains_before[0], mains_after[0]
    check(ast.dump(a.args) == ast.dump(b.args) and ast.dump(ast.Module(body=a.decorator_list, type_ignores=[])) == ast.dump(ast.Module(body=b.decorator_list, type_ignores=[])), "main signature changed")
    rest_before = ast.Module(body=[n for n in before.body if n is not a], type_ignores=[])
    rest_after = ast.Module(body=[n for n in after.body if n is not b], type_ignores=[])
    check(ast.dump(rest_before, include_attributes=False) == ast.dump(rest_after, include_attributes=False), "an AST outside main changed")
    before_functions = {n.name: n for n in before.body if isinstance(n, ast.FunctionDef) and n.name != "main"}
    after_functions = {n.name: n for n in after.body if isinstance(n, ast.FunctionDef) and n.name != "main"}
    check(before_functions.keys() == after_functions.keys(), "non-main function inventory changed")
    for name, node in before_functions.items():
        check(ast.get_source_segment(original, node) == ast.get_source_segment(changed, after_functions[name]), "non-main function bytes changed: " + name)
    return sorted(before_functions)


def validate_reviewed_delta(original, changed):
    before, after = ast.parse(original), ast.parse(changed)
    old_functions = {n.name: n for n in before.body if isinstance(n, ast.FunctionDef)}
    new_functions = {n.name: n for n in after.body if isinstance(n, ast.FunctionDef)}
    check(old_functions.keys() == new_functions.keys(), "controller function inventory changed")
    approved = {
        "named_kernel": ("runprefix+['lake','env','leanchecker'", "viewprefix+['leanchecker'"),
        "full_owned": ("runprefix+['lake','env','lean'", "viewprefix+['lean'"),
        "actual_inputs": ("runprefix+['lake','env','lean'", "viewprefix+['lean'"),
    }
    normalized = changed
    for name, (old_prefix, new_prefix) in approved.items():
        old_body = ast.get_source_segment(original, old_functions[name])
        new_body = ast.get_source_segment(changed, new_functions[name])
        check(old_body.count(old_prefix) == new_body.count(new_prefix) == 1, "reviewed helper prefix count differs: " + name)
        check(new_body == old_body.replace(old_prefix, new_prefix, 1), "validation body changed beyond reviewed helper prefix: " + name)
        check(new_body.replace(new_prefix, old_prefix, 1) == old_body, "helper inverse normalization differs: " + name)
        normalized = normalized.replace(new_body, old_body, 1)
    untouched = validate_main_only(original, normalized)
    old_main, new_main = old_functions["main"], new_functions["main"]
    def normal_assignment(node):
        rows = [n for n in ast.walk(node) if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "normal_cmd" for t in n.targets)]
        check(len(rows) == 1, "one normal command assignment is required")
        return rows[0]
    old_normal = ast.get_source_segment(original, normal_assignment(old_main))
    new_normal = ast.get_source_segment(changed, normal_assignment(new_main))
    check(new_normal == old_normal.replace("runprefix+['lake','env','lean'", "viewprefix+['lean'", 1), "normal command changed beyond explicit composed-view prefix")
    def final_audit(node):
        rows = [n for n in ast.walk(node) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "stage" and n.args and isinstance(n.args[0], ast.Constant) and n.args[0].value == "runtime-final-audit"]
        check(len(rows) == 1, "one original runtime final audit is required")
        return rows[0]
    check(ast.dump(final_audit(old_main), include_attributes=False) == ast.dump(final_audit(new_main), include_attributes=False), "runtime final audit must keep original runprefix and arguments")
    first_gate = " before=actual_inputs('omitted-direct-imports',source_imports)\n"
    last_gate = " stable();assert source_outputs()==produced and sha(src)==source_sha\n"
    def target_sequence(text):
        check(text.count(first_gate) == text.count(last_gate) == 1, "original target validation sequence anchors differ")
        start = text.index(first_gate)
        return text[start:text.index(last_gate, start) + len(last_gate)]
    old_sequence, new_sequence = target_sequence(original), target_sequence(changed)
    check(new_sequence.replace("normal_cmd=viewprefix+['lean'", "normal_cmd=runprefix+['lake','env','lean'", 1) == old_sequence,
          "original import/normal/kernel/owned/final-audit validation sequence changed")
    return {"normalized_prefix_helpers": sorted(approved), "byte_identical_helpers": sorted(set(untouched) - set(approved)), "non_main_AST_equal_after_exact_inverse_prefix_normalization": True,
            "original_target_validation_sequence_unchanged_except_normal_prefix": True}


def decode_request(request):
    check(set(request) == {"command", *LIMITS}, "unexpected actual request fields")
    check({k: request[k] for k in LIMITS} == LIMITS, "actual request limits changed")
    command = request["command"]
    check(isinstance(command, str) and len(command.encode()) <= 65536 and "\0" not in command, "invalid actual command")
    check(command.startswith("python3 - <<'PY'\n") and command.endswith("PY\n"), "unexpected actual command envelope")
    body = command.split("<<'PY'", 1)[1].rsplit("\nPY", 1)[0]
    tree = ast.parse(body)
    check(len(tree.body) == 5, "actual request wrapper is not the reviewed five statements")
    decoded = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "decompress":
            check(len(node.targets) == 1 and isinstance(node.targets[0], ast.Name), "unexpected payload assignment")
            try:
                payload = ast.literal_eval(node.value.args[0].args[0])
                decoded[node.targets[0].id] = zlib.decompress(base64.b64decode(payload, validate=True))
            except Exception as error:
                raise BuildError("invalid compressed request payload") from error
    check(set(decoded) == {"source", "observation"}, "actual wrapper payloads differ")
    return tree, decoded


def reusable_path_tokens(tokens, previous_paths, selected_paths):
    """Refuse stale absolute old-provider entries; receiver-relative entries stay reusable."""
    for token in tokens:
        check(isinstance(token, str) and token and "\0" not in token, "empty or invalid recorded LEAN_PATH entry")
        path = PurePosixPath(token)
        check(".." not in path.parts and not token.startswith("//"), "recorded LEAN_PATH is noncanonical or traverses a parent")
        if not path.is_absolute():
            continue
        if path.is_relative_to(ROOT / ".lake/packages"):
            continue
        for name, previous in previous_paths.items():
            if selected_paths[name] != previous and (path.is_relative_to(PurePosixPath(previous)) or path.is_relative_to(V4_VIEW / name)):
                raise BuildError("recorded LEAN_PATH has a stale absolute provider and cannot be reused without a newly authorized observation: " + name + " at " + token)


def load_context(probe_path):
    probe_raw = authenticate_probe(read_required(probe_path))
    report = json.loads(probe_raw)
    check(report.get("schema") == "p29_all_standard_package_readonly_probe_v1" and report.get("Lean_invocations") == report.get("filesystem_writes") == 0, "unexpected actual probe schema or effects")
    source = read_required(OLD / "postimage.py")
    bootstrap = read_required(OLD / "bootstrap.py")
    contract_raw = read_required(OLD.parent / "v2/INPUT_CONTRACT.json")
    check(sha(source) == SOURCE_SHA and sha(bootstrap) == BOOTSTRAP_SHA and sha(contract_raw) == CONTRACT_SHA, "reviewed controller/bootstrap/contract bytes differ")
    contract = json.loads(contract_raw)
    receipts = {
        "ACTUAL_REQUEST.json": read_required(PRIOR / "ACTUAL_REQUEST.json"),
        "FRESH_SERVICE_OBSERVATION.json": read_required(PRIOR / "FRESH_SERVICE_OBSERVATION.json"),
        "ACTUAL_TASK_JOIN.json": read_required(PRIOR / "ACTUAL_TASK_JOIN.json"),
        "V4_TERMINAL_TASK.json": read_required(PACKET / "V4_TERMINAL_TASK.json"),
        "V4_STDOUT.log": read_required(PACKET / "V4_STDOUT.log"),
        "V4_COMPLETE_OUTPUT_RESPONSE.json": read_required(PACKET / "V4_COMPLETE_OUTPUT_RESPONSE.json"),
    }
    request, observation, join, terminal = [json.loads(receipts[n]) for n in ["ACTUAL_REQUEST.json", "FRESH_SERVICE_OBSERVATION.json", "ACTUAL_TASK_JOIN.json", "V4_TERMINAL_TASK.json"]]
    request_ast, payloads = authenticate_prior_request(receipts["ACTUAL_REQUEST.json"])
    check(payloads["source"] == bootstrap and payloads["observation"] == receipts["FRESH_SERVICE_OBSERVATION.json"], "prior actual request payload identity differs")
    check(terminal.get("job_id") == terminal.get("task_id") == join.get("job_id") == JOB, "prior task identity differs")
    check(terminal.get("status") == "failed" and terminal.get("exit_code") == 1 and terminal.get("log_bytes") == len(receipts["V4_STDOUT.log"]) == 2116, "prior terminal result differs")
    check(terminal.get("log_truncated") is False and terminal.get("log_discarded_bytes") == 0, "prior stdout is incomplete")
    check({k: terminal[k] for k in LIMITS} == LIMITS == join.get("actual_limits"), "prior actual task limit binding differs")
    check(join.get("actual_submitted_at") == terminal.get("submitted_at") and join.get("observation_sha256") == sha(payloads["observation"]), "prior observation/task join differs")
    after = datetime.datetime.strptime(observation["clock_after"]["current_time"], "%Y-%m-%d %H:%M:%S UTC").replace(tzinfo=datetime.timezone.utc).timestamp()
    age = terminal["submitted_at"] - after
    check(0 <= age <= 300 and age == join.get("submission_seconds_after_observation") and join.get("submission_window_max_seconds") == 300, "prior actual submission freshness join differs")
    check(observation.get("requested_MCP_limits") == contract["MCP_limits"] and observation.get("submission_observation_max_age_seconds") == 300, "prior observation envelope differs")
    output = json.loads(receipts["V4_COMPLETE_OUTPUT_RESPONSE.json"])
    check(output.get("output", "").encode() == base64.b64decode(output["output_base64"], validate=True) == receipts["V4_STDOUT.log"] and output.get("eof") is True and output.get("next_offset") == 2116 and output.get("log_truncated") is False and output.get("discarded_bytes") == 0, "prior complete output receipt differs")
    files = report.get("files", {})
    check(set(files) == set(REQUIRED_FILES), "actual probe runtime file inventory differs")
    bodies = {}
    local_bodies = {"driver.py": source, "INPUT_CONTRACT.json": contract_raw, "SERVICE_OBSERVATION.json": payloads["observation"]}
    for name in REQUIRED_FILES:
        row = files[name]
        check(row.get("path") == str(V4 / name) and isinstance(row.get("stat"), list) and len(row["stat"]) == 5 and row["stat"][2] == row["bytes"], "v4 runtime file path/stat differs: " + name)
        bodies[name] = decode_runtime_file(row, local_bodies.get(name))
    failures = [json.loads(line[len(b"P29_FAILURE "):]) for line in receipts["V4_STDOUT.log"].splitlines() if line.startswith(b"P29_FAILURE ")]
    failure = json.loads(bodies["FAILURE.json"])
    check(failures == [failure], "probed v4 failure does not equal actual terminal stdout")
    check(failure.get("error") == "Gate failed: omitted-direct-imports" and failure.get("completed_stages") == ["mathlib-package-view-lean-path", "omitted-direct-imports"] and failure.get("supplier_source_kernel_owned_replays") == 0 and failure.get("partial_target_outputs_preserved") == {str(ROOT / (TARGET_REL + ".lean")): {"bytes": 7887, "sha256": TARGET_SHA}}, "v4 failed-stage/source-only boundary differs")
    check(bodies["omitted-direct-imports.log"] == MISSING_LOG, "v4 failed import is not the exact Batteries failure")
    state = json.loads(bodies["runtime-evidence/state.json"])
    check(state.get("root") == str(ROOT) and state.get("log") == str(V3 / "runtime-evidence/compiler-commands.jsonl") and state.get("environment", {}).get("P0_CI_GUARD_STATE") == str(V3 / "runtime-evidence/state.json"), "original state root/log/environment changed")
    check(state.get("policy") == "Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2" and state.get("action_commit") == contract["action_commit"] and state.get("guard_sha256") == contract["original_tools_members"]["original-tools/ci_runtime_guard.py"]["sha256"], "original guard/action policy changed")
    live = report["live_guard_log"]
    check(live.get("path") == state["log"], "probe live guard path differs")
    live_raw = decode_pinned(live)
    prefix = ["python3", str(BASE / "original-tools/run_guarded.py"), "--state", str(V4 / "runtime-evidence/state.json")]
    expected_commands = {
        "mathlib-package-view-lean-path": prefix + ["lake", "env", "python3", "-c", 'import os; print(os.environ["LEAN_PATH"])'],
        "omitted-direct-imports": prefix + ["lake", "env", "lean", "-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", "--stdin"],
    }
    tree = ast.parse(source)
    template = ast.literal_eval(next(n.value for n in tree.body if isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name) and n.targets[0].id == "AUDIT_TEMPLATE"))
    audit = template.replace("TARGET_MODULE_NAMES", "#[" + ", ".join("`" + name for name in contract["target"]["direct_imports"]) + "]").encode()
    stages = []
    for label, command in expected_commands.items():
        rec = json.loads(bodies[label + "-process.json"])
        check(rec.get("stage") == label and rec.get("command") == command and rec.get("cwd") == str(ROOT) and rec.get("log_path") == str(V4 / (label + ".log")) and rec.get("log_sha256") == sha(bodies[label + ".log"]), "prior stage command/log binding differs: " + label)
        check(rec.get("exit_code") == (0 if label.startswith("mathlib-") else 1) and rec.get("forbidden_source_calls") == [], "prior stage result differs: " + label)
        if label == "omitted-direct-imports":
            check(rec.get("stdin_sha256") == sha(audit), "prior failed import stdin differs")
        stages.append(rec)
    validate_guard_chain(bodies[FROZEN_LOG], live_raw, stages)
    manifest_raw = decode_pinned(report["manifest"])
    check(report["manifest"]["path"] == str(ROOT / "lake-manifest.json") and manifest_raw == base64.b64decode(contract["configuration"]["lake-manifest.json"]["postimage_base64"]), "probe manifest differs from unchanged contract")
    manifest = json.loads(manifest_raw)
    check(len(manifest["packages"]) == 10, "manifest must preserve all ten packages")
    for name in ["lean-toolchain", "lakefile.toml"]:
        check(decode_pinned(report["source_view"][name]) == base64.b64decode(contract["configuration"][name]["postimage_base64"]), "probe configuration differs: " + name)
    table = report["original_derived_facet_table"]
    check(table.get("bytes") == 23833463 and table.get("sha256") == "e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636" and table.get("path") == str(V3 / "original-external-derived/P2_DECLARED_FACETS.jsonl"), "original accepted facet table differs")
    check(report.get("package_view_link") == {"path": str(ROOT / ".lake/packages"), "is_symlink": True, "target": str(V4_VIEW)}, "owned package link is no longer the v4 view")
    repair = json.loads(bodies["PACKAGE_VIEW_REPAIR.json"])
    previous_paths = repair["selected_package_paths"]
    names = {row["name"] for row in manifest["packages"]}
    expected_previous = {name: "/workspace/compile-deps/mathlib" if name == "mathlib" else "/workspace/goldbach-p2/.lake/packages/" + name for name in names}
    check(previous_paths == expected_previous and repair.get("new_view") == str(V4_VIEW) and set(report["packages"]) == names, "original v4 ten-provider selection differs")
    selected_paths, selections = dict(previous_paths), {}
    for package in manifest["packages"]:
        name = package["name"]
        record = report["packages"][name]
        check(record.get("manifest_revision") == package["rev"], "probe package revision differs: " + name)
        if name == "LeanArchitect" or record.get("historical_facet_count") == 0:
            continue
        selected = select_historical_provider(name, record)
        selected_paths[name] = selected["path"]
        selections[name] = selected
    check(selected_paths == previous_paths, "the reviewed continuation must retain every existing v4 package provider")
    check(report["packages"]["batteries"]["historical_facet_count"] == 0 and report["packages"]["batteries"]["historical_roots"] == [], "Batteries must be supplied by its separately accepted native cache, never by a substituted stock package")
    path_record = json.loads(bodies["ACTUAL_FIRST_NAMESPACE_PATHS.json"])
    tokens = bodies["mathlib-package-view-lean-path.log"].decode().strip().split(":")
    check(tokens == path_record.get("actual_LEAN_PATH") and path_record.get("relative_path_stage_cwd") == str(ROOT), "original successful path-stage evidence differs")
    check([str(PurePosixPath(x) if PurePosixPath(x).is_absolute() else ROOT / x) for x in tokens] == path_record.get("interpreted_absolute_search_paths"), "original path interpretation differs")
    reusable_path_tokens(tokens, previous_paths, selected_paths)
    return {"probe_raw": probe_raw, "probe": report, "source": source.decode(), "contract_raw": contract_raw, "contract": contract, "receipts": receipts, "v4_bodies": bodies, "selected_paths": selected_paths, "selections": selections, "previous_paths": previous_paths, "v3_guard_prefix": bodies[FROZEN_LOG], "combined_guard_prefix": live_raw, "v4_stages": stages, "tokens": tokens}


def make_bootstrap(changes, postimage_sha):
    return ("import pathlib,hashlib\n" +
            "p=pathlib.Path(" + repr(str(V4)) + ")\n" +
            "source=(p/'driver.py').read_text()\n" +
            "assert hashlib.sha256(source.encode()).hexdigest()==" + repr(SOURCE_SHA) + "\n" +
            "changes=" + repr([(before, after) for _, before, after in changes]) + "\n" +
            "for before,after in changes:\n assert source.count(before)==1\n source=source.replace(before,after)\n" +
            "assert hashlib.sha256(source.encode()).hexdigest()==" + repr(postimage_sha) + "\n" +
            "contract=(p/'INPUT_CONTRACT.json').read_text()\n" +
            "assert hashlib.sha256(contract.encode()).hexdigest()==" + repr(CONTRACT_SHA) + "\n" +
            "cache_text=globals()['CACHE_PROBE_TEXT']\n" +
            "assert isinstance(cache_text,str) and len(cache_text.encode())==2729017 and hashlib.sha256(cache_text.encode()).hexdigest()==" + repr(ACTUAL_CACHE_PROBE_PIN["sha256"]) + "\n" +
            "exec(compile(source,'omitted-prime-wall-P2-standard-package-resume-v5.py','exec'),{'__name__':'__main__','SOURCE_TEXT':source,'SOURCE_SHA256':" + repr(postimage_sha) + ",'INPUT_CONTRACT_TEXT':contract,'CACHE_PROBE_TEXT':cache_text,'SERVICE_OBSERVATION_JSON':globals()['SERVICE_OBSERVATION_JSON'],'SERVICE_OBSERVATION_SHA256':globals()['SERVICE_OBSERVATION_SHA256']})\n").encode()


def sizing_command(bootstrap, observation, cache_probe=None):
    source_payload = base64.b64encode(zlib.compress(bootstrap, 9)).decode()
    observation_payload = base64.b64encode(zlib.compress(observation, 9)).decode()
    cache_line = "cache=globals()['CACHE_PROBE_TEXT']\n" if cache_probe is None else "cache=zlib.decompress(base64.b64decode(" + repr(base64.b64encode(zlib.compress(cache_probe, 9)).decode()) + ")).decode()\n"
    return ("python3 - <<'PY'\nimport base64,zlib,hashlib\nsource=zlib.decompress(base64.b64decode(" + repr(source_payload) + "))\nobservation=zlib.decompress(base64.b64decode(" + repr(observation_payload) + "))\n" + cache_line + "assert hashlib.sha256(source).hexdigest()==" + repr(sha(bootstrap)) + " and hashlib.sha256(observation).hexdigest()==" + repr(sha(observation)) + "\nexec(compile(source,'omitted-prime-wall-P2-standard-package-resume-v5-bootstrap.py','exec'),{'__name__':'__main__','CACHE_PROBE_TEXT':cache,'SERVICE_OBSERVATION_JSON':observation.decode(),'SERVICE_OBSERVATION_SHA256':" + repr(sha(observation)) + "})\nPY\n").encode()


def build(probe_path, output, measure_observation=None, cache_probe_path=None):
    check(probe_path.is_file(), "actual PROBE_RESULT.json is required before controller generation")
    cache_probe_path = cache_probe_path or PACKET / "CACHE_PROBE_RESULT.json"
    check(cache_probe_path.is_file(), "actual CACHE_PROBE_RESULT.json is required before controller generation")
    check(output.resolve().is_relative_to(HERE), "output must remain inside the authorized builder directory")
    check(not output.exists() and not output.is_symlink(), "output directory already exists; no overwrite")
    context = load_context(probe_path)
    from cache_inputs import load_cache_context
    context["cache_probe_raw"] = verify_bytes(read_required(cache_probe_path), ACTUAL_CACHE_PROBE_PIN)
    context["cache"] = load_cache_context(context["cache_probe_raw"])
    old_lemma = {(r["module"], r["facet"]): r["identity"] for r in context["probe"]["Batteries_Tactic_Lemma_original_rows"]}
    cache_lemma = {(r["original"]["module"], r["original"]["facet"]): r["original"]["identity"] for r in context["cache"]["rows"] if r["original"]["module"] == "Batteries.Tactic.Lemma"}
    check(len(old_lemma) == 5 and old_lemma == cache_lemma, "both genuine probes must agree on the five accepted Lemma identities")
    from main_delta import make_changes
    changes = make_changes(context)
    original = context["source"]
    postimage = original
    for label, before, after in changes:
        check(postimage.count(before) == 1, "literal replacement is not unique: " + label)
        postimage = postimage.replace(before, after)
    functions = validate_reviewed_delta(original, postimage)
    inverse = postimage
    for label, before, after in reversed(changes):
        check(inverse.count(after) == 1, "inverse replacement is not unique: " + label)
        inverse = inverse.replace(after, before)
    check(inverse == original, "whole-file inverse does not recover original v4 bytes")
    compile(postimage, "v5-postimage-syntax-only", "exec")
    postimage_raw = postimage.encode()
    bootstrap = make_bootstrap(changes, sha(postimage_raw))
    compile(bootstrap, "v5-bootstrap-syntax-only", "exec")
    patch = "".join(difflib.unified_diff(original.splitlines(keepends=True), postimage.splitlines(keepends=True), fromfile="v4/postimage.py", tofile="v5/postimage.py")).encode()
    sizing_observation = read_required(measure_observation) if measure_observation else context["receipts"]["FRESH_SERVICE_OBSERVATION.json"]
    compact_size = len(sizing_command(bootstrap, sizing_observation))
    command_size = len(sizing_command(bootstrap, sizing_observation, context["cache_probe_raw"]))
    binding = {
        "schema": "p29_standard_package_resume_v5_static_binding_v1",
        "status": "STATIC_ONLY_NOT_SUBMITTED_OR_PROOF_ACCEPTED",
        "baseline_postimage": pin(original.encode()), "unchanged_contract_sha256": CONTRACT_SHA,
        "postimage": pin(postimage_raw), "bootstrap": pin(bootstrap), "patch": pin(patch),
        "probe": pin(context["probe_raw"]), "cache_probe": {**pin(context["cache_probe_raw"]), "separate_required_artifact": "CACHE_PROBE_RESULT.json", "controller_input_global": "CACHE_PROBE_TEXT", "whole_evidence_preserved_at_runtime": "READ_ONLY_CACHE_PROBE.json"}, "prior_request_job": JOB,
        "prior_receipts": {name: pin(data) for name, data in context["receipts"].items()},
        "literal_replacements": len(changes), "replacement_labels": [label for label, _, _ in changes],
        "wholefile_inverse_exact": True, "reviewed_helper_delta": functions,
        "top_level_non_main_AST_equal_after_exact_three_prefix_inverse_normalization": True,
        "unchanged_target_source_sha256": TARGET_SHA,
        "original_v3_guard_prefix": pin(context["v3_guard_prefix"]),
        "combined_v3_v4_guard_prefix": pin(context["combined_guard_prefix"]),
        "previous_package_paths": context["previous_paths"], "selected_package_paths": context["selected_paths"],
        "changed_package_providers": sorted(name for name in context["selected_paths"] if context["selected_paths"][name] != context["previous_paths"][name]),
        "provider_selection_authority": "The unchanged accepted e9edf facet table fixes all original physical paths, sizes and SHA-256 values; every selected Batteries row must rejoin expected_origins before linking. Current cache receipt is auxiliary provenance, not qualification authority.",
        "batteries_view": {"modules": 192, "facets": 960, "only_namespace": "Batteries", "provider_lib": context["cache"]["cache_lib"], "research_namespace_529_unchanged": True, "overincluded_AnalyticNumberTheory_probe_rows_not_selected": 44, "provenance": context["cache"]["provenance"]},
        "reused_successful_stages": ["runtime-initial-audit", "pinned-lean-version", "pinned-lean-prefix", "mathlib-package-view-lean-path"],
        "old_successful_stage_reinvocations": 0,
        "path_revalidation": "The successful v4 path stage remains historical. The unchanged original raw Lake path is the tail of an explicit project/native:Batteries-only:original-path order. A new guarded Python stage must freshly observe that exact composed LEAN_PATH and cwd before the original full import/facet checks.",
        "command_transport_sizing": {"standalone_inline_all_evidence_command_bytes": command_size, "compact_bootstrap_and_observation_bytes_excluding_required_cache_blob_loader": compact_size, "maximum_bytes": 65536, "standalone_inline_within_limit": command_size <= 65536, "required_transport": "Exact Git-blob and SHA256 verified cache artifact plus compact pinned controller/bootstrap loader", "observation_bytes": len(sizing_observation), "observation_sha256": sha(sizing_observation), "observation_is_fresh_submission_authority": False, "uses_historical_observation_only_for_sizing": measure_observation is None, "fresh_final_actual_request_must_be_measured_again": True},
        "generated_owned_output": str(V5), "generated_owned_Batteries_view": str(V5_VIEW), "unchanged_owned_package_view": str(V4_VIEW),
        "runtime_or_Lean_executed_locally": False, "new_proof_credit": 0,
    }
    artifacts = {"postimage.py": postimage_raw, "bootstrap.py": bootstrap, "V4_TO_V5.patch": patch, "STATIC_BINDING.json": (json.dumps(binding, indent=2) + "\n").encode()}
    output.mkdir()
    for name, data in artifacts.items():
        with (output / name).open("xb") as stream:
            stream.write(data)
    return binding


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--probe", type=Path, default=PACKET / "PROBE_RESULT.json")
    parser.add_argument("--output", type=Path, default=HERE / "generated")
    parser.add_argument("--measure-observation", type=Path)
    parser.add_argument("--cache-probe", type=Path, default=PACKET / "CACHE_PROBE_RESULT.json")
    args = parser.parse_args()
    try:
        binding = build(args.probe, args.output, args.measure_observation, args.cache_probe)
    except (BuildError, KeyError, TypeError, ValueError) as error:
        print("V5_BUILD_BLOCKED: " + str(error), file=sys.stderr)
        return 2
    print(json.dumps({"output": str(args.output), "postimage": binding["postimage"], "bootstrap": binding["bootstrap"], "command_transport_sizing": binding["command_transport_sizing"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
