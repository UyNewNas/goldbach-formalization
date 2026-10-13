"""New recovery fixtures; executes only actual pure Python gates extracted by AST.

No Lean/Lake/checker, subprocess, production main, source lexer, or old receipts
are executed or substituted. Temporary files are dummy Python test objects.
"""
from collections import Counter
import ast
import copy
import hashlib
import json
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[4]
RUNNER = ROOT / "verification/verify_part4_upper.py"
WORKFLOW = ROOT / ".github/workflows/part4-upper.yml"
source = RUNNER.read_text()
tree = ast.parse(source, filename=str(RUNNER))
compile(tree, str(RUNNER), "exec")
helpers = {"digest", "object_snapshot", "check_object_snapshot",
           "check_binary_snapshots", "parse_inventory"}
nodes = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in helpers]
assert {n.name for n in nodes} == helpers
ns = {"Path": Path, "hashlib": hashlib, "json": json, "Counter": Counter}
for node in tree.body:
    if isinstance(node, ast.Assign):
        for target in node.targets:
            if isinstance(target, ast.Name) and target.id in {"MODULES", "ALLOWED"}:
                ns[target.id] = ast.literal_eval(node.value)
exec(compile(ast.Module(body=nodes, type_ignores=[]), str(RUNNER), "exec"), ns)
results = []


def require(condition):
    if not condition:
        raise AssertionError("Fixture condition failed")


def check(name, action):
    action()
    results.append({"name": name, "status": "PASSED"})
    print("PASS " + name)


def rejected(action):
    try:
        action()
    except RuntimeError:
        return
    raise AssertionError("Expected production gate to reject")


modules = ns["MODULES"]
records = [{"name": m + ".fixture", "module": m, "kind": "theorem",
            "universe_parameters": [], "type": "True", "axioms": ["propext"]}
           for m in modules]
counts = [{"module": m, "count": 1} for m in modules]


def inventory(rs=None, cs=None, total=None):
    rs = records if rs is None else rs
    cs = counts if cs is None else cs
    total = len(rs) if total is None else total
    return "\n".join([*("PART4_UPPER_AUDIT_DECL " + json.dumps(r) for r in rs),
                      *("PART4_UPPER_AUDIT_MODULE " + json.dumps(c) for c in cs),
                      "PART4_UPPER_AUDIT_COUNT " + str(total)])


def bad_record(field, value):
    rs = copy.deepcopy(records)
    rs[0][field] = value
    rejected(lambda: ns["parse_inventory"](inventory(rs=rs)))


check("runner_ast_parse_and_compile", lambda: require(bool(tree.body)))
check("runner_unsealed_inventory_checkpoint", lambda: require(
    source.index('report["compiler_inventory_checked_unsealed"] = True') <
    source.index('fresh = run(') and
    source.index('(run_output / "declarations.json").write_text(') <
    source.index('fresh = run(')))
check("five_module_inventory_accept", lambda: require(ns["parse_inventory"](inventory()) == (records, counts)))
check("empty_inventory_reject", lambda: rejected(lambda: ns["parse_inventory"]("")))
check("wrong_total_reject", lambda: rejected(lambda: ns["parse_inventory"](inventory(total=6))))
check("duplicate_total_reject", lambda: rejected(lambda: ns["parse_inventory"](inventory() + "\nPART4_UPPER_AUDIT_COUNT 5")))
check("duplicate_name_reject", lambda: bad_record("name", records[1]["name"]))
check("forbidden_transitive_axiom_reject", lambda: bad_record("axioms", ["sorryAx"]))
check("axioms_nonlist_reject", lambda: bad_record("axioms", "propext"))
check("axiom_declaration_reject", lambda: bad_record("kind", "axiom"))
check("abbreviated_type_reject", lambda: bad_record("type", "True ⋯"))
check("empty_type_reject", lambda: bad_record("type", " "))
check("missing_universes_reject", lambda: bad_record("universe_parameters", None))
check("wrong_declaration_module_reject", lambda: bad_record("module", "Other"))
check("missing_module_reject", lambda: rejected(lambda: ns["parse_inventory"](inventory(cs=counts[:-1]))))
bad_counts = copy.deepcopy(counts)
bad_counts[0]["count"] = True
check("boolean_module_count_reject", lambda: rejected(lambda: ns["parse_inventory"](inventory(cs=bad_counts))))

with tempfile.TemporaryDirectory(prefix="p4-runner-fixtures-") as temporary:
    tmp = Path(temporary)
    ns["ROOT"] = tmp
    target = tmp / "Fixture.olean"
    target.write_bytes(b"dummy compiler object")
    expected = ns["object_snapshot"](target)
    check("unchanged_object_accept", lambda: ns["check_object_snapshot"](target, expected))
    target.write_bytes(b"mutated dummy object")
    check("object_byte_change_reject", lambda: rejected(lambda: ns["check_object_snapshot"](target, expected)))
    target.write_bytes(b"dummy compiler object")
    for part in ("server", "private"):
        p = target.with_suffix(".olean." + part)
        p.write_bytes(b"dummy additional part")
        check("added_" + part + "_part_reject", lambda: rejected(lambda: ns["check_object_snapshot"](target, expected)))
        with_part = ns["object_snapshot"](target)
        p.unlink()
        check("removed_" + part + "_part_reject", lambda: rejected(lambda: ns["check_object_snapshot"](target, with_part)))
    target.write_bytes(b"")
    check("empty_primary_object_reject", lambda: rejected(lambda: ns["object_snapshot"](target)))
    target.unlink()
    check("missing_primary_object_reject", lambda: rejected(lambda: ns["object_snapshot"](target)))
    binaries = {}
    for name in ("lean", "lake", "leanchecker"):
        path = tmp / name
        path.write_bytes(b"dummy executable bytes")
        binaries[name] = {"path": str(path), "sha256": ns["digest"](path)}
    check("three_unchanged_binaries_accept", lambda: ns["check_binary_snapshots"](binaries))
    for name in binaries:
        path = Path(binaries[name]["path"])
        path.write_bytes(b"changed")
        check("changed_" + name + "_binary_reject", lambda: rejected(lambda: ns["check_binary_snapshots"](binaries)))
        path.write_bytes(b"dummy executable bytes")


def marker_gate(error_text):
    candidates = [n for n in ast.walk(tree) if isinstance(n, ast.If)
                  and any(isinstance(x, ast.Constant) and isinstance(x.value, str)
                          and error_text in x.value for x in ast.walk(n))]
    candidates.sort(key=lambda n: len(list(ast.walk(n))))
    require(bool(candidates))
    return compile(ast.Module(body=[candidates[0]], type_ignores=[]), str(RUNNER), "exec")


individual = marker_gate("Missing explicit individual kernel replay evidence")
aggregate = marker_gate("Missing aggregate fresh kernel replay evidence")
for label, gate, variable, expected_marker in (
    ("individual", individual, "replay", "replaying " + modules[0]),
    ("aggregate_fresh", aggregate, "fresh", "replaying verification.Part4UpperAudit with --fresh"),
):
    context = {"module": modules[0], "audit_module": "verification.Part4UpperAudit",
               "expected": expected_marker}
    def execute_marker(value):
        exec(gate, {**context, variable: value})
    check(label + "_exact_marker_accept", lambda: execute_marker(expected_marker))
    check(label + "_missing_marker_reject", lambda: rejected(lambda: execute_marker("")))
    check(label + "_duplicate_marker_reject", lambda: rejected(lambda: execute_marker(expected_marker + "\n" + expected_marker)))

calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call)
         and isinstance(n.func, ast.Name) and n.func.id == "run"]
check("dependency_build_timeout_5400", lambda: require(any(
    any(isinstance(a, ast.Constant) and a.value == "dependencies-and-targets-build.log" for a in n.args)
    and any(k.arg == "timeout_seconds" and isinstance(k.value, ast.Constant) and k.value.value == 5400 for k in n.keywords)
    for n in calls)))
check("fresh_replay_timeout_7200", lambda: require(any(
    any(isinstance(a, ast.Constant) and a.value == "all-five-and-imports-fresh-replay.log" for a in n.args)
    and any(k.arg == "timeout_seconds" and isinstance(k.value, ast.Constant) and k.value.value == 7200 for k in n.keywords)
    for n in calls)))
workflow = WORKFLOW.read_text()
for field in ("aggregate_fresh_replay_module", "output_part_sets_and_hashes_rechecked", "toolchain_binary_hashes_rechecked"):
    check("workflow_final_gate_" + field, lambda f=field: require('report["' + f + '"]' in workflow))
check("workflow_failure_and_skip_fail", lambda: require('test "$CACHE_OUTCOME" = success' in workflow
      and 'test "$VERIFICATION_OUTCOME" = success' in workflow and 'set -euo pipefail' in workflow))
print(json.dumps({"status": "PASSED", "case_count": len(results), "cases": results,
                  "scope": "New Python-only fixtures against actual AST-extracted gates; no Lean execution",
                  "old_raw_logs_recovered": False}, ensure_ascii=False))
