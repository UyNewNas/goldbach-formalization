#!/usr/bin/env python3
"""Exercise only the readiness function with Python fakes; never run a driver."""
import argparse
import ast
import copy
import hashlib
import json
from pathlib import Path
import re
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
HISTORY = HERE / "snapshots/source386-before-finite-layering"
CORE = "ImbalancedChen.Part3FiniteLambdaOverLogCore"
MELLIN = "ImbalancedChen.PrimeProductsMellinExactMeanInsertion"
NORMAL_FUNCTIONS = ["require", "git_file", "pinned", "helpers", "file_binding",
                    "regular_fingerprint", "reuse_manifest", "cache_snapshot", "snapshot",
                    "preflight", "current_snapshot", "run_owner", "worker"]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fingerprint(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha(raw)}


def functions(tree):
    return {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}


def dump(node):
    return ast.dump(node, include_attributes=False)


def verify():
    before = ast.parse((HISTORY / "run_selected.py").read_bytes())
    after = ast.parse((HERE / "run_selected.py").read_bytes())
    old, new = functions(before), functions(after)
    need(all(dump(old[name]) == dump(new[name]) for name in NORMAL_FUNCTIONS),
         "normal/audit helper function AST differs")
    need(set(old) == set(new), "driver function set differs")
    changed = {name for name in old if dump(old[name]) != dump(new[name])}
    need(changed == {"selection", "source_manifest", "dependency_readiness"},
         "driver function changes exceed the reviewed revision")
    def globals_except_targets(tree):
        return [dump(n) for n in tree.body if isinstance(n, (ast.Assign, ast.AnnAssign))
                and not (isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and
                         t.id == "TARGETS" for t in n.targets))]
    need(globals_except_targets(before) == globals_except_targets(after),
         "runtime/API/guard/global bindings differ")
    ib = ast.parse((HISTORY / "install_sources.py").read_bytes())
    ia = ast.parse((HERE / "install_sources.py").read_bytes())
    ibf, iaf = functions(ib), functions(ia)
    need(set(ibf) == set(iaf) and all(dump(ibf[n]) == dump(iaf[n])
         for n in ibf if n != "install"), "installer helper changed")
    transformed = copy.deepcopy(ibf["install"])
    replacements = 0
    for node in ast.walk(transformed):
        if (isinstance(node, ast.Compare) and isinstance(node.left, ast.Call) and
            isinstance(node.left.func, ast.Name) and node.left.func.id == "len" and
            len(node.left.args) == 1 and isinstance(node.left.args[0], ast.Name) and
            node.left.args[0].id == "allowed" and len(node.comparators) == 1 and
            isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value == 5):
            node.comparators[0].value = 6
            replacements += 1
    need(replacements == 1 and dump(transformed) == dump(iaf["install"]),
         "installer changes exceed the five-to-six additive count")
    need(globals_except_targets(ib) == globals_except_targets(ia), "installer globals changed")

    payloads = {m: (ROOT / (m.replace(".", "/") + ".lean")).read_bytes() for m in [CORE, MELLIN]}
    for module, raw in payloads.items():
        need(re.findall(rb"^import ([^\r\n]+)", raw, re.M) == [b"Mathlib"],
             "pure fixture owner is not literally Mathlib-only: " + module)
    cases = []
    def case(name, order, change=None, expected_pass=True, expected_guard=1, project_targets=None):
        local_payloads = dict(payloads)
        spec = SimpleNamespace(order=list(order), active_dependency_closure=set(order),
            fixed_dependencies=[], suppliers={}, readiness_targets=list(project_targets or []),
            input_bindings={"source_commit": "f" * 40},
            sources={m: sha(b) for m, b in local_payloads.items()}, baseline={"stable": True})
        command = {"exit_code": 0, "actual_built_modules": [], "actual_failed_modules": []}
        state = {"snapshot_count": 0, "guards": [], "runs": [], "saves": [], "git_reads": [],
                 "drift_before": False, "drift_after": False}
        if change:
            change(spec, local_payloads, command, state)
        def snapshot(s, received):
            need(received is spec, "unexpected spec")
            state["snapshot_count"] += 1
            if ((state["snapshot_count"] == 1 and state["drift_before"]) or
                (state["snapshot_count"] > 1 and state["drift_after"])):
                return {"stable": False}
            return spec.baseline
        def git_file(commit, path):
            need(commit == spec.input_bindings["source_commit"], "wrong committed-source binding")
            state["git_reads"].append(path)
            module = path[:-5].replace("/", ".")
            return local_payloads[module]
        def guard(lane, arguments):
            need(lane == 0, "guard lane changed")
            state["guards"].append(list(arguments))
            return ["FAKE_GUARD_ONLY"] + list(arguments)
        def run(folder, label, arguments, cwd):
            need(arguments[0] == "FAKE_GUARD_ONLY" and label == "dependency-stock-readiness",
                 "unguarded readiness command")
            state["runs"].append(arguments)
            return command
        fake = SimpleNamespace(
            api=SimpleNamespace(sha=sha),
            h=SimpleNamespace(module_path=lambda m: m.replace(".", "/") + ".lean",
                              imports=lambda b: [w for line in re.findall(rb"^import ([^\r\n]+)", b, re.M)
                                                 for w in line.decode().split()], guard=guard),
            ops=SimpleNamespace(run=run),
            d=SimpleNamespace(save=lambda path, value: state["saves"].append((str(path), value))))
        namespace = {"require": need, "current_snapshot": snapshot, "git_file": git_file,
                     "PROJECT": Path("/FAKE_PROJECT_NOT_EXECUTED")}
        only_function = ast.Module(body=[copy.deepcopy(new["dependency_readiness"])], type_ignores=[])
        exec(compile(ast.fix_missing_locations(only_function), "<readiness fixture only>", "exec"), namespace)
        failure = None
        try:
            result = namespace["dependency_readiness"](fake, spec, Path("/FAKE_RUN_NOT_WRITTEN"))
        except (ValueError, KeyError) as error:
            failure = str(error)
        need((failure is None) == expected_pass, "wrong fixture outcome: " + name)
        need(len(state["guards"]) == len(state["runs"]) == expected_guard,
             "wrong guarded-command count: " + name)
        need(len(state["saves"]) == (1 if expected_pass else 0), "failed fixture wrote a success receipt")
        for arguments in state["guards"]:
            expected = ["lake", "--no-build", "build"] + ["+" + m + ":olean"
                        for m in (project_targets or ["Mathlib"])]
            need(arguments == expected and len(arguments) > 3, "bare/default/wrong readiness targets")
        if expected_pass:
            need(result["stock_readiness_performed"] and not result["fresh_dependency_acceptance"],
                 "readiness outcome was promoted to fresh acceptance")
            if not project_targets:
                need(len(state["git_reads"]) == len(order), "not all pure committed sources checked")
        cases.append({"name": name, "expected": "PASS" if expected_pass else "HOLD",
                      "observed": "PASS" if failure is None else "HOLD", "guarded_fake_commands": expected_guard})

    case("Core only", [CORE])
    case("Mellin only", [MELLIN])
    case("Core and Mellin", [CORE, MELLIN])
    case("same pure subset reversed", [MELLIN, CORE])
    case("empty selection", [], expected_pass=False, expected_guard=0)
    case("duplicate selection", [CORE, CORE], expected_pass=False, expected_guard=0)
    case("unknown empty-dependency owner", ["ImbalancedChen.P1OriginalSingletonAtlasProperPower"],
         expected_pass=False, expected_guard=0)
    case("extra active module", [CORE], lambda s,p,c,t: s.active_dependency_closure.add(MELLIN), False, 0)
    case("fixed dependency present", [CORE], lambda s,p,c,t: s.fixed_dependencies.append("x"), False, 0)
    case("P3 supplier present", [CORE], lambda s,p,c,t: s.suppliers.update({"x": {}}), False, 0)
    case("committed source hash mismatch", [CORE], lambda s,p,c,t: s.sources.update({CORE: "0" * 64}), False, 0)
    def wrong_import(spec, data, command, state):
        data[CORE] = data[CORE].replace(b"import Mathlib\n", b"import Mathlib.Data.Nat.Basic\n", 1)
        spec.sources[CORE] = sha(data[CORE])
    case("hash-matching nonliteral import", [CORE], wrong_import, False, 0)
    case("before snapshot drift", [CORE], lambda s,p,c,t: t.update(drift_before=True), False, 0)
    case("after snapshot drift", [CORE], lambda s,p,c,t: t.update(drift_after=True), False, 1)
    case("stock nonzero exit", [CORE], lambda s,p,c,t: c.update(exit_code=1), False, 1)
    case("stock built a module", [CORE], lambda s,p,c,t: c.update(actual_built_modules=["Mathlib"]), False, 1)
    case("stock reported failure", [CORE], lambda s,p,c,t: c.update(actual_failed_modules=["Mathlib"]), False, 1)
    case("existing project-dependency branch", ["ImbalancedChen.P1OriginalSingletonAtlasProperPower"],
         project_targets=["ImbalancedChen.ExistingDependencyFixture"])
    return {"schema": "p15_six_owner_pure_readiness_python_fixtures_v1",
            "status": "PASS_PURE_PYTHON_FIXTURES_NO_DRIVER_OR_LEAN_EXECUTION",
            "runner": fingerprint(HERE / "run_selected.py"),
            "installer": fingerprint(HERE / "install_sources.py"),
            "fixture": fingerprint(Path(__file__)), "case_count": len(cases), "cases": cases,
            "unchanged_normal_audit_function_ASTs": NORMAL_FUNCTIONS,
            "changed_driver_functions": sorted(changed),
            "runtime_API_guard_global_bindings_unchanged": True,
            "installer_only_allowed_count_changed_5_to_6": True,
            "real_guard_calls": 0, "real_command_calls": 0, "Lean_or_Lake_invocations": 0,
            "cloud_tasks": 0, "cache_writes": 0, "new_Lean_acceptance": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-report", action="store_true")
    args = parser.parse_args()
    result = verify()
    output = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.write_report:
        (HERE / "PURE_READINESS_FIXTURES.json").write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
