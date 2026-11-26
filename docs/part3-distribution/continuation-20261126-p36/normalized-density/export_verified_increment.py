#!/usr/bin/env python3
"""Seal or locally verify completed P3.6 increment evidence without running Lean."""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha1, sha256
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
DEFAULT_PROJECT = next((parent for parent in Path(__file__).resolve().parents
                        if (parent / "verification/p36/compile_p36_local.py").is_file()), Path.cwd())
OWNERS = tuple("ImbalancedChen." + stem for stem in (
    "P3OriginalU5NormalizedDensityReserve", "P3OriginalU5RoundedPairDensity",
    "P3OriginalU5PairNormalizedDensityReserve"))
COMPILER_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
CHECKER_SHA256 = "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
SHA256 = re.compile(r"[0-9a-f]{64}")
RUN_NAME = re.compile(r"\d{8}T\d{6}\.\d{6}Z")
HELPER_DIGESTS = {
    "exported_evidence/verify_and_install.py": "131799ef5a29a0c719183518732ef25614fe872d6f6896a5d2d16644eeb42cf3",
    "verify_warm_common_parameters.py": "51bf36b212cd9de1168c6ee0900638c0def43f99fd677c2f70e78375e51be0f1",
}

# Exact report pins from the independently read P1 lineage diagnostic.
LEGACY_RUNS = PurePosixPath("/workspace/p36-original-u5-20261125/.lake/p36-build/runs")
LEGACY_REPORT_PINS = {
    LEGACY_RUNS / run / "report.json": (writer, digest)
    for writer, reports in {
        "229fbe9720e65982fd0241b7ddafe7f06e8894e19d128a6ac4ea255860945de9": {
            "20261125T084935.166056Z": "9ea0377b9bd86226e4a4e521fa9252112bef9d9035077e729587e198a2b966de",
        },
        "3ca5c1e971324ea770e0494fbbabcdc162c0cf9db036816e6d692cb24cdfa733": {
            "20261125T092212.672586Z": "8f09ff2ede080ef8dffeef4c121e92c0a878830246196dbca457fb8ca39bc563",
            "20261125T093852.057747Z": "d1d4c2189ffce7ba0510237bde354128a4834ecd2d7cdf1a4500658130bb66fe",
            "20261125T101539.846113Z": "91a6259816f6542fc92e52b5b11cc0251748145715fa44e83a097d72a0dd4727",
        },
        "895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30": {
            "20261125T104040.872664Z": "be02e38ef4527c3fa9fc214646a7614f9f8ee049711a973ed92c4e13cf7936a4",
            "20261125T104529.325181Z": "d5501f6a6a79f8050d5506ce6c58301eb427f3a725ef175aeeb9035ed72f8cba",
            "20261125T105613.425054Z": "1ff745000fea979506e61ebb9e3c4074d63c72b3144305707ca3a67268e23e98",
            "20261125T110021.438890Z": "7392d7281955a8b37477b7e096896f1337acef2e327760392a471ebcf1c654be",
            "20261125T111315.718164Z": "56f9ef7e521e0cfba2bddcd248a54553328de60ec7341438a0091c970dbe78b7",
            "20261125T115614.209375Z": "519cb65cd0fca8cc8b951ebc236577908f41310c9d862160ec596088ee27570e",
            "20261125T120540.276582Z": "e032d37830a62a75fa6a2aa2572032f4bc96662b67c92376ebe305414d09012e",
            "20261125T121602.672538Z": "bcf8795b00bf4fcf69f2a245b195378e24f03f4c522843e28984078707cb6cd2",
            "20261125T122001.677272Z": "0771c9fd3063327d85f1191e9d09a439191b03761574c8c47084a6ad7de92a5f",
            "20261125T123240.328724Z": "30138ab4eb4a792293392c862460a57156a126f722b56763ec06fc31b1c36669",
            "20261125T123800.133568Z": "4c53b4791f2f9cb2355fdf269ce3512737967d9f270e2f5fa3d0ffb42cce783e",
            "20261125T124355.176154Z": "5e8ef35a629f17056b6daf1ce57605c887cc0ddb5e762976c17500d20c18f766",
        },
    }.items()
    for run, digest in reports.items()
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def load(name, path, source):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    exec(compile(source, str(path), "exec"), module.__dict__)
    return module


def pinned_sources(root, digests, description):
    sources = {}
    for relative, digest in digests.items():
        source = (root / relative).read_bytes()
        require(serialized_sha(source) == digest, description + relative)
        sources[relative] = source
    return sources


def load_originals(project, helper_dir=None):
    helper_dir = helper_dir or DEFAULT_PROJECT / "verification/p36"
    if not (helper_dir / "exported_evidence/verify_and_install.py").is_file():
        helper_dir = project / "verification/p36"
    helpers = pinned_sources(helper_dir, HELPER_DIGESTS, "Original archive helper differs before import: ")
    archive_file = "exported_evidence/verify_and_install.py"
    warm_file = "verify_warm_common_parameters.py"
    archive_helpers = load("p36_export_helpers", helper_dir / archive_file, helpers[archive_file])
    originals = pinned_sources(project, archive_helpers.PINNED_VERIFIERS, "Original verification file differs: ")
    for name in ("verify_variable_envelope_boxes", "verify_part3_distribution"):
        path = "verification/" + name + ".py"
        load(name, project / path, originals[path])
    path = "verification/verify_part3_continuation.py"
    helper = load("p36_original_continuation", project / path, originals[path])
    path = "verification/p36/compile_p36_local.py"
    runner = load("p36_original_runner", project / path, originals[path])
    warm = load("p36_archive_writer", helper_dir / warm_file, helpers[warm_file])
    return runner, helper, archive_helpers, warm


def serialized_sha(data):
    return sha256(data).hexdigest()


def absolute(path):
    value = PurePosixPath(path)
    require(value.is_absolute() and ".." not in value.parts and value.as_posix() == path,
            "Invalid original path: " + path)
    return value


def check_object_facets(base, objects):
    require(isinstance(objects, dict) and base in objects
            and set(objects) <= {base, base + ".private", base + ".server"}
            and all(SHA256.fullmatch(digest) for digest in objects.values()),
            "Missing or unexpected object/sidecar: " + base)


def checked_log(stage, directory, read, prefix):
    name = stage["name"]
    require(re.fullmatch(r"[.A-Za-z0-9_'-]+", name) and name not in (".", "..")
            and type(stage["exit_code"]) is int and stage["exit_code"] == 0,
            "Failed or invalid command stage: " + name)
    path = str(directory / (name + ".log"))
    require(stage["log"] == path, "Log path differs: " + name)
    first, body = read(prefix + name + ".log", path, stage["log_sha256"]).decode().split("\n", 1)
    require(first == "command=" + json.dumps(stage["command"]), "Log command header differs: " + name)
    return body


def stage_bodies(report, run, read, targets):
    require(report.get("status") == "VERIFIED_OWNED" and report.get("schema") == 1
            and report.get("targets") == list(targets) and report.get("strict_owned") is True
            and report.get("blockers") == [] and report.get("finished_utc") and not report.get("error"),
            "Expected a completed VERIFIED_OWNED run for the exact target set")
    stages = report["commands"]
    require(stages and len({stage["name"] for stage in stages}) == len(stages),
            "Missing or duplicated command stages")
    return {stage["name"]: checked_log(stage, run, read, "run/") for stage in stages}


def check_stage_order(report, targets):
    names = [stage["name"] for stage in report["commands"]]
    compiled = ["compile-" + name for name in report["topological_order"]
                if report["modules"][name]["action"] == "compiled"]
    replay = ["replay-" + module for module in targets]
    verification = [name for name in names if name.startswith(("compile-", "replay-"))
                    or name == "owned-inventory-audit"]
    require(verification == compiled + replay + ["owned-inventory-audit"]
            and verification == names[-len(verification):],
            "Original dependency compile, owner compile, replay, and audit order differs")


def exact_owned_stages(report, run, targets, bodies):
    stages = {stage["name"]: stage for stage in report["commands"]}
    original = absolute(report["project"])
    objdir = absolute(report["build_dir"]) / "lib/lean"
    compiler = absolute(report["compiler"]["path"])
    checker = compiler.with_name("leanchecker")
    require({name for name in stages if name.startswith("replay-")} ==
            {"replay-" + owner for owner in targets}, "Kernel replay owner set differs")
    for owner in targets:
        relative = owner.replace(".", "/")
        obj = str(objdir / (relative + ".olean"))
        source = str(original / (relative + ".lean"))
        command = [str(compiler), "-t0", "-j1", "-R", str(original),
                   "-DwarningAsError=true", "-o", obj, source]
        node = report["modules"][owner]
        stage = stages["compile-" + owner]
        require(node["package"] == "project" and node["action"] == "compiled"
                and node["strict"] is True and node["exit_code"] == 0 and node["source"] == source
                and node["command"] == stage["command"] == command
                and node["log"] == stage["log"] and node["log_sha256"] == stage["log_sha256"],
                "Fresh owned strict compile differs: " + owner)
        check_object_facets(obj, node["objects"])
        replay = "replay-" + owner
        require(stages[replay]["command"] == [str(checker), "--verbose", owner]
                and "replaying " + owner in bodies[replay].splitlines(),
                "Missing exact bundled replay line or command: " + owner)
    audit = report["commands"][-1]
    require(audit["name"] == "owned-inventory-audit" and audit["command"] ==
            [str(compiler), "-t0", "-j1", "-DwarningAsError=true", "-R", str(run),
             str(run / "P36OwnedAudit.lean")], "Complete final audit command differs")


def complete_inventory(report, run, read, targets, bodies, helper):
    audit = helper.render_audit(targets).encode()
    require(read("run/P36OwnedAudit.lean", str(run / "P36OwnedAudit.lean")) == audit,
            "Audit source differs from the original renderer")
    records, counts = helper.baseline.validate_inventory(bodies["owned-inventory-audit"], modules=targets)
    require(report.get("declarations_file") == str(run / "declarations.json")
            and json.loads(read("run/declarations.json", str(run / "declarations.json"))) == records
            and report["declaration_count"] == len(records) and report["module_counts"] == counts,
            "Saved complete inventory disagrees with the original audit log")
    require(all("⋯" not in r["type"] and isinstance(r["level_parameters"], list)
                and all(isinstance(p, str) for p in r["level_parameters"]) for r in records),
            "Truncated type or invalid universe parameters")
    return records, counts


def check_environment(report, bodies, objdir, pins, runner):
    require(report["dependency_pins"] == pins
            and all(pins.get(k) == pin for k, pin in runner.REQUIRED_PINS.items()),
            "Manifest and original dependency pins differ")
    stages = {stage["name"]: stage["command"] for stage in report["commands"]}
    compiler = report["compiler"]
    toolchain = absolute(compiler["path"]).parent.parent
    require(compiler["path"] == str(toolchain / "bin/lean")
            and compiler["sha256"] == COMPILER_SHA256
            and "version 4.33.0-rc1," in compiler["version"] and runner.LEAN_COMMIT in compiler["version"]
            and stages["lean-version"] == [compiler["path"], "--version"]
            and bodies["lean-version"].strip() == compiler["version"], "Original Lean compiler differs")
    roots = {}
    for name, pin in pins.items():
        command = stages["pin-" + name]
        require(len(command) == 6 and command[:3] == ["git", "--no-optional-locks", "-C"]
                and command[-2:] == ["rev-parse", "HEAD"] and absolute(command[3]).name == name
                and bodies["pin-" + name].strip() == pin, "Dependency pin command/log differs: " + name)
        roots[name] = absolute(command[3])
        require(stages["clean-" + name] ==
                [*command[:4], "status", "--porcelain", "--untracked-files=no"]
                and not bodies["clean-" + name].strip(), "Dependency clean command/log differs: " + name)
    lean_path = [str(objdir), *(str(roots[n] / ".lake/build/lib/lean") for n in sorted(roots)),
                 str(toolchain / "lib/lean")]
    require(report["lean_path"] == lean_path and len(lean_path) == len(set(lean_path)),
            "Original LEAN_PATH roots or search order differ")
    return roots


def git_bytes(project, *args):
    return subprocess.check_output(["git", "--no-optional-locks", *args], cwd=project)


def checked_project_source(project, commit, relative, payload):
    path = project / relative
    require(path.resolve().is_relative_to(project) and path.is_file()
            and path.read_bytes() == payload == git_bytes(project, "show", commit + ":" + relative),
            "Project source differs from the archived bytes or frozen Git object: " + relative)


def check_source_manifest(data, report, project, source_commit, runner):
    selections = json.loads(data).get("sources")
    require(isinstance(selections, list), "Source selection manifest is missing its sources array")
    selected = set()
    for entry in selections:
        module = entry["module"]
        require(runner.MODULE.fullmatch(module) and module not in selected,
                "Invalid or duplicate selected source module: " + module)
        relative = module.replace(".", "/") + ".lean"
        digest = entry["selected_sha256"]
        require(entry["selected_path"] == relative and SHA256.fullmatch(digest),
                "Selected source path or hash differs: " + module)
        payload = (project / relative).read_bytes()
        require(serialized_sha(payload) == digest, "Selected source digest differs: " + module)
        checked_project_source(project, source_commit, relative, payload)
        if module in report["modules"]:
            node = report["modules"][module]
            require(node["package"] == "project" and node["source_sha256"] == digest,
                    "Selected source disagrees with the compiled graph: " + module)
        selected.add(module)
    return len(selected)


def lineage_run(run, module, node):
    raw_log = node.get("previous_log")
    require(isinstance(raw_log, str), "Missing previous compile log for reused module: " + module)
    log = absolute(raw_log)
    prior = log.parent
    require(prior.parent == run.parent and RUN_NAME.fullmatch(prior.name)
            and prior.name < run.name and log.name == "compile-" + module + ".log",
            "Previous compile log escapes its earlier original run: " + module)
    return prior


def capture_lineage(report, run, read):
    """Preserve each necessary original prior report once and use its exact stage records."""
    runs, records, reports = {}, {}, {}
    for module, node in report["modules"].items():
        if node["action"] == "reused":
            prior = lineage_run(run, module, node)
            runs.setdefault(prior, []).append(module)
    for prior, names in runs.items():
        path = prior / "report.json"
        raw = read("lineage/" + prior.name + "/report.json", str(path))
        earlier = json.loads(raw)
        require(earlier["schema"] == report["schema"] and earlier["project"] == report["project"]
                and earlier["build_dir"] == report["build_dir"],
                "Prior compile report belongs to a different schema, project, or build")
        writer, digest = earlier["runner_sha256"], serialized_sha(raw)
        pin = LEGACY_REPORT_PINS.get(path)
        if pin is not None:
            require((writer, digest) == pin, "Pinned legacy compile report writer or SHA-256 differs: " + str(path))
        else:
            require(writer == report["runner_sha256"], "Unpinned historical runner for compile report: " + str(path))
        reports[str(path)] = {"runner_sha256": writer, "report_sha256": digest, "status": earlier["status"],
                              "writer_binding": "pinned legacy report" if pin is not None else "current runner",
                              "reused_module_count": len(names)}
        stages = {stage["name"]: stage for stage in earlier["commands"]}
        require(len(stages) == len(earlier["commands"]), "Prior compile report repeats a command stage")
        for module in names:
            records[module] = (earlier["modules"][module], stages["compile-" + module])
    return records, reports


def check_prior_compile(module, node, record, run, command, inputs, read):
    prior = lineage_run(run, module, node)
    old, stage = record
    require(old["action"] == "compiled" and type(old["exit_code"]) is int and old["exit_code"] == 0
            and {field: old.get(field) for field in inputs} == inputs
            and old["input_key"] == node["input_key"] and old["objects"] == node["objects"]
            and stage["name"] == "compile-" + module and stage["command"] == command
            and all(old[field] == stage[field] for field in ("command", "log", "log_sha256", "exit_code"))
            and stage["log"] == node["previous_log"], "Reused module's historical compile differs: " + module)
    checked_log(stage, prior, read, "lineage/" + prior.name + "/")


def check_external_source(node, package, kind, relative, roots):
    source = node["source"]
    if package == "core":
        require(kind == "core" and source is None, "Core module has an external source: " + relative)
        return
    require(package in roots and kind in {"cached", "build"}, "Invalid external package or kind: " + relative)
    if source is None:
        require(kind == "cached", "Package build source is missing: " + relative)
        return
    allowed = {str(roots[package] / relative)}
    if package == "goldbach" and relative.startswith("MathlibNt/Wu2008DoubleSieve/"):
        allowed.add(str(roots[package] / "research/wu2008/src" / relative))
    require(source in allowed, "External source escapes its pinned package root: " + relative)


def check_native_sources(report, bodies, roots, snapshots):
    native = {module: node for module, node in report["modules"].items()
              if node["package"] == "goldbach" and node["source"] is not None}
    stages = [stage for stage in report["commands"] if stage["name"] == "native-tracked-files"]
    aliases = report.get("native_research_aliases", [])
    if not native:
        require(not stages and not aliases, "Unexpected native tracked listing or aliases")
        return {}
    root = roots["goldbach"]
    require(len(stages) == 1 and stages[0]["command"] ==
            ["git", "--no-optional-locks", "-C", str(root), "ls-files", "-s"],
            "Original native tracked-files command differs")
    tracked = {}
    for line in bodies["native-tracked-files"].splitlines():
        metadata, relative = line.split("\t", 1)
        _mode, blob, stage = metadata.split()
        require(re.fullmatch(r"[0-9a-f]{40}", blob) and stage == "0" and relative not in tracked,
                "Invalid or duplicate native tracked-file record")
        tracked[relative] = blob
    expected_aliases, native_blobs = {}, {}
    for module, node in native.items():
        path = absolute(node["source"])
        relative = path.relative_to(root).as_posix()
        if relative not in tracked:
            match = "research/wu2008/src/" + relative
            require(relative.startswith("MathlibNt/Wu2008DoubleSieve/") and match in tracked,
                    "Native source lacks original tracked lineage: " + module)
            expected_aliases[module] = {
                "module": module, "source": str(path), "sha256": node["source_sha256"],
                "tracked_matches": [{"path": match, "git_blob": tracked[match]}],
            }
            bind(snapshots, str(root / match), node["source_sha256"])
            relative = match
        native_blobs[str(path)] = tracked[relative]
    actual_aliases = {alias["module"]: alias for alias in aliases}
    require(len(actual_aliases) == len(aliases) and actual_aliases == expected_aliases,
            "Original native alias records differ from the tracked listing and resolved module sources")
    return native_blobs


def check_graph(report, targets, project, source_commit, run, read, originals, snapshots, roots, lineage):
    runner = originals[0]
    modules, order = report["modules"], report["topological_order"]
    require(len(order) == len(set(order)) and set(order) == set(modules)
            and report["counts"] == dict(Counter(node["kind"] for node in modules.values())),
            "Incomplete original module graph")
    mirrors = report["external_cache_mirrors"]
    require(set(mirrors) == set(report["planned_external_cache_mirrors"]), "Native mirror set differs")
    objdir = absolute(report["build_dir"]) / "lib/lean"
    original = absolute(report["project"])
    toolchain = absolute(report["compiler"]["path"]).parent.parent
    stages = {stage["name"]: stage for stage in report["commands"]}
    require({name for name in stages if name.startswith("compile-")} ==
            {"compile-" + name for name, node in modules.items() if node["action"] == "compiled"},
            "Compile stages and graph actions differ")
    signatures, resolved = {}, {}
    project_count = 0
    for name in order:
        require(runner.MODULE.fullmatch(name), "Invalid module identity: " + name)
        node = modules[name]
        imports = list(node["imports"])
        require(len(imports) == len(set(imports)) and all(i in signatures for i in imports),
                "Missing or out-of-order import: " + name)
        dependencies = {i: signatures[i] for i in imports}
        suffix = name.replace(".", "/")
        source, digest = node["source"], node.get("source_sha256")
        package = node["package"]
        kind, action = node["kind"], node["action"]
        relative = suffix + ".lean"
        if source is not None:
            require(absolute(source).as_posix().endswith("/" + suffix + ".lean"),
                    "Source does not have its module path: " + name)
            bind(snapshots, source, digest)
        if package == "project":
            project_count += 1
            require(kind == "build" and source == str(original / relative), "Project module path differs: " + name)
            payload = read("source/" + relative, source, digest)
            checked_project_source(project, source_commit, relative, payload)
            text = payload.decode()
            actual_imports = runner.parse_imports(text)
            if name != "Init" and not re.search(r"(?m)^\s*prelude\b", runner.lean_code(text)):
                actual_imports = list(dict.fromkeys(["Init", *actual_imports]))
            require(imports == actual_imports, "Project source imports differ from the report: " + name)
            if name in targets:
                require(not originals[1].baseline.FORBIDDEN.search(runner.lean_code(text)),
                        "Forbidden construct in owned source: " + name)
        else:
            check_external_source(node, package, kind, relative, roots)
        obj = str(objdir / (suffix + ".olean"))
        objects = node["objects"]
        if kind in {"cached", "core"}:
            require(action == "external_cache" and package != "project", "Invalid cache action: " + name)
            cache_root = toolchain / "lib/lean" if kind == "core" else roots[package] / ".lake/build/lib/lean"
            cached = str(cache_root / (suffix + ".olean"))
            require(node["cached_object"] == cached, "Original cache path differs: " + name)
            check_object_facets(cached, objects)
            signatures[name] = runner.digest_json({"objects": objects, "imports": dependencies, "source": digest})
            resolved[name] = cached
            if name in mirrors:
                copied = {obj + path[len(cached):]: value for path, value in objects.items()}
                require(mirrors[name] == {"source_objects": objects, "mirrored_objects": copied}
                        and node["mirrored_objects"] == copied, "Native cache mirror differs: " + name)
                for path, value in copied.items():
                    bind(snapshots, path, value)
                resolved[name] = obj
        else:
            require(kind == "build" and action in {"compiled", "reused"},
                    "Unexpected target or dependency build action: " + name)
            strict = node.get("strict", False)
            require(type(strict) is bool, "Invalid warning policy: " + name)
            input_data = {"source": source, "source_sha256": digest, "compiler": report["compiler"],
                          "strict": strict, "imports": dependencies, "lean_path": report["lean_path"],
                          "trust": 0, "threads": 1}
            key = runner.digest_json(input_data)
            require(node["input_key"] == key, "Recursive dependency signature differs: " + name)
            check_object_facets(obj, objects)
            command = [report["compiler"]["path"], "-t0", "-j1", "-R", source[:-(len(relative) + 1)]]
            if strict:
                command.append("-DwarningAsError=true")
            command += ["-o", obj, source]
            if action == "compiled":
                stage = stages["compile-" + name]
                require(all(node.get(field) == value for field, value in input_data.items())
                        and node["command"] == stage["command"] == command
                        and node["log"] == stage["log"] and node["log_sha256"] == stage["log_sha256"]
                        and node["exit_code"] == 0, "Original compile metadata differs: " + name)
            else:
                require(name in lineage, "Missing original successful compile lineage: " + name)
                check_prior_compile(name, node, lineage[name], run, command, input_data, read)
            signatures[name] = runner.digest_json({"input_key": key, "objects": objects})
            resolved[name] = obj
        for path, value in objects.items():
            bind(snapshots, path, value)
        if name in targets:
            for path, value in objects.items():
                read("objects/" + absolute(path).relative_to(objdir).as_posix(), path, value)
    reachable = set(targets)
    for name in reversed(order):
        if name in reachable:
            reachable.update(modules[name]["imports"])
    require(reachable == set(modules) and project_count == report["project_module_count"]
            and set(mirrors) <= set(modules), "Project closure counts or reachable graph differ")
    return resolved


def bind(snapshots, path, digest):
    absolute(path)
    require(isinstance(digest, str) and SHA256.fullmatch(digest)
            and snapshots.get(path, digest) == digest, "Conflicting or invalid snapshot hash: " + path)
    snapshots[path] = digest


def check_runtime_binding(read, binding, run_report, report_sha, source_commit, targets, tool_hashes):
    if binding is None:
        return {"status": "unknown", "sha256_before_and_after": None}
    raw = read("runtime/binding.json", binding["path"], binding["sha256"])
    observed = json.loads(raw)
    require(len(targets) == 1 and observed == {
        "owner": targets[0], "source_commit": source_commit, "status": "VERIFIED_OWNED",
        "exit_code": 0, "report": run_report, "report_sha256": report_sha,
        "runtime_tool_sha256_before": tool_hashes, "runtime_tool_sha256_after": tool_hashes,
    } and type(observed["exit_code"]) is int, "Independent runtime binding differs from the original run")
    return {"status": "independently captured", "sha256_before_and_after": tool_hashes}


def validate_run(project, source_commit, report, run, owners, read, originals, report_sha=None, binding=None):
    runner, helper, archive_helpers, _ = originals
    targets = tuple(owners)
    build = absolute(report["build_dir"])
    original = absolute(report["project"])
    require(run.parent == build / "runs" and RUN_NAME.fullmatch(run.name)
            and report["runner_sha256"] == archive_helpers.PINNED_VERIFIERS["verification/p36/compile_p36_local.py"],
            "Original runner or run path differs")
    bodies = stage_bodies(report, run, read, targets)
    exact_owned_stages(report, run, targets, bodies)
    check_stage_order(report, targets)
    records, counts = complete_inventory(report, run, read, targets, bodies, helper)
    config = dict(archive_helpers.PINNED_VERIFIERS)
    for name in ("lean-toolchain", "lake-manifest.json"):
        config[name] = archive_helpers.file_sha(project / name)
    for name, digest in config.items():
        data = read("config/" + name, str(original / name), digest)
        checked_project_source(project, source_commit, name, data)
    require((project / "lean-toolchain").read_text().strip() == runner.TOOLCHAIN_PIN,
            "Project Lean toolchain pin differs")
    packages = json.loads((project / "lake-manifest.json").read_bytes())["packages"]
    pins = {package["name"]: package["rev"] for package in packages}
    require(len(pins) == len(packages), "Duplicate package pins")
    roots = check_environment(report, bodies, build / "lib/lean", pins, runner)
    compiler = absolute(report["compiler"]["path"])
    runner_file = "verification/p36/compile_p36_local.py"
    snapshots = {str(original / runner_file): config[runner_file]}
    bind(snapshots, str(compiler), COMPILER_SHA256)
    selected_count = None
    selection_binding = "omitted"
    if "source_manifest" in report:
        manifest = report["source_manifest"]
        selection_path = absolute(manifest["path"])
        data = read("SOURCE_SELECTION.json", manifest["path"], manifest["sha256"])
        selection_binding = "external file bound by report hash"
        if selection_path.is_relative_to(original):
            relative = selection_path.relative_to(original).as_posix()
            tracked = git_bytes(project, "--literal-pathspecs", "ls-tree", "-z", "--full-tree",
                                source_commit, "--", relative)
            selection_binding = "generated file bound by report hash"
            if tracked:
                checked_project_source(project, source_commit, relative, data)
                selection_binding = "frozen Git blob"
        selected_count = check_source_manifest(data, report, project, source_commit, runner)
        bind(snapshots, manifest["path"], manifest["sha256"])
    lineage, prior_reports = capture_lineage(report, run, read)
    resolved = check_graph(report, targets, project, source_commit, run, read, originals, snapshots, roots, lineage)
    native_blobs = check_native_sources(report, bodies, roots, snapshots)
    require(not report.get("transferred_verified_objects"), "Unexpected transferred dependency receipt")
    for owner, digest in owners.items():
        require(report["modules"][owner]["source_sha256"] == digest, "Expected owned source hash differs: " + owner)
    reports_only_digest = runner.digest_json(snapshots)
    reports_only_count = len(snapshots)
    export_checks = {str(original / name): config[name] for name in (
        "lake-manifest.json", "verification/verify_part3_continuation.py", "verification/verify_part3_distribution.py",
        "verification/Part3DistributionAudit.lean", "verification/verify_variable_envelope_boxes.py")}
    export_checks[str(compiler.with_name("leanchecker"))] = CHECKER_SHA256
    export_checks[str(run / "P36OwnedAudit.lean")] = serialized_sha(helper.render_audit(targets).encode())
    runtime_paths = (compiler, compiler.with_name("leanchecker"), *(
        original / name for name in ("verification/p36/compile_p36_local.py",
        "verification/verify_part3_continuation.py", "verification/verify_part3_distribution.py",
        "verification/Part3DistributionAudit.lean")))
    for path, digest in export_checks.items():
        bind(snapshots, path, digest)
    runtime = check_runtime_binding(read, binding, str(run / "report.json"), report_sha, source_commit,
                                    targets, {str(path): snapshots[str(path)] for path in runtime_paths})
    summary = {"scope": "Exact original owner only", "whole_p36_closed": False,
               "source_commit": source_commit, "targets": list(targets), "source_sha256": owners,
               "objects_sha256": {owner: report["modules"][owner]["objects"] for owner in targets},
               "declaration_count": len(records), "module_counts": counts,
               "observed_transitive_axioms": sorted({a for r in records for a in r["axioms"]}),
               "dependency_pins": pins, "lean_path": report["lean_path"],
               "compiler": report["compiler"], "source_selection_entries": selected_count,
               "source_selection_binding": selection_binding,
               "prior_compile_run_count": len(prior_reports),
               "prior_compile_reports": prior_reports,
               "prior_compile_scope": "Reused successful dependency compile stages only",
               "reused_module_count": len(lineage),
               "report_recorded_snapshot_sha256": reports_only_digest,
               "report_recorded_snapshot_count": reports_only_count,
               "independent_runtime_binding": runtime,
               "export_time_additional_input_sha256": export_checks,
               "snapshot_sha256": runner.digest_json(snapshots), "snapshot_count": len(snapshots),
               "snapshot_scope": "Export-time rechecks of report-recorded and separately identified inputs",
               "original_finished_utc": report["finished_utc"]}
    return summary, snapshots, roots, resolved, native_blobs


def live_facets(base):
    return {str(base) + suffix for suffix in ("", ".private", ".server")
            if Path(str(base) + suffix).is_file()}


def check_live_inputs(report, snapshots, roots, resolved, native_blobs, runner, file_sha):
    for path, digest in snapshots.items():
        require(Path(path).is_file() and file_sha(Path(path)) == digest,
                "Current bytes differ from original run binding: " + path)
    lean_path = [Path(p) for p in report["lean_path"]]
    for name, node in report["modules"].items():
        expected = Path(resolved[name])
        selected = runner.lean_object_path(lean_path, name)
        require(selected is not None and selected.is_file() and selected.resolve() == expected.resolve(),
                "Original import resolution changed: " + name)
        # Bind the complete current sidecar sets as well as the recorded paths and digests.
        original = Path(node["cached_object"]) if node["kind"] in {"cached", "core"} else expected
        require(live_facets(original) == set(node["objects"]), "Original object sidecar set changed: " + name)
        if original != expected:
            require(live_facets(expected) == set(node["mirrored_objects"]), "Native mirror sidecar set changed: " + name)
    for name, root in roots.items():
        require(git_bytes(root, "rev-parse", "HEAD").decode().strip() == report["dependency_pins"][name]
                and not git_bytes(root, "status", "--porcelain", "--untracked-files=no").strip(),
                "Dependency checkout pin or tracked clean state changed: " + name)
    for alias in report.get("native_research_aliases", []):
        for match in alias["tracked_matches"]:
            blob = git_bytes(roots["goldbach"], "rev-parse", "HEAD:" + match["path"]).decode().strip()
            require(blob == match["git_blob"], "Tracked native alias Git identity changed")
    for path, blob in native_blobs.items():
        data = Path(path).read_bytes()
        git_blob = sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        require(git_blob == blob, "Native source bytes differ from the original tracked Git blob: " + path)
        root = roots["goldbach"]
        relative = absolute(path).relative_to(root)
        nested = PurePosixPath("research/wu2008/src")
        if relative.is_relative_to(nested):
            ordinary = Path(str(root / relative.relative_to(nested)))
            require(not ordinary.is_file(), "A flattened native source now shadows its nested tracked source")


def check_report_identity(report_sha, terminal_sha):
    require(terminal_sha is None or terminal_sha == report_sha, "Original report hash differs from the pinned terminal digest")
    return {"report_sha256": report_sha, "terminal_report_sha256": terminal_sha,
            "original_report_identity": "pinned terminal SHA-256" if terminal_sha else "reported path, no terminal digest"}


def export(args, project, owners, originals):
    runner, _, archive_helpers, warm = originals
    original_report = args.report.resolve(strict=True)
    run = original_report.parent
    require(original_report.name == "report.json", "Expected the original run/report.json")
    captured = original_report.read_bytes()
    report = json.loads(captured)
    require(Path(report["project"]) == project, "Export requires the project's original runtime path")
    evidence = warm.EvidenceArchive()
    report_hash = serialized_sha(captured)
    report_identity = check_report_identity(report_hash, args.report_sha256)
    require((args.runtime_binding is None) == (args.runtime_binding_sha256 is None),
            "Supply both the independent binding file and its pinned SHA-256")
    binding = None
    if args.runtime_binding is not None:
        require(args.report_sha256 is not None and SHA256.fullmatch(args.runtime_binding_sha256),
                "An independent runtime binding requires its SHA-256 and the original terminal report SHA-256")
        binding = {"path": str(args.runtime_binding.resolve(strict=True)), "sha256": args.runtime_binding_sha256}
    evidence.add("run/report.json", original_report, report_hash)

    def read(name, original, digest=None):
        evidence.add(name, original, digest)
        return Path(original).read_bytes()

    summary, snapshots, roots, resolved, native_blobs = validate_run(
        project, args.source_commit, report, PurePosixPath(run.as_posix()), owners, read, originals,
        report_hash, binding)
    check_live_inputs(report, snapshots, roots, resolved, native_blobs, runner, archive_helpers.file_sha)
    args.output_dir.mkdir(parents=True, exist_ok=False)
    receipt = warm.publish_evidence(
        args.output_dir.resolve(), evidence,
        {**summary, **report_identity, "status": "VERIFIED_OWNED_EXPORT", "report_path": str(original_report),
         "runtime_binding_file": binding, "archive_role": "Original execution evidence with export-time rechecks"},
        lambda: require(original_report.read_bytes() == captured, "Original report changed during export"))
    receipt_path = args.output_dir / "RECEIPT.json"
    return {"status": receipt["status"], "receipt": str(receipt_path.resolve()),
            "receipt_sha256": archive_helpers.file_sha(receipt_path),
            "archive": receipt["archive"], "archive_sha256": receipt["archive_sha256"],
            "archive_bytes": receipt["archive_bytes"], "declaration_count": summary["declaration_count"],
            "snapshot_count": summary["snapshot_count"]}


def verify(args, project, owners, originals):
    _, _, helpers, _ = originals
    receipt_bytes = args.receipt.read_bytes()
    require(serialized_sha(receipt_bytes) == args.receipt_sha256, "Pinned receipt SHA-256 differs")
    receipt = json.loads(receipt_bytes)
    archive = args.archive.read_bytes()
    require(receipt["status"] == "VERIFIED_OWNED_EXPORT"
            and len(archive) == receipt["archive_bytes"] and serialized_sha(archive) == receipt["archive_sha256"],
            "Receipt status or archive size/hash differs")
    files = receipt["files"]
    original_report = absolute(receipt["report_path"])
    require(original_report.name == "report.json", "Original report path differs")
    seen = set()
    with tempfile.TemporaryDirectory(prefix="p36-increment-verify-") as directory:
        root = Path(directory)
        helpers.safe_unpack(archive, files, root)

        def read(name, original, digest=None):
            entry = files[name]
            require(str(original) == entry["path"] and (digest is None or digest == entry["sha256"]),
                    "Archive manifest disagrees with original path or digest: " + name)
            seen.add(name)
            return (root / name).read_bytes()

        raw_report = read("run/report.json", original_report, receipt["report_sha256"])
        identity = check_report_identity(serialized_sha(raw_report), receipt["terminal_report_sha256"])
        require(all(receipt.get(field) == value for field, value in identity.items()), "Report provenance differs")
        binding = receipt["runtime_binding_file"]
        if binding is not None:
            require(identity["terminal_report_sha256"] is not None, "Runtime binding lacks a terminal report digest")
        summary, _, _, _, _ = validate_run(
            project, args.source_commit, json.loads(raw_report), original_report.parent, owners, read, originals,
            identity["report_sha256"], binding)
        require(seen == set(files), "Unexpected archive members outside the verified scope")
        require(all(receipt.get(key) == value for key, value in summary.items()),
                "Receipt and independently revalidated original evidence differ")
    return {**summary, "status": "PASS_LOCAL_EVIDENCE_VERIFICATION",
            "receipt_sha256": args.receipt_sha256, "archive_sha256": receipt["archive_sha256"],
            "archive_members": len(files), "local_lean_run": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    exporter = commands.add_parser("export")
    exporter.add_argument("--report", type=Path, required=True)
    exporter.add_argument("--report-sha256")
    exporter.add_argument("--runtime-binding", type=Path)
    exporter.add_argument("--runtime-binding-sha256")
    exporter.add_argument("--output-dir", type=Path, required=True)
    verifier = commands.add_parser("verify")
    verifier.add_argument("--receipt", type=Path, required=True)
    verifier.add_argument("--receipt-sha256", required=True)
    verifier.add_argument("--archive", type=Path, required=True)
    for command in (exporter, verifier):
        command.add_argument("--project", type=Path, default=DEFAULT_PROJECT)
        command.add_argument("--source-commit", required=True)
        command.add_argument("--owner", choices=OWNERS, required=True)
        command.add_argument("--source-sha256", required=True)
    args = parser.parse_args()
    try:
        require(re.fullmatch(r"[0-9a-f]{40}", args.source_commit), "Expected full Git source commit")
        require(SHA256.fullmatch(args.source_sha256), "Expected full owned source SHA-256")
        project = args.project.resolve(strict=True)
        require(git_bytes(project, "rev-parse", args.source_commit + "^{commit}").decode().strip() == args.source_commit,
                "Frozen source commit differs")
        originals = load_originals(project)
        function = export if args.command == "export" else verify
        print(json.dumps(function(args, project, {args.owner: args.source_sha256}, originals), indent=2))
    except (OSError, RuntimeError, ValueError, TypeError, LookupError, AttributeError,
            subprocess.CalledProcessError) as error:
        parser.exit(1, "Evidence rejected: " + str(error) + "\n")


if __name__ == "__main__":
    main()
