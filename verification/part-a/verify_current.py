#!/usr/bin/env python3
"""Accept retained current-run evidence only after source and declaration checks."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
ROOT, CURRENT = HERE.parents[1], HERE / "current"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FINGERPRINT = "2e72fddba29d838fa1869c072f6c4924b511a12dc5f8df36851137617c6baa1f"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    require(path.is_file(), "missing evidence file: " + str(path))
    return json.loads(path.read_text())


def census(text, modules, label):
    parsed = {tag: [] for tag in ("DECL", "SERIALIZED", "MODULE", "COUNT")}
    for line in text.splitlines():
        require(not line.startswith("P0_ROUND6_INVENTORY_MISMATCH"), label + ": inventory mismatch diagnostic")
        for tag in parsed:
            prefix = "P0_ROUND6_" + tag + " "
            if line.startswith(prefix):
                parsed[tag].append(json.loads(line[len(prefix):]))
    declarations = {}
    for item in parsed["DECL"]:
        name = item["name"]
        require(name not in declarations, label + ": duplicate declaration " + name)
        require(item["module"] in modules, label + ": unexpected owner for " + name)
        require(all(item[k] is False for k in ("is_axiom", "is_partial", "is_unsafe")), label + ": unsafe/admitted " + name)
        require(isinstance(item["axioms"], list) and set(item["axioms"]) <= ALLOWED, label + ": unapproved axioms for " + name)
        require(all(isinstance(item[k], str) and item[k].strip() and "⋯" not in item[k]
                    for k in ("type", "readable_type", "kind")), label + ": incomplete record " + name)
        declarations[name] = dict(item, axioms=sorted(set(item["axioms"])))
    for tag in ("SERIALIZED", "MODULE"):
        require(len(parsed[tag]) == len(modules) and {x["module"] for x in parsed[tag]} == modules,
                label + ": incomplete/duplicate " + tag + " module census")
    counts = {x["module"]: x["count"] for x in parsed["MODULE"]}
    for item in parsed["SERIALIZED"]:
        module = item["module"]
        names = {name for name, d in declarations.items() if d["module"] == module}
        require(item["has_data"] is True and item["import_all"] is True and item["is_module"] is False,
                label + ": incomplete serialized data for " + module)
        require(names and counts[module] == item["serialized_constant_count"] == len(names), label + ": count mismatch for " + module)
        for field in ("serialized_constant_names", "environment_constant_names"):
            require(len(item[field]) == len(names) and set(item[field]) == names, label + ": name mismatch for " + module)
    require(parsed["COUNT"] == [len(declarations)], label + ": missing/incorrect final count")
    return declarations


def historical_records(modules):
    result = subprocess.run([sys.executable, "-B", str(HERE / "verify.py")], cwd=ROOT, capture_output=True, text=True)
    require(result.returncode == 0, "historical verification failed: " + (result.stderr or result.stdout).strip())
    summary = json.loads(result.stdout)
    require(summary["source_list_sha256"] == FINGERPRINT, "historical source fingerprint changed")
    combined = {}
    for tag in ("a3", "a4"):
        manifest = load(HERE / "original" / (tag + "-manifest.json"))
        with zipfile.ZipFile(HERE / "original" / (tag + ".zip")) as archive:
            records = census(archive.read("batch-types.log").decode(), set(manifest["closure_modules"]), "historical " + tag)
        for name, item in records.items():
            if item["module"] in modules:
                require(name not in combined or combined[name] == item, "historical shared declaration conflict: " + name)
                combined[name] = item
    require(len(combined) == 1880, "historical union is not 1880 declarations")
    return combined


def main():
    require(CURRENT.is_dir(), "missing current evidence directory: " + str(CURRENT))
    filenames = ("build.log", "checker.log", "types.log", "OBJECTS_BEFORE.json", "OBJECTS_AFTER.json", "ENVIRONMENT.json")
    for name in filenames:
        require((CURRENT / name).is_file(), "missing current evidence file: " + name)
    before, after = load(CURRENT / "OBJECTS_BEFORE.json"), load(CURRENT / "OBJECTS_AFTER.json")
    require(isinstance(before, dict) and before == after, "source/configuration/input-object snapshots differ")
    for path, digest in before.items():
        require(not Path(path).is_absolute() and ".." not in Path(path).parts and re.fullmatch(r"[0-9a-f]{64}", digest),
                "invalid snapshot entry: " + path)
    sources = load(HERE / "source-manifest.json")
    require(len(sources) == 69, "production source manifest is not 69 modules")
    canonical = "".join(digest + "  " + path + "\n" for path, digest in sorted(sources.items()))
    require(sha(canonical.encode()) == FINGERPRINT, "production source fingerprint mismatch")
    modules = {path[:-5].replace("/", ".") for path in sources}
    kernels = modules | {"ImbalancedChen"}
    audit_path = "verification/part-a/PartAAudit.lean"
    config = ("ImbalancedChen.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json")
    bound = set(sources) | set(config) | {audit_path}
    for path in sorted(bound):
        require(path in before and sha((ROOT / path).read_bytes()) == before[path], "current source/configuration hash mismatch: " + path)
        if path in sources:
            require(before[path] == sources[path], "historical source binding mismatch: " + path)
    for module in kernels:
        path = ".lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
        require(path in before, "missing project object binding: " + path)
    require(any(p.startswith(".lake/packages/") and p.endswith(".olean") for p in before), "missing dependency object bindings")
    environment = load(CURRENT / "ENVIRONMENT.json")
    commit = environment["source_commit"]
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit), "invalid source_commit")
    version = (ROOT / "lean-toolchain").read_text().strip().split(":v", 1)[1]
    require(re.search(r"\bversion " + re.escape(version) + r"(?:,|\s|$)", environment["Lean_version"]), "Lean version differs from pin")
    for path in sorted(bound):
        result = subprocess.run(["git", "show", commit + ":" + path], cwd=ROOT, capture_output=True,
                                env=dict(os.environ, GIT_NO_LAZY_FETCH="1"))
        require(result.returncode == 0 and sha(result.stdout) == before[path], "source_commit does not bind input: " + path)
    commands = environment["commands"]
    require(len(commands) == 3 and {c["stage"] for c in commands} == {"build", "checker", "types"}, "missing/duplicate command stages")
    for command in commands:
        require(type(command["exit_code"]) is int and command["exit_code"] == 0, "nonzero command exit: " + command["stage"])
        require(isinstance(command["argv"], list) and all(isinstance(x, str) for x in command["argv"]), "invalid command argv")
    argv = {c["stage"]: c["argv"] for c in commands}
    require(argv["build"] in (["lake", "build"], ["lake", "build", "ImbalancedChen"]), "unexpected build command")
    require(argv["checker"][:4] == ["lake", "env", "leanchecker", "--verbose"] and
            len(argv["checker"][4:]) == 70 and set(argv["checker"][4:]) == kernels, "checker command coverage mismatch")
    require(argv["types"] == ["lake", "env", "lean", "-t0", "-M24576", "-DwarningAsError=true", audit_path], "unexpected declaration audit command")
    build = (CURRENT / "build.log").read_text().strip().splitlines()
    require(build and re.fullmatch(r"Build completed successfully(?: \(\d+ jobs\))?\.", build[-1]), "build did not finish successfully")
    replay = [line[10:] for line in (CURRENT / "checker.log").read_text().splitlines() if line.startswith("replaying ")]
    require(len(replay) == 70 and set(replay) == kernels, "kernel replay is not exactly 69 modules plus root")
    current = census((CURRENT / "types.log").read_text(), modules, "current")
    historical = historical_records(modules)
    require(len(current) == 1880 and current.keys() == historical.keys(), "current complete declaration names/count differ from history")
    for name in current:
        changed = [k for k in current[name].keys() | historical[name].keys() if current[name].get(k) != historical[name].get(k)]
        require(not changed, "current declaration differs from history: " + name + " fields=" + ",".join(changed))
    receipt = {
        "status": "PASS_CURRENT_ROOT_BUILD_REPLAY_AND_DECLARATION_AUDIT", "source_commit": commit,
        "Lean_version": environment["Lean_version"], "production_modules": 69, "kernel_modules": 70,
        "complete_serialized_declarations": 1880, "kernel_module_names": sorted(kernels),
        "file_sha256": {name: sha((CURRENT / name).read_bytes()) for name in filenames},
        "configuration_sha256": {path: before[path] for path in config}, "audit_source_sha256": before[audit_path],
        "validator_sha256": sha(Path(__file__).read_bytes()), "historical_verifier_sha256": sha((HERE / "verify.py").read_bytes()),
        "historical_source_fingerprint": FINGERPRINT, "snapshot_entries": len(before),
        "allowed_transitive_axioms": sorted(ALLOWED), "unconditional_main_theorem_complete": False,
    }
    (CURRENT / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError, zipfile.BadZipFile) as error:
        raise SystemExit("FAIL: " + str(error)) from error
