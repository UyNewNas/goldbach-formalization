#!/usr/bin/env python3
"""Check the exact Part A sources against retained historical acceptance evidence.

This is a provenance and complete-declaration audit. It does not run Lean and
does not claim that a newly assembled library root has been compiled.
"""
import hashlib
import json
from pathlib import Path
import re
import sys
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ORIGINAL = HERE / "original"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CONFIGURATION = {
    "ImbalancedChen.lean": "944fdaf45377f61a5158d95193364285d9c9c18e893fc3e5eee6753b6c20affc",
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254",
}
EXPECTED = {
    "a3": {
        "manifest": "98564438c7ae4684eb2f4224317672ccb3bb157fdaf2bc02c3870e6d5da57c2d",
        "zip": "e9bbf3a92783d7724301def148227a6c02654507aa26257c84186fee2055be24",
        "root": "ImbalancedChen.RealHalfProductMassSuppliers", "modules": 24,
        "declarations": 558, "run": 44470415535,
    },
    "a4": {
        "manifest": "3138efabe92e5d15b0646c0261a443ccba1fe1b846c4844dbc08778984bffeb4",
        "zip": "6ed7c09208dd3acf813db3d2c34a012a4d239aaff56899cf039f9e41725c7970",
        "root": "ImbalancedChen.UniformPowerEulerNormalization", "modules": 56,
        "declarations": 1580, "run": 44440822784,
    },
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def imports(text):
    """Read imports after removing Lean's nested block comments and line comments."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == "-/":
            depth -= 1
            out.append(" ")
            i += 2
        elif not depth and text[i:i + 2] == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            if not depth:
                out.append(text[i])
            i += 1
    require(depth == 0, "unterminated Lean comment")
    return [m for line in "".join(out).splitlines()
            if re.match(r"^\s*(?:public\s+)?import\s", line)
            for m in re.sub(r"^\s*(?:public\s+)?import\s+", "", line).split()]


def closure(root, records):
    seen = set()
    def visit(module):
        if module in seen or not module.startswith("ImbalancedChen."):
            return
        require(module in records, "missing project dependency: " + module)
        seen.add(module)
        for dependency in records[module]["imports"]:
            visit(dependency)
    visit(root)
    return seen


def main():
    for path, digest in CONFIGURATION.items():
        require(sha((ROOT / path).read_bytes()) == digest, "configuration hash mismatch: " + path)
    sources, declarations, summaries, dependency_records = {}, {}, {}, []
    for tag, expected in EXPECTED.items():
        raw = (ORIGINAL / (tag + "-manifest.json")).read_bytes()
        require(sha(raw) == expected["manifest"], tag + " manifest digest")
        manifest = json.loads(raw)
        archive = ORIGINAL / (tag + ".zip")
        require(sha(archive.read_bytes()) == expected["zip"], tag + " artifact digest")
        records = {r["module"]: r for r in manifest["closure_source_records"]}
        selected = closure(expected["root"], records)
        require(len(selected) == expected["modules"], tag + " selected closure count")
        overlays = {r["module"]: r for r in manifest["candidate_overlays"]}
        with zipfile.ZipFile(archive) as z:
            load = lambda path: json.loads(z.read(path))
            acceptance = load("BATCH_ACCEPTANCE.json")
            stage = load("P1_STAGE_RECEIPT.json")
            objects_raw = z.read("BATCH_OBJECTS_BEFORE.json")
            objects = json.loads(objects_raw)
            require(acceptance["status"] == "PASS_EXACT_CANDIDATE_CLOSURE_ONLY", tag + " acceptance")
            require(acceptance["proof_artifact_hash"] == sha(objects_raw), tag + " object snapshot digest")
            require(stage["manifest_sha256"] == expected["manifest"], tag + " staged manifest")
            require(stage["source_commit"] == manifest["base_commit"] == acceptance["source_commit"], tag + " source revision")
            require(manifest["closure_modules"] == stage["closure_modules"] == acceptance["modules"], tag + " accepted module list")
            require(z.read("batch-build.log").decode().rstrip().endswith("jobs)."), tag + " build log ending")
            require("Build completed successfully" in z.read("batch-build.log").decode().splitlines()[-1], tag + " build success")
            replay = [line[10:] for line in z.read("batch-checker.log").decode().splitlines() if line.startswith("replaying ")]
            require(len(replay) == len(set(replay)) and set(replay) == set(acceptance["modules"]), tag + " kernel replay coverage")
            runtime = load("runtime/audit.json")
            require(runtime["status"] == "PASS_RUNTIME_GUARD_ONLY", tag + " runtime guard")
            require(runtime["command_log_sha256"] == sha(z.read("runtime/compiler-commands.jsonl")), tag + " runtime commands")
            require(runtime["state_sha256"] == sha(z.read("runtime/state.json")), tag + " runtime state")
            dependency_records.append(load("dependencies.json"))
            input_hashes = {Path(p).name: h for p, h in load("runtime/state.json")["input_sha256"].items()}
            for path in ["lean-toolchain", "lake-manifest.json"]:
                require(sha((ROOT / path).read_bytes()) == input_hashes[path], "dependency pin changed: " + path)
            lines = z.read("batch-types.log").decode().splitlines()
            ds = [json.loads(line[15:]) for line in lines if line.startswith("P0_ROUND6_DECL ")]
            inv = [json.loads(line[21:]) for line in lines if line.startswith("P0_ROUND6_SERIALIZED ")]
            require(len(ds) == acceptance["complete_serialized_declarations"], tag + " full declaration count")
            require(len({d["name"] for d in ds}) == len(ds), tag + " duplicate declaration")
            require(len(inv) == len(acceptance["modules"]) and {x["module"] for x in inv} == set(acceptance["modules"]), tag + " serialized coverage")
            for item in inv:
                names = {d["name"] for d in ds if d["module"] == item["module"]}
                require(names == set(item["serialized_constant_names"]) == set(item["environment_constant_names"]), tag + " declaration census: " + item["module"])
            for d in ds:
                require(not (d["is_axiom"] or d["is_partial"] or d["is_unsafe"]), "unsafe/admitted declaration: " + d["name"])
                require(set(d["axioms"]) <= ALLOWED, "unapproved axiom: " + d["name"])
                require(all(d[k].strip() and "⋯" not in d[k] for k in ["type", "readable_type"]), "incomplete type: " + d["name"])
                if d["module"] in selected:
                    require(d["name"] not in declarations or declarations[d["name"]] == d, "shared declaration conflict: " + d["name"])
                    declarations[d["name"]] = d
            count = sum(d["module"] in selected for d in ds)
            require(count == expected["declarations"], tag + " selected declaration count")
            for module in sorted(selected):
                row = records[module]
                digest = overlays.get(module, {}).get("candidate_sha256", row["sha256"])
                path = row["install_path"]
                require(objects[path] == digest, "historical source binding: " + path)
                data = (ROOT / path).read_bytes()
                require(sha(data) == digest, "source hash mismatch: " + path)
                require(imports(data.decode()) == row["imports"], "import graph changed: " + path)
                require(path not in sources or sources[path] == digest, "shared source conflict: " + path)
                sources[path] = digest
            summaries[tag] = {"run": expected["run"], "selected_modules": len(selected), "selected_declarations": count,
                              "original_modules": len(acceptance["modules"]), "original_declarations": len(ds),
                              "selected_overlays": sorted(selected & overlays.keys())}
    require(dependency_records[0] == dependency_records[1], "historical dependency revisions differ")
    actual = {str(p.relative_to(ROOT)) for p in (ROOT / "ImbalancedChen").rglob("*.lean")}
    require(actual == set(sources), "extra or missing production module")
    require(imports((ROOT / "ImbalancedChen.lean").read_text()) == [e["root"] for e in EXPECTED.values()], "aggregate root changed")
    require(len(sources) == 69 and len(declarations) == 1880, "combined census changed")
    source_list = "".join(digest + "  " + path + "\n" for path, digest in sorted(sources.items()))
    require(sha(source_list.encode()) == "2e72fddba29d838fa1869c072f6c4924b511a12dc5f8df36851137617c6baa1f", "combined source fingerprint")
    result = {"status": "PASS_HISTORICAL_SOURCE_AND_DECLARATION_ACCEPTANCE", "modules": 69,
              "complete_serialized_declarations": 1880, "source_list_sha256": sha(source_list.encode()),
              "source_bytes": sum((ROOT / p).stat().st_size for p in sources), "historical_runs": summaries,
              "configuration_sha256": CONFIGURATION,
              "allowed_transitive_axioms": sorted(ALLOWED), "new_root_compilation_checked_by_this_script": False,
              "unconditional_main_theorem_complete": False}
    if "--write" in sys.argv[1:]:
        (HERE / "source-manifest.json").write_text(json.dumps(sources, indent=2, sort_keys=True) + "\n")
        (HERE / "historical-receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        raise SystemExit("FAIL: " + str(error)) from error
