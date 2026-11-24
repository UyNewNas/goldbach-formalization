"""Aggregate existing P3 receipts without running Lean or creating a new audit.

Pass --receipt DIRECTORY repeatedly, oldest first. Each directory must contain
report.json, declarations.json and the original verification.zip. The last
complete inventory for each defining module wins; a stale last version fails
instead of falling back. --output defaults to '-' (JSON on stdout).
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import zipfile

sys.dont_write_bytecode = True
import verify_part3_continuation as continuation
import verify_part3_distribution as baseline

ROOT = Path(__file__).resolve().parents[1]
SCOPE = "Existing receipt evidence only; no new Lean compilation, kernel replay or axiom audit."


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


@lru_cache(maxsize=None)
def git_bytes(*args: str) -> bytes:
    result = subprocess.run(["git", *args], cwd=ROOT, capture_output=True)
    require(result.returncode == 0, "git " + " ".join(args) + ": " +
            result.stderr.decode(errors="replace").strip())
    return result.stdout


def read_receipt(directory: Path) -> dict:
    """Validate the saved evidence, including inventories, without executing it."""
    raw = {name: (directory / name).read_bytes()
           for name in ("report.json", "declarations.json", "verification.zip")}
    report = json.loads(raw["report.json"])
    modules = tuple(report["modules"])
    require(report["status"] == "PASSED", "Receipt status is not PASSED")
    require(modules and len(set(modules)) == len(modules) and
            set(modules) <= set(continuation.MODULES), "Invalid receipt module coverage")
    require(report["allowed_transitive_axioms"] == sorted(baseline.ALLOWED),
            "Changed transitive axiom allowlist")
    head = report["head_commit"]
    require(isinstance(head, str) and re.fullmatch(r"[0-9a-f]{40}", head),
            "Receipt head must be a full commit SHA")
    require(report["baseline_commit"] == continuation.BASELINE_HEAD, "Changed baseline")
    sources = report["source_sha256"]
    for relative, expected in sources.items():
        path = PurePosixPath(relative)
        require(not path.is_absolute() and ".." not in path.parts and str(path) == relative,
                "Invalid recorded source path: " + relative)
        require(digest(git_bytes("show", head + ":" + relative)) == expected,
                "Recorded source hash differs from receipt commit: " + relative)
    for relative, expected in baseline.CONFIG_SHA256.items():
        require(sources.get(relative) == expected and
                digest((ROOT / relative).read_bytes()) == expected,
                "Frozen configuration differs: " + relative)
    for relative in (baseline.AUDIT, baseline.LEXER, "verification/verify_part3_distribution.py"):
        require(sources.get(relative) == digest((ROOT / relative).read_bytes()),
                "Original audit/validator changed: " + relative)
    require("verification/verify_part3_continuation.py" in sources,
            "Missing continuation verifier source binding")
    require(all(module_path(m) in sources for m in modules), "Missing owned source hash")

    with zipfile.ZipFile(io.BytesIO(raw["verification.zip"])) as archive:
        names = archive.namelist()
        require(len(set(names)) == len(names), "Duplicate ZIP entries")
        for name in ("report.json", "declarations.json"):
            require(archive.read(name) == raw[name], "ZIP/adjacent bytes differ: " + name)
        audit = archive.read("Part3ContinuationAudit.lean")
        require(digest(audit) == report["generated_audit_sha256"] and
                audit == continuation.render_audit(modules).encode(),
                "Generated audit differs from the original complete audit body")
        stages, logs = {}, {}
        for stage in report["stages"]:
            name = stage["name"]
            require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]+", name) and
                    name not in stages, "Invalid or duplicate stage name")
            require(type(stage["exit_code"]) is int and stage["exit_code"] == 0,
                    "Stage did not succeed: " + name)
            data = archive.read(name + ".log")
            require(digest(data) == stage["log_sha256"], "Stage log hash mismatch: " + name)
            header, separator, body = data.decode().partition("\n")
            require(separator and header.startswith("command=") and
                    json.loads(header[len("command="):]) == stage["command"],
                    "Stage command/log mismatch: " + name)
            stages[name], logs[name] = stage, body

    def command(name: str, expected: list[str]) -> None:
        require(name in stages and stages[name]["command"] == expected,
                "Missing or changed stage command: " + name)

    command("head", ["git", "rev-parse", "HEAD"])
    require(logs["head"].strip() == head, "Head log differs from report")
    command("baseline-ancestor", ["git", "merge-base", "--is-ancestor",
                                  continuation.BASELINE_HEAD, head])
    for name in ("working-tree", "final-working-tree"):
        command(name, ["git", "status", "--porcelain", "--untracked-files=all"])
        require(not logs[name].strip(), "Receipt working tree was dirty: " + name)
    command("baseline-proof-preservation", ["git", "diff", "--name-only",
            continuation.BASELINE_HEAD, "--", *(module_path(m) for m in baseline.MODULES)])
    require(not logs["baseline-proof-preservation"].strip(), "Baseline proofs changed")
    command("lean-version", ["lake", "env", "lean", "--version"])
    version = logs["lean-version"].strip()
    require(version == report["lean_version"] and
            re.search(r"\bversion 4\.33\.0-rc1(?:,|\))", version) and
            continuation.LEAN_COMMIT in version, "Compiler version binding differs")
    require("bundled-tools" in logs and json.loads(logs["bundled-tools"]) == report["tool_paths"],
            "Bundled tool evidence differs")
    tool_paths = report["tool_paths"]
    for name in ("lean", "leanchecker"):
        path = tool_paths[name]
        require(PurePosixPath(path) == PurePosixPath(tool_paths["sysroot"]) / "bin" / name and
                re.fullmatch(r"[0-9a-f]{64}", report["tool_sha256"].get(path, "")),
                "Missing bundled tool/hash binding: " + name)
    manifest = json.loads((ROOT / "lake-manifest.json").read_bytes())
    for package in manifest["packages"]:
        pin, clean = "pin-" + package["name"], "clean-" + package["name"]
        require(pin in stages, "Missing dependency pin stage: " + pin)
        pin_command = stages[pin]["command"]
        require(len(pin_command) == 5 and pin_command[:2] == ["git", "-C"] and
                pin_command[2].endswith("/.lake/packages/" + package["name"]),
                "Wrong dependency checkout: " + pin)
        repo = pin_command[2]
        command(pin, ["git", "-C", repo, "rev-parse", "HEAD"])
        command(clean, ["git", "-C", repo, "status", "--porcelain", "--untracked-files=all"])
        require(logs[pin].strip() == package["rev"] and not logs[clean].strip(),
                "Dependency revision/cleanliness differs: " + package["name"])
    command("build-new-targets", ["lake", "build", *modules])
    lean = ["lake", "env", tool_paths["lean"], "-t0", "-j1", "-DwarningAsError=true"]
    for module in modules:
        stem = module.rsplit(".", 1)[1]
        strict, replay = stem + "-strict", stem + "-replay"
        obj = ".lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
        require(strict in stages, "Missing strict stage: " + module)
        cmd = stages[strict]["command"]
        require(len(cmd) == 9 and cmd[7].endswith("/" + obj), "Wrong strict object: " + module)
        command(strict, [*lean, "-o", cmd[7], module_path(module)])
        require(re.fullmatch(r"[0-9a-f]{64}", report["olean_sha256"].get(obj, "")),
                "Missing verified object hash: " + module)
        command(replay, ["lake", "env", tool_paths["leanchecker"], "--verbose", module])
        require("replaying " + module in logs[replay].splitlines(),
                "Missing literal replay evidence: " + module)
    require("axioms" in stages, "Missing complete axiom audit stage")
    cmd = stages["axioms"]["command"]
    require(len(cmd) == 7 and PurePosixPath(cmd[-1]).name == "Part3ContinuationAudit.lean",
            "Wrong axiom audit command")
    command("axioms", [*lean, cmd[-1]])
    records, counts = baseline.validate_inventory(logs["axioms"], modules=modules)
    require(records == json.loads(raw["declarations.json"]) and
            counts == report["module_counts"] and len(records) == report["declaration_count"],
            "Report/declarations differ from the complete audited inventory")
    return {"directory": str(directory), "report": report, "records": records,
            "file_sha256": {name: digest(data) for name, data in raw.items()},
            "verified_stage_count": len(stages)}


def local_import_closure(module: str, head: str, current: dict[str, bytes]) -> dict[str, str]:
    """Compare actual local source bytes; external imports retain receipt pin evidence."""
    past = set(git_bytes("ls-tree", "-r", "--name-only", head).decode().splitlines())
    pending, result = [module_path(module)], {}
    while pending:
        relative = pending.pop()
        if relative in result:
            continue
        data = (ROOT / relative).read_bytes()
        require(data == git_bytes("show", head + ":" + relative),
                "Local import source differs from receipt commit: " + relative)
        current[relative] = data
        result[relative] = digest(data)
        code = baseline.lean_code(data.decode())
        imports = re.findall(r"(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)?import[ \t]+([^\n]+)$", code)
        require(len(imports) == len(re.findall(r"\bimport\b", code)),
                "Unsupported import syntax; cannot certify closure: " + relative)
        for line in imports:
            for name in line.split():
                require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name),
                        "Unsupported imported module name: " + name)
                imported = module_path(name)
                if imported in past or (ROOT / imported).is_file():
                    pending.append(imported)
    return dict(sorted(result.items()))


def aggregate(directories: list[Path]) -> dict:
    result = {"status": "FAILED", "scope": SCOPE, "p3_overall_status": "OPEN",
              "created_utc": datetime.now(timezone.utc).isoformat(),
              "selection_policy": "Last complete defining-module inventory in receipt order; no name deduplication.",
              "required_modules": list(continuation.MODULES), "receipts": [], "errors": []}
    errors, selected, current = result["errors"], {}, {}
    for directory in directories:
        try:
            receipt = read_receipt(directory.resolve())
            index = len(result["receipts"])
            report = receipt["report"]
            result["receipts"].append({k: receipt[k] for k in
                ("directory", "file_sha256", "verified_stage_count")} | {
                "head_commit": report["head_commit"], "modules": report["modules"],
                "declaration_count": report["declaration_count"]})
            for module in report["modules"]:
                selected[module] = (index, receipt)
        except (OSError, ValueError, KeyError, TypeError, RuntimeError, zipfile.BadZipFile) as error:
            errors.append({"kind": "invalid_receipt", "receipt": str(directory), "error": str(error)})
    selections, records = [], []
    for module in continuation.MODULES:
        if module not in selected:
            errors.append({"kind": "missing_module", "module": module})
            continue
        index, receipt = selected[module]
        report, relative = receipt["report"], module_path(module)
        try:
            data = (ROOT / relative).read_bytes()
            actual, expected = digest(data), report["source_sha256"][relative]
            if actual != expected:
                errors.append({"kind": "source_mismatch", "module": module,
                               "receipt_index": index, "expected": expected, "actual": actual})
                continue
            closure = local_import_closure(module, report["head_commit"], current)
            owned = [r for r in receipt["records"] if r["module"] == module]
            selections.append({"module": module, "receipt_index": index,
                "head_commit": report["head_commit"], "source_sha256": actual,
                "declaration_count": len(owned), "local_import_sha256": closure})
            records.extend(owned)
        except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
            errors.append({"kind": "import_closure_mismatch", "module": module, "error": str(error)})
    if len({r["name"] for r in records}) != len(records):
        errors.append({"kind": "duplicate_selected_declaration", "error": "Conflicting names across selected modules"})
    for relative, data in current.items():
        if not (ROOT / relative).is_file() or (ROOT / relative).read_bytes() != data:
            errors.append({"kind": "source_changed_during_aggregation", "path": relative})
    for receipt in result["receipts"]:
        for name, expected in receipt["file_sha256"].items():
            path = Path(receipt["directory"]) / name
            if not path.is_file() or digest(path.read_bytes()) != expected:
                errors.append({"kind": "receipt_changed_during_aggregation", "path": str(path)})
    if not errors:
        result.update(status="AGGREGATED_FROM_PASSED_RECEIPTS", modules=selections,
                      declaration_count=len(records), declarations=records,
                      allowed_transitive_axioms=sorted(baseline.ALLOWED))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, action="append", required=True,
                        help="Saved receipt directory; later complete module inventories replace earlier ones")
    parser.add_argument("--output", default="-", help="Aggregate JSON path, or '-' for stdout")
    args = parser.parse_args()
    result = aggregate(args.receipt)
    text = json.dumps(result, indent=2) + "\n"
    if args.output == "-":
        print(text, end="")
    else:
        output = Path(args.output)
        require(output.resolve() not in {directory.resolve() / name for directory in args.receipt
                for name in ("report.json", "declarations.json", "verification.zip")},
                "Output must not overwrite receipt evidence")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text)
    raise SystemExit(1 if result["errors"] else 0)


if __name__ == "__main__":
    main()
