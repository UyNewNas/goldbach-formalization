#!/usr/bin/env python3
"""Validate and import the fixed P2.10 CI collection without compiling or replaying.

Run in the original P2 verification worktree, with its accepted private cache
idle. Supply the run/commit and index SHA observed when downloading the trusted
GitHub collection. --check-only performs the same verification without changing
the worktree. Temporary extraction is not an acceptance or a compiler cache.

Only pages 128..689 and Checks 08..43 may be installed. Existing target records,
objects, audit directories or logs cause rejection, even if their bytes agree.
Original receipts and their historical paths are preserved, not rewritten.
Same-filesystem transfers use exclusive hard links; EXDEV transfers copy.
Incoming bootstrap objects are streamed and hashed before reusing local storage.
Each fully verified block releases its extraction directories; all blocks must
still pass before the final registry commit.
"""
from __future__ import annotations

import argparse
from collections import Counter
import errno
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import tarfile
import tempfile
import zipfile

import run_winner9_private_checks as C
import run_winner9_private_audit as A
import export_winner9_private_evidence as E

PREFIX = "ImbalancedChen.P2Winner9"
PRIVATE = ".lake/p2-private"
CONTROL = ".lake/p210-ci"
RESUME = ".lake/p210-resume"
RESUME_PLAN = "verification/part2/p210_resume_plan.json"
FIXED_BOOTSTRAP = {
    "artifact_id": 15013442313, "artifact_name": "p210-bootstrap-45589950483-1",
    "run_id": "45589950483", "run_attempt": 1,
    "commit": "8bb6eac5aae11d217fb29324e1db7685954d30ac", "zip_bytes": 413971373,
    "zip_sha256": "8a3e7275fafe9b5b0046a541d320fd4669dd413a5444384ff782c3873d16c76c",
    "tar_sha256": "e17d879ab60ad21874b8b26ce20075a1b646af82ee18cf00749773ba5dc37370",
    "manifest_sha256": "d0c466739000ffe4351612a751123ae22db6f088c27cd71d640d1649dd6a5771",
    "records_sha256": "ee3d1b8d4dd962ba4195b90299062ab972de82422cb24114822a1a5442e77689",
}
FACETS = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")
KEYS = ("module", "source_sha256", "object_sha256", "toolchain", "cache_schema",
        "deps", "dependency_signatures", "closure_signature", "exit_code")
GATES = {"strict_compile": True, "stock_leanchecker": True,
         "owned_declarations_and_axioms": True}
DRIVER_HASHES = {
    C.__file__: "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    A.__file__: "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    E.__file__: "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
}
LEAN_SHA = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
CHECKER_SHA = "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
need = A.require


def read(path: Path):
    return json.loads(path.read_bytes())


def stable(record: dict) -> dict:
    return {key: record[key] for key in KEYS}


def safe_name(name: str) -> str:
    path = PurePosixPath(name)
    need(name and not path.is_absolute() and ".." not in path.parts
         and "\\" not in name and path.as_posix() == name and name != ".",
         "Unsafe archive or destination path: " + name)
    return name


def exclusive_link_or_copy(source: Path, destination: Path, expected: str) -> None:
    """Preserve bytes and reject existing destinations on either filesystem."""
    need(source.is_file() and not source.is_symlink(), "Not a regular input file: " + str(source))
    destination.parent.mkdir(parents=True, exist_ok=True)
    created = False
    try:
        try:
            os.link(source, destination, follow_symlinks=False)
            created = True
        except OSError as error:
            if error.errno != errno.EXDEV:
                raise
            need(shutil.disk_usage(destination.parent).free >= source.stat().st_size,
                 "Insufficient space for cross-filesystem copy: " + str(destination))
            with source.open("rb") as incoming, destination.open("xb") as outgoing:
                created = True
                shutil.copyfileobj(incoming, outgoing)
        need(C.digest(destination) == expected, "File changed during transfer: " + str(source))
    except BaseException:
        if created:
            destination.unlink(missing_ok=True)
        raise


def unpack_tar(path: Path, destination: Path,
               reuse: dict[str, tuple[Path, str]] | None = None) -> dict[str, str]:
    reuse = reuse or {}
    files = {}
    with tarfile.open(path) as archive:
        for member in archive:
            name = safe_name(member.name)
            need(member.isfile() and name not in files, "Linked, special or duplicate tar member: " + name)
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            if name in reuse:
                source, expected = reuse[name]
                need(member.size == source.stat().st_size, "Reusable tar object size differs: " + name)
                digest, size = hashlib.sha256(), 0
                with archive.extractfile(member) as incoming:
                    while chunk := incoming.read(1024 * 1024):
                        digest.update(chunk)
                        size += len(chunk)
                need(size == member.size and digest.hexdigest() == expected,
                     "Reusable tar object bytes differ: " + name)
                exclusive_link_or_copy(source, target, expected)
                files[name] = digest.hexdigest()
            else:
                with archive.extractfile(member) as incoming, target.open("xb") as outgoing:
                    shutil.copyfileobj(incoming, outgoing)
                files[name] = C.digest(target)
    need(set(reuse) <= set(files), "Missing reusable dependency object in tar")
    return files


def unpack_zip(path: Path, destination: Path) -> dict[str, str]:
    files = {}
    with zipfile.ZipFile(path) as archive:
        for member in archive.infolist():
            name = safe_name(member.filename)
            mode = member.external_attr >> 16
            need(not member.is_dir() and not stat.S_ISLNK(mode)
                 and stat.S_IFMT(mode) in (0, stat.S_IFREG) and name not in files,
                 "Linked, special or duplicate ZIP member: " + name)
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            with archive.open(member) as incoming, target.open("xb") as outgoing:
                shutil.copyfileobj(incoming, outgoing)
            files[name] = C.digest(target)
    return files


def targets(block: int) -> list[str]:
    return [PREFIX + f"NumericalPage{page:04}" for page in range(16 * block, min(16 * (block + 1), 690))] + [
        PREFIX + f"NumericalCheck{block:02}"]


def nodes(root: Path, roots: list[str]) -> dict:
    result = {}
    for module in roots:
        result.update(A.project_nodes(root, module))
    return result


def binding(module: str) -> dict:
    page = int(module[-4:])
    count = min(16, 11026 - 16 * page)
    return {"page": page, "first_ordinal": 16 * page, "row_count": count,
            "last_ordinal": 16 * page + count - 1, "block": page // 16, "local_page": page % 16}


def export_gate(manifest: dict, wanted: list[str]) -> None:
    need(set(manifest["accepted_modules"]) == set(wanted)
         and manifest["accepted_module_count"] == len(wanted)
         and not manifest["unselected_modules"] and not manifest["rejected_candidates"]
         and not manifest["duplicate_owned_declarations"], "Incomplete or rejected block export")
    coverage = manifest["coverage"]["numerical_pages"]
    expected = {module: binding(module) for module in wanted[:-1]}
    need(coverage["bindings"] == expected and coverage["accepted_bound_pages"] == len(expected)
         and coverage["covered_rows"] == sum(item["row_count"] for item in expected.values()),
         "Incorrect original numerical page intervals")


def unchanged(paths: dict[Path, str]) -> None:
    for path, digest in paths.items():
        need(path.is_file() and C.digest(path) == digest, "Verified input changed: " + str(path))


def discard_block_extractions(directories: tuple[Path, ...], evidence: E.Evidence) -> None:
    """Remove this import's temporary copies only after frozen paths are safe."""
    for directory in directories:
        need(not any(path.resolve().is_relative_to(directory.resolve()) for path in evidence.frozen),
             "Extraction still contains a frozen input: " + str(directory))
    for directory in directories:
        shutil.rmtree(directory)


def no_destination(root: Path, relative: str) -> None:
    path = root / safe_name(relative)
    for parent in (path, *path.parents):
        if parent == root:
            break
        need(not parent.is_symlink(), "Destination contains a symlink: " + str(parent))
    need(not path.exists(), "Existing cache/evidence is never overwritten: " + str(path))


def resume_plan(root: Path, index: dict) -> dict | None:
    """Bind a resumed collection to its published plan and original bootstrap."""
    if index.get("schema", 1) == 1:
        need("bootstrap_origin" not in index, "Legacy collection cannot claim a foreign bootstrap")
        return None
    need(index.get("schema") == 2, "Unsupported collection schema")
    path = root / RESUME_PLAN
    need(path.is_file() and not path.is_symlink() and C.digest(path) == index["plan_sha256"],
         "Resume plan differs from the published receiver source")
    plan = read(path)
    need(plan["schema"] == 1 and plan["source_commit"] == FIXED_BOOTSTRAP["commit"]
         and plan["bootstrap"] == index["bootstrap_origin"] == FIXED_BOOTSTRAP,
         "Resume bootstrap is not the exact successful public producer")
    need(plan["importer_sha256"] == C.digest(Path(__file__)), "Resume importer differs from the reviewed plan")
    ids = [item["artifact_id"] for item in plan["recovery_inputs"]]
    need(len(ids) == len(set(ids)), "Duplicate recovery artifact in the published plan")
    return plan


def original_registry(archive_path: Path, item: dict) -> tuple[bytes, dict[str, set[str]]]:
    """Read original bytes from a pinned public checkpoint; never rewrite receipts."""
    need(archive_path.stat().st_size == item["zip_bytes"]
         and C.digest(archive_path) == item["zip_sha256"], "Original recovery ZIP changed")
    member = ("p210-ci/recovery/new-objects-records-and-receipts.tar.gz"
              if item["format"] == "block-recovery-v1" else "proof-and-original-evidence.tar.gz")
    need(item["format"] in ("block-recovery-v1", "page-probe-v1", "slot-v1"),
         "Unsupported original checkpoint format")
    registry, receipts, names = None, {}, set()
    with zipfile.ZipFile(archive_path) as package:
        need(len(package.namelist()) == len(set(package.namelist())) and member in package.namelist(),
             "Duplicate or missing original recovery ZIP member")
        with package.open(member) as stream:
            digest = hashlib.sha256()
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
        need(digest.hexdigest() == item["tar_sha256"], "Original recovery tar changed")
        with package.open(member) as stream, tarfile.open(fileobj=stream, mode="r|gz") as archive:
            for entry in archive:
                name = safe_name(entry.name)
                need(name not in names and entry.isfile(), "Duplicate or non-file original recovery member")
                names.add(name)
                if name == PRIVATE + "/records.json":
                    need(entry.size <= 32 * 1024 * 1024, "Unexpected original registry size")
                    registry = archive.extractfile(entry).read()
                elif name.startswith(PRIVATE + "/audit/") and name.endswith(("/receipt.json", "/latest.json")):
                    data = archive.extractfile(entry).read()
                    value = json.loads(data)
                    receipts.setdefault(value["module"], set()).add(hashlib.sha256(data).hexdigest())
    need(registry is not None, "Original recovery archive omits its compilation registry")
    return registry, receipts


def resume_origins(raw: Path, files: dict, info: dict, plan: dict, wanted: list[str]) -> tuple[set[str], dict]:
    """Qualify every claimed reuse against the unmodified public source ZIP."""
    plan_path = RESUME + "/resume-plan.json"
    need(plan_path in files and C.digest(raw / plan_path) == info["plan_sha256"]
         and read(raw / plan_path) == plan, "Block did not preserve the original resume plan")
    expected = {str(item["artifact_id"]): item for item in plan["recovery_inputs"] if item["block"] == info["block"]}
    need(set(info["origins"]) == set(expected), "Block recovery origins differ from the published plan")
    controls, verified = {plan_path}, {}
    for key, item in expected.items():
        origin = info["origins"][key]
        zip_path, records_path = RESUME + "/origins/" + key + "/source.zip", RESUME + "/origins/" + key + "/records.json"
        need(origin == dict(item, zip_path=zip_path, records_path=records_path), "Changed recovery origin metadata")
        need(zip_path in files and records_path in files, "Missing original recovery transport or registry")
        registry, receipts = original_registry(raw / zip_path, item)
        need((raw / records_path).read_bytes() == registry, "Recovery registry is not the original producer bytes")
        records = json.loads(registry)
        successful = {name for name in wanted if name in records and records[name].get("exit_code") == 0
                      and records[name].get("new_strict_compile") is True}
        need(set(item["modules"]) <= successful, "Recovery plan claims an unsuccessful compilation")
        if item["format"] == "block-recovery-v1":
            need(set(item["modules"]) == successful, "Recovery plan omits an already compiled page")
        controls.update((zip_path, records_path))
        verified[key] = {"item": item, "records": records, "receipts": receipts}
    need(set(info["module_origins"]) == set(wanted), "Missing or unexpected numerical module origin")
    return controls, verified


def strict_command(module: str, record: dict, memory_mb: int) -> list[str]:
    need(memory_mb in (6144, 11264), "Unsupported original strict compilation memory limit")
    return [C.LEAN, "-t0", "-j1", f"-M{memory_mb}", "-DwarningAsError=true",
            "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", "-o", record["object"],
            module.replace(".", "/") + ".lean"]


def compile_origin(raw: Path, files: dict, info: dict, module: str, record: dict,
                   verified: dict, controls: set[str]) -> list[str]:
    origin = info["module_origins"][module]["compile"]
    key = origin["artifact_id"]
    if key is None:
        need(not any(module in value["item"]["modules"] for value in verified.values()),
             "A previously compiled module was incorrectly reported as a new compilation")
        need(origin["reused"] is False and origin["memory_mb"] == 11264
             and all(origin[k] == info[k] for k in ("run_id", "commit"))
             and int(origin["run_attempt"]) == int(info["run_attempt"]), "False current-run compilation origin")
        path = RESUME + "/slots/" + module + "/compile-records.json"
    else:
        value = verified.get(str(key))
        need(value is not None and module in value["item"]["modules"] and origin["reused"] is True,
             "Compilation reuse is absent from the pinned original artifact")
        need(all(origin[k] == value["item"][k] for k in ("run_id", "commit"))
             and int(origin["run_attempt"]) == value["item"]["run_attempt"], "Wrong original compilation producer")
        path = RESUME + "/origins/" + str(key) + "/records.json"
    need(origin["records_path"] == path and path in files
         and C.digest(raw / path) == origin["records_sha256"], "Missing original compilation registry snapshot")
    original = read(raw / path)[module]
    need({k: v for k, v in original.items() if k != "object"} == {k: v for k, v in record.items() if k != "object"},
         "Original compilation record was rewritten beyond its object locator")
    command = strict_command(module, original, origin["memory_mb"])
    need(original["command"] == command and original["attempts"][-1]["command"] == command,
         "Compilation parameters differ from their original producer")
    controls.add(path)
    return command


def audit_origin(raw: Path, files: dict, info: dict, module: str, receipt_sha256: str,
                 verified: dict) -> None:
    origin = info["module_origins"][module]["audit"]
    path = RESUME + "/slots/" + module + "/selected-receipt.json"
    need(origin["receipt_path"] == path and path in files
         and C.digest(raw / path) == origin["receipt_sha256"] == receipt_sha256,
         "Audit origin does not preserve the selected original receipt")
    need(origin["reuse"] in ("fresh", "exact", "relocated", "replay"), "Unknown audit reuse boundary")
    if origin["artifact_id"] is None:
        need(origin["reuse"] in ("fresh", "replay")
             and all(origin[k] == info[k] for k in ("run_id", "commit"))
             and int(origin["run_attempt"]) == int(info["run_attempt"]), "False current-run audit origin")
    else:
        original = verified.get(str(origin["artifact_id"]))
        need(original is not None and module in original["item"]["modules"]
             and origin["reuse"] in ("exact", "relocated")
             and all(origin[k] == original["item"][k] for k in ("run_id", "commit"))
             and int(origin["run_attempt"]) == original["item"]["run_attempt"]
             and receipt_sha256 in original["receipts"].get(module, set()),
             "Accepted audit reuse differs from the original public receipt")


def validate(root: Path, incoming: Path, temporary: Path, args) -> dict:
    index_path = incoming / "index.json"
    need(C.digest(index_path) == args.index_sha256, "Collection index differs from the trusted download")
    index = read(index_path)
    need(index["commit"] == args.commit and index["run_id"] == args.run_id,
         "Wrong CI source commit or workflow run")
    plan_input = resume_plan(root, index)
    control = RESUME if plan_input else CONTROL
    attempt = int(index["run_attempt"])
    producer = int(index["bootstrap_producer_attempt"])
    need(attempt >= 1 and (producer == FIXED_BOOTSTRAP["run_attempt"] if plan_input else 1 <= producer <= attempt)
         and index["new_pages"] == 562 and index["new_rows"] == 8978
         and index["old_rows_replayed"] == 0 and index["terminal_integrated"] is False,
         "Unexpected collection scope or producer attempt")
    blocks = {f"{block:02}": targets(block) for block in range(8, 44)}
    new_targets = {module for wanted in blocks.values() for module in wanted}
    need(len(new_targets) == 598 and set(index["blocks"]) == set(blocks), "Incomplete or overlapping blocks")
    expected_files = {"index.json", "bootstrap.tar.gz", *(f"block-{block}.zip" for block in blocks)}
    need({path.name for path in incoming.iterdir()} == expected_files
         and all((incoming / name).is_file() and not (incoming / name).is_symlink() for name in expected_files),
         "Collection contains missing, linked or unexpected files")
    inputs = {incoming / name: C.digest(incoming / name) for name in expected_files}
    if plan_input:
        inputs[root / RESUME_PLAN] = index["plan_sha256"]
        inputs[Path(__file__)] = plan_input["importer_sha256"]
        need(index["bootstrap_sha256"] == FIXED_BOOTSTRAP["tar_sha256"], "Changed original bootstrap transport")
    need(inputs[incoming / "bootstrap.tar.gz"] == index["bootstrap_sha256"], "Bootstrap transport changed")
    for path, expected in DRIVER_HASHES.items():
        need(C.digest(Path(path)) == expected, "Original verification driver changed: " + path)
        inputs[Path(path)] = expected
    need(C.digest(Path(C.LEAN)) == LEAN_SHA and C.digest(Path(A.LEANCHECKER)) == CHECKER_SHA,
         "Lean or stock leanchecker differs from the accepted environment")
    toolchain = {"lean_version": subprocess.check_output([C.LEAN, "--version"], text=True).strip(),
                 "lean_binary_sha256": LEAN_SHA,
                 "mathlib_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=C.MATHLIB, text=True).strip()}
    need(toolchain["mathlib_commit"] == C.PIN, "Mathlib differs from the pinned environment")
    for path in (Path(C.LEAN), Path(A.LEANCHECKER), A.TEMPLATE):
        inputs[path] = C.digest(path)

    common = nodes(root, [PREFIX + "MaterializedLogChecker", PREFIX + "SeedArchiveChecks"])
    seeds = [PREFIX + f"CompleteSeedBlock{block:02}" for block in range(8, 44)]
    base = nodes(root, [*common, *seeds])
    need(len(common) == 57 and len(base) == 93 and set(base) == set(common) | set(seeds),
         "Local 93-module dependency coverage mismatch")
    records_path = root / PRIVATE / "records.json"
    old_raw = records_path.read_bytes()
    old_records = json.loads(old_raw)
    inputs[records_path] = hashlib.sha256(old_raw).hexdigest()
    need(set(base) <= set(old_records) and not new_targets.intersection(old_records),
         "Missing old dependencies or already recorded numerical targets")
    old_snapshot = A.snapshot(root, root / PRIVATE / "lib", base, toolchain)
    A.verify_compilation(old_records, base, old_snapshot)
    reusable = {}
    for module in base:
        relative = PRIVATE + "/lib/" + module.replace(".", "/") + ".olean"
        obj = root / relative
        inputs[obj] = old_records[module]["object_sha256"]
        reusable[relative] = (obj, old_records[module]["object_sha256"])

    boot = temporary / "bootstrap"
    boot_files = unpack_tar(incoming / "bootstrap.tar.gz", boot, reuse=reusable)
    sealed = read(boot / CONTROL / "bootstrap.json")
    if plan_input:
        need(C.digest(boot / CONTROL / "bootstrap.json") == FIXED_BOOTSTRAP["manifest_sha256"],
             "Changed original bootstrap seal")
    need(set(boot_files) == set(sealed["files"]) | {CONTROL + "/bootstrap.json"}
         and all(boot_files[name] == digest for name, digest in sealed["files"].items()),
         "Bootstrap inventory or file hash mismatch")
    plan = read(boot / CONTROL / "plan.json")
    bootstrap_origin = plan_input["bootstrap"] if plan_input else {"commit": args.commit, "run_id": args.run_id}
    for value in (plan, sealed):
        need(value["commit"] == bootstrap_origin["commit"] and value["run_id"] == bootstrap_origin["run_id"]
             and int(value["run_attempt"]) == producer, "Bootstrap provenance mismatch")
    need(plan["blocks"] == blocks and plan["shared_count"] == 57 and plan["seed_count"] == 36
         and plan["new_pages"] == 562 and plan["new_rows"] == 8978
         and plan["old_rows_replayed"] == 0 and plan["toolchain"] == toolchain
         and sealed["proof_credit"] == 0, "Unexpected bootstrap plan")
    reference_path = boot / CONTROL / "public-reference.json"
    need(C.digest(reference_path) == plan["public_reference_sha256"], "Public reference changed")
    reference = read(reference_path)
    bootstrap_records = read(boot / PRIVATE / "records.json")
    if plan_input:
        need(C.digest(reference_path) == C.digest(boot / PRIVATE / "records.json") == FIXED_BOOTSTRAP["records_sha256"],
             "Original bootstrap registry bytes changed")
    need(len(common) == 57 and len(base) == 93 and set(base) == set(common) | set(seeds)
         and plan["modules"] == sorted(base) and sealed["modules"] == sorted(base)
         and set(reference) == set(bootstrap_records) == set(base), "Public 93-module coverage mismatch")
    A.verify_compilation(bootstrap_records, base,
                         A.snapshot(root, boot / PRIVATE / "lib", base, toolchain))
    for module in base:
        need(stable(old_records[module]) == stable(reference[module]) == stable(bootstrap_records[module]),
             "Local accepted dependency differs from CI/public history: " + module)

    graph = nodes(root, [wanted[-1] for wanted in blocks.values()])
    need(set(graph) == set(base) | new_targets, "Unexpected complete numerical source closure")
    stage, archive = temporary / "worktree", temporary / "archive"
    stage.mkdir(); archive.mkdir()
    for module, node in graph.items():
        path = node["source"]
        inputs[path] = C.digest(path)
        destination = stage / path.relative_to(root)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
    for module in base:
        relative = PRIVATE + "/lib/" + module.replace(".", "/") + ".olean"
        exclusive_link_or_copy(boot / relative, stage / relative, old_records[module]["object_sha256"])
    new_records, install_files, owned = {}, {}, set()
    origin_counts = {"new_strict_compilations_in_run": 0, "reused_strict_compilations": 0,
                     "reused_accepted_audits": 0, "reused_stock_replays_for_new_audits": 0}
    evidence = E.Evidence()
    drivers = {C.digest(Path(A.__file__)): Path(A.__file__)}
    for block, wanted in blocks.items():
        saved = index["blocks"][block]
        zip_path = incoming / f"block-{block}.zip"
        need(inputs[zip_path] == saved["zip_sha256"], "Block ZIP hash mismatch: " + block)
        delivery = temporary / "blocks" / block / "delivery"
        delivered = unpack_zip(zip_path, delivery)
        info = read(delivery / "provenance.json")
        need(info == saved["provenance"] and info["block"] == block and info["modules"] == wanted
             and info["commit"] == args.commit and info["run_id"] == args.run_id
             and (1 if plan_input else producer) <= int(info["run_attempt"]) <= attempt
             and info["bootstrap_sha256"] == index["bootstrap_sha256"] and info["gates"] == GATES,
             "Block provenance or gates mismatch: " + block)
        if plan_input:
            need(info.get("schema") == 2 and info["bootstrap_origin"] == index["bootstrap_origin"]
                 and info["plan_sha256"] == index["plan_sha256"], "Resumed block origin or plan mismatch")
        need(set(delivered) == set(info["delivery_files"]) | {"provenance.json"}
             and all(delivered[name] == digest for name, digest in info["delivery_files"].items()),
             "Delivery inventory or file hash mismatch: " + block)
        manifest = read(delivery / "evidence/manifest.json")
        need(delivered["evidence/manifest.json"] == info["evidence_manifest_sha256"]
             and delivered["new-objects-and-receipts.tar.gz"] == info["object_archive_sha256"],
             "Evidence/object transport mismatch: " + block)
        export_gate(manifest, wanted)
        raw = temporary / "blocks" / block / "objects"
        raw_files = unpack_tar(delivery / "new-objects-and-receipts.tar.gz", raw)
        need(raw_files == info["files"], "Object/receipt file inventory mismatch: " + block)
        controls, verified_origins = resume_origins(raw, raw_files, info, plan_input, wanted) if plan_input else (set(), {})
        fresh = read(delivery / "new-records.json")
        need(set(fresh) == set(wanted) and (delivery / "new-records.json").read_bytes()
             == (raw / control / "delivery/new-records.json").read_bytes(), "Conflicting new compile registry")
        facets = {PRIVATE + "/lib/" + module.replace(".", "/") + suffix for module in wanted for suffix in FACETS}
        logs = set()
        for module, record in fresh.items():
            expected_command = (compile_origin(raw, raw_files, info, module, record, verified_origins, controls)
                                if plan_input else strict_command(module, record, 6144))
            need(record.get("new_strict_compile") is True and record["command"] == expected_command
                 and record["source"] == expected_command[-1] and record["exit_code"] == 0,
                 "Missing original strict compilation: " + module)
            checks = record["dependency_file_check"]
            need(checks["before_matches_records"] is True and checks["after_matches_records"] is True
                 and checks["expected_sha256"] == checks["before_sha256"] == checks["after_sha256"],
                 "Compilation dependency files were not frozen: " + module)
            module_logs = {record["log"], *(entry["log"] for entry in record["attempts"])}
            need(record["attempts"] and record["attempts"][-1]["exit_code"] == 0
                 and record["attempts"][-1]["command"] == expected_command,
                 "Missing successful original compile attempt: " + module)
            need(all(re.fullmatch(re.escape(PRIVATE + "/logs/" + module) + r"\.attempt[1-9][0-9]*\.log", name)
                     for name in module_logs), "Compile log belongs to another module")
            logs.update(module_logs)
            need(PRIVATE + "/lib/" + module.replace(".", "/") + ".olean" in raw_files,
                 "Missing numerical object: " + module)
        need(logs <= set(raw_files), "Missing original module compile logs")
        if plan_input:
            controls.update(RESUME + "/" + name for name in ("delivery/new-records.json", "resources.json", "state.json"))
            controls.update(RESUME + "/slots/" + module + "/" + name for module in wanted for name in
                            ("state.json", "compile-records.json", "selected-receipt.json", "compile.log", "compile.time.txt",
                             "audit.log", "audit.time.txt", "export.log", "export.time.txt"))
        else:
            controls = {CONTROL + "/" + name for name in
                        ("delivery/new-records.json", "compile.log", "export.log", "resources-shard.json", "audit-0.log", "audit-1.log")}
        for name, digest in raw_files.items():
            audit = any(name.startswith(PRIVATE + "/audit/" + module + "/") for module in wanted)
            if name in facets or name in logs or audit:
                need(name not in install_files, "Overlapping block installation path: " + name)
                exclusive_link_or_copy(raw / name, stage / name, digest)
                install_files[name] = digest
            else:
                need(name in controls, "Unapproved installation/control path: " + name)
                exclusive_link_or_copy(raw / name, archive / "blocks" / block / "control" / name, digest)
        new_records.update(fresh)
        records = dict(old_records, **new_records)
        local_nodes = A.project_nodes(stage, wanted[-1])
        frozen = A.snapshot(stage, stage / PRIVATE / "lib", local_nodes, toolchain)
        A.verify_compilation(records, local_nodes, frozen)
        need(set(manifest["object_manifest"]) == set(local_nodes), "Export dependency scope differs from sources")

        need(manifest["split"] == "all" and len(manifest["packages"]) == 1, "Expected one original all-evidence package")
        package = manifest["packages"][0]
        package_path = delivery / "evidence/all.tar.gz"
        need(package["sha256"] == C.digest(package_path) and package["bytes"] == package_path.stat().st_size
             and package["modules"] == sorted(wanted), "Exporter package binding mismatch")
        exported = temporary / "blocks" / block / "exported"
        exported_files = unpack_tar(package_path, exported)
        package_manifest = read(exported / "PACKAGE_MANIFEST.json")
        need(package_manifest["files"] == manifest["files"] and package_manifest["modules"] == sorted(wanted)
             and package_manifest["no_olean_objects"] is True
             and set(exported_files) == set(manifest["files"]) | {"PACKAGE_MANIFEST.json"}, "Exporter package inventory mismatch")
        for name, item in manifest["files"].items():
            need(exported_files[name] == item["sha256"] and (exported / name).stat().st_size == item["bytes"],
                 "Exporter evidence file changed: " + name)
        for name, digest in raw_files.items():
            if "worktree/" + name in exported_files:
                need(exported_files["worktree/" + name] == digest,
                     "Exported evidence differs from its original worktree file: " + name)
        need(read(exported / "EXPORT_METADATA.json") == {key: value for key, value in manifest.items() if key not in ("packages", "files")},
             "Exporter metadata mismatch")
        context = read(exported / "context/records.json")
        selected = read(exported / "context/selected-compile-records.json")
        need(C.digest(exported / "context/records.json") == manifest["records_snapshot_sha256"]
             and set(context) == set(base) | set(wanted) and set(selected) == set(local_nodes)
             and selected == {module: context[module] for module in local_nodes}
             and all(context[module] == fresh[module] for module in wanted)
             and all(stable(context[module]) == stable(reference[module]) for module in base),
             "Exported compile context differs from the exact bootstrap/new records")
        for module, actual in frozen["project"].items():
            item = manifest["object_manifest"][module]
            need(all(item[key] == actual[key] for key in ("source", "source_sha256", "object_sha256"))
                 and C.digest(exported / "sources" / actual["source"]) == actual["source_sha256"],
                 "Exported original source/object differs: " + module)
        declaration_count, axiom_counts = 0, Counter()
        for module in wanted:
            metadata = manifest["accepted_modules"][module]
            receipt_path = exported / "audits" / module / "selected-receipt.json"
            receipt_raw = receipt_path.read_bytes()
            receipt = json.loads(receipt_raw)
            if plan_input:
                audit_origin(raw, raw_files, info, module, C.digest(receipt_path), verified_origins)
                origin = info["module_origins"][module]
                if origin["audit"]["artifact_id"] is None:
                    need((origin["audit"]["reuse"] == "replay") == (receipt["replay"].get("reused") is True),
                         "Partial stock-replay reuse differs from the original auditor receipt")
                origin_counts["reused_strict_compilations" if origin["compile"]["reused"]
                              else "new_strict_compilations_in_run"] += 1
                origin_counts["reused_accepted_audits"] += int(origin["audit"]["artifact_id"] is not None)
                origin_counts["reused_stock_replays_for_new_audits"] += int(origin["audit"]["artifact_id"] is None
                                                                          and origin["audit"]["reuse"] == "replay")
            audit_directory = stage / PRIVATE / "audit" / module
            candidates = [*audit_directory.glob("attempt-*/receipt.json"), audit_directory / "latest.json"]
            need(C.digest(receipt_path) == metadata["receipt_sha256"]
                 and receipt["input_snapshot"]["driver_sha256"] in drivers
                 and any(path.is_file() and path.read_bytes() == receipt_raw for path in candidates),
                 "Selected original receipt was not preserved: " + module)
            checked = E.validate_receipt(stage, module, receipt, records, evidence, drivers)
            artifact_names = {"audits/" + module + "/selected-receipt.json"}
            artifact_names.update("worktree/" + name for name in receipt["artifacts"])
            need(set(metadata["artifact_paths"]) == artifact_names
                 and all(exported_files["worktree/" + name] == digest for name, digest in receipt["artifacts"].items()),
                 "Selected exported artifacts differ from the accepted receipt: " + module)
            parsed = checked["parsed"]
            expected = {"source_sha256": fresh[module]["source_sha256"], "object_sha256": fresh[module]["object_sha256"],
                        "compile_closure_signature": fresh[module]["closure_signature"],
                        "driver_sha256": receipt["input_snapshot"]["driver_sha256"],
                        "declaration_count": parsed["declaration_count"], "axiom_counts": parsed["axiom_counts"],
                        "project_modules": sorted(checked["project"]),
                        "page_binding": E.page_binding(module, (stage / fresh[module]["source"]).read_text(), parsed["declarations"])}
            need(all(metadata[key] == value for key, value in expected.items()), "Accepted metadata differs from original audit: " + module)
            names = {declaration["name"] for declaration in parsed["declarations"]}
            need(not owned.intersection(names), "Duplicate owned declaration across blocks")
            owned.update(names)
            declaration_count += parsed["declaration_count"]
            axiom_counts.update(parsed["axiom_counts"])
        need(manifest["owned_declaration_count"] == manifest["unique_owned_declaration_count"] == declaration_count
             and manifest["transitive_axiom_counts"] == dict(axiom_counts), "Export declaration/axiom totals differ")
        discard_block_extractions((delivery, raw, exported), evidence)
        print("VALIDATED", block, len(wanted) - 1, "pages; original receipts preserved", flush=True)

    need(set(new_records) == new_targets and len(new_records) == 598, "Incomplete new registry")
    if plan_input:
        need(all(index.get(key) == value for key, value in origin_counts.items()),
             "Collection new/reuse counts differ from independently validated module origins")
    evidence.verify_frozen()
    unchanged(inputs)
    need(A.snapshot(root, root / PRIVATE / "lib", base, toolchain) == old_snapshot, "Local accepted closure changed during validation")
    archive_relative = PRIVATE + f"/ci-imports/{args.run_id}-{attempt}-{args.index_sha256[:12]}"
    for name in install_files:
        no_destination(root, name)
    for module in new_targets:
        no_destination(root, PRIVATE + "/audit/" + module)
        for suffix in FACETS:
            no_destination(root, PRIVATE + "/lib/" + module.replace(".", "/") + suffix)
    no_destination(root, archive_relative)
    merged = dict(old_records, **new_records)
    merged_raw = E.encoded(merged)
    for name in expected_files:
        exclusive_link_or_copy(incoming / name, archive / name, inputs[incoming / name])
    (archive / "local-records-before.json").write_bytes(old_raw)
    (archive / "import-receipt.json").write_bytes(E.encoded({
        "run_id": args.run_id, "commit": args.commit, "index_sha256": args.index_sha256,
        "bootstrap_sha256": index["bootstrap_sha256"], "modules": sorted(new_targets),
        "new_pages": 562, "new_rows": 8978, "terminal_integrated": False,
        "records_before_sha256": inputs[records_path], "records_after_sha256": hashlib.sha256(merged_raw).hexdigest(),
        "installed_files": install_files, "verification": "Original snapshot/compilation and receipt validators; no compile or replay"}))
    return {"stage": stage, "archive": archive, "archive_relative": archive_relative,
            "archive_files": {str(path.relative_to(archive)): C.digest(path)
                              for path in archive.rglob("*") if path.is_file()},
            "files": install_files, "inputs": inputs, "records_path": records_path,
            "merged_raw": merged_raw, "old_snapshot": old_snapshot, "base": base, "toolchain": toolchain}


def install(root: Path, verified: dict) -> None:
    unchanged(verified["inputs"])
    installed, archive_created, committed, pending = [], False, False, None
    archive = root / verified["archive_relative"]
    try:
        for name, digest in verified["files"].items():
            no_destination(root, name)
            destination = root / name
            exclusive_link_or_copy(verified["stage"] / name, destination, digest)
            installed.append(destination)
        no_destination(root, verified["archive_relative"])
        archive.parent.mkdir(parents=True, exist_ok=True)
        archive.mkdir()
        archive_created = True
        for name, digest in verified["archive_files"].items():
            no_destination(archive, name)
            exclusive_link_or_copy(verified["archive"] / name, archive / name, digest)
        unchanged(verified["inputs"])
        need(A.snapshot(root, root / PRIVATE / "lib", verified["base"], verified["toolchain"])
             == verified["old_snapshot"], "Accepted dependencies changed before registry commit")
        with tempfile.NamedTemporaryFile(prefix=".records-ci-import-", dir=verified["records_path"].parent, delete=False) as stream:
            pending = Path(stream.name)
            stream.write(verified["merged_raw"])
            stream.flush()
            os.fsync(stream.fileno())
        need(C.digest(verified["records_path"]) == verified["inputs"][verified["records_path"]],
             "Another process changed the registry; stop concurrent cache writers")
        os.replace(pending, verified["records_path"])
        committed = True
    finally:
        if not committed:
            for path in reversed(installed):
                path.unlink(missing_ok=True)
                for directory in path.parents:
                    if directory == root / PRIVATE:
                        break
                    try:
                        directory.rmdir()
                    except OSError:
                        break
            if archive_created:
                shutil.rmtree(archive, ignore_errors=True)
        if pending is not None:
            pending.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("collection", type=Path, help="Expanded collect artifact: index.json, bootstrap.tar.gz, block-XX.zip")
    parser.add_argument("--run-id", required=True, help="Workflow run ID observed at the trusted download")
    parser.add_argument("--commit", required=True, help="Full CI source commit observed at the trusted download")
    parser.add_argument("--index-sha256", required=True, help="SHA256 of index.json anchored at the trusted download")
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--staging-parent", type=Path, help="Optional temporary extraction location with sufficient disk space")
    args = parser.parse_args()
    need(re.fullmatch(r"[1-9][0-9]*", args.run_id) is not None
         and re.fullmatch(r"[0-9a-f]{40}", args.commit) is not None
         and re.fullmatch(r"[0-9a-f]{64}", args.index_sha256) is not None, "Invalid trusted provenance arguments")
    root, incoming = Path.cwd().resolve(), args.collection.resolve()
    with tempfile.TemporaryDirectory(prefix="p210-ci-import-", dir=args.staging_parent) as temporary:
        verified = validate(root, incoming, Path(temporary), args)
        if args.check_only:
            print("CHECK_ONLY_PASSED: 598 new modules / 562 pages / 8978 rows; local cache unchanged")
        else:
            install(root, verified)
            print("IMPORTED: 598 new modules / 562 pages / 8978 rows; original receipts preserved")
            print("PROVENANCE", root / verified["archive_relative"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
