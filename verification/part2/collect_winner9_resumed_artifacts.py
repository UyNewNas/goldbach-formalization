#!/usr/bin/env python3
"""Collect complete resumed blocks while retaining their original public inputs.

This script transports receipts. The original C/A/E gates and the receiver's
source/object/receipt checks remain the proof acceptance boundary.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import zipfile

import import_winner9_ci_artifacts as I
import export_winner9_private_evidence as E

REPO = "UyNewNas/goldbach-formalization"
ROOT = Path.cwd().resolve()
WORK = ROOT / ".lake/p210-collect"
OUT = WORK / "collection"
need = I.need


def sha(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def api(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint]))


def download(item, destination):
    with destination.open("xb") as stream:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{item['id']}/zip"],
                       stdout=stream, check=True)
    need(destination.stat().st_size == item["size_in_bytes"]
         and item["digest"] == "sha256:" + sha(destination), "Changed artifact transport")


def main():
    need(os.environ["GITHUB_REPOSITORY"] == REPO, "Unexpected collection repository")
    run, attempt, commit = os.environ["GITHUB_RUN_ID"], int(os.environ["GITHUB_RUN_ATTEMPT"]), os.environ["GITHUB_SHA"]
    need(subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == commit,
         "Collection checkout differs from its producer")
    plan_path = ROOT / I.RESUME_PLAN
    plan = I.read(plan_path)
    need(plan["bootstrap"] == I.FIXED_BOOTSTRAP and plan["importer_sha256"] == sha(I.__file__),
         "Collection plan or importer changed")
    WORK.mkdir(parents=True, exist_ok=False)
    OUT.mkdir()
    boot = plan["bootstrap"]
    meta = api(f"repos/{REPO}/actions/artifacts/{boot['artifact_id']}")
    need(meta["id"] == boot["artifact_id"] and meta["name"] == boot["artifact_name"] and not meta["expired"]
         and meta["size_in_bytes"] == boot["zip_bytes"] and meta["digest"] == "sha256:" + boot["zip_sha256"]
         and str(meta["workflow_run"]["id"]) == boot["run_id"]
         and meta["workflow_run"]["head_sha"] == boot["commit"], "Foreign bootstrap artifact")
    original = WORK / "bootstrap.zip"
    download(meta, original)
    inventory = I.unpack_zip(original, WORK / "bootstrap")
    need(inventory == {"bootstrap.tar.gz": boot["tar_sha256"]}, "Bootstrap archive inventory changed")
    I.exclusive_link_or_copy(WORK / "bootstrap/bootstrap.tar.gz", OUT / "bootstrap.tar.gz", boot["tar_sha256"])
    artifacts, page = [], 1
    while True:
        values = api(f"repos/{REPO}/actions/runs/{run}/artifacts?per_page=100&page={page}")["artifacts"]
        artifacts.extend(values)
        if len(values) < 100:
            break
        page += 1
    blocks, modules, new_compiles, reused_compiles, reused_audits, reused_replays = {}, set(), 0, 0, 0, 0
    for block in range(8, 44):
        key, wanted = f"{block:02}", I.targets(block)
        pattern = re.compile(rf"p210-block-{key}-{re.escape(run)}-([1-9][0-9]*)")
        matches = [(int(match[1]), item) for item in artifacts if not item["expired"]
                   and (match := pattern.fullmatch(item["name"])) and int(match[1]) <= attempt]
        need(matches, "Missing complete block artifact: " + key)
        selected_attempt, item = max(matches, key=lambda pair: pair[0])
        need(sum(number == selected_attempt for number, _ in matches) == 1, "Ambiguous complete block producer")
        need(str(item["workflow_run"]["id"]) == run and item["workflow_run"]["head_sha"] == commit,
             "Foreign completed block producer")
        target = OUT / f"block-{key}.zip"
        download(item, target)
        with zipfile.ZipFile(target) as archive:
            need(len(archive.namelist()) == len(set(archive.namelist())), "Duplicate block ZIP member")
            info = json.loads(archive.read("provenance.json"))
            manifest = json.loads(archive.read("evidence/manifest.json"))
            need(info["schema"] == 2 and info["block"] == key and info["modules"] == wanted
                 and info["commit"] == commit and info["run_id"] == run
                 and int(info["run_attempt"]) == selected_attempt and info["gates"] == I.GATES
                 and info["bootstrap_origin"] == boot and info["bootstrap_sha256"] == boot["tar_sha256"]
                 and info["plan_sha256"] == sha(plan_path), "Incomplete or foreign resumed block")
            I.export_gate(manifest, wanted)
            need(set(info["module_origins"]) == set(wanted), "Unexpected or missing module origin for collection counts")
            need(set(archive.namelist()) == set(info["delivery_files"]) | {"provenance.json"},
                 "Unexpected delivery ZIP inventory")
            for name, digest in info["delivery_files"].items():
                value = hashlib.sha256()
                with archive.open(name) as stream:
                    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                        value.update(chunk)
                need(value.hexdigest() == digest, "Changed original delivery member: " + name)
        need(not modules.intersection(wanted), "Overlapping complete block modules")
        modules.update(wanted)
        for origin in info["module_origins"].values():
            if origin["compile"]["reused"]:
                reused_compiles += 1
            else:
                new_compiles += 1
            if origin["audit"]["artifact_id"] is not None:
                reused_audits += 1
            elif origin["audit"]["reuse"] == "replay":
                reused_replays += 1
        blocks[key] = {"artifact_id": item["id"], "artifact_name": item["name"],
                       "zip_bytes": item["size_in_bytes"], "zip_sha256": sha(target), "provenance": info}
        print("COLLECTED", key, len(wanted), "original accepted modules", flush=True)
    need(len(modules) == 598 and new_compiles + reused_compiles == 598, "Incomplete numerical collection")
    index = {"schema": 2, "commit": commit, "run_id": run, "run_attempt": str(attempt),
             "bootstrap_producer_attempt": boot["run_attempt"], "bootstrap_origin": boot,
             "bootstrap_sha256": boot["tar_sha256"], "plan_sha256": sha(plan_path), "blocks": blocks,
             "new_pages": 562, "new_rows": 8978, "old_rows_replayed": 0, "terminal_integrated": False,
             "new_strict_compilations_in_run": new_compiles, "reused_strict_compilations": reused_compiles,
             "reused_accepted_audits": reused_audits,
             "reused_stock_replays_for_new_audits": reused_replays,
             "scope": "Pages 128..689 and Checks 08..43 relative to the accepted 2048-row prefix; reused proofs are not new work."}
    (OUT / "index.json").write_bytes(E.encoded(index))
    print("COLLECTION_INDEX_SHA256", sha(OUT / "index.json"), flush=True)


if __name__ == "__main__":
    main()
