#!/usr/bin/env python3
"""Transport the fixed completed collection, omitting an already received bootstrap.

Only public bytes are downloaded, hashed and copied. This script never imports
the proof drivers, invokes Lean, changes receipts or assigns new proof credit.
The receiver must still run the unchanged original importer on all 38 inputs.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import zipfile


SOURCE = {
    "repository": "UyNewNas/goldbach-formalization",
    "commit": "94c7c507ab747cf4e05a4f19d8d4507cedfede38",
    "run_id": "45611402948",
    "run_attempt": 1,
    "artifact_id": 15041690180,
    "artifact_name": "p210-collection-45611402948-1",
    "zip_bytes": 635602594,
    "zip_sha256": "1965d3a92c336a4b1931835275e2602d14bef41bfd7cebcaeea3fa098ca597df",
    "index_sha256": "687c35f8ef018ad85e7cc68581dcadd98cd0acd22bd22f031dfd95966abfc70e",
}
BOOTSTRAP_SHA256 = "e17d879ab60ad21874b8b26ce20075a1b646af82ee18cf00749773ba5dc37370"
PLAN_SHA256 = "46e739a5a5ddfa3ad6b0dd4697f1bf95bb9cbb21ef84ce1c7f32e2cb33162978"
IMPORTER_SHA256 = "b90f11e049080eff0ccc2d09e63f2d78ce88825791b5c4efdf6a92dc78be188c"
BRANCH = "refs/heads/codex-p210-complete-20261125"
BLOCKS = tuple(f"{number:02}" for number in range(8, 44))
DELIVERED = ("index.json", *(f"block-{block}.zip" for block in BLOCKS))
CHUNK_BYTES = 1024 * 1024


def require(condition, message):
    if not condition:
        raise ValueError(message)


def stream_fingerprint(stream, destination=None):
    digest, count = hashlib.sha256(), 0
    for chunk in iter(lambda: stream.read(CHUNK_BYTES), b""):
        digest.update(chunk)
        count += len(chunk)
        if destination is not None:
            destination.write(chunk)
    return {"sha256": digest.hexdigest(), "bytes": count}


def fingerprint(path):
    with Path(path).open("rb") as stream:
        return stream_fingerprint(stream)


def verify_source_metadata(metadata, run, source):
    require(metadata["id"] == source["artifact_id"]
            and metadata["name"] == source["artifact_name"]
            and metadata["expired"] is False
            and metadata["size_in_bytes"] == source["zip_bytes"]
            and metadata["digest"] == "sha256:" + source["zip_sha256"]
            and str(metadata["workflow_run"]["id"]) == source["run_id"]
            and metadata["workflow_run"]["head_sha"] == source["commit"],
            "Source artifact metadata differs from the fixed public collection")
    require(str(run["id"]) == source["run_id"] and run["head_sha"] == source["commit"]
            and run["run_attempt"] == source["run_attempt"]
            and run["repository"]["full_name"] == source["repository"]
            and run["status"] == "completed" and run["conclusion"] == "success",
            "Source proof run is foreign, changed or not successfully completed")


def build_delivery(archive_path, output, source, transport, plan, plan_sha256):
    """Validate the whole source before creating a byte-preserving delivery.

    The CLI always supplies the immutable anchors above. Explicit bindings keep
    this data-only operation testable using small archives without a network.
    """
    archive_path, output = Path(archive_path), Path(output)
    require(not os.path.lexists(output), "Delivery output already exists")
    require(archive_path.is_file() and not archive_path.is_symlink(), "Source ZIP must be a regular file")
    require(fingerprint(archive_path) == {"sha256": source["zip_sha256"], "bytes": source["zip_bytes"]},
            "Complete source ZIP size or SHA256 mismatch")
    with zipfile.ZipFile(archive_path) as archive:
        members = archive.infolist()
        names = [item.filename for item in members]
        require(len(names) == 38 and len(names) == len(set(names))
                and set(names) == set(DELIVERED) | {"bootstrap.tar.gz"},
                "Source ZIP member inventory must be exactly the 38 original flat files")
        for item in members:
            require(item.filename == item.orig_filename and not item.is_dir()
                    and stat.S_IFMT(item.external_attr >> 16) in (0, stat.S_IFREG)
                    and not (item.external_attr & 0x10) and not (item.flag_bits & 1),
                    "Unsafe, nonregular or encrypted ZIP member: " + item.filename)
        require(archive.getinfo("index.json").file_size <= 16 * CHUNK_BYTES, "Unexpectedly large source index")
        index_bytes = archive.read("index.json")
        require(hashlib.sha256(index_bytes).hexdigest() == source["index_sha256"],
                "Original index SHA256 mismatch")
        index = json.loads(index_bytes)
        require(index["schema"] == 2 and index["commit"] == source["commit"]
                and index["run_id"] == source["run_id"]
                and index["run_attempt"] == str(source["run_attempt"])
                and index["plan_sha256"] == plan_sha256
                and set(index["blocks"]) == set(BLOCKS)
                and index["new_pages"] == 562 and index["new_rows"] == 8978
                and index["old_rows_replayed"] == 0 and index["terminal_integrated"] is False,
                "Original index producer, plan, blocks or scope mismatch")
        require(index["bootstrap_origin"] == plan["bootstrap"]
                and index["bootstrap_producer_attempt"] == plan["bootstrap"]["run_attempt"]
                and index["bootstrap_sha256"] == plan["bootstrap"]["tar_sha256"],
                "Original bootstrap origin differs from the pinned plan")
        files = {"index.json": {"sha256": source["index_sha256"], "bytes": len(index_bytes)}}
        # Even the omitted bootstrap is fully decompressed and hashed; no
        # extraction or delivery of those already held bytes is necessary.
        with archive.open("bootstrap.tar.gz") as stream:
            bootstrap = stream_fingerprint(stream)
        require(bootstrap["sha256"] == index["bootstrap_sha256"]
                and bootstrap["bytes"] == archive.getinfo("bootstrap.tar.gz").file_size,
                "Omitted bootstrap bytes or SHA256 mismatch")
        for block in BLOCKS:
            name, binding = f"block-{block}.zip", index["blocks"][block]
            require(type(binding["zip_bytes"]) is int and binding["zip_bytes"] > 0
                    and archive.getinfo(name).file_size == binding["zip_bytes"],
                    "Original block size mismatch: " + name)
            with archive.open(name) as stream:
                actual = stream_fingerprint(stream)
            require(actual == {"sha256": binding["zip_sha256"], "bytes": binding["zip_bytes"]},
                    "Original block bytes or SHA256 mismatch: " + name)
            files[name] = actual
        tail = {
            "schema": "p210-public-collection-tail-v1",
            "source": dict(source), "transport": dict(transport),
            "bootstrap": {"filename": "bootstrap.tar.gz", **bootstrap},
            "files": files,
            "scope": {"modules": 598, "pages": 562, "rows": 8978, "terminal_integrated": False},
            "proof_compilation": 0, "stock_replay": 0,
        }
        # No delivery directory exists until every original member has passed.
        # Rehash during the copy as well. A later I/O failure leaves diagnostics
        # in this exclusive workspace and fails the upload step closed.
        output.mkdir()
        for name in DELIVERED:
            with archive.open(name) as stream, (output / name).open("xb") as destination:
                copied = stream_fingerprint(stream, destination)
            require(copied == files[name], "Original bytes changed during delivery: " + name)
        with (output / "tail.json").open("x", encoding="utf-8") as stream:
            json.dump(tail, stream, sort_keys=True, indent=2)
            stream.write("\n")
    return tail


def api(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint]))


def main():
    require(os.environ["GITHUB_REPOSITORY"] == SOURCE["repository"]
            and os.environ["GITHUB_REF"] == BRANCH, "Unexpected transport repository or branch")
    commit, run = os.environ["GITHUB_SHA"], os.environ["GITHUB_RUN_ID"]
    attempt = os.environ["GITHUB_RUN_ATTEMPT"]
    require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None
            and re.fullmatch(r"[1-9][0-9]*", run) is not None
            and re.fullmatch(r"[1-9][0-9]*", attempt) is not None
            and commit != SOURCE["commit"] and run != SOURCE["run_id"],
            "Transport must have its own actual producer identity")
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == commit,
            "Transport checkout differs from its producer")
    root = Path.cwd().resolve()
    plan_path = root / "verification/part2/p210_resume_plan.json"
    importer_path = root / "verification/part2/import_winner9_ci_artifacts.py"
    require(fingerprint(plan_path)["sha256"] == PLAN_SHA256
            and fingerprint(importer_path)["sha256"] == IMPORTER_SHA256,
            "Original resume plan or importer changed")
    plan = json.loads(plan_path.read_bytes())
    require(plan["importer_sha256"] == IMPORTER_SHA256
            and plan["bootstrap"]["tar_sha256"] == BOOTSTRAP_SHA256,
            "Original plan has an unexpected importer or bootstrap")
    endpoint = "repos/" + SOURCE["repository"] + "/actions/"
    metadata = api(endpoint + "artifacts/" + str(SOURCE["artifact_id"]))
    source_run = api(endpoint + "runs/" + SOURCE["run_id"])
    verify_source_metadata(metadata, source_run, SOURCE)
    work = root / ".lake/p210-public-transport"
    work.mkdir(parents=True, exist_ok=False)
    # Keep the full original ZIP locally in this job, outside the upload path.
    original = work / "source-collection.zip"
    with original.open("xb") as stream:
        subprocess.run(["gh", "api", endpoint + "artifacts/" + str(SOURCE["artifact_id"]) + "/zip"],
                       stdout=stream, check=True)
    tail = build_delivery(original, work / "delivery", SOURCE,
                          {"commit": commit, "run_id": run, "run_attempt": int(attempt)}, plan, PLAN_SHA256)
    print(json.dumps({"status": "PUBLIC_TRANSPORT_VERIFIED", "original_files": len(tail["files"]),
                      "delivered_bytes": sum(item["bytes"] for item in tail["files"].values()),
                      "omitted_bootstrap_bytes": tail["bootstrap"]["bytes"],
                      "proof_compilation": 0, "stock_replay": 0}, sort_keys=True))


if __name__ == "__main__":
    main()
