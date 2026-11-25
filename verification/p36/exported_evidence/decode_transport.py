#!/usr/bin/env python3
"""Reconstruct pinned evidence payloads from captured byte-offset stdout pages."""
from pathlib import Path
import argparse, base64, hashlib, json

def require(ok, why):
    if not ok:
        raise RuntimeError(why)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def preserve(path, data):
    if path.exists():
        require(path.read_bytes() == data, "Existing bytes differ: " + str(path))
    else:
        path.write_bytes(data)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--profile", type=Path, required=True)
    args = ap.parse_args()
    profile = json.loads(args.profile.read_bytes())
    root = args.profile.resolve().parent
    terminals = json.loads((root / "EXPORT_TERMINALS.json").read_bytes())
    require([(t["kind"], t["index"], t["task_id"]) for t in terminals] ==
            [(t["kind"], t["index"], t["task_id"]) for t in profile["exports"]],
            "Export task identity/order differs from the independently pinned profile")
    pagesize = profile["page_bytes"]
    checked, chunks = [], []
    for terminal in terminals:
        kind, index = terminal["kind"], terminal["index"]
        require(terminal["status"] == "succeeded" and terminal["exit_code"] == 0
                and terminal["output_truncated"] is False, "Export did not finish intact")
        stem = "receipt" if kind == "receipt" else "archive-" + str(index)
        output = bytearray()
        offsets = list(range(0, terminal["output_bytes"], pagesize))
        expected_names = {stem + "-page-" + str(n).zfill(7) + ".b64" for n in offsets}
        require({p.name for p in root.glob(stem + "-page-*.b64")} == expected_names,
                "Missing, duplicate, or extra transport page")
        for offset in offsets:
            encoded = "".join((root / (stem + "-page-" + str(offset).zfill(7) + ".b64")).read_text().split())
            page = base64.b64decode(encoded, validate=True)
            require(len(page) == min(pagesize, terminal["output_bytes"] - offset),
                    "Page byte length differs")
            require(len(output) == offset, "Non-contiguous page offset")
            output.extend(page)
        stdout = bytes(output)
        require(len(stdout) == terminal["output_bytes"], "Stdout byte count differs")
        lines = stdout.splitlines()
        require(len(lines) == 4 and lines[0].startswith(b"P36_EXPORT_META ")
                and lines[1] == b"P36_EXPORT_BASE64_BEGIN"
                and lines[3] == b"P36_EXPORT_BASE64_END", "Unexpected export stdout envelope")
        meta = json.loads(lines[0][len(b"P36_EXPORT_META "):])
        payload = base64.b64decode(lines[2], validate=True)
        require(base64.b64encode(payload) == lines[2], "Non-canonical payload base64")
        require(meta["kind"] == kind and meta["index"] == index
                and meta["bytes"] == len(payload) and meta["sha256"] == digest(payload),
                "Export payload metadata differs")
        if kind == "receipt":
            require(index == -1 and meta["offset"] == 0 and meta["total_bytes"] == len(payload)
                    and digest(payload) == profile["receipt_sha256"], "Receipt pin differs")
            preserve(root / "RECEIPT.json", payload)
        else:
            require(index == len(chunks)
                    and meta["offset"] == sum(len(p) for p in chunks)
                    and meta["total_bytes"] == profile["archive_bytes"], "Archive part offset/total differs")
            chunks.append(payload)
            preserve(root / ("archive-part-" + str(index) + ".bin"), payload)
        preserve(root / (stem + ".stdout"), stdout)
        checked.append({"task_id": terminal["task_id"], "status": terminal["status"],
                        "exit_code": terminal["exit_code"], "output_truncated": terminal["output_truncated"],
                        "stdout_bytes": len(stdout), "stdout_sha256": digest(stdout),
                        "page_count": len(offsets), "payload": meta})
    archive = b"".join(chunks)
    require(len(archive) == profile["archive_bytes"]
            and digest(archive) == profile["archive_sha256"], "Combined archive pin differs")
    preserve(root / "evidence.tar.xz", archive)
    result = {"status": "PASS", "transport_page_bytes": pagesize, "exports": checked,
              "archive_bytes": len(archive), "archive_sha256": digest(archive),
              "receipt_sha256": profile["receipt_sha256"]}
    (root / "TRANSPORT_VERIFICATION.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "archive_bytes": len(archive),
                      "archive_sha256": digest(archive), "export_count": len(checked),
                      "total_pages": sum(x["page_count"] for x in checked)}))

if __name__ == "__main__":
    main()

