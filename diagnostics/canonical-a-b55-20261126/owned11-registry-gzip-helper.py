def write_registry_snapshot(name, raw):
    # Only wrapper-owned complete registry copies are compressed; the canonical
    # registry and every original runner artifact remain at their original paths.
    assert name in {"registry-before-audit.json", "registry-after-audit.json"}
    path = out / (name + ".gz")
    index_path = out / (name + ".gz.index.json")
    assert not path.exists() and not index_path.exists(), "Preserve earlier compressed evidence"
    compressed = gzip.compress(raw, compresslevel=9, mtime=0)
    raw_sha256 = hashlib.sha256(raw).hexdigest()
    index = {
        "canonical_registry": str(registry),
        "uncompressed_bytes": len(raw), "uncompressed_sha256": raw_sha256,
        "gzip": {"path": str(path), "bytes": len(compressed),
                 "sha256": hashlib.sha256(compressed).hexdigest()},
        "lossless_decompressed_bytes_equal": True,
        "lossless_decompressed_sha256": raw_sha256,
        "loose_registry_copy_written": False,
    }
    index_raw = (json.dumps(index, ensure_ascii=False, indent=2) + "\n").encode()
    disk = os.statvfs(out)
    block = disk.f_frsize
    reserve = 32 * 1024 * 1024
    allocation = (((len(compressed) + block - 1) // block
                   + (len(index_raw) + block - 1) // block + 1) * block)
    assert disk.f_bavail * block >= allocation + reserve, \
        "Compressed registry and index would breach the original 32 MiB reserve"
    with path.open("xb") as stream:
        stream.write(compressed)
    restored = gzip.decompress(path.read_bytes())
    assert restored == raw, "Compressed registry did not preserve the complete original bytes"
    assert len(restored) == len(raw) and hashlib.sha256(restored).hexdigest() == raw_sha256
    assert file_info(path) == index["gzip"]
    with index_path.open("xb") as stream:
        stream.write(index_raw)
    disk_after = os.statvfs(out)
    assert disk_after.f_bavail * disk_after.f_frsize >= reserve
    return index
