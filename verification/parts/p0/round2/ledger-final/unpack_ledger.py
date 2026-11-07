#!/usr/bin/env python3
"""Restore and verify this ledger package using the Python standard library."""
import argparse
import base64
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda: f.read(1024 * 1024), b""):
            h.update(b)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--destination", type=Path, default=Path.cwd())
    args = ap.parse_args()
    package = Path(__file__).resolve().parent
    manifest_file = package / "package-manifest.json"
    expected_manifest = (package / "package-manifest.json.sha256").read_text(encoding="utf-8").split()[0]
    if digest(manifest_file) != expected_manifest:
        raise ValueError("package manifest SHA256 mismatch")
    manifest = json.loads(manifest_file.read_text(encoding="utf-8"))
    if manifest["schema"] != "chen-ledger-package-v1":
        raise ValueError("unsupported package schema")
    archive = manifest["archive"]
    encoded = package / archive["base64_file"]
    if encoded.name != archive["base64_file"] or digest(encoded) != archive["base64_sha256"]:
        raise ValueError("base64 archive filename/hash mismatch")
    root_name = archive["root"]
    if PurePosixPath(root_name).parts != (root_name,) or root_name in (".", ".."):
        raise ValueError("invalid archive root")
    target = args.destination.resolve()
    target.mkdir(parents=True, exist_ok=True)
    final = target / root_name
    if final.exists() or final.is_symlink():
        raise FileExistsError("refusing to overwrite " + str(final))
    files = {entry["path"]: entry for entry in manifest["input_inventory"]["files"]}
    directories = set(manifest["input_inventory"]["directories"])
    with tempfile.TemporaryDirectory(prefix="ledger-restore-", dir=target) as temporary:
        temporary = Path(temporary)
        compressed = temporary / "input.tar.gz"
        with encoded.open("rb") as source, compressed.open("wb") as output:
            base64.decode(source, output)
        if (compressed.stat().st_size != archive["gzip_bytes"]
                or digest(compressed) != archive["gzip_sha256"]):
            raise ValueError("decoded gzip archive size/hash mismatch")
        restored = temporary / root_name
        restored.mkdir()
        seen_files, seen_dirs = set(), set()
        seen_members = set()
        with tarfile.open(compressed, "r:gz") as tar:
            for member in tar:
                path = PurePosixPath(member.name)
                if (path.is_absolute() or ".." in path.parts or "\\" in member.name
                        or not path.parts or path.parts[0] != root_name
                        or member.name in seen_members):
                    raise ValueError("unsafe/duplicate archive member " + member.name)
                seen_members.add(member.name)
                rel = PurePosixPath(*path.parts[1:]).as_posix()
                if len(path.parts) == 1:
                    if not member.isdir():
                        raise ValueError("archive root is not a directory")
                    continue
                destination = restored.joinpath(*path.parts[1:])
                if member.isdir():
                    if rel not in directories:
                        raise ValueError("unexpected directory " + rel)
                    destination.mkdir(parents=True, exist_ok=True)
                    seen_dirs.add(rel)
                elif member.isfile() and rel in files:
                    expected = files[rel]
                    if member.size != expected["bytes"]:
                        raise ValueError("member size mismatch " + rel)
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    with tar.extractfile(member) as source, destination.open("xb") as output:
                        shutil.copyfileobj(source, output, 1024 * 1024)
                    if digest(destination) != expected["sha256"]:
                        raise ValueError("restored file SHA256 mismatch " + rel)
                    destination.chmod(expected["mode"])
                    seen_files.add(rel)
                else:
                    raise ValueError("unexpected/nonregular archive member " + member.name)
        if seen_files != set(files) or seen_dirs != directories:
            raise ValueError("archive inventory is incomplete")
        if final.exists() or final.is_symlink():
            raise FileExistsError("destination appeared during restoration")
        restored.rename(final)
    print(json.dumps({"restored": str(final), "verified_files": len(files),
                      "gzip_sha256": archive["gzip_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
