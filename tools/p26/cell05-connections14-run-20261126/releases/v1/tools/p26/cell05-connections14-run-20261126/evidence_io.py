#!/usr/bin/env python3
"""Regular-file evidence archives and an explicit, read-only historical path view."""
from pathlib import Path, PurePosixPath
import hashlib
import io
import json
import os
import stat
import tarfile


def require(value, message):
    if not value:
        raise RuntimeError(message)


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def same(a, b):
    return isinstance(a, dict) and isinstance(b, dict) and all(a.get(k) == b.get(k) for k in ('bytes', 'sha256'))


def canonical(path, must_exist=False):
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts, f'Noncanonical physical path: {path}')
    for part in [*reversed(path.parents), path]:
        try:
            mode = part.lstat().st_mode
        except FileNotFoundError:
            continue
        require(not stat.S_ISLNK(mode), f'Symlink in physical path: {part}')
        if part != path:
            require(stat.S_ISDIR(mode), f'Non-directory ancestor: {part}')
    require(not must_exist or path.exists(), f'Missing physical path: {path}')
    return path


def fp(path):
    path = canonical(path, True)
    require(stat.S_ISREG(path.lstat().st_mode), f'Nonregular physical evidence file: {path}')
    return {'path': str(path), **pin(path.read_bytes())}


def read(path):
    return json.loads(canonical(path, True).read_text())


def dump_new(path, value):
    path = canonical(path)
    require(not path.exists(), f'Refuse to overwrite evidence: {path}')
    path.parent.mkdir(parents=True, exist_ok=True)
    canonical(path.parent, True)
    with path.open('x') as out:
        out.write(json.dumps(value, indent=2) + '\n')


def absolute(name):
    path = PurePosixPath(name)
    require(path.is_absolute() and '..' not in path.parts and str(path) == str(name),
            f'Invalid historical absolute path: {name}')
    return path


def member_name(name):
    path = PurePosixPath(name)
    require(name and not path.is_absolute() and '..' not in path.parts and str(path) == name,
            f'Unsafe archive member name: {name}')
    return path


def archive_bytes(path, expected_pin=None):
    """Read a tar snapshot without extracting paths or honoring inode links."""
    path = canonical(path, True)
    before = fp(path)
    if expected_pin is not None:
        require(same(before, expected_pin), 'Archive SHA/size does not match the independently pinned artifact')
    files = {}
    with tarfile.open(path, 'r:xz') as archive:
        for item in archive:
            member_name(item.name)
            require(item.isfile() and not item.issym() and not item.islnk(), 'Nonregular archive member')
            require(item.name not in files, 'Duplicate archive member')
            files[item.name] = archive.extractfile(item).read()
            require(len(files[item.name]) == item.size, 'Truncated archive member')
    require(fp(path) == before, 'Archive changed during readback')
    return files


def checked_export(path, archive_pin, manifest_pin):
    files = archive_bytes(path, archive_pin)
    require(same(pin(files['EXPORT_MANIFEST.json']), manifest_pin), 'Original export manifest pin mismatch')
    manifest = json.loads(files['EXPORT_MANIFEST.json'])
    expected = {row['member']: row for row in manifest['members']}
    require(len(expected) == len(manifest['members']), 'Duplicate declared export member')
    require(set(files) == set(expected) | {'EXPORT_MANIFEST.json'}, 'Export member coverage mismatch')
    for name, identity in expected.items():
        require(same(pin(files[name]), identity), f'Original export member changed: {name}')
    return files, manifest


def write_archive(path, files, manifest, manifest_name='CAPSULE_MANIFEST.json'):
    """Write only regular bytes, then reread every member before publishing."""
    path = canonical(path)
    partial = canonical(path.with_name(path.name + '.partial'))
    require(not path.exists() and not partial.exists(), 'Refuse existing archive/partial')
    require(manifest_name not in files, 'Reserved root manifest name')
    planned = {name: pin(data) for name, data in files.items()}
    require(manifest['members'] == [{'member': name, **planned[name]} for name in sorted(planned)],
            'Root manifest does not list the exact selected bytes')
    all_files = {**files, manifest_name: (json.dumps(manifest, indent=2) + '\n').encode()}
    for name in all_files:
        member_name(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    canonical(path.parent, True)
    with partial.open('xb') as stream:
        with tarfile.open(fileobj=stream, mode='w:xz', preset=6) as archive:
            for name, data in sorted(all_files.items()):
                info = tarfile.TarInfo(name)
                info.type, info.mode, info.mtime, info.size = tarfile.REGTYPE, 0o644, 0, len(data)
                archive.addfile(info, io.BytesIO(data))
    require(archive_bytes(partial) == all_files, 'Written archive regular-byte readback differs')
    canonical(path)
    os.link(partial, path)
    partial.unlink()
    return fp(path)


class EvidenceView:
    """No prefix rewriting or filesystem search: every old path has one exact key."""

    def __init__(self):
        self.values = {}
        self.origins = {}

    def add(self, old_path, data, origin):
        key = str(absolute(str(old_path)))
        require(isinstance(data, bytes), 'Historical evidence must remain raw bytes')
        if key in self.values:
            require(self.values[key] == data and self.origins[key] == origin, f'Conflicting exact-path mapping: {key}')
        else:
            self.values[key], self.origins[key] = data, origin

    def raw(self, old_path):
        key = str(absolute(str(old_path)))
        require(key in self.values, f'Unmapped historical path; no fallback is permitted: {key}')
        return self.values[key]

    def fp(self, old_path):
        return {'path': str(absolute(str(old_path))), **pin(self.raw(old_path))}

    def checked(self, identity, expected_path):
        expected_path = str(absolute(str(expected_path)))
        require(identity.get('path') == expected_path and identity == self.fp(expected_path),
                f'Historical path/byte fingerprint link mismatch: {expected_path}')
        return json.loads(self.raw(expected_path))

    def mappings(self):
        return [{'original': self.fp(name), 'resolved': self.origins[name]} for name in sorted(self.values)]
