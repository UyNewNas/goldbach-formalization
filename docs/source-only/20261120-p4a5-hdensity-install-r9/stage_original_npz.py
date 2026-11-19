#!/usr/bin/env python3
"""Stage exact G3 members from individually hashed original NPZs, not G3_INPUTS.zip."""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = ROOT / 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G3_FIXTURES.json'
MANIFEST_SHA = 'f79c794c614af8b4aec78ca4601f9b6e6d58f3e47d72b72eac98f94003cca184'
DATA_SHA = '5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4'
PREFIX = 'chen-numerical-evidence-20261010-renewal-v2/'
CHUNK = 1024 * 1024


def digest_file(path):
    h = hashlib.sha256()
    with path.open('rb') as src:
        for chunk in iter(lambda: src.read(CHUNK), b''):
            h.update(chunk)
    return h.hexdigest()


def member_digest(stream, out=None):
    h = hashlib.sha256()
    size = 0
    for chunk in iter(lambda: stream.read(CHUNK), b''):
        h.update(chunk)
        size += len(chunk)
        if out is not None:
            out.write(chunk)
    return h.hexdigest(), size


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--outer-zip', type=Path, required=True)
    parser.add_argument('--stage', type=Path, required=True)
    args = parser.parse_args()
    assert digest_file(MANIFEST) == MANIFEST_SHA, 'fixture manifest mismatch'
    stage = args.stage.resolve(strict=True)
    parent = stage / 'ImbalancedChen'
    assert digest_file(parent / 'P4AOriginalNewFifthArchiveData.lean') == DATA_SHA, 'Data source mismatch'
    fixture_dir = parent / 'g3-fixtures'
    assert not fixture_dir.is_symlink(), 'fixture directory is a symlink'
    assert fixture_dir.resolve().is_relative_to(parent.resolve()), 'fixture directory escapes stage'
    blocks = json.loads(MANIFEST.read_text())['blocks']
    assert len(blocks) == 94
    names, originals = set(), set()
    for b in blocks:
        name = b['input_original']
        assert re.fullmatch(r'goldbach-research/fifth-prefix-new-coverage-(?:refinement-)?blocks/block-\d{4}\.npz', name)
        assert name not in originals
        originals.add(name)
        assert len(b['members']) == 2
        assert {m['source_member'] for m in b['members']} == {'cells.npy', 'floors.npy'}
        for m in b['members']:
            p = PurePosixPath(m['staged'])
            assert len(p.parts) == 2 and p.parts[0] == 'g3-fixtures'
            assert re.fullmatch(r'[CF]\d{4}-(?:cells|floors)\.npy', p.name)
            assert p.name not in names
            names.add(p.name)
            destination = fixture_dir / p.name
            assert not destination.is_symlink(), 'fixture is a symlink'
            if destination.exists():
                assert destination.stat().st_size == m['bytes'] and digest_file(destination) == m['sha256'], 'different fixture exists'
    assert len(names) == 188
    hashes = []
    with zipfile.ZipFile(args.outer_zip) as outer:
        outer_names = [i.filename for i in outer.infolist()]
        for b in blocks:
            assert outer_names.count(PREFIX + b['input_original']) == 1, 'missing or duplicate original block'

        def read_block(b):
            data = outer.read(PREFIX + b['input_original'])
            assert hashlib.sha256(data).hexdigest() == b['original_npz_sha256'], 'original NPZ hash mismatch'
            return zipfile.ZipFile(io.BytesIO(data))

        # Verify every member before creating the output directory or writing data.
        for b in blocks:
            with read_block(b) as inner:
                member_names = [i.filename for i in inner.infolist()]
                for m in b['members']:
                    assert member_names.count(m['source_member']) == 1, 'missing or duplicate NPZ member'
                    with inner.open(m['source_member']) as src:
                        h, size = member_digest(src)
                    assert h == m['sha256'] and size == m['bytes'], 'member mismatch'
            hashes.append({'path': b['input_original'], 'sha256': b['original_npz_sha256']})
        fixture_dir.mkdir(exist_ok=True)
        for b in blocks:
            with read_block(b) as inner:
                for m in b['members']:
                    destination = fixture_dir / PurePosixPath(m['staged']).name
                    if destination.exists():
                        continue
                    fd, tmp = tempfile.mkstemp(prefix='.g3-', dir=fixture_dir)
                    try:
                        with os.fdopen(fd, 'wb') as out, inner.open(m['source_member']) as src:
                            h, size = member_digest(src, out)
                        assert h == m['sha256'] and size == m['bytes'], 'member changed during staging'
                        os.replace(tmp, destination)
                    finally:
                        if os.path.exists(tmp):
                            os.unlink(tmp)
    receipt = {'scope': 'selected original blocks and members only; no numerical certificate evaluation',
               'release': 'https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/tag/v2026.10.10',
               'manifest_sha256': MANIFEST_SHA, 'data_source_sha256': DATA_SHA,
               'full_release_archive_hash_verified': False, 'g3_inputs_zip_hash_verified': False,
               'npz_count': len(hashes), 'member_count': len(names),
               'member_bytes': sum(m['bytes'] for b in blocks for m in b['members']),
               'members_postwrite_hash_checked': True, 'certificates_evaluated': False,
               'original_npz_sha256': hashes}
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
