#!/usr/bin/env python3
"""Package the completed P1.5 retention review using the Batch13 deterministic tar format."""
import argparse
import hashlib
import io
import json
import lzma
from pathlib import Path
import re
import tarfile

BASE = Path('/workspace')
PROOFS = BASE / 'p1-complete-proof'
ROOT = PROOFS / '20261125-p15-actual-means-v1'
PROJECT = BASE / 'blue-member-build'
REVIEW = ROOT / 'reviews/actual-means-final.json'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def binding(data):
    return {'bytes': len(data), 'sha256': sha(data)}


def fingerprint(path):
    assert path.is_file() and not path.is_symlink(), path
    return binding(path.read_bytes())


def inventory():
    entries = sorted(ROOT.rglob('*'))
    assert all(not p.is_symlink() and (p.is_file() or p.is_dir()) for p in entries)
    return {p for p in entries if p.is_file()}


def add_member(archive, name, payload):
    item = tarfile.TarInfo(name)
    item.size = len(payload)
    item.mtime = 0
    item.mode = 0o644
    archive.addfile(item, io.BytesIO(payload))


def export(commit, review, out):
    assert out.parent == PROOFS and out != ROOT and not out.exists(), 'choose a fresh sibling export directory'
    assert review == REVIEW and not review.is_symlink() and re.fullmatch('[0-9a-f]{40}', commit)
    review_bytes = review.read_bytes()
    report = json.loads(review_bytes)
    assert report['schema'] == 'p15_retained_actual_means_review_v1'
    assert report['current_source_commit'] == commit and report['all_23_accepted'] is True
    assert report['context_and_inventory_stable'] and not report['failures']
    assert report['git_before'] == report['git_after'] and report['context_before'] == report['context_after']
    context = report['context_after']
    assert len(report['owners']) == 23 and len(context['project_sources']) == 304
    assert not report['compilation_performed'] and not report['whole_P1_complete']

    retained = inventory()
    assert review in retained
    expected = {review: binding(review_bytes)}
    for module, digest in {**context['project_sources'], **context['protected_roots']}.items():
        path = PROJECT / (module.replace('.', '/') + '.lean')
        expected[path] = {'sha256': digest}
    for path, saved in context['configuration'].items():
        expected[PROJECT / path] = saved
    for path, saved in context['runtime'].items():
        expected[Path(path)] = saved
    for module, owner in report['owners'].items():
        owner_dir = ROOT / owner['original_source_commit'] / module
        for receipt in owner['receipts'].values():
            path = Path(receipt['path'])
            assert path in retained and path.is_relative_to(owner_dir)
            expected[path] = {k: receipt[k] for k in ('bytes', 'sha256')}

    paths = sorted(retained.union(expected))
    rows = []
    for path in paths:
        verified = fingerprint(path)
        assert all(verified[k] == v for k, v in expected.get(path, {}).items()), path
        rows.append({'path': str(path.relative_to(BASE)), **verified})

    actual = {'source_commit': commit, 'accepted_modules': sorted(report['owners']),
              'accepted_owners': len(report['owners']), 'retained_files': len(retained),
              'owned_declarations': sum(v['total_owned_exports'] for v in report['owners'].values()),
              'public_declarations': sum(v['total_public_exports'] for v in report['owners'].values()),
              'review_path': str(review.relative_to(BASE)), 'review_sha256': sha(review_bytes),
              'whole_P1_complete': False}
    index = (json.dumps({'actual_result': actual, 'files': rows}, sort_keys=True, indent=2) + '\n').encode()
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode='w') as tar:
        for row in rows:
            path = BASE / row['path']
            payload = path.read_bytes()
            assert (len(payload), sha(payload)) == (row['bytes'], row['sha256']), path
            add_member(tar, row['path'], payload)
        add_member(tar, 'ARCHIVE_FILES.json', index)
    raw = buffer.getvalue()
    packed = lzma.compress(raw)
    assert inventory() == retained, 'receipt root changed during export'
    for row in rows:
        path = BASE / row['path']
        assert fingerprint(path) == {k: row[k] for k in ('bytes', 'sha256')}, path
    out.mkdir(exist_ok=False)
    (out / 'ARCHIVE_FILES.json').write_bytes(index)
    archive = out / 'verification.tar.xz'
    archive.write_bytes(packed)
    summary = {'path': str(archive), 'bytes': len(packed), 'sha256': sha(packed),
               'uncompressed_tar_sha256': sha(raw), 'index_sha256': sha(index),
               'payload_files': len(rows), 'actual_result': actual}
    (out / 'SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('ARCHIVE_SUMMARY ' + json.dumps(summary), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('verification requires enabled Python assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--review', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    export(args.source_commit, args.review.absolute(), args.output_dir.resolve())
