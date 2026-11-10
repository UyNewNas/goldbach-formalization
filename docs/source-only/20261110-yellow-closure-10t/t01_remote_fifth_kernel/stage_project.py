"""Remote-only exact-byte materializer. Does not invoke Lean, Lake or a guard."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def checked(path: Path, record: dict) -> bytes:
    data = path.read_bytes()
    if len(data) != record['bytes'] or hashlib.sha256(data).hexdigest() != record['sha256']:
        raise ValueError(f'Exact input changed: {path}')
    if 'git_blob_sha1' in record:
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != record['git_blob_sha1']:
            raise ValueError(f'Git blob differs: {path}')
    return data


def write_new(path: Path, data: bytes) -> None:
    if path.exists():
        raise ValueError(f'Destination already exists: {path}')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def main() -> None:
    if os.getenv('GITHUB_ACTIONS') != 'true':
        raise SystemExit('Run only in root-authorized GitHub Actions')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dest', type=Path, required=True)
    p.add_argument('--purpose', choices=['source_validation', 'yellow_green'], required=True)
    args = p.parse_args()
    manifest_bytes = (HERE / 'EXACT_INSTALL_MANIFEST.json').read_bytes()
    m = json.loads(manifest_bytes)
    t = m['targets'][0]
    if t['id'] != 'fifth_floor' or t['unresolved_modules']:
        raise ValueError('Wrong or unresolved target')
    if args.dest.exists():
        raise ValueError('A new isolated destination is required')
    if args.purpose == 'yellow_green':
        if not (t['whole_yellow_scope_complete'] and not t['remaining_mathematical_premises']):
            raise ValueError('Whole assigned source scope is incomplete')
    for r in m['review_inputs']:
        checked(ROOT / r['repository_path'], r)
    for r in m['reviewed_primary_sources']:
        checked(ROOT / r['repository_path'], r)
    config = {r['install_path']: r for r in m['configuration']}
    toolchain = checked(ROOT / config['lean-toolchain']['repository_path'], config['lean-toolchain'])
    lock = checked(ROOT / config['lake-manifest.json']['repository_path'], config['lake-manifest.json'])
    if toolchain.decode().strip() != m['toolchain']:
        raise ValueError('Wrong Lean toolchain')
    revs = {r['name']: r['rev'] for r in json.loads(lock)['packages']}
    if revs['mathlib'] != m['mathlib_rev'] or revs['goldbach'] != m['native_rev']:
        raise ValueError('Wrong dependency revisions')
    for r in m['support_files']:
        checked(HERE / r['path'], r)
    lakefile = checked(HERE / 'project-lakefile.toml', m['project_lakefile'])
    audit = checked(HERE / 'T01Audit.lean', m['audit_source'])
    args.dest.mkdir(parents=True)
    write_new(args.dest / 'lean-toolchain', toolchain)
    write_new(args.dest / 'lake-manifest.json', lock)
    write_new(args.dest / 'lakefile.toml', lakefile)
    for r in m['files']:
        source = HERE / r['bundle_path'] if r['must_bundle'] else ROOT / r['repository_path']
        write_new(args.dest / r['install_path'], checked(source, r))
    for r in m['data_inputs']:
        write_new(args.dest / r['install_path'], checked(ROOT / r['repository_path'], r))
    write_new(args.dest / 'T01Audit.lean', audit)
    provenance = {
        'target': t, 'source_commit': os.environ['SOURCE_COMMIT'],
        'run_id': os.environ['GITHUB_RUN_ID'], 'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'],
        'manifest_sha256': hashlib.sha256(manifest_bytes).hexdigest(),
        'audit_source_sha256': hashlib.sha256(audit).hexdigest(),
        'project_lakefile_sha256': hashlib.sha256(lakefile).hexdigest(),
        'source_identity_sha256': t['source_identity_sha256'],
        'source_count': len(m['files']), 'data_inputs': m['data_inputs'],
        'review_inputs': m['review_inputs'], 'purpose': args.purpose,
        'compiled': False, 'kernel_verified': False,
    }
    write_new(args.dest / 'T01_PROVENANCE.json', (json.dumps(provenance, indent=2) + '\n').encode())
    print(json.dumps({'status': 'MATERIALIZED_UNCOMPILED', 'target': t['id'],
                      'source_count': len(m['files']), 'data_count': len(m['data_inputs'])}))


if __name__ == '__main__':
    main()
