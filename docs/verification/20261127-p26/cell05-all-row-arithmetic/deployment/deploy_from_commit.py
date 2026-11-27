"""Install this pinned package in its isolated P2 stage and run its preflight."""
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile

REPOSITORY = 'https://github.com/UyNewNas/goldbach-formalization.git'
FETCH = Path('/workspace/p26-cell05-arithmetic-source-20261127.git')
STAGE = Path('/workspace/p26-cell05-all-row-arithmetic-20261127-v1')
ARCHIVE = 'docs/verification/20261127-p26/cell05-all-row-arithmetic/deployment/deployment.tar.xz'
ARCHIVE_SHA = '4f642c9f2771dd8e4a58d5b0c24fa0ce66207b65c1b08f0e9b7cf0ee9b712780'
WORKFLOW_SHA = 'd5db6efd5dfa747af56c2cfa77db1e2bcbbab77f132e7983a0938fdb73185d42'


def main():
    commit = sys.argv[1]
    assert len(commit) == 40 and all(c in '0123456789abcdef' for c in commit)
    if not FETCH.exists():
        subprocess.run(['git', 'init', '--bare', str(FETCH)], check=True)
        subprocess.run(['git', '--git-dir', str(FETCH), 'remote', 'add', 'origin', REPOSITORY], check=True)
        subprocess.run(['git', '--git-dir', str(FETCH), 'config', 'remote.origin.promisor', 'true'], check=True)
        subprocess.run(['git', '--git-dir', str(FETCH), 'config', 'remote.origin.partialclonefilter', 'blob:none'], check=True)
    else:
        assert not FETCH.is_symlink()
        remote = subprocess.check_output(['git', '--git-dir', str(FETCH), 'remote', 'get-url', 'origin'], text=True).strip()
        assert remote == REPOSITORY
    subprocess.run(['git', '--git-dir', str(FETCH), 'fetch', '--depth=1', '--filter=blob:none', '--no-tags', 'origin', commit], check=True)
    body = subprocess.check_output(['git', '--git-dir', str(FETCH), 'show', commit + ':' + ARCHIVE])
    assert len(body) == 327380 and hashlib.sha256(body).hexdigest() == ARCHIVE_SHA
    with tarfile.open(fileobj=io.BytesIO(body), mode='r:xz') as archive:
        members = archive.getmembers()
        assert len(members) == 20 and len({m.name for m in members}) == 20
        assert all(m.isfile() and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts for m in members)
        data = {m.name: archive.extractfile(m).read() for m in members}
    manifest = json.loads(data['DEPLOYMENT_MANIFEST.json'])
    assert manifest['stage'] == str(STAGE) and manifest['workflow_sha256'] == WORKFLOW_SHA
    assert set(data) == {'DEPLOYMENT_MANIFEST.json'} | {r['path'] for r in manifest['files']}
    for row in manifest['files']:
        payload = data[row['path']]
        assert len(payload) == row['bytes'] and hashlib.sha256(payload).hexdigest() == row['sha256']
    for name, payload in data.items():
        path = STAGE / name
        for parent in (path, *path.parents):
            assert not parent.is_symlink(), str(parent)
        if path.exists():
            assert path.is_file() and path.read_bytes() == payload, str(path)
    for name, payload in data.items():
        path = STAGE / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists():
            with path.open('xb') as stream:
                stream.write(payload)
    print(json.dumps({'status': 'EXACT_DEPLOYMENT', 'commit': commit, 'archive_sha256': ARCHIVE_SHA,
                      'workflow_sha256': WORKFLOW_SHA, 'files': len(data), 'new_Lean_commands': 0}), flush=True)
    runner = STAGE / 'tools/p26/cell05-all-row-arithmetic-20261127/run_arithmetic.py'
    subprocess.run([sys.executable, '-I', '-S', '-B', str(runner), 'preflight',
                    '--workflow-sha256', WORKFLOW_SHA], cwd='/workspace', check=True)


if __name__ == '__main__':
    main()
