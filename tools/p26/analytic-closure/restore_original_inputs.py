"""Restore original bytes from the explicitly authorized, pinned input archive.

Byte identity is checked against the existing archive-core ledger. This utility
does not grant Lean proof or cached-object acceptance.
"""
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-analytic-closure-20261127/original13-transfer')
GIT = STAGE / 'inputs.git'
COMMIT = 'a2a7146f8de2beb8fc79f09d111f4af023840580'
ARCHIVE_SHA256 = '201942a41594e4bc3133b3fe7cc771c20452c6917fc415a427b3477b0ab50a2d'
DEST = Path('/workspace/goldbach-research')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    def blob(name):
        return subprocess.check_output(['git', '--git-dir=' + str(GIT),
                                        'show', COMMIT + ':' + name])

    archive = blob('original-inputs.tar.xz')
    assert len(archive) == 18600020 and sha(archive) == ARCHIVE_SHA256
    manifest = json.loads(blob('MANIFEST.json'))
    ledger_path = ROOT / 'docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json'
    ledger = json.loads(ledger_path.read_text())
    expected = {Path(x['loader_absolute_path']).name: (x['bytes'], x['sha256'])
                for x in ledger['all_inputs']}
    recorded = {x['name']: (x['bytes'], x['sha256']) for x in manifest['sources']}
    assert recorded == expected and len(expected) == 26
    payloads = {}
    with tarfile.open(fileobj=io.BytesIO(archive), mode='r:xz') as tar:
        for member in tar:
            assert member.isfile() and member.name in expected
            assert member.name not in payloads and Path(member.name).name == member.name
            data = tar.extractfile(member).read()
            assert (len(data), sha(data)) == expected[member.name]
            payloads[member.name] = data
    assert set(payloads) == set(expected)
    assert sum(map(len, payloads.values())) == 80189086
    # Check every existing destination before writing any missing file.
    for name, data in payloads.items():
        path = DEST / name
        if path.exists():
            assert path.is_file() and path.read_bytes() == data, path
    DEST.mkdir(exist_ok=True)
    restored = []
    for name, data in payloads.items():
        path = DEST / name
        if not path.exists():
            with path.open('xb') as output:
                output.write(data)
            restored.append(name)
        assert (path.stat().st_size, sha(path.read_bytes())) == expected[name]
    (STAGE / 'original-inputs.tar.xz').write_bytes(archive)
    report = {
        'schema': 'p26_original13_cloud_restore_v1',
        'commit': COMMIT, 'archive_bytes': len(archive),
        'archive_sha256': ARCHIVE_SHA256, 'ledger_sha256': sha(ledger_path.read_bytes()),
        'destination': str(DEST), 'verified_sources': len(expected),
        'verified_raw_bytes': 80189086, 'newly_restored': restored,
        'all_original_bytes_match': True, 'formal_acceptance': False,
        'P2_6_complete': False,
    }
    (STAGE / 'RESTORE.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'newly_restored'}, indent=2))


if __name__ == '__main__':
    main()
