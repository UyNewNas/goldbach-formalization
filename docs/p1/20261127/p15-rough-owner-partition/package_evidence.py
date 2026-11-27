#!/usr/bin/env python3
"""Package only the new owner and its attempts, excluding reused import bytes."""
from pathlib import Path
import hashlib
import json
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = Path('/workspace/p1-complete-proof/20261127-p15-rough-owner-partition-v1')
FINAL = ROOT / 'formal-00003'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(name, data):
    (HERE / name).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


result = json.loads((FINAL / 'VALIDATION_RESULTS.json').read_text())
assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
assert result['module'] == 'ImbalancedChen.P1OriginalHistoricalRoughOwnerPartition'
source = Path(result['source']['path'])
assert sha(source.read_bytes()) == result['source']['sha256']
assert all(result[k]['exit_code'] == 0 for k in ('normal', 'kernel', 'audit'))
exports = json.loads((FINAL / 'OWNED_EXPORTS.json').read_text())
assert len(exports) == result['owned'] == 13 and result['private'] == 1
assert all(set(row['axioms']) <= ALLOWED for row in exports)
coupled = json.loads((FINAL / 'COUPLED_IMPORT_VALIDATION.json').read_text())
assert coupled['status'] == 'PASS' and coupled['reused_module_normal_or_kernel_commands'] == 0
review = json.loads((HERE / 'INDEPENDENT_REVIEW.json').read_text())
assert review['blocking_findings'] == [] and review['source_sha256'] == result['source']['sha256']
save('ACCEPTANCE.json', {
    'base_commit': 'eb49783592eddfa946382539a48649d2118e28a8',
    'owner': result, 'public_and_generated_nonprivate': 12,
    'superseded_versions_counted': False,
    'residual_reuse': coupled, 'original_register': '18/21',
    'whole_P1_5_complete': False})
members = {'sources/' + source.name: source.read_bytes()}
for p in ROOT.rglob('*'):
    if p.is_file() and not p.is_symlink():
        members['attempts/' + str(p.relative_to(ROOT))] = p.read_bytes()
for name in ('README.md', 'PLAN.md', 'validate.py', 'package_evidence.py',
             'ACCEPTANCE.json', 'INDEPENDENT_REVIEW.json', 'UPSTREAM_REUSE_CHECK.json'):
    members['delivery/' + name] = (HERE / name).read_bytes()
index = [{'path': name, 'bytes': len(data), 'sha256': sha(data)}
         for name, data in sorted(members.items())]
members['FILE_INDEX.json'] = (json.dumps(index, indent=2) + '\n').encode()
archive = HERE / 'p15-rough-owner-evidence.zip'
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
    for name, data in sorted(members.items()):
        z.writestr(name, data)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for row in index:
        data = z.read(row['path'])
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
save('ARCHIVE.json', {'archive': archive.name, 'bytes': archive.stat().st_size,
    'sha256': sha(archive.read_bytes()), 'members': len(members),
    'CRC_and_every_indexed_member_rehashed': True,
    'reused_import_symlink_payloads_excluded': True,
    'whole_P1_5_complete': False})
print(json.dumps({'status': 'PASS', 'owned': 13, 'private': 1,
                  'archive_bytes': archive.stat().st_size}))
