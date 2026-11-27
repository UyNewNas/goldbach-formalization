#!/usr/bin/env python3
"""Package exact new-owner evidence; never traverses accepted import symlinks."""
from pathlib import Path
import hashlib
import json
import zipfile

WORK = Path('/workspace/p15-continue-20261127')
HERE = Path(__file__).resolve().parent
PART = Path('/workspace/p1-complete-proof/20261127-p15-disagreement-partition-v1')
RES = Path('/workspace/p1-complete-proof/20261127-p15-residual-carrier-v1')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


finals = [RES / 'formal-00000', PART / 'formal-coupled-00001']
accepted = []
for directory in finals:
    result = json.loads((directory / 'VALIDATION_RESULTS.json').read_text())
    assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
    source = Path(result['source']['path'])
    assert sha(source.read_bytes()) == result['source']['sha256']
    assert all(result[key]['exit_code'] == 0 for key in ('normal', 'kernel', 'audit'))
    exports = json.loads((directory / 'OWNED_EXPORTS.json').read_text())
    assert len(exports) == result['owned']
    assert all(set(row['axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'} for row in exports)
    accepted.append({key: result[key] for key in
        ('module', 'source', 'owned', 'private', 'axioms', 'normal_method', 'import_context')})
coupled = json.loads((finals[1] / 'COUPLED_IMPORT_VALIDATION.json').read_text())
assert coupled['status'] == 'PASS'
assert sum(row['owned'] for row in accepted) == 20
write('ACCEPTANCE.json', {'base_commit': '94ee23f6b197de4f5980ee2601f654afba49ef64',
    'owners': accepted, 'total_owned': 20, 'total_private': 3,
    'total_public': 17, 'superseded_owners_not_counted': True,
    'same_witness_and_admitting_side_coupled': True,
    'whole_P1_5_complete': False, 'original_register': '18/21'})
write('INDEPENDENT_REVIEW.json', {
    'reviewer': '/root/p15_partition_review', 'reviewer_is_author': False,
    'source_fingerprints': [row['source'] for row in accepted],
    'verdict': 'APPROVE_WITHIN_FINITE_PREREQUISITE_SCOPE', 'blocking_findings': [],
    'source_review': 'Same chosen owner carries the ordered residual tail and its admitting-side valid continuation. Signed coefficients, sign-before-mask attachment and complete-modulus filtering are preserved.',
    'validation_review': 'Both final owner normal/kernel/full-owned receipts and coupled import validation pass; original reused import fingerprints are unchanged.',
    'declined_to_judge': ['whole-atom tensor factorisation', 'collision payment',
                         'uniform signed medium', 'full P1.5 completion'],
    'reviewer_Lean_or_checker_commands': 0,
    'reviewer_mutations': False,
    'review_message_serialized_by': '/root',
    'historical_notes': ['The earlier regex concern was a JSON-escaped display misreading and was withdrawn.',
                         'The first import-shadowing failure remains preserved separately.'],
    'whole_P1_5_complete': False})

members = {}
for row in accepted:
    p = Path(row['source']['path'])
    members['sources/' + p.name] = p.read_bytes()
for base, prefix in [(PART, 'partition'), (RES, 'residual')]:
    for p in base.rglob('*'):
        if p.is_symlink() or not p.is_file():
            continue
        members[prefix + '/' + str(p.relative_to(base))] = p.read_bytes()
for name in ('validate.py', 'validate_residual.py', 'validate_coupled.py',
             'package_evidence.py', 'ACCEPTANCE.json', 'INDEPENDENT_REVIEW.json', 'README.md'):
    members['delivery/' + name] = (HERE / name).read_bytes()
index = [{'path': name, 'bytes': len(data), 'sha256': sha(data)}
         for name, data in sorted(members.items())]
members['FILE_INDEX.json'] = (json.dumps(index, indent=2) + '\n').encode()
archive = HERE / 'p15-residual-partition-evidence.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED) as z:
    for name, data in sorted(members.items()):
        z.writestr(name, data)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for row in index:
        data = z.read(row['path'])
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
write('ARCHIVE.json', {'archive': archive.name, 'bytes': archive.stat().st_size,
    'sha256': sha(archive.read_bytes()), 'members': len(members),
    'all_indexed_members_rehashed_and_CRC_verified': True,
    'import_symlink_payloads_excluded': True, 'whole_P1_5_complete': False})
print(json.dumps({'owners': len(accepted), 'owned': 20,
                  'archive_bytes': archive.stat().st_size, 'whole_P1_5_complete': False}))
