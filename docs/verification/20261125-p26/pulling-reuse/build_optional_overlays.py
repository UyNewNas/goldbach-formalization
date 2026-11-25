#!/usr/bin/env python3
"""Prepare narrowly scoped source overlays; never write the production tree."""
from pathlib import Path
import difflib
import hashlib
import json

ROOT = Path(__file__).resolve().parent
SOURCE = Path('/workspace/p26-source-closure')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def patch(name, old, new):
    return ''.join(difflib.unified_diff(
        old.decode().splitlines(keepends=True), new.decode().splitlines(keepends=True),
        fromfile='a/ImbalancedChen/' + name, tofile='b/ImbalancedChen/' + name))


def main():
    target = ROOT / 'optional/ImbalancedChen'
    target.mkdir(parents=True, exist_ok=True)
    records = []
    name = 'P2OriginalSaving19OwnedIntegral.lean'
    old = (SOURCE / 'ImbalancedChen' / name).read_bytes()
    assert sha(old) == 'ab58f4acc2a2ea93919d0ee37e5c63e1dba1f07fd704833fefc042d0bb61bafc'
    old_import = b'import ImbalancedChen.P2OriginalSaving19PullingOwnership\n'
    new_import = b'import ImbalancedChen.P2OriginalSaving19PullingReuse\n'
    old_open = b'open P2OriginalSaving19PullingOwnership\n'
    new_open = b'open P2OriginalSaving19PullingReuse\n'
    assert old.count(old_import) == old.count(old_open) == 1
    new = old.replace(old_import, new_import).replace(old_open, new_open)
    assert new.replace(new_import, old_import).replace(new_open, old_open) == old
    (target / name).write_bytes(new)
    (ROOT / 'OWNED_INTEGRAL_REWIRE.patch').write_text(patch(name, old, new))
    records.append({'module': 'ImbalancedChen.' + name[:-5], 'original_sha256': sha(old),
                    'candidate_sha256': sha(new), 'original_bytes': len(old),
                    'candidate_bytes': len(new), 'only_changes': ['one import', 'one open'],
                    'all_other_bytes_identical': True})

    name = 'P2OriginalSaving19OwnedSource.lean'
    old = (SOURCE / 'ImbalancedChen' / name).read_bytes()
    assert sha(old) == 'e18f481c54879b7a51346db7f3549c1ac12f393a194b79322a600e7bf89c1c8b'
    old_import = b'import ImbalancedChen.P2OriginalSaving19Original28918\n'
    new_import = old_import + b'import ImbalancedChen.P2OriginalSaving19GateProper\n'
    old_proof = (
        b'    (\xe2\x88\x80 c (v : VertexIndex c) g, 0 \xe2\x89\xa4 evalQ (gate c g) (originalPoint c v)) := by\n'
        b'  decide\n')
    new_proof = old_proof[:-len(b'  decide\n')] + (
        b'  constructor\n'
        b'  \xc2\xb7 intro c g\n'
        b'    exact P2OriginalSaving19GateProper.original_gate_normals_nonzero c g\n'
        b'  \xc2\xb7 decide +kernel\n')
    assert old.count(old_import) == old.count(old_proof) == 1
    new = old.replace(old_import, new_import).replace(old_proof, new_proof)
    assert new.replace(new_import, old_import).replace(new_proof, old_proof) == old
    (target / name).write_bytes(new)
    (ROOT / 'OWNED_SOURCE_GATE_REUSE.patch').write_text(patch(name, old, new))
    records.append({'module': 'ImbalancedChen.' + name[:-5], 'original_sha256': sha(old),
                    'candidate_sha256': sha(new), 'original_bytes': len(old),
                    'candidate_bytes': len(new), 'only_changes': ['one import',
                    'original_gate_checks proof reuses accepted properness and retains closed nonnegative guard'],
                    'all_other_bytes_identical': True, 'compiled': False})
    (ROOT / 'OPTIONAL_OVERLAY_AUDIT.json').write_text(json.dumps({
        'schema': 'saving19-pulling-reuse-optional-overlays-v1',
        'installed': False, 'compiled': False, 'records': records,
        'noncomputable_getter_migration_not_attempted': True}, indent=2) + '\n')
    print(json.dumps(records, indent=2))


if __name__ == '__main__':
    main()
