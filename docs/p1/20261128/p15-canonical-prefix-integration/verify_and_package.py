#!/usr/bin/env python3
"""Read-only receipt/audit checks, then archive exactly the three canonical-prefix context owners."""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def check(fp):
    p = Path(fp['path'])
    assert p.stat().st_size == fp['bytes'] and sha(p) == fp['sha256'], str(p)


def save(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


assert (ROOT / 'run.py').read_bytes() == (ROOT / 'EXECUTED_DRIVER.py').read_bytes()
donor = json.loads((ROOT / 'provenance/DONOR_ORIGINAL_RECORDS.json').read_text())
assert donor['original_record']['exit_code'] == 0
assert donor['new_donor_math_credit'] == 0 and donor['donor_binary_transplant'] is False
check(donor['source'])
check(donor['original_compiler'])
for original in donor['objects']:
    check(original)

selection = json.loads((ROOT / 'SOURCE_SELECTION.json').read_text())
coupled = json.loads((ROOT / 'COUPLED_IMPORT_VALIDATION.json').read_text())
assert coupled['status'] == 'PASS' and coupled['old_module_normal_or_kernel_commands'] == 0
assert coupled['inputs'] == json.loads((ROOT / 'REUSED_78_INPUTS.json').read_text())
for fp in coupled['inputs']:
    check(fp)
for r in selection['member_reused_boundary']:
    check(r['object'])
core_path = Path('/workspace/blue-build-tools/validate_member_roots_owned.py')
core_sha = 'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'
state_sha = '9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'
assert sha(core_path) == core_sha
assert sha('/workspace/blue-build-tools/member-runtime-evidence/state.json') == state_sha
spec = importlib.util.spec_from_file_location('original_owned_core', core_path)
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)
owners = []
for row in selection['sources']:
    module = row['module']
    folder = ROOT / 'modules' / module
    result = json.loads((folder / 'ACCEPTED.json').read_text())
    assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
    inputs = result['inputs']
    check(inputs['source'])
    assert inputs['guard_state_sha256'] == state_sha and inputs['audit_core_sha256'] == core_sha
    for dep in inputs['dependencies'].values():
        for fp in dep:
            check(fp)
    for fp in result['objects']:
        check(fp)
    for label in ('normal', 'kernel', 'audit'):
        assert result[label]['exit_code'] == 0
        check(result[label]['log'])
    attempt = Path(result['normal']['log']['path']).parent
    assert json.loads((attempt / 'VALIDATION_RESULTS.json').read_text()) == result
    assert (attempt / 'SELECTED_SOURCE.lean').read_bytes() == Path(inputs['source']['path']).read_bytes()
    assert [s for s in (attempt / 'kernel.log').read_text().splitlines() if s.startswith('replaying ')] == [
        'replaying ' + module]
    exports, inventory, axioms = core.read_audit((attempt / 'owned-audit.log').read_text(), [module], 0)
    assert exports == json.loads((attempt / 'OWNED_EXPORTS.json').read_text())
    assert inventory == json.loads((attempt / 'OWNED_INVENTORY.json').read_text())
    assert len(exports) == result['owned'] and inventory['private_name_count'] == result['private']
    assert set(axioms) <= ALLOWED
    preimage = ROOT / 'provenance' / (module + '.original.lean')
    assert preimage.stat().st_size == row['original_source']['bytes']
    assert sha(preimage) == row['original_source']['sha256']
    owners.append(result)
assert len(owners) == 3
result = json.loads((ROOT / 'RESULT.json').read_text())
assert result['status'] == 'PASS_CONTEXT_INTEGRATION'
assert result['modules'] == [r['module'] for r in owners]
assert result['owned_context_total'] == sum(r['owned'] for r in owners)
review = json.loads((ROOT / 'INDEPENDENT_REVIEW.json').read_text())
assert review['blocking_findings'] == []
assert review['source_sha256'] == {r['module']: r['inputs']['source']['sha256'] for r in owners}
assert review['driver_sha256'] == sha(ROOT / 'run.py')
acceptance = {'base_commit': selection['work_head'], 'owners': owners,
              'owned': sum(r['owned'] for r in owners), 'private': sum(r['private'] for r in owners),
              'reused_accepted_context_modules': 78, 'old_module_normal_or_kernel_commands': 0,
              'original_register': '18/21', 'whole_P1_5_complete': False}
save(ROOT / 'ACCEPTANCE.json', acceptance)
archive = ROOT / 'p15-canonical-prefix-integration-evidence.zip'
members = {}
for p in ROOT.rglob('*'):
    if p.is_file() and not p.is_symlink() and p != archive and p.name not in ('ARCHIVE.json', 'PUBLISHED.json'):
        assert '__pycache__' not in p.parts
        members[str(p.relative_to(ROOT))] = p.read_bytes()
index = [{'path': n, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}
         for n, b in sorted(members.items())]
members['FILE_INDEX.json'] = (json.dumps(index, indent=2) + '\n').encode()
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
    for n, b in sorted(members.items()):
        z.writestr(n, b)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for row in index:
        b = z.read(row['path'])
        assert len(b) == row['bytes'] and hashlib.sha256(b).hexdigest() == row['sha256']
save(ROOT / 'ARCHIVE.json', {'archive': archive.name, 'bytes': archive.stat().st_size,
     'sha256': sha(archive), 'members': len(members), 'CRC_and_each_member_rehashed': True,
     'reused_import_payloads_excluded': True, 'whole_P1_5_complete': False})
print(json.dumps({'status': 'PASS', 'owned': acceptance['owned'], 'private': acceptance['private'],
                  'archive_bytes': archive.stat().st_size}))
