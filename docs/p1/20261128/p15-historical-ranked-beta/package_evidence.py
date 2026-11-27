#!/usr/bin/env python3
"""Check and package only the new canonical owner and immutable attempts."""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
FINAL = ROOT / 'formal-00002'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}


def sha(p):
    with Path(p).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def check(fp):
    p = Path(fp['path'])
    assert p.stat().st_size == fp['bytes'] and sha(p) == fp['sha256'], str(p)


result = json.loads((FINAL / 'VALIDATION_RESULTS.json').read_text())
for n in (0, 1):
    old = ROOT / ('formal-' + str(n).zfill(5))
    initial = json.loads((old / 'SOURCE_AND_REUSED_IMPORT_BEFORE.json').read_text())[0]
    assert (old / 'SELECTED_SOURCE.lean').stat().st_size == initial['bytes']
    assert sha(old / 'SELECTED_SOURCE.lean') == initial['sha256']
    assert (ROOT / ('validate_' + str(n).zfill(5) + '.py')).read_bytes() == (old / 'EXECUTED_DRIVER.py').read_bytes()
assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
assert result['owned'] == 16 and result['private'] == 1
assert result['module'] == 'ImbalancedChen.P1OriginalHistoricalRankedBeta'
check(result['source'])
assert Path(result['source']['path']).read_bytes() == (FINAL / 'SELECTED_SOURCE.lean').read_bytes()
assert (ROOT / 'validate_00002.py').read_bytes() == (FINAL / 'EXECUTED_DRIVER.py').read_bytes()
for label in ('normal', 'kernel', 'audit'):
    assert result[label]['exit_code'] == 0
    check(result[label]['log'])
assert [s for s in (FINAL / 'kernel.log').read_text().splitlines() if s.startswith('replaying ')] == [
    'replaying ' + result['module']]
for fp in json.loads((FINAL / 'OUTPUTS_AFTER_NORMAL.json').read_text()):
    check(fp)
for fp in json.loads((FINAL / 'SOURCE_AND_REUSED_IMPORT_AFTER.json').read_text()):
    check(fp)
coupled = json.loads((FINAL / 'COUPLED_IMPORT_VALIDATION.json').read_text())
assert coupled['status'] == 'PASS' and coupled['accepted_import_normal_or_kernel_commands'] == 0
for fp in coupled['inputs']:
    check(fp)
core_path = Path('/workspace/blue-build-tools/validate_member_roots_owned.py')
assert sha(core_path) == result['original_audit_core_sha256']
assert sha('/workspace/blue-build-tools/member-runtime-evidence/state.json') == result['original_guard_state_sha256']
spec = importlib.util.spec_from_file_location('original_core', core_path)
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)
exports, inventory, axioms = core.read_audit((FINAL / 'owned-audit.log').read_text(), [result['module']], 0)
assert exports == json.loads((FINAL / 'OWNED_EXPORTS.json').read_text())
assert inventory == json.loads((FINAL / 'OWNED_INVENTORY.json').read_text())
assert len(exports) == 16 and set(axioms) <= ALLOWED
review = json.loads((ROOT / 'INDEPENDENT_REVIEW.json').read_text())
assert review['blocking_findings'] == [] and review['source_sha256'] == result['source']['sha256']
acceptance = {'base_commit': '82bff271ddde80b88abe18467aa3517ca19038a8',
    'owner': result, 'coupled_imports': coupled, 'owned': 16, 'private': 1, 'original_register': '18/21', 'whole_P1_5_complete': False}
(ROOT / 'ACCEPTANCE.json').write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + '\n')
archive = ROOT / 'p15-historical-ranked-beta-evidence.zip'
members = {}
for p in ROOT.rglob('*'):
    if p.is_file() and not p.is_symlink() and p != archive and p.name != 'ARCHIVE.json':
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
    for x in index:
        b = z.read(x['path'])
        assert len(b) == x['bytes'] and hashlib.sha256(b).hexdigest() == x['sha256']
(ROOT / 'ARCHIVE.json').write_text(json.dumps({'archive': archive.name,
    'bytes': archive.stat().st_size, 'sha256': sha(archive), 'members': len(members),
    'CRC_and_each_member_rehashed': True, 'reused_import_payloads_excluded': True,
    'whole_P1_5_complete': False}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'owned': 16, 'private': 1, 'archive_bytes': archive.stat().st_size}))
