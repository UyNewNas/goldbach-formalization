#!/usr/bin/env python3
"""Recheck frozen evidence; package no reused import payloads or new compiles."""
from pathlib import Path
import difflib
import hashlib
import importlib.util
import json
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
WORK = Path('/workspace/p15-continue-20261127')
CORE = Path('/workspace/blue-build-tools/validate_member_roots_owned.py')
STATE = Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}


def sha(p):
    with Path(p).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def check(fp):
    p = Path(fp['path'])
    assert p.stat().st_size == fp['bytes'] and sha(p) == fp['sha256'], str(p)


def save(p, data):
    p.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


selection = json.loads((ROOT / 'SOURCE_SELECTION.json').read_text())
result = json.loads((ROOT / 'RESULT.json').read_text())
assert result['status'] == 'PASS_CONTEXT_INTEGRATION'
assert len(selection['sources']) == len(result['modules']) == 78
assert result['modules'] == [r['module'] for r in selection['sources']]
assert sha(ROOT / 'run.py') == sha(ROOT / 'EXECUTED_DRIVER_00000.py') == \
    '7a59df4ab1da60f9a4c25314c0ba9a89db2e6ed8eb1085f5de219c817a0d889e'
assert sha(STATE) == '9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'
assert sha(CORE) == 'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'
for row in selection['member_reused_boundary']:
    check(row['object'])
spec = importlib.util.spec_from_file_location('original_owned_core', CORE)
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)
records, patches = [], []
for row in selection['sources']:
    module = row['module']
    r = json.loads((ROOT / 'modules' / module / 'ACCEPTED.json').read_text())
    assert r['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
    assert not r['reused_donor_math_counted_as_new'] and not r['whole_P1_5_complete']
    check(r['inputs']['source'])
    for fps in r['inputs']['dependencies'].values():
        for fp in fps:
            check(fp)
    for fp in r['objects']:
        check(fp)
    for label in ('normal', 'kernel', 'audit'):
        assert r[label]['exit_code'] == 0
        check(r[label]['log'])
    kernel = Path(r['kernel']['log']['path']).read_text()
    assert [s for s in kernel.splitlines() if s.startswith('replaying ')] == ['replaying ' + module]
    audit_log = Path(r['audit']['log']['path'])
    exports, inventory, axioms = core.read_audit(audit_log.read_text(), [module], 0)
    assert len(exports) == r['owned'] and inventory['private_name_count'] == r['private']
    assert set(axioms) <= ALLOWED and axioms == r['axioms']
    assert exports == json.loads((audit_log.parent / 'OWNED_EXPORTS.json').read_text())
    assert inventory == json.loads((audit_log.parent / 'OWNED_INVENTORY.json').read_text())
    source = Path(r['inputs']['source']['path'])
    relative = module.replace('.', '/') + '.lean'
    original = subprocess.check_output(['git', '-C', str(WORK), 'show',
        selection['work_head'] + ':' + relative], text=True)
    patches.extend(difflib.unified_diff(original.splitlines(True),
        source.read_text().splitlines(True), fromfile='a/' + relative, tofile='b/' + relative))
    records.append(r)
save(ROOT / 'READONLY_VERIFICATION.json', {
    'status': 'PASS_ALL_78_FROZEN_RECORDS_REHASHED_AND_AUDITS_REPARSED',
    'modules': len(records), 'owned_context_total': sum(r['owned'] for r in records),
    'private_context_total': sum(r['private'] for r in records),
    'donor_sources_revalidated': sum('P3.6' in r['source_origin'] for r in records),
    'source_sha256': {r['module']: r['inputs']['source']['sha256'] for r in records},
    'original_Member_boundary': len(selection['member_reused_boundary']),
    'old_Member_normal_or_kernel_commands': 0, 'whole_P1_5_complete': False})
(ROOT / 'PUBLICATION_SOURCE_DIFF.patch').write_text(''.join(patches))
if '--verify-only' in sys.argv:
    print((ROOT / 'READONLY_VERIFICATION.json').read_text())
    raise SystemExit(0)
review = json.loads((ROOT / 'INDEPENDENT_REVIEW.json').read_text())
assert review['blocking_findings'] == []
assert review['source_sha256'] == {r['module']: r['inputs']['source']['sha256'] for r in records}
save(ROOT / 'ACCEPTANCE.json', {
    'scope': 'isolated Member-context normal, exact module kernel and full-owned audit',
    'targets': selection['targets'], 'module_count': len(records),
    'owned_context_total': sum(r['owned'] for r in records),
    'private_context_total': sum(r['private'] for r in records),
    'donor_sources_revalidated': sum('P3.6' in r['source_origin'] for r in records),
    'new_donor_mathematical_credit': 0, 'old_Member_normal_or_kernel_commands': 0,
    'original_proper_power_register': '18/21; three recorded HOLDs unchanged',
    'whole_P1_5_complete': False, 'records': records})
archive = ROOT / 'p15-whole-atom-integration-evidence.zip'
members = {}
for p in ROOT.rglob('*'):
    if p.is_file() and not p.is_symlink() and p != archive and p.name != 'ARCHIVE.json':
        assert '__pycache__' not in p.parts, str(p)
        members[str(p.relative_to(ROOT))] = p.read_bytes()
index = [{'path': name, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    for name, data in sorted(members.items())]
members['FILE_INDEX.json'] = (json.dumps(index, indent=2) + '\n').encode()
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
    for name, data in sorted(members.items()):
        z.writestr(name, data)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for row in index:
        data = z.read(row['path'])
        assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
save(ROOT / 'ARCHIVE.json', {'archive': archive.name, 'bytes': archive.stat().st_size,
    'sha256': sha(archive), 'members': len(members),
    'CRC_and_every_indexed_member_rehashed': True,
    'reused_import_symlink_payloads_excluded': True, 'whole_P1_5_complete': False})
print(json.dumps({'status': 'PASS', 'modules': len(records), 'archive_bytes': archive.stat().st_size}))
