#!/usr/bin/env python3
"""Validate only the new owner in isolated outputs, under the original lane.

Normal compilation uses guarded Lean directly, not a Lake named-target build.
Existing imported owners are reused; no live project sources/caches are changed.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

WORK = Path('/workspace/p15-continue-20261127')
PROJECT = Path('/workspace/blue-member-build')
OUT = Path('/workspace/p1-complete-proof/20261127-p15-disagreement-partition-v1/formal-00001')
STATE = Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
STATE_SHA = '9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'
MODULE = 'ImbalancedChen.P1OriginalHistoricalDisagreementPartition'
SOURCE = WORK / 'ImbalancedChen/P1OriginalHistoricalDisagreementPartition.lean'
CORE = Path('/workspace/blue-build-tools/validate_member_roots_owned.py')
CORE_SHA = 'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'
BASE = PROJECT / 'ImbalancedChen/P1OriginalHistoricalFirstDisagreement.lean'
BASE_OBJECT = PROJECT / '.lake/build/lib/lean/ImbalancedChen/P1OriginalHistoricalFirstDisagreement.olean'


def fingerprint(path):
    return {'path': str(path), 'bytes': path.stat().st_size,
            'sha256': hashlib.file_digest(path.open('rb'), 'sha256').hexdigest()}


def save(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def run(label, command, environment):
    log = OUT / (label + '.log')
    assert not log.exists(), 'Never replay a retained successful/ambiguous attempt'
    receipt = {'argv': command, 'cwd': str(PROJECT), 'started_utc':
               datetime.datetime.now(datetime.timezone.utc).isoformat()}
    save(label + '-started.json', receipt)
    started = time.monotonic()
    with log.open('xb') as output:
        result = subprocess.run(command, cwd=PROJECT, env=environment,
                                stdout=output, stderr=subprocess.STDOUT)
    receipt.update(exit_code=result.returncode, wall_seconds=time.monotonic()-started,
                   finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   log=fingerprint(log))
    save(label + '-command.json', receipt)
    if result.returncode:
        print(log.read_text()[-12000:], flush=True)
        raise RuntimeError(label + ' failed')
    return receipt


def worker():
    assert fingerprint(STATE)['sha256'] == STATE_SHA
    assert fingerprint(CORE)['sha256'] == CORE_SHA
    before = [fingerprint(p) for p in (SOURCE, BASE, BASE_OBJECT, STATE, CORE)]
    save('SOURCE_AND_REUSED_IMPORT_BEFORE.json', before)
    lib = OUT / 'build/lib/lean'
    namespace = lib / 'ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
    original_namespace = PROJECT / '.lake/build/lib/lean/ImbalancedChen'
    assert not (original_namespace / (MODULE.split('.')[-1] + '.olean')).exists()
    # Reuse accepted import bytes through absolute symlinks: Lean resolves
    # an entire namespace from the first matching LEAN_PATH entry.
    links = []
    for source in original_namespace.rglob('*'):
        target = namespace / source.relative_to(original_namespace)
        if source.is_symlink():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(source)
            links.append({'path': str(target), 'target': str(source)})
        elif source.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        elif source.is_file():
            target.symlink_to(source)
            links.append({'path': str(target), 'target': str(source)})
    save('REUSED_IMPORT_LINKS.json', links)
    ir = OUT / 'build/ir/ImbalancedChen'
    ir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_PATH'] = str(lib) + os.pathsep + env.get('LEAN_PATH', '')
    name = MODULE.split('.')[-1]
    normal = run('normal', ['lean', '--root=' + str(WORK),
        '-o', str(lib / 'ImbalancedChen' / (name + '.olean')),
        '-i', str(lib / 'ImbalancedChen' / (name + '.ilean')),
        '-c', str(ir / (name + '.c')), str(SOURCE)], env)
    produced = [fingerprint(lib / 'ImbalancedChen' / (name + ext))
                for ext in ('.olean', '.ilean')] + [fingerprint(ir / (name + '.c'))]
    save('OUTPUTS_AFTER_NORMAL.json', produced)
    kernel = run('kernel', ['leanchecker', '--verbose', MODULE], env)
    replayed = [line.removeprefix('replaying ') for line in
                (OUT / 'kernel.log').read_text().splitlines() if line.startswith('replaying ')]
    assert replayed == [MODULE], replayed
    spec = importlib.util.spec_from_file_location('original_owned_core', CORE)
    core = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(core)
    audit_source = OUT / 'OwnedAudit.lean'
    audit_source.write_text(core.make_audit_code([MODULE]))
    audit = run('owned-audit', ['lean', '-Dpp.maxSteps=1000000', str(audit_source)], env)
    raw = (OUT / 'owned-audit.log').read_text()
    declarations, inventory, axioms = core.read_audit(raw, [MODULE], audit['exit_code'])
    # Reject elisions both literally and as finite Unicode escape sequences.
    import re
    for row in declarations:
        for value in [row['type'], row['type_expression'], *row['universe_parameters']]:
            decoded = value
            for _ in range(3):
                decoded = re.sub(r'\\u([0-9a-fA-F]{4})|\\U([0-9a-fA-F]{8})',
                    lambda m: chr(int(m.group(1) or m.group(2), 16)), decoded)
            assert not any(token in decoded for token in ('sorryAx', '…', '⋯', '...'))
    save('OWNED_EXPORTS.json', declarations)
    save('OWNED_INVENTORY.json', inventory)
    after = [fingerprint(p) for p in (SOURCE, BASE, BASE_OBJECT, STATE, CORE)]
    assert before == after
    assert all(Path(row['path']).is_symlink() and
               os.readlink(row['path']) == row['target'] for row in links)
    assert produced == [fingerprint(Path(row['path'])) for row in produced]
    save('SOURCE_AND_REUSED_IMPORT_AFTER.json', after)
    save('VALIDATION_RESULTS.json', {'status': 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED',
        'module': MODULE, 'source': before[0], 'normal': normal, 'kernel': kernel,
        'audit': audit, 'owned': len(declarations),
        'private': inventory['private_name_count'], 'axioms': axioms,
        'original_guard_state_sha256': STATE_SHA, 'original_audit_core_sha256': CORE_SHA,
        'normal_method': 'guarded Lean with isolated outputs, not Lake named-target acceptance',
        'import_context': 'Existing accepted FirstDisagreement module and its imports; no fresh import replay',
        'live_source_or_live_cache_edits': False, 'whole_P1_5_complete': False})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--worker', action='store_true')
    args = ap.parse_args()
    if args.worker:
        worker()
        return
    assert not OUT.exists(), 'Choose a new explicit attempt rather than overwrite evidence'
    OUT.mkdir(parents=True)
    command = ['python3', '/workspace/blue-build-tools/serialize_validation_lane.py',
        '--state', str(STATE), '--receipt', str(OUT / 'LANE.json'),
        'python3', '/workspace/blue-build-tools/run_guarded.py', '--state', str(STATE),
        'lake', '--no-build', 'env', 'python3', '-B', str(Path(__file__).resolve()), '--worker']
    result = subprocess.run(command, cwd=PROJECT)
    raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
