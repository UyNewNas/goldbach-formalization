#!/usr/bin/env python3
"""Refresh only P160 division after the proof-only declaration-collision repair."""

import base64
import hashlib
import json
import lzma
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile


ROOT = Path('/workspace/p2-1-original96-20261126')
HERE = Path('verification/part2/original96')
PRIVATE = Path('.lake/p2-private')
ARCHIVE = Path('original96-acceptance-attempt-002.tar.xz')
ARCHIVE_SHA = '8ef2c54ee98551220e4af28cabea2448a646757fb95c41eedc10eb6cd5c9482b'
ARCHIVE_SIZE = 1369720
REFERENCE_SHA = '09f62777eb9996fb7c7d41e27238afec282b904a8072cc9555d055c6ec43cfc5'
DIVISION = 'ImbalancedChen.Certificates.P2OriginalP160DirectDivision'
SOURCE = DIVISION.replace('.', '/') + '.lean'
SOURCE_SHA = '9ed96205fe8d95563b180f94e1810a29fa1e69d20ab2aaafa10c9f8209994a3e'
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
BASELINE = Path('.lake/original96-baseline')
BASELINE_SHA = '8657cfffef159185f73c6a04ae4d31c846c0d0a9'
JOINT_HELPERS = {
    'freeze_joint_reference.py': '5af69fa31010ebf08f0189eae29b278ce588e074673c9cc1fed7c1d6cf33a901',
    'run_joint_increment.py': 'd4be3348f0d1d12dc4721409fd7b89b9563203b8a99bbb0aaeaf7ecfc610f664',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(path):
    return json.loads(Path(path).read_bytes())


def check_pins(pins):
    for path, expected in pins.items():
        require(sha(path) == expected, 'changed proof input: ' + str(path))


def receipt_for(name, record):
    latest = PRIVATE / 'audit' / name / 'latest.json'
    receipt = read(latest)
    require(receipt['module'] == name and receipt['accepted'] and
            receipt['source_sha256'] == record['source_sha256'] == sha(record['source']) and
            receipt['object_sha256'] == record['object_sha256'] == sha(record['object']) and
            receipt['compile_closure_signature'] == record['closure_signature'], 'bad owner binding: ' + name)
    require(receipt['replay']['command'] == [str(LEAN.with_name('leanchecker')), '--verbose', name] and
            all(receipt[gate]['exit_code'] == 0 and receipt[gate]['inputs_unchanged']
                for gate in ('replay', 'audit')), 'missing stock replay/audit: ' + name)
    check_pins(receipt['artifacts'])
    decl, = (p for p in receipt['artifacts'] if p.endswith('/declarations.json'))
    historical = Path(decl).with_name('receipt.json')
    require(sha(historical) == sha(latest), 'latest receipt differs from its attempt: ' + name)
    entries = read(decl)['declarations']
    require(all(row['module'] == name and all(row[k] is False for k in ('unsafe', 'partial', 'axiom')) and
                set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
                for row in entries), 'unsafe, partial or axiomatic declaration: ' + name)
    return receipt, {'source': [record['source'], record['source_sha256']],
                     'object': [record['object'], record['object_sha256']],
                     'receipt': [str(historical), sha(historical)],
                     'declarations': [decl, receipt['artifacts'][decl]],
                     'count': receipt['audit']['declaration_count']}


def main():
    require(Path.cwd().resolve() == ROOT, f'execute within {ROOT}')
    joint = HERE / 'joint'
    reference = joint / 'joint-reference.json.xz'
    pins = {joint / path: value for path, value in JOINT_HELPERS.items()}
    pins.update({reference: REFERENCE_SHA, ARCHIVE: ARCHIVE_SHA, SOURCE: SOURCE_SHA})
    check_pins(pins)
    sys.path.insert(0, str(ROOT / joint))
    from freeze_joint_reference import new_reference, shared_providers
    from run_joint_increment import LEAN_SHA256, MATHLIB, MATHLIB_PIN, owned

    frozen_joint = json.loads(lzma.decompress(reference.read_bytes()))
    original = frozen_joint['new_archive']['summary']
    archived = new_reference(ARCHIVE, ARCHIVE_SHA, ARCHIVE_SIZE, original)
    providers = shared_providers(frozen_joint['old'], archived)
    pins.update({**original['reviewed_inputs'], SOURCE: SOURCE_SHA, LEAN: LEAN_SHA256,
                 LEAN.with_name('leanchecker'): 'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a'})
    proof_inputs = dict(original['proof_inputs'])
    division_obj = str(PRIVATE / 'lib' / (DIVISION.replace('.', '/') + '.olean'))
    pins.update({p: digest for p, digest in proof_inputs.items() if p not in {SOURCE, division_obj}})
    check_pins(pins)
    for path, expected in archived['frozen_files'].items():
        if Path(path).name in {'records.json', 'summary.json'}:
            check_pins({path: expected})
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB, text=True).strip() == MATHLIB_PIN and
            subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=BASELINE, text=True).strip() == BASELINE_SHA and
            not any((BASELINE / '.lake/build/lib/lean').rglob('*')), 'baseline or Mathlib is not frozen')
    records_path = PRIVATE / 'records.json'
    initial_records = read(records_path)
    old_names = owned(frozen_joint['old'])
    require(len(old_names) == 18581, 'unexpected original owned inventory size')
    _, compile_path = original['proof_lean_path'].split(':', 1)
    env = dict(os.environ, LEAN_PATH=compile_path)
    attempts = Path('evidence/original96-division-refresh')
    attempts.mkdir(parents=True, exist_ok=True)
    attempt = Path(tempfile.mkdtemp(prefix='attempt-', dir=attempts))
    commands = []

    def run(label, argv, execution_env=env):
        check_pins(pins)
        log = attempt / (label + '.log')
        with log.open('wb') as stream:
            result = subprocess.run(argv, env=execution_env, stdout=stream, stderr=subprocess.STDOUT)
        commands.append({'argv': argv, 'exit_code': result.returncode, 'log': str(log), 'sha256': sha(log),
                         'lean_path': execution_env['LEAN_PATH']})
        (attempt / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        check_pins(pins)
        require(result.returncode == 0, f'{label} failed: {log}\n' + log.read_text(errors='replace')[-5000:])
        return log.read_text()

    try:
        strict = run('strict-compile', [sys.executable, '-B', 'verification/part2/run_winner9_private_checks.py',
                     '--baseline-root', str(BASELINE), '--workers', '1', '--threads', '1', '--memory-mb', '6144', DIVISION])
        require([line.split()[1] for line in strict.splitlines() if line.startswith('PASS ')] == [DIVISION],
                'expected only the refreshed division compile')
        audit_summary = 'p21-original96-division-refresh-' + attempt.name + '.json'
        audit_log = run('owned-stock-audit', [sys.executable, '-B', 'verification/part2/run_winner9_private_audit.py',
                        '--memory-mb', '6144', '--summary-name', audit_summary, DIVISION])
        fresh = read(PRIVATE / 'audit' / audit_summary)
        require(fresh['all_accepted'] and set(fresh['modules']) == {DIVISION} and
                not fresh['modules'][DIVISION]['reused'] and f'REPLAY {DIVISION}\n' in audit_log,
                'expected only a fresh division replay and owned audit')
        records = read(records_path)
        require({k:v for k,v in records.items() if k != DIVISION} ==
                {k:v for k,v in initial_records.items() if k != DIVISION}, 'unrelated compiler record changed')
        receipts, owners = {}, {}
        for name in original['modules']:
            receipts[name], owners[name] = receipt_for(name, records[name])
            if name != DIVISION:
                for field in ('source', 'object', 'receipt', 'declarations'):
                    require(owners[name][field][1] == archived['owners'][name][field][1],
                            'reused logarithm evidence differs: ' + name + '/' + field)
        group = {'owners': owners, 'checks': archived['checks']}
        names = owned(group)
        collisions = sorted(names & old_names)
        require(not collisions, 'duplicate with original 140: ' + str(collisions))
        proof_inputs.update({SOURCE: SOURCE_SHA, division_obj: records[DIVISION]['object_sha256']})
        current = {path: digest for path, digest in proof_inputs.items()}
        current.update({str(records_path): sha(records_path)})
        for row in owners.values():
            current.update(row[key] for key in ('receipt', 'declarations'))
        check_pins(current)
        run('p160-division-contract', [str(LEAN), '-DwarningAsError=true', '-DmaxRecDepth=50000',
            '-DmaxHeartbeats=40000000', str(HERE / 'P160DivisionContract.lean')],
            dict(env, LEAN_PATH=original['proof_lean_path']))
        check_pins(current)
        summary = dict(original, status='ACCEPTED_ORIGINAL96_DIVISION_REFRESH', proof_inputs=proof_inputs,
                       reviewed_inputs={str(p): h for p,h in pins.items()},
                       owned_declarations=len(names), unique_owned_declarations=len(names), duplicate_owned_declarations={},
                       union_owned_declarations=len(old_names | names), union_duplicate_owned_declarations={},
                       freshly_compiled_this_attempt=[DIVISION], fresh_audit_and_replay=[DIVISION],
                       source_comparison_reused=True, source_comparison_executed_this_attempt=False,
                       original_archive={'path': str(ARCHIVE), 'bytes': ARCHIVE_SIZE, 'sha256': ARCHIVE_SHA,
                                         'source_comparison_paths': [f'evidence/original96-acceptance/attempt-002/{name}.log'
                                             for name in ('comparison-inputs', 'lean-source-outputs', 'python-source-comparison')]},
                       shared_providers=sorted(providers), owner_bindings=owners, records_sha256=sha(records_path))
        summary['audit'] = dict(original['audit'], modules={**original['audit']['modules'], **fresh['modules']})
        summary['owner_execution'] = {name: {'reused_from_attempt_002': name != DIVISION,
                                              'fresh_compile_audit_replay': name == DIVISION} for name in owners}
        (attempt / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
        archive = attempt / 'division-refresh.tar.xz'
        pack = {records_path, PRIVATE / 'audit' / audit_summary, *map(Path, proof_inputs),
                *(attempt.glob('*.log')), attempt/'commands.json', attempt/'summary.json'}
        for name, receipt in receipts.items():
            pack.update(map(Path, receipt['artifacts']))
            pack.update([Path(owners[name]['receipt'][0]), PRIVATE / 'audit' / name / 'latest.json', Path(records[name]['log'])])
        with tarfile.open(archive, 'w:xz') as tar:
            for path in sorted(pack):
                tar.add(path, arcname=str(path.relative_to(ROOT) if path.is_absolute() else path))
        print('P21_DIVISION_REFRESH ' + json.dumps({'status': summary['status'], 'attempt': str(attempt),
              'owned_declarations': len(names), 'union_owned_declarations': len(old_names | names),
              'fresh_compile_audit_replay': [DIVISION], 'source_comparison_reused': True,
              'source_comparison_executed_this_attempt': False, 'summary_sha256': sha(attempt/'summary.json')}), flush=True)
        print('P21_DIVISION_REFRESH_ARCHIVE ' + json.dumps({'path': str(archive),
              'bytes': archive.stat().st_size, 'sha256': sha(archive)}), flush=True)
        if archive.stat().st_size < 1200000:
            print('P21_DIVISION_REFRESH_ARCHIVE_BASE64 ' + base64.b64encode(archive.read_bytes()).decode(), flush=True)
    except Exception as error:
        (attempt / 'failure.json').write_text(json.dumps({'error': str(error)}) + '\n')
        raise


if __name__ == '__main__':
    main()
