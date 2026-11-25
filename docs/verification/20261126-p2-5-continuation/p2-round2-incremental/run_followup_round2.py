#!/usr/bin/env python3
"""Run the pinned second incremental P2 analytic round with unchanged gates."""
from pathlib import Path
import argparse
import base64
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess
import sys

ROOT = Path('/workspace/p2-saving16-20261125')
PREVIOUS_COMMIT = '59e552b5459f6c0b8852e02c037c00d34a86e32f'
BASELINE = Path('/workspace/p25-analytic-baseline-8657-20261125')
BASELINE_COMMIT = '8657cfffef159185f73c6a04ae4d31c846c0d0a9'
OLD = 'docs/verification/20261125-p2-5-saving16'
FOLDER = 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental'
RUNNER = FOLDER + '/run_followup_round2.py'
SNAPSHOT = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
SNAPSHOT_SHA = 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
MATHLIB = Path('/workspace/compile-deps/mathlib')
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
LEAN = '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean'
PINS = {
    'verification/part2/run_winner9_private_checks.py': 'f7816db16309f99b6f3babbe128425c06818b3da1dec556dffffe5e8132a6314',
    'verification/part2/run_winner9_private_audit.py': '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'verification/part2/winner9_private_audit_template.lean': '2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
    'verification/part2/winner9_external_snapshot.py': 'a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf',
    'verification/part2/inspect_winner9_owner_native.py': '28fbce08aa1adcc379ee592eda3760d2465b27e784cc735497d35b3658c9e464',
    'lean-toolchain': '62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef',
    'lake-manifest.json': '35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849',
    OLD + '/prepare-q96-original-inputs.py': 'f65108ecfb8b0274f1d2e730e13f29fde4f48fea028cae4fc985bc6a8940428e',
    OLD + '/p2-followup-repairs/run_followup.py': '5a93104eea7bcfc2f7f873c1ac667e0384c70ee3b517afa8eeef7259cefc392e',
    OLD + '/CONTINUATION_SOURCE_CLOSURE.json': '1374843ddd9c27e2eb588c0b5f102ec81d5e5d8ef08abd3a021a56fff3decb80',
    OLD + '/CONTINUATION_AUDIT_TARGETS.json': 'cb02b537ae86fb726deaa7bb832a797cb7b41ee4c536244626dd59ff6733a6c7',
    OLD + '/Q96_EXISTING_INPUTS_AND_SOURCES.json': '79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0',
    FOLDER + '/CONTINUATION_SOURCE_CLOSURE.json': '8f46282f610a6ead91f20d968d28e9a70fc11b389553eaf0ee7b9b3e3baa2139',
    FOLDER + '/CONTINUATION_AUDIT_TARGETS.json': '680ebbaac927dbe5a509a8e66d72794c8add7be6e6164460cd916afd6fdd3b50',
    FOLDER + '/SOURCE_SELECTION.json': 'a5fc037b54531183aa9ef70699b856a8c1e85eb7539ae2c28ef935276590b6e2',
}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def output(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def baseline_checks():
    assert output(['git', 'rev-parse', 'HEAD'], BASELINE) == BASELINE_COMMIT
    assert not output(['git', 'status', '--porcelain', '--untracked-files=no'], BASELINE)
    assert not (BASELINE / '.lake/build/lib/lean').exists()
    assert not list((ROOT / '.lake/p2-private/lib/ImbalancedChen').glob('P2Winner9CompleteSeedBlock[0-9][0-9].olean'))
    assert output(['git', 'rev-parse', 'HEAD'], MATHLIB) == MATHLIB_COMMIT
    assert sha(SNAPSHOT) == SNAPSHOT_SHA


def logged_call(command, path):
    with path.open('w') as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
        return process.wait()


def compile_summary(path):
    found = []
    for line in path.read_text().splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict) and 'successful_closure' in value and 'total' in value:
            found.append(value)
    return found[0] if len(found) == 1 else None


def accepted_summaries(compile_exit, audit_exit, compiled, audited, roots, targets):
    return bool(compile_exit == audit_exit == 0 and compiled and audited
        and compiled.get('roots') == roots and compiled.get('total') == 377
        and compiled.get('successful_closure') == 377 and compiled.get('complete') is True
        and compiled.get('status') == 'complete' and compiled.get('exit_code') == 0
        and compiled.get('failed_or_blocked') == [] and compiled.get('pending') == []
        and audited.get('requested') == audited.get('accepted') == len(targets) == 69
        and audited.get('all_accepted') is True
        and set(audited.get('modules', {})) == set(targets)
        and all(row.get('accepted') is True for row in audited['modules'].values()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication_commit')
    parser.add_argument('--prior-result-sha256')
    args = parser.parse_args()
    assert len(args.publication_commit) == 40 and all(c in '0123456789abcdef' for c in args.publication_commit)
    if args.prior_result_sha256 is not None:
        assert len(args.prior_result_sha256) == 64 and all(c in '0123456789abcdef' for c in args.prior_result_sha256)
    if sys.flags.optimize != 0:
        raise RuntimeError('Run without Python -O: all gate assertions must remain enabled')
    assert output(['git', 'rev-parse', 'HEAD']) == PREVIOUS_COMMIT
    assert not output(['git', 'status', '--porcelain', '--untracked-files=no'])
    subprocess.check_call(['git', 'merge-base', '--is-ancestor', PREVIOUS_COMMIT, args.publication_commit], cwd=ROOT)

    def published(path):
        return subprocess.check_output(['git', 'show', args.publication_commit + ':' + path], cwd=ROOT)

    assert Path(__file__).read_bytes() == published(RUNNER)
    for path, expected in PINS.items():
        assert hashlib.sha256(published(path)).hexdigest() == expected, path
        if not path.startswith(FOLDER + '/'):
            assert sha(ROOT / path) == expected, path
    prior_path = ROOT / '.lake/p25-followup-repairs-attempt001/RUN_RESULT.json'
    prior_raw = prior_path.read_bytes()
    prior_sha = hashlib.sha256(prior_raw).hexdigest()
    assert args.prior_result_sha256 is None or prior_sha == args.prior_result_sha256
    prior = json.loads(prior_raw)
    assert prior['source_commit'] == PREVIOUS_COMMIT and prior.get('ended_utc') and 'audit_exit' in prior, 'Previous round must finish first'
    assert prior['project_modules'] == 377 and prior['owned_targets'] == 67
    assert prior['runner_sha256'] == PINS[OLD + '/p2-followup-repairs/run_followup.py']
    old_graph = json.loads((ROOT / OLD / 'CONTINUATION_SOURCE_CLOSURE.json').read_text())
    graph = json.loads(published(FOLDER + '/CONTINUATION_SOURCE_CLOSURE.json'))
    target_document = json.loads(published(FOLDER + '/CONTINUATION_AUDIT_TARGETS.json'))
    targets = target_document['modules']
    selection = json.loads(published(FOLDER + '/SOURCE_SELECTION.json'))
    old_targets = json.loads((ROOT / OLD / 'CONTINUATION_AUDIT_TARGETS.json').read_text())['modules']
    assert graph['roots'] == old_graph['roots'] and len(graph['roots']) == 5
    assert set(graph['modules']) == set(old_graph['modules']) and len(graph['modules']) == graph['project_modules'] == 377
    assert len(targets) == len(set(targets)) == target_document['count'] == 69
    assert set(targets) == set(old_targets) | set(selection['added_owned_targets'])
    assert len(old_targets) == 67 and len(selection['added_owned_targets']) == 2
    assert all(name in graph['modules'] for name in targets)
    sys.path.insert(0, str(ROOT / 'verification/part2'))
    from inspect_winner9_owner_native import imports
    from winner9_external_snapshot import ExternalSnapshot

    def project_imports(path):
        return [name for name in imports(path.read_text()) if name.startswith('ImbalancedChen.')]

    changes = []
    for name, row in old_graph['modules'].items():
        assert sha(ROOT / row['source']) == row['sha256'], name
        assert project_imports(ROOT / row['source']) == row['imports'], name
        new = graph['modules'][name]
        assert row['source'] == new['source'] and row['imports'] == new['imports'], name
        if row['sha256'] != new['sha256']:
            changes.append({'module': name, 'source': row['source'], 'before_sha256': row['sha256'], 'after_sha256': new['sha256']})
    assert changes == selection['changed_sources'] and len(changes) == 6
    baseline_checks()
    external = ExternalSnapshot(SNAPSHOT, lean=LEAN, mathlib_pin=MATHLIB_COMMIT, project_lib=ROOT / '.lake/p2-private/lib')
    external_before = external.verify()
    recovery = ROOT / '.lake/p25-unused-cache-reclamation-second-recovery.json'
    setup = ROOT / '.lake/p25-empty-baseline-setup.json'
    recovered = json.loads(recovery.read_text())
    assert recovered['deleted_duplicate_files_still_absent'] and len(recovered['originals_fully_rehashed_now']) == 44
    records = ROOT / '.lake/p2-private/records.json'
    raw = records.read_bytes()
    json.loads(raw)
    out = ROOT / '.lake/p25-followup-repairs-attempt002'
    out.mkdir(parents=True, exist_ok=False)
    (out / 'previous-records.json.gz').write_bytes(gzip.compress(raw, mtime=0))
    previous = {'source_commit': PREVIOUS_COMMIT, 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(), 'compressed_sha256': sha(out / 'previous-records.json.gz')}
    assert sha(records) == previous['sha256'] and sha(prior_path) == prior_sha
    (out / 'PREVIOUS_RECORDS.json').write_text(json.dumps(previous, indent=2) + '\n')
    (out / 'PRIOR_RUN_RESULT.json').write_bytes(prior_raw)
    for path in [recovery, setup]:
        (out / path.name).write_bytes(path.read_bytes())
    subprocess.check_call(['git', 'checkout', '--detach', args.publication_commit], cwd=ROOT)
    for path, expected in PINS.items():
        assert sha(ROOT / path) == expected, path
    assert sha(ROOT / RUNNER) == sha(__file__)
    for name, row in graph['modules'].items():
        assert sha(ROOT / row['source']) == row['sha256'], name
        assert project_imports(ROOT / row['source']) == row['imports'], name
    baseline_checks()
    assert external.verify() == external_before
    compile_roots = graph['roots']
    priority = [row['module'] for row in changes]
    ordered = priority + [name for name in targets if name not in priority]
    assert len(ordered) == 69 and set(ordered) == set(targets)
    state = {'schema': 'p25-round2-pinned-compile-and-owned-audit-v1',
             'source_commit': args.publication_commit, 'previous_commit': PREVIOUS_COMMIT,
             'source_tree': output(['git', 'rev-parse', 'HEAD^{tree}']), 'runner_sha256': sha(__file__),
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'prior_run_result_sha256': prior_sha, 'prior_result_pin_supplied': args.prior_result_sha256 is not None,
             'baseline_root': str(BASELINE), 'baseline_commit': BASELINE_COMMIT, 'baseline_has_build_objects': False,
             'mathlib_commit': MATHLIB_COMMIT, 'external_before': external_before,
             'project_modules': 377, 'owned_targets': 69, 'compile_roots': compile_roots,
             'source_and_gate_pins': PINS, 'external_snapshot_sha256': sha(SNAPSHOT),
             'disk_free_start': shutil.disk_usage(ROOT).free,
             'scope': selection['scope'], 'accepted': False, 'finite_guard_credit': False, 'P2_5_proved': False}
    receipt = out / 'RUN_RESULT.json'

    def save():
        temporary = receipt.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(state, indent=2) + '\n')
        temporary.replace(receipt)

    save()
    assert state['disk_free_start'] >= 1073741824
    with (out / 'INPUT_PREPARATION.log').open('w') as log:
        state['input_preparation_exit'] = subprocess.call([sys.executable, str(ROOT / OLD / 'prepare-q96-original-inputs.py')], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    save()
    assert state['input_preparation_exit'] == 0
    command = [sys.executable, 'verification/part2/run_winner9_private_checks.py', *compile_roots,
               '--baseline-root', str(BASELINE), '--workers', '1', '--threads', '1', '--memory-mb', '11264',
               '--external-snapshot', str(SNAPSHOT), '--time-budget-seconds', '1400']
    state['compile_command'] = command
    save()
    state['compile_exit'] = logged_call(command, out / 'COMPILE.log')
    state['compile_summary'] = compile_summary(out / 'COMPILE.log')
    state['compile_log_sha256'] = sha(out / 'COMPILE.log')
    save()
    baseline_checks()
    summary_name = 'p25-round2-repairs-owned-audit.json'
    command = [sys.executable, 'verification/part2/run_winner9_private_audit.py', *ordered,
               '--summary-name', summary_name, '--memory-mb', '11264', '--external-snapshot', str(SNAPSHOT)]
    state['audit_command'] = command
    save()
    state['audit_exit'] = logged_call(command, out / 'AUDIT.log')
    summary = ROOT / '.lake/p2-private/audit' / summary_name
    state['audit_summary'] = json.loads(summary.read_text()) if summary.is_file() else None
    state['audit_log_sha256'] = sha(out / 'AUDIT.log')
    save()
    baseline_checks()
    state['external_after'] = external.verify()
    state['source_after_matches'] = all(sha(ROOT / row['source']) == row['sha256'] and project_imports(ROOT / row['source']) == row['imports'] for row in graph['modules'].values())
    state['gate_after_matches'] = all(sha(ROOT / path) == expected for path, expected in PINS.items()) and sha(ROOT / RUNNER) == state['runner_sha256']
    state['snapshot_after_matches'] = sha(SNAPSHOT) == SNAPSHOT_SHA and state['external_after'] == external_before
    state['head_after_matches'] = output(['git', 'rev-parse', 'HEAD']) == args.publication_commit and not output(['git', 'status', '--porcelain', '--untracked-files=no'])
    state['prior_result_after_matches'] = sha(prior_path) == prior_sha
    state['baseline_after_matches'] = True
    state['accepted'] = accepted_summaries(state['compile_exit'], state['audit_exit'], state['compile_summary'], state['audit_summary'], compile_roots, targets) and all(state[key] for key in ['source_after_matches', 'gate_after_matches', 'snapshot_after_matches', 'head_after_matches', 'prior_result_after_matches', 'baseline_after_matches'])
    state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    state['disk_free_end'] = shutil.disk_usage(ROOT).free
    save()
    print('P25_ROUND2_RESULT ' + json.dumps(state), flush=True)
    paths = [receipt, out / 'PREVIOUS_RECORDS.json', out / 'PRIOR_RUN_RESULT.json', out / recovery.name, out / setup.name, summary]
    paths += [ROOT / '.lake/p2-private/audit' / name / 'latest.json' for name in ordered]
    manifest, included, omitted = [], [], []
    used = 0
    for path in paths:
        if not path.is_file():
            continue
        raw = path.read_bytes()
        row = {'path': str(path.relative_to(ROOT)), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
        manifest.append(row)
        if used + len(raw) <= 500000:
            included.append(dict(row, data_base64=base64.b64encode(raw).decode()))
            used += len(raw)
        else:
            omitted.append(row)
    print('P25_ROUND2_EXPORT_JSON ' + json.dumps({'source_commit': args.publication_commit, 'manifest': manifest, 'included_files': included, 'unexported_files': omitted}, separators=(',', ':')), flush=True)
    return 0 if state['accepted'] else 1


if __name__ == '__main__':
    sys.exit(main())
