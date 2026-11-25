#!/usr/bin/env python3
"""Continue the pinned P2.5 closure using the unchanged compiler and audit gates."""
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
PREVIOUS_COMMIT = '8ca72929b39e77d86297fd370d02da36860b312b'
BASELINE = Path('/workspace/p25-analytic-baseline-8657-20261125')
BASELINE_COMMIT = '8657cfffef159185f73c6a04ae4d31c846c0d0a9'
FOLDER = 'docs/verification/20261125-p2-5-saving16'
RUNNER = FOLDER + '/p2-followup-repairs/run_followup.py'
SNAPSHOT = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
PINS = {
    'verification/part2/run_winner9_private_checks.py': 'f7816db16309f99b6f3babbe128425c06818b3da1dec556dffffe5e8132a6314',
    'verification/part2/run_winner9_private_audit.py': '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'verification/part2/winner9_private_audit_template.lean': '2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
    FOLDER + '/CONTINUATION_SOURCE_CLOSURE.json': '1374843ddd9c27e2eb588c0b5f102ec81d5e5d8ef08abd3a021a56fff3decb80',
    FOLDER + '/CONTINUATION_AUDIT_TARGETS.json': 'cb02b537ae86fb726deaa7bb832a797cb7b41ee4c536244626dd59ff6733a6c7',
    FOLDER + '/Q96_EXISTING_INPUTS_AND_SOURCES.json': '79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0',
}
PRIORITY = ['ImbalancedChen.' + name for name in [
    'P4AOriginalRemainingEighthSources', 'P4AUpperTaggedParityCompiler',
    'P4AOriginalFirstFailureH3SourceSemantics', 'P4ASlot9InheritedActualAction',
    'P1OriginalCoarseContinuationCells', 'P1HistoricalCapCeilingCheck',
    'P4AOriginalHistoricalFifthSelectedSlotBridge', 'P1HistoricalFifthJointIntegralSign',
    'P1ActualUpperClosedParameterUniformity', 'P1HistoricalFourthFullCellIntegral',
    'P2OriginalSaving19SourceMeasure']]


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def output(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication_commit')
    parser.add_argument('previous_commit')
    args = parser.parse_args()
    for value in [args.publication_commit, args.previous_commit]:
        assert len(value) == 40 and all(c in '0123456789abcdef' for c in value)
    assert args.previous_commit == PREVIOUS_COMMIT
    assert output(['git', 'rev-parse', 'HEAD']) == PREVIOUS_COMMIT
    assert not output(['git', 'status', '--porcelain', '--untracked-files=no'])
    subprocess.check_call(['git', 'merge-base', '--is-ancestor', args.previous_commit,
                           args.publication_commit], cwd=ROOT)

    def published(path):
        return subprocess.check_output(['git', 'show', args.publication_commit + ':' + path], cwd=ROOT)

    assert Path(__file__).read_bytes() == published(RUNNER)
    for path, expected in PINS.items():
        assert hashlib.sha256(published(path)).hexdigest() == expected, path
    assert sha(SNAPSHOT) == 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
    assert output(['git', 'rev-parse', 'HEAD'], BASELINE) == BASELINE_COMMIT
    assert not output(['git', 'status', '--porcelain', '--untracked-files=no'], BASELINE)
    assert not (BASELINE / '.lake/build/lib/lean').exists()
    assert not list((ROOT / '.lake/p2-private/lib/ImbalancedChen').glob('P2Winner9CompleteSeedBlock[0-9][0-9].olean'))
    recovery = ROOT / '.lake/p25-unused-cache-reclamation-second-recovery.json'
    setup = ROOT / '.lake/p25-empty-baseline-setup.json'
    recovered = json.loads(recovery.read_text())
    assert recovered['deleted_duplicate_files_still_absent'] and len(recovered['originals_fully_rehashed_now']) == 44
    records = ROOT / '.lake/p2-private/records.json'
    assert sha(records) == '939901a3e66ea7f5b233b48b73e20b72fbe7a878afeefb8165a2558a3e3a9d93'
    json.loads(records.read_bytes())
    out = ROOT / '.lake/p25-followup-repairs-attempt001'
    assert not out.exists()
    out.mkdir(parents=True)
    raw = records.read_bytes()
    (out / 'previous-records.json.gz').write_bytes(gzip.compress(raw, mtime=0))
    previous = {'source_commit': args.previous_commit, 'bytes': len(raw),
                'sha256': hashlib.sha256(raw).hexdigest(),
                'compressed_sha256': sha(out / 'previous-records.json.gz')}
    (out / 'PREVIOUS_RECORDS.json').write_text(json.dumps(previous, indent=2) + '\n')
    for path in [recovery, setup]:
        (out / path.name).write_bytes(path.read_bytes())
    subprocess.check_call(['git', 'checkout', '--detach', args.publication_commit], cwd=ROOT)
    for path, expected in PINS.items():
        assert sha(ROOT / path) == expected, path
    graph = json.loads((ROOT / FOLDER / 'CONTINUATION_SOURCE_CLOSURE.json').read_text())
    targets = json.loads((ROOT / FOLDER / 'CONTINUATION_AUDIT_TARGETS.json').read_text())['modules']
    assert len(graph['modules']) == graph['project_modules'] == 377 and len(targets) == 67
    for name, row in graph['modules'].items():
        assert sha(ROOT / row['source']) == row['sha256'], name
    assert all(name in graph['modules'] for name in PRIORITY + targets)
    compile_roots = list(dict.fromkeys(PRIORITY + graph['roots']))
    ordered = PRIORITY + [name for name in targets if name not in PRIORITY]
    state = {'schema': 'p25-followup-pinned-compile-and-owned-audit-v1',
             'source_commit': args.publication_commit, 'previous_commit': args.previous_commit,
             'source_tree': output(['git', 'rev-parse', 'HEAD^{tree}']),
             'runner_sha256': sha(__file__), 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'baseline_root': str(BASELINE), 'baseline_commit': BASELINE_COMMIT,
             'baseline_has_build_objects': False, 'project_modules': 377,
             'owned_targets': 67, 'compile_roots': compile_roots,
             'source_and_gate_pins': PINS, 'external_snapshot_sha256': sha(SNAPSHOT),
             'disk_free_start': shutil.disk_usage(ROOT).free,
             'scope': 'Current analytic dependency closure only. No finite data guard, original input binding, full Q96 certificate or P2.5 endpoint acceptance is asserted.',
             'accepted': False, 'P2_5_proved': False}
    receipt = out / 'RUN_RESULT.json'

    def save():
        temporary = receipt.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(state, indent=2) + '\n')
        temporary.replace(receipt)

    save()
    assert state['disk_free_start'] >= 1073741824
    with (out / 'INPUT_PREPARATION.log').open('w') as log:
        state['input_preparation_exit'] = subprocess.call(
            [sys.executable, str(ROOT / FOLDER / 'prepare-q96-original-inputs.py')],
            cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    save()
    assert state['input_preparation_exit'] == 0
    command = [sys.executable, 'verification/part2/run_winner9_private_checks.py',
               *compile_roots, '--baseline-root', str(BASELINE), '--workers', '1',
               '--threads', '1', '--memory-mb', '11264', '--external-snapshot', str(SNAPSHOT),
               '--time-budget-seconds', '1400']
    state['compile_command'] = command
    save()
    state['compile_exit'] = subprocess.call(command, cwd=ROOT)
    save()
    assert not (BASELINE / '.lake/build/lib/lean').exists()
    assert not list((ROOT / '.lake/p2-private/lib/ImbalancedChen').glob('P2Winner9CompleteSeedBlock[0-9][0-9].olean'))
    command = [sys.executable, 'verification/part2/run_winner9_private_audit.py',
               *ordered, '--summary-name', 'p25-followup-repairs-owned-audit.json',
               '--memory-mb', '11264', '--external-snapshot', str(SNAPSHOT)]
    state['audit_command'] = command
    save()
    state['audit_exit'] = subprocess.call(command, cwd=ROOT)
    summary = ROOT / '.lake/p2-private/audit/p25-followup-repairs-owned-audit.json'
    state['audit_summary'] = json.loads(summary.read_text()) if summary.is_file() else None
    state['source_after_matches'] = all(sha(ROOT / row['source']) == row['sha256'] for row in graph['modules'].values())
    state['gate_after_matches'] = all(sha(ROOT / path) == expected for path, expected in PINS.items())
    state['snapshot_after_matches'] = sha(SNAPSHOT) == state['external_snapshot_sha256']
    state['head_after_matches'] = output(['git', 'rev-parse', 'HEAD']) == args.publication_commit and not output(['git', 'status', '--porcelain', '--untracked-files=no'])
    state['accepted'] = bool(state['compile_exit'] == state['audit_exit'] == 0 and state['source_after_matches'] and state['gate_after_matches'] and state['snapshot_after_matches'] and state['head_after_matches'] and state['audit_summary'] and state['audit_summary'].get('all_accepted'))
    state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    state['disk_free_end'] = shutil.disk_usage(ROOT).free
    save()
    print('P25_FOLLOWUP_RESULT ' + json.dumps(state), flush=True)
    paths = [receipt, out / 'PREVIOUS_RECORDS.json', out / recovery.name, out / setup.name, summary]
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
    print('P25_FOLLOWUP_EXPORT_JSON ' + json.dumps({'source_commit': args.publication_commit,
          'manifest': manifest, 'included_files': included, 'unexported_files': omitted}, separators=(',', ':')), flush=True)
    return 0 if state['accepted'] else 1


if __name__ == '__main__':
    sys.exit(main())
