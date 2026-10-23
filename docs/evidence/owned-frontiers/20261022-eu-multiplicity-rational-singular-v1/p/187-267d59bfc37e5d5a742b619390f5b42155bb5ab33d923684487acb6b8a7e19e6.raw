"""Replay and completely inventory a small frozen batch of owned modules.

Claims only the defining modules and their actual transitive axiom sets. It is
not an external-import closure replay, aggregate build, or main theorem claim.
"""
from pathlib import Path
import datetime
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
import subprocess
import time

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]
OLD = Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-integration/.lake/takeover-p0')
TARGETS = {
    'ImbalancedChen.CurrentChenUpsilon6KernelBuffer': 'e1be094adfdaf863cfbd15c273d04c2b5d2da120f21dcf9dd81cf15be86af51d',
    'ImbalancedChen.CurrentChenPairLevelGeometry': '2ddd43d70fe1a94474acfabc92998e240be630feac91904e5ff4b0f0861116d6',
}


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    global TARGETS
    parser = argparse.ArgumentParser()
    parser.add_argument('--target', action='append', help='Module.Name=FrozenSHA256')
    parser.add_argument('--memory-mib', type=int, choices=(4096, 6144), default=4096)
    parser.add_argument('--rss-limit-mib', type=int)
    parser.add_argument('--resource-reason')
    args = parser.parse_args()
    if args.target:
        TARGETS = dict(item.split('=', 1) for item in args.target)
    runtime = load('proof_runtime', STATE / 'runtime.py')
    guard = load('owned_checker_guard', ROOT.parent / 'goldbach-integration/verification/parts/takeover-p0/checker_memory_guard.py')
    rt = runtime.Runtime(ROOT, memory_mib=args.memory_mib, rss_limit_mib=args.rss_limit_mib,
                         resource_reason=args.resource_reason)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out = STATE / 'audits' / stamp
    out.mkdir(parents=True)
    report = {'status': 'RUNNING', 'targets': TARGETS, 'stages': [],
              'audit_runner_sha256': runtime.sha(__file__),
              'scope': 'Owned stock replay and complete serialized/type/axiom census only',
              'external_closure_replay_claimed': False, 'unconditional_main_claimed': False}
    receipt = out / 'receipt.json'
    def save():
        receipt.write_text(json.dumps(report, indent=2) + '\n')
    def snapshot():
        return {'pins': rt.pins(), 'sources': {m: runtime.sha(rt.paths(m)[0]) for m in TARGETS},
                'owned_object_parts': {m: rt.parts(rt.paths(m)[1]) for m in TARGETS},
                'lean_real_sha256': runtime.sha(runtime.BIN / 'lean.real'),
                'checker_sha256': runtime.sha(runtime.BIN / 'leanchecker')}
    try:
        with (OLD / 'locks/compiler-0.lock').open('a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            rt.heavy_lock_fd = lock.fileno()
            before = snapshot()
            assert before['sources'] == TARGETS
            report['inputs_before'] = before
            save()
            for module in TARGETS:
                obj = rt.paths(module)[1]
                assert obj.is_file()
                for directory in [rt.build, *[runtime.PROVIDERS / p['name'] / '.lake/build/lib/lean' for p in rt.packages], runtime.BIN.parent / 'lib/lean']:
                    prefix = directory / module.replace('.', '/')
                    assert not prefix.is_dir() or not list(prefix.rglob('*.olean')), 'Checker prefix would select descendants'
                command = [str(runtime.BIN / 'leanchecker'), '--verbose', module]
                if rt.rss_limit_mib is None:
                    result = guard.run_checker_guarded(command, cwd=ROOT, env=rt.environment(),
                        log_path=out / ('replay-' + module + '.log'), receipt_path=out / ('replay-' + module + '.json'))
                else:
                    result = {'status': 'RUNNING', 'command': command, 'resource_reason': rt.resource_reason}
                    checker_receipt = out / ('replay-' + module + '.json')
                    start = time.monotonic()
                    checker_log = out / ('replay-' + module + '.log')
                    with checker_log.open('wb') as stream:
                        code, usage, stopped, error = rt.run_owned_lean(command, cwd=ROOT, log=stream,
                            record=result, receipt=checker_receipt)
                    result.update(status='GUARD_ERROR' if error else 'RESOURCE_STOP' if stopped else 'PASS' if code == 0 else 'FAILED',
                                  returncode=code, max_rss_kib=usage.ru_maxrss, guard_error=error,
                                  seconds=round(time.monotonic() - start, 3), log_sha256=runtime.sha(checker_log))
                    checker_receipt.write_text(json.dumps(result, indent=2) + '\n')
                report['stages'].append({'kind': 'stock_replay', 'module': module, 'result': result})
                save()
                assert result['status'] == 'PASS', 'Stock replay resource/failure: ' + module
            template = (ROOT / 'verification/parts/p0/queue/AuditTemplate.lean').read_text()
            first, body = template.split('open Lean Elab Command in', 1)
            first = first.replace('import TARGET_IMPORT', '\n'.join('import ' + m for m in TARGETS))
            source = first + '\n'
            for module in TARGETS:
                source += 'open Lean Elab Command in' + body.replace('TARGET_NAME', module) + '\n'
            audit = out / 'OwnedAudit.lean'
            audit.write_text(source)
            report['generated_audit_sha256'] = runtime.sha(audit)
            command = [str(runtime.BIN / 'lean'), '-j2', '-M' + str(rt.memory_mib), '-DwarningAsError=true', str(audit.relative_to(ROOT))]
            started = time.monotonic()
            log = out / 'declarations.log'
            with log.open('wb') as stream:
                audit_record = {'status': 'RUNNING', 'command': command, 'resource_reason': rt.resource_reason}
                code, usage, stopped, error = rt.run_owned_lean(command, cwd=ROOT, log=stream,
                    record=audit_record, receipt=out / 'audit-process.json')
                audit_record.update(status='GUARD_ERROR' if error else 'RESOURCE_STOP' if stopped else 'PASS' if code == 0 else 'FAILED',
                                    returncode=code, max_rss_kib=usage.ru_maxrss, guard_error=error)
                (out / 'audit-process.json').write_text(json.dumps(audit_record, indent=2) + '\n')
            report.pop('active_child', None)
            report['stages'].append({'kind': 'full_inventory_type_axioms', 'exit_code': code,
                'seconds': round(time.monotonic() - started, 3), 'max_rss_kib': usage.ru_maxrss,
                'log_sha256': runtime.sha(log), 'command': command})
            save()
            assert code == 0 and not stopped and error is None, 'Owned census command failed'
            inventories = {}
            declarations = {}
            for line in log.read_text().splitlines():
                if line.startswith('P0_QUEUE_INVENTORY '):
                    row = json.loads(line.split(' ', 1)[1])
                    assert row['module'] not in inventories
                    inventories[row['module']] = row
                elif line.startswith('P0_QUEUE_DECL '):
                    row = json.loads(line.split(' ', 1)[1])
                    assert row['name'] not in declarations
                    assert row['module'] in TARGETS
                    assert not row['unsafe'] and not row['partial'] and not row['axiom']
                    assert set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
                    assert row['type'] and '⋯' not in row['type']
                    declarations[row['name']] = row
            assert set(inventories) == set(TARGETS)
            for module, inv in inventories.items():
                names = {n for n, row in declarations.items() if row['module'] == module}
                assert len(inv['serialized']) == len(set(inv['serialized'])) > 0
                assert names == set(inv['serialized']) == set(inv['environment'])
            after = snapshot()
            report['inputs_after'] = after
            assert before == after
            (out / 'declarations.json').write_text(json.dumps(list(declarations.values()), indent=2) + '\n')
            report.update(status='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS',
                          declaration_counts={m: len(inv['serialized']) for m, inv in inventories.items()},
                          source_template_sha256=runtime.sha(ROOT / 'verification/parts/p0/queue/AuditTemplate.lean'))
            save()
    except BaseException as error:
        report.update(status='INCOMPLETE', error=f'{type(error).__name__}: {error}')
        save()
        print(json.dumps({'receipt': str(receipt), 'status': report['status'], 'error': report['error']}), flush=True)
        raise
    print(json.dumps({'receipt': str(receipt), 'status': report['status'], 'declaration_counts': report['declaration_counts']}), flush=True)


if __name__ == '__main__':
    main()
