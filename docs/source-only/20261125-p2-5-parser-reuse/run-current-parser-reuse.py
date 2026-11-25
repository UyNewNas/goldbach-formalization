#!/usr/bin/env python3
"""Compile/replay/audit the existing representation helpers, without witness data."""
from pathlib import Path
import argparse
import base64
import datetime
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path('/workspace/p25-q96-20261125')
BASELINE = Path('/workspace/p25-q96-baseline-8657')
MATHLIB = Path('/mathlib')
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
PACKAGE = 'docs/source-only/20261125-p2-5-parser-reuse'
PARSER = 'ImbalancedChen.P2OriginalSaving19SourceJson'
ROOTS = ['ImbalancedChen.P2OriginalSaving19CharInputBridge',
         'ImbalancedChen.P2OriginalSaving19SourceJsonCharInput',
         'ImbalancedChen.P2OriginalSaving19PackedChars']


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()


def output(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('publication_commit')
    args.add_argument('previous_commit')
    args.add_argument('--attempt', type=int, default=1)
    options = args.parse_args()
    for value in [options.publication_commit, options.previous_commit]:
        require(len(value) == 40 and all(c in '0123456789abcdef' for c in value),
                'Expected full lowercase commit SHA')
    require(1 <= options.attempt <= 999, 'Invalid attempt number')
    out = ROOT / f'.lake/p25-parser-reuse/attempt-{options.attempt:03d}'
    require(not out.exists(), 'Attempt exists; inspect its records before any retry')
    out.mkdir(parents=True)
    receipt = out / 'RESULT.json'
    state = {'schema': 'p25-existing-representation-current-parser-verification-v1',
             'accepted': False, 'status': 'PREPARING',
             'publication_commit': options.publication_commit,
             'previous_commit': options.previous_commit,
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'scope': 'Only the four-module representation-helper closure. No witness is read, no concrete String binding or whole parse is proved, and no Q96 or P2.5 completion follows.',
             'runner_sha256': sha(__file__)}

    def save():
        temporary = receipt.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
        temporary.replace(receipt)

    save()
    try:
        require(output(['git', 'rev-parse', 'HEAD']) in
                [options.previous_commit, options.publication_commit],
                'Unexpected task worktree HEAD')
        require(not output(['git', 'status', '--porcelain', '--untracked-files=no']),
                'Tracked task worktree is dirty')
        subprocess.check_call(['git', 'merge-base', '--is-ancestor',
                               options.previous_commit, options.publication_commit], cwd=ROOT)
        published_runner = subprocess.check_output(
            ['git', 'show', options.publication_commit + ':' + PACKAGE + '/run-current-parser-reuse.py'], cwd=ROOT)
        require(hashlib.sha256(published_runner).hexdigest() == state['runner_sha256'],
                'Executing runner differs from the published source')
        subprocess.check_call(['git', 'checkout', '--detach', options.publication_commit], cwd=ROOT)
        os.chdir(ROOT)
        graph_path = Path(PACKAGE) / 'SOURCE_CLOSURE.json'
        graph = json.loads(graph_path.read_text())
        require(graph['roots'] == ROOTS and graph['project_module_count'] == 4,
                'Unexpected helper closure')
        require(set(graph['modules']) == set(ROOTS + [PARSER]), 'Unexpected project modules')
        before = {name: sha(row['path']) for name, row in graph['modules'].items()}
        require(all(before[name] == row['sha256'] for name, row in graph['modules'].items()),
                'Published source map differs from files')
        require(before[PARSER] == 'd58e22ba7e2d92b6c9f2d139993361ae9b827d25d6869fcf38f3837ba7bc3d02',
                'Accepted current parser changed')
        require(output(['git', 'rev-parse', 'HEAD'], BASELINE) ==
                '8657cfffef159185f73c6a04ae4d31c846c0d0a9', 'Baseline pin differs')
        require(not (BASELINE / '.lake/build/lib/lean').exists(), 'Unexpected baseline objects')
        require(output(['git', 'rev-parse', 'HEAD'], MATHLIB) ==
                'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1', 'Mathlib pin differs')
        require(Path('/workspace/compile-deps/mathlib').resolve() == MATHLIB.resolve(),
                'Mathlib alias differs')
        require(sha(LEAN) == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
                'Lean binary differs')
        require(sha(LEAN.with_name('leanchecker')) ==
                'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a',
                'Kernel replay binary differs')
        paths = ['/mathlib/.lake/build/lib/lean'] + [
            f'/mathlib/.lake/packages/{p}/.lake/build/lib/lean'
            for p in ['plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets', 'aesop', 'Qq', 'batteries']]
        require(all(Path(p).is_dir() for p in paths), 'Approved package path is missing')
        env = dict(os.environ)
        env['LEAN_PATH'] = ':'.join(paths)
        local_options = {name: [line for line in Path(row['path']).read_text().splitlines()
                               if line.startswith('set_option ')]
                         for name, row in graph['modules'].items()}
        state.update(source_tree=output(['git', 'rev-parse', 'HEAD^{tree}']),
                     source_before=before, source_map_sha256=sha(graph_path),
                     source_local_options=local_options,
                     resource_note='CLI uses M11264 and maxRecDepth50000. The repaired PackedChars module retains donor options and locally uses maxRecDepth1000000, Elab.async=false and stderrAsMessages=false; these options do not propagate into consumers. This run contains no large-input closed guard.',
                     approved_LEAN_PATH=env['LEAN_PATH'], status='COMPILING')
        compile_command = [sys.executable, 'verification/part2/run_winner9_private_checks.py',
                           *ROOTS, '--baseline-root', str(BASELINE), '--workers', '1',
                           '--threads', '1', '--memory-mb', '11264', '--time-budget-seconds', '200']
        state['compile_command'] = compile_command
        save()
        state['compile_exit'] = subprocess.call(compile_command, cwd=ROOT, env=env)
        state['status'] = 'REPLAY_AND_COMPLETE_OWNED_AUDIT'
        save()
        audit_command = [sys.executable, 'verification/part2/run_winner9_private_audit.py',
                         *graph['topological_order'], '--summary-name',
                         'p25-parser-reuse-owned-audit.json', '--memory-mb', '11264']
        state['audit_command'] = audit_command
        state['audit_exit'] = subprocess.call(audit_command, cwd=ROOT, env=env)
        summary = ROOT / '.lake/p2-private/audit/p25-parser-reuse-owned-audit.json'
        state['audit_summary'] = json.loads(summary.read_text()) if summary.exists() else None
        state['source_after'] = {name: sha(row['path']) for name, row in graph['modules'].items()}
        state['accepted'] = bool(state['compile_exit'] == 0 and state['audit_exit'] == 0
                                 and state['source_after'] == before and state['audit_summary']
                                 and state['audit_summary'].get('all_accepted'))
        state['status'] = 'HELPER_CLOSURE_ACCEPTED' if state['accepted'] else 'HELPER_CLOSURE_NOT_ACCEPTED'
        return 0 if state['accepted'] else 1
    except Exception as error:
        state['status'] = 'PRECONDITION_OR_BINDING_FAILED'
        state['error'] = str(error)
        print('P25_PARSER_REUSE_ERROR ' + str(error), flush=True)
        return 1
    finally:
        state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()
        print('P25_PARSER_REUSE_RESULT ' + json.dumps(state), flush=True)
        print('P25_PARSER_REUSE_RECEIPT ' + str(receipt) + ' ' + sha(receipt), flush=True)


if __name__ == '__main__':
    sys.exit(main())
