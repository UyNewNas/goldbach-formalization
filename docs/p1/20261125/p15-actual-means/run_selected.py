#!/usr/bin/env python3
"""Validate and compile explicitly selected P1.5 owners on the existing member lane."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-p15-actual-means-v1')
API = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
TARGETS = tuple('ImbalancedChen.' + name for name in """
P1ActualVariableFifthGlobalPositiveLimit
P1OriginalFifthMiddleShellFiniteBudget
P1OriginalFifthMovingScaleLimit
P1OriginalFourthUntruncatedIntegral
P1OriginalVariableFourthActiveMeshCover
P1OriginalVariableFourthFullActivePositiveLimit
P1FifthMiddleNormalizedPointwise
P1OriginalFifthMiddleShellMovingLimit
P1OriginalVariableFourthFullSmallSource
P1OriginalVariableFourthUntruncatedDomination
P1ActualVariableFifthSmallLastGeometry
P1OriginalFifthMiddleShellRemainderSplit
P1OriginalVariableFourthFullActiveIntegral
P1OriginalVariableFourthFullSmallRemainder
P1OriginalVariableFourthFullSourceAssembly
P1ActualVariableFifthTailPointwise
P1OriginalFifthUniformSmallRemainder
P1OriginalVariableFourthFullSourceMean
P1ActualVariableFifthUniformTail
P1OriginalFifthZeroCutoffLimit
P1OriginalFifthUntruncatedIntegral
P1ActualVariableFifthUntruncatedDomination
P1ActualVariableFifthFullMean
""".split())
FOURTH = 'ImbalancedChen.P1OriginalVariableFourthFullSourceMean'
FIFTH = 'ImbalancedChen.P1ActualVariableFifthFullMean'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def selection(requested):
    require(requested and len(requested) == len(set(requested)), 'specify unique targets')
    unknown = set(requested) - set(TARGETS)
    require(not unknown, 'outside the 23-owner selection: ' + ', '.join(sorted(unknown)))
    return [m for m in TARGETS if m in requested]


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def pinned(commit, path, digest):
    raw = git_file(commit, path)
    require(hashlib.sha256(raw).hexdigest() == digest, 'published pin differs: ' + path)
    return raw


def helpers():
    raw = pinned(API_COMMIT, API, API_SHA)
    api = ModuleType('published_batch13')
    api.__file__ = API
    exec(compile(raw, API, 'exec'), api.__dict__)
    require((api.REPO, api.PROJECT, api.TOOLS) == (REPO, PROJECT, TOOLS), 'unexpected helper environment')
    code = {p: pinned(TOOLS, p, sha) for p, sha in api.PINS.items()}
    return SimpleNamespace(api=api, h=api.load(code[api.HELPER], 'batch5'),
                           ops=api.load(code[api.OPS], 'batch6'),
                           d=api.load(code[api.PRIMITIVES], 'primitives'), e9=code[api.E9])


def file_binding(path):
    require(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(s, modules, review):
    h, d = s.h, s.d
    configs = review['runtime_configuration_bindings']
    configuration = {p: d.fingerprint(PROJECT / p) for p in configs}
    require(configuration == configs and not os.path.lexists(PROJECT / 'lakefile.lean') and
            not any((PROJECT / p).is_symlink() for p in configs), 'runtime configuration differs')
    runtime = d.runtime_binding(h)
    require(runtime == review['existing_runtime_bindings'], 'runtime binding differs')
    protected = {m: file_binding(PROJECT / h.module_path(m)) for m in h.FOUR_ROOTS}
    require(protected == h.FOUR_ROOTS, 'protected original roots differ')
    return {'project_sources': {m: file_binding(PROJECT / h.module_path(m)) for m in modules},
            'protected_roots': protected, 'configuration': configuration, 'runtime': runtime}


def preflight(s, commit, selected):
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source-commit must name a commit')
    review = json.loads(pinned(commit, REVIEW, REVIEW_SHA))
    for path, expected in review['source_configuration_bindings'].items():
        source = git_file(commit, path)
        require({'bytes': len(source), 'sha256': s.api.sha(source)} == expected,
                'published configuration differs: ' + path)
    h = s.h
    graph, actual = h.project_graph(PROJECT, [FIFTH, FOURTH])
    require(len(graph) == 304 and len(h.closure(graph, [FOURTH])) == 252 and
            h.closure(graph, [FIFTH]) == set(graph) and set(TARGETS) <= set(graph),
            'actual-means closure differs')
    sources = {m: s.api.sha(git_file(commit, h.module_path(m))) for m in graph}
    for m in graph:
        require(actual[m]['sha256'] == sources[m], 'published source differs: ' + m)
    baseline = snapshot(s, graph, review)
    require(baseline['project_sources'] == sources, 'sources changed during preflight')
    order = s.d.compile_order([], selected, graph)
    return review, graph, sources, baseline, order


def run_owner(s, commit, base, run, m, graph, sources):
    folder = base / m
    s.d.write_frozen(folder / 'inputs/e9.py', s.e9)
    # A different Git commit can have the identical proof/dependency context.
    # Hold its retained computation for inspection; the pinned API still owns
    # receipt validation, and this wrapper never rebases an acceptance receipt.
    previous = [p / m for p in ROOT.iterdir()
                if p.is_dir() and p.name != commit and re.fullmatch('[0-9a-f]{40}', p.name)
                and (p / m).is_dir()]
    normal_dir = folder / 'normal' / m
    if not os.path.lexists(normal_dir / 'NORMAL_PASS.json') and any(normal_dir.glob('attempt-*/normal-started.json')):
        previous.append(folder)
    if previous:
        current = s.api.context(commit, PROJECT, m, graph, sources, s.h, s.d)
        current = {k: v for k, v in current.items() if k != 'source_commit'}
        for old in previous:
            normal = old / 'normal' / m
            bindings = []
            receipt = normal / 'NORMAL_PASS.json'
            if receipt.is_file():
                bindings.append((receipt, json.loads(receipt.read_bytes())['dependency_context']))
            for started in normal.glob('attempt-*/normal-started.json'):
                context = started.parent / 'CONTEXT_BEFORE.json'
                require(context.is_file(), 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(started))
                bindings.append((started, json.loads(context.read_bytes())))
            for path, binding in bindings:
                identity = {k: v for k, v in binding.items() if k != 'source_commit'}
                require(identity.keys() == current.keys() and binding.get('source_commit') == old.parent.name,
                        'RETAINED_HISTORY_REQUIRES_INSPECTION: incomplete or misbound context in ' + str(path))
                require(identity != current, 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(path))
            require(bindings or (not any((old / 'plans').glob('*.json')) and
                                 not any((old / 'audits').glob('*'))),
                    'RETAINED_HISTORY_REQUIRES_INSPECTION: missing normal context in ' + str(old))
    # Preserve a partial audit even if its normal later becomes unavailable.
    for plan in (folder / 'plans').glob('*.json'):
        require((folder / 'audits' / plan.stem / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(plan))
    for directory in (folder / 'audits').glob('*'):
        require((directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(directory))
    passed = s.api.normal_one(commit, PROJECT, folder, m, graph, sources, s.h, s.ops, s.d)
    accepted = set()
    s.api.audit(commit, PROJECT, folder, {m: passed}, graph, sources, s.h, s.ops,
                s.d, run / m, accepted)
    require(accepted == {m}, 'owner missing from validated audit receipt')


def worker(s, commit, selected, run):
    s.d.verify_lane(s.h)
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [],
              'failures': {}, 'whole_P1_complete': False}
    try:
        review, graph, sources, baseline, order = preflight(s, commit, selected)
        result['targets'] = order
        s.d.save(run / 'CONTEXT_BEFORE.json', baseline)
        for m in order:
            try:
                require(snapshot(s, graph, review) == baseline, 'source or runtime context changed')
                run_owner(s, commit, ROOT / commit, run, m, graph, sources)
                result['accepted_owners'].append(m)
                s.ops.emit('OWNER_ACCEPTED', module=m)
            except Exception as error:
                result['failures'][m] = str(error)
                s.ops.emit('OWNER_HELD_OR_FAILED', module=m, reason=str(error))
        after = snapshot(s, graph, review)
        s.d.save(run / 'CONTEXT_AFTER.json', after)
        require(after == baseline, 'source or runtime context changed')
    except Exception as error:
        result['context_error'] = str(error)
    s.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('context_error')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--targets', nargs='+', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    require(re.fullmatch('[0-9a-f]{40}', commit), 'source-commit requires a full lowercase SHA')
    selected = selection(args.targets)
    s = helpers()
    if args.check:
        require(args.inside_lane is None, 'check does not use a lane')
        _, graph, _, _, order = preflight(s, commit, selected)
        print(json.dumps({'status': 'STATIC_SOURCE_AND_RUNTIME_CONFIG_VERIFIED',
                          'source_commit': commit, 'source_count': len(graph), 'targets': order}))
        return 0
    base = ROOT / commit
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name)
                and run.is_dir(), 'invalid worker directory')
        return worker(s, commit, selected, run)
    run = s.d.attempt(base / 'runs')
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [],
              'failures': {}, 'whole_P1_complete': False}
    try:
        before = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_BEFORE.json', before)
        executed = run / 'executed-driver.py'
        s.d.write_frozen(executed, Path(__file__).read_bytes())
        child = ['python3', '-B', str(executed), '--source-commit', commit, '--targets',
                 *selected, '--run', '--inside-lane', str(run)]
        command = s.ops.run(run, 'serialized-worker', s.h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        if (run / 'WORKER_RESULT.json').is_file():
            result.update(s.api.read_json(run / 'WORKER_RESULT.json'))
        result['worker_exit_code'] = command['exit_code']
        require(command['exit_code'] == 0, 'serialized worker exited ' + str(command['exit_code']))
    except Exception as error:
        result['dispatch_error'] = str(error)
    finally:
        try:
            after = s.d.original_git_state(REPO)
            s.d.save(run / 'GIT_AFTER.json', after)
            require(after == s.api.read_json(run / 'GIT_BEFORE.json'), 'original dirty Git state changed')
        except Exception as error:
            result['git_error'] = str(error)
    success = (set(result['accepted_owners']) == set(selected) and not result['failures']
               and not any(key in result for key in ('context_error', 'dispatch_error', 'git_error')))
    result['all_selected_owners_accepted'] = success
    s.d.save(run / 'RESULT.json', result)
    s.ops.emit('P15_RESULT', path=str(run / 'RESULT.json'), **result)
    return int(not success)


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
