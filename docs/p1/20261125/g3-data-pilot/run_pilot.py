#!/usr/bin/env python3
"""G3 Data-only pilot: read-only check, durable fixture-bound normal, separate audit.

No source/fixture installation, Reader rebuild or downstream Checked claims.
The unchanged normal validator is supplemented by an immutable NPY companion.
"""
from pathlib import Path, PurePosixPath
from datetime import datetime
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
TOOLS = 'afe0ca6653f4eba9c258ecb8a743d0b45edd10c6'
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-g3-data-pilot-v1')
DATA = 'ImbalancedChen.P4AOriginalNewFifthArchiveData'
READER = 'ImbalancedChen.P4AOriginalNewFifthArchiveReader'
DATA_SHA = '5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4'
READER_SHA = '59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6'
RETRY = 'docs/p1/20261125/batch11-repairs/retry_four.py'
GROUP_CALLER = 'docs/p1/20261125/next-frontier/batch12-candidates/run_candidates.py'
INVENTORY = 'docs/p1/20261125/g3-reuse/G3_REUSE_INVENTORY.json'
READER_RECEIPT = 'docs/p1/20261124/batch5-verified-evidence/AUDIT24_VALIDATION_RESULTS.json'
PINS = {
    RETRY: '290228a30d7a773a52a27241d6d3fbf18efb3d5e3fd9b30c8f0db4d670e5717e',
    GROUP_CALLER: '8fc871e44e4702b01005aa179170cd172b50537f7aaa98e6bbdde4253ef2ac47',
    INVENTORY: 'c89fd6388cfb269ebe74bad97e62454a8ad36fc317d7e5685253f4c13785047e',
    READER_RECEIPT: '18a4660cae2ce1f0fa2d233f84be244f46b7a9522bd46f7289c89e50d72adcd1',
}
NORMAL = ROOT / 'normal' / DATA / 'NORMAL_PASS.json'
COMPANION = NORMAL.with_name('FIXTURE_BOUND_NORMAL.json')


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def inputs(repo, project):
    def git(commit, path):
        return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)

    raw = {path: git(TOOLS if path in (RETRY, GROUP_CALLER) else SOURCE, path) for path in PINS}
    need(all(sha(raw[path]) == digest for path, digest in PINS.items()), 'published input pin differs')
    p = types.ModuleType('published_normal_primitives')
    p.__file__ = '<pinned Git object: ' + RETRY + '>'
    exec(compile(raw[RETRY], p.__file__, 'exec'), p.__dict__)
    audit_api = p.load(raw[GROUP_CALLER], 'published_audit_caller')
    need(p.COMMIT == audit_api.SOURCE == SOURCE and p.PROJECT == audit_api.PROJECT == PROJECT,
         'published primitive source/environment differs')
    pins = dict(PINS)
    for path in (p.HELPER, p.OPS, p.PRIMITIVES, p.E9):
        raw[path] = git(SOURCE, path)
        pins[path] = p.PINS[path]
        need(sha(raw[path]) == pins[path], 'unchanged helper pin differs: ' + path)
    h, ops, d = p.load(raw[p.HELPER], 'batch5'), p.load(raw[p.OPS], 'batch6'), p.load(raw[p.PRIMITIVES], 'primitives')
    graph, actual = h.project_graph(project, [DATA])
    sources = {m: sha(git(SOURCE, h.module_path(m))) for m in graph}
    need(len(graph) == 68 and graph[DATA] == [READER] and sources[DATA] == DATA_SHA and
         sources[READER] == READER_SHA and {m: v['sha256'] for m, v in actual.items()} == sources,
         'Data/Reader or complete 68-module source closure differs')
    inventory = json.loads(raw[INVENTORY])
    fixtures = {row['install_path']: {'bytes': row['bytes'], 'sha256': row['sha256']} for row in inventory['g3_files']}
    source = git(SOURCE, h.module_path(DATA)).decode()
    pairs = re.findall(r'include_new_fifth_pair%\s+"([^"]+)"\s+"([^"]+)"', source)
    need(len(pairs) == source.count('include_new_fifth_pair%') == 94, 'literal include scope differs')
    expected_pairs = [(f'g3-fixtures/{bank}{i:04d}-cells.npy', f'g3-fixtures/{bank}{i:04d}-floors.npy')
                      for bank in ('C', 'F') for i in range(47)]
    need(pairs == expected_pairs, 'literal block order/pair paths differ')
    includes = [str(PurePosixPath(h.module_path(DATA)).parent / rel) for pair in pairs for rel in pair]
    need(len(fixtures) == len(inventory['g3_files']) == len(includes) == 188 and
         set(fixtures) == set(includes) and sum(x['bytes'] for x in fixtures.values()) == 423244864,
         '188 fixture inventory does not match Data-relative includes')
    receipt = json.loads(raw[READER_RECEIPT])
    reader_sources = {m: sources[m] for m in sorted(h.closure(graph, [READER]))}
    need(len(reader_sources) == 67 and receipt['status'] == p.PASS and receipt['modules'][READER] == READER_SHA and
         receipt['full_owned_including_private_generated'] is True and receipt['only_standard_axioms'] is True and
         all(receipt['project_dependency_sources'].get(m) == value for m, value in reader_sources.items()),
         'accepted Reader source closure binding differs')
    need(all(sha((project / h.module_path(m)).read_bytes()) == value for m, value in h.FOUR_ROOTS.items()),
         'protected original root source differs')
    return p, audit_api, h, ops, d, raw, pins, graph, sources, fixtures, receipt, reader_sources


def live_inputs(project, spec):
    p, audit_api, h, ops, d, raw, pins, graph, sources, fixtures, receipt, reader_sources = spec
    actual = {rel: d.fingerprint(project / rel) for rel in sorted(fixtures)}
    need(actual == fixtures, 'G3 fixture size/SHA differs from exact original inventory')
    reader = d.snapshot(project, READER)
    need(reader == receipt['source_plus_five_outputs'][READER], 'accepted Reader source/five outputs differ; no rebuild authorized')
    need({m: sha((project / h.module_path(m)).read_bytes()) for m in reader_sources} == reader_sources,
         'accepted Reader source closure changed')
    return {'source_commit': SOURCE, 'data_source_sha256': DATA_SHA, 'inventory_sha256': PINS[INVENTORY],
            'fixtures': actual, 'reader_reuse': {'receipt_sha256': PINS[READER_RECEIPT],
            'source_plus_five_outputs': reader, 'project_sources': reader_sources}}


def checkpoint(path, spec):
    d = spec[4]
    binding = live_inputs(PROJECT, spec)
    value = {'checked_utc': d.now(), 'input_binding': binding}
    d.save(path, value)
    return {'path': str(path), 'sha256': d.fingerprint(path)['sha256']}, value


def companion_valid(spec, current):
    p, audit_api, h, ops, d, raw, pins, graph, sources, fixtures, receipt, reader_sources = spec
    need(NORMAL.is_file() and COMPANION.is_file(), 'NO_FIXTURE_BOUND_NORMAL: generic receipt alone is insufficient')
    normal, bound = p.read_json(NORMAL), p.read_json(COMPANION)
    need(bound['schema'] == 'p1_g3_fixture_bound_normal_v1' and bound['module'] == DATA and
         bound['source_commit'] == SOURCE and bound['input_binding'] == current and
         bound['normal_receipt'] == {'path': str(NORMAL), 'sha256': d.fingerprint(NORMAL)['sha256']} and
         bound['source_plus_five_outputs'] == normal['source_plus_five_outputs'] == d.snapshot(PROJECT, DATA),
         'fixture-bound normal companion differs')
    p.normal_valid(DATA, normal, p.context(PROJECT, DATA, graph, sources, h, d), h, d)
    checks = []
    for key in ('before', 'after'):
        path = Path(bound[key]['path'])
        need(d.fingerprint(path)['sha256'] == bound[key]['sha256'], 'fixture checkpoint hash differs')
        value = p.read_json(path)
        need(value['input_binding'] == current, 'fixture checkpoint binding differs')
        checks.append(datetime.fromisoformat(value['checked_utc']))
    command = normal['normal_command']
    need(checks[0] <= datetime.fromisoformat(command['started_utc']) <=
         datetime.fromisoformat(command['finished_utc']) <= checks[1], 'fixture checkpoints do not enclose actual normal')
    return normal


def worker(spec, phase, run):
    p, audit_api, h, ops, d, raw, pins, graph, sources, fixtures, receipt, reader_sources = spec
    d.verify_lane(h)
    binding = p.read_json(ROOT / 'BINDING.json')
    need(binding['driver_sha256'] == sha(Path(__file__).read_bytes()) and binding['inputs'] == pins and
         binding['source_commit'] == SOURCE and binding['tooling_commit'] == TOOLS and binding['module'] == DATA and
         binding['project'] == str(PROJECT) and binding['runtime'] == d.runtime_binding(h), 'worker binding differs')
    result = {'phase': phase, 'module': DATA, 'source_commit': SOURCE, 'status': 'HELD_OR_FAILED',
              'source_or_fixture_installation_performed': False, 'reader_normal_repeated': False,
              'downstream_94_checked_modules_accepted': False, 'whole_P1_complete': False}
    try:
        normal_present, companion_present = os.path.lexists(NORMAL), os.path.lexists(COMPANION)
        need(normal_present == companion_present, 'ORPHAN_GENERIC_NORMAL_OR_COMPANION_REQUIRES_INSPECTION')
        need(phase == 'normal' or companion_present, 'AUDIT_REQUIRES_FIXTURE_BOUND_NORMAL')
        before_ref, before = checkpoint(run / 'FIXTURES_BEFORE.json', spec)
        prior = companion_valid(spec, before['input_binding']) if companion_present else None
        accepted, errors, normal = set(), [], prior
        try:
            if phase == 'normal':
                normal = p.normal_one(DATA, graph, sources, h, ops, d, root=ROOT, project=PROJECT)
            else:
                audit_api.audit(ROOT, {DATA: normal}, graph, sources, p, h, ops, d, run, accepted)
        except Exception as error:
            errors.append(str(error))
        try:
            after_ref, after = checkpoint(run / 'FIXTURES_AFTER.json', spec)
            need(before['input_binding'] == after['input_binding'], 'fixtures/accepted Reader changed during operation')
        except Exception as error:
            errors.append('post-operation fixture gate: ' + str(error))
        need(not errors, '; '.join(errors))
        if phase == 'normal' and prior is None:
            need(p.read_json(NORMAL) == normal, 'durable generic normal differs')
            p.normal_valid(DATA, normal, p.context(PROJECT, DATA, graph, sources, h, d), h, d)
            d.save(COMPANION, {'schema': 'p1_g3_fixture_bound_normal_v1', 'module': DATA, 'source_commit': SOURCE,
                   'input_binding': after['input_binding'], 'before': before_ref, 'after': after_ref,
                   'normal_receipt': {'path': str(NORMAL), 'sha256': d.fingerprint(NORMAL)['sha256']},
                   'source_plus_five_outputs': normal['source_plus_five_outputs'],
                   'kernel_or_full_owned_claim': False, 'downstream_94_checked_modules_accepted': False,
                   'whole_P1_complete': False})
        companion_valid(spec, after['input_binding'])
        if phase == 'audit':
            need(accepted == {DATA}, 'Data owner audit did not complete')
            audit_results = {str(path): d.fingerprint(path) for path in
                             sorted((ROOT / 'audits').glob('*/lane-0/VALIDATION_RESULTS.json'))}
            d.save(run / 'FIXTURE_BOUND_AUDIT.json', {'schema': 'p1_g3_fixture_bound_audit_v1', 'module': DATA,
                   'source_commit': SOURCE, 'normal_companion_sha256': d.fingerprint(COMPANION)['sha256'],
                   'input_binding': after['input_binding'], 'before': before_ref, 'after': after_ref,
                   'validated_e9_results': audit_results, 'source_plus_five_outputs': d.snapshot(PROJECT, DATA),
                   'downstream_94_checked_modules_accepted': False, 'whole_P1_complete': False})
        result['status'] = 'NORMAL_WITH_FIXTURES_AUDIT_PENDING' if phase == 'normal' else 'DATA_OWNER_ACCEPTED_WITH_FIXTURES'
        result['normal_reused'] = prior is not None
        result['normal_companion'] = str(COMPANION)
    except Exception as error:
        result['error'] = str(error)
        ops.emit('G3_DATA_HELD_OR_FAILED', phase=phase, reason=str(error))
    d.save(run / 'RESULT.json', result)
    ops.emit('G3_DATA_RESULT', **result)
    return 1 if result['status'] == 'HELD_OR_FAILED' else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ('check', 'normal', 'audit'):
        mode.add_argument('--' + flag, action='store_true')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    repo, project = args.source_repo.resolve(), args.project.resolve()
    spec = inputs(repo, project)
    p, audit_api, h, ops, d, raw, pins, graph, sources, fixtures, receipt, reader_sources = spec
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        live_inputs(project, spec)
        print(json.dumps({'status': 'READ_ONLY_INPUTS_READER_MATCH_NOT_DATA_ACCEPTANCE', 'source_commit': SOURCE,
                          'source_closure_count': len(sources), 'fixture_count': len(fixtures),
                          'fixture_bytes': sum(x['bytes'] for x in fixtures.values()), 'whole_P1_complete': False}))
        return 0
    need(repo == REPO and project == PROJECT, 'execution is restricted to the existing cloud project')
    phase = 'normal' if args.normal else 'audit'
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires run directory')
        run = args.run_dir.resolve()
        need(run.parent == ROOT / 'runs' / phase and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid run directory')
        return worker(spec, phase, run)
    need(args.run_dir is None, 'run-dir requires serialized worker')
    original = d.original_git_state(repo)
    d.save(ROOT / 'BINDING.json', {'source_commit': SOURCE, 'tooling_commit': TOOLS, 'module': DATA,
           'driver_sha256': sha(Path(__file__).read_bytes()), 'inputs': pins, 'runtime': d.runtime_binding(h),
           'project': str(PROJECT)})
    for path, data in raw.items():
        d.write_frozen(ROOT / 'inputs' / ('e9.py' if path == p.E9 else Path(path).name), data)
    executed = ROOT / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(ROOT / 'runs' / phase)
    d.save(run / 'GIT_BEFORE.json', original)
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', [
            'python3', '-B', str(executed), '--' + phase, '--inside-lane', '--run-dir', str(run)]), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(repo)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty source Git worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
