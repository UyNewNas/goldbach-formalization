#!/usr/bin/env python3
"""Reuse the exact original Recorded normal log through the unchanged e9 API.

Only the missing named kernel and complete-owned audit may run, with e9's two
stock no-build gates.  The original aggregate exit 1 and unknown Git commit are
preserved.  No normal build, source installation or NORMAL_PASS is synthesized.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import types

if not __debug__:
    raise RuntimeError('optimized Python is forbidden for original-evidence reuse')

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261128-p14-recorded-owned-supplement')
PREFIX = 'docs/p1/20261128/p14-recorded-owned-supplement/'
DRIVER = PREFIX + 'run_recorded_owned_supplement.py'
MANIFEST = PREFIX + 'MANIFEST.json'
PLAN_PATH = PREFIX + 'AUDIT_PLAN.json'
MODULE = 'ImbalancedChen.P5RecordedOldFifthBlockTotals'
SOURCE = MODULE.replace('.', '/') + '.lean'
SOURCE_SHA = '7a2548770d2e8f863ae30f9016b61845591b3f4882b60ec1b82bd43fdf1216fa'
BASE = 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52'
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
HELPER = 'docs/p1/20261124/batch5-parallel/run_batch5_parallel.py'
PRIMITIVES = 'docs/p1/20261125/batch10-resume/resume_batch10.py'
E9 = 'docs/p1/20261124/normal-supplement-audit/run_parallel_acceptance_multibatch.py'
PINS = {
    HELPER: '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5',
    PRIMITIVES: '63e999403a1d39251642097c8a03e8b60983df785267fcca32f118b57aab2f71',
    E9: 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1',
}
REVIEW = Path('/workspace/p1-complete-proof/20261125-batch16-repairs-v1/9ea714790c06b2270f2028555d9ba774b152d536/expression-two/inputs/review.json')
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
LEGACY_ROOT = Path('/workspace/p1-complete-proof/modern-p1-build/incremental-six-root-after-source-repairs')
NORMAL_SHA = '63da4b14f4b1f9dda09882e90464cf8cffd322667471932e2a4e4b2898ae8bb9'
CONTEXT_SHA = 'db2dfc6e2ae8357ded33da4d3f5f938284db78ebaf5d6caa17d097d4ff5f3538'
COMMAND_PATH = 'docs/verification/20261123-blue-compilation/member-repair-batch96/P5OriginalTaylorFiveDimensionalMidpoint/static-provenance/ACTUAL_COMMAND.json'
COMMAND_SHA = 'c4831ed2e770a24776e23431d1a601cda0b8b8dce823430674fdddb05736ddc0'
NORMAL_KEY = 'original-incremental-six-root'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(repo, commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)


def load(raw, name):
    module = types.ModuleType(name)
    module.__file__ = '<unchanged pinned Git object: ' + name + '>'
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': sha(raw)}


def read_archive(raw, specification):
    need(fingerprint(raw) == {key: specification[key] for key in ('bytes', 'sha256')}, 'frozen original evidence archive differs')
    expected = specification['members']
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:xz') as archive:
        members = archive.getmembers()
        need(len(members) == len(expected) and {member.name for member in members} == set(expected),
             'evidence archive membership differs')
        need(sum(member.size for member in members) <= 32 * 1024 * 1024, 'evidence archive exceeds fixed expanded bound')
        result = {}
        for member in members:
            need(member.isfile() and member.size == expected[member.name]['bytes'] and
                 member.size <= 16 * 1024 * 1024, 'evidence archive contains a non-file or oversized member')
            data = archive.extractfile(member).read()
            need(fingerprint(data) == expected[member.name], 'original archive member differs: ' + member.name)
            result[member.name] = data
    return result


def original_inputs(manifest, plan, originals, h):
    """Verify original bytes and e9's complete Built-set rule without execution."""
    need(manifest['schema'] == 'p14_recorded_original_normal_reuse_manifest_v1' and
         manifest['module'] == MODULE and manifest['source_path'] == SOURCE and
         manifest['source_bytes'] == 23109 and manifest['source_sha256'] == SOURCE_SHA and
         manifest['review_baseline_commit'] == BASE, 'selected source or evidence scope differs')
    command_raw = originals['originals/ACTUAL_COMMAND.json']
    command = json.loads(command_raw)
    context_raw = originals['originals/SOURCE_CONTEXT.json']
    context = json.loads(context_raw)
    normal_raw = originals['originals/normal.log']
    need(sha(command_raw) == COMMAND_SHA and sha(context_raw) == CONTEXT_SHA and sha(normal_raw) == NORMAL_SHA,
         'original primary command/context/log differs')
    need(manifest['normal_command'] == {'repository_path': COMMAND_PATH, 'bytes': 9862,
                                       'sha256': COMMAND_SHA, 'exit_code': 1}, 'original command pin differs')
    need(command['exit_code'] == manifest['normal_whole_batch_exit_code'] == 1 and
         command['cwd'] == str(PROJECT) and command['log_sha256'] == NORMAL_SHA and
         command['source_context'] == str(LEGACY_ROOT / 'SOURCE_CONTEXT.json') and
         command['source_context_sha256'] == CONTEXT_SHA, 'original aggregate provenance differs')
    target_source = context['effective_source_bindings'][MODULE]
    need(target_source == {'path': str(PROJECT / SOURCE), 'bytes': 23109, 'sha256': SOURCE_SHA},
         'original target source context differs')
    text = h.ANSI.sub('', normal_raw.decode())
    built = h.BUILT.findall(text)
    need(len(built) == len(set(built)) and len(built) == 43 and MODULE in built and
         MODULE not in command['actual_failed_modules'], 'original successful target header is missing/ambiguous')
    leaf_error = re.compile(r'^error:\s+' + re.escape(SOURCE) + r':', re.M)
    need(not leaf_error.search(text), 'original log contains a selected-source error')
    extra = set(built) - set(command['actual_Built_project_modules'])
    need(extra == {'ImbalancedChen.P1CorrectedFifthCausalTupleDictionary'} and
         not set(command['actual_Built_project_modules']) - set(built), 'unexpected legacy Built-summary discrepancy')
    selected_headers = [{'line': number, 'text': line, 'module': match.group(1)}
                        for number, line in enumerate(text.splitlines(), 1)
                        if (match := h.BUILT.match(line)) and match.group(1) == MODULE]
    need(len(selected_headers) == 1, 'selected original Built header is not unique')
    need(plan['schema'] == 'p1_completed_normal_multibatch_audit_plan_v1' and
         plan['project'] == str(PROJECT) and plan['receipt_root'] == str(ROOT / 'audit') and
         plan['lanes'] == [{'id': 0, 'modules': [MODULE]}, {'id': 1, 'modules': []}] and
         plan['expected_project_sources'] == {MODULE: SOURCE_SHA} and
         plan['modules'] == {MODULE: {'source_sha256': SOURCE_SHA, 'normal_log': NORMAL_KEY, 'project_closure': [MODULE]}},
         'e9 plan scope or project source closure differs')
    need(set(plan['normal_logs']) == {NORMAL_KEY}, 'additional normal log introduced')
    normal = plan['normal_logs'][NORMAL_KEY]
    need(normal['path'] == str(LEGACY_ROOT / 'normal.log') and normal['sha256'] == NORMAL_SHA and
         normal['source_commit'] is None and normal['expected_built_modules'] == built and
         normal['source_context_path'] == str(LEGACY_ROOT / 'SOURCE_CONTEXT.json') and
         normal['source_context_sha256'] == CONTEXT_SHA and normal['original_whole_batch_exit_code'] == 1,
         'normal reuse must retain complete raw-log scope and original context, not invent a Git revision')
    need(plan['runner_binding'] == {'path': E9, 'sha256': PINS[E9]} and plan['runtime_states'] == list(map(str, h.STATES)) and
         plan['excluded_prior13'] == [] and plan['reused_complete_modules'] == [] and
         plan['source_review_head'] == BASE and plan['active_lane'] == 0 and
         plan['default_dual_lane_invocation_forbidden'] is True and
         plan['successful_normal_not_to_be_repeated'] is True and
         plan['historical_output_snapshot_claimed'] is False and
         plan['whole_P1_complete'] is False and plan['whole_P1_4_complete'] is False, 'unchanged API boundaries differ')
    need(manifest['tools_commit'] == TOOLS and manifest['immutable_tools'] == PINS and
         manifest['runtime_review'] == {'path': str(REVIEW), 'sha256': REVIEW_SHA}, 'fixed runtime/tool bindings differ')
    for key in ('normal_reexecution_permitted', 'new_NORMAL_PASS_permitted', 'source_installation_permitted',
                'whole_P1_4_complete', 'new_kernel_owned_acceptance_claimed'):
        need(manifest[key] is False, 'reuse boundary changed: ' + key)
    return {'command': command, 'context': context, 'built': built, 'selected_headers': selected_headers}


def live_binding(manifest, plan, originals, h, d, review):
    runtime = d.runtime_binding(h)
    configuration = {path: d.fingerprint(PROJECT / path) for path in
                     ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')}
    need(runtime == review['existing_runtime_bindings'] and configuration == review['runtime_configuration_bindings'] and
         not (PROJECT / 'lakefile.lean').exists(), 'original runtime/configuration binding differs')
    need(plan['audit_template'] == {'path': str(d.AUDIT_TEMPLATE), 'sha256': d.AUDIT_TEMPLATE_SHA},
         'unchanged complete-owned audit template required')
    for member, path in [('originals/normal.log', LEGACY_ROOT / 'normal.log'),
                         ('originals/SOURCE_CONTEXT.json', LEGACY_ROOT / 'SOURCE_CONTEXT.json')]:
        need(path.is_file() and not path.is_symlink() and d.fingerprint(path) == fingerprint(originals[member]),
             'live original primary evidence differs: ' + str(path))
    context = json.loads(originals['originals/SOURCE_CONTEXT.json'])
    need({Path(row['path']).name: row['sha256'] for row in context['config_pins']} ==
         {path: value['sha256'] for path, value in configuration.items()},
         'current configuration differs from the actual original normal context')
    graph, _ = h.project_graph(PROJECT, [MODULE])
    need(graph == {MODULE: []}, 'Recorded project dependency closure changed')
    snapshot = d.snapshot(PROJECT, MODULE)
    need(snapshot == manifest['observed_live_source_plus_five'] and
         snapshot[SOURCE] == {'bytes': 23109, 'sha256': SOURCE_SHA},
         'current six files differ from the bounded read-only observation; HOLD without rebuild')
    return {'source_plus_five': snapshot, 'runtime': runtime, 'configuration': configuration,
            'protected_roots': h.check_roots()}


def verify_result(root, plan, original, current, h, d):
    lane = root / 'audit/lane-0'
    result = json.loads((lane / 'VALIDATION_RESULTS.json').read_bytes())
    need(result['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS' and
         result['modules'] == {MODULE: SOURCE_SHA} and result['project_dependency_sources'] == {MODULE: SOURCE_SHA} and
         result['source_plus_five_outputs'] == {MODULE: current['source_plus_five']} and
         result['plan_sha256'] == d.fingerprint(root / 'audit/AUDIT_PLAN.json')['sha256'] and
         json.loads((root / 'audit/AUDIT_PLAN.json').read_bytes()) == plan and
         result['runtime_state'] == str(h.STATES[0]) and
         result['runtime_state_sha256'] == current['runtime'][str(h.STATES[0])]['sha256'] and
         result['audit_template_sha256'] == d.AUDIT_TEMPLATE_SHA, 'unchanged e9 result binding differs')
    reused = result['reused_normal_evidence']
    need(json.loads((lane / 'REUSED_NORMAL_EVIDENCE.json').read_bytes()) == reused and set(reused) == {NORMAL_KEY},
         'original normal evidence record differs')
    row = reused[NORMAL_KEY]
    need(row['path'] == str(LEGACY_ROOT / 'normal.log') and row['sha256'] == NORMAL_SHA and row['source_commit'] is None and
         row['all_actual_built_modules'] == original['built'] and row['selected_actual_built_headers'] == original['selected_headers'] and
         row['selected_sources'] == {MODULE: SOURCE_SHA} and row['whole_normal_batch_exit0_required'] is False,
         'original normal reuse was relabelled or narrowed')
    need(set(result['kernel_commands']) == {MODULE}, 'kernel owner scope differs')
    commands = [(result['stock_readiness_before'], ['lake', '--no-build', 'build', '+' + MODULE + ':olean']),
                (result['kernel_commands'][MODULE], ['lake', 'env', 'leanchecker', '--verbose', MODULE]),
                (result['audit_command'], ['lake', 'env', 'lean', '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000',
                                           '--root=' + str(lane), str(lane / 'PublicAudit.lean')]),
                (result['stock_readiness_after'], ['lake', '--no-build', 'build', '+' + MODULE + ':olean'])]
    for command, argv in commands:
        log = lane / command['log']
        need(command['exit_code'] == 0 and command['cwd'] == str(PROJECT) and command['argv'] == h.guard(0, argv) and
             d.fingerprint(log)['sha256'] == command['log_sha256'] and
             json.loads(log.with_name(log.stem + '-command.json').read_bytes()) == command, 'e9 command/log identity differs')
    template = d.AUDIT_TEMPLATE.read_text()
    audit = re.sub(r'^import ImbalancedChen\.[^\n]+\n', '', template, flags=re.M)
    audit = 'import ' + MODULE + '\n' + audit
    audit, count = re.subn(r'let modules := #\[[^\n]*\]', 'let modules := #[`' + MODULE + ']', audit, count=1)
    need(count == 1 and (lane / 'PublicAudit.lean').read_text() == audit, 'e9 audit template changed beyond original module substitution')
    text = (lane / 'all-owned-types-axioms.log').read_text()
    records = [json.loads(value) for value in re.findall(r'AUDIT_RECORD (\{[^\n]+\})', text)]
    inventories = [json.loads(value)['names'] for value in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})', text)]
    names = [row['name'] for row in records]
    need(len(inventories) == 1 and names and len(names) == len(set(names)) and sorted(names) == sorted(inventories[0]) and
         {row['module'] for row in records} == {MODULE} and
         json.loads((lane / 'OWNED_EXPORTS.json').read_bytes()) == records and result['total_owned_exports'] == len(records) and
         result['total_public_exports'] == sum(not row['is_private'] for row in records), 'complete dynamic owned inventory differs')
    need(all(row['kind'] != 'axiom' and set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} and
             isinstance(row['type'], str) and row['type'] and isinstance(row['type_expression'], str) and row['type_expression'] and
             isinstance(row['universe_parameters'], list) and type(row['is_private']) is bool for row in records),
         'full type/AST/universe/axiom evidence is missing')
    forbidden = ('sorryAx', '…', '⋯', '...')
    need(not any(token in text for token in forbidden) and
         not any(token in row['type'] or token in row['type_expression'] for row in records for token in forbidden),
         'owned output contains elision or forbidden axiom')
    need(all(result[key] for key in ('full_owned_including_private_generated', 'only_standard_axioms',
                                     'pp_all_true_no_elisions', 'source_plus_five_outputs_unchanged_across_kernel_and_audit',
                                     'successful_normal_not_repeated')) and result['whole_P1_complete'] is False,
         'unchanged e9 acceptance flags differ')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--run', action='store_true')
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    source = args.source_commit
    need(re.fullmatch(r'[0-9a-f]{40}', source) is not None, 'full published source commit required')
    driver = Path(__file__).read_bytes()
    need(driver == git(REPO, source, DRIVER), 'executing caller differs from claimed Git source')
    manifest_raw = git(REPO, source, MANIFEST)
    manifest = json.loads(manifest_raw)
    plan_raw = git(REPO, source, PLAN_PATH)
    plan = json.loads(plan_raw)
    need(manifest['audit_plan'] == {'path': PLAN_PATH, **fingerprint(plan_raw)}, 'frozen e9 plan differs')
    archive_spec = manifest['evidence_archive']
    need(archive_spec['path'] == PREFIX + 'evidence/original-normal-and-live-observation.tar.xz', 'archive path differs')
    originals = read_archive(git(REPO, source, archive_spec['path']), archive_spec)
    tools = {path: git(REPO, TOOLS, path) for path in PINS}
    need(all(sha(tools[path]) == digest for path, digest in PINS.items()), 'original immutable helper/API bytes differ')
    h, d = load(tools[HELPER], 'original_batch5'), load(tools[PRIMITIVES], 'original_batch10')
    original = original_inputs(manifest, plan, originals, h)
    need(git(REPO, BASE, COMMAND_PATH) == originals['originals/ACTUAL_COMMAND.json'] and
         fingerprint(git(REPO, source, SOURCE)) == {'bytes': 23109, 'sha256': SOURCE_SHA},
         'original command or published source identity differs')
    review_raw = REVIEW.read_bytes()
    need(sha(review_raw) == REVIEW_SHA, 'fixed runtime review differs')
    review = json.loads(review_raw)
    current = live_binding(manifest, plan, originals, h, d, review)
    binding = {'schema': 'p14_recorded_original_normal_reuse_execution_binding_v1', 'source_commit': source,
               'driver_sha256': sha(driver), 'manifest_sha256': sha(manifest_raw), 'plan_sha256': sha(plan_raw),
               'immutable_e9_sha256': PINS[E9], 'module': MODULE, 'live_before': current,
               'original_normal_log_sha256': NORMAL_SHA, 'original_normal_context_sha256': CONTEXT_SHA,
               'original_normal_git_commit': None, 'original_whole_batch_exit_code': 1, 'whole_P1_4_complete': False}
    if args.check:
        need(not args.worker, 'read-only check cannot be a worker')
        print(json.dumps({'status': 'READ_ONLY_ORIGINAL_NORMAL_REUSE_CHECK_PASS_NOT_ACCEPTANCE',
                          **binding, 'existing_execution_present': (ROOT / 'run').exists()}), flush=True)
        return 0
    run = ROOT / 'run'
    if not args.worker:
        need(not run.exists() and not (ROOT / 'audit').exists(),
             'existing kernel/audit attempt requires receipt inspection; no automatic replay')
        before_git = d.original_git_state(REPO)
        d.save(ROOT / 'BINDING.json', binding)
        d.write_frozen(ROOT / 'inputs/MANIFEST.json', manifest_raw)
        d.write_frozen(ROOT / 'inputs/AUDIT_PLAN.json', plan_raw)
        d.write_frozen(ROOT / 'inputs/e9.py', tools[E9])
        executed = ROOT / 'executed-driver.py'
        d.write_frozen(executed, driver)
        run.mkdir()
        d.save(run / 'GIT_BEFORE.json', before_git)
        child = ['python3', '-B', str(executed), '--source-commit', source, '--run', '--worker']
        try:
            return subprocess.run(h.serialize(0, run / 'VALIDATION_LANE.json', child)).returncode
        finally:
            after_git = d.original_git_state(REPO)
            d.save(run / 'GIT_AFTER.json', after_git)
            need(after_git == before_git, 'original Git checkout changed')
    d.verify_lane(h)
    need(json.loads((ROOT / 'BINDING.json').read_bytes()) == binding and
         (ROOT / 'inputs/MANIFEST.json').read_bytes() == manifest_raw and
         (ROOT / 'inputs/AUDIT_PLAN.json').read_bytes() == plan_raw and
         (ROOT / 'inputs/e9.py').read_bytes() == tools[E9], 'frozen caller inputs changed')
    lane_receipt = json.loads((run / 'VALIDATION_LANE.json').read_bytes())
    need(lane_receipt['status'] == 'VALIDATION_LANE_ACQUIRED' and lane_receipt['state'] == str(h.STATES[0]),
         'original serializer lane receipt differs')
    d.save(run / 'LIVE_BEFORE.json', current)
    runner = ROOT / 'inputs/e9.py'
    try:
        prepared = d.record_command(PROJECT, run, 'audit-prepare',
                                    ['python3', '-B', str(runner), '--plan', str(ROOT / 'inputs/AUDIT_PLAN.json'), '--prepare-only'])
        need(prepared['exit_code'] == 0, 'unchanged e9 preparation failed; preserve partial receipt')
        completed = d.record_command(PROJECT, run, 'audit-lane-0',
                                     ['python3', '-B', str(runner), '--plan', str(ROOT / 'audit/AUDIT_PLAN.json'),
                                      '--receipt-root', str(ROOT / 'audit'), '--lane', '0'])
        need(completed['exit_code'] == 0, 'unchanged e9 readiness/kernel/full-owned gate held or failed')
    finally:
        after = live_binding(manifest, plan, originals, h, d, review)
        d.save(run / 'LIVE_AFTER.json', after)
        need(after == current, 'sources/outputs/runtime/protected roots changed across unchanged e9 gates')
    result = verify_result(ROOT, plan, original, current, h, d)
    summary = {'status': 'PASS_ORIGINAL_NORMAL_REUSED_UNCHANGED_E9_KERNEL_FULL_OWNED', 'source_commit': source,
               'module': MODULE, 'validation_result': str(ROOT / 'audit/lane-0/VALIDATION_RESULTS.json'),
               'validation_result_sha256': d.fingerprint(ROOT / 'audit/lane-0/VALIDATION_RESULTS.json')['sha256'],
               'original_whole_batch_exit_code': 1, 'original_normal_git_commit': None,
               'original_log_sha256': NORMAL_SHA, 'original_source_context_sha256': CONTEXT_SHA,
               'actual_original_built_count': len(original['built']), 'original_summary_built_count': 42,
               'new_normal_invocations': 0, 'new_kernel_invocations': 1, 'new_full_owned_audit_invocations': 1,
               'stock_no_build_gates_preserved': 2, 'owned_total': result['total_owned_exports'],
               'public_total': result['total_public_exports'],
               'private_total': result['total_owned_exports'] - result['total_public_exports'],
               'observed_live_six_stable': True, 'historical_output_snapshot_claimed': False, 'whole_P1_4_complete': False}
    d.save(run / 'RECORDED_ORIGINAL_NORMAL_REUSE_RESULT.json', summary)
    print(json.dumps(summary), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
