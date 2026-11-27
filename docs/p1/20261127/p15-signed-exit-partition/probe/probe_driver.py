"""Probe one original Partition source without rebuilding accepted dependencies.

The original Dictionary receipts are referenced by immutable byte pins.  Their
normal context supplies the exact forty-module dependency inputs; this probe
does not replay or re-accept the Dictionary.  The full D288 inventory receives
before/after metadata protection.  The original Variation reader is reused.
"""
from pathlib import Path
from types import ModuleType, SimpleNamespace
import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ACCEPTANCE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DICTIONARY_COMMIT = '040d46058821746c69c5183b3f6c22792287c4ba'
DICTIONARY = 'ImbalancedChen.P1OriginalHistoricalCoefficientDictionary'
VARIATION_COMMIT = 'f7e9219f4860a819758d52752c5a9309dd14a8c7'
VARIATION_ADAPTER = 'docs/p1/20261127/p15-mellin-variation/run_variation.py'
VARIATION_ADAPTER_SHA = '1c132fefea799e8a3a3127defb07785138e3669e1f80beee2f5aa733b1914f50'
EVIDENCE_COMMIT = '3c9bc8fbb8dcd8adc9e4f69c53aab7f41b8d5508'
EVIDENCE = 'docs/p1/20261127/p15-dictionary-mellin-acceptance/'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
SOURCE_BASE = DICTIONARY_COMMIT
TARGET = 'ImbalancedChen.P1SignedExitPartition'
NAME = 'P1SignedExitPartition.lean'
SOURCE_PATH = 'ImbalancedChen/' + NAME
ORIGINAL_SOURCE_SHA = 'cb4d4bb096d7de762cb23925af58624736bcfd753251f348b352acc67bdd2ad9'
ORIGINAL_SOURCE_BYTES = 15982
SOURCE_SHA = '19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c'
SOURCE_BYTES = 15972
PROJECT_IMPORTS = ['ImbalancedChen.FirstExitHistoricalLevels']
MATHLIB_IMPORT = 'Mathlib.Algebra.BigOperators.Group.Finset.Piecewise'
IMPORTS = PROJECT_IMPORTS + [MATHLIB_IMPORT]
ROOT = Path('/workspace/p1-complete-proof/20261127-p15-signed-exit-partition-probe-v1')
RUN = ROOT / SOURCE_SHA / 'attempt-00000'
INPUT = Path('/workspace/p1-complete-proof/p15-staged-scripts') / ('signed_exit_partition_' + SOURCE_SHA + '.lean')
PREVIOUS_FAILURE = {'task_id':'job_26dda8849e2f4038b3a5eb22f333d49b','source_sha256':ORIGINAL_SOURCE_SHA,'result_sha256':'b87a76b34d3df676d1f65817582711ab83c5e3e6903bdd77abfb9c7d61f55554','log_sha256':'f5faaf911b3ac6c4ab71bee14c836b9058a9e37096a66e527cf648f562f0acbd'}

DICT_RUN = ACCEPTANCE_ROOT / DICTIONARY_COMMIT / 'runs/attempt-00000'
DICT_NORMAL = ACCEPTANCE_ROOT / DICTIONARY_COMMIT / DICTIONARY / 'normal' / DICTIONARY
# These are exact original raw receipts, already published in the accepted packet.
RECEIPTS = {
    'normal_context': {
        'path': DICT_NORMAL / 'attempt-00000/CONTEXT_BEFORE.json',
        'published': 'dictionary-owner/normal/' + DICTIONARY + '/attempt-00000/CONTEXT_BEFORE.json',
        'bytes': 144381, 'sha256': '5591ac1fd7254757a280a93ad2e89e7c8c8c3e4f34ed086a384bdda4c8366da8'},
    'normal_pass': {
        'path': DICT_NORMAL / 'NORMAL_PASS.json',
        'published': 'dictionary-owner/normal/' + DICTIONARY + '/NORMAL_PASS.json',
        'bytes': 152633, 'sha256': '2c54cda903defdb827f78a7a80234382c7fe0a073a6b8afc6f85acb50de6f1e2'},
    'full_context': {
        'path': DICT_RUN / 'CONTEXT_BEFORE.json',
        'published': 'dictionary-run/CONTEXT_BEFORE.json',
        'bytes': 972087, 'sha256': '97cc22bcbdacad741734ee836834e89bc782e90df075f2d89e440d7418f1610a'},
    'formal_result': {
        'path': DICT_RUN / 'RESULT.json',
        'published': 'dictionary-run/RESULT.json',
        'bytes': 44254, 'sha256': '5a1341c82adea857e1c9ccefd6bf4b76daa1e2c25bfc96083e7eca2938a073e9'},
}
READONLY = {
    'published': 'dictionary-readonly/ACTUAL_DICTIONARY_READONLY_RESULT.json',
    'bytes': 41802, 'sha256': 'f9eb58730d245143b566359c46f35d28d3700b5f07cf8e221dd56b58502d3af4'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def regular(path):
    need(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return path.read_bytes()


def pin_of(row):
    return {key: row[key] for key in ('bytes', 'sha256')}


def metadata(path):
    if not os.path.lexists(path):
        return None
    st = path.lstat()
    need(stat.S_ISREG(st.st_mode), 'nonregular protected input: ' + str(path))
    return [st.st_dev, st.st_ino, st.st_mode, st.st_size, st.st_mtime_ns, st.st_ctime_ns]


def dictionary_reference(v, c):
    """Read frozen receipts; do not execute the old Dictionary acceptance reader."""
    documents, retained = {}, {}
    for name, row in RECEIPTS.items():
        raw = regular(row['path'])
        need(fp(raw) == pin_of(row) and raw == v.git(EVIDENCE_COMMIT, EVIDENCE + row['published']),
             'original Dictionary receipt differs: ' + name)
        documents[name] = json.loads(raw)
        retained[str(row['path'])] = pin_of(row)
    readonly_raw = v.git(EVIDENCE_COMMIT, EVIDENCE + READONLY['published'])
    need(fp(readonly_raw) == pin_of(READONLY), 'published original Dictionary readonly receipt differs')
    readonly = json.loads(readonly_raw)
    formal = documents['formal_result']
    normal = documents['normal_pass']
    normal_context = documents['normal_context']
    full = documents['full_context']
    need(readonly['status'] == 'ORIGINAL_DICTIONARY_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION' and
         readonly['new_owner_accepted'] is True and readonly['normal_or_kernel_commands_executed'] == 0 and
         readonly['identity']['source_commit'] == DICTIONARY_COMMIT and
         readonly['identity']['new_owner'] == DICTIONARY and
         formal['identity'] == readonly['identity'] and formal['owner'] == readonly['owner'] and
         formal['new_owner_accepted'] is True and formal['worker_exit_code'] == 0 and
         formal['accepted_owners'] == [DICTIONARY] and not formal['failures'] and
         normal['dependency_context'] == normal_context and normal_context['source_commit'] == DICTIONARY_COMMIT,
         'original Dictionary identity or original success reference differs')
    need(len(normal_context['project_sources']) == 289 and
         len(normal_context['dependency_objects_and_traces']) == 576 and
         len(full['selected_live_sources']) == 289 and
         len(full['preserved_dependency_artifacts']) == 288 and
         sum(len(row) for row in full['preserved_dependency_artifacts'].values()) == 6048 and
         full['selected_live_sources'] == normal_context['project_sources'],
         'original complete D288 source/artifact inventory differs')
    owner = readonly['owner']['binding']
    return SimpleNamespace(documents=documents, readonly=readonly, owner=owner, retained=retained,
        reference={
            'source_acceptance_commit': DICTIONARY_COMMIT,
            'evidence_publication': EVIDENCE_COMMIT,
            'original_success': pin_of(RECEIPTS['formal_result']),
            'original_readonly': pin_of(READONLY),
            'original_normal_context': pin_of(RECEIPTS['normal_context']),
            'original_full_context': pin_of(RECEIPTS['full_context']),
            'dictionary_acceptance_replayed_here': False,
            'dependency_owners_reaccepted_here': False})


def dependency_spec(c, retained):
    raw = c.g.pinned(AG, c.g.MANIFEST, c.g.MANIFEST_SHA)
    manifest = json.loads(raw)
    rows = manifest['project_sources']
    graph = {m: row['imports'] for m, row in rows.items()}
    active = c.s.h.closure(graph, PROJECT_IMPORTS)
    normal = retained.documents['normal_context']
    full = retained.documents['full_context']
    need(len(active) == 40 and TARGET not in active and
         active <= set(full['preserved_dependency_artifacts']) and
         all(normal['project_sources'][m] == rows[m]['sha256'] for m in active),
         'actual Partition dependency closure is not the recorded forty-module subset')
    for m in active:
        stem = '.lake/build/lib/lean/' + m.replace('.', '/')
        need(all(full['preserved_dependency_artifacts'][m][stem + ext] ==
                 normal['dependency_objects_and_traces'][stem + ext] for ext in ('.olean', '.trace')),
             'recorded dependency object/trace identities disagree: ' + m)
        need(set(full['preserved_dependency_artifacts'][m]) == set(c.g.artifact_paths(m)),
             'incomplete recorded dependency artifact positions: ' + m)
    expected_graph = {m: graph[m] for m in active}
    live_graph, live = c.s.h.project_graph(PROJECT, PROJECT_IMPORTS)
    need(live_graph == expected_graph and
         {m: row['sha256'] for m, row in live.items()} == {m: rows[m]['sha256'] for m in active},
         'live Partition project dependency sources/imports differ')
    return SimpleNamespace(graph=expected_graph,
        sources={m: rows[m]['sha256'] for m in active}, active=active,
        dependency_pins={m: full['preserved_dependency_artifacts'][m] for m in active},
        review=c.review, retained_inputs=retained.retained,
        input_bindings={
            'original_dictionary_reference': retained.reference,
            'graph_commit': AG, 'graph_path': c.g.MANIFEST, 'graph_sha256': c.g.MANIFEST_SHA,
            'project_dependency_count': 40, 'dependency_artifact_positions': 840,
            'new_owner_accepted': False})


def load():
    raw = subprocess.check_output(['git', 'show', VARIATION_COMMIT + ':' + VARIATION_ADAPTER], cwd=REPO)
    need(fp(raw)['sha256'] == VARIATION_ADAPTER_SHA, 'original Variation reader pin differs')
    v = ModuleType('original_variation_reader')
    v.__file__ = str(ACCEPTANCE_ROOT / VARIATION_COMMIT / 'published-entrypoints/run_variation.py')
    exec(compile(raw, VARIATION_ADAPTER, 'exec'), v.__dict__)
    c = v.load(VARIATION_COMMIT)
    need((v.ROOT, v.REPO, v.PROJECT) == (ACCEPTANCE_ROOT, REPO, PROJECT), 'fixed environment differs')
    variation = v.check(c)
    need(variation['status'] == 'REVALIDATED', 'original Variation acceptance unavailable')
    source = regular(INPUT)
    original = v.git(SOURCE_BASE, SOURCE_PATH)
    need(fp(original) == {'bytes': ORIGINAL_SOURCE_BYTES, 'sha256': ORIGINAL_SOURCE_SHA}, 'original source pin differs')
    need(fp(source) == {'bytes': SOURCE_BYTES, 'sha256': SOURCE_SHA} and
         b''.join(source.split()) == b''.join(original.split()) and c.s.h.imports(source) == IMPORTS,
         'original complete Partition source/header/import bytes differ')
    retained = dictionary_reference(v, c)
    spec = dependency_spec(c, retained)
    return SimpleNamespace(v=v, c=c, source=source, retained=retained, spec=spec, variation=variation)


def target_state(x):
    c = x.c
    roots = [p / TARGET for p in ACCEPTANCE_ROOT.iterdir()
             if p.is_dir() and re.fullmatch('[0-9a-f]{40}', p.name) and os.path.lexists(p / TARGET)]
    need(not roots, 'existing target owner requires inspection; never rerun it')
    c.g.require_fresh_owner(TARGET, c.g.module_artifacts(c.s, TARGET))
    path = PROJECT / SOURCE_PATH
    source = regular(path) if os.path.lexists(path) else None
    need(source is None or source == x.source, 'foreign installed target source')
    stem = PROJECT / '.lake/build/lib/lean' / TARGET.replace('.', '/')
    for ext in ('.trace.nobuild', '.ir.sig.hash'):
        need(not os.path.lexists(Path(str(stem) + ext)), 'partial target artifact: ' + ext)
    return {'live_source': None if source is None else fp(source), 'owner_history': [],
            'artifacts': c.g.module_artifacts(c.s, TARGET)}


def full_dictionary_metadata(x):
    full = x.retained.documents['full_context']
    paths = {PROJECT / x.c.s.h.module_path(m) for m in full['selected_live_sources']}
    for row in full['preserved_dependency_artifacts'].values():
        paths.update(PROJECT / rel for rel in row)
    paths.update(PROJECT / rel for rel in x.retained.owner['all_observed_target_artifacts'])
    paths.update(Path(p) for p in full['retained_original_evidence'])
    paths.update(Path(p) for p in x.retained.retained)
    # --no-build may create a trace.nobuild sidecar on a failed readiness query.
    for m in full['selected_live_sources']:
        stem = PROJECT / '.lake/build/lib/lean' / m.replace('.', '/')
        paths.add(Path(str(stem) + '.trace.nobuild'))
        paths.add(Path(str(stem) + '.ir.sig.hash'))
    return {str(p): metadata(p) for p in sorted(paths)}


def native_input(x):
    base = PROJECT / '.lake/packages/mathlib'
    rel = MATHLIB_IMPORT.replace('.', '/')
    source = base / (rel + '.lean')
    stem = base / '.lake/build/lib/lean' / rel
    required = (source, Path(str(stem) + '.olean'), Path(str(stem) + '.trace'))
    pins = {str(p): fp(regular(p)) for p in required}
    suffixes = ('.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
                '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash',
                '.trace', '.trace.nobuild', '.ir', '.ir.hash', '.ir.sig', '.ir.sig.hash')
    return {'required_existing_inputs': pins,
            'metadata': {str(Path(str(stem) + ext)): metadata(Path(str(stem) + ext)) for ext in suffixes}}


def fixed(x):
    c = x.c
    # Reuse the original snapshot API for precise new-input pins, not for a new acceptance.
    dependencies = c.g.snapshot(c.s, x.spec)
    need(c.g.file_binding(PROJECT / c.s.h.module_path(DICTIONARY)) ==
         x.retained.documents['normal_context']['project_sources'][DICTIONARY],
         'original Dictionary owner source differs')
    need(c.g.module_artifacts(c.s, DICTIONARY) == x.retained.owner['all_observed_target_artifacts'],
         'original Dictionary owner artifacts differ')
    variation = x.v.check(c)
    need(variation == x.variation, 'original Variation readonly identity changed')
    return {'actual_dependency_context': dependencies,
            'dictionary_all_source_and_artifact_metadata': full_dictionary_metadata(x),
            'dictionary_acceptance_reference': x.retained.reference,
            'variation': x.v.accepted(c), 'existing_owners': x.v.fixed(c),
            'native_direct_import': native_input(x), 'target': target_state(x)}


def summary(x, result):
    return {'schema': result['schema'], 'run': str(RUN), 'target': TARGET,
            'source_sha256': SOURCE_SHA, 'exit_code': result['exit_code'],
            'probe_passed': result['probe_passed'], 'preservation_passed': result['preservation_passed'],
            'project_dependency_count': 40, 'new_formal_credit': 0,
            'whole_P1_5_complete': False}


def relay_original_log_tail():
    # Reading a bounded view does not alter the complete original log or its receipt.
    for name in ('probe.log', 'serialized-probe.log'):
        path = RUN / name
        if os.path.lexists(path):
            tail = regular(path).decode('utf-8', errors='replace')[-24000:]
            print('ORIGINAL_LOG_TAIL_BEGIN ' + name, flush=True)
            print(tail, end='' if tail.endswith('\n') else '\n', flush=True)
            print('ORIGINAL_LOG_TAIL_END ' + name, flush=True)
            return


def worker(x):
    c = x.c
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__) == RUN / 'probe_driver.py' and RUN.resolve() == RUN, 'unexpected worker route')
    need(c.s.api.read_json(RUN / 'GIT_BEFORE.json') == c.s.d.original_git_state(REPO),
         'checkout changed before worker')
    need(regular(RUN / NAME) == x.source, 'frozen probe source differs')
    before = fixed(x)
    c.s.d.save(RUN / 'PRESERVED_BEFORE.json', before)
    result = {'schema': 'p15_signed_exit_partition_no_output_probe_v1',
        'target': TARGET, 'source_base': SOURCE_BASE, 'source_path': SOURCE_PATH,
        'source_sha256': SOURCE_SHA, 'source_bytes': SOURCE_BYTES,
        'original_source_unchanged': False, 'nonwhitespace_source_unchanged': True,
        'original_source_sha256': ORIGINAL_SOURCE_SHA, 'previous_failure': PREVIOUS_FAILURE,
        'dictionary_reference': x.retained.reference,
        'variation_original_acceptance': x.variation,
        'project_dependency_count': 40, 'dependency_artifact_positions': 840,
        'protected_dictionary_sources': 289, 'protected_dictionary_dependency_artifact_positions': 6048,
        'direct_imports': IMPORTS, 'direct_import_readiness': None, 'command': None,
        'exit_code': 3, 'probe_passed': False, 'preservation_passed': False,
        'output_object_requested': False, 'new_owner_accepted': False,
        'new_formal_credit': 0, 'whole_P1_5_complete': False}
    try:
        ready = SimpleNamespace(manifest={'project_sources': {TARGET: {'all_imports': IMPORTS}}})
        result['direct_import_readiness'] = c.g.direct_import_readiness(c.s, ready, TARGET, RUN)
        need(fixed(x) == before, 'direct-import no-build query changed protected inputs')
        cmd = c.s.ops.run(RUN, 'probe',
            c.s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(RUN / NAME)]),
            cwd=PROJECT, relay=True)
        result['command'] = cmd
        need(not cmd['actual_built_modules'] and not cmd['actual_failed_modules'],
             'probe attempted a dependency build')
        result['exit_code'] = cmd['exit_code']
    except Exception as error:
        result['probe_error'] = str(error)
    finally:
        try:
            after = fixed(x)
            c.s.d.save(RUN / 'PRESERVED_AFTER.json', after)
            need(before == after, 'protected source/artifact/acceptance state changed')
            need(all(not list(RUN.glob(pattern)) for pattern in
                     ('*.olean*', '*.ilean*', '*.c', '*.o', '*.bc', '*.ir', '*.trace*')),
                 'no-output probe produced an object')
            result['preservation_passed'] = True
        except Exception as error:
            result['preservation_error'] = str(error)
    result['probe_passed'] = (result['exit_code'] == 0 and result['preservation_passed'] and
                              not result.get('probe_error') and not result.get('preservation_error'))
    if not result['probe_passed'] and result['exit_code'] == 0:
        result['exit_code'] = 3
    c.s.d.save(RUN / 'PROBE_RESULT.json', result)
    print(json.dumps(summary(x, result), sort_keys=True), flush=True)
    return result['exit_code']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker', action='store_true')
    args = parser.parse_args()
    x = load()
    if args.worker:
        return worker(x)
    target_state(x)
    need(RUN.resolve() == RUN, 'symlink in new probe route')
    RUN.mkdir(parents=True, exist_ok=False)
    x.c.s.d.write_frozen(RUN / 'probe_driver.py', regular(Path(__file__)))
    x.c.s.d.write_frozen(RUN / NAME, x.source)
    before = x.c.s.d.original_git_state(REPO)
    x.c.s.d.save(RUN / 'GIT_BEFORE.json', before)
    try:
        cmd = x.c.s.ops.run(RUN, 'serialized-probe',
            x.c.s.h.serialize(0, RUN / 'LANE.json',
                ['python3', '-B', str(RUN / 'probe_driver.py'), '--worker']), cwd=PROJECT, relay=True)
    finally:
        after = x.c.s.d.original_git_state(REPO)
        x.c.s.d.save(RUN / 'GIT_AFTER.json', after)
        relay_original_log_tail()
        need(before == after, 'original checkout Git state changed')
    result = x.c.s.api.read_json(RUN / 'PROBE_RESULT.json')
    need(not cmd['actual_built_modules'] and not cmd['actual_failed_modules'] and
         result['exit_code'] == cmd['exit_code'], 'serialized probe command scope or terminal status differs')
    print(json.dumps({**summary(x, result), 'result': fp(regular(RUN / 'PROBE_RESULT.json'))}, sort_keys=True), flush=True)
    return cmd['exit_code']


if __name__ == '__main__':
    raise SystemExit(main())
