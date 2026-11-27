"""UNBOUND formal adapter for one original PolicyComparison owner.

No operation is allowed before actual probe inputs are bound.  Reuse the
published Partition acceptance at 7296 and its forty existing dependencies;
only PolicyComparison may receive a new normal/full-owned/kernel acceptance.
Its complete original mathematical source is immutable, including proof bodies.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
INPUTS = None
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PUBLICATION_PARENT = '19f493948737f6f5f7bc5e858d5266b41f976b22'
SOURCE_COMMIT = '040d46058821746c69c5183b3f6c22792287c4ba'
PARTITION_COMMIT = '7296a9659fbf34773ec03f437860c14073b3a638'
PARTITION = 'ImbalancedChen.P1SignedExitPartition'
TARGET = 'ImbalancedChen.P1SignedExitPolicyComparison'
NAME = 'P1SignedExitPolicyComparison.lean'
LIVE = 'ImbalancedChen/' + NAME
PACKET = 'docs/p1/20261127/p15-signed-exit-policy-comparison'
SOURCE_PIN = {'bytes': 17805, 'sha256': 'c60992855b519d9767e66f31c9007dd18f2292e326e28539fc2a39d1d831b57f'}
IMPORTS = [PARTITION]
SUPPORT = PACKET + '/support/probe_policy_v1.py'
SUPPORT_PIN = {'bytes': 12998, 'sha256': '1b0915e36b854e8f4e92c46e1bb9d9578013c8d74ace08331dc925c24af3e167'}
PROBE_JOB = 'job_fa097654baec4780b96c1831b24d3c85'
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-signed-exit-policy-probe-v1')
PROBE_RUN = PROBE_ROOT / SOURCE_PIN['sha256'] / 'attempt-00000'
PROBE_FILES = (
    'PROBE_RESULT.json', NAME, 'probe_driver.py',
    'probe-command.json', 'probe-started.json', 'probe.log',
    'serialized-probe-command.json', 'serialized-probe-started.json', 'serialized-probe.log',
    'LANE.json', 'PRESERVED_BEFORE.json', 'PRESERVED_AFTER.json',
    'GIT_BEFORE.json', 'GIT_AFTER.json',
    TARGET + '/direct-import-stock-readiness-command.json',
    TARGET + '/direct-import-stock-readiness-started.json',
    TARGET + '/direct-import-stock-readiness.log',
)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def regular(path):
    need(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return path.read_bytes()


def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def validate_inputs():
    # First gate: no project filesystem, Git, helper or compiler operation before binding.
    need(isinstance(INPUTS, dict), 'UNBOUND: complete original PolicyComparison probe inputs required')
    need(set(INPUTS) == {'probe'} and isinstance(INPUTS['probe'], dict), 'unexpected formal input shape')
    row = INPUTS['probe']
    need(set(row) == {'job_id', 'directory', 'files'} and row['job_id'] == PROBE_JOB and
         row['directory'] == str(PROBE_RUN) and isinstance(row['files'], dict) and
         set(row['files']) == set(PROBE_FILES), 'incomplete original probe identity/file inventory')
    for name, pin in row['files'].items():
        need(isinstance(pin, dict) and set(pin) == {'bytes', 'sha256'} and
             type(pin['bytes']) is int and pin['bytes'] > 0 and
             isinstance(pin['sha256'], str) and re.fullmatch('[0-9a-f]{64}', pin['sha256']),
             'incomplete original probe file pin: ' + name)
    need(row['files'][NAME] == SOURCE_PIN and row['files']['probe_driver.py'] == SUPPORT_PIN,
         'original source or reviewed probe driver differs')


def verify_source(raw):
    need(fingerprint(raw) == SOURCE_PIN, 'any change to original PolicyComparison source is forbidden')
    need(re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', raw.decode()) is None,
         'forbidden proof escape in original source')


def command_record(record, log_raw, expected_argv, expected_log, allowed=()):
    need(record['argv'] == expected_argv and record['cwd'] == str(PROJECT) and
         record['exit_code'] == 0 and record['actual_failed_modules'] == [] and
         set(record['actual_built_modules']) <= set(allowed) and
         record['project_error_count'] == 0 and record['log'] == str(expected_log) and
         fingerprint(log_raw) == {'bytes': record['log_bytes'], 'sha256': record['log_sha256']},
         'original command scope, completion or log identity differs')
    return record


def verify_probe_scope(result, readonly, parent_binding):
    need(result['schema'] == 'p15_policy_comparison_no_output_probe_v1' and
         result['target'] == TARGET and result['source_commit'] == SOURCE_COMMIT and
         result['source_path'] == LIVE and result['source'] == SOURCE_PIN and
         result['original_source_unchanged'] is True and result['direct_imports'] == IMPORTS and
         result['project_dependency_count'] == 41 and result['exit_code'] == 0 and
         result['probe_passed'] is True and result['preservation_passed'] is True and
         result['output_object_requested'] is False and result['new_owner_accepted'] is False and
         result['new_formal_credit'] == 0 and result['whole_P1_5_complete'] is False and
         result['partition_original_identity'] == readonly and
         result['partition_original_receipt_bindings'] == parent_binding and
         not result.get('probe_error') and not result.get('preservation_error'),
         'original probe source, parent acceptance or terminal scope differs')


def verify_finished_lane(lane, worker_argv, state, state_sha256):
    need(lane['status'] == 'VALIDATION_LANE_FINISHED' and lane['exit_code'] == 0 and
         lane['argv'] == worker_argv and lane['state'] == state and
         lane['state_sha256'] == state_sha256 and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True,
         'original outer serializer/lane is incomplete or misbound')


def retained_inputs(c):
    x, pc = c.x, c.x.c
    owner = x.parent.accepted(pc)
    need(pc.g.module_artifacts(pc.s, PARTITION) == owner['binding']['all_observed_target_artifacts'] and
         pc.g.file_binding(PROJECT / pc.s.h.module_path(PARTITION)) ==
             c.support.PARTITION_SOURCE_SHA, 'original Partition source/artifacts differ')
    stem = PROJECT / '.lake/build/lib/lean' / PARTITION.replace('.', '/')
    return {'original_inputs': x.parent.fixed(pc), 'original_partition_owner': owner,
        'partition_extra_metadata': {ext: pc.support.metadata(Path(str(stem) + ext))
                                    for ext in ('.trace.nobuild', '.ir.sig.hash')},
        'parent_receipts': {k: c.support.receipt(v) for k, v in c.support.PARTITION_BINDING.items()}}


def require_same_stable_inputs(recorded, current):
    old, new = recorded['original_inputs'], current['original_inputs']
    need(all(old[k] == new[k] for k in
             ('actual_dependency_context', 'dictionary_acceptance_reference', 'variation')) and
         old['native_direct_import']['required_existing_inputs'] ==
             new['native_direct_import']['required_existing_inputs'] and
         old['existing_owners']['environment'] == new['existing_owners']['environment'] and
         all(recorded[k] == current[k] for k in
             ('original_partition_owner', 'partition_extra_metadata', 'parent_receipts')),
         'original dependency content, parent acceptance or runtime changed')


def verified_probe(c):
    need(PROBE_RUN.resolve() == PROBE_RUN, 'unexpected original probe route')
    raw = {}
    for rel in PROBE_FILES:
        data = regular(PROBE_RUN / rel)
        need(fingerprint(data) == INPUTS['probe']['files'][rel] and
             data == git(c.commit, PACKET + '/probe/' + rel),
             'original probe bytes differ from exact publication: ' + rel)
        raw[rel] = data
    need(raw[NAME] == c.source and raw['probe_driver.py'] == c.support_raw,
         'original successful probe used another source or driver')
    result = json.loads(raw['PROBE_RESULT.json'])
    verify_probe_scope(result, c.x.readonly, c.support.PARTITION_BINDING)
    s = c.s
    inner_argv = s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(PROBE_RUN / NAME)])
    direct_argv = s.h.guard(0, ['lake', '--no-build', 'build', '+' + PARTITION + ':olean'])
    worker_argv = ['python3', '-B', str(PROBE_RUN / 'probe_driver.py'), '--worker']
    outer_argv = s.h.serialize(0, PROBE_RUN / 'LANE.json', worker_argv)
    records = {}
    for name, argv in (('probe', inner_argv),
                       (TARGET + '/direct-import-stock-readiness', direct_argv),
                       ('serialized-probe', outer_argv)):
        record = command_record(json.loads(raw[name + '-command.json']), raw[name + '.log'],
                                argv, PROBE_RUN / (name + '.log'))
        started = json.loads(raw[name + '-started.json'])
        need(started['argv'] == record['argv'] and started['cwd'] == record['cwd'] and
             started['started_utc'] == record['started_utc'], 'original started/finished command mismatch')
        records[name] = record
    need(result['command'] == records['probe'] and result['direct_import_readiness'] ==
         records[TARGET + '/direct-import-stock-readiness'], 'original result command differs')
    lane = json.loads(raw['LANE.json'])
    state = outer_argv[outer_argv.index('--state') + 1]
    verify_finished_lane(lane, worker_argv, state, fingerprint(regular(Path(state)))['sha256'])
    need(raw['PRESERVED_BEFORE.json'] == raw['PRESERVED_AFTER.json'] and
         raw['GIT_BEFORE.json'] == raw['GIT_AFTER.json'], 'original probe preservation failed')
    before = json.loads(raw['PRESERVED_BEFORE.json'])
    need(before['new_target']['source'] in (None, SOURCE_PIN) and
         all(value is None for value in before['new_target']['artifacts'].values()),
         'probe original target was not fresh')
    require_same_stable_inputs(before, retained_inputs(c))
    observed = set()
    for root in PROBE_ROOT.parent.glob('20261127-p15-signed-exit-policy-probe-v*'):
        need(root.is_dir() and root.resolve() == root, 'unexpected policy probe history root')
        for source in root.iterdir():
            need(source.is_dir() and re.fullmatch('[0-9a-f]{64}', source.name) and source.resolve() == source,
                 'unexpected policy probe source history')
            for attempt in source.iterdir():
                need(attempt.is_dir() and re.fullmatch('attempt-[0-9]{5}', attempt.name) and
                     attempt.resolve() == attempt, 'unexpected policy probe attempt history')
                observed.add(str(attempt))
    need(observed == {str(PROBE_RUN)}, 'unreviewed prior/partial policy probe exists; preserve and inspect')
    return {'job_id': PROBE_JOB, 'directory': str(PROBE_RUN),
            'files': INPUTS['probe']['files'], 'outer_completion_verified': True,
            'formal_credit_from_probe': 0}


def load(commit):
    validate_inputs()
    need(isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit) and
         commit not in (PUBLICATION_PARENT, SOURCE_COMMIT, PARTITION_COMMIT), 'new exact publication required')
    runner = git(commit, PACKET + '/run_policy.py')
    need(runner == regular(Path(__file__)), 'executed formal adapter differs from publication')
    support_raw = git(commit, SUPPORT)
    need(fingerprint(support_raw) == SUPPORT_PIN, 'reviewed original probe input helper differs')
    support = ModuleType('original_policy_probe_inputs')
    support.__file__ = SUPPORT
    exec(compile(support_raw, SUPPORT, 'exec'), support.__dict__)
    need((support.REPO, support.PROJECT, support.ACCEPTANCE_ROOT, support.TARGET) ==
         (REPO, PROJECT, ROOT, TARGET) and support.PARTITION_COMMIT == PARTITION_COMMIT,
         'original probe roots/parent/target differ')
    x = support.load()
    pc = x.c
    source = git(commit, PACKET + '/' + NAME)
    verify_source(source)
    need(source == x.source == git(SOURCE_COMMIT, LIVE) == git(commit, LIVE) and
         pc.s.h.imports(source) == IMPORTS, 'canonical/original mathematical source changed')
    for rel in ('ImbalancedChen/P1SignedExitPartition.lean',
                'ImbalancedChen/P5OriginalGroupLogAbelVariation.lean'):
        need(git(commit, rel) == git(PUBLICATION_PARENT, rel), 'unrelated accepted canonical source changed')
    graph = {**pc.spec.graph, TARGET: list(IMPORTS)}
    sources = {**pc.spec.sources, TARGET: SOURCE_PIN['sha256']}
    need(len(pc.spec.graph) == 41 and TARGET not in pc.spec.graph and
         len(graph) == len(sources) == 42 and pc.s.h.closure(graph, [TARGET]) == set(graph),
         'formal graph is not exactly original forty plus Partition plus PolicyComparison')
    spec = SimpleNamespace(graph=graph, sources=sources,
        manifest={'project_sources': {TARGET: {'all_imports': list(IMPORTS)}}})
    base = ROOT / commit
    c = SimpleNamespace(support=support, support_raw=support_raw, x=x, g=pc.g, s=pc.s,
        spec=spec, source=source, runner=runner, base=base, commit=commit,
        run=base / 'signed-exit-policy-operation')
    c.public_source_names = ['ImbalancedChen.' + name for private, kind, name in
        re.findall(r'^(private )?(def|theorem) (\w+)\b', source.decode(), re.MULTILINE) if not private]
    c.ident = {'commit': commit, 'module': TARGET, 'source_origin_commit': SOURCE_COMMIT,
        'source': SOURCE_PIN, 'mathematical_source_unchanged': True,
        'publication_parent': PUBLICATION_PARENT, 'publication': PACKET + '/' + NAME,
        'partition_original_acceptance': x.readonly,
        'partition_original_receipt_bindings': support.PARTITION_BINDING,
        'actual_project_dependencies': 41, 'formal_graph_sources': 42,
        'adapter_sha256': fingerprint(runner)['sha256'], 'probe_helper': SUPPORT_PIN,
        'probe': verified_probe(c), 'whole_P1_5_complete': False}
    return c


def fixed(c):
    result = retained_inputs(c)
    result['retained_probe_evidence'] = {rel: fingerprint(regular(PROBE_RUN / rel)) for rel in PROBE_FILES}
    need(result['retained_probe_evidence'] == INPUTS['probe']['files'], 'retained original probe files changed')
    return result


def owner_roots():
    return sorted(p / TARGET for p in ROOT.iterdir() if p.is_dir() and
                  re.fullmatch('[0-9a-f]{40}', p.name) and os.path.lexists(p / TARGET))


def fresh(c):
    need(not owner_roots(), 'prior/partial PolicyComparison owner found; preserve and inspect without rerun')
    c.g.require_fresh_owner(TARGET, c.g.module_artifacts(c.s, TARGET))
    stem = PROJECT / '.lake/build/lib/lean' / TARGET.replace('.', '/')
    need(all(not os.path.lexists(Path(str(stem) + ext)) for ext in ('.trace.nobuild', '.ir.sig.hash')),
         'partial extra PolicyComparison artifact')
    path = PROJECT / LIVE
    source = regular(path) if os.path.lexists(path) else None
    need(source is None or source == c.source, 'foreign or modified PolicyComparison installation')
    return source


def accepted(c):
    need(owner_roots() == [c.base / TARGET], 'owner missing or competing prior owner exists')
    old = c.g.existing_owner(c.s, c.commit, c.spec, TARGET)
    c.g.require_completed_existing_owner(c.s, c.commit, c.spec, TARGET, old)
    folders = list((c.base / TARGET / 'audits').iterdir())
    need(len(folders) == 1, 'expected one immutable complete-owned audit')
    validation = c.s.api.read_json(folders[0] / 'lane-0/VALIDATION_RESULTS.json')
    exports = c.s.api.read_json(folders[0] / 'lane-0/OWNED_EXPORTS.json')
    need(validation['only_standard_axioms'] is True and
         validation['full_owned_including_private_generated'] is True and
         validation['total_owned_exports'] == len(exports) and
         validation['total_public_exports'] == sum(not row['is_private'] for row in exports),
         'incomplete owned/private audit or nonstandard axioms')
    public = {row['name'] for row in exports if not row['is_private']}
    need(set(c.public_source_names) <= public, 'original public source declaration missing from owned audit')
    return {'owned': validation['total_owned_exports'], 'public': validation['total_public_exports'],
        'axioms': sorted({axiom for row in exports for axiom in row['axioms']}),
        'binding': c.g.acceptance_binding(c.s, c.commit, TARGET)}


def install(c, prior):
    path = PROJECT / LIVE
    need(path.parent.resolve() == path.parent, 'unexpected source-parent symlink')
    c.s.d.write_frozen(c.run / 'original-published.lean', c.source)
    if prior is not None:
        c.s.d.write_frozen(c.run / 'original-installed.lean', prior)
        need(regular(path) == c.source, 'existing exact source changed before formal run')
    else:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.policy-install-', delete=False) as stream:
            temporary = Path(stream.name)
            try:
                os.fchmod(stream.fileno(), 0o644)
                stream.write(c.source)
                stream.flush()
                os.fsync(stream.fileno())
                os.link(temporary, path)
            finally:
                temporary.unlink(missing_ok=True)
        descriptor = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    need(regular(path) == c.source, 'installed original source differs')
    c.s.d.save(c.run / 'INSTALL.json', {'identity': c.ident, 'original_present': prior is not None})


def worker(c):
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__) == c.run / 'executed.py' and c.run.resolve() == c.run, 'unexpected formal worker route')
    need(c.s.api.read_json(c.run / 'GIT_BEFORE.json') == c.s.d.original_git_state(REPO),
         'original Git state changed before worker')
    before = fixed(c)
    c.s.d.save(c.run / 'PRESERVED_BEFORE.json', before)
    try:
        prior = fresh(c)
        stock = c.g.direct_import_readiness(c.s, c.spec, TARGET, c.run)
        need(fixed(c) == before and fresh(c) == prior, 'no-build readiness changed original inputs')
        install(c, prior)
        c.g.run_owner(c.s, c.commit, c.base, c.run, TARGET, c.spec.graph, c.spec.sources)
        owner = accepted(c)
    finally:
        after = fixed(c)
        c.s.d.save(c.run / 'PRESERVED_AFTER.json', after)
        need(before == after, 'formal operation changed accepted dependencies or original evidence')
    c.s.d.save(c.run / 'WORKER_PASS.json', {'identity': c.ident, 'owner': owner, 'native_stock': stock})


def command(c, name, expected, allowed=()):
    log = c.run / (name + '.log')
    return command_record(c.s.api.read_json(c.run / (name + '-command.json')),
                          regular(log), expected, log, allowed)


def dispatch(c):
    fresh(c)
    need(c.run.resolve() == c.run, 'unexpected formal operation route')
    c.run.mkdir(parents=True, exist_ok=False)
    c.s.d.write_frozen(c.run / 'executed.py', c.runner)
    before = c.s.d.original_git_state(REPO)
    c.s.d.save(c.run / 'GIT_BEFORE.json', before)
    try:
        outer = c.s.ops.run(c.run, 'serialized-policy', c.s.h.serialize(0, c.run / 'LANE.json',
            ['python3', '-B', str(c.run / 'executed.py'), '--source-commit', c.commit, '--worker']),
            cwd=PROJECT, relay=True)
        need(outer['exit_code'] == 0 and outer['actual_failed_modules'] == [] and
             set(outer['actual_built_modules']) <= {TARGET}, 'formal serialized scope/status differs')
        passed = c.s.api.read_json(c.run / 'WORKER_PASS.json')
        need(passed['identity'] == c.ident and passed['owner'] == accepted(c), 'incomplete original worker evidence')
    finally:
        after = c.s.d.original_git_state(REPO)
        c.s.d.save(c.run / 'GIT_AFTER.json', after)
        need(before == after, 'original dirty checkout Git state changed')
    c.s.d.save(c.run / 'PASS.json', {'identity': c.ident,
        'worker': c.s.d.fingerprint(c.run / 'WORKER_PASS.json'), 'command': outer,
        'preserved': c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json')})


def check(c):
    need(c.run.resolve() == c.run, 'unexpected operation symlink')
    if not os.path.lexists(c.run):
        prior = fresh(c)
        fixed(c)
        return {'status': 'FRESH', 'identity': c.ident, 'original_source_present': prior is not None,
                'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}
    read = c.s.api.read_json
    need((c.run / 'PASS.json').is_file(), 'partial/failed formal operation; preserve and inspect')
    passed, installed = read(c.run / 'PASS.json'), read(c.run / 'INSTALL.json')
    need(regular(c.run / 'executed.py') == c.runner and regular(c.run / 'original-published.lean') == c.source and
         passed['identity'] == installed['identity'] == c.ident and
         type(installed['original_present']) is bool and
         passed['worker'] == c.s.d.fingerprint(c.run / 'WORKER_PASS.json'), 'formal provenance differs')
    backup = c.run / 'original-installed.lean'
    need(regular(backup) == c.source if installed['original_present'] else not os.path.lexists(backup),
         'original source preservation differs')
    worker_result = read(c.run / 'WORKER_PASS.json')
    need(worker_result['identity'] == c.ident and worker_result['owner'] == accepted(c),
         'actual original owned acceptance differs')
    need(read(c.run / 'GIT_BEFORE.json') == read(c.run / 'GIT_AFTER.json') and
         passed['preserved'] == c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json') ==
         c.s.d.fingerprint(c.run / 'PRESERVED_AFTER.json'), 'original operation preservation differs')
    recorded, current = read(c.run / 'PRESERVED_BEFORE.json'), fixed(c)
    require_same_stable_inputs(recorded, current)
    need(recorded['retained_probe_evidence'] == current['retained_probe_evidence'], 'original probe evidence changed')
    worker_argv = ['python3', '-B', str(c.run / 'executed.py'), '--source-commit', c.commit, '--worker']
    outer_argv = c.s.h.serialize(0, c.run / 'LANE.json', worker_argv)
    outer = command(c, 'serialized-policy', outer_argv, {TARGET})
    direct = command(c, TARGET + '/direct-import-stock-readiness',
        c.s.h.guard(0, ['lake', '--no-build', 'build', '+' + PARTITION + ':olean']))
    need(outer == passed['command'] and direct == worker_result['native_stock'], 'original formal command differs')
    lane = read(c.run / 'LANE.json')
    state = outer_argv[outer_argv.index('--state') + 1]
    verify_finished_lane(lane, worker_argv, state, fingerprint(regular(Path(state)))['sha256'])
    return {'status': 'REVALIDATED', 'identity': c.ident,
            'owner': {k: v for k, v in worker_result['owner'].items() if k != 'binding'},
            'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}


def main():
    validate_inputs()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ('run', 'check', 'worker'):
        mode.add_argument('--' + name, action='store_true')
    args = parser.parse_args()
    c = load(args.source_commit)
    if args.worker:
        worker(c)
    else:
        if args.run:
            dispatch(c)
        print(json.dumps(check(c), sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
