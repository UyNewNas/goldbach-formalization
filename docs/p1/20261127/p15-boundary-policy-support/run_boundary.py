#!/usr/bin/env python3
"""Accept only the selected Boundary repair after its actual successful probe.

All 56 dependencies retain their original source/object identities. The pinned
owner API performs normal compilation, kernel replay and complete-owned type
and axiom audit, including private/generated declarations. Actual probe pins
must be bound before any environment or compiler operation is permitted.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PACKET = 'docs/p1/20261127/p15-boundary-policy-support'
TARGET = 'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport'
NAME = 'P1HistoricalBoundaryPolicyDifferenceSupport.lean'
LIVE = 'ImbalancedChen/' + NAME
SOURCE_PIN = {'bytes': 20356, 'sha256': '38aec5706c23b20e6893223767f13101254f90058f1d554c445a186dc56c1a46'}
IMPORTS = ['ImbalancedChen.P1SignedExitCoefficientDifference',
           'ImbalancedChen.FirstExitValidSelection', 'ImbalancedChen.HistoricalPrefixCertificate']
PROBE_RUN = (Path('/workspace/p1-complete-proof/20261127-p15-boundary-policy-probe-v1') /
             SOURCE_PIN['sha256'] / 'attempt-00000')
PROBE = {'directory': '/workspace/p1-complete-proof/20261127-p15-boundary-policy-probe-v1/38aec5706c23b20e6893223767f13101254f90058f1d554c445a186dc56c1a46/attempt-00000',
 'files': {'GIT_AFTER.json': {'bytes': 1157,
                              'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
           'GIT_BEFORE.json': {'bytes': 1157,
                               'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
           'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport/direct-import-stock-readiness-command.json': {'bytes': 1070,
                                                                                                                     'sha256': 'e01e5a4e96182f23a689f4c3027bfdc2216dc6461fec97b9005fc71caf93cf2e'},
           'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport/direct-import-stock-readiness-started.json': {'bytes': 479,
                                                                                                                     'sha256': 'a572b001a573a7be32bf2151a7014a03f867b7e083c891c0831e4e25430a0258'},
           'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport/direct-import-stock-readiness.log': {'bytes': 150527,
                                                                                                            'sha256': 'fbe5c48f85b6259072fb26db06c3380e515f5d4afe786abe6cee8292fc1b3713'},
           'LANE.json': {'bytes': 1285,
                         'sha256': 'd6e52b35a8526940760b5d6099faf9df93083b94bb767ba7d49e569db46e8940'},
           'P1HistoricalBoundaryPolicyDifferenceSupport.lean': {'bytes': 20356,
                                                                'sha256': '38aec5706c23b20e6893223767f13101254f90058f1d554c445a186dc56c1a46'},
           'PRESERVED_AFTER.json': {'bytes': 9205,
                                    'sha256': '592925c611d9b34b53d4fcdbc0ccaebb3c9bdbc079102fb2a5783bb5dbac486d'},
           'PRESERVED_BEFORE.json': {'bytes': 9205,
                                     'sha256': '592925c611d9b34b53d4fcdbc0ccaebb3c9bdbc079102fb2a5783bb5dbac486d'},
           'PROBE_RESULT.json': {'bytes': 5356,
                                 'sha256': '352a27703e177972e1cc7416c70662b2bfd99288b43076b2ca9500d4ff708656'},
           'TARGET_AFTER.json': {'bytes': 2126,
                                 'sha256': 'bd8d35c24de380259c3dac9f900dd0913db43994a6d228dba7b5545d68cc8c3d'},
           'TARGET_BEFORE.json': {'bytes': 2126,
                                  'sha256': 'bd8d35c24de380259c3dac9f900dd0913db43994a6d228dba7b5545d68cc8c3d'},
           'probe-command.json': {'bytes': 1023,
                                  'sha256': 'e83fc4837f0f1d9e4da602a91c0de07f91bedc568c4e137cd585a0398926e037'},
           'probe-started.json': {'bytes': 518,
                                  'sha256': 'a08a58a4d5bfe8c908fe3d02c2ed12ddda8a7ec51283c9b2d50a7433e3c908e4'},
           'probe.log': {'bytes': 103,
                         'sha256': '4311c76b27e36dbaf85d7697f2d169aa20e0f6e4b44897c10aaa55bdfb491336'},
           'probe_driver.py': {'bytes': 8153,
                               'sha256': '655cbf0063675637a8338a08fcfe9d43f2f8721b1889636af54c142b1ad36e22'},
           'serialized-probe-command.json': {'bytes': 1256,
                                             'sha256': '42993654586d4f3f8dd3dddac463ae8e8815cc38e3fbca8a5b334ff9134f622a'},
           'serialized-probe-started.json': {'bytes': 738,
                                             'sha256': '8cb6c3addfd05cf1a9450fc06582cf86064fb8f82cade8c12107e24324d9b543'},
           'serialized-probe.log': {'bytes': 5649,
                                    'sha256': '97c6ea5f952644d5ccb5f8308719d8ceae8eb6b48a1003891bbfb8797727ae30'}},
 'source_commit': 'f8c9aa12aab3306960454b98c1517f968edc735f'}
PROBE_NAMES = {
    NAME, 'probe_driver.py', 'PROBE_RESULT.json', 'LANE.json',
    'GIT_BEFORE.json', 'GIT_AFTER.json', 'PRESERVED_BEFORE.json', 'PRESERVED_AFTER.json',
    'TARGET_BEFORE.json', 'TARGET_AFTER.json',
    'probe-command.json', 'probe-started.json', 'probe.log',
    'serialized-probe-command.json', 'serialized-probe-started.json', 'serialized-probe.log',
    TARGET + '/direct-import-stock-readiness-command.json',
    TARGET + '/direct-import-stock-readiness-started.json',
    TARGET + '/direct-import-stock-readiness.log'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def regular(path):
    need(path.is_file() and not path.is_symlink() and path.resolve() == path,
         'expected original regular file: ' + str(path))
    return path.read_bytes()


def validate_binding():
    need(isinstance(PROBE, dict) and set(PROBE) == {'source_commit', 'directory', 'files'} and
         isinstance(PROBE['source_commit'], str) and re.fullmatch('[0-9a-f]{40}', PROBE['source_commit']) and
         PROBE['directory'] == str(PROBE_RUN) and isinstance(PROBE['files'], dict) and
         set(PROBE['files']) == PROBE_NAMES,
         'actual complete Boundary successful-probe identity and file bindings required')
    for name, row in PROBE['files'].items():
        need(isinstance(row, dict) and set(row) == {'bytes', 'sha256'} and
             type(row['bytes']) is int and row['bytes'] > 0 and
             isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']),
             'actual successful-probe pin required: ' + name)
    need(PROBE['files'][NAME] == SOURCE_PIN, 'probe source is not the selected Boundary repair')


def probe_bytes():
    validate_binding()
    data = {name: regular(PROBE_RUN / name) for name in PROBE_NAMES}
    need({name: fingerprint(raw) for name, raw in data.items()} == PROBE['files'],
         'original successful Boundary probe files changed')
    return data


def stable_view(record):
    """Keep the original Coefficient stable-input semantics for later readers."""
    value = json.loads(json.dumps(record))
    value['dependency_inputs']['original_coefficient_inputs'].pop('full_context')
    return value


def retained(c):
    pins = {name: fingerprint(regular(PROBE_RUN / name)) for name in PROBE_NAMES}
    need(pins == PROBE['files'], 'original Boundary probe evidence changed')
    return {'dependency_inputs': c.x.helper.retained(c.x), 'original_probe_references': PROBE}


def verify_probe(c, data):
    result = json.loads(data['PROBE_RESULT.json'])
    need(result['schema'] == 'p15_boundary_policy_no_output_probe_v1' and result['identity'] == c.x.ident and
         result['exit_code'] == 0 and result['probe_passed'] is True and result['preservation_passed'] is True and
         result['output_object_requested'] is False and result['new_owner_accepted'] is False and
         result['new_formal_credit'] == 0 and result['whole_P1_5_complete'] is False and
         not result.get('probe_error') and not result.get('preservation_error') and data[NAME] == c.source,
         'original successful Boundary probe source/scope differs')
    worker = ['python3', '-B', str(PROBE_RUN / 'probe_driver.py'),
              '--source-commit', PROBE['source_commit'], '--worker']
    outer = c.s.h.serialize(0, PROBE_RUN / 'LANE.json', worker)
    commands = {'probe': c.s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(PROBE_RUN / NAME)]),
        'serialized-probe': outer,
        TARGET + '/direct-import-stock-readiness': c.s.h.guard(0,
            ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in IMPORTS])}
    records = {}
    for name, argv in commands.items():
        records[name] = c.verifier.command_record(json.loads(data[name + '-command.json']),
            data[name + '.log'], argv, PROBE_RUN / (name + '.log'))
        started = json.loads(data[name + '-started.json'])
        need(all(started[key] == records[name][key] for key in ('argv', 'cwd', 'started_utc')),
             'original probe start/completion differs')
    need(result['command'] == records['probe'] and result['direct_import_readiness'] ==
         records[TARGET + '/direct-import-stock-readiness'], 'original probe result command differs')
    state = outer[outer.index('--state') + 1]
    c.verifier.verify_finished_lane(json.loads(data['LANE.json']), worker, state,
                                    fingerprint(regular(Path(state)))['sha256'])
    need(all(data[name + '_BEFORE.json'] == data[name + '_AFTER.json'] for name in
             ('PRESERVED', 'TARGET', 'GIT')), 'original probe preservation differs')
    target = json.loads(data['TARGET_BEFORE.json'])
    need(target['source'] in (None, SOURCE_PIN) and all(pin is None for pin in target['artifacts'].values()),
         'original probe did not start with a fresh target')
    recorded = {'dependency_inputs': json.loads(data['PRESERVED_BEFORE.json']), 'original_probe_references': PROBE}
    need(stable_view(recorded) == stable_view(retained(c)), 'original probe dependency inputs changed')


def load(commit):
    validate_binding()
    need(isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit), 'exact source publication required')
    data = probe_bytes()
    probe = ModuleType('retained_boundary_probe_loader')
    probe.__file__ = str(PROBE_RUN / 'probe_driver.py')
    exec(compile(data['probe_driver.py'], probe.__file__, 'exec'), probe.__dict__)
    need((probe.REPO, probe.PROJECT, probe.TARGET, probe.RUN, probe.SOURCE_PIN) ==
         (REPO, PROJECT, TARGET, PROBE_RUN, SOURCE_PIN), 'fixed probe loader environment/source differs')
    x = probe.load(PROBE['source_commit'])  # Read prior acceptance; no parent build/worker/probe.
    need(x.helper.IMPORTS == IMPORTS and len(x.spec.graph) == len(x.spec.sources) == 57,
         'expected 56 original dependencies and only the new Boundary target')
    runner = probe.git(commit, PACKET + '/run_boundary.py')
    need(runner == regular(Path(__file__)) and
         json.loads(probe.git(commit, PACKET + '/PROBE_BINDING.json')) == PROBE,
         'formal adapter or actual probe binding differs from exact publication')
    need(probe.git(commit, LIVE) == x.source == data[NAME] and fingerprint(x.source) == SOURCE_PIN,
         'selected repaired Boundary source changed')
    base = ROOT / commit
    c = SimpleNamespace(x=x, probe=probe, verifier=x.pc.x.parent, g=x.g, s=x.s, spec=x.spec,
        source=x.source, runner=runner, commit=commit, base=base, run=base / 'boundary-policy-operation')
    c.ident = {'commit': commit, 'module': TARGET, 'source': SOURCE_PIN, 'selected_source_unchanged': True,
        'source_origin_reference': x.helper.SOURCE_ORIGIN_REFERENCE, 'source_repair': x.helper.SOURCE_REPAIR,
        'adapter_sha256': fingerprint(runner)['sha256'],
        'coefficient_original_acceptance_binding': x.binding,
        'dictionary_acceptance_reference': x.dictionary.reference,
        'probe': PROBE, 'actual_project_dependencies': 56, 'formal_graph_sources': 57,
        'whole_P1_5_complete': False}
    verify_probe(c, data)
    return c


def accepted(c):
    roots = sorted(path / TARGET for path in ROOT.iterdir() if path.is_dir() and
                   re.fullmatch('[0-9a-f]{40}', path.name) and os.path.lexists(path / TARGET))
    need(roots == [c.base / TARGET], 'target owner missing or competing/partial prior owner exists')
    old = c.g.existing_owner(c.s, c.commit, c.spec, TARGET)
    c.g.require_completed_existing_owner(c.s, c.commit, c.spec, TARGET, old)
    audits = list((c.base / TARGET / 'audits').iterdir())
    need(len(audits) == 1, 'expected one full-owned audit')
    result = c.s.api.read_json(audits[0] / 'lane-0/VALIDATION_RESULTS.json')
    exports = c.s.api.read_json(audits[0] / 'lane-0/OWNED_EXPORTS.json')
    public = {row['name'] for row in exports if not row['is_private']}
    declared = {'ImbalancedChen.' + name for private, kind, name in
        re.findall(r'^(private )?(def|theorem) (\w+)\b', c.source.decode(), re.MULTILINE) if not private}
    need(result['only_standard_axioms'] is True and result['full_owned_including_private_generated'] is True and
         result['total_owned_exports'] == len(exports) and result['total_public_exports'] == len(public) and
         declared <= public, 'incomplete public/private/generated type/axiom audit')
    return {'owned': len(exports), 'public': len(public),
        'axioms': sorted({axiom for row in exports for axiom in row['axioms']}),
        'binding': c.g.acceptance_binding(c.s, c.commit, TARGET)}


def install(c):
    prior = c.x.helper.fresh(c.x)
    path = PROJECT / LIVE
    c.s.d.write_frozen(c.run / 'original-published.lean', c.source)
    if prior['source'] is None:
        need(path.parent.resolve() == path.parent, 'unexpected source parent route')
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.boundary-install-', delete=False) as stream:
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
    c.s.d.save(c.run / 'INSTALL.json', {'identity': c.ident, 'prior': prior})


def worker(c):
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__) == c.run / 'executed.py' and c.run.resolve() == c.run, 'unexpected formal worker route')
    need(c.s.api.read_json(c.run / 'GIT_BEFORE.json') == c.s.d.original_git_state(REPO), 'Git changed before worker')
    before = retained(c)
    c.s.d.save(c.run / 'PRESERVED_BEFORE.json', before)
    try:
        prior = c.x.helper.fresh(c.x)
        stock = c.g.direct_import_readiness(c.s, c.spec, TARGET, c.run)
        need(retained(c) == before and c.x.helper.fresh(c.x) == prior, 'no-build readiness changed retained inputs')
        install(c)
        c.g.run_owner(c.s, c.commit, c.base, c.run, TARGET, c.spec.graph, c.spec.sources)
        owner = accepted(c)
    finally:
        after = retained(c)
        c.s.d.save(c.run / 'PRESERVED_AFTER.json', after)
        need(before == after, 'formal operation changed retained original dependencies')
    c.s.d.save(c.run / 'WORKER_PASS.json', {'identity': c.ident, 'owner': owner, 'native_stock': stock})


def worker_argv(c):
    return ['python3', '-B', str(c.run / 'executed.py'), '--source-commit', c.commit, '--worker']


def dispatch(c):
    c.x.helper.fresh(c.x)
    need(c.run.resolve() == c.run, 'unexpected formal operation route')
    c.run.mkdir(parents=True, exist_ok=False)
    c.s.d.write_frozen(c.run / 'executed.py', c.runner)
    before = c.s.d.original_git_state(REPO)
    c.s.d.save(c.run / 'GIT_BEFORE.json', before)
    try:
        outer = c.s.ops.run(c.run, 'serialized-boundary',
            c.s.h.serialize(0, c.run / 'LANE.json', worker_argv(c)), cwd=PROJECT, relay=True)
        need(outer['exit_code'] == 0 and not outer['actual_failed_modules'] and
             set(outer['actual_built_modules']) <= {TARGET}, 'serialized target scope/status differs')
        passed = c.s.api.read_json(c.run / 'WORKER_PASS.json')
        need(passed['identity'] == c.ident and passed['owner'] == accepted(c), 'new owner acceptance incomplete')
    finally:
        after = c.s.d.original_git_state(REPO)
        c.s.d.save(c.run / 'GIT_AFTER.json', after)
        need(before == after, 'original checkout Git state changed')
    c.s.d.save(c.run / 'PASS.json', {'identity': c.ident, 'command': outer,
        'worker': c.s.d.fingerprint(c.run / 'WORKER_PASS.json'),
        'preserved': c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json')})


def check(c):
    need(c.run.resolve() == c.run, 'unexpected formal operation route')
    if not os.path.lexists(c.run):
        prior = c.x.helper.fresh(c.x)
        retained(c)
        return {'status': 'FRESH', 'identity': c.ident, 'original_source_present': prior['source'] is not None,
                'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}
    read = c.s.api.read_json
    passed, installed, completed = (read(c.run / name) for name in ('PASS.json', 'INSTALL.json', 'WORKER_PASS.json'))
    need(regular(c.run / 'executed.py') == c.runner and regular(c.run / 'original-published.lean') == c.source and
         regular(PROJECT / LIVE) == c.source and passed['identity'] == installed['identity'] == completed['identity'] == c.ident and
         completed['owner'] == accepted(c) and passed['worker'] == c.s.d.fingerprint(c.run / 'WORKER_PASS.json'),
         'formal source/owner provenance differs')
    need(installed['prior']['source'] in (None, SOURCE_PIN) and
         all(pin is None for pin in installed['prior']['artifacts'].values()), 'formal owner did not start fresh')
    need(read(c.run / 'GIT_BEFORE.json') == read(c.run / 'GIT_AFTER.json') and
         passed['preserved'] == c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json') ==
         c.s.d.fingerprint(c.run / 'PRESERVED_AFTER.json'), 'formal preservation differs')
    need(stable_view(read(c.run / 'PRESERVED_BEFORE.json')) == stable_view(retained(c)),
         'original stable dependency content/acceptance references changed')
    outer_argv = c.s.h.serialize(0, c.run / 'LANE.json', worker_argv(c))
    commands = {'serialized-boundary': (outer_argv, (TARGET,)),
        TARGET + '/direct-import-stock-readiness': (c.s.h.guard(0,
            ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in IMPORTS]), ())}
    records = {}
    for name, (argv, allowed) in commands.items():
        records[name] = c.verifier.command_record(read(c.run / (name + '-command.json')),
            regular(c.run / (name + '.log')), argv, c.run / (name + '.log'), allowed)
    need(records['serialized-boundary'] == passed['command'] and
         records[TARGET + '/direct-import-stock-readiness'] == completed['native_stock'], 'formal command differs')
    state = outer_argv[outer_argv.index('--state') + 1]
    c.verifier.verify_finished_lane(read(c.run / 'LANE.json'), worker_argv(c), state,
                                    fingerprint(regular(Path(state)))['sha256'])
    return {'status': 'REVALIDATED', 'identity': c.ident,
        'owner': {key: value for key, value in completed['owner'].items() if key != 'binding'},
        'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    modes = parser.add_mutually_exclusive_group(required=True)
    for name in ('run', 'check', 'worker'):
        modes.add_argument('--' + name, action='store_true')
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
