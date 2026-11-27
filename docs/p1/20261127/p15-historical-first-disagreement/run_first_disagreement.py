#!/usr/bin/env python3
"""Accept only the selected FirstDisagreement repair after its actual successful probe.

All 293 dependencies retain their original source/object identities. The pinned
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
PACKET = 'docs/p1/20261127/p15-historical-first-disagreement'
TARGET = 'ImbalancedChen.P1OriginalHistoricalFirstDisagreement'
NAME = 'P1OriginalHistoricalFirstDisagreement.lean'
LIVE = 'ImbalancedChen/' + NAME
SOURCE_PIN = {'bytes': 5545, 'sha256': '00b11f60f73300ff8443ed72367c19f6c817fa5384d1449296b929a0155731ec'}
IMPORTS = ['ImbalancedChen.P1OriginalHistoricalCoefficientDictionary',
           'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport']
PROBE_RUN = (Path('/workspace/p1-complete-proof/20261127-p15-historical-first-disagreement-probe-v1') /
             SOURCE_PIN['sha256'] / 'attempt-00000')
PROBE = {'directory': '/workspace/p1-complete-proof/20261127-p15-historical-first-disagreement-probe-v1/00b11f60f73300ff8443ed72367c19f6c817fa5384d1449296b929a0155731ec/attempt-00000',
 'files': {'GIT_AFTER.json': {'bytes': 1157,
                              'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
           'GIT_BEFORE.json': {'bytes': 1157,
                               'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
           'ImbalancedChen.P1OriginalHistoricalFirstDisagreement/direct-import-stock-readiness-command.json': {'bytes': 1049,
                                                                                                               'sha256': '05566f4201341344f9e9f2cf9566a58e0ea754f952b5bcc1fb2bdadd836cbefb'},
           'ImbalancedChen.P1OriginalHistoricalFirstDisagreement/direct-import-stock-readiness-started.json': {'bytes': 450,
                                                                                                               'sha256': 'b20f06a623bde33ae21aaeba87395c795386811f74b50879ebaacc2983b9923f'},
           'ImbalancedChen.P1OriginalHistoricalFirstDisagreement/direct-import-stock-readiness.log': {'bytes': 195986,
                                                                                                      'sha256': '9d6a00b7deb8e309d1f824c3b6ca6521de5bc295898d9ebada5759179af2d01f'},
           'LANE.json': {'bytes': 1299,
                         'sha256': '6657312b3248865e70fe5ea66b4a7a6505d48dd2229216919ccb3193168159f1'},
           'P1OriginalHistoricalFirstDisagreement.lean': {'bytes': 5545,
                                                          'sha256': '00b11f60f73300ff8443ed72367c19f6c817fa5384d1449296b929a0155731ec'},
           'PRESERVED_AFTER.json': {'bytes': 16114,
                                    'sha256': 'b1131eee65ff128e1bf13a27461aae8de230f18d73888367af6f77c873bed11c'},
           'PRESERVED_BEFORE.json': {'bytes': 16114,
                                     'sha256': 'b1131eee65ff128e1bf13a27461aae8de230f18d73888367af6f77c873bed11c'},
           'PROBE_RESULT.json': {'bytes': 5349,
                                 'sha256': 'c297a640bc0ddfc1c0f7c0e3853af2437e17a35f6a1ee1be9bf37d0e3eb51f77'},
           'TARGET_AFTER.json': {'bytes': 2000,
                                 'sha256': '85a8aba3629aea49a8681a1de5ba2f568db787a2826bfcf6b3804b5ca0370c86'},
           'TARGET_BEFORE.json': {'bytes': 2000,
                                  'sha256': '85a8aba3629aea49a8681a1de5ba2f568db787a2826bfcf6b3804b5ca0370c86'},
           'probe-command.json': {'bytes': 1046,
                                  'sha256': '0982cdd478f8db9b0f1373430a2a60f4065dfbf9e6a3857aa1a1da8bf89c3ce4'},
           'probe-started.json': {'bytes': 526,
                                  'sha256': '881dd740150dff5fb070beecfcc5f0c9e925bdca36455fe97b43bcc88e68f105'},
           'probe.log': {'bytes': 103,
                         'sha256': '4311c76b27e36dbaf85d7697f2d169aa20e0f6e4b44897c10aaa55bdfb491336'},
           'probe_driver.py': {'bytes': 8215,
                               'sha256': 'e37e501828cc6c4bfe3ddbd326b6dd694e5db0d4b7db0e85222388d056368460'},
           'serialized-probe-command.json': {'bytes': 1297,
                                             'sha256': '132e4bec0cb3d6ea1e1e9c63ecadf6a73133200942d37dd9837996ec47181be7'},
           'serialized-probe-started.json': {'bytes': 766,
                                             'sha256': 'f7aaadb3cb103243cc97dfb9b6e5fd3e030d0af21c9d397b2bcd2cfc3bdc7de9'},
           'serialized-probe.log': {'bytes': 5677,
                                    'sha256': '15426dfd6051123f06fc862a3bcbeb7664d71df3f2f3ca6a0b35b7bd97a804b0'}},
 'source_commit': '965dfa7329d5509ca651e186a5b379a655f47db3'}
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
         'actual complete FirstDisagreement successful-probe identity and file bindings required')
    for name, row in PROBE['files'].items():
        need(isinstance(row, dict) and set(row) == {'bytes', 'sha256'} and
             type(row['bytes']) is int and row['bytes'] > 0 and
             isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']),
             'actual successful-probe pin required: ' + name)
    need(PROBE['files'][NAME] == SOURCE_PIN, 'probe source is not the selected FirstDisagreement repair')


def probe_bytes():
    validate_binding()
    data = {name: regular(PROBE_RUN / name) for name in PROBE_NAMES}
    need({name: fingerprint(raw) for name, raw in data.items()} == PROBE['files'],
         'original successful FirstDisagreement probe files changed')
    return data


def stable_view(c, record):
    """Reuse the original Boundary reader's stable-input comparison view."""
    value = json.loads(json.dumps(record))
    value['dependency_inputs']['original_boundary_inputs'] = c.x.parent.stable_view(
        value['dependency_inputs']['original_boundary_inputs'])
    return value


def retained(c):
    pins = {name: fingerprint(regular(PROBE_RUN / name)) for name in PROBE_NAMES}
    need(pins == PROBE['files'], 'original FirstDisagreement probe evidence changed')
    return {'dependency_inputs': c.x.helper.retained(c.x), 'original_probe_references': PROBE}


def verify_probe(c, data):
    result = json.loads(data['PROBE_RESULT.json'])
    need(result['schema'] == 'p15_historical_first_disagreement_no_output_probe_v1' and result['identity'] == c.x.ident and
         result['exit_code'] == 0 and result['probe_passed'] is True and result['preservation_passed'] is True and
         result['output_object_requested'] is False and result['new_owner_accepted'] is False and
         result['new_formal_credit'] == 0 and result['whole_P1_5_complete'] is False and
         not result.get('probe_error') and not result.get('preservation_error') and data[NAME] == c.source,
         'original successful FirstDisagreement probe source/scope differs')
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
    need(stable_view(c, recorded) == stable_view(c, retained(c)), 'original probe dependency inputs changed')


def load(commit):
    validate_binding()
    need(isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit), 'exact source publication required')
    data = probe_bytes()
    probe = ModuleType('retained_first_disagreement_probe_loader')
    probe.__file__ = str(PROBE_RUN / 'probe_driver.py')
    exec(compile(data['probe_driver.py'], probe.__file__, 'exec'), probe.__dict__)
    need((probe.REPO, probe.PROJECT, probe.TARGET, probe.RUN, probe.SOURCE_PIN) ==
         (REPO, PROJECT, TARGET, PROBE_RUN, SOURCE_PIN), 'fixed probe loader environment/source differs')
    x = probe.load(PROBE['source_commit'])  # Read prior acceptance; no parent build/worker/probe.
    need(x.helper.IMPORTS == IMPORTS and len(x.spec.graph) == len(x.spec.sources) == 294,
         'expected 293 original dependencies and only the new bridge target')
    runner = probe.git(commit, PACKET + '/run_first_disagreement.py')
    need(runner == regular(Path(__file__)) and
         json.loads(probe.git(commit, PACKET + '/PROBE_BINDING.json')) == PROBE,
         'formal adapter or actual probe binding differs from exact publication')
    need(probe.git(commit, LIVE) == x.source == data[NAME] and fingerprint(x.source) == SOURCE_PIN,
         'selected repaired FirstDisagreement source changed')
    base = ROOT / commit
    c = SimpleNamespace(x=x, probe=probe, verifier=x.verifier, g=x.g, s=x.s, spec=x.spec,
        source=x.source, runner=runner, commit=commit, base=base, run=base / 'historical-first-disagreement-operation')
    c.ident = {'commit': commit, 'module': TARGET, 'source': SOURCE_PIN, 'selected_source_unchanged': True,
        'source_origin_reference': x.helper.SOURCE_ORIGIN_REFERENCE, 'source_repair': x.helper.SOURCE_REPAIR,
        'adapter_sha256': fingerprint(runner)['sha256'],
        'boundary_original_acceptance_binding': x.binding,
        'dictionary_acceptance_reference': x.dictionary.reference,
        'probe': PROBE, 'actual_project_dependencies': 293, 'formal_graph_sources': 294,
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
    declared = c.x.helper.public_source_names(c.source)
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
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.first-disagreement-install-', delete=False) as stream:
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
        outer = c.s.ops.run(c.run, 'serialized-first-disagreement',
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
    need(stable_view(c, read(c.run / 'PRESERVED_BEFORE.json')) == stable_view(c, retained(c)),
         'original stable dependency content/acceptance references changed')
    outer_argv = c.s.h.serialize(0, c.run / 'LANE.json', worker_argv(c))
    commands = {'serialized-first-disagreement': (outer_argv, (TARGET,)),
        TARGET + '/direct-import-stock-readiness': (c.s.h.guard(0,
            ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in IMPORTS]), ())}
    records = {}
    for name, (argv, allowed) in commands.items():
        records[name] = c.verifier.command_record(read(c.run / (name + '-command.json')),
            regular(c.run / (name + '.log')), argv, c.run / (name + '.log'), allowed)
    need(records['serialized-first-disagreement'] == passed['command'] and
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
