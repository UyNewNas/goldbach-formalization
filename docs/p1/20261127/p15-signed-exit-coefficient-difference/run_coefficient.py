#!/usr/bin/env python3
"""Accept only the unchanged CoefficientDifference owner using retained inputs.

The existing successful no-output probe is read, never rerun. Its pinned loader
retains the original Policy/Partition/Dictionary/Variation acceptance identities.
The published owner API supplies normal, kernel replay and full-owned type/axiom
audit. There is no dependency rebuild or reduced-audit mode.
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
PACKET = 'docs/p1/20261127/p15-signed-exit-coefficient-difference'
TARGET = 'ImbalancedChen.P1SignedExitCoefficientDifference'
NAME = 'P1SignedExitCoefficientDifference.lean'
LIVE = 'ImbalancedChen/' + NAME
SOURCE_PIN = {'bytes': 17943, 'sha256': '4de8d8f28bfc304351192ed785aade7609aee909425e5109ff7c4a38236823e6'}
IMPORTS = ['ImbalancedChen.P1SignedExitPolicyComparison',
           'ImbalancedChen.FirstExitGenericModuli', 'ImbalancedChen.PhysicalUpperWeightBridge']
PROBE_RUN = (Path('/workspace/p1-complete-proof/20261127-p15-signed-exit-coefficient-probe-v1') /
             SOURCE_PIN['sha256'] / 'attempt-00000')
PROBE_FILES = {'GIT_AFTER.json': {'bytes': 1157,
                    'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
 'GIT_BEFORE.json': {'bytes': 1157,
                     'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
 'ImbalancedChen.P1SignedExitCoefficientDifference/direct-import-stock-readiness-command.json': {'bytes': 1060,
                                                                                                 'sha256': '6090f7b63d32dceb0711a30d256d6c4152642523141a88d3ba9bea3096531624'},
 'ImbalancedChen.P1SignedExitCoefficientDifference/direct-import-stock-readiness-started.json': {'bytes': 471,
                                                                                                 'sha256': '9efc6fe716b7d1864671da3231326ac6ca01f40c28631868e60ac97229c72a27'},
 'ImbalancedChen.P1SignedExitCoefficientDifference/direct-import-stock-readiness.log': {'bytes': 150527,
                                                                                        'sha256': '6b7b2b6fc56bf2da83ca4c9e9108600da55b6827fe3c489825d426432469bf0c'},
 'LANE.json': {'bytes': 1222, 'sha256': '9dad3e1240e0a3d59a001085c92a69ec935830c31892575bc5dd1823f594350a'},
 'P1SignedExitCoefficientDifference.lean': {'bytes': 17943,
                                            'sha256': '4de8d8f28bfc304351192ed785aade7609aee909425e5109ff7c4a38236823e6'},
 'PRESERVED_AFTER.json': {'bytes': 1537035,
                          'sha256': 'bc3a364b836b6d2c1b9a1fa7659c090c8680f9dc91279c096cd3e279c64f43d9'},
 'PRESERVED_BEFORE.json': {'bytes': 1537035,
                           'sha256': 'bc3a364b836b6d2c1b9a1fa7659c090c8680f9dc91279c096cd3e279c64f43d9'},
 'PROBE_RESULT.json': {'bytes': 14771,
                       'sha256': '41d486e9c736eaebb9c39dc6a6b3a9ef3cd3c12f834a0734da2d129d8f010ee8'},
 'probe-command.json': {'bytes': 1030,
                        'sha256': '493adc550c99e2e869f3ccd2d1cae770cf694ec4dcd0a18652efd935e25d2dd1'},
 'probe-started.json': {'bytes': 516,
                        'sha256': 'a7720c9ea4915ba121a4a0460b4077c1fdd56bc88cb55a0b0dcce219a3a3f439'},
 'probe.log': {'bytes': 103, 'sha256': '4311c76b27e36dbaf85d7697f2d169aa20e0f6e4b44897c10aaa55bdfb491336'},
 'probe_driver.py': {'bytes': 16104,
                     'sha256': 'f0220368e248e9a3ceb012dbc1d69be1a28f15154f58336dfdbfd84869912fd8'},
 'serialized-probe-command.json': {'bytes': 1210,
                                   'sha256': 'ea1eb826b658d1ad209a377c0e8d02ec935fe5b0a60b36fd35d7c2153ed5cd14'},
 'serialized-probe-started.json': {'bytes': 683,
                                   'sha256': '7baacbaac8d764664a6b71ecd5cb4e8b8d3ebf82c8e963d836d2454c20b0cee9'},
 'serialized-probe.log': {'bytes': 12955,
                          'sha256': '70efcba71ee9074881168f9cf7c7a72d7edee3003f5616d588c7e7df41daec70'}}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def regular(path):
    need(path.is_file() and not path.is_symlink() and path.resolve() == path,
         'expected original regular file: ' + str(path))
    return path.read_bytes()


def probe_bytes():
    data = {rel: regular(PROBE_RUN / rel) for rel in PROBE_FILES}
    need({rel: fingerprint(raw) for rel, raw in data.items()} == PROBE_FILES,
         'existing successful Coefficient probe bytes changed')
    return data


def protected_inputs(c):
    """The original probe fixed() protection, excluding its now-new target."""
    h, x, pc = c.probe, c.x, c.x.c
    owner = x.parent.accepted(pc)
    need(pc.g.module_artifacts(pc.s, h.POLICY) == owner['binding']['all_observed_target_artifacts'] and
         pc.g.file_binding(PROJECT / pc.s.h.module_path(h.POLICY)) == h.POLICY_SOURCE_PIN['sha256'],
         'original Policy source/artifacts differ')
    stem = PROJECT / '.lake/build/lib/lean' / h.POLICY.replace('.', '/')
    return {'original_inputs': x.parent.fixed(pc), 'original_policy_owner': owner,
            'policy_extra_metadata': {ext: pc.x.c.support.metadata(Path(str(stem) + ext))
                                      for ext in ('.trace.nobuild', '.ir.sig.hash')},
            'policy_adapter': fingerprint(h.bound_bytes(h.POLICY_BINDING['adapter'])),
            'parent_receipts': {key: h.receipt(h.POLICY_BINDING[key])
                                for key in ('formal_pass', 'readonly_receipt')}}


def same_probe_inputs(c, recorded, current):
    c.x.parent.require_same_stable_inputs(recorded['original_inputs'], current['original_inputs'])
    need(recorded['original_inputs']['retained_probe_evidence'] ==
         current['original_inputs']['retained_probe_evidence'] and
         all(recorded[key] == current[key] for key in
             ('original_policy_owner', 'policy_extra_metadata', 'policy_adapter', 'parent_receipts')),
         'original Policy acceptance/probe inputs changed')


def canonical_pin(value):
    return fingerprint(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                  ensure_ascii=False).encode())


def stable_view(protected):
    """Exactly the content compared by the published Policy stable-input reader."""
    policy, partition = protected['original_inputs'], protected['original_inputs']['original_inputs']
    return {
        'partition_inputs': {key: partition[key] for key in
            ('actual_dependency_context', 'dictionary_acceptance_reference', 'variation')},
        'native_required_inputs': partition['native_direct_import']['required_existing_inputs'],
        'existing_owners_environment': partition['existing_owners']['environment'],
        'policy_inputs': {key: policy[key] for key in
            ('original_partition_owner', 'partition_extra_metadata', 'parent_receipts', 'retained_probe_evidence')},
        'coefficient_inputs': {key: protected[key] for key in
            ('original_policy_owner', 'policy_extra_metadata', 'policy_adapter', 'parent_receipts')}}


def retained(c):
    protected = protected_inputs(c)
    probe_pins = {rel: fingerprint(regular(PROBE_RUN / rel)) for rel in PROBE_FILES}
    need(probe_pins == PROBE_FILES, 'original Coefficient probe evidence changed')
    # Full content is checked before/after in memory and committed as a digest.
    # Original receipts remain at their pinned paths; no historical JSON copies.
    return {'schema': 'p15_retained_input_digest_v1',
        'canonical_serialization': 'UTF-8 json.dumps(sort_keys=True,separators=(",",":"),ensure_ascii=False)',
        'full_context': canonical_pin(protected), 'stable_context': canonical_pin(stable_view(protected)),
        'original_policy_acceptance_references': c.probe.POLICY_BINDING,
        'original_probe_references': {'directory': str(PROBE_RUN), 'files': probe_pins}}


def verify_probe(c, data):
    result = json.loads(data['PROBE_RESULT.json'])
    need(result['schema'] == 'p15_coefficient_difference_no_output_probe_v1' and
         result['target'] == TARGET and result['source_path'] == LIVE and
         result['source_commit'] == c.probe.SOURCE_COMMIT and result['source'] == SOURCE_PIN and
         data[NAME] == c.source and result['direct_imports'] == IMPORTS and
         result['project_dependency_count'] == 42 and result['exit_code'] == 0 and
         result['probe_passed'] is True and result['preservation_passed'] is True and
         result['original_source_unchanged'] is True and result['output_object_requested'] is False and
         result['new_owner_accepted'] is False and result['new_formal_credit'] == 0 and
         result['whole_P1_5_complete'] is False and
         result['policy_original_identity'] == c.x.readonly and
         result['policy_original_acceptance_binding'] == c.probe.POLICY_BINDING and
         not result.get('probe_error') and not result.get('preservation_error'),
         'existing successful probe source/scope/parent differs')
    worker = ['python3', '-B', str(PROBE_RUN / 'probe_driver.py'), '--worker']
    outer = c.s.h.serialize(0, PROBE_RUN / 'LANE.json', worker)
    commands = {
        'probe': c.s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(PROBE_RUN / NAME)]),
        TARGET + '/direct-import-stock-readiness': c.s.h.guard(0,
            ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in IMPORTS]),
        'serialized-probe': outer}
    verified = {}
    for name, argv in commands.items():
        record = json.loads(data[name + '-command.json'])
        c.x.parent.command_record(record, data[name + '.log'], argv, PROBE_RUN / (name + '.log'))
        started = json.loads(data[name + '-started.json'])
        need(all(started[key] == record[key] for key in ('argv', 'cwd', 'started_utc')),
             'probe start/completion mismatch')
        verified[name] = record
    need(result['command'] == verified['probe'] and result['direct_import_readiness'] ==
         verified[TARGET + '/direct-import-stock-readiness'], 'probe result command differs')
    state = outer[outer.index('--state') + 1]
    c.x.parent.verify_finished_lane(json.loads(data['LANE.json']), worker, state,
                                    fingerprint(regular(Path(state)))['sha256'])
    need(data['PRESERVED_BEFORE.json'] == data['PRESERVED_AFTER.json'] and
         data['GIT_BEFORE.json'] == data['GIT_AFTER.json'], 'probe preservation differs')
    before = json.loads(data['PRESERVED_BEFORE.json'])
    need(before['new_target']['source'] in (None, SOURCE_PIN) and
         all(pin is None for pin in before['new_target']['artifacts'].values()),
         'probe did not start with a fresh target')
    same_probe_inputs(c, before, protected_inputs(c))


def load(commit):
    need(isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit), 'exact source commit required')
    data = probe_bytes()
    probe = ModuleType('retained_coefficient_probe_loader')
    probe.__file__ = str(PROBE_RUN / 'probe_driver.py')
    exec(compile(data['probe_driver.py'], probe.__file__, 'exec'), probe.__dict__)
    need((probe.REPO, probe.PROJECT, probe.ACCEPTANCE_ROOT, probe.TARGET, probe.RUN) ==
         (REPO, PROJECT, ROOT, TARGET, PROBE_RUN) and probe.SOURCE_PIN == SOURCE_PIN and
         probe.IMPORTS == IMPORTS, 'original probe loader environment differs')
    x = probe.load()  # Existing parent load/check only; no Lean/kernel command.
    runner = x.parent.git(commit, PACKET + '/run_coefficient.py')
    need(runner == regular(Path(__file__)), 'executed adapter differs from exact source publication')
    need(json.loads(x.parent.git(commit, PACKET + '/INPUTS.json')) ==
         {'directory': str(PROBE_RUN), 'files': PROBE_FILES}, 'published actual probe bindings differ')
    source = x.parent.git(commit, LIVE)
    need(source == x.source == data[NAME] and fingerprint(source) == SOURCE_PIN and
         not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', source.decode()),
         'original complete coefficient source changed or contains proof escape')
    graph = {**x.c.spec.graph, TARGET: list(IMPORTS)}
    sources = {**x.c.spec.sources, TARGET: SOURCE_PIN['sha256']}
    need(len(graph) == len(sources) == 43 and TARGET not in x.c.spec.graph and
         x.c.s.h.closure(graph, [TARGET]) == set(graph), 'expected exactly 42 reused inputs and one new owner')
    spec = SimpleNamespace(graph=graph, sources=sources,
                          manifest={'project_sources': {TARGET: {'all_imports': IMPORTS}}})
    base = ROOT / commit
    c = SimpleNamespace(probe=probe, x=x, g=x.c.g, s=x.c.s, source=source, runner=runner,
                        spec=spec, commit=commit, base=base, run=base / 'signed-exit-coefficient-operation')
    c.ident = {'commit': commit, 'module': TARGET, 'source': SOURCE_PIN,
        'source_origin_commit': probe.SOURCE_COMMIT, 'mathematical_source_unchanged': True,
        'adapter_sha256': fingerprint(runner)['sha256'],
        'policy_original_acceptance_binding': probe.POLICY_BINDING,
        'probe': {'directory': str(PROBE_RUN), 'files': PROBE_FILES, 'formal_credit_from_probe': 0},
        'actual_project_dependencies': 42, 'formal_graph_sources': 43, 'whole_P1_5_complete': False}
    verify_probe(c, data)
    return c


def accepted(c):
    roots = sorted(p / TARGET for p in ROOT.iterdir() if p.is_dir() and
                   re.fullmatch('[0-9a-f]{40}', p.name) and os.path.lexists(p / TARGET))
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
         declared <= public, 'incomplete original public/full-owned type/axiom audit')
    return {'owned': len(exports), 'public': len(public),
            'axioms': sorted({axiom for row in exports for axiom in row['axioms']}),
            'binding': c.g.acceptance_binding(c.s, c.commit, TARGET)}


def install(c):
    prior = c.probe.fresh(c.x)
    path = PROJECT / LIVE
    c.s.d.write_frozen(c.run / 'original-published.lean', c.source)
    if prior['source'] is None:
        need(path.parent.resolve() == path.parent, 'unexpected source parent route')
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.coefficient-install-', delete=False) as stream:
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
    need(Path(__file__) == c.run / 'executed.py' and c.run.resolve() == c.run, 'unexpected worker route')
    need(c.s.api.read_json(c.run / 'GIT_BEFORE.json') == c.s.d.original_git_state(REPO), 'Git changed before worker')
    before = retained(c)
    c.s.d.save(c.run / 'PRESERVED_BEFORE.json', before)
    try:
        prior = c.probe.fresh(c.x)
        stock = c.g.direct_import_readiness(c.s, c.spec, TARGET, c.run)
        need(retained(c) == before and c.probe.fresh(c.x) == prior, 'no-build readiness changed retained inputs')
        install(c)
        c.g.run_owner(c.s, c.commit, c.base, c.run, TARGET, c.spec.graph, c.spec.sources)
        owner = accepted(c)
    finally:
        after = retained(c)
        c.s.d.save(c.run / 'PRESERVED_AFTER.json', after)
        need(before == after, 'formal operation changed retained inputs')
    c.s.d.save(c.run / 'WORKER_PASS.json', {'identity': c.ident, 'owner': owner, 'native_stock': stock})


def worker_argv(c):
    return ['python3', '-B', str(c.run / 'executed.py'), '--source-commit', c.commit, '--worker']


def dispatch(c):
    c.probe.fresh(c.x)
    need(c.run.resolve() == c.run, 'unexpected operation route')
    c.run.mkdir(parents=True, exist_ok=False)
    c.s.d.write_frozen(c.run / 'executed.py', c.runner)
    before = c.s.d.original_git_state(REPO)
    c.s.d.save(c.run / 'GIT_BEFORE.json', before)
    try:
        outer = c.s.ops.run(c.run, 'serialized-coefficient',
            c.s.h.serialize(0, c.run / 'LANE.json', worker_argv(c)), cwd=PROJECT, relay=True)
        need(outer['exit_code'] == 0 and not outer['actual_failed_modules'] and
             set(outer['actual_built_modules']) <= {TARGET}, 'serialized target scope/status differs')
        passed = c.s.api.read_json(c.run / 'WORKER_PASS.json')
        need(passed['identity'] == c.ident and passed['owner'] == accepted(c), 'incomplete new owner acceptance')
    finally:
        after = c.s.d.original_git_state(REPO)
        c.s.d.save(c.run / 'GIT_AFTER.json', after)
        need(before == after, 'original checkout Git state changed')
    c.s.d.save(c.run / 'PASS.json', {'identity': c.ident, 'command': outer,
        'worker': c.s.d.fingerprint(c.run / 'WORKER_PASS.json'),
        'preserved': c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json')})


def check(c):
    need(c.run.resolve() == c.run, 'unexpected operation route')
    if not os.path.lexists(c.run):
        prior = c.probe.fresh(c.x)
        retained(c)
        return {'status': 'FRESH', 'identity': c.ident, 'original_source_present': prior['source'] is not None,
                'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}
    read = c.s.api.read_json
    passed = read(c.run / 'PASS.json')  # Missing/partial operations are retained, never restarted.
    installed, completed = read(c.run / 'INSTALL.json'), read(c.run / 'WORKER_PASS.json')
    need(regular(c.run / 'executed.py') == c.runner and regular(c.run / 'original-published.lean') == c.source and
         regular(PROJECT / LIVE) == c.source and passed['identity'] == installed['identity'] ==
         completed['identity'] == c.ident and completed['owner'] == accepted(c) and
         passed['worker'] == c.s.d.fingerprint(c.run / 'WORKER_PASS.json'), 'formal source/owner provenance differs')
    need(installed['prior']['source'] in (None, SOURCE_PIN) and
         all(pin is None for pin in installed['prior']['artifacts'].values()), 'owner did not start fresh')
    need(read(c.run / 'GIT_BEFORE.json') == read(c.run / 'GIT_AFTER.json') and
         passed['preserved'] == c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json') ==
         c.s.d.fingerprint(c.run / 'PRESERVED_AFTER.json'), 'formal preservation differs')
    recorded, current = read(c.run / 'PRESERVED_BEFORE.json'), retained(c)
    need({key: value for key, value in recorded.items() if key != 'full_context'} ==
         {key: value for key, value in current.items() if key != 'full_context'},
         'original stable dependency content/acceptance references changed')
    outer_argv = c.s.h.serialize(0, c.run / 'LANE.json', worker_argv(c))
    commands = {'serialized-coefficient': (outer_argv, (TARGET,)),
        TARGET + '/direct-import-stock-readiness': (c.s.h.guard(0,
            ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in IMPORTS]), ())}
    records = {}
    for name, (argv, allowed) in commands.items():
        records[name] = c.x.parent.command_record(read(c.run / (name + '-command.json')),
            regular(c.run / (name + '.log')), argv, c.run / (name + '.log'), allowed)
    need(records['serialized-coefficient'] == passed['command'] and
         records[TARGET + '/direct-import-stock-readiness'] == completed['native_stock'], 'formal command differs')
    state = outer_argv[outer_argv.index('--state') + 1]
    c.x.parent.verify_finished_lane(read(c.run / 'LANE.json'), worker_argv(c), state,
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
