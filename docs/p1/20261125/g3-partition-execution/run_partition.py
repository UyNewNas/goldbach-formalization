#!/usr/bin/env python3
"""One reviewed G3 owner: source check, fixture-bound normal, or separate audit.

Published normal/audit engines and the original installer/guards remain unchanged.
Source-only local checks never read fixture payloads or cloud runtime files.
"""
from datetime import datetime
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
BASE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
MANIFEST = 'docs/p1/20261125/g3-partition-review/SOURCE_PARTITION.json'
INVENTORY = 'docs/p1/20261125/g3-reuse/G3_REUSE_INVENTORY.json'
READER_RECEIPT = 'docs/p1/20261124/batch5-verified-evidence/AUDIT24_VALIDATION_RESULTS.json'
OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'
CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
EXACT_FACETS = 'docs/p1/20261125/batch13-accepted-evidence/G3_EXACT_FACETS.json'
PINS = {
    API_PATH: '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea',
    MANIFEST: '67ca0a0157134c1c93cc1130d7ed80e56e85edadb4373ee18981c6f68048693d',
    INVENTORY: 'c89fd6388cfb269ebe74bad97e62454a8ad36fc317d7e5685253f4c13785047e',
    READER_RECEIPT: '18a4660cae2ce1f0fa2d233f84be244f46b7a9522bd46f7289c89e50d72adcd1',
    OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614',
    CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880',
    EXACT_FACETS: 'd6063b581259ce08e394493e44e52ed821239b4cd5f3efaf331638f62dc319a9',
}
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-g3-partition-v1')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261125-g3-data-pilot-v1')
DATA = 'ImbalancedChen.P4AOriginalNewFifthArchiveData'
READER = 'ImbalancedChen.P4AOriginalNewFifthArchiveReader'
OLD_DATA_SHA = '5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4'
READER_SHA = '59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6'
CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def source_preflight(s):
    need((s.project / 'ImbalancedChen').is_dir() and not (s.project / 'ImbalancedChen').is_symlink(),
         'project source directory must be regular')
    for row in s.updates:
        path = s.project / row['path']
        if os.path.lexists(path):
            need(path.is_file() and not path.is_symlink(), 'source must be regular, never a symlink: ' + str(path))
        else:
            need(row['before_sha256'] is None, 'existing facade is absent')
    return s.d.preflight_sources(s.project, s.updates, s.payloads)


def check_configs(s, basis):
    expected = s.source_config if basis == 'source' else s.runtime_config
    need({p: s.d.fingerprint(s.project / p) for p in CONFIGS} == expected and
         not os.path.lexists(s.project / 'lakefile.lean'), 'project configuration differs from selected pinned basis')


def check_environment(s, installed=False):
    check_configs(s, 'runtime')
    need(s.d.runtime_binding(s.h) == s.runtime, 'accepted runtime/guard/serializer/template changed')
    expected = {m: digest for m, digest in s.sources.items() if installed or m not in s.targets}
    expected.update(s.protected)
    need(all(sha((s.project / s.h.module_path(m)).read_bytes()) == digest for m, digest in expected.items()),
         'project source context or protected source changed')


def inputs(repo, project, commit, module, basis):
    need(re.fullmatch(r'[0-9a-f]{40}', commit) is not None, 'source-commit requires a full lowercase SHA')
    need(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=repo).strip() == b'commit',
         'source-commit is not a commit object')

    def git(c, path):
        return subprocess.check_output(['git', 'show', c + ':' + path], cwd=repo)

    raw = {p: git(API_COMMIT if p == API_PATH else commit, p) for p in PINS}
    need(all(sha(raw[p]) == digest for p, digest in PINS.items()), 'published input pin differs')
    api = types.ModuleType('published_batch13_api')
    api.__file__ = '<pinned Git object: ' + API_PATH + '>'
    exec(compile(raw[API_PATH], api.__file__, 'exec'), api.__dict__)
    need(api.TOOLS == BASE and api.PROJECT == PROJECT and api.REPO == REPO, 'published API environment differs')
    pins = {**PINS, **api.PINS}
    for path, digest in api.PINS.items():
        raw[path] = git(BASE, path)
        need(sha(raw[path]) == digest, 'unchanged helper pin differs: ' + path)
    h, ops, d = api.load(raw[api.HELPER], 'batch5'), api.load(raw[api.OPS], 'batch6'), api.load(raw[api.PRIMITIVES], 'batch10')
    manifest = json.loads(raw[MANIFEST])
    rows = manifest['modules']
    targets = [r['module'] for r in rows]
    need(manifest['schema'] == 'p1_g3_literal_data_partition_v1' and manifest['base_source_commit'] == BASE and
         len(targets) == len(set(targets)) == 25 and targets[-1] == DATA and module in targets,
         'module is outside the exact 25-owner partition')
    payloads, updates = {}, []
    for row in rows:
        m, path = row['module'], row['path']
        need(path == h.module_path(m) and PurePosixPath(path).parent == PurePosixPath('ImbalancedChen') and
             row['expected_before_sha256'] == (OLD_DATA_SHA if m == DATA else None), 'partition source path/preimage differs')
        payloads[path] = git(commit, path)
        need(sha(payloads[path]) == row['source_sha256'] and len(payloads[path]) == row['bytes'] and
             h.imports(payloads[path]) == row['imports'], 'partition payload/imports differ: ' + m)
        updates.append({'module': m, 'path': path, 'before_sha256': row['expected_before_sha256'],
                        'after_sha256': row['source_sha256'], 'cloud_source_mutation_required': True})
    need(sha(git(BASE, h.module_path(DATA))) == OLD_DATA_SHA, 'original Data Git preimage differs')
    tree = subprocess.check_output(['git', 'ls-tree', '-r', '-z', commit, '--', 'ImbalancedChen'], cwd=repo)
    blobs = {x.split(b'\t', 1)[1].decode(): x.split(b'\t', 1)[0].split()[2].decode() for x in tree.split(b'\0') if x}
    graph, _, sources = d.project_context(project, {'helper': h, 'updates': updates, 'payloads': payloads, 'blob_ids': blobs})
    need(len(graph) == 92 and graph[DATA] == [READER] + targets[:-1] and
         all(graph[m] == [READER] for m in targets[:-1]), 'partition overlay dependency scope differs')
    fixtures = {x['path']: {'bytes': x['bytes'], 'sha256': x['sha256']} for x in manifest['data_inputs']}
    inventory = json.loads(raw[INVENTORY])
    need(len(fixtures) == len(manifest['data_inputs']) == 188 and fixtures ==
         {x['install_path']: {'bytes': x['bytes'], 'sha256': x['sha256']} for x in inventory['g3_files']} and
         sum(x['bytes'] for x in fixtures.values()) == 423244864, 'exact 188-file fixture inventory differs')
    subsets, covered = {}, []
    for row in rows[:-1]:
        pairs = re.findall(r'include_new_fifth_pair%\s+"([^"]+)"\s+"([^"]+)"', payloads[row['path']].decode())
        paths = [str(PurePosixPath(row['path']).parent / arg) for pair in pairs for arg in pair]
        need(paths == row['fixture_paths'] and len(paths) == 2 * len(row['owns_original_declarations']),
             'provider fixture include scope differs')
        subsets[row['module']] = paths
        covered.extend(paths)
    need(len(covered) == len(set(covered)) == 188 and set(covered) == set(fixtures), 'provider fixture ownership differs')
    subsets[DATA] = sorted(fixtures)
    reader_receipt = json.loads(raw[READER_RECEIPT])
    reader_sources = {m: sources[m] for m in sorted(h.closure(graph, [READER]))}
    need(len(reader_sources) == 67 and sources[READER] == READER_SHA and
         reader_receipt['status'] == api.PASS and reader_receipt['modules'][READER] == READER_SHA and
         reader_receipt['full_owned_including_private_generated'] is True and reader_receipt['only_standard_axioms'] is True and
         all(reader_receipt['project_dependency_sources'].get(m) == digest for m, digest in reader_sources.items()),
         'accepted Reader source/closure receipt differs')
    protected = dict(h.FOUR_ROOTS)
    for row in manifest['protected_sources'].values():
        need(sha(git(commit, row['path'])) == row['sha256'], 'published protected source differs')
        protected[row['module']] = row['sha256']
    review, observed = json.loads(raw[CONFIG_REVIEW]), json.loads(raw[OBSERVATION])['configs']
    source_config = {}
    for path in CONFIGS:
        raw[path] = git(commit, path)
        source_config[path] = {'bytes': len(raw[path]), 'sha256': sha(raw[path])}
        pins[path] = sha(raw[path])
    runtime_config = review['runtime_configuration_bindings']
    need(source_config == review['source_configuration_bindings'] and set(runtime_config) == set(CONFIGS) and
         runtime_config == {p: {k: observed[p][k] for k in ('bytes', 'sha256')} for p in CONFIGS} and
         all(observed[p]['exists'] and not observed[p]['is_symlink'] for p in CONFIGS) and
         not observed['lakefile.lean']['exists'] and not observed['lakefile.lean']['is_symlink'],
         'source/runtime configuration evidence differs')
    s = types.SimpleNamespace(repo=repo, project=project, commit=commit, module=module, root=ROOT / commit,
        api=api, h=h, ops=ops, d=d, raw=raw, pins=pins, manifest=manifest, targets=targets, updates=updates,
        payloads=payloads, graph=graph, sources=sources, fixtures=fixtures, subsets=subsets,
        reader_receipt=reader_receipt, reader_sources=reader_sources, protected=protected,
        source_config=source_config, runtime_config=runtime_config, runtime=review['existing_runtime_bindings'])
    source_preflight(s)
    check_configs(s, basis)
    need(all(sha((project / h.module_path(m)).read_bytes()) == digest for m, digest in protected.items()),
         'protected root/Reader/Archive/BoxIntegral source differs')
    if basis == 'runtime':
        check_environment(s)
    return s


def owner_root(s, m):
    return s.root / m


def normal_paths(s, m):
    folder = owner_root(s, m) / 'normal' / m
    return folder / 'NORMAL_PASS.json', folder / 'FIXTURE_BOUND_NORMAL.json'


def receipt_pair(normal, companion):
    present = os.path.lexists(normal), os.path.lexists(companion)
    need(present[0] == present[1], 'ORPHAN_GENERIC_NORMAL_OR_COMPANION_REQUIRES_INSPECTION')
    return present[0]


def audit_pair(root):
    present = os.path.lexists(root / 'FIXTURE_BOUND_AUDIT.json')
    directories, plans = list((root / 'audits').glob('*')), list((root / 'plans').glob('*'))
    need(present == bool(directories or plans), 'ORPHAN_OR_PARTIAL_AUDIT_REQUIRES_INSPECTION')
    if present:
        need(all(p.is_file() and not p.is_symlink() and p.suffix == '.json' for p in plans) and
             all(p.is_dir() and not p.is_symlink() for p in directories) and
             {p.stem for p in plans} == {p.name for p in directories},
             'ORPHAN_OR_PARTIAL_AUDIT_PLAN_REQUIRES_INSPECTION')
    return present


def ref(s, path):
    return {'path': str(path), 'sha256': s.d.fingerprint(path)['sha256']}


def old_monolith_gate(s, actions):
    old = OLD_ROOT / 'normal' / DATA
    need(not any(os.path.lexists(old / name) for name in ('NORMAL_PASS.json', 'FIXTURE_BOUND_NORMAL.json')),
         'OLD_MONOLITH_SUCCESS_OR_COMPANION_REQUIRES_INSPECTION')
    if next(x for x in actions if x['module'] == DATA)['action'] == 'REPLACE_PREIMAGE':
        for row in json.loads(s.raw[EXACT_FACETS])['files']:
            path = s.project / row['relative_path']
            need(not path.is_symlink(), 'failed monolith source/artifact became a symlink')
            need((path.is_file() and s.d.fingerprint(path) == {k: row[k] for k in ('bytes', 'sha256')})
                 if row['exists'] else not os.path.lexists(path), 'failed monolith artifact state changed; inspect first')


def data_artifacts(s):
    return {row['relative_path']: s.d.fingerprint(s.project / row['relative_path'])
            if (s.project / row['relative_path']).is_file() else None
            for row in json.loads(s.raw[EXACT_FACETS])['files'] if not row['relative_path'].endswith('.lean')}


def live(s, paths, installed):
    check_environment(s, installed)
    actual = {p: s.d.fingerprint(s.project / p) for p in sorted(paths)}
    need(actual == {p: s.fixtures[p] for p in sorted(paths)}, 'fixture size/SHA differs from original inventory')
    reader = s.d.snapshot(s.project, READER)
    need(reader == s.reader_receipt['source_plus_five_outputs'][READER], 'accepted Reader source/five outputs changed; no rebuild')
    state = s.reader_receipt['runtime_state']
    need(state in s.runtime and s.runtime[state]['sha256'] == s.reader_receipt['runtime_state_sha256'] and
         s.reader_receipt['audit_template_sha256'] == s.d.AUDIT_TEMPLATE_SHA, 'Reader accepted runtime binding differs')
    return {'fixtures': actual, 'reader_reuse': {'receipt_sha256': PINS[READER_RECEIPT],
            'source_plus_five_outputs': reader, 'project_sources': s.reader_sources}}


def input_binding(s, m, current):
    value = {'source_commit': s.commit, 'module': m, 'source_sha256': s.sources[m],
             'manifest_sha256': PINS[MANIFEST], 'inventory_sha256': PINS[INVENTORY],
             'fixtures': {p: current['fixtures'][p] for p in sorted(s.subsets[m])},
             'reader_reuse': current['reader_reuse']}
    if m == DATA:
        providers = {}
        for dep in s.targets[:-1]:
            bound = input_binding(s, dep, current)
            normal = normal_companion_valid(s, dep, bound)
            audit_companion_valid(s, dep, bound, normal)
            providers[dep] = {'normal_companion': ref(s, normal_paths(s, dep)[1]),
                              'audit_companion': ref(s, owner_root(s, dep) / 'FIXTURE_BOUND_AUDIT.json')}
        value['accepted_provider_companions'] = providers
    return value


def checkpoint(s, m, path):
    start = s.d.now()
    binding = input_binding(s, m, live(s, s.subsets[m], installed=True))
    value = {'checked_started_utc': start, 'checked_finished_utc': s.d.now(), 'input_binding': binding}
    s.d.save(path, value)
    return ref(s, path), value


def check_window(before, after, commands):
    def time(value):
        result = datetime.fromisoformat(value)
        need(result.utcoffset() is not None, 'checkpoint/command time requires a timezone')
        return result
    begin, end = time(before['checked_finished_utc']), time(after['checked_started_utc'])
    need(time(before['checked_started_utc']) <= begin <= end <= time(after['checked_finished_utc']) and commands,
         'invalid fixture checkpoint window')
    need(all(begin <= time(c['started_utc']) <= time(c['finished_utc']) <= end for c in commands),
         'fixture checkpoints do not enclose actual commands; no retrospective companion')


def check_checkpoints(s, m, phase, bound, current, commands):
    values = []
    for key, filename in (('before', 'FIXTURES_BEFORE.json'), ('after', 'FIXTURES_AFTER.json')):
        path = Path(bound[key]['path'])
        need(path.name == filename and path.parent.parent == owner_root(s, m) / 'runs' / phase and
             re.fullmatch(r'attempt-[0-9]{5}', path.parent.name) and ref(s, path) == bound[key], 'fixture checkpoint reference differs')
        value = s.api.read_json(path)
        need(value['input_binding'] == current, 'fixture checkpoint input binding differs')
        values.append(value)
    check_window(*values, commands)


def normal_companion_valid(s, m, current):
    normal_path, companion = normal_paths(s, m)
    need(receipt_pair(normal_path, companion), 'NO_FIXTURE_BOUND_NORMAL: ' + m)
    normal, bound = s.api.read_json(normal_path), s.api.read_json(companion)
    need(bound['schema'] == 'p1_g3_partition_fixture_normal_v1' and bound['source_commit'] == s.commit and
         bound['module'] == m and bound['input_binding'] == current and bound['normal_receipt'] == ref(s, normal_path) and
         bound['source_plus_five_outputs'] == normal['source_plus_five_outputs'] == s.d.snapshot(s.project, m),
         'fixture-bound normal differs: ' + m)
    s.api.normal_valid(s.commit, s.project, m, normal,
                       s.api.context(s.commit, s.project, m, s.graph, s.sources, s.h, s.d), s.h, s.d)
    check_checkpoints(s, m, 'normal', bound, current, [normal['normal_command']])
    return normal


def audit_evidence(s, m, normal):
    evidence, commands, accepted = {}, [], set()
    for directory in sorted((owner_root(s, m) / 'audits').glob('*')):
        need(directory.is_dir() and not directory.is_symlink(), 'unexpected audit entry')
        plan = s.api.read_json(directory / 'AUDIT_PLAN.json')
        need(s.api.read_json(owner_root(s, m) / 'plans' / (directory.name + '.json')) == plan,
             'original frozen audit plan differs')
        accepted.update(s.api.audit_valid(s.commit, s.project, directory, plan, {m: normal}, s.graph, s.sources, s.h, s.d))
        path = directory / 'lane-0/VALIDATION_RESULTS.json'
        result = s.api.read_json(path)
        evidence[str(path)] = s.d.fingerprint(path)
        commands += [result['stock_readiness_before'], *result['kernel_commands'].values(),
                     result['audit_command'], result['stock_readiness_after']]
    need(accepted == {m}, 'single-owner e9 audit did not complete: ' + m)
    return evidence, commands


def audit_companion_valid(s, m, current, normal):
    root = owner_root(s, m)
    need(audit_pair(root), 'NO_FIXTURE_BOUND_AUDIT: ' + m)
    bound = s.api.read_json(root / 'FIXTURE_BOUND_AUDIT.json')
    evidence, commands = audit_evidence(s, m, normal)
    need(bound['schema'] == 'p1_g3_partition_fixture_audit_v1' and bound['source_commit'] == s.commit and
         bound['module'] == m and bound['input_binding'] == current and
         bound['normal_companion'] == ref(s, normal_paths(s, m)[1]) and bound['validated_e9_results'] == evidence and
         bound['source_plus_five_outputs'] == s.d.snapshot(s.project, m), 'fixture-bound audit differs: ' + m)
    check_checkpoints(s, m, 'audit', bound, current, commands)
    return bound


def binding(s):
    return {'source_commit': s.commit, 'api_commit': API_COMMIT, 'module': s.module, 'all_partition_targets': s.targets,
            'project': str(PROJECT), 'driver_sha256': sha(Path(__file__).read_bytes()), 'inputs': s.pins,
            'project_sources': s.sources, 'source_configuration': s.source_config,
            'runtime_configuration': s.runtime_config, 'existing_runtime': s.runtime}


def worker(s, phase, run):
    root, m = owner_root(s, s.module), s.module
    s.d.verify_lane(s.h)
    need(s.api.read_json(root / 'BINDING.json') == binding(s), 'serialized worker binding changed')
    result = {'phase': phase, 'module': m, 'source_commit': s.commit, 'status': 'HELD_OR_FAILED',
              'reader_normal_repeated': False, 'downstream_94_Checked_accepted': False, 'whole_G3_or_P1_complete': False}
    try:
        actions = source_preflight(s)
        old_monolith_gate(s, actions)
        normal_path, companion = normal_paths(s, m)
        prior_present = receipt_pair(normal_path, companion)
        audit_present = audit_pair(root) if phase == 'audit' else False
        need(phase == 'normal' or prior_present, 'AUDIT_REQUIRES_FIXTURE_BOUND_NORMAL')
        live(s, s.fixtures, installed=False)  # Complete 188-file gate before any source installation.
        if phase == 'normal':
            artifacts = data_artifacts(s)
            installed = s.d.install_sources(s.project, s.updates, s.payloads, run / 'source-backups', s.h)
            need(data_artifacts(s) == artifacts, 'source installation changed existing Data artifacts')
            s.d.save(run / 'SOURCE_INSTALL.json', {'sources': installed, 'preserved_Data_artifacts': artifacts})
        else:
            need(all(x['action'] == 'ALREADY_AFTER_NOOP' for x in actions), 'audit requires every exact installed postimage')
        before_ref, before = checkpoint(s, m, run / 'FIXTURES_BEFORE.json')
        normal = normal_companion_valid(s, m, before['input_binding']) if prior_present else None
        if audit_present:
            audit_companion_valid(s, m, before['input_binding'], normal)
        accepted, errors = set(), []
        try:
            if phase == 'normal':
                normal = s.api.normal_one(s.commit, s.project, root, m, s.graph, s.sources, s.h, s.ops, s.d)
            else:
                s.api.audit(s.commit, s.project, root, {m: normal}, s.graph, s.sources, s.h, s.ops, s.d, run, accepted)
        except Exception as error:
            errors.append(str(error))
        try:
            after_ref, after = checkpoint(s, m, run / 'FIXTURES_AFTER.json')
            need(before['input_binding'] == after['input_binding'], 'fixtures/Reader/provider acceptance changed during phase')
        except Exception as error:
            errors.append('post-operation gate: ' + str(error))
        need(not errors, '; '.join(errors))
        if phase == 'normal' and not prior_present:
            need(s.api.read_json(normal_path) == normal, 'durable generic normal differs')
            check_window(before, after, [normal['normal_command']])
            s.d.save(companion, {'schema': 'p1_g3_partition_fixture_normal_v1', 'source_commit': s.commit, 'module': m,
                     'input_binding': after['input_binding'], 'before': before_ref, 'after': after_ref,
                     'normal_receipt': ref(s, normal_path), 'source_plus_five_outputs': normal['source_plus_five_outputs'],
                     'kernel_or_full_owned_claim': False, 'whole_G3_or_P1_complete': False})
        normal = normal_companion_valid(s, m, after['input_binding'])
        if phase == 'audit':
            need(accepted == {m}, 'single-owner audit did not complete')
            evidence, commands = audit_evidence(s, m, normal)
            if not audit_present:
                check_window(before, after, commands)
                s.d.save(root / 'FIXTURE_BOUND_AUDIT.json', {'schema': 'p1_g3_partition_fixture_audit_v1',
                         'source_commit': s.commit, 'module': m, 'input_binding': after['input_binding'],
                         'before': before_ref, 'after': after_ref, 'normal_companion': ref(s, companion),
                         'validated_e9_results': evidence, 'source_plus_five_outputs': s.d.snapshot(s.project, m),
                         'downstream_94_Checked_accepted': False, 'whole_G3_or_P1_complete': False})
            audit_companion_valid(s, m, after['input_binding'], normal)
        result.update(status='NORMAL_WITH_FIXTURES_VALIDATED' if phase == 'normal' else 'SINGLE_OWNER_ACCEPTED_WITH_FIXTURES',
                      normal_reused=prior_present, audit_reused=audit_present,
                      normal_companion=str(companion), source_installation_requested=phase == 'normal')
    except Exception as error:
        result['error'] = str(error)
        s.ops.emit('G3_PARTITION_HELD_OR_FAILED', phase=phase, module=m, reason=str(error))
    s.d.save(run / 'RESULT.json', result)
    s.ops.emit('G3_PARTITION_RESULT', **result)
    return 1 if result['status'] == 'HELD_OR_FAILED' else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--module', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ('check', 'normal', 'audit'):
        mode.add_argument('--' + flag, action='store_true')
    parser.add_argument('--config-basis', choices=('runtime', 'source'), default='runtime')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    repo, project = args.source_repo.resolve(), args.project.resolve()
    need(args.config_basis == 'runtime' or (args.check and project != PROJECT), 'source basis requires a non-cloud --check')
    need(args.check or (repo == REPO and project == PROJECT), 'execution requires the existing cloud paths')
    s = inputs(repo, project, args.source_commit, args.module, args.config_basis)
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        actions = source_preflight(s)
        if args.config_basis == 'runtime':
            old_monolith_gate(s, actions)
            current = live(s, s.fixtures, installed=False)
            if s.module == DATA:
                input_binding(s, DATA, current)
        print(json.dumps({'status': 'SOURCE_CONFIG_ONLY_NOT_CLOUD_READY' if args.config_basis == 'source' else
                         'READ_ONLY_FIXTURE_READER_RUNTIME_CHECK_PASS_NOT_ACCEPTANCE', 'source_commit': s.commit,
                         'module': s.module, 'manifest_sha256': PINS[MANIFEST], 'union_source_modules': len(s.sources),
                         'owner_source_modules': len(s.h.closure(s.graph, [s.module])), 'partition_owners': len(s.targets),
                         'fixture_count': len(s.fixtures), 'owner_fixture_count': len(s.subsets[s.module]),
                         'configuration_basis': args.config_basis, 'source_configuration': s.source_config,
                         'runtime_configuration': s.runtime_config,
                         'actions': {a: sum(x['action'] == a for x in actions) for a in
                                     ('ALREADY_AFTER_NOOP', 'REPLACE_PREIMAGE', 'CREATE_ABSENT')},
                         'no_source_or_receipt_writes': True, 'no_Lean_or_Lake_run': True,
                         'cloud_runtime_readiness_claimed': False, 'whole_G3_or_P1_complete': False}))
        return 0
    root = owner_root(s, s.module)
    phase = 'normal' if args.normal else 'audit'
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' / phase and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(), 'invalid run directory')
        return worker(s, phase, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = s.d.original_git_state(repo)
    s.d.save(root / 'BINDING.json', binding(s))
    for path, raw in s.raw.items():
        name = 'source-configuration/' + path if path in CONFIGS else 'e9.py' if path == s.api.E9 else Path(path).name
        s.d.write_frozen(root / 'inputs' / name, raw)
    executed = root / 'executed-driver.py'
    s.d.write_frozen(executed, Path(__file__).read_bytes())
    run = s.d.attempt(root / 'runs' / phase)
    s.d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--source-commit', s.commit, '--module', s.module,
             '--' + phase, '--config-basis', 'runtime', '--inside-lane', '--run-dir', str(run)]
    try:
        command = s.ops.run(run, 'serialized-worker', s.h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        return command['exit_code']
    finally:
        after = s.d.original_git_state(repo)
        s.d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty source Git state changed')


if __name__ == '__main__':
    raise SystemExit(main())
