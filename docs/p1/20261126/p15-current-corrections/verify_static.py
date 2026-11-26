#!/usr/bin/env python3
"""Pure Python/Git source checks and isolated fixtures; no driver main or Lean."""
from copy import deepcopy
from functools import lru_cache
from pathlib import Path
from types import ModuleType, SimpleNamespace
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
ANCHOR = '6067deae48cbdc0095ac12acc47e24a6ef29cb69'
OLD_RUNNER = 'docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py'
OLD_RUNNER_SHA = '81b9e49db7b5c9585f6d5bef12f383898c8a8f8f4ff65786d2cb22e4b3316af0'
UNCHANGED = ['require', 'git_file', 'pinned', 'helpers', 'file_binding', 'regular_fingerprint',
    'run_owner', 'artifact_paths', 'module_artifacts', 'require_fresh_owner', 'existing_owner',
    'require_completed_existing_owner', 'acceptance_binding', 'direct_import_readiness']
CASES = []


def need(ok, message):
    if not ok:
        raise AssertionError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


@lru_cache(None)
def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def pin(path):
    raw = path.read_bytes()
    return {'bytes': len(raw), 'sha256': sha(raw)}


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph[module])
    return seen


def imports(raw):
    return [module for line in re.findall(r'^import\s+([^\n]+)$', raw.decode(), re.M) for module in line.split()]


def functions(raw):
    return {node.name: node for node in ast.parse(raw).body if isinstance(node, ast.FunctionDef)}


def module_from(path, name):
    module = ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def case(name, action, reject=False):
    try:
        value = action()
    except (ValueError, AssertionError, KeyError) as error:
        need(reject, name + ': ' + str(error))
        reason = re.sub(re.escape(tempfile.gettempdir()) + r'/p15-correction-fixture-[^/\s]+',
                        '<isolated-fixture>', str(error))
        CASES.append({'case': name, 'result': 'EXPECTED_HOLD', 'reason': reason})
        return None
    need(not reject, name + ': incorrectly allowed')
    CASES.append({'case': name, 'result': 'PASS'})
    return value


def main():
    need((REPO / '.git').exists(), 'repository root differs')
    runner_path, installer_path = HERE / 'run_selected.py', HERE / 'install_sources.py'
    runner_raw, installer_raw = runner_path.read_bytes(), installer_path.read_bytes()
    old = git_file(ANCHOR, OLD_RUNNER)
    need(sha(old) == OLD_RUNNER_SHA, 'published integration template pin differs')
    current_functions, original_functions = functions(runner_raw), functions(old)
    for name in UNCHANGED:
        need(ast.dump(current_functions[name], include_attributes=False) ==
             ast.dump(original_functions[name], include_attributes=False), 'borrowed function changed: ' + name)
    runner = module_from(runner_path, 'isolated_correction_source_readers')
    installer = module_from(installer_path, 'isolated_addition_planner')
    # No helpers(), preflight(), worker(), main(), installer main(), or live
    # acceptance API is invoked. Replace the sole reader with local Git bytes.
    def local_file(commit, path):
        if commit == 'UNPUBLISHED_STATIC_FIXTURE' and path.startswith('docs/p1/20261126/p15-current-corrections/'):
            return (REPO / path).read_bytes()
        return git_file(ANCHOR if commit == 'UNPUBLISHED_STATIC_FIXTURE' else commit, path)
    runner.git_file = local_file
    fake = SimpleNamespace(api=SimpleNamespace(sha=sha), h=SimpleNamespace(imports=imports,
        module_path=lambda module: module.replace('.', '/') + '.lean', closure=closure))
    manifest_json = json.loads((HERE / 'SOURCE_MANIFEST.json').read_bytes())
    first = manifest_json['selection_guidance']['minimum_first_targets']
    manifest, graph, sources, observed, binding = case('full_360_published_source_and_provenance_readers',
        lambda: runner.source_manifest(fake, 'UNPUBLISHED_STATIC_FIXTURE', first))
    need(len(graph) == 360 and len(closure(graph, first)) == 130, '360/130 source count differs')
    need(set(closure(graph, first)) & set(runner.TARGETS) == set(first), 'first-three selection was expanded')
    ready = manifest['selection_guidance']['project_graph_unblocked_candidates']
    need(len(ready) == 18 and len(closure(graph, ready)) == 157, '18/157 project graph scope differs')
    blocked = set(manifest['unaccepted_p3_dependencies'])
    need(sorted(module for module in runner.TARGETS if closure(graph, [module]) & blocked) ==
         manifest['selection_guidance']['project_graph_blocked_candidates'], 'blocked candidate partition differs')
    for name, roots, reject in [('explicit_first3', first, False), ('reversed_explicit_first3', first[::-1], False),
            ('no_implicit_full_scope', None, True), ('empty_scope', [], True),
            ('duplicate_owner', first + [first[0]], True),
            ('accepted_Core_cannot_be_target', ['ImbalancedChen.Part3FiniteLambdaOverLogCore'], True),
            ('Geometry_requires_separate_revision', ['ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry'], True),
            ('P3_owner_cannot_be_target', ['ImbalancedChen.Part3BrunWeights'], True)]:
        case(name, lambda roots=roots: runner.selection(roots), reject)

    # Every retained-context recipe is tied to a published normal receipt hash,
    # not to a source hash used as a substitute object fingerprint.
    originals, summaries = {}, {}
    for name, group in manifest['accepted_supplier_groups'].items():
        raw = runner.published_binding(group['source_graph'])
        original = json.loads(raw)
        original_graph = {module: row['imports'] for module, row in original['project_sources'].items()}
        originals[name] = (original, original_graph)
        summaries[name] = json.loads(runner.published_binding(group['public_evidence']))
        need(len(original_graph) == group['published_source_count'], 'original graph count differs')
        need(sha(runner.published_binding(group['driver'])) == group['driver']['sha256'], 'old driver differs')
        for owner in group['owners']:
            active = closure(original_graph, [owner])
            need(active == closure(graph, [owner]) and all(
                original['project_sources'][module]['sha256'] == sources[module] for module in active),
                'accepted owner source closure differs: ' + owner)
            if name != 'mellin':
                owner_record = summaries[name]['owners'][owner]
                need(owner_record['source_commit'] == group['source_commit'] and
                     owner_record['source_sha256'] == sources[owner] and
                     runner.valid_fingerprint(owner_record['receipt_bindings']['normal']),
                     'original normal receipt hash missing: ' + owner)
    for module, policy in manifest['fixed_dependencies'].items():
        if policy['kind'] == 'retained_accepted_normal_dependency_context':
            witness = policy['witness_owner']
            group = manifest['accepted_suppliers'][witness]['group']
            original, original_graph = originals[group]
            need(module in closure(original_graph, [witness]) - {witness} and
                 original['project_sources'][module]['sha256'] == sources[module] and group != 'mellin',
                 'fixed dependency context coverage differs')
        else:
            record = observed['modules'][module]
            need(record['source']['sha256'] == sources[module] and
                 all(runner.valid_fingerprint(record['outputs'][ext]) for ext in ('.olean', '.trace')),
                 'observed cache pin missing')
    CASES.append({'case': '295_historical_context_witnesses_and_8_real_object_observations', 'result': 'PASS'})

    # Execute only the literal-import gate with a fake recorder. A failed stock
    # command, a successful command that built something, and malformed imports
    # must all hold before the immutable normal/audit path could run.
    good_module = first[0]
    recorded = []
    stock = {'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': []}
    mock_ops = SimpleNamespace(run=lambda folder, name, argv, **kw: recorded.append(argv) or deepcopy(stock))
    gate_s = SimpleNamespace(ops=mock_ops, h=SimpleNamespace(guard=lambda lane, argv: ['guard', lane, *argv]))
    literal = ['ImbalancedChen.P1OriginalSingletonPointwiseData', 'Mathlib.MeasureTheory.Integral.Bochner.Basic']
    gate_spec = SimpleNamespace(manifest={'project_sources': {good_module: {'all_imports': literal}}})
    case('direct_gate_checks_all_literal_imports_lane0',
         lambda: runner.direct_import_readiness(gate_s, gate_spec, good_module, Path('/fixture')))
    need(recorded[-1] == ['guard', 0, 'lake', '--no-build', 'build',
                         *['+' + module + ':olean' for module in literal]], 'literal gate command differs')
    for name, changes in [('native_readiness_exit3', {'exit_code': 3}),
                          ('no_build_gate_cannot_build', {'actual_built_modules': [good_module]}),
                          ('no_build_gate_cannot_fail_module', {'actual_failed_modules': [good_module]})]:
        before = deepcopy(stock)
        stock.update(changes)
        case(name, lambda: runner.direct_import_readiness(gate_s, gate_spec, good_module, Path('/fixture')), True)
        stock.clear(); stock.update(before)
    gate_spec.manifest['project_sources'][good_module]['all_imports'] = []
    case('empty_imports_never_trigger_bare_default_build',
         lambda: runner.direct_import_readiness(gate_s, gate_spec, good_module, Path('/fixture')), True)

    # Old Core acceptance remains a one-node live closure even when unrelated
    # old Mellin bytes in the full 168-node historical publication differ.
    core = 'ImbalancedChen.Part3FiniteLambdaOverLogCore'
    mellin = 'ImbalancedChen.PrimeProductsMellinExactMeanInsertion'
    core_commit = manifest['accepted_suppliers'][core]['source_commit']
    core_group = SimpleNamespace(commit=core_commit, graph={core: [], mellin: []},
        sources={core: sources[core], mellin: 'old-Mellin'}, base=Path('/fixture/old-Core'),
        public={'owners': {core: {'receipt_bindings': {'normal': {'bytes': 1, 'sha256': 'f' * 64}}}}})
    core_spec = SimpleNamespace(manifest=manifest, graph={core: [], mellin: []},
        sources={core: sources[core], mellin: sources[mellin]}, review={'runtime_configuration_bindings': {},
        'existing_runtime_bindings': {}}, historical_owners={})
    original_context = {'source_commit': core_commit, 'project_sources': {core: sources[core]},
                        'dependency_objects_and_traces': {}, 'configuration': {}, 'existing_runtime': {}}
    normal = {'module': core, 'source_commit': core_commit, 'status': 'NORMAL_PASS_AUDIT_PENDING',
              'dependency_context': original_context}
    old_group_fn, old_read_fn = runner.historical_group, runner.retained_read
    runner.historical_group = lambda *args: core_group
    runner.retained_read = lambda *args: json.dumps(normal).encode()
    case('Core_keeps_ef450_identity_despite_unrelated_Mellin_epoch', lambda: runner.retained_owner(fake, core_spec, core))
    core_spec.historical_owners.clear()
    core_spec.sources[core] = 'changed-Core'
    case('changed_selected_Core_source_holds', lambda: runner.retained_owner(fake, core_spec, core), True)
    core_spec.sources[core] = sources[core]
    normal['dependency_context']['source_commit'] = manifest['accepted_suppliers'][mellin]['source_commit']
    case('Core_receipt_cannot_be_rebound_to_Mellin_commit', lambda: runner.retained_owner(fake, core_spec, core), True)
    runner.historical_group, runner.retained_read = old_group_fn, old_read_fn

    # The published Mellin terminal observation also fixes the outer audit-lane
    # log. Exercise its real retained_read path on fixture bytes, without any
    # live acceptance API or execution of a driver/installer entrypoint.
    with tempfile.TemporaryDirectory(prefix='p15-correction-fixture-') as directory:
        fixed = deepcopy(manifest['accepted_supplier_groups']['mellin'])
        fixed['evidence_root'] = directory
        run = Path(directory) / fixed['source_commit'] / fixed['run']
        (run / mellin).mkdir(parents=True)
        public = deepcopy(summaries['mellin'])
        published_reader = runner.published_binding
        (run / 'executed-driver.py').write_bytes(published_reader(fixed['driver']))
        (run / 'RESULT.json').write_text(json.dumps({key: value for key, value in public['result'].items()
            if key not in ('batch6', 'path')}))
        for stem in ('CONTEXT', 'GIT'):
            for suffix in ('BEFORE', 'AFTER'):
                (run / (stem + '_' + suffix + '.json')).write_bytes(b'{}\n')
        audit_log = run / mellin / 'audit-lane-0.log'
        audit_raw = b'isolated successful audit-lane fixture\n'
        audit_log.write_bytes(audit_raw)
        audit_row = next(row for row in public['normal_and_audit'] if row.get('name') == 'audit-lane-0')
        audit_row['log_sha256'] = sha(audit_raw)
        runner.published_binding = lambda value: (json.dumps(public).encode()
            if value == fixed['public_evidence'] else published_reader(value))
        def mellin_fixture():
            fixture = SimpleNamespace(manifest={'accepted_supplier_groups': {'mellin': fixed}},
                historical_groups={}, retained_inputs={})
            runner.historical_group(fake, fixture, 'mellin')
            need(fixture.retained_inputs[str(audit_log)] == pin(audit_log),
                 'Mellin audit log was not included in retained input preservation')
            return fixture
        case('Mellin_published_audit_log_bound_and_preserved', mellin_fixture)
        audit_log.write_bytes(b'different audit log\n')
        case('Mellin_wrong_published_audit_log_SHA_holds', mellin_fixture, True)
        audit_log.write_bytes(audit_raw)
        audit_row['exit_code'] = 1
        case('Mellin_unsuccessful_published_audit_lane_holds', mellin_fixture, True)
        runner.published_binding = published_reader

    # The addition planner runs against a temporary fixture tree, with every
    # external/runtime function replaced. No production installer is invoked.
    with tempfile.TemporaryDirectory(prefix='p15-correction-fixture-') as directory:
        project = Path(directory)
        (project / 'ImbalancedChen').mkdir()
        target, dependency = 'ImbalancedChen.FixtureTarget', 'ImbalancedChen.FixtureDependency'
        payloads = {target: b'import ImbalancedChen.FixtureDependency\n', dependency: b'import Mathlib\n'}
        fixture_graph = {target: [dependency], dependency: []}
        fixture_sources = {m: sha(raw) for m, raw in payloads.items()}
        source_path = lambda m: project / (m.replace('.', '/') + '.lean')
        source_path(dependency).write_bytes(payloads[dependency])
        fixture_review = {'source_configuration_bindings': {}}
        cache = {target: {'fixture.olean': None}, dependency: {'fixture.olean': {'bytes': 1, 'sha256': '0' * 64}}}
        fixture_driver = SimpleNamespace(TARGETS=[target], REVIEW='fixture-review', REVIEW_SHA='fixture',
            selection=lambda selected: selected,
            source_manifest=lambda *args: ({}, fixture_graph, fixture_sources, {}, {}),
            pinned=lambda *args: json.dumps(fixture_review).encode(), environment=lambda *args: {},
            module_artifacts=lambda s, m: deepcopy(cache[m]), require_fresh_owner=runner.require_fresh_owner,
            file_binding=lambda path: sha(path.read_bytes()))
        fixture_s = SimpleNamespace(h=SimpleNamespace(closure=closure,
            module_path=lambda module: module.replace('.', '/') + '.lean'), api=SimpleNamespace(sha=sha))
        installer.PROJECT = project
        installer.git_file = lambda commit, path: (installer_raw if path.endswith('install_sources.py')
            else payloads[path[:-5].replace('/', '.')])
        result = case('additive_plan_accepts_only_absent_selected_source',
            lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]))
        need([row[0] for row in result['planned']] == [target] and not source_path(target).exists(),
             'planning wrote a file or broadened target list')
        source_path(target).write_bytes(b'conflicting source\n')
        case('existing_different_source_has_no_overwrite_path',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)
        source_path(target).unlink()
        cache[target]['fixture.olean'] = {'bytes': 1, 'sha256': '0' * 64}
        case('absent_source_with_existing_artifact_holds',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)
        cache[target]['fixture.olean'] = None
        source_path(dependency).unlink()
        case('missing_unselected_dependency_is_not_auto_installed',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)
        source_path(dependency).write_bytes(payloads[dependency])
        source_path(target).symlink_to(source_path(dependency))
        case('symlink_source_is_not_followed_or_replaced',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)

    # Exactly one project write primitive exists, under the prevalidated plan,
    # and it requires O_EXCL. The runner has no project/cache write primitive.
    opens = [node for node in ast.walk(ast.parse(installer_raw)) if isinstance(node, ast.Call) and
             isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and
             node.func.value.id == 'os' and node.func.attr == 'open']
    need(len(opens) == 1 and 'O_EXCL' in ast.unparse(opens[0].args[1]) and
         'O_TRUNC' not in ast.unparse(opens[0]), 'additive write primitive broadened')
    need(not any(isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and
        node.func.attr in {'unlink', 'remove', 'rename', 'rmtree', 'install_sources'}
        for node in ast.walk(ast.parse(runner_raw + b'\n' + installer_raw))), 'destructive/cache writer present')
    runtime_paths = [runner.API, 'docs/p1/20261124/batch5-parallel/run_batch5_parallel.py',
        'docs/p1/20261125/p15-singleton-proper-power/P3_REUSE.json',
        'docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py',
        'docs/p1/20261125/p15-original-atlas-proper-power/run_selected.py']
    for path in runtime_paths:
        need((REPO / path).read_bytes() == git_file(ANCHOR, path), 'protected old source changed: ' + path)
    receipt = {'schema': 'p15_current_corrections_local_static_verification_v1',
        'status': 'PASS_LOCAL_SOURCE_BINDINGS_AST_PRESERVATION_AND_ISOLATED_PYTHON_FIXTURES_ONLY',
        'source_anchor_commit': ANCHOR,
        'inputs': {name: pin(HERE / name) for name in ['SOURCE_MANIFEST.json', 'FIXED_DEPENDENCY_OBSERVATIONS.json',
                                                     'run_selected.py', 'install_sources.py', 'verify_static.py', 'README.md']},
        'unchanged_original_functions': UNCHANGED, 'immutable_template_sha256': OLD_RUNNER_SHA,
        'counts': {'targets': 21, 'published_project_sources': 360, 'accepted_supplier_whitelist': 17,
            'fixed_dependencies': 303, 'retained_normal_context_witnesses': 295,
            'recorded_object_dependencies': 8, 'unaccepted_P3_suppliers': 19,
            'first3_selected_source_closure': 130, 'project_unblocked18_source_closure': 157},
        'fixtures': CASES, 'fixture_count': len(CASES),
        'driver_or_installer_entrypoints_executed': False, 'live_acceptance_API_invoked': False,
        'Lean_or_kernel_invoked': False, 'cloud_jobs_submitted': False, 'new_lean_acceptance': False,
        'protected_old_paths_unchanged': runtime_paths, 'whole_P1_5_complete': False}
    (HERE / 'STATIC_VERIFICATION.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'fixture_count': len(CASES),
        'receipt': pin(HERE / 'STATIC_VERIFICATION.json')}, ensure_ascii=False))


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    main()
