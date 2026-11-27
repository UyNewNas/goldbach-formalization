#!/usr/bin/env python3
"""Probe the exact historical coefficient dictionary without object outputs.

The dictionary has 288 retained project dependencies, distinct from AG's 144.
The original atlas normal-context witness has a separate 58-source evidence
scope. Neither scope is a new acceptance, source installation, or build request.
"""
from pathlib import Path
from types import ModuleType, SimpleNamespace
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
ACCEPT_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-historical-coefficient-dictionary-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-historical-coefficient-dictionary-probe-v1')
AI = '6d9072f7b33332eaf5ecfff22876e0404cd6ab51'
AJ = '6d87764cbc9fce5b10a2665a458619e44d8255ae'
AK = 'd4f88a20262af7d54ed0e6e58dfc533496c595e3'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
PACKAGE = 'docs/p1/20261127/p15-historical-coefficient-dictionary/'
SCRIPT = PACKAGE + 'probe_dictionary.py'
READER = 'docs/p1/20261126/p15-trimlog-accuracy/run_trimlog.py'
READER_FP = {'bytes': 36541, 'sha256': '0c6307af83c197123bd2da678bfd4ac6b76916169d6d457f83733461725b8272'}
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/TRIMLOG_AI_PUBLIC_ACCEPTANCE.json'
PUBLIC_FP = {'bytes': 18539, 'sha256': '2bb01aa28ab117933b0ec8f766245f0a9faaeb750448bb6e47536c4dbfdf18f0'}
TARGET = 'ImbalancedChen.P1OriginalHistoricalCoefficientDictionary'
SOURCE = 'ImbalancedChen/P1OriginalHistoricalCoefficientDictionary.lean'
ORIGIN = 'docs/source-only/20261127/p1-historical-coefficient-dictionary/P1OriginalHistoricalCoefficientDictionary.lean'
SOURCE_FP = {'bytes': 9079, 'sha256': 'b90556b05b152cea39fd72eb55428986105ad86a4926e2badf50175927c47409'}
PROJECT_IMPORTS = ['ImbalancedChen.P1Full87TrueDUnitBound',
                   'ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData']
EXTERNAL_IMPORTS = ['Mathlib.Data.Complex.Basic']
IMPORTS = PROJECT_IMPORTS + EXTERNAL_IMPORTS
INITIAL4 = ['ImbalancedChen.P1Full87TrueDPolicyDelta',
            'ImbalancedChen.P1Full87TrueDUnitBound',
            'ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData',
            'ImbalancedChen.P1OriginalSingletonPointwiseData']
WITNESS = 'ImbalancedChen.P5SmoothChartHBDyadicPartition'
FIXED_WITNESS_COUNTS = {'ImbalancedChen.P1Full87TrueDPolicyDelta': 177,
                        'ImbalancedChen.P1OriginalSingletonPointwiseData': 60,
                        WITNESS: 47}
INITIAL4_COMMIT = 'd20acdf13882e17d97833064f5e7c54f3192b03c'
ATLAS10_COMMIT = '418ad4b9a5f2d992871062258a2eefd7fdf4b9ee'
SUFFIXES = ['.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
            '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash',
            '.ir', '.ir.hash', '.ir.sig', '.c', '.c.hash', '.bc', '.bc.hash',
            '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace']


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def closure(graph, roots):
    seen = set()

    def visit(module):
        if module in seen:
            return
        require(module in graph, 'missing project dependency: ' + module)
        seen.add(module)
        for imported in graph[module]:
            visit(imported)

    for root in roots:
        visit(root)
    return seen


def scope(manifest, initial_graph, atlas_graph):
    rows = manifest['project_sources']
    graph = {m: row['imports'] for m, row in rows.items()}
    require(len(graph) == 360 and TARGET not in graph, 'old graph/new owner scope differs')
    dependencies = closure(graph, PROJECT_IMPORTS)
    old_active = closure(graph, ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'])
    witness = closure(graph, [WITNESS])
    require(len(dependencies) == 288 and len(old_active) == 144
            and len(dependencies - old_active) == 180,
            'dictionary needs its exact 288-source scope, not the original AG144 scope')
    require(not (dependencies | witness).intersection(manifest['unaccepted_p3_dependencies']),
            'unaccepted P3 dependency entered dictionary or witness scope')
    suppliers, fixed = set(manifest['accepted_suppliers']), set(manifest['fixed_dependencies'])
    require(dependencies & suppliers == set(INITIAL4) and len(dependencies & fixed) == 284
            and (dependencies & suppliers) | (dependencies & fixed) == dependencies
            and not suppliers.intersection(fixed), 'dependency acceptance classification differs')
    require(all(manifest['accepted_suppliers'][m]['group'] == 'initial4' for m in INITIAL4)
            and manifest['accepted_suppliers'][WITNESS]['group'] == 'atlas10',
            'original supplier evidence groups differ')
    groups = manifest['accepted_supplier_groups']
    require(groups['initial4']['source_commit'] == INITIAL4_COMMIT
            and set(groups['initial4']['owners']) == set(INITIAL4)
            and groups['atlas10']['source_commit'] == ATLAS10_COMMIT,
            'original accepting commits or owners differ')
    old_rows = initial_graph['project_sources']
    old_graph = {m: row['imports'] for m, row in old_rows.items()}
    require(len(old_graph) == 316 and closure(old_graph, INITIAL4) == dependencies
            and all(all(rows[m][k] == old_rows[m][k] for k in ('path', 'sha256', 'imports'))
                    for m in dependencies), 'initial4 original 288-source context differs')
    atlas_rows = atlas_graph['project_sources']
    atlas = {m: row['imports'] for m, row in atlas_rows.items()}
    require(len(atlas) == 68 and closure(atlas, [WITNESS]) == witness
            and len(witness) == 58 and witness <= old_active and len(witness - dependencies) == 11
            and all(all(rows[m][k] == atlas_rows[m][k] for k in ('path', 'sha256', 'imports'))
                    for m in witness), 'separate atlas witness context differs')
    counts = {}
    for module in sorted(dependencies & fixed):
        policy = manifest['fixed_dependencies'][module]
        name = policy.get('witness_owner')
        require(policy['kind'] == 'retained_accepted_normal_dependency_context'
                and policy['required_extensions'] == ['.olean', '.trace']
                and name in FIXED_WITNESS_COUNTS
                and module in closure(graph, [name]) - {name},
                'fixed dependency lacks its original accepted-normal witness: ' + module)
        counts[name] = counts.get(name, 0) + 1
    require(counts == FIXED_WITNESS_COUNTS, 'fixed dependency witness partition differs')
    return {'owner': TARGET, 'project_direct_imports': PROJECT_IMPORTS,
            'external_direct_imports': EXTERNAL_IMPORTS,
            'project_dependency_count': 288, 'project_source_count_with_owner': 289,
            'dependency_sources': {m: {k: rows[m][k] for k in ('path', 'bytes', 'sha256')}
                                   for m in sorted(dependencies)},
            'accepted_suppliers': INITIAL4, 'fixed_dependency_count': 284,
            'fixed_dependency_witness_counts': counts,
            'same_as_original_initial4_accepted_closure': True,
            'original_AG_scope_count': 144, 'dependencies_outside_original_AG': sorted(dependencies - old_active),
            'dictionary_artifact_slots': 6048, 'P3_hold_intersection': [],
            'separate_original_evidence_scope': {'owner': WITNESS, 'source_count': 58,
                'sources': sorted(witness), 'outside_dictionary': sorted(witness - dependencies),
                'within_original_AG144': True, 'not_added_to_dictionary_import_graph': True,
                'artifact_slots': 1218}}


def require_original_acceptance(report, published):
    require(report['status'] == 'ORIGINAL_TRIMLOG_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION'
            and report['new_owner_accepted'] is True
            and report['normal_or_kernel_commands_executed'] == 0
            and report['identity']['source_commit'] == AI
            and published['source_commit'] == AI
            and published['status'] == 'NORMAL_KERNEL_ALL_OWNED_ACCEPTED_AND_READ_BACK',
            'original AI acceptance is not a complete read-only acceptance')
    owner = report['owner']
    require(owner['binding'] == published['owner_binding']
            and owner['audit_id'] == published['audit_id'] == '3d934c02c7fcb8f3a335'
            and owner['owned_count'] == published['owned_count'] == 4
            and owner['public_count'] == published['public_count'] == 4
            and owner['full_owned_including_private_generated'] is True
            and owner['only_standard_axioms'] is True
            and published['normal_exit_code'] == published['final_stock_exit_code'] == 0
            and set(published['kernel_exit_codes'].values()) == {0}
            and report['accepting_run']['path'] == published['original_accepting_run']['path']
            and report['accepting_run']['new_owner_accepted'] is True
            and report['accepting_run']['recompiled_by_check'] is False,
            'original AI owned declarations or accepting-run binding differs')


def require_fresh_slot(source, artifacts, history):
    require(source is None, 'dictionary canonical source is already installed; inspect before probing')
    require(len(artifacts) == 21 and all(v is None for v in artifacts.values()) and not history,
            'dictionary has artifacts or started acceptance history; inspect without recompiling')


def dictionary_history():
    found = []
    require(OLD_ROOT.is_dir(), 'old evidence root is missing')
    for root in (OLD_ROOT, ACCEPT_ROOT):
        if not os.path.lexists(root):
            continue
        require(root.is_dir() and root.resolve() == root, 'nonregular dictionary evidence root')
        for folder in sorted(root.iterdir()):
            if re.fullmatch('[0-9a-f]{40}', folder.name) and os.path.lexists(folder / TARGET):
                owner = folder / TARGET
                require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder
                        and owner.is_dir() and not owner.is_symlink() and owner.resolve() == owner,
                        'nonregular dictionary owner history')
                found.append(str(owner))
    return found


def load_original(publication, executed):
    require(__debug__ and re.fullmatch('[0-9a-f]{40}', publication), 'exact publication commit required')
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', AK, publication], cwd=REPO).returncode == 0,
            'probe publication must descend from the frozen AK source')
    require(executed == git_file(publication, SCRIPT), 'probe entrypoint differs from its publication')
    raw = git_file(AI, READER)
    entry = OLD_ROOT / AI / 'runs/attempt-00000/executed-trimlog.py'
    require(raw_fp(raw) == READER_FP and entry.is_file() and not entry.is_symlink()
            and entry.read_bytes() == raw and git_file(publication, READER) == raw,
            'immutable original AI reader differs')
    base = ModuleType('immutable_dictionary_AI_reader')
    base.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), base.__dict__)
    c = base.load(AI, raw)
    source = git_file(AK, ORIGIN)
    require(raw_fp(source) == SOURCE_FP and git_file(publication, ORIGIN) == source
            and c.ag.h.imports(source) == IMPORTS, 'complete frozen dictionary source/imports differ')
    pub = git_file(AJ, PUBLIC)
    require(raw_fp(pub) == PUBLIC_FP and git_file(publication, PUBLIC) == pub,
            'original AJ public acceptance differs')
    # Use the immutable entrypoint with its original valid selection. Its returned
    # AG144 binding is retained under its own name, never relabelled as D288.
    manifest, graph, sources, observed, original_inputs = c.g.source_manifest(c.ag, AG, base.AG_OWNERS)
    groups = manifest['accepted_supplier_groups']
    initial = json.loads(c.g.published_binding(groups['initial4']['source_graph']))
    atlas = json.loads(c.g.published_binding(groups['atlas10']['source_graph']))
    selected = scope(manifest, initial, atlas)
    review_raw = c.g.pinned(AG, c.g.REVIEW, c.g.REVIEW_SHA)
    review = json.loads(review_raw)
    for path, expected in review['source_configuration_bindings'].items():
        require(raw_fp(git_file(AG, path)) == expected, 'original published configuration differs: ' + path)
    context = SimpleNamespace(manifest=manifest, graph=graph, sources=sources, observed=observed,
        review=review, original_inputs=original_inputs, review_binding={
            'commit': AG, 'path': c.g.REVIEW, **raw_fp(review_raw)})
    return base, c, source, json.loads(pub), selected, context


def readonly_spec(context, active, name, selected):
    return SimpleNamespace(manifest=context.manifest, graph=context.graph, sources=context.sources,
        observed=context.observed, review=context.review, active=set(active), selected=set(),
        input_bindings={'schema': 'p15_dictionary_independent_readonly_dependency_scope_v1',
            'scope_name': name, 'active_source_count': len(active),
            'original_AG_manifest_binding': context.original_inputs,
            'runtime_review': context.review_binding, 'dictionary_scope': selected,
            'no_new_compilation_owner_selected': True},
        retained_inputs={}, historical_groups={}, historical_owners={},
        supplier_evidence={}, dependency_pins={})


def require_snapshot_scope(value, active, count):
    require(len(active) == count and set(value['selected_live_sources']) == set(active)
            and set(value['preserved_dependency_artifacts']) == set(active)
            and all(len(paths) == 21 for paths in value['preserved_dependency_artifacts'].values())
            and sum(map(len, value['preserved_dependency_artifacts'].values())) == 21 * count,
            'full retained-source/artifact protection scope is incomplete')


def prepare_dependency_scopes(c, context, selected):
    dependencies = set(selected['dependency_sources'])
    observed_graph, observed = c.ag.h.project_graph(PROJECT, PROJECT_IMPORTS)
    require(observed_graph == {m: context.graph[m] for m in dependencies}
            and {m: row['sha256'] for m, row in observed.items()} ==
                {m: context.sources[m] for m in dependencies},
            'installed dictionary dependency source graph differs; no installation or rebuild permitted')
    direct = readonly_spec(context, dependencies, 'dictionary_project_dependencies_288', selected)
    c.g.environment(c.ag, context.review)
    for module in INITIAL4:
        c.g.retained_owner(c.ag, direct, module, validate_live=True)
        direct.dependency_pins[module] = c.g.module_artifacts(c.ag, module)
    for module in sorted(dependencies - set(INITIAL4)):
        direct.dependency_pins[module] = c.g.fixed_dependency_pins(c.ag, direct, module)
    require(set(direct.dependency_pins) == dependencies and set(direct.supplier_evidence) == set(INITIAL4),
            'dictionary original supplier/fixed pin inventory differs')
    direct.baseline = c.g.snapshot(c.ag, direct)
    require_snapshot_scope(direct.baseline, dependencies, 288)

    # validate_live=True on this witness requires all 58 original sources. That
    # scope is separate; its 11 extra modules never enter the dictionary graph.
    witness_set = set(selected['separate_original_evidence_scope']['sources'])
    witness = readonly_spec(context, witness_set, 'original_atlas_normal_witness_58', selected)
    original = c.g.retained_owner(c.ag, witness, WITNESS, validate_live=True)
    require(original.normal == direct.historical_owners[WITNESS].normal,
            'fixed dependency pins and separate accepted witness use different normal receipts')
    witness.dependency_pins = {m: c.g.module_artifacts(c.ag, m) for m in sorted(witness_set)}
    witness.baseline = c.g.snapshot(c.ag, witness)
    require_snapshot_scope(witness.baseline, witness_set, 58)
    folders = {str(owner.folder) for owner in direct.historical_owners.values()}
    require(len(folders) == 5, 'original four suppliers and atlas witness evidence folders differ')
    return SimpleNamespace(direct=direct, witness=witness, evidence_folders=sorted(folders))


def retained_snapshot(c, retained):
    """Acceptance-backed snapshots, only after all original readers succeeded."""
    direct = c.g.snapshot(c.ag, retained.direct)
    witness = c.g.snapshot(c.ag, retained.witness)
    require_snapshot_scope(direct, retained.direct.active, 288)
    require_snapshot_scope(witness, retained.witness.active, 58)
    require(direct == retained.direct.baseline and witness == retained.witness.baseline,
            'original dictionary dependency or separate witness context changed')
    return {'dictionary_dependency_scope': direct, 'separate_original_witness_scope': witness,
            'original_supplier_acceptance_bindings': retained.direct.supplier_evidence,
            'separate_witness_acceptance_binding': retained.witness.supplier_evidence}


def snapshot(base, c, published, context, selected):
    """Observe every protected slot even if a new original-receipt read fails.

    These object fingerprints are preservation observations, not acceptance.
    Acceptance is established separately by prepare_dependency_scopes.
    """
    report = base.check(c)
    require_original_acceptance(report, published)
    observations = {}
    for label, active, count in (
            ('dictionary_288', set(selected['dependency_sources']), 288),
            ('separate_witness_58', set(selected['separate_original_evidence_scope']['sources']), 58)):
        value = {'selected_live_sources': {m: base.fp(PROJECT / c.ag.h.module_path(m)) for m in sorted(active)},
                 'preserved_dependency_artifacts': {m: c.g.module_artifacts(c.ag, m) for m in sorted(active)}}
        require_snapshot_scope(value, active, count)
        observations[label] = value
    slot = {'source': base.fp(PROJECT / SOURCE),
            'artifacts': c.g.module_artifacts(c.ag, TARGET), 'history': dictionary_history()}
    require_fresh_slot(**slot)
    groups = context.manifest['accepted_supplier_groups']
    folders = [Path(groups['initial4']['evidence_root']) / INITIAL4_COMMIT / m for m in INITIAL4]
    folders.append(Path(groups['atlas10']['evidence_root']) / ATLAS10_COMMIT / WITNESS)
    paths = [OLD_ROOT / AI, base.INSTALL_ROOT / AI, *folders]
    trees = {str(path): c.readers['ag'].tree_inventory(path) for path in paths}
    return {'original_acceptance_read': report, 'dictionary_slot': slot,
            'additional_preservation_observations_not_acceptance': observations,
            'original_AI_and_supplier_evidence_trees': trees,
            'git': c.ag.d.original_git_state(REPO)}


def require_probe_output(base, probe, outcome):
    require(base.fp(probe) == SOURCE_FP and all(not os.path.lexists(probe.with_suffix(ext)) for ext in SUFFIXES),
            'whole probe source changed or emitted an object')
    require(outcome['actual_built_modules'] == outcome['actual_failed_modules'] == [],
            'probe rebuilt or failed a project build')


def direct_import_readiness(c, run_dir):
    command = c.ag.h.serialize(0, run_dir / 'DIRECT_IMPORTS_LANE.json',
        c.ag.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in IMPORTS]))
    outcome = c.ag.ops.run(run_dir, 'serialized-dictionary-direct-import-readiness',
                          command, cwd=PROJECT, relay=False)
    require(outcome['exit_code'] == 0 and outcome['actual_built_modules'] == []
            and outcome['actual_failed_modules'] == [], 'DIRECT_IMPORTS_NOT_READY_NO_REBUILD_ALLOWED')
    return outcome


def run(publication, executed):
    base, c, source, published, selected, context = load_original(publication, executed)
    parent = PROBE_ROOT / publication / 'runs'
    require(parent.resolve() == parent, 'probe evidence parent traverses a symlink')
    require(not parent.exists() or (parent.is_dir() and not any(parent.iterdir())),
            'this publication already has probe history; inspect its original result instead of repeating it')
    run_dir = c.ag.d.attempt(parent)
    probe = run_dir / 'OriginalHistoricalCoefficientDictionaryProbe.lean'
    result = {'schema': 'p15_historical_coefficient_dictionary_whole_no_output_probe_v1',
              'publication': publication, 'source_origin': {'commit': AK, 'path': ORIGIN, **SOURCE_FP},
              'original_AI_acceptance_commit': AI, 'original_AG_acceptance_commit': AG,
              'source': {'path': str(probe), **SOURCE_FP}, 'scope': selected,
              'entrypoint': {'path': SCRIPT, **raw_fp(executed)},
              'normal_or_kernel_acceptance_claimed': False, 'new_owner_accepted': False,
              'whole_P1_5_complete': False, 'preservation_passed': False,
              'original_dependency_acceptance_preparation_completed': False,
              'Lean_typecheck_commands': 0, 'typecheck_command_completed': False, 'exit_code': 3}
    observation_before = before = retained = None
    try:
        observation_before = snapshot(base, c, published, context, selected)
        c.ag.d.save(run_dir / 'OBSERVATION_BEFORE.json', observation_before)
        c.ag.d.write_frozen(run_dir / 'executed-probe.py', executed)
        retained = prepare_dependency_scopes(c, context, selected)
        before = {'preservation': observation_before, 'original_acceptance': retained_snapshot(c, retained)}
        result['original_dependency_acceptance_preparation_completed'] = True
        c.ag.d.save(run_dir / 'CONTEXT_BEFORE.json', before)
        c.ag.d.save(run_dir / 'SELECTED_SCOPE.json', selected)
        c.ag.d.write_frozen(probe, source)
        require_probe_output(base, probe, {'actual_built_modules': [], 'actual_failed_modules': []})
        result['direct_import_readiness'] = direct_import_readiness(c, run_dir)
        command = c.ag.h.serialize(0, run_dir / 'PROBE_LANE.json',
            c.ag.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
        result['Lean_typecheck_commands'] = 1
        outcome = c.ag.ops.run(run_dir, 'serialized-whole-dictionary-probe', command, cwd=PROJECT, relay=False)
        result.update(typecheck_command_completed=True, command=outcome, exit_code=outcome['exit_code'])
        require_probe_output(base, probe, outcome)
        log = Path(outcome['log'])
        result.update(log={'path': str(log), **base.fp(log)}, compiler_output=log.read_text(),
                      whole_original_module_submitted=True, output_object_requested=False,
                      existing_project_modules_rebuilt=[], original_serializer_and_guard_used=True)
    except Exception as error:
        result['probe_error'] = str(error)
    finally:
        try:
            observation_after = snapshot(base, c, published, context, selected)
            c.ag.d.save(run_dir / 'OBSERVATION_AFTER.json', observation_after)
            after = {'preservation': observation_after, 'original_acceptance': (
                retained_snapshot(c, retained) if retained is not None else None)}
            c.ag.d.save(run_dir / 'CONTEXT_AFTER.json', after)
            require(observation_before is not None and observation_after == observation_before,
                    'prior source/object/evidence/runtime/Git or dictionary slot changed')
            if before is not None:
                require(after == before, 'original accepted dependency context changed')
            if os.path.lexists(probe):
                require_probe_output(base, probe, {'actual_built_modules': [], 'actual_failed_modules': []})
            else:
                require(result['Lean_typecheck_commands'] == 0, 'submitted whole probe source disappeared')
            result['preservation_passed'] = True
        except Exception as error:
            result['preservation_error'] = str(error)
    success = (result['exit_code'] == 0 and result['original_dependency_acceptance_preparation_completed']
               and result['typecheck_command_completed']
               and result['preservation_passed'] and not result.get('probe_error')
               and not result.get('preservation_error'))
    result['probe_passed'] = success
    path = run_dir / 'ACTUAL_DICTIONARY_PROBE_RESULT.json'
    c.ag.d.save(path, result)
    summary = {key: result[key] for key in ('publication', 'probe_passed', 'exit_code',
        'original_dependency_acceptance_preparation_completed',
        'typecheck_command_completed', 'Lean_typecheck_commands', 'preservation_passed',
        'new_owner_accepted', 'normal_or_kernel_acceptance_claimed', 'whole_P1_5_complete')}
    summary.update(result_path=str(path), result_fingerprint=base.fp(path),
        dictionary_project_dependencies=288, dictionary_artifact_slots=6048,
        separate_original_witness_sources=58, witness_sources_outside_dictionary=11)
    summary.update({key: result[key] for key in ('probe_error', 'preservation_error', 'log', 'compiler_output') if key in result})
    print(json.dumps(summary, sort_keys=True), flush=True)
    return 0 if success else max(1, int(result['exit_code']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', required=True)
    args = parser.parse_args()
    path = Path(__file__)
    require(path.is_file() and not path.is_symlink(), 'probe must be a regular file')
    return run(args.publication, path.read_bytes())


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'DICTIONARY_PROBE_HELD', 'error_type': type(error).__name__,
                          'error': str(error), 'new_owner_accepted': False,
                          'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
