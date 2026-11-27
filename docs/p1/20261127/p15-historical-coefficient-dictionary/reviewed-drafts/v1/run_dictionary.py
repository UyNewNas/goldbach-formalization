#!/usr/bin/env python3
"""Independent dictionary acceptance. INPUTS=None forbids external operations."""
from pathlib import Path
from types import ModuleType, SimpleNamespace
import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
sys.dont_write_bytecode = True

REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
INSTALL_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-dictionary-source-install-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-historical-coefficient-dictionary-probe-v1')
PACKAGE = 'docs/p1/20261127/p15-historical-coefficient-dictionary/'
SCRIPT = PACKAGE + 'run_dictionary.py'
INSTALLER = PACKAGE + 'install_dictionary_source.py'
PROBE_SCRIPT = PACKAGE + 'probe_dictionary.py'
PROBE = PACKAGE + 'probe/ACTUAL_DICTIONARY_PROBE_RESULT.json'
AI = '6d9072f7b33332eaf5ecfff22876e0404cd6ab51'
AJ = '6d87764cbc9fce5b10a2665a458619e44d8255ae'
AK = 'd4f88a20262af7d54ed0e6e58dfc533496c595e3'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
AM = '45e8de70fb3045b04f3ef3ad2ff364c7ee2f390c'
PROBE_SCRIPT_FP = {'bytes':26465, 'sha256':'93f5e3e93eaf6948ae63a072b65cae98bf90cd76bfe235b536499eaf3cecb106'}
READER = 'docs/p1/20261126/p15-trimlog-accuracy/run_trimlog.py'
READER_FP = {'bytes':36541, 'sha256':'0c6307af83c197123bd2da678bfd4ac6b76916169d6d457f83733461725b8272'}
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/TRIMLOG_AI_PUBLIC_ACCEPTANCE.json'
PUBLIC_FP = {'bytes':18539, 'sha256':'2bb01aa28ab117933b0ec8f766245f0a9faaeb750448bb6e47536c4dbfdf18f0'}
TARGET = 'ImbalancedChen.P1OriginalHistoricalCoefficientDictionary'
SOURCE = 'ImbalancedChen/P1OriginalHistoricalCoefficientDictionary.lean'
ORIGIN = 'docs/source-only/20261127/p1-historical-coefficient-dictionary/P1OriginalHistoricalCoefficientDictionary.lean'
SOURCE_FP = {'bytes':9079, 'sha256':'b90556b05b152cea39fd72eb55428986105ad86a4926e2badf50175927c47409'}
PROJECT_IMPORTS = ['ImbalancedChen.P1Full87TrueDUnitBound', 'ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData']
IMPORTS = PROJECT_IMPORTS + ['Mathlib.Data.Complex.Basic']
TRIMLOG = 'ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy'
GEOMETRY = 'ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry'
GEOMETRY_SOURCE = 'ImbalancedChen/P1OriginalSingletonRemainingTypeIGeometry.lean'
GEOMETRY_PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-remaining-typei-geometry-probe-v1')
INPUTS = None


def require(ok, message):
    if not ok:
        raise RuntimeError(message)



def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}



def value_fp(value):
    return raw_fp((json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode())



def fp(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    require(path.is_file() and not path.is_symlink(), 'nonregular file: ' + str(path))
    with path.open('rb') as stream:
        return {'bytes': os.fstat(stream.fileno()).st_size,
                'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}



def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def valid_pin(row):
    return (isinstance(row, dict) and set(row) == {'bytes', 'sha256'} and
            type(row['bytes']) is int and row['bytes'] >= 0 and isinstance(row['sha256'], str) and
            re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None)


def validate_inputs(inputs):
    require(isinstance(inputs, dict) and inputs.get('canonical_source') == SOURCE_FP and
            inputs.get('probe_publication') == AM and valid_pin(inputs.get('probe_document')) and
            inputs['probe_document']['bytes'] > 0 and
            isinstance(inputs.get('probe_job'), str) and re.fullmatch('job_[0-9a-f]{32}', inputs['probe_job']),
            'actual successful dictionary probe INPUTS are unbound')
    geometry = inputs.get('geometry')
    require(isinstance(geometry, dict) and geometry.get('mode') in ('unaccepted', 'accepted'),
            'prior Geometry state must be explicitly bound')
    if geometry['mode'] == 'accepted':
        require(isinstance(geometry.get('source_commit'), str) and
                re.fullmatch('[0-9a-f]{40}', geometry['source_commit']) and
                geometry.get('reader_path') == 'docs/p1/20261127/p15-remaining-typei-geometry/run_geometry.py' and
                valid_pin(geometry.get('reader')) and valid_pin(geometry.get('readonly_report')),
                'actual accepted Geometry reader/report identity is unbound')
    else:
        require('source' in geometry and (geometry['source'] is None or valid_pin(geometry['source'])),
                'unaccepted Geometry source observation must be explicit')


def load(commit, executed):
    validate_inputs(INPUTS)
    require(__debug__ and isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit) and commit != AM,
            'a separate exact formal publication is required')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
            subprocess.run(['git', 'merge-base', '--is-ancestor', AM, commit], cwd=REPO).returncode == 0,
            'formal publication must descend from the actual probe publication')
    require(executed == git_file(commit, SCRIPT), 'executed dictionary adapter differs from publication')
    raw = git_file(AM, PROBE_SCRIPT)
    require(raw_fp(raw) == PROBE_SCRIPT_FP and git_file(commit, PROBE_SCRIPT) == raw,
            'immutable original dictionary probe/reader differs')
    probe_api = ModuleType('immutable_AM_dictionary_probe_readers'); probe_api.__file__ = PROBE_SCRIPT
    exec(compile(raw, PROBE_SCRIPT, 'exec'), probe_api.__dict__)
    base, ai, source, published, selected, context = probe_api.load_original(AM, raw)
    require(base.ROOT == ROOT == ai.g.ROOT and base.REPO == REPO and base.PROJECT == PROJECT and
            raw_fp(source) == SOURCE_FP and git_file(commit, SOURCE) == source and
            git_file(commit, ORIGIN) == source == git_file(AK, ORIGIN) and ai.ag.h.imports(source) == IMPORTS,
            'fixed roots or complete canonical/origin source/import identity differs')
    require(git_file(commit, base.DRIVER) == git_file(AG, base.DRIVER) and
            git_file(commit, base.MANIFEST) == git_file(AG, base.MANIFEST) and
            git_file(commit, READER) == git_file(AI, READER), 'old accepted entrypoint or registry changed')
    probe_raw = git_file(commit, PROBE)
    require(raw_fp(probe_raw) == INPUTS['probe_document'], 'published actual dictionary probe document differs')
    c = SimpleNamespace(commit=commit, script=executed, source=source, base=base, ai=ai,
        g=ai.g, ag=ai.ag, published=published, selected=selected, scope_context=context,
        probe_api=probe_api, probe=json.loads(probe_raw), geometry_reader=None)
    require(TARGET not in c.g.TARGETS and GEOMETRY not in selected['dependency_sources'] and
            len(c.g.TARGETS) == 21, 'new owner registry or independent dependency graph differs')
    if INPUTS['geometry']['mode'] == 'accepted':
        binding = INPUTS['geometry']; geo_commit = binding['source_commit']
        require(geo_commit != commit, 'dictionary and Geometry cannot share an accepting publication/runs')
        geo_raw = git_file(geo_commit, binding['reader_path'])
        require(raw_fp(geo_raw) == binding['reader'] and git_file(commit, binding['reader_path']) == geo_raw,
                'frozen accepted Geometry reader differs')
        reader = ModuleType('immutable_prior_accepted_geometry'); reader.__file__ = binding['reader_path']
        exec(compile(geo_raw, reader.__file__, 'exec'), reader.__dict__)
        require(reader.TARGET == GEOMETRY and reader.SOURCE == GEOMETRY_SOURCE and reader.ROOT == ROOT and
                reader.PROJECT == PROJECT and reader.REPO == REPO, 'prior Geometry reader owner/root differs')
        c.geometry_reader = (reader, reader.load(geo_commit, geo_raw))
    c.identity = {'source_commit': commit, 'adapter': {'path': SCRIPT, **raw_fp(executed)},
        'new_owner': TARGET, 'canonical_source': {'path': SOURCE, **SOURCE_FP},
        'source_origin': {'commit': AK, 'path': ORIGIN, **SOURCE_FP},
        'immutable_AM_probe_reader': {'commit': AM, 'path': PROBE_SCRIPT, **PROBE_SCRIPT_FP},
        'original_AG_acceptance_commit': AG, 'original_AI_acceptance_commit': AI,
        'probe_job': INPUTS['probe_job'], 'probe_publication': AM,
        'probe_document': {'path': PROBE, **INPUTS['probe_document']},
        'prior_Geometry_state': INPUTS['geometry'], 'Geometry_is_not_a_dictionary_dependency': True,
        'independent_from_original_21_target_registry': True}
    return c


def read_probe(c, retained):
    p = c.probe
    require(p['schema'] == 'p15_historical_coefficient_dictionary_whole_no_output_probe_v1' and
            p['publication'] == AM and p['source_origin'] == {'commit': AK, 'path': ORIGIN, **SOURCE_FP} and
            p['entrypoint'] == {'path': PROBE_SCRIPT, **PROBE_SCRIPT_FP} and
            p['original_AI_acceptance_commit'] == AI and p['original_AG_acceptance_commit'] == AG and
            p['scope'] == c.selected and p['probe_passed'] is True and p['exit_code'] == 0 and
            p['preservation_passed'] is True and p['typecheck_command_completed'] is True and
            p['original_dependency_acceptance_preparation_completed'] is True and p['Lean_typecheck_commands'] == 1 and
            p['whole_original_module_submitted'] is True and p['output_object_requested'] is False and
            p['existing_project_modules_rebuilt'] == [] and p['original_serializer_and_guard_used'] is True and
            p['normal_or_kernel_acceptance_claimed'] is False and p['new_owner_accepted'] is False and
            p['whole_P1_5_complete'] is False and not any(p.get(k) for k in ('probe_error', 'preservation_error')),
            'actual whole-source probe is not successful with full original dependency preservation')
    source = Path(p['source']['path']); run = source.parent
    require(source.is_absolute() and source.resolve() == source and
            source.name == 'OriginalHistoricalCoefficientDictionaryProbe.lean' and
            run.parent == PROBE_ROOT / AM / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
            fp(source) == SOURCE_FP and source.read_bytes() == c.source and
            fp(run / 'ACTUAL_DICTIONARY_PROBE_RESULT.json') == INPUTS['probe_document'] and
            (run / 'executed-probe.py').read_bytes() == git_file(AM, PROBE_SCRIPT),
            'original whole-source probe source/result/entrypoint identity differs')
    whole = c.base.read_command(c.ai, run, 'serialized-whole-dictionary-probe',
        c.ag.h.serialize(0, run / 'PROBE_LANE.json',
            c.ag.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(source)])))
    direct = c.base.read_command(c.ai, run, 'serialized-dictionary-direct-import-readiness',
        c.ag.h.serialize(0, run / 'DIRECT_IMPORTS_LANE.json',
            c.ag.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in IMPORTS])))
    require(whole == p['command'] and direct == p['direct_import_readiness'] and
            whole['actual_built_modules'] == whole['actual_failed_modules'] ==
            direct['actual_built_modules'] == direct['actual_failed_modules'] == [] and
            fp(Path(whole['log'])) == {k: p['log'][k] for k in ('bytes', 'sha256')} and
            Path(whole['log']).read_text() == p['compiler_output'], 'actual probe command/log differs')
    before = c.ag.api.read_json(run / 'CONTEXT_BEFORE.json')
    require(before == c.ag.api.read_json(run / 'CONTEXT_AFTER.json') and
            before['preservation'] == c.ag.api.read_json(run / 'OBSERVATION_BEFORE.json') ==
                c.ag.api.read_json(run / 'OBSERVATION_AFTER.json') and
            c.ag.api.read_json(run / 'SELECTED_SCOPE.json') == c.selected and
            before['original_acceptance'] == c.probe_api.retained_snapshot(c.ai, retained),
            'actual probe D288/W58 original acceptance or before/after context differs')
    c.probe_api.require_original_acceptance(before['preservation']['original_acceptance_read'], c.published)
    c.probe_api.require_fresh_slot(**before['preservation']['dictionary_slot'])
    c.probe_api.require_probe_output(c.base, source, whole)
    return {'path': str(run), 'tree': c.ai.readers['ag'].tree_inventory(run)}


def geometry_snapshot(c):
    binding = INPUTS['geometry']
    artifacts = c.g.module_artifacts(c.ag, GEOMETRY)
    require(len(artifacts) == 21 and set(artifacts) == set(c.g.artifact_paths(GEOMETRY)),
            'Geometry preservation needs all 21 owner artifact slots')
    source = fp(PROJECT / GEOMETRY_SOURCE)
    history = []
    for folder in sorted(ROOT.iterdir()):
        if re.fullmatch('[0-9a-f]{40}', folder.name) and os.path.lexists(folder / GEOMETRY):
            owner = folder / GEOMETRY
            require(owner.is_dir() and owner.resolve() == owner, 'nonregular Geometry owner history')
            history.append(str(owner))
    trees = {}
    if os.path.lexists(GEOMETRY_PROBE_ROOT):
        trees[str(GEOMETRY_PROBE_ROOT)] = c.ai.readers['ag'].tree_inventory(GEOMETRY_PROBE_ROOT)
    report = None
    if binding['mode'] == 'unaccepted':
        require(c.geometry_reader is None and source == binding['source'] and not history and
                all(value is None for value in artifacts.values()),
                'Geometry gained accepted or partial owner state; bind its actual accepted reader before proceeding')
    else:
        reader, geo = c.geometry_reader
        report = reader.check(geo)
        require(report['status'] == 'ORIGINAL_GEOMETRY_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION' and
                report['new_owner_accepted'] is True and report['normal_or_kernel_commands_executed'] == 0 and
                report['identity']['source_commit'] == binding['source_commit'] and
                report['identity']['new_owner'] == GEOMETRY and
                value_fp(report) == binding['readonly_report'] and source == reader.SOURCE_FP and
                artifacts == report['owner']['binding']['all_observed_target_artifacts'] and
                report['owner']['only_standard_axioms'] is True and
                report['owner']['full_owned_including_private_generated'] is True and
                report['accepting_run']['new_owner_accepted'] is True and
                report['accepting_run']['recompiled_by_check'] is False and
                history == [str(ROOT / binding['source_commit'] / GEOMETRY)],
                'prior Geometry complete read-only acceptance identity differs')
        for path in (ROOT / binding['source_commit'], reader.INSTALL_ROOT / binding['source_commit']):
            trees[str(path)] = c.ai.readers['ag'].tree_inventory(path)
    return {'mode': binding['mode'], 'source': source, 'artifacts': artifacts, 'history': history,
            'complete_original_readonly_acceptance': report, 'evidence_trees': trees,
            'is_dictionary_dependency': False}


def prepare(c):
    validate_inputs(INPUTS)
    old = c.base.prepare_base(c.ai)
    for module, row in old.ag.manifest['project_sources'].items():
        require(raw_fp(git_file(c.commit, row['path'])) == {k: row[k] for k in ('bytes', 'sha256')},
                'new publication changed accepted source: ' + module)
    retained = c.probe_api.prepare_dependency_scopes(c.ai, c.scope_context, c.selected)
    state = SimpleNamespace(old=old, ai=ai_snapshot(c, old), retained=retained,
        dependency_context=c.probe_api.retained_snapshot(c.ai, retained), probe=read_probe(c, retained),
        supplier_trees={path: c.ai.readers['ag'].tree_inventory(Path(path)) for path in retained.evidence_folders},
        geometry=geometry_snapshot(c))
    unchanged(c, state)
    return state


def unchanged(c, state):
    validate_inputs(INPUTS)
    c.base.unchanged_old(c.ai, state.old)
    require(ai_snapshot(c, state.old) == state.ai and
            c.probe_api.retained_snapshot(c.ai, state.retained) == state.dependency_context and
            c.ai.readers['ag'].tree_inventory(Path(state.probe['path'])) == state.probe['tree'] and
            {path: c.ai.readers['ag'].tree_inventory(Path(path)) for path in state.retained.evidence_folders} ==
                state.supplier_trees and geometry_snapshot(c) == state.geometry,
            'original AI, D288/W58, supplier/probe evidence, or independent Geometry state changed')


def preservation_summary(c, state):
    return {'original_AG_AE_context': c.base.preservation_summary(state.old),
        'original_AI_acceptance': state.ai['acceptance']['owner'],
        'original_AI_source_and_21_artifacts': value_fp({'source': state.ai['source'], 'artifacts': state.ai['artifacts']}),
        'original_AI_evidence_installation_trees': value_fp(state.ai['trees']),
        'dictionary_dependency_count': 288, 'dictionary_artifact_slots': 6048,
        'separate_witness_count': 58, 'witness_outside_dictionary': 11,
        'original_D288_W58_acceptance_context': value_fp(state.dependency_context),
        'original_supplier_evidence_trees': value_fp(state.supplier_trees),
        'actual_whole_probe_evidence': {'path': state.probe['path'], **value_fp(state.probe['tree'])},
        'independent_prior_Geometry': value_fp(state.geometry),
        'Geometry_is_not_a_dictionary_dependency': True}


def require_new_slot(source, artifacts, history, *, installed):
    require(not history and len(artifacts) == 21 and all(value is None for value in artifacts.values()),
            'dictionary has started owner history or artifacts; inspect without recompilation')
    require(source == SOURCE_FP if installed else source in (None, SOURCE_FP),
            'only the exact frozen dictionary source can be installed')


def installation_action(before):
    require(before in (None, SOURCE_FP), 'foreign canonical source cannot be installed or replaced')
    return 'EXCLUSIVE_NEW_CANONICAL_SOURCE' if before is None else 'IDENTICAL_SOURCE_BEFORE_OWNER_START'


def dependency_inventory(c, state):
    dependencies = set(c.selected['dependency_sources'])
    source = state.retained.direct.baseline['preserved_dependency_artifacts']
    require(len(dependencies) == 288 and set(source) == dependencies and GEOMETRY not in dependencies and
            all(len(row) == 21 and set(row) == set(c.g.artifact_paths(module)) for module, row in source.items()) and
            sum(map(len, source.values())) == 6048,
            'complete original D288 dependency inventory required; AG144 or two-slot pins cannot substitute')
    return copy.deepcopy(source)


def new_spec(c, state):
    require(fp(PROJECT / SOURCE) == SOURCE_FP and (PROJECT / SOURCE).resolve() == PROJECT / SOURCE,
            'exact dictionary source must first be separately installed')
    graph = {**c.scope_context.graph, TARGET: list(PROJECT_IMPORTS)}
    sources = {**c.scope_context.sources, TARGET: SOURCE_FP['sha256']}
    active = c.ag.h.closure(graph, [TARGET]); dependencies = set(c.selected['dependency_sources'])
    require(len(graph) == len(sources) == 361 and active == dependencies | {TARGET} and len(active) == 289 and
            GEOMETRY not in active, 'separate dictionary 361-known/289-active graph differs')
    observed_graph, observed = c.ag.h.project_graph(PROJECT, [TARGET])
    require(observed_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in observed.items()} == {m: sources[m] for m in active},
            'installed dictionary graph differs')
    installation, install_pins = read_installation(c, state)
    pins = dependency_inventory(c, state)
    retained_pins = {**state.old.retained, **state.retained.direct.retained_inputs,
                     **state.retained.witness.retained_inputs, **install_pins}
    spec = SimpleNamespace(graph=graph, sources=sources, active=active, selected={TARGET}, order=[TARGET],
        dependency_pins=pins, review=c.scope_context.review, retained_inputs=retained_pins,
        manifest={'project_sources': {TARGET: {'all_imports': list(IMPORTS)}}},
        input_bindings={'source_commit': c.commit, 'selected_targets': [TARGET], 'independent_owner': c.identity,
            'independent_source_installation': installation, 'original_AG_context': value_fp(state.old.ag.baseline),
            'original_D288_context': value_fp(state.retained.direct.baseline),
            'separate_original_W58_context': value_fp(state.retained.witness.baseline),
            'preservation': preservation_summary(c, state)})
    spec.baseline = c.g.snapshot(c.ag, spec)
    return spec



def require_ai_acceptance(report, published):
    require(report['status'] == 'ORIGINAL_TRIMLOG_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION' and
            report['new_owner_accepted'] is True and report['normal_or_kernel_commands_executed'] == 0 and
            report['identity']['source_commit'] == published['source_commit'] == AI and
            published['status'] == 'NORMAL_KERNEL_ALL_OWNED_ACCEPTED_AND_READ_BACK',
            'original AI acceptance is not a complete read-only acceptance')
    owner = report['owner']
    require(owner['binding'] == published['owner_binding'] and
            owner['audit_id'] == published['audit_id'] == '3d934c02c7fcb8f3a335' and
            owner['owned_count'] == published['owned_count'] == 4 and
            owner['public_count'] == published['public_count'] == 4 and
            owner['full_owned_including_private_generated'] is True and owner['only_standard_axioms'] is True and
            published['normal_exit_code'] == published['final_stock_exit_code'] == 0 and
            set(published['kernel_exit_codes'].values()) == {0} and
            report['accepting_run']['path'] == published['original_accepting_run']['path'] and
            report['accepting_run']['new_owner_accepted'] is True and
            report['accepting_run']['recompiled_by_check'] is False,
            'original AI public/normal/full-owned/kernel/run binding differs')



def ai_snapshot(c, old):
    base, ai = c.base, c.ai
    spec = base.new_spec(ai, old)
    existing = base.new_owner_state(ai, spec)
    require(existing['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT', 'original AI owner is no longer accepted')
    owner = base.accepted_public(ai, spec)
    report = {'status': 'ORIGINAL_TRIMLOG_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION',
        'identity': ai.identity, 'new_owner_accepted': True, 'normal_or_kernel_commands_executed': 0,
        'owner': owner, 'accepting_run': base.read_completed_run(ai, old, spec, owner),
        'independent_source_installation': spec.input_bindings['independent_source_installation']}
    require_ai_acceptance(report, c.published)
    require(c.g.snapshot(c.ag, spec) == spec.baseline, 'original AI read changed its dependency context')
    artifacts = c.g.module_artifacts(c.ag, TRIMLOG)
    require(fp(PROJECT / base.SOURCE) == base.SOURCE_FP and len(artifacts) == 21 and
            set(artifacts) == set(c.g.artifact_paths(TRIMLOG)) and
            artifacts == owner['binding']['all_observed_target_artifacts'],
            'original AI canonical source or full 21-artifact binding differs')
    trees = {str(path): ai.readers['ag'].tree_inventory(path)
             for path in (ROOT / AI, base.INSTALL_ROOT / AI)}
    return {'acceptance': report, 'source': fp(PROJECT / base.SOURCE), 'artifacts': artifacts, 'trees': trees}



def owner_history():
    require(ROOT.is_dir() and ROOT.resolve() == ROOT, 'original owner root differs')
    history = []
    for folder in sorted(ROOT.iterdir()):
        if re.fullmatch('[0-9a-f]{40}', folder.name) and os.path.lexists(folder / TARGET):
            owner = folder / TARGET
            require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder and
                    owner.is_dir() and not owner.is_symlink() and owner.resolve() == owner,
                    'nonregular Dictionary owner history')
            history.append(owner)
    return history



def require_new_attempt(runs):
    require(runs.resolve() == runs and (not os.path.lexists(runs) or
            (runs.is_dir() and not runs.is_symlink() and not any(runs.iterdir()))),
            'existing attempt history must be inspected; successful results use --check, partial/HOLD never auto-retry')



def unique_run(runs):
    require(runs.is_dir() and runs.resolve() == runs, 'complete original run history is missing')
    entries = list(runs.iterdir())
    require(len(entries) == 1, 'nonunique/partial original run history requires inspection')
    run = entries[0]
    require(run.is_dir() and not run.is_symlink() and run.resolve() == run and
            re.fullmatch('attempt-[0-9]{5}', run.name), 'nonregular original run history')
    return run



def require_terminal(result, worker, identity, *, installation):
    flag = 'source_install_complete' if installation else 'new_owner_accepted'
    require(result == {**worker, 'worker_exit_code': 0, flag: True} and
            worker['identity'] == identity and worker['whole_P1_5_complete'] is False and
            worker['new_owner_accepted'] is False and
            not any(worker.get(k) for k in ('installation_error', 'preparation_error', 'failures',
                                           'preservation_error', 'dispatch_error', 'git_error')),
            'original result/worker identity, terminal success, or failure binding differs')
    if installation:
        require(worker['schema'] == 'p15_independent_dictionary_source_install_v1' and
                worker['normal_or_kernel_commands_executed'] == 0 and worker['source_installed'] is True and
                worker['source_after'] == SOURCE_FP and worker['source_before'] in (None, SOURCE_FP) and
                worker['installation_action'] == installation_action(worker['source_before']),
                'same-commit source installation terminal binding differs')
    else:
        require(worker['schema'] == 'p15_independent_dictionary_acceptance_v1' and
                worker['targets'] == worker['accepted_owners'] == [TARGET] and worker['failures'] == {},
                'same-commit Dictionary normal/full-owned/kernel terminal binding differs')



def read_installation(c, state):
    run = unique_run(INSTALL_ROOT / c.commit / 'runs')
    result = c.ag.api.read_json(run / 'SOURCE_INSTALL_RESULT.json')
    worker = c.ag.api.read_json(run / 'WORKER_RESULT.json')
    require_terminal(result, worker, c.identity, installation=True)
    raw = git_file(c.commit, INSTALLER); executed = run / 'executed-installer.py'
    require(fp(executed) == raw_fp(raw) and executed.read_bytes() == raw and
            worker['installer'] == {'path': INSTALLER, **raw_fp(raw)} and
            worker['preservation'] == preservation_summary(c, state) and
            c.ag.api.read_json(run / 'OLD_CONTEXT_BEFORE.json') ==
            c.ag.api.read_json(run / 'OLD_CONTEXT_AFTER.json') == preservation_summary(c, state) and
            c.ag.api.read_json(run / 'GIT_BEFORE.json') == c.ag.api.read_json(run / 'GIT_AFTER.json') == state.old.git,
            'same-commit installer/script/original AI and AG context/Git chain differs')
    command = c.base.read_command(c.ai, run, 'serialized-dictionary-install',
        c.ag.h.serialize(0, run / 'DICTIONARY_INSTALL_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--install', '--inside-lane', str(run)]))
    require(command['actual_built_modules'] == command['actual_failed_modules'] == [],
            'source installation attempted a build')
    names = ['SOURCE_INSTALL_RESULT.json', 'WORKER_RESULT.json', 'OLD_CONTEXT_BEFORE.json',
        'OLD_CONTEXT_AFTER.json', 'GIT_BEFORE.json', 'GIT_AFTER.json', 'executed-installer.py',
        'serialized-dictionary-install-command.json', 'serialized-dictionary-install.log']
    pins = {str(run / name): fp(run / name) for name in names}
    require(all(row is not None for row in pins.values()), 'incomplete separate source installation receipts')
    backup = run / 'canonical-source-before.lean'
    if worker['source_before'] is None:
        require(worker['source_backup'] is None and not os.path.lexists(backup), 'unexpected pre-install source backup')
    else:
        require(fp(backup) == worker['source_before'] and
                worker['source_backup'] == {'path': str(backup), **worker['source_before']},
                'exact pre-install canonical source was not preserved')
        pins[str(backup)] = fp(backup)
    return {'run': str(run), 'source_install_receipts': pins}, pins



def new_owner_state(c, spec):
    history = owner_history(); folder = ROOT / c.commit / TARGET
    require(all(path == folder for path in history), 'foreign Dictionary owner history requires inspection')
    if not os.path.lexists(folder):
        require_new_slot(fp(PROJECT / SOURCE), c.g.module_artifacts(c.ag, TARGET), history, installed=True)
        existing = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
        require(existing['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT', 'fresh Dictionary owner classification differs')
        return existing
    require(fp(folder / 'normal' / TARGET / 'NORMAL_PASS.json') is not None,
            'partial Dictionary owner without normal receipt requires inspection')
    existing = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
    c.g.require_completed_existing_owner(c.ag, c.commit, spec, TARGET, existing)
    return existing



def accepted_public(c, spec):
    existing = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
    c.g.require_completed_existing_owner(c.ag, c.commit, spec, TARGET, existing)
    binding = c.g.acceptance_binding(c.ag, c.commit, TARGET)
    require(len(binding['audits']) == 1 and len(binding['source_plus_five_outputs']) == 6 and
            len(binding['all_observed_target_artifacts']) == 21, 'Dictionary single-owner receipt shape differs')
    audit = c.ag.api.read_json(Path(binding['audits'][0]['result']['path']))
    require(audit['only_standard_axioms'] is True and audit['full_owned_including_private_generated'] is True and
            type(audit['total_owned_exports']) is int and type(audit['total_public_exports']) is int and
            0 < audit['total_public_exports'] <= audit['total_owned_exports'],
            'Dictionary must have actual complete full-owned/kernel/standard-axiom acceptance')
    return {'module': TARGET, 'source_commit': c.commit, 'binding': binding,
        'audit_id': Path(binding['audits'][0]['plan']['path']).parent.name,
        'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports'],
        'only_standard_axioms': audit['only_standard_axioms'],
        'full_owned_including_private_generated': audit['full_owned_including_private_generated'],
        'original_21_target_count': 21, 'original_21_accepted_count': 18,
        'new_owner_is_outside_original_21': True, 'whole_P1_5_complete': False}



def read_completed_run(c, state, spec, owner):
    run = unique_run(ROOT / c.commit / 'runs')
    result = c.ag.api.read_json(run / 'RESULT.json')
    worker = c.ag.api.read_json(run / 'WORKER_RESULT.json')
    require_terminal(result, worker, c.identity, installation=False)
    executed = run / 'executed-dictionary.py'
    require(worker['owner'] == owner and worker['preservation'] == preservation_summary(c, state) and
            fp(executed) == raw_fp(c.script) and executed.read_bytes() == c.script and
            c.ag.api.read_json(run / 'CONTEXT_BEFORE.json') ==
            c.ag.api.read_json(run / 'CONTEXT_AFTER.json') == spec.baseline and
            c.ag.api.read_json(run / 'GIT_BEFORE.json') == c.ag.api.read_json(run / 'GIT_AFTER.json') == state.old.git,
            'same-commit original Dictionary owner/script/context/Git chain differs')
    wrapper = c.base.read_command(c.ai, run, 'serialized-dictionary',
        c.ag.h.serialize(0, run / 'DICTIONARY_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--run', '--inside-lane', str(run)]))
    direct = c.base.read_command(c.ai, run / TARGET, 'direct-import-stock-readiness',
        c.ag.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in IMPORTS]))
    stock = c.base.read_command(c.ai, run, 'final-stock-readiness',
        c.ag.h.guard(0, ['lake', '--no-build', 'build', '+' + TARGET + ':olean']))
    require(set(wrapper['actual_built_modules']) <= {TARGET} and wrapper['actual_failed_modules'] == [] and
            stock == worker['final_stock_readiness'] and direct == worker['direct_import_readiness'] and
            stock['actual_built_modules'] == stock['actual_failed_modules'] ==
            direct['actual_built_modules'] == direct['actual_failed_modules'] == [],
            'original serialized acceptance/direct-import/final-stock no-build receipts differ')
    names = ['RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
        'GIT_BEFORE.json', 'GIT_AFTER.json', 'executed-dictionary.py',
        'serialized-dictionary-command.json', 'serialized-dictionary.log',
        'final-stock-readiness-command.json', 'final-stock-readiness.log',
        TARGET + '/direct-import-stock-readiness-command.json', TARGET + '/direct-import-stock-readiness.log']
    pins = {name: {'path': str(run / name), **fp(run / name)} for name in names}
    return {'path': str(run), 'original_run_receipts': pins, 'final_stock_readiness': stock,
        'new_owner_accepted': True, 'recompiled_by_check': False}



def check(c):
    state = prepare(c); spec = new_spec(c, state)
    existing = new_owner_state(c, spec)
    result = {'schema': 'p15_independent_dictionary_readonly_v1', 'identity': c.identity,
        'known_source_count': 361, 'active_source_count': 289, 'preserved_dependency_count': 288,
        'new_owner_accepted': False, 'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}
    if existing['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT':
        owner = accepted_public(c, spec)
        result.update(status='ORIGINAL_DICTIONARY_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION', owner=owner,
            accepting_run=read_completed_run(c, state, spec, owner), new_owner_accepted=True)
    else:
        require_new_attempt(ROOT / c.commit / 'runs')
        result.update(status='FRESH_INSTALLED_DICTIONARY_NOT_YET_ACCEPTED', owner=None)
    require(c.g.snapshot(c.ag, spec) == spec.baseline, 'Dictionary dependency context changed during read')
    unchanged(c, state)
    result['preservation'] = preservation_summary(c, state)
    result['independent_source_installation'] = spec.input_bindings['independent_source_installation']
    return result



def worker(c, run):
    validate_inputs(INPUTS)
    result = {'schema': 'p15_independent_dictionary_acceptance_v1', 'identity': c.identity,
        'targets': [TARGET], 'accepted_owners': [], 'failures': {}, 'new_owner_accepted': False,
        'new_owner_is_outside_original_21': True, 'original_21_target_count': 21,
        'original_21_accepted_count': 18, 'whole_P1_5_complete': False}
    state = spec = None
    try:
        c.ag.d.verify_lane(c.ag.h)
        state = prepare(c); spec = new_spec(c, state)
        existing = new_owner_state(c, spec)
        require(existing['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT',
                'already accepted Dictionary owner: use --check, never recompile')
        c.ag.d.save(run / 'CONTEXT_BEFORE.json', spec.baseline)
        result['direct_import_readiness'] = c.g.direct_import_readiness(c.ag, spec, TARGET, run)
        require(c.g.snapshot(c.ag, spec) == spec.baseline, 'no-build import readiness changed dependencies')
        unchanged(c, state)
        c.g.run_owner(c.ag, c.commit, ROOT / c.commit, run, TARGET, spec.graph, spec.sources)
        owner = accepted_public(c, spec)
        require(c.g.snapshot(c.ag, spec) == spec.baseline, 'Dictionary owner changed its dependency context')
        unchanged(c, state)
        artifacts = c.g.module_artifacts(c.ag, TARGET)
        stock = c.ag.ops.run(run, 'final-stock-readiness',
            c.ag.h.guard(0, ['lake', '--no-build', 'build', '+' + TARGET + ':olean']), cwd=PROJECT)
        require(stock['exit_code'] == 0 and stock['actual_built_modules'] == stock['actual_failed_modules'] == [] and
                c.g.module_artifacts(c.ag, TARGET) == artifacts, 'Dictionary final no-build stock changed artifacts')
        result.update(accepted_owners=[TARGET], owner=owner, final_stock_readiness=stock)
    except Exception as error:
        result['failures'][TARGET] = str(error)
    finally:
        try:
            if spec is not None:
                after = c.g.snapshot(c.ag, spec); c.ag.d.save(run / 'CONTEXT_AFTER.json', after)
                require(after == spec.baseline, 'Dictionary dependencies/runtime changed')
            if state is not None:
                unchanged(c, state)
                result['preservation'] = preservation_summary(c, state)
        except Exception as error:
            result['preservation_error'] = str(error)
    c.ag.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('preservation_error')))



def dispatch(c, *, installation=False):
    """One serialized worker; preserve preparation failures after attempt allocation."""
    validate_inputs(INPUTS)
    runs = (INSTALL_ROOT if installation else ROOT) / c.commit / 'runs'
    require_new_attempt(runs)
    run = c.ag.d.attempt(runs)
    name = 'serialized-dictionary-install' if installation else 'serialized-dictionary'
    lane = 'DICTIONARY_INSTALL_LANE.json' if installation else 'DICTIONARY_LANE.json'
    executed = run / ('executed-installer.py' if installation else 'executed-dictionary.py')
    result_name = 'SOURCE_INSTALL_RESULT.json' if installation else 'RESULT.json'
    result = {'schema': 'p15_independent_dictionary_source_install_v1' if installation
                      else 'p15_independent_dictionary_acceptance_v1',
        'identity': c.identity, 'worker_exit_code': 3, 'new_owner_accepted': False, 'whole_P1_5_complete': False}
    if installation:
        result.update(source_installed=False, source_install_complete=False)
    else:
        result.update(targets=[TARGET], accepted_owners=[], failures={})
    git = None
    try:
        git = c.ag.d.original_git_state(REPO); c.ag.d.save(run / 'GIT_BEFORE.json', git)
        c.ag.d.write_frozen(executed, c.installer if installation else c.script)
        command = c.ag.ops.run(run, name, c.ag.h.serialize(0, run / lane,
            ['python3', '-B', str(executed), '--source-commit', c.commit,
             '--install' if installation else '--run', '--inside-lane', str(run)]), relay=True)
        result['worker_exit_code'] = command['exit_code']
        require(set(command['actual_built_modules']) <= (set() if installation else {TARGET}) and
                command['actual_failed_modules'] == [], 'serialized worker built/failed an old project module')
        require(fp(run / 'WORKER_RESULT.json') is not None, 'worker stopped before its result')
        result.update(c.ag.api.read_json(run / 'WORKER_RESULT.json'))
    except Exception as error:
        result['dispatch_error'] = str(error)
    finally:
        try:
            after = c.ag.d.original_git_state(REPO); c.ag.d.save(run / 'GIT_AFTER.json', after)
            require(git is not None and after == git, 'original dirty Git state changed or was unavailable')
        except Exception as error:
            result['git_error'] = str(error)
    success = result.get('worker_exit_code') == 0 and not any(result.get(k) for k in
        ('installation_error', 'preparation_error', 'failures', 'preservation_error', 'dispatch_error', 'git_error'))
    success = success and (result.get('source_installed') is True if installation
                           else result.get('accepted_owners') == [TARGET])
    result['source_install_complete' if installation else 'new_owner_accepted'] = success
    c.ag.d.save(run / result_name, result)
    print(json.dumps({'path': str(run / result_name), **result}, sort_keys=True), flush=True)
    return 0 if success else max(1, int(result.get('worker_exit_code', 3)))



def main():
    validate_inputs(INPUTS)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true'); mode.add_argument('--run', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args(); path = Path(__file__)
    require(path.is_file() and not path.is_symlink(), 'entrypoint must be a regular file')
    c = load(args.source_commit, path.read_bytes())
    if args.check:
        require(args.inside_lane is None, '--check is read-only and has no worker lane')
        print(json.dumps(check(c), sort_keys=True), flush=True); return 0
    if args.inside_lane:
        run = args.inside_lane
        require(run.is_absolute() and run.resolve() == run and run.parent == ROOT / c.commit / 'runs' and
                re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected Dictionary worker path')
        require(unique_run(run.parent) == run, 'nonunique Dictionary worker attempt')
        return worker(c, run)
    state = prepare(c); spec = new_spec(c, state)
    require(new_owner_state(c, spec)['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT',
            'already accepted Dictionary owner: use --check, never recompile')
    unchanged(c, state)
    return dispatch(c)


if __name__ == '__main__':
    try:
        validate_inputs(INPUTS)
        os.environ.update({'GIT_OPTIONAL_LOCKS':'0','GIT_NO_LAZY_FETCH':'1',
                           'GIT_TERMINAL_PROMPT':'0','PYTHONDONTWRITEBYTECODE':'1'})
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status':'INDEPENDENT_DICTIONARY_HOLD','error_type':type(error).__name__,
            'error':str(error),'new_owner_accepted':False,'whole_P1_5_complete':False}), flush=True)
        raise SystemExit(3)
