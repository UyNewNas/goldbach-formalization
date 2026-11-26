#!/usr/bin/env python3
"""Independent formal acceptance of one exact AD TrimLogAccuracy module.

The old twenty-one-target runner and manifest are read unchanged. This new owner
has a separate scope and cannot change the old 18/21 count or close all P1.5.
"""
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
PACKAGE = 'docs/p1/20261126/p15-trimlog-accuracy/'
SCRIPT = PACKAGE + 'run_trimlog.py'
INSTALLER = PACKAGE + 'install_trimlog_source.py'
PROBE = PACKAGE + 'probe/ACTUAL_TRIMLOG_PROBE_RESULT.json'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
AH = 'c8ef05d421f8ba388aadc6d7d24c626ff40c9c14'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
AF = 'b06429e9c2d8fbd5c654105d5f4e44f26c0865f4'
AE = 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
ANCESTORS = (AG, AE, '9f2013ad9cb9caac9cec03cb213d9949c4443c65',
    'ae373b971d2b88f97532dc883d835751dd10c67b', 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
    '6484b348b82d8ca6221262bb53f255fa92e9adc8', '2779eb7b2b0433bea10d523ef976317893f8429d',
    '18e41c4a1c01ca22e5537acb934e04891279b616', '445201674271f9d9d6b846ecc634a10c4a0c6043')
TARGET = 'ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy'
SOURCE = 'ImbalancedChen/P1OriginalSingletonAtlasTrimLogAccuracy.lean'
ORIGIN = 'docs/source-only/20261126/p1-atlas-trim-log-accuracy-budget-sum/P1OriginalSingletonAtlasTrimLogAccuracy.lean'
SOURCE_FP = {'bytes': 4303, 'sha256': 'b0786de15bf78fed3751fc408735482b807e39931e87056d3d60780fa2123bb4'}
LOWER = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
ATLAS = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'
RESERVE = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
ROUGH = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'
AE_OWNERS = [LOWER, ATLAS]
AG_OWNERS = [RESERVE, ROUGH]
AE_DRIVER_FP = {'bytes': 306454, 'sha256': '2fac63da6dd93b54ded3a8c5c8542558f3a03a738092fcb43b2336ab8674705e'}
AE_MANIFEST_FP = {'bytes': 364863, 'sha256': '6c5c0b8795a2c6fa1265e5030b12a9e77500efe651b8796b11b748a0ed47ada5'}
AG_DRIVER_FP = {'bytes': 343325, 'sha256': '0440906dfc3caa894ff7226e53ad42be54adda1d5879bd1a72cad578a3b3612d'}
AG_MANIFEST_FP = {'bytes': 369103, 'sha256': '21c0b14701a2123edab7353aa27dbb9c950427a805d75aaa3562c6033eb137f9'}
EVIDENCE_DOCS = {'ae_collector': {'path': 'docs/p1/20261126/p15-reservebranches-first-compile-repair/collect_ae_acceptance.py',
                  'bytes': 37350,
                  'sha256': '1f58ed8515916b7d8f83d85910e7a05f0fd68cf769e60552159f23c61686c916'},
 'ae_read': {'path': 'docs/p1/20261126/p15-reservebranches-first-compile-repair/ACTUAL_AE_ACCEPTANCE_READ.json',
             'bytes': 45763,
             'sha256': 'b630616bbcfe7e1b073ff0046efa7c606f4319ca66442286db7a7898d611075f'},
 'ae_lower': {'path': 'docs/p1/20261125/p15-current-public-acceptance/LOWERTRIM_AE_PUBLIC_ACCEPTANCE.json',
              'bytes': 11615,
              'sha256': 'fac4e9665c918179f4f72fae8fc009a5ccb912f4674bc8d56dbf256906470681'},
 'ae_atlas': {'path': 'docs/p1/20261125/p15-current-public-acceptance/ATLASTRIM_AE_PUBLIC_ACCEPTANCE.json',
              'bytes': 7359,
              'sha256': '18201db1ec50df50b023d894abaae0f4675650f4c3a9e8efe619b344c9ada325'},
 'ag_collector': {'path': 'docs/p1/20261126/p15-ag-acceptance/collect_ag_acceptance.py',
                  'bytes': 32762,
                  'sha256': 'fa6c44804c4f8af8f809940db6e61c72aed9c4b651d82682707471539b3c2ba7'},
 'ag_read': {'path': 'docs/p1/20261126/p15-ag-acceptance/ACTUAL_AG_ACCEPTANCE_READ.json',
             'bytes': 47262,
             'sha256': 'fbe0f5d38f9563e7ebbefab6e232591a9fc8fa3a53dc420e6719f1ea94cfe687'},
 'ag_reserve': {'path': 'docs/p1/20261125/p15-current-public-acceptance/RESERVEBRANCHES_AG_PUBLIC_ACCEPTANCE.json',
                'bytes': 11664,
                'sha256': '24872c1040b9c30933b7a37e9729eb7d1cfd3784bf55c355d49d9780a09d2dbf'},
 'ag_rough': {'path': 'docs/p1/20261125/p15-current-public-acceptance/ATLASROUGHPRIME_AG_PUBLIC_ACCEPTANCE.json',
              'bytes': 7580,
              'sha256': 'a069090c31c719362b81e5ea7eadd5ea7a473ec7faa4a99dd8f839041a630058'}}
INPUTS = {'probe_job': 'job_7665d03cf175443da5d86004875cb7a6',
 'probe_document': {'bytes': 2875,
                    'sha256': 'eb98e6b13ba803051820a5637cad7c3c512ffc41f8090997cf2e07203557b2e7'},
 'canonical_source': {'bytes': 4303,
                      'sha256': 'b0786de15bf78fed3751fc408735482b807e39931e87056d3d60780fa2123bb4'}}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def value_fp(value):
    return raw_fp((json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode())


def pin(row):
    return {key: row[key] for key in ('bytes', 'sha256')}


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


def load_driver(commit, anchor, driver_fp, manifest_fp):
    raw, manifest = git_file(commit, DRIVER), git_file(commit, MANIFEST)
    entry = ROOT / commit / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw) == driver_fp and raw_fp(manifest) == manifest_fp and
            fp(entry) == driver_fp and entry.read_bytes() == raw, 'original reader/manifest differs')
    driver = ModuleType('immutable_trimlog_base_' + commit); driver.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
            (REPO, PROJECT, ROOT, DRIVER, anchor), 'original reader environment differs')
    return driver


def load(commit, executed):
    require(__debug__ and isinstance(INPUTS, dict) and re.fullmatch('[0-9a-f]{40}', commit) and
            INPUTS['canonical_source'] == SOURCE_FP and
            re.fullmatch('job_[0-9a-f]{32}', INPUTS['probe_job']), 'actual publication/probe inputs are unbound')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
            subprocess.run(['git', 'merge-base', '--is-ancestor', AH, commit], cwd=REPO).returncode == 0,
            'new publication must descend from fixed AH evidence')
    require(executed == git_file(commit, SCRIPT), 'executed independent adapter differs from publication')
    require(git_file(commit, DRIVER) == git_file(AG, DRIVER) and
            git_file(commit, MANIFEST) == git_file(AG, MANIFEST), 'old 21-target entrypoint changed')
    source = git_file(commit, SOURCE)
    require(raw_fp(source) == SOURCE_FP and source == git_file(AD, ORIGIN), 'canonical differs from exact AD source')
    docs, readers = {}, {}
    for name, binding in EVIDENCE_DOCS.items():
        raw = git_file(AH, binding['path'])
        require(raw_fp(raw) == pin(binding) and git_file(commit, binding['path']) == raw,
                'original published evidence differs: ' + name)
        if name.endswith('_collector'):
            reader = ModuleType('immutable_' + name); reader.__file__ = binding['path']
            exec(compile(raw, binding['path'], 'exec'), reader.__dict__)
            readers[name[:2]] = reader
        else:
            docs[name] = json.loads(raw)
    require((readers['ae'].AE, readers['ae'].AD, readers['ag'].AG, readers['ag'].AF) ==
            (AE, AD, AG, AF), 'original collector identities differ')
    for label in ('ae', 'ag'):
        require(value_fp(readers[label].PINNED) == docs[label + '_read']['frozen_actual_input_binding'],
                'original collector frozen input binding differs')
    raw_probe = git_file(commit, PROBE)
    require(raw_fp(raw_probe) == INPUTS['probe_document'], 'published actual whole probe differs')
    probe = json.loads(raw_probe)
    require(probe['schema'] == 'p15_AtlasTrimLogAccuracy_actual_whole_module_no_output_probe_v1' and
            probe['candidate_publication'] == {'commit': AD, 'path': ORIGIN, **SOURCE_FP} and
            probe['runtime_source_commit'] == AG and probe['original_AE_acceptance_source_commit'] == AE and
            probe['exit_code'] == 0 and pin(probe['candidate']) == SOURCE_FP and
            probe['whole_original_module_submitted'] is True and probe['Lean_typecheck_commands'] == 1 and
            probe['original_serializer_and_guard_used'] is True and probe['lake_no_build_env_lean'] is True and
            probe['output_object_requested'] is False and probe['existing_project_modules_rebuilt'] == [] and
            probe['new_canonical_source_and_21_project_artifacts_remained_absent'] is True and
            probe['all_original_AG_AE_AC_AA_Y_W_U_S_Q_evidence_runtime_and_Git_preserved'] is True and
            probe['normal_or_kernel_acceptance_claimed'] is False and probe['new_owner_acceptance'] is False,
            'actual no-output probe status/scope differs')
    d = load_driver(AE, AD, AE_DRIVER_FP, AE_MANIFEST_FP)
    g = load_driver(AG, AF, AG_DRIVER_FP, AG_MANIFEST_FP)
    c = SimpleNamespace(commit=commit, script=executed, source=source, d=d, g=g,
        ae=d.helpers(), ag=g.helpers(), readers=readers, docs=docs, probe=probe)
    require(c.ag.h.imports(source) == [ATLAS], 'new module must have only its original AtlasTrim import')
    c.identity = {'source_commit': commit, 'adapter': {'path': SCRIPT, **raw_fp(executed)},
        'new_owner': TARGET, 'canonical_source': {'path': SOURCE, **SOURCE_FP},
        'source_origin': {'commit': AD, 'path': ORIGIN, **SOURCE_FP},
        'evidence_publication': AH, 'original_accepting_commits': [AE, AG],
        'probe_job': INPUTS['probe_job'], 'probe_document': {'path': PROBE, **INPUTS['probe_document']},
        'independent_from_original_21_target_registry': True}
    return c


def read_original(c, label, driver, s, spec, modules, origins, public_keys):
    reader, published = c.readers[label], c.docs[label + '_read']
    require(published['selected_owners_revalidated'] == modules and
            value_fp(spec.baseline) == published['current_read_snapshot'], 'original accepted scope snapshot differs')
    runs = [reader.read_run(driver, s, spec.graph, i, fixed) for i, fixed in enumerate(reader.PINNED['runs'])]
    require(reader.accepting_runs(runs) == origins and [row[2] for row in runs] == published['original_runs'],
            'original run identity or terminal status differs')
    common, bindings = reader.identity(spec, modules), {}
    for module, index in origins.items():
        owner = reader.read_owner(driver, s, spec, runs, module, index, reader.PINNED['owners'][module])
        flat = reader.flat_summary(runs, index, module, owner, common)
        require(flat == c.docs[public_keys[module]] == published['public_summaries'][reader.PINNED['owners'][module]['public_name']],
                'original owner/public/six-receipt binding differs')
        bindings[module] = driver.acceptance_binding(s, AE if label == 'ae' else AG, module)
    return runs, bindings


def source_inventory(c, graph):
    return {m: fp(PROJECT / c.ag.h.module_path(m)) for m in sorted(graph)}


def artifact_inventory(c, modules):
    return {m: c.g.module_artifacts(c.ag, m) for m in sorted(modules)}


def prepare_base(c):
    ae = c.d.preflight(c.ae, AE, AE_OWNERS)
    ag = c.g.preflight(c.ag, AG, AG_OWNERS)
    require(ae.graph == ag.graph and len(ag.graph) == 360 and
            (len(ae.active), len(ae.dependency_pins), len(ae.supplier_evidence)) == (153, 151, 25) and
            (len(ag.active), len(ag.dependency_pins), len(ag.supplier_evidence)) == (144, 142, 24) and
            ae.order == AE_OWNERS and ag.order == AG_OWNERS and
            set(ae.initial_owners) == set(AE_OWNERS) and set(ag.initial_owners) == set(AG_OWNERS) and
            all(ae.sources[m] == ag.sources[m] for m in ae.active) and RESERVE not in ae.active and
            TARGET not in ag.graph and TARGET not in c.g.TARGETS, 'separate old scopes or new-owner boundary differs')
    ae_runs, ae_bindings = read_original(c, 'ae', c.d, c.ae, ae, AE_OWNERS,
        {LOWER: 0, ATLAS: 1}, {LOWER: 'ae_lower', ATLAS: 'ae_atlas'})
    ag_runs, ag_bindings = read_original(c, 'ag', c.g, c.ag, ag, AG_OWNERS,
        {RESERVE: 0, ROUGH: 1}, {RESERVE: 'ag_reserve', ROUGH: 'ag_rough'})
    suppliers = set(ag.manifest['previously_accepted_targets']) | set(ag.manifest['accepted_suppliers'])
    require(ae.supplier_evidence == {m: ae_runs[1][0]['original_supplier_acceptance_bindings'][m]
            for m in ae.active & (set(ae.manifest['previously_accepted_targets']) | set(ae.manifest['accepted_suppliers']))} and
            ag.supplier_evidence == ag_runs[1][0]['original_supplier_acceptance_bindings'], 'original supplier dictionaries differ')
    union = ae.active | ag.active; watch = union | set(c.g.TARGETS)
    require(len(union) == 157 and len(watch) == 160 and len(ag.manifest['previously_accepted_targets']) == 16 and
            not ae.active & set(ag.manifest['unaccepted_p3_dependencies']), 'old union/watch/P3 scope differs')
    sources, artifacts = source_inventory(c, ag.graph), artifact_inventory(c, watch)
    require(sources == {m: pin(row) for m, row in ag.manifest['project_sources'].items()} and
            sum(map(len, artifacts.values())) == 3360, 'old 360-source/160-artifact inventory differs')
    for m, row in ag.manifest['project_sources'].items():
        raw = git_file(c.commit, row['path'])
        require(raw_fp(raw) == pin(row) and c.ag.h.imports(raw) == row['all_imports'], 'old published source/import changed: ' + m)
    trees = {commit: c.readers['ag'].tree_inventory(ROOT / commit) for commit in ANCESTORS}
    require({k: {'entry_count': len(v), **value_fp(v)} for k, v in trees.items()} ==
            c.docs['ag_read']['complete_original_AG_AE_AC_AA_Y_W_U_S_Q_evidence_inventory'], 'old nine evidence trees differ')
    retained = {}
    for runs in (ae_runs, ag_runs):
        for _, context, _ in runs:
            for path, expected in context['retained_original_evidence'].items():
                require(path not in retained or retained[path] == expected, 'old retained input conflict')
                retained[path] = expected
    extras = c.readers['ag'].PINNED['extra_pins']
    require(len(extras) == 9 and extras == c.docs['ag_read']['preserved_extra_evidence'], 'old nine external pins differ')
    retained.update(extras)
    probe = c.probe
    probe_file = Path(probe['candidate']['path']); probe_log = Path(probe['log']['path'])
    require(probe_file.read_bytes() == c.source and probe_log.read_text() == probe['compiler_output'], 'actual probe source/log differs')
    retained.update({str(probe_file): SOURCE_FP, str(probe_log): pin(probe['log']),
        str(probe_file.parent / 'ACTUAL_TRIMLOG_PROBE_RESULT.json'): INPUTS['probe_document']})
    require(all(fp(path) == expected for path, expected in retained.items()), 'retained original/probe evidence differs')
    state = SimpleNamespace(ae=ae, ag=ag, ae_bindings=ae_bindings, ag_bindings=ag_bindings,
        sources=sources, artifacts=artifacts, trees=trees, retained=retained, watch=watch,
        git=c.ag.d.original_git_state(REPO))
    unchanged_old(c, state)
    return state


def unchanged_old(c, state):
    require(source_inventory(c, state.ag.graph) == state.sources and artifact_inventory(c, state.watch) == state.artifacts and
            {commit: c.readers['ag'].tree_inventory(ROOT / commit) for commit in ANCESTORS} == state.trees and
            c.d.snapshot(c.ae, state.ae) == state.ae.baseline and c.g.snapshot(c.ag, state.ag) == state.ag.baseline and
            {m: c.d.acceptance_binding(c.ae, AE, m) for m in AE_OWNERS} == state.ae_bindings and
            {m: c.g.acceptance_binding(c.ag, AG, m) for m in AG_OWNERS} == state.ag_bindings and
            all(fp(path) == expected for path, expected in state.retained.items()) and
            c.ag.d.original_git_state(REPO) == state.git, 'old source/artifact/acceptance/evidence/runtime/Git changed')


def require_new_slot(source, artifacts, history, *, installed):
    require(not history and len(artifacts) == 21 and all(value is None for value in artifacts.values()),
            'new owner has started history or project artifacts; inspection required')
    require(source == SOURCE_FP if installed else source in (None, SOURCE_FP), 'new canonical source differs')


def owner_history(commit):
    result = []
    require(ROOT.is_dir() and ROOT.resolve() == ROOT, 'original acceptance root differs')
    for folder in ROOT.iterdir():
        if re.fullmatch('[0-9a-f]{40}', folder.name) and os.path.lexists(folder / TARGET):
            require(folder.is_dir() and not folder.is_symlink(), 'nonregular owner history root')
            result.append(folder / TARGET)
    return result


def new_spec(c, state):
    require(fp(PROJECT / SOURCE) == SOURCE_FP and (PROJECT / SOURCE).resolve() == PROJECT / SOURCE,
            'exact new canonical source must be installed separately')
    graph = {**state.ag.graph, TARGET: [ATLAS]}; sources = {**state.ag.sources, TARGET: SOURCE_FP['sha256']}
    active = c.ag.h.closure(graph, [TARGET])
    require(len(graph) == 361 and active == state.ae.active | {TARGET} and len(active) == 154,
            'new 154-source scope does not match the exact AE dependency prefix')
    dependencies = copy.deepcopy(state.ae.dependency_pins)
    for module in AE_OWNERS:
        dependencies[module] = state.ae_bindings[module]['all_observed_target_artifacts']
    require(set(dependencies) == active - {TARGET} and len(dependencies) == 153 and
            all(len(value) == 21 for value in dependencies.values()), 'new owner dependency inventory differs')
    observed_graph, observed = c.ag.h.project_graph(PROJECT, [TARGET])
    require(observed_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in observed.items()} == {m: sources[m] for m in active}, 'installed new graph differs')
    spec = SimpleNamespace(graph=graph, sources=sources, active=active, selected={TARGET}, order=[TARGET],
        dependency_pins=dependencies, review=state.ag.review, retained_inputs=dict(state.retained),
        manifest={'project_sources': {TARGET: {'all_imports': [ATLAS]}}},
        input_bindings={'source_commit': c.commit, 'selected_targets': [TARGET], 'independent_owner': c.identity,
            'original_AE_context': value_fp(state.ae.baseline), 'original_AG_context': value_fp(state.ag.baseline)})
    spec.baseline = c.g.snapshot(c.ag, spec)
    return spec


def new_owner_state(c, spec):
    history = owner_history(c.commit); folder = ROOT / c.commit / TARGET
    require(all(path == folder for path in history), 'foreign accepting/started history for new owner requires inspection')
    normal = folder / 'normal' / TARGET / 'NORMAL_PASS.json'
    artifacts = c.g.module_artifacts(c.ag, TARGET)
    if not os.path.lexists(folder):
        require_new_slot(fp(PROJECT / SOURCE), artifacts, history, installed=True)
        result = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
        require(result['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT', 'fresh owner classification differs')
        return result
    require(normal.is_file() and not normal.is_symlink(), 'partial started owner without normal receipt; inspection required')
    result = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
    c.g.require_completed_existing_owner(c.ag, c.commit, spec, TARGET, result)
    return result


def accepted_public(c, spec):
    existing = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
    c.g.require_completed_existing_owner(c.ag, c.commit, spec, TARGET, existing)
    binding = c.g.acceptance_binding(c.ag, c.commit, TARGET)
    require(len(binding['audits']) == 1 and len(binding['source_plus_five_outputs']) == 6 and
            len(binding['all_observed_target_artifacts']) == 21, 'new single-owner receipt shape differs')
    audit = c.ag.api.read_json(Path(binding['audits'][0]['result']['path']))
    return {'module': TARGET, 'source_commit': c.commit, 'binding': binding,
        'audit_id': Path(binding['audits'][0]['plan']['path']).parent.name,
        'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports'],
        'only_standard_axioms': audit['only_standard_axioms'],
        'full_owned_including_private_generated': audit['full_owned_including_private_generated'],
        'original_21_target_count': 21, 'original_21_accepted_count': 18,
        'new_owner_is_outside_original_21': True, 'whole_P1_5_complete': False}


def preservation_summary(state):
    return {'old_source_count': len(state.sources), 'old_watch_modules': len(state.artifacts),
        'old_artifact_slots': sum(map(len, state.artifacts.values())), 'old_evidence_tree_count': len(state.trees),
        'old_sources': value_fp(state.sources), 'old_artifacts': value_fp(state.artifacts),
        'old_evidence': value_fp(state.trees), 'retained_inputs': value_fp(state.retained),
        'original_AE_acceptances': state.ae_bindings, 'original_AG_acceptances': state.ag_bindings}


def check(c):
    state = prepare_base(c); spec = new_spec(c, state)
    existing = new_owner_state(c, spec)
    result = {'schema': 'p15_independent_trimlog_readonly_v1', 'identity': c.identity,
        'active_source_count': 154, 'preserved_dependency_count': 153,
        'new_owner_accepted': existing['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT',
        'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}
    if result['new_owner_accepted']:
        result.update(status='ORIGINAL_TRIMLOG_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION', owner=accepted_public(c, spec))
    else:
        result.update(status='FRESH_INSTALLED_TRIMLOG_NOT_YET_ACCEPTED', owner=None)
    require(c.g.snapshot(c.ag, spec) == spec.baseline, 'new-owner dependency context changed during read')
    unchanged_old(c, state)
    result['preservation'] = preservation_summary(state)
    return result


def worker(c, run):
    c.ag.d.verify_lane(c.ag.h)
    state = prepare_base(c); spec = new_spec(c, state)
    existing = new_owner_state(c, spec)
    require(existing['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT', 'already accepted new owner: use --check, never recompile')
    result = {'schema': 'p15_independent_trimlog_acceptance_v1', 'identity': c.identity,
        'targets': [TARGET], 'accepted_owners': [], 'failures': {}, 'new_owner_is_outside_original_21': True,
        'original_21_target_count': 21, 'original_21_accepted_count': 18, 'whole_P1_5_complete': False}
    c.ag.d.save(run / 'CONTEXT_BEFORE.json', spec.baseline)
    try:
        result['direct_import_readiness'] = c.g.direct_import_readiness(c.ag, spec, TARGET, run)
        require(c.g.snapshot(c.ag, spec) == spec.baseline, 'context changed during no-build import readiness')
        unchanged_old(c, state)
        c.g.run_owner(c.ag, c.commit, ROOT / c.commit, run, TARGET, spec.graph, spec.sources)
        owner = accepted_public(c, spec)
        require(c.g.snapshot(c.ag, spec) == spec.baseline, 'context changed during new owner acceptance')
        unchanged_old(c, state)
        before = c.g.module_artifacts(c.ag, TARGET)
        stock = c.ag.ops.run(run, 'final-stock-readiness', c.ag.h.guard(0,
            ['lake', '--no-build', 'build', '+' + TARGET + ':olean']), cwd=PROJECT)
        require(stock['exit_code'] == 0 and stock['actual_built_modules'] == stock['actual_failed_modules'] == [] and
                c.g.module_artifacts(c.ag, TARGET) == before, 'new-owner final no-build stock differs')
        result.update(accepted_owners=[TARGET], owner=owner, final_stock_readiness=stock)
    except Exception as error:
        result['failures'][TARGET] = str(error)
    finally:
        try:
            after = c.g.snapshot(c.ag, spec); c.ag.d.save(run / 'CONTEXT_AFTER.json', after)
            require(after == spec.baseline, 'new owner dependencies/runtime changed')
            unchanged_old(c, state)
        except Exception as error:
            result['preservation_error'] = str(error)
    result['preservation'] = preservation_summary(state)
    c.ag.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('preservation_error')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true'); mode.add_argument('--run', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args(); path = Path(__file__)
    require(path.is_file() and not path.is_symlink(), 'entrypoint must be a regular file')
    c = load(args.source_commit, path.read_bytes())
    if args.check:
        require(args.inside_lane is None, '--check is read-only and has no lane')
        print(json.dumps(check(c), sort_keys=True), flush=True); return 0
    runs = ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        require(run.is_absolute() and run.resolve() == run and run.parent == runs and
                re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected new owner worker path')
        return worker(c, run)
    require(runs.resolve() == runs, 'new evidence parent traverses a symlink')
    run = c.ag.d.attempt(runs); git = c.ag.d.original_git_state(REPO)
    c.ag.d.save(run / 'GIT_BEFORE.json', git)
    executed = run / 'executed-trimlog.py'; c.ag.d.write_frozen(executed, c.script)
    try:
        command = c.ag.ops.run(run, 'serialized-trimlog', c.ag.h.serialize(0, run / 'TRIMLOG_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--run', '--inside-lane', str(run)]), relay=True)
        worker_result = c.ag.api.read_json(run / 'WORKER_RESULT.json')
        result = {**worker_result, 'worker_exit_code': command['exit_code'],
            'new_owner_accepted': command['exit_code'] == 0 and worker_result['accepted_owners'] == [TARGET]}
        c.ag.d.save(run / 'RESULT.json', result)
    finally:
        after = c.ag.d.original_git_state(REPO); c.ag.d.save(run / 'GIT_AFTER.json', after)
        require(after == git, 'original dirty Git state changed')
    print(json.dumps({'path': str(run / 'RESULT.json'), **result}, sort_keys=True), flush=True)
    return command['exit_code']


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'INDEPENDENT_TRIMLOG_HOLD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_accepted': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
