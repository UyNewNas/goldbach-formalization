#!/usr/bin/env python3
"""Separate Geometry acceptance using immutable AI reads and the original AG API.

INPUTS remains unbound until a successful actual whole-module probe is published.
An existing attempt, partial owner, or foreign owner history is never retried.
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
INSTALL_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-geometry-source-install-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-remaining-typei-geometry-probe-v1')
PACKAGE = 'docs/p1/20261127/p15-remaining-typei-geometry/'
SCRIPT = PACKAGE + 'run_geometry.py'
INSTALLER = PACKAGE + 'install_geometry_source.py'
PROBE_SCRIPT = PACKAGE + 'probe_geometry.py'
PROBE = PACKAGE + 'probe/ACTUAL_GEOMETRY_PROBE_RESULT.json'
AI = '6d9072f7b33332eaf5ecfff22876e0404cd6ab51'
AJ = '6d87764cbc9fce5b10a2665a458619e44d8255ae'
AK = 'd4f88a20262af7d54ed0e6e58dfc533496c595e3'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
READER = 'docs/p1/20261126/p15-trimlog-accuracy/run_trimlog.py'
READER_FP = {'bytes': 36541, 'sha256': '0c6307af83c197123bd2da678bfd4ac6b76916169d6d457f83733461725b8272'}
AI_INSTALLER = 'docs/p1/20261126/p15-trimlog-accuracy/install_trimlog_source.py'
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/TRIMLOG_AI_PUBLIC_ACCEPTANCE.json'
PUBLIC_FP = {'bytes': 18539, 'sha256': '2bb01aa28ab117933b0ec8f766245f0a9faaeb750448bb6e47536c4dbfdf18f0'}
TARGET = 'ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry'
SOURCE = 'ImbalancedChen/P1OriginalSingletonRemainingTypeIGeometry.lean'
ORIGINAL_SOURCE_FP = {'bytes': 11273, 'sha256': 'a0f9f8dd7c14158366e1247d26db649b6b66f2505f5e88b5f3472f81ff63f5f6'}
SOURCE_FP = {'bytes': 11337, 'sha256': '2b982d9bedc546b5ef5f01cc64b0d6401ac5b2a830585e6998924dba74f0d91f'}
FAILED_PROBE_FP = {'bytes': 42835, 'sha256': 'bbdf61c6f78ae5b34b541fd3340bab2439d1aa57307224a3c8e299d14c396b0b'}
IMPORTS = ['ImbalancedChen.P1OriginalSingletonSmoothLicence',
           'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
           'ImbalancedChen.P5OriginalHBMediumChartReserves']
TRIMLOG = 'ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy'
ATLAS = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'
RESERVE = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
ROUGH = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'
INPUTS = None  # UNBOUND: an exit-1 probe cannot enable installation or acceptance.


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


def validate_inputs(inputs):
    require(isinstance(inputs, dict) and inputs.get('canonical_source') == SOURCE_FP and
            isinstance(inputs.get('probe_job'), str) and re.fullmatch('job_[0-9a-f]{32}', inputs['probe_job']) and
            isinstance(inputs.get('probe_publication'), str) and re.fullmatch('[0-9a-f]{40}', inputs['probe_publication']) and
            isinstance(inputs.get('probe_document'), dict) and
            type(inputs['probe_document'].get('bytes')) is int and inputs['probe_document']['bytes'] > 0 and
            isinstance(inputs['probe_document'].get('sha256'), str) and
            re.fullmatch('[0-9a-f]{64}', inputs['probe_document']['sha256']),
            'actual successful Geometry probe inputs are unbound')


def require_corrected_source(original, source):
    anchor = b'open P5CanonicalTentNarrowSingletonTransfer (actualLicence)\n'
    notation = b'\nlocal notation "R" => P5Z.ExactOriginalSmoothDyadicPartition.R\n'
    require(raw_fp(original) == ORIGINAL_SOURCE_FP and original.count(anchor) == 1 and
            raw_fp(source) == SOURCE_FP and source == original.replace(anchor, anchor + notation),
            'Geometry is not the exact single local-notation repair of its AJ source')


def scope(manifest):
    sources = manifest['project_sources']
    graph = {m: row['imports'] for m, row in sources.items()}
    require(len(graph) == 360 and TARGET not in graph and TRIMLOG not in graph,
            'original graph/new-owner identity differs')
    def closure(roots):
        seen = set()
        def visit(module):
            if module in seen:
                return
            require(module in graph, 'missing project dependency: ' + module)
            seen.add(module)
            for imported in graph[module]:
                visit(imported)
        for module in roots:
            visit(module)
        return seen
    dependencies, old_active = closure(IMPORTS), closure([RESERVE, ROUGH])
    require(len(dependencies) == 141 and len(old_active) == 144 and dependencies <= old_active and
            RESERVE in dependencies and ROUGH not in dependencies and
            not dependencies.intersection(manifest['unaccepted_p3_dependencies']),
            'Geometry must have exactly 141 accepted dependencies within original AG 144')
    return {'owner': TARGET, 'direct_imports': IMPORTS,
            'active_source_count_with_owner': 142, 'dependency_count': 141,
            'dependency_sources': {m: {k: sources[m][k] for k in ('path', 'bytes', 'sha256')}
                                   for m in sorted(dependencies)},
            'AG_accepted_scope_count': 144, 'subset_of_original_AG_scope': True,
            'unaccepted_P3_dependencies': []}


def dependency_inventory(ag, bindings, dependencies, artifact_paths):
    inventory = copy.deepcopy(ag.baseline['preserved_dependency_artifacts'])
    require(set(bindings) == {RESERVE, ROUGH} and set(inventory) == ag.active - {RESERVE, ROUGH},
            'original AG baseline/owner dependency binding differs')
    for module in (RESERVE, ROUGH):
        inventory[module] = copy.deepcopy(bindings[module]['all_observed_target_artifacts'])
    require(set(inventory) == ag.active and len(inventory) == 144 and
            len(dependencies) == 141 and dependencies <= ag.active and
            RESERVE in dependencies and ROUGH not in dependencies,
            'complete AG dependency inventory differs')
    require(all(len(row) == 21 and set(row) == set(artifact_paths(module))
                for module, row in inventory.items()),
            'full 21-artifact inventory required; fixed two-artifact pins cannot substitute')
    return {module: inventory[module] for module in sorted(dependencies)}


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


def load(commit, executed):
    validate_inputs(INPUTS)
    require(__debug__ and isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit),
            'exact publication commit required')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
            subprocess.run(['git', 'merge-base', '--is-ancestor', AJ, commit], cwd=REPO).returncode == 0 and
            subprocess.run(['git', 'merge-base', '--is-ancestor', INPUTS['probe_publication'], commit],
                           cwd=REPO).returncode == 0,
            'publication must descend from AJ and its actual successful probe publication')
    require(executed == git_file(commit, SCRIPT), 'executed Geometry adapter differs from publication')
    raw = git_file(AI, READER)
    entry = ROOT / AI / 'runs/attempt-00000/executed-trimlog.py'
    require(raw_fp(raw) == READER_FP and fp(entry) == READER_FP and entry.read_bytes() == raw and
            git_file(commit, READER) == raw and git_file(commit, AI_INSTALLER) == git_file(AI, AI_INSTALLER),
            'immutable original AI reader/installer differs')
    base = ModuleType('immutable_geometry_formal_AI_reader')
    base.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), base.__dict__)
    ai = base.load(AI, raw)
    require(base.TARGET == TRIMLOG and ai.commit == AI and base.ROOT == ROOT and
            base.PROJECT == PROJECT and base.REPO == REPO and base.AG == AG,
            'fixed AI reader identity differs')
    require(git_file(commit, base.DRIVER) == git_file(AG, base.DRIVER) and
            git_file(commit, base.MANIFEST) == git_file(AG, base.MANIFEST),
            'original AG driver/manifest or 21-target registry changed')
    source = git_file(INPUTS['probe_publication'], SOURCE)
    require_corrected_source(git_file(AJ, SOURCE), source)
    require(git_file(commit, SOURCE) == source and
            ai.ag.h.imports(source) == IMPORTS and git_file(commit, base.SOURCE) == ai.source,
            'complete Geometry/AI published source or Geometry imports differ')
    public_raw = git_file(AJ, PUBLIC)
    require(raw_fp(public_raw) == PUBLIC_FP and git_file(commit, PUBLIC) == public_raw,
            'fixed AJ publication of original AI acceptance differs')
    manifest = json.loads(git_file(AG, base.MANIFEST))
    selected = scope(manifest)
    probe_raw = git_file(commit, PROBE)
    require(raw_fp(probe_raw) == INPUTS['probe_document'], 'actual Geometry probe document differs')
    c = SimpleNamespace(commit=commit, script=executed, source=source, base=base, ai=ai,
        g=ai.g, ag=ai.ag, published=json.loads(public_raw), manifest=manifest,
        selected=selected, probe=json.loads(probe_raw))
    require(TARGET not in c.g.TARGETS and len(c.g.TARGETS) == 21, 'new owner entered original registry')
    c.identity = {'source_commit': commit, 'adapter': {'path': SCRIPT, **raw_fp(executed)},
        'new_owner': TARGET, 'canonical_source': {'path': SOURCE, **SOURCE_FP},
        'source_origin': {'commit': INPUTS['probe_publication'], 'path': SOURCE, **SOURCE_FP},
        'original_geometry_source': {'commit': AJ, 'path': SOURCE, **ORIGINAL_SOURCE_FP},
        'repair': 'one_local_notation_for_original_dyadic_R',
        'immutable_AI_reader': {'commit': AI, 'path': READER, **READER_FP},
        'original_AG_acceptance_commit': AG, 'original_AI_acceptance_commit': AI,
        'probe_job': INPUTS['probe_job'], 'probe_publication': INPUTS['probe_publication'],
        'probe_document': {'path': PROBE, **INPUTS['probe_document']},
        'independent_from_original_21_target_registry': True}
    return c


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


def read_probe(c):
    p = c.probe
    require(p['schema'] == 'p15_remaining_typei_geometry_whole_no_output_probe_v2' and
            p['publication'] == INPUTS['probe_publication'] and
            p['source_origin'] == {'commit': INPUTS['probe_publication'], 'path': SOURCE, **SOURCE_FP} and
            p['original_geometry_source'] == {'commit': AJ, 'path': SOURCE, **ORIGINAL_SOURCE_FP} and
            p['repair'] == 'one_local_notation_for_original_dyadic_R' and
            p['original_failed_probe'] == {'publication': AK, **FAILED_PROBE_FP} and
            p['original_AI_acceptance_commit'] == AI and p['original_AG_acceptance_commit'] == AG and
            p['scope'] == c.selected and p['probe_passed'] is True and p['exit_code'] == 0 and
            p['preservation_passed'] is True and p['typecheck_command_completed'] is True and
            p['whole_original_module_submitted'] is True and p['output_object_requested'] is False and
            p['existing_project_modules_rebuilt'] == [] and p['original_serializer_and_guard_used'] is True and
            p['normal_or_kernel_acceptance_claimed'] is False and p['new_owner_accepted'] is False and
            p['whole_P1_5_complete'] is False and
            not any(p.get(k) for k in ('probe_error', 'preservation_error')),
            'actual whole-module no-output probe is not a successful preserved result')
    source = Path(p['source']['path']); run = source.parent
    require(source.is_absolute() and source.resolve() == source and
            source.name == 'OriginalSingletonRemainingTypeIGeometryProbe.lean' and
            run.parent == PROBE_ROOT / INPUTS['probe_publication'] / 'runs' and
            re.fullmatch('attempt-[0-9]{5}', run.name) and fp(source) == SOURCE_FP and
            source.read_bytes() == c.source and
            fp(run / 'ACTUAL_GEOMETRY_PROBE_RESULT.json') == INPUTS['probe_document'],
            'actual probe retained source/result identity differs')
    require(fp(run / 'executed-probe.py') is not None and
            (run / 'executed-probe.py').read_bytes() == git_file(INPUTS['probe_publication'], PROBE_SCRIPT),
            'actual probe executed entrypoint differs from its original publication')
    command = c.base.read_command(c.ai, run, 'serialized-whole-geometry-probe',
        c.ag.h.serialize(0, run / 'PROBE_LANE.json',
            c.ag.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(source)])))
    require(command == p['command'] and command['actual_built_modules'] == command['actual_failed_modules'] == [] and
            fp(Path(command['log'])) == {k: p['log'][k] for k in ('bytes', 'sha256')} and
            Path(command['log']).read_text() == p['compiler_output'],
            'actual probe command/log/no-build binding differs')
    before = c.ag.api.read_json(run / 'CONTEXT_BEFORE.json')
    require(before == c.ag.api.read_json(run / 'CONTEXT_AFTER.json') and
            c.ag.api.read_json(run / 'SELECTED_SCOPE.json') == c.selected,
            'actual probe before/after preserved scope differs')
    require_ai_acceptance(before['original_acceptance_read'], c.published)
    failed = failed_probe_snapshot(c)
    require(before['original_AK_failed_probe'] == failed, 'original failed AK probe tree differs')
    slot = before['geometry_slot']
    require_new_slot(slot['source'], slot['artifacts'], slot['history'], installed=False)
    suffixes = ('.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
        '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig',
        '.c', '.c.hash', '.bc', '.bc.hash', '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace')
    require(all(not os.path.lexists(source.with_suffix(ext)) for ext in suffixes),
            'no-output probe emitted an object')
    return {'path': str(run), 'tree': c.ai.readers['ag'].tree_inventory(run), 'original_AK_failed_probe': failed}


def failed_probe_snapshot(c):
    root = PROBE_ROOT / AK
    path = root / 'runs/attempt-00000/ACTUAL_GEOMETRY_PROBE_RESULT.json'
    require(fp(path) == FAILED_PROBE_FP, 'original failed AK probe result differs')
    row = c.ag.api.read_json(path)
    require(row['publication'] == AK and row['exit_code'] == 1 and row['probe_passed'] is False and
            row['preservation_passed'] is True and row['new_owner_accepted'] is False and
            row['normal_or_kernel_acceptance_claimed'] is False and
            row['source_origin'] == {'commit': AJ, 'path': SOURCE, **ORIGINAL_SOURCE_FP} and
            row['existing_project_modules_rebuilt'] == [], 'original failed AK probe status differs')
    return {'result': {'path': str(path), **FAILED_PROBE_FP},
            'full_failed_probe_tree': c.ai.readers['ag'].tree_inventory(root)}


def prepare(c):
    old = c.base.prepare_base(c.ai)
    for module, row in old.ag.manifest['project_sources'].items():
        require(raw_fp(git_file(c.commit, row['path'])) == {k: row[k] for k in ('bytes', 'sha256')},
                'new publication changed accepted source: ' + module)
    state = SimpleNamespace(old=old, ai=ai_snapshot(c, old), probe=read_probe(c))
    unchanged(c, state)
    return state


def unchanged(c, state):
    c.base.unchanged_old(c.ai, state.old)
    require(ai_snapshot(c, state.old) == state.ai and
            c.ai.readers['ag'].tree_inventory(Path(state.probe['path'])) == state.probe['tree'] and
            failed_probe_snapshot(c) == state.probe['original_AK_failed_probe'],
            'original AI source/21 artifacts/full evidence/install trees or actual probe evidence changed')


def preservation_summary(c, state):
    return {'original_AG_AE_nine_tree_360_source_160_slot_context': c.base.preservation_summary(state.old),
        'original_AI_acceptance': state.ai['acceptance']['owner'],
        'original_AI_source': state.ai['source'],
        'original_AI_21_artifacts': value_fp(state.ai['artifacts']),
        'original_AI_full_evidence_and_installation_trees': {
            path: {'entry_count': len(tree), **value_fp(tree)} for path, tree in state.ai['trees'].items()},
        'actual_probe_evidence_tree': {'path': state.probe['path'],
            'entry_count': len(state.probe['tree']), **value_fp(state.probe['tree'])},
        'original_AK_failed_probe_evidence': value_fp(state.probe['original_AK_failed_probe'])}


def owner_history():
    require(ROOT.is_dir() and ROOT.resolve() == ROOT, 'original owner root differs')
    history = []
    for folder in sorted(ROOT.iterdir()):
        if re.fullmatch('[0-9a-f]{40}', folder.name) and os.path.lexists(folder / TARGET):
            owner = folder / TARGET
            require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder and
                    owner.is_dir() and not owner.is_symlink() and owner.resolve() == owner,
                    'nonregular Geometry owner history')
            history.append(owner)
    return history


def require_new_slot(source, artifacts, history, *, installed):
    require(not history and len(artifacts) == 21 and all(row is None for row in artifacts.values()),
            'Geometry has started owner history or artifacts; inspect without recompilation')
    require(source == SOURCE_FP if installed else source in (None, ORIGINAL_SOURCE_FP, SOURCE_FP),
            'Geometry canonical source differs; only the exact reviewed AJ repair is allowed')


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
        require(worker['schema'] == 'p15_independent_geometry_source_install_v1' and
                worker['normal_or_kernel_commands_executed'] == 0 and worker['source_installed'] is True and
                worker['source_after'] == SOURCE_FP and worker['source_before'] in (None, ORIGINAL_SOURCE_FP, SOURCE_FP) and
                worker['installation_action'] == installation_action(worker['source_before']),
                'same-commit source installation terminal binding differs')
    else:
        require(worker['schema'] == 'p15_independent_geometry_acceptance_v1' and
                worker['targets'] == worker['accepted_owners'] == [TARGET] and worker['failures'] == {},
                'same-commit Geometry normal/full-owned/kernel terminal binding differs')


def installation_action(before):
    require(before in (None, ORIGINAL_SOURCE_FP, SOURCE_FP), 'unreviewed canonical source cannot be installed')
    if before is None:
        return 'EXCLUSIVE_NEW_CANONICAL_SOURCE'
    if before == ORIGINAL_SOURCE_FP:
        return 'EXACT_AJ_SOURCE_REPLACED_BY_R_RESOLUTION_REPAIR'
    return 'IDENTICAL_SOURCE_BEFORE_OWNER_START'


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
    command = c.base.read_command(c.ai, run, 'serialized-geometry-install',
        c.ag.h.serialize(0, run / 'GEOMETRY_INSTALL_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--install', '--inside-lane', str(run)]))
    require(command['actual_built_modules'] == command['actual_failed_modules'] == [],
            'source installation attempted a build')
    names = ['SOURCE_INSTALL_RESULT.json', 'WORKER_RESULT.json', 'OLD_CONTEXT_BEFORE.json',
        'OLD_CONTEXT_AFTER.json', 'GIT_BEFORE.json', 'GIT_AFTER.json', 'executed-installer.py',
        'serialized-geometry-install-command.json', 'serialized-geometry-install.log']
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


def new_spec(c, state):
    require(fp(PROJECT / SOURCE) == SOURCE_FP and (PROJECT / SOURCE).resolve() == PROJECT / SOURCE,
            'exact Geometry source must first be separately installed')
    graph = {**state.old.ag.graph, TRIMLOG: [ATLAS], TARGET: list(IMPORTS)}
    sources = {**state.old.ag.sources, TRIMLOG: c.base.SOURCE_FP['sha256'], TARGET: SOURCE_FP['sha256']}
    active = c.ag.h.closure(graph, [TARGET])
    dependencies = set(c.selected['dependency_sources'])
    require(len(graph) == len(sources) == 362 and active == dependencies | {TARGET} and len(active) == 142,
            'separate Geometry 362-known/142-active graph differs')
    pins = dependency_inventory(state.old.ag, state.old.ag_bindings, dependencies, c.g.artifact_paths)
    observed_graph, observed = c.ag.h.project_graph(PROJECT, [TARGET])
    require(observed_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in observed.items()} == {m: sources[m] for m in active},
            'installed Geometry graph differs')
    installation, installation_pins = read_installation(c, state)
    spec = SimpleNamespace(graph=graph, sources=sources, active=active, selected={TARGET}, order=[TARGET],
        dependency_pins=pins, review=state.old.ag.review,
        retained_inputs={**state.old.retained, **installation_pins},
        manifest={'project_sources': {TARGET: {'all_imports': list(IMPORTS)}}},
        input_bindings={'source_commit': c.commit, 'selected_targets': [TARGET],
            'independent_owner': c.identity, 'independent_source_installation': installation,
            'original_AG_context': value_fp(state.old.ag.baseline),
            'original_AI_context': value_fp(state.ai), 'preservation': preservation_summary(c, state)})
    spec.baseline = c.g.snapshot(c.ag, spec)
    return spec


def new_owner_state(c, spec):
    history = owner_history(); folder = ROOT / c.commit / TARGET
    require(all(path == folder for path in history), 'foreign Geometry owner history requires inspection')
    if not os.path.lexists(folder):
        require_new_slot(fp(PROJECT / SOURCE), c.g.module_artifacts(c.ag, TARGET), history, installed=True)
        existing = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
        require(existing['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT', 'fresh Geometry owner classification differs')
        return existing
    require(fp(folder / 'normal' / TARGET / 'NORMAL_PASS.json') is not None,
            'partial Geometry owner without normal receipt requires inspection')
    existing = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
    c.g.require_completed_existing_owner(c.ag, c.commit, spec, TARGET, existing)
    return existing


def accepted_public(c, spec):
    existing = c.g.existing_owner(c.ag, c.commit, spec, TARGET)
    c.g.require_completed_existing_owner(c.ag, c.commit, spec, TARGET, existing)
    binding = c.g.acceptance_binding(c.ag, c.commit, TARGET)
    require(len(binding['audits']) == 1 and len(binding['source_plus_five_outputs']) == 6 and
            len(binding['all_observed_target_artifacts']) == 21, 'Geometry single-owner receipt shape differs')
    audit = c.ag.api.read_json(Path(binding['audits'][0]['result']['path']))
    require(audit['only_standard_axioms'] is True and audit['full_owned_including_private_generated'] is True and
            type(audit['total_owned_exports']) is int and type(audit['total_public_exports']) is int and
            0 < audit['total_public_exports'] <= audit['total_owned_exports'],
            'Geometry must have actual complete full-owned/kernel/standard-axiom acceptance')
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
    executed = run / 'executed-geometry.py'
    require(worker['owner'] == owner and worker['preservation'] == preservation_summary(c, state) and
            fp(executed) == raw_fp(c.script) and executed.read_bytes() == c.script and
            c.ag.api.read_json(run / 'CONTEXT_BEFORE.json') ==
            c.ag.api.read_json(run / 'CONTEXT_AFTER.json') == spec.baseline and
            c.ag.api.read_json(run / 'GIT_BEFORE.json') == c.ag.api.read_json(run / 'GIT_AFTER.json') == state.old.git,
            'same-commit original Geometry owner/script/context/Git chain differs')
    wrapper = c.base.read_command(c.ai, run, 'serialized-geometry',
        c.ag.h.serialize(0, run / 'GEOMETRY_LANE.json',
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
        'GIT_BEFORE.json', 'GIT_AFTER.json', 'executed-geometry.py',
        'serialized-geometry-command.json', 'serialized-geometry.log',
        'final-stock-readiness-command.json', 'final-stock-readiness.log',
        TARGET + '/direct-import-stock-readiness-command.json', TARGET + '/direct-import-stock-readiness.log']
    pins = {name: {'path': str(run / name), **fp(run / name)} for name in names}
    return {'path': str(run), 'original_run_receipts': pins, 'final_stock_readiness': stock,
        'new_owner_accepted': True, 'recompiled_by_check': False}


def check(c):
    state = prepare(c); spec = new_spec(c, state)
    existing = new_owner_state(c, spec)
    result = {'schema': 'p15_independent_geometry_readonly_v1', 'identity': c.identity,
        'known_source_count': 362, 'active_source_count': 142, 'preserved_dependency_count': 141,
        'new_owner_accepted': False, 'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}
    if existing['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT':
        owner = accepted_public(c, spec)
        result.update(status='ORIGINAL_GEOMETRY_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION', owner=owner,
            accepting_run=read_completed_run(c, state, spec, owner), new_owner_accepted=True)
    else:
        require_new_attempt(ROOT / c.commit / 'runs')
        result.update(status='FRESH_INSTALLED_GEOMETRY_NOT_YET_ACCEPTED', owner=None)
    require(c.g.snapshot(c.ag, spec) == spec.baseline, 'Geometry dependency context changed during read')
    unchanged(c, state)
    result['preservation'] = preservation_summary(c, state)
    result['independent_source_installation'] = spec.input_bindings['independent_source_installation']
    return result


def worker(c, run):
    result = {'schema': 'p15_independent_geometry_acceptance_v1', 'identity': c.identity,
        'targets': [TARGET], 'accepted_owners': [], 'failures': {}, 'new_owner_accepted': False,
        'new_owner_is_outside_original_21': True, 'original_21_target_count': 21,
        'original_21_accepted_count': 18, 'whole_P1_5_complete': False}
    state = spec = None
    try:
        c.ag.d.verify_lane(c.ag.h)
        state = prepare(c); spec = new_spec(c, state)
        existing = new_owner_state(c, spec)
        require(existing['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT',
                'already accepted Geometry owner: use --check, never recompile')
        c.ag.d.save(run / 'CONTEXT_BEFORE.json', spec.baseline)
        result['direct_import_readiness'] = c.g.direct_import_readiness(c.ag, spec, TARGET, run)
        require(c.g.snapshot(c.ag, spec) == spec.baseline, 'no-build import readiness changed dependencies')
        unchanged(c, state)
        c.g.run_owner(c.ag, c.commit, ROOT / c.commit, run, TARGET, spec.graph, spec.sources)
        owner = accepted_public(c, spec)
        require(c.g.snapshot(c.ag, spec) == spec.baseline, 'Geometry owner changed its dependency context')
        unchanged(c, state)
        artifacts = c.g.module_artifacts(c.ag, TARGET)
        stock = c.ag.ops.run(run, 'final-stock-readiness',
            c.ag.h.guard(0, ['lake', '--no-build', 'build', '+' + TARGET + ':olean']), cwd=PROJECT)
        require(stock['exit_code'] == 0 and stock['actual_built_modules'] == stock['actual_failed_modules'] == [] and
                c.g.module_artifacts(c.ag, TARGET) == artifacts, 'Geometry final no-build stock changed artifacts')
        result.update(accepted_owners=[TARGET], owner=owner, final_stock_readiness=stock)
    except Exception as error:
        result['failures'][TARGET] = str(error)
    finally:
        try:
            if spec is not None:
                after = c.g.snapshot(c.ag, spec); c.ag.d.save(run / 'CONTEXT_AFTER.json', after)
                require(after == spec.baseline, 'Geometry dependencies/runtime changed')
            if state is not None:
                unchanged(c, state)
                result['preservation'] = preservation_summary(c, state)
        except Exception as error:
            result['preservation_error'] = str(error)
    c.ag.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('preservation_error')))


def dispatch(c, *, installation=False):
    """One serialized worker; preserve preparation failures after attempt allocation."""
    runs = (INSTALL_ROOT if installation else ROOT) / c.commit / 'runs'
    require_new_attempt(runs)
    run = c.ag.d.attempt(runs)
    name = 'serialized-geometry-install' if installation else 'serialized-geometry'
    lane = 'GEOMETRY_INSTALL_LANE.json' if installation else 'GEOMETRY_LANE.json'
    executed = run / ('executed-installer.py' if installation else 'executed-geometry.py')
    result_name = 'SOURCE_INSTALL_RESULT.json' if installation else 'RESULT.json'
    result = {'schema': 'p15_independent_geometry_source_install_v1' if installation
                      else 'p15_independent_geometry_acceptance_v1',
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
                re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected Geometry worker path')
        require(unique_run(run.parent) == run, 'nonunique Geometry worker attempt')
        return worker(c, run)
    state = prepare(c); spec = new_spec(c, state)
    require(new_owner_state(c, spec)['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT',
            'already accepted Geometry owner: use --check, never recompile')
    unchanged(c, state)
    return dispatch(c)


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'INDEPENDENT_GEOMETRY_HOLD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_accepted': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
