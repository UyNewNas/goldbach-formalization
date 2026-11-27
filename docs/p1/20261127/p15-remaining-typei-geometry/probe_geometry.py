#!/usr/bin/env python3
"""Typecheck the unchanged, newly selectable RemainingTypeIGeometry owner.

This is a whole-module probe without object outputs. It reuses the immutable
AI acceptance reader and the existing serializer/guard. It does not install
sources, build dependencies, grant normal/kernel acceptance, or close P1.5.
"""
from pathlib import Path
from types import ModuleType
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
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-remaining-typei-geometry-probe-v1')
AI = '6d9072f7b33332eaf5ecfff22876e0404cd6ab51'
AJ = '6d87764cbc9fce5b10a2665a458619e44d8255ae'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
PACKAGE = 'docs/p1/20261127/p15-remaining-typei-geometry/'
SCRIPT = PACKAGE + 'probe_geometry.py'
READER = 'docs/p1/20261126/p15-trimlog-accuracy/run_trimlog.py'
READER_FP = {'bytes': 36541, 'sha256': '0c6307af83c197123bd2da678bfd4ac6b76916169d6d457f83733461725b8272'}
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/TRIMLOG_AI_PUBLIC_ACCEPTANCE.json'
PUBLIC_FP = {'bytes': 18539, 'sha256': '2bb01aa28ab117933b0ec8f766245f0a9faaeb750448bb6e47536c4dbfdf18f0'}
TARGET = 'ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry'
SOURCE = 'ImbalancedChen/P1OriginalSingletonRemainingTypeIGeometry.lean'
SOURCE_FP = {'bytes': 11273, 'sha256': 'a0f9f8dd7c14158366e1247d26db649b6b66f2505f5e88b5f3472f81ff63f5f6'}
IMPORTS = ['ImbalancedChen.P1OriginalSingletonSmoothLicence',
           'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
           'ImbalancedChen.P5OriginalHBMediumChartReserves']
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


def scope(manifest):
    sources = manifest['project_sources']
    graph = {m: row['imports'] for m, row in sources.items()}
    require(len(graph) == 360 and TARGET not in graph, 'old graph/new owner scope differs')

    def closure(roots):
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

    dependencies = closure(IMPORTS)
    old_active = closure(['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                          'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'])
    require(len(dependencies) == 141 and len(old_active) == 144 and dependencies <= old_active,
            'geometry must use precisely 141 dependencies within the original AG scope')
    require(not dependencies.intersection(manifest['unaccepted_p3_dependencies']),
            'unaccepted P3 dependency entered geometry scope')
    return {'owner': TARGET, 'direct_imports': IMPORTS,
            'active_source_count_with_owner': 142, 'dependency_count': 141,
            'dependency_sources': {m: {k: sources[m][k] for k in ('path', 'bytes', 'sha256')}
                                   for m in sorted(dependencies)},
            'AG_accepted_scope_count': 144, 'subset_of_original_AG_scope': True,
            'unaccepted_P3_dependencies': []}


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
    require(source in (None, SOURCE_FP), 'existing geometry canonical source differs')
    require(len(artifacts) == 21 and all(v is None for v in artifacts.values()) and not history,
            'geometry has artifacts or started acceptance history; inspect without recompiling')


def geometry_history():
    require(OLD_ROOT.is_dir() and OLD_ROOT.resolve() == OLD_ROOT, 'old evidence root differs')
    found = []
    for folder in sorted(OLD_ROOT.iterdir()):
        if re.fullmatch('[0-9a-f]{40}', folder.name) and os.path.lexists(folder / TARGET):
            owner = folder / TARGET
            require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder
                    and owner.is_dir() and not owner.is_symlink() and owner.resolve() == owner,
                    'nonregular geometry owner history')
            found.append(str(owner))
    return found


def load_original(publication, executed):
    require(__debug__ and re.fullmatch('[0-9a-f]{40}', publication), 'exact publication commit required')
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', AJ, publication], cwd=REPO).returncode == 0,
            'probe publication must descend from the original AJ checkpoint')
    require(executed == git_file(publication, SCRIPT), 'probe entrypoint differs from its publication')
    raw = git_file(AI, READER)
    entry = OLD_ROOT / AI / 'runs/attempt-00000/executed-trimlog.py'
    require(raw_fp(raw) == READER_FP and entry.is_file() and not entry.is_symlink()
            and entry.read_bytes() == raw and git_file(publication, READER) == raw,
            'immutable original AI reader differs')
    base = ModuleType('immutable_geometry_AI_reader')
    base.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), base.__dict__)
    c = base.load(AI, raw)
    source = git_file(AJ, SOURCE)
    require(raw_fp(source) == SOURCE_FP and git_file(publication, SOURCE) == source
            and c.ag.h.imports(source) == IMPORTS, 'complete unchanged geometry source/imports differ')
    pub = git_file(AJ, PUBLIC)
    require(raw_fp(pub) == PUBLIC_FP and git_file(publication, PUBLIC) == pub,
            'original AJ public acceptance differs')
    manifest_raw = git_file(AG, base.MANIFEST)
    require(raw_fp(manifest_raw) == base.AG_MANIFEST_FP, 'original AG manifest differs')
    return base, c, source, json.loads(pub), scope(json.loads(manifest_raw))


def snapshot(base, c, published):
    report = base.check(c)
    require_original_acceptance(report, published)
    slot = {'source': base.fp(PROJECT / SOURCE),
            'artifacts': c.g.module_artifacts(c.ag, TARGET), 'history': geometry_history()}
    require_fresh_slot(**slot)
    trees = {str(path): c.readers['ag'].tree_inventory(path)
             for path in (OLD_ROOT / AI, base.INSTALL_ROOT / AI)}
    return {'original_acceptance_read': report, 'geometry_slot': slot,
            'original_AI_evidence_and_installation_trees': trees,
            'git': c.ag.d.original_git_state(REPO)}


def require_probe_output(base, probe, outcome):
    require(base.fp(probe) == SOURCE_FP and all(not os.path.lexists(probe.with_suffix(ext)) for ext in SUFFIXES),
            'whole probe source changed or emitted an object')
    require(outcome['actual_built_modules'] == outcome['actual_failed_modules'] == [],
            'probe rebuilt a project module')


def run(publication, executed):
    base, c, source, published, selected = load_original(publication, executed)
    before = snapshot(base, c, published)
    parent = PROBE_ROOT / publication / 'runs'
    require(parent.resolve() == parent, 'probe evidence parent traverses a symlink')
    require(not parent.exists() or (parent.is_dir() and not any(parent.iterdir())),
            'this publication already has probe history; inspect its original result instead of repeating it')
    run_dir = c.ag.d.attempt(parent)
    probe = run_dir / 'OriginalSingletonRemainingTypeIGeometryProbe.lean'
    result = {'schema': 'p15_remaining_typei_geometry_whole_no_output_probe_v1',
              'publication': publication, 'source_origin': {'commit': AJ, 'path': SOURCE, **SOURCE_FP},
              'original_AI_acceptance_commit': AI, 'original_AG_acceptance_commit': AG,
              'source': {'path': str(probe), **SOURCE_FP}, 'scope': selected,
              'normal_or_kernel_acceptance_claimed': False, 'new_owner_accepted': False,
              'whole_P1_5_complete': False, 'preservation_passed': False,
              'typecheck_command_completed': False, 'exit_code': 3}
    try:
        c.ag.d.write_frozen(probe, source)
        c.ag.d.write_frozen(run_dir / 'executed-probe.py', executed)
        c.ag.d.save(run_dir / 'CONTEXT_BEFORE.json', before)
        c.ag.d.save(run_dir / 'SELECTED_SCOPE.json', selected)
        require_probe_output(base, probe, {'actual_built_modules': [], 'actual_failed_modules': []})
        command = c.ag.h.serialize(0, run_dir / 'PROBE_LANE.json',
            c.ag.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
        outcome = c.ag.ops.run(run_dir, 'serialized-whole-geometry-probe', command, cwd=PROJECT, relay=False)
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
            after = snapshot(base, c, published)
            c.ag.d.save(run_dir / 'CONTEXT_AFTER.json', after)
            require(after == before, 'prior source/object/evidence/runtime/Git or geometry slot changed')
            require_probe_output(base, probe, {'actual_built_modules': [], 'actual_failed_modules': []})
            result['preservation_passed'] = True
        except Exception as error:
            result['preservation_error'] = str(error)
    success = (result['exit_code'] == 0 and result['typecheck_command_completed']
               and result['preservation_passed'] and not result.get('probe_error')
               and not result.get('preservation_error'))
    result['probe_passed'] = success
    path = run_dir / 'ACTUAL_GEOMETRY_PROBE_RESULT.json'
    c.ag.d.save(path, result)
    print(json.dumps({'result_path': str(path), **result}, sort_keys=True), flush=True)
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
        print(json.dumps({'status': 'GEOMETRY_PROBE_HELD', 'error_type': type(error).__name__,
                          'error': str(error), 'new_owner_accepted': False,
                          'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
