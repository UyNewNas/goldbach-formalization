#!/usr/bin/env python3
"""Typecheck the minimally namespace-repaired RemainingTypeIGeometry owner.

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
AK = 'd4f88a20262af7d54ed0e6e58dfc533496c595e3'
AL = '13981b6d4b60ed3d4d36b74ff2522fdce7811de0'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
PACKAGE = 'docs/p1/20261127/p15-remaining-typei-geometry/'
SCRIPT = PACKAGE + 'probe_geometry.py'
READER = 'docs/p1/20261126/p15-trimlog-accuracy/run_trimlog.py'
READER_FP = {'bytes': 36541, 'sha256': '0c6307af83c197123bd2da678bfd4ac6b76916169d6d457f83733461725b8272'}
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/TRIMLOG_AI_PUBLIC_ACCEPTANCE.json'
PUBLIC_FP = {'bytes': 18539, 'sha256': '2bb01aa28ab117933b0ec8f766245f0a9faaeb750448bb6e47536c4dbfdf18f0'}
TARGET = 'ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry'
SOURCE = 'ImbalancedChen/P1OriginalSingletonRemainingTypeIGeometry.lean'
ORIGINAL_SOURCE_FP = {'bytes': 11273, 'sha256': 'a0f9f8dd7c14158366e1247d26db649b6b66f2505f5e88b5f3472f81ff63f5f6'}
PREVIOUS_SOURCE_FP = {'bytes': 11337, 'sha256': '2b982d9bedc546b5ef5f01cc64b0d6401ac5b2a830585e6998924dba74f0d91f'}
SOURCE_FP = {'bytes': 11341, 'sha256': '2c3963d7847dc99aa809474b9b3ae387d0e75b67e37743682d3d9e53202dfa77'}
SECOND_FAILED_PROBE_FP = {'bytes': 39001, 'sha256': '8a484f37d462a8c22aefa2adba2d552263f980c0d271e24e5fcfb0cf6188ed54'}
FAILED_PROBE_FP = {'bytes': 42835, 'sha256': 'bbdf61c6f78ae5b34b541fd3340bab2439d1aa57307224a3c8e299d14c396b0b'}
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
    require(source in (None, ORIGINAL_SOURCE_FP, SOURCE_FP), 'existing geometry canonical source differs')
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


def require_corrected_source(original, source):
    anchor = b'open P5CanonicalTentNarrowSingletonTransfer (actualLicence)\n'
    notation = b'\nlocal notation "R" => P5Z.ExactOriginalSmoothDyadicPartition.R\n'
    require(raw_fp(original) == ORIGINAL_SOURCE_FP and original.count(anchor) == 1
            and raw_fp(source) == SOURCE_FP
            and original.count(b'(R := R cj)') == 1
            and source == original.replace(anchor, anchor + notation).replace(
                b'(R := R cj)', '(«R» := R cj)'.encode()),
            'geometry source is not the exact notation and escaped-parameter repair')


def failed_probe_snapshot(base, c):
    root = PROBE_ROOT / AK
    path = root / 'runs/attempt-00000/ACTUAL_GEOMETRY_PROBE_RESULT.json'
    require(base.fp(path) == FAILED_PROBE_FP, 'original AK failed probe receipt differs')
    data = json.loads(path.read_bytes())
    require(data['publication'] == AK and data['exit_code'] == 1
            and data['probe_passed'] is False and data['preservation_passed'] is True
            and data['new_owner_accepted'] is False
            and data['normal_or_kernel_acceptance_claimed'] is False
            and data['source_origin'] == {'commit': AJ, 'path': SOURCE, **ORIGINAL_SOURCE_FP}
            and data['existing_project_modules_rebuilt'] == [],
            'original AK failed probe identity or result differs')
    return {'result': {'path': str(path), **FAILED_PROBE_FP},
            'full_failed_probe_tree': c.readers['ag'].tree_inventory(root)}


def second_failed_probe_snapshot(base, c):
    root = PROBE_ROOT / AL
    path = root / 'runs/attempt-00000/ACTUAL_GEOMETRY_PROBE_RESULT.json'
    require(base.fp(path) == SECOND_FAILED_PROBE_FP, 'original AL failed probe receipt differs')
    data = json.loads(path.read_bytes())
    require(data['publication'] == AL and data['exit_code'] == 1
            and data['probe_passed'] is False and data['preservation_passed'] is True
            and data['new_owner_accepted'] is False
            and data['normal_or_kernel_acceptance_claimed'] is False
            and data['source_origin'] == {'commit': AL, 'path': SOURCE, **PREVIOUS_SOURCE_FP}
            and data['original_failed_probe'] == {'publication': AK, **FAILED_PROBE_FP}
            and data['existing_project_modules_rebuilt'] == [],
            'original AL failed probe identity or result differs')
    return {'result': {'path': str(path), **SECOND_FAILED_PROBE_FP},
            'full_failed_probe_tree': c.readers['ag'].tree_inventory(root)}


def load_original(publication, executed):
    require(__debug__ and re.fullmatch('[0-9a-f]{40}', publication), 'exact publication commit required')
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', AL, publication], cwd=REPO).returncode == 0,
            'corrected probe publication must descend from the actual AL failed probe publication')
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
    original = git_file(AJ, SOURCE)
    source = git_file(publication, SOURCE)
    require_corrected_source(original, source)
    require(c.ag.h.imports(source) == IMPORTS, 'geometry imports differ')
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
            'original_AK_failed_probe': failed_probe_snapshot(base, c),
            'original_AL_failed_probe': second_failed_probe_snapshot(base, c),
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
    result = {'schema': 'p15_remaining_typei_geometry_whole_no_output_probe_v3',
              'publication': publication, 'source_origin': {'commit': publication, 'path': SOURCE, **SOURCE_FP},
              'original_geometry_source': {'commit': AJ, 'path': SOURCE, **ORIGINAL_SOURCE_FP},
              'repair': 'dyadic_R_notation_and_escaped_original_parameter',
              'original_failed_probe': {'publication': AK, **FAILED_PROBE_FP},
              'second_failed_probe': {'publication': AL, **SECOND_FAILED_PROBE_FP},
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
