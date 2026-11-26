#!/usr/bin/env python3
"""SOURCE ONLY: verify only the cell00 typed header/facet-index owner.

Minimal adaptation of the published remaining-arithmetic runner. Reuse its
accepted complete external context and unchanged seven required project
objects; no existing owner is compiled, replayed or audited again. Compile,
independently replay and fully audit only TypedSourceFacts. OriginalSourceFacts
is deliberately not a target. Pass the exact source publication40 argument.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import traceback
import types

ROOT = Path('/workspace/p25-q96-20261125')
PRIOR = ROOT / '.lake/diagnostic/p25-cell00-row00-arithmetic-attempt001'
OUT = ROOT / '.lake/diagnostic/p25-cell00-typed-source-facts-attempt001'
REUSE = ROOT / '.lake/diagnostic/p25-cell00-remaining-arithmetic-attempt001'
REUSE_PUBLICATION = '5cc2b181f51be2f20ce316256fe2cdf3e691ca69'
REUSE_RESULT_SHA = '1e48fc2e2a45b2e4247ab08597586dae6c8cac3cd9a05788e465b5175d262f7c'
REUSE_RUNNER = 'docs/verification/20261126-p2-5-continuation/run_cell00_remaining_arithmetic_cloud.py'
REUSE_RUNNER_SHA = '17b4b2193968c061a8bbb31ac0e3043c8cbf4eb2b22ee010a0359a57c8de4918'
PRIOR_PUBLICATION = '8fa1d8c84f8c465da8f8fd00bfce1410e1807ae3'
PRIOR_RESULT_SHA = '7094b47bfe97aaa8236cda1309e805440a3b6a1b48b5d4083fa6ba75cd2e8265'
PRIOR_OBJECT_SHA = '7c8eb471baa5194d264a17adecf198beb5e3d6b46ab3c548ba9d1c9946756d51'
PRIOR_RUNNER = 'docs/verification/20261126-p2-5-continuation/run_cell00_row00_arithmetic_cloud.py'
PRIOR_RUNNER_SHA = '51155a110a8a4519a1ece049425e833b1edde31d7754347fdbe25a018dcc56d2'
RUNNER_REL = 'docs/verification/20261126-p2-5-continuation/run_cell00_typed_source_facts_cloud.py'
PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-source-facts')
MANIFEST_SHA = 'd6b7129968e3d2651f2e5a6cceb75a05d2b7732380a5e827fa1db828181907e0'
SELECTION_SHA = '963c536386cb0b93982fbccbc47a4625bbb03ae23658048d1913902f542b4b04'
FILES_SHA = '87825d586c17e09493996e5c267a7e1c45e1573988f9c3061e95487123ba0f35'
ROW00 = 'ImbalancedChen.P2Saving16Cell00Row00Arithmetic'
ROWS = ['ImbalancedChen.P2Saving16Cell00Row%02dArithmetic' % i for i in range(1, 8)]
COMPOSITION = 'ImbalancedChen.P2Saving16Cell00AllRowsArithmetic'
TARGET = 'ImbalancedChen.P2Saving16Cell00TypedSourceFacts'
TARGETS = [TARGET]
ORIGINAL_TRANSPORT = 'ImbalancedChen.P2Saving16Cell00OriginalSourceFacts'
TARGET_SOURCE_SHA = '5afdaa38a0fd572d8946672d245b884890f28e87b9644b47d2b16ae397b565a0'
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def record_file(path):
    path = Path(path)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest(path)}


def now():
    return datetime.now(timezone.utc).isoformat()


def git(*args, cwd=ROOT):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false',
                                    *args], cwd=cwd, text=True, timeout=120).strip()


def imports(log):
    values = [json.loads(line.removeprefix('P0_QUEUE_IMPORTS '))
              for line in Path(log).read_text().splitlines() if line.startswith('P0_QUEUE_IMPORTS ')]
    require(len(values) == 1 and len(values[0]) == len(set(values[0])), 'Missing/duplicate audited imports')
    return values[0]


def main():
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]), 'Pass one exact publication40')
    require(sys.flags.optimize == 0, 'Do not run with Python -O')
    publication = sys.argv[1]
    require(ROOT.is_dir() and not OUT.exists(), 'Missing checkout or existing attempt; preserve prior attempts')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked checkout is dirty')
    OUT.mkdir()
    state = {
        'schema': 'p25-cell00-typed-source-facts-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600, 'module_order': TARGETS,
        'modules': {}, 'dependency_objects': {}, 'dependency_receipts': {}, 'dependency_modules_compiled': [],
        'reused_owner_receipts': {}, 'private_records_written': [],
        'accepted_dependency_gates_rerun': [], 'original_cell00_sha256': INPUT_SHA,
        'host_correctness_credit': False, 'typed_headers_proved': False,
        'typed_facet_indices_proved': False, 'original_transport_owner_compiled': False,
        'original_archive_binding_proved_by_this_run': False,
        'original_archive_headers_proved': False, 'original_archive_facet_indices_proved': False,
        'source_cell_membership_proved': False, 'all96_vertex_inequalities_proved': False,
        'positive_normal_balance_proved': False, 'facet_incidence_proved': False,
        'pulling_ownership_proved': False, 'all_cell_finite_guards_proved': False,
        'Q96_proved': False, 'P2_5_proved': False,
    }
    frozen = {}
    external_entries = []
    expected_external = set()
    providers = []

    def write():
        temporary = OUT / 'RESULT.tmp'
        temporary.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
        temporary.replace(OUT / 'RESULT.json')

    def bind(path, expected=None):
        path = Path(path)
        actual = digest(path)
        require(expected is None or actual == expected, 'Artifact hash mismatch: ' + str(path))
        require(str(path) not in frozen or frozen[str(path)] == actual, 'Artifact changed: ' + str(path))
        frozen[str(path)] = actual
        return path

    def artifact(row, expected=None):
        path = bind(row['path'], expected or row['sha256'])
        require(path.stat().st_size == row['bytes'] and digest(path) == row['sha256'], 'Artifact record mismatch')
        return path

    def check_frozen():
        require(all(digest(path) == value for path, value in frozen.items()), 'Frozen proof inputs changed')

    def external_resolutions():
        for row in external_entries:
            relative = row['module'].replace('.', '/') + '.olean'
            found = [root / relative for root in providers if (root / relative).is_file()]
            require([str(path) for path in found] == [row['object']['path']],
                    'External import provider changed: ' + row['module'])
            companions = [str(found[0]) + suffix for suffix in ['.private', '.server']
                          if Path(str(found[0]) + suffix).is_file()]
            require(companions == [entry['path'] for entry in row['companions']],
                    'External companion inventory changed: ' + row['module'])

    def context_check():
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Source publication changed')
        require(git('rev-parse', 'HEAD', cwd=Path(prior['runtime']['mathlib_path'])) == MATHLIB_PIN,
                'Mathlib source pin changed')
        for row in prior['fastdet_capsule']['P3_package_pins'].values():
            require(git('rev-parse', 'HEAD', cwd=Path(row['path'])) == row['git_commit'], 'External package pin changed')
        external_resolutions()
        check_frozen()

    def validate_owner(container, receipt_path, module, expected_object=None):
        owner = container['modules'][module]
        require(owner['module'] == module and owner['accepted'] is True and
                owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', 'Owner is not accepted: ' + module)
        spec = helper.SOURCES[module]
        origin = owner['source_origin']
        require(origin == {'commit': container['publication_commit'], 'path': spec['path'],
                           'sha256': spec['source_sha256']}, 'Original source origin changed: ' + module)
        source = artifact(owner['source_copy'], spec['source_sha256'])
        require(source.read_bytes() == subprocess.check_output(['git', 'show', origin['commit'] + ':' + origin['path']],
                                                               cwd=ROOT, timeout=120), 'Accepted source differs from publication')
        obj = artifact(owner['object'], expected_object)
        aud = artifact(owner['audit_source'])
        require(aud.read_text() == audit_template.replace(helper.PAYLOAD, module), 'Complete-owned audit template changed')
        wanted = {
            'normal': [str(LEAN), *FLAGS, '--root=' + container['isolated_source_root'], '-o', str(obj), str(source)],
            'replay': [str(CHECKER), '--verbose', module],
            'audit': [str(LEAN), *FLAGS, '--root=' + str(aud.parent), str(aud)],
        }
        require(set(owner['stages']) == set(wanted), 'Accepted three-stage inventory differs')
        for name, command in wanted.items():
            stage = owner['stages'][name]
            require(stage['status'] == 'PASSED' and stage['exit_code'] == 0 and not stage['timed_out'] and
                    stage['command'] == command, 'Accepted strict stage differs: ' + name)
            log = bind(stage['log'], stage['log_sha256'])
            require(log.stat().st_size == stage['log_bytes'], 'Stage log is incomplete')
        declarations, inventory, project = helper.read_audit(Path(owner['stages']['audit']['log']), module)
        require(declarations == owner['owned_declarations'] and len(declarations) == owner['owned_count'] and
                json.loads(artifact(owner['declarations']).read_text()) == declarations and
                json.loads(artifact(owner['inventory']).read_text()) == inventory and
                owner['actual_project_closure'] == project and
                owner['required_owned_names'] == spec['public_names'] and
                set(spec['public_names']) <= {row['name'] for row in declarations}, 'Complete owner inventory differs')
        artifact(record_file(receipt_path))
        return owner, declarations, inventory

    def copy_dependency(module, source, expected):
        require(module in helper.SOURCES and module not in TARGETS and module not in state['dependency_objects'],
                'Unknown, duplicate, or target dependency')
        source = bind(source, expected)
        destination = lib / (module.replace('.', '/') + '.olean')
        require(not destination.exists(), 'Dependency destination already exists')
        shutil.copyfile(source, destination)
        bind(destination, expected)
        companions = []
        for suffix in ['.private', '.server']:
            companion = Path(str(source) + suffix)
            if companion.exists():
                require(str(companion) in prior['frozen_inputs'], 'Unbound historical project companion')
                bind(companion, prior['frozen_inputs'][str(companion)])
                copied = Path(str(destination) + suffix)
                shutil.copyfile(companion, copied)
                bind(copied, frozen[str(companion)])
                companions.append(record_file(copied))
        state['dependency_objects'][module] = {
            'path': str(source), 'isolated_path': str(destination), 'sha256': expected,
            'source_sha256': helper.SOURCES[module]['source_sha256'], 'companions': companions,
            'accepted_prior_receipt': record_file(prior_path),
        }

    def run_stage(owner, label, command, log):
        module = owner['module']
        require(module == TARGET and label in ('normal', 'replay', 'audit'),
                'Only the new TypedSourceFacts owner may receive any Lean/checker stage')
        context_check()
        started = time.monotonic()
        stage = {'command': command, 'status': 'RUNNING', 'started_utc': now(), 'log': str(log)}
        owner['stages'][label] = stage
        write()
        print('P25_TYPED_SOURCE_FACTS_STAGE_START', module, label, flush=True)
        with log.open('wb') as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            try:
                code = process.wait(timeout=600)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=30)
                code = 124
        stage.update(status='PASSED' if code == 0 else 'FAILED', exit_code=code, timed_out=timed_out,
                     seconds=round(time.monotonic() - started, 3), ended_utc=now(),
                     log_sha256=digest(log), log_bytes=log.stat().st_size)
        write()
        print('P25_TYPED_SOURCE_FACTS_STAGE_RESULT', module, label, json.dumps({k: stage[k] for k in
              ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}), flush=True)
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=module, failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 2000))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(module + ' ' + label + ' failed with exit ' + str(code))
        context_check()

    write()
    try:
        prior_path = bind(PRIOR / 'RESULT.json', PRIOR_RESULT_SHA)
        prior = json.loads(prior_path.read_text())
        require(prior['schema'] == 'p25-cell00-row00-arithmetic-strict-v1' and prior['accepted'] is True and
                prior['status'] == 'TYPED_PAYLOAD_ROW00_ARITHMETIC_ACCEPTED' and
                prior['publication_commit'] == PRIOR_PUBLICATION and prior['module_order'] == [ROW00] and
                set(prior['modules']) == {ROW00} and prior['dependency_modules_compiled'] == [] and
                prior['private_records_written'] == [] and prior['fastdet_recompiled_on_P3'] is False and
                prior['row00_typed_simplex_valid_proved'] is True and prior['strict_flags'] == FLAGS and
                prior['original_cell00_sha256'] == INPUT_SHA and prior['P2_5_proved'] is False,
                'Exact accepted row00 aggregate is required')
        artifact(prior['runner'], PRIOR_RUNNER_SHA)
        state['prior_row00_receipt'] = record_file(prior_path)
        require(git('rev-parse', 'HEAD') in {REUSE_PUBLICATION, publication}, 'Unexpected current P3 publication')
        if git('rev-parse', 'HEAD') != publication:
            with (OUT / 'PUBLICATION.log').open('wb') as stream:
                subprocess.run(['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false', 'fetch', '--no-tags',
                                'origin', publication], cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                               timeout=120, check=True)
                subprocess.run(['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false', 'checkout', '--detach',
                                publication], cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                               timeout=120, check=True)
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Selected publication is not clean')
        require(Path(__file__).read_bytes() == subprocess.check_output(['git', 'show', publication + ':' + RUNNER_REL],
                                                                       cwd=ROOT, timeout=120), 'Executed runner is not published')
        bind(Path(__file__).resolve())
        prior_runner = bind(ROOT / PRIOR_RUNNER, PRIOR_RUNNER_SHA)
        require(prior_runner.read_bytes() == subprocess.check_output(['git', 'show', PRIOR_PUBLICATION + ':' + PRIOR_RUNNER],
                                                                     cwd=ROOT, timeout=120), 'Historical runner changed')
        helper = types.ModuleType('p25_frozen_row00_audit_helpers')
        helper.__file__ = str(prior_runner)
        exec(compile(prior_runner.read_bytes(), str(prior_runner), 'exec'), helper.__dict__)
        require(helper.ROOT == ROOT and helper.OUT == PRIOR and helper.TARGET == ROW00 and
                helper.FLAGS == FLAGS and helper.ALLOWED_AXIOMS == ALLOWED_AXIOMS, 'Historical helper constants differ')
        for path, expected in prior['frozen_inputs'].items():
            bind(path, expected)
        state['prior_frozen_input_count'] = len(prior['frozen_inputs'])
        manifest_path = bind(ROOT / PACKAGE / 'MANIFEST.json', MANIFEST_SHA)
        selection_path = bind(ROOT / PACKAGE / 'SOURCE_SELECTION.json', SELECTION_SHA)
        files_path = bind(ROOT / PACKAGE / 'FILES.json', FILES_SHA)
        manifest = json.loads(manifest_path.read_text())
        selection = json.loads(selection_path.read_text())
        require(manifest['schema'] == 'p25-cell00-source-facts-source-only-v1' and
                selection['schema'] == 'p25-cell00-source-facts-source-selection-v1' and
                manifest['new_sources'] == selection['new_owners'] and
                [row['module'] for row in selection['new_owners']] == [TARGET, ORIGINAL_TRANSPORT] and
                manifest['scope']['new_public_theorem_commands'] == 4 and
                selection['pending_field_source_is_not_selected'] is True and
                selection['transitive_object_selection_complete'] is False,
                'Frozen candidate selection differs; only its typed owner may be selected')
        for row in json.loads(files_path.read_text())['files']:
            bind(ROOT / row['path'], row['sha256'])
        original_graph = {}
        for module, source_spec in helper.SOURCES.items():
            spec = dict(source_spec)
            source = bind(ROOT / spec['path'], spec['source_sha256'])
            public = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)', source.read_text(), re.M)
            namespace = spec.get('public_namespace')
            spec['public_names'] = [namespace + '.' + name for name in public] if namespace else []
            original_graph[module] = spec
        require(prior['source_graph'] == original_graph and len(original_graph) == 9,
                'Accepted row00 source graph differs from the pinned helper')
        helper.SOURCES = dict(original_graph)
        for module, spec in original_graph.items():
            source = bind(ROOT / spec['path'], spec['source_sha256'])
            require(source.read_bytes() == subprocess.check_output(['git', 'show', publication + ':' + spec['path']],
                                                                   cwd=ROOT, timeout=120),
                    'Accepted dependency source differs from selected publication: ' + module)
            actual_imports = [name for line in re.findall(r'^import\s+([^\n]+)$', source.read_text(), re.M)
                              for name in line.split() if name.startswith('ImbalancedChen.')]
            require(actual_imports == spec['project_imports'], 'Project import graph differs: ' + module)
        selected = selection['new_owners'][0]
        require(selected['module'] == TARGET and selected['sha256'] == TARGET_SOURCE_SHA and
                selected['path'] == str(PACKAGE/'ImbalancedChen/P2Saving16Cell00TypedSourceFacts.lean') and
                selected['public_source_declarations'] == ['cell00_headers', 'cell00_facet_indices'] and
                selected['imports'] == ['ImbalancedChen.P2OriginalSaving16FiniteCore',
                                        'ImbalancedChen.P2Saving16Cell00StoredFloors'],
                'Typed source candidate identity differs')
        source = bind(ROOT / selected['path'], TARGET_SOURCE_SHA)
        require(source.stat().st_size == selected['bytes'] and
                source.read_bytes() == subprocess.check_output(['git', 'show', publication + ':' + selected['path']],
                                                               cwd=ROOT, timeout=120),
                'Typed source is not the exact published candidate')
        actual_imports = re.findall(r'^import\s+(\S+)\s*$', source.read_text(), re.M)
        public = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)',
                            source.read_text(), re.M)
        require(actual_imports == selected['imports'] and public == selected['public_source_declarations'],
                'Typed owner public names or imports differ')
        helper.SOURCES[TARGET] = {'path': selected['path'], 'source_sha256': TARGET_SOURCE_SHA,
                                  'project_imports': selected['imports'], 'public_namespace': TARGET,
                                  'public_names': [TARGET + '.' + name for name in public]}
        required_dependencies = helper.project_closure(TARGET) - {TARGET}
        require(required_dependencies == set(helper.KNOWN_OBJECTS) and len(required_dependencies) == 7,
                'The exact seven accepted dependencies are required')
        state.update(source_selection=record_file(selection_path), source_manifest=record_file(manifest_path),
                     expected_project_imports_by_owner={TARGET: sorted(helper.project_closure(TARGET))},
                     omitted_source_only_owner=ORIGINAL_TRANSPORT)
        audit_template_path = artifact(prior['audit_template'])
        audit_template = audit_template_path.read_text()
        state['audit_template'] = record_file(audit_template_path)
        row00_owner, row00_declarations, row00_inventory = validate_owner(prior, prior_path, ROW00, PRIOR_OBJECT_SHA)
        require(row00_owner['owned_count'] == 21, 'Row00 complete inventory count differs')
        state['reused_owner_receipts'][ROW00] = json.loads(json.dumps(row00_owner))
        expected_external = {name for name in imports(row00_owner['stages']['audit']['log'])
                             if not name.startswith('ImbalancedChen.')}
        require(len(expected_external) == 5312, 'Exact row00 external import closure differs')

        src, lib, audit = OUT / 'src', OUT / 'lib', OUT / 'audit'
        for directory in [src / 'ImbalancedChen', lib / 'ImbalancedChen', audit]:
            directory.mkdir(parents=True)
        tails = prior['approved_LEAN_PATH'].split(':')[1:]
        require(prior['approved_LEAN_PATH'].split(':')[0] == prior['isolated_library'] and tails and
                len(tails) == len(set(tails)) and all(Path(p).is_dir() and
                Path(p).resolve().is_relative_to(Path('/mathlib').resolve()) and
                not (Path(p) / 'ImbalancedChen').exists() for p in tails), 'Unexpected external/project fallback path')
        for name, binary in [('lean', LEAN), ('leanchecker', CHECKER)]:
            require(artifact(prior['runtime'][name]) == binary, 'Runtime binary identity differs')
        require(prior['runtime']['mathlib_pin'] == MATHLIB_PIN, 'Mathlib pin differs')
        state['runtime'] = prior['runtime']
        env = dict(os.environ)
        env.pop('LEAN_SRC_PATH', None)
        env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
        env['LEAN_PATH'] = ':'.join([str(lib), *tails])
        env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')
        state.update(approved_LEAN_PATH=env['LEAN_PATH'], isolated_library=str(lib), isolated_source_root=str(src))
        require(set(prior['dependency_objects']) == set(original_graph) - {ROW00} and
                set(prior['dependency_receipts']) == set(original_graph) - {ROW00}, 'Prior dependency inventory differs')
        for module in sorted(required_dependencies):
            row = prior['dependency_objects'][module]
            require(row['sha256'] == helper.KNOWN_OBJECTS[module], 'Accepted dependency object differs')
            require(row['source_sha256'] == helper.SOURCES[module]['source_sha256'], 'Accepted dependency source differs')
            bind(row['path'], row['sha256'])
            bind(row['isolated_path'], row['sha256'])
            artifact(prior['dependency_receipts'][module])
            copy_dependency(module, row['isolated_path'], row['sha256'])
            state['dependency_receipts'][module] = json.loads(json.dumps(prior['dependency_receipts'][module]))
        require(set(state['dependency_objects']) == required_dependencies and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 7,
                'Fresh library must contain only the seven accepted dependencies')

        # Reuse the complete context that the published remaining-arithmetic
        # attempt has already verified. Existing owners receive no new Lean or
        # checker invocation; their source/object/receipt origins remain intact.
        reuse_path = bind(REUSE/'RESULT.json', REUSE_RESULT_SHA)
        reuse_context = json.loads(reuse_path.read_text())
        require(reuse_context['schema'] == 'p25-cell00-remaining-arithmetic-strict-v1' and
                reuse_context['status'] == 'CELL00_ALL_EIGHT_TYPED_ARITHMETIC_ACCEPTED' and
                reuse_context['accepted'] is True and reuse_context['publication_commit'] == REUSE_PUBLICATION and
                reuse_context['module_order'] == ROWS + [COMPOSITION] and
                set(reuse_context['modules']) == set(ROWS + [COMPOSITION]) and
                all(owner['accepted'] is True for owner in reuse_context['modules'].values()) and
                reuse_context['dependency_modules_compiled'] == [] and reuse_context['private_records_written'] == [] and
                reuse_context['row00_normal_recompiled'] is False and
                reuse_context['complete_external_after_matches_before'] is True and
                reuse_context['runtime'] == prior['runtime'] and reuse_context['strict_flags'] == FLAGS and
                reuse_context['original_cell00_sha256'] == INPUT_SHA and
                reuse_context['P2_5_proved'] is False,
                'The exact accepted complete-context receipt is required')
        artifact(reuse_context['runner'], REUSE_RUNNER_SHA)
        require((ROOT/REUSE_RUNNER).read_bytes() == subprocess.check_output(
                    ['git', 'show', REUSE_PUBLICATION + ':' + REUSE_RUNNER], cwd=ROOT, timeout=120) and
                digest(ROOT/REUSE_RUNNER) == REUSE_RUNNER_SHA,
                'The published complete-context runner differs')
        bind(ROOT/REUSE_RUNNER, REUSE_RUNNER_SHA)
        for path, expected in reuse_context['frozen_inputs'].items():
            bind(path, expected)
        require(reuse_context['reused_owner_receipts'][ROW00] == row00_owner,
                'The original row00 owner receipt was changed by its context reuse')
        reuse = reuse_context['row00_additional_reuse_validation']
        require(reuse['module'] == ROW00 and reuse['accepted'] is True and
                reuse['status'] == 'REPLAY_COMPLETE_OWNED_REUSE_VALIDATED' and
                reuse['normal_recompiled'] is False and reuse['owned_count'] == 21 and
                reuse['source_origin'] == row00_owner['source_origin'] and
                reuse['source_copy'] == row00_owner['source_copy'] and
                reuse['original_owner_receipt'] == record_file(prior_path),
                'Previously accepted row00 context validation differs')
        artifact(reuse['object'], PRIOR_OBJECT_SHA)
        reuse_audit = artifact(reuse['audit_source'])
        require(reuse_audit.read_text() == audit_template.replace(helper.PAYLOAD, ROW00),
                'Previously accepted complete audit template differs')
        wanted_reuse_stages = {
            'replay': [str(CHECKER), '--verbose', ROW00],
            'audit': [str(LEAN), *FLAGS, '--root=' + str(reuse_audit.parent), str(reuse_audit)],
        }
        require(set(reuse['stages']) == set(wanted_reuse_stages), 'Unexpected previous reuse stages')
        for label, command in wanted_reuse_stages.items():
            stage = reuse['stages'][label]
            require(stage['status'] == 'PASSED' and stage['exit_code'] == 0 and not stage['timed_out'] and
                    stage['command'] == command, 'Previous context gate differs: ' + label)
            log = bind(stage['log'], stage['log_sha256'])
            require(log.stat().st_size == stage['log_bytes'], 'Previous context gate log is incomplete')
        declarations, inventory, project = helper.read_audit(Path(reuse['stages']['audit']['log']), ROW00)
        require(declarations == row00_declarations == reuse['owned_declarations'] and
                inventory == row00_inventory == reuse['inventory'] and
                project == row00_owner['actual_project_closure'] == reuse['actual_project_closure'] and
                {m for m in imports(reuse['stages']['audit']['log']) if not m.startswith('ImbalancedChen.')} == expected_external,
                'Previously validated complete-owned declarations/imports differ')
        state['reused_complete_context_receipt'] = record_file(reuse_path)
        state['reused_row00_context_validation'] = json.loads(json.dumps(reuse))
        for module in sorted(required_dependencies):
            require(reuse_context['source_graph'][module] == original_graph[module] and
                    reuse_context['dependency_receipts'][module] == prior['dependency_receipts'][module] and
                    reuse_context['dependency_objects'][module]['sha256'] == helper.KNOWN_OBJECTS[module] and
                    reuse_context['dependency_objects'][module]['source_sha256'] == original_graph[module]['source_sha256'],
                    'Accepted dependency provenance changed between contexts: ' + module)
            artifact({'path': reuse_context['dependency_objects'][module]['isolated_path'],
                      'sha256': helper.KNOWN_OBJECTS[module],
                      'bytes': Path(prior['dependency_objects'][module]['isolated_path']).stat().st_size})
        helper.SOURCES = {m: spec for m, spec in helper.SOURCES.items() if m in required_dependencies | {TARGET}}
        require(set(helper.SOURCES) == helper.project_closure(TARGET) and len(helper.SOURCES) == 8,
                'The actual selected closure must contain seven dependencies and one new owner')
        state['source_graph'] = helper.SOURCES

        providers = [LEAN.parent.parent / 'lib/lean', *map(Path, tails)]
        require(len(providers) == len(set(providers)) and all(p.is_dir() and not (p/'ImbalancedChen').exists() for p in providers),
                'External provider roots are missing/repeated or shadow project objects')
        accepted_snapshot_path = artifact(reuse_context['complete_external_before'])
        accepted_snapshot = json.loads(accepted_snapshot_path.read_text())
        require(reuse['complete_external_before'] == reuse_context['complete_external_before'] and
                accepted_snapshot['schema'] == 'p25-complete-current-external-snapshot-v1' and
                accepted_snapshot['provider_roots'] == list(map(str, providers)) and
                accepted_snapshot['module_count'] == len(accepted_snapshot['entries']) == len(expected_external) == 5312 and
                {row['module'] for row in accepted_snapshot['entries']} == expected_external and
                len({row['module'] for row in accepted_snapshot['entries']}) == len(expected_external),
                'Accepted complete external snapshot differs')
        snapshot_start = now()
        for row in accepted_snapshot['entries']:
            module = row['module']
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module), 'Invalid audited module name')
            relative = module.replace('.', '/') + '.olean'
            found = [root / relative for root in providers if (root / relative).is_file()]
            require(len(found) == 1 and str(found[0]) == row['object']['path'], 'Missing/shadowed external module: ' + module)
            path = artifact(row['object'])
            companions = []
            for suffix in ['.private', '.server']:
                companion = Path(str(path) + suffix)
                if companion.is_file():
                    companions.append(record_file(companion))
            require(companions == row['companions'], 'External companion inventory or bytes changed: ' + module)
            for companion in companions:
                artifact(companion)
            external_entries.append({'module': module, 'object': record_file(path), 'companions': companions,
                                     'historical_object_hash_available': True,
                                     'historical_object_sha256': row['object']['sha256']})
        snapshot = {
            'schema': 'p25-complete-current-external-snapshot-v1', 'started_utc': snapshot_start, 'finished_utc': now(),
            'provider_roots': list(map(str, providers)), 'module_count': len(external_entries),
            'inherited_historical_object_pins': len(external_entries), 'first_captured_current_object_pins': 0,
            'historical_missing_hashes_invented': False,
            'inherited_from_accepted_context': record_file(reuse_path),
            'inherited_from_complete_snapshot': record_file(accepted_snapshot_path), 'entries': external_entries,
        }
        snapshot_path = OUT / 'COMPLETE_EXTERNAL_BEFORE.json'
        snapshot_path.write_text(json.dumps(snapshot, indent=2) + '\n')
        bind(snapshot_path)
        state['complete_external_before'] = record_file(snapshot_path)
        state['frozen_inputs'] = dict(frozen)
        write()
        context_check()

        for module in TARGETS:
            source = src / (module.replace('.', '/') + '.lean')
            obj = lib / (module.replace('.', '/') + '.olean')
            aud = audit / (module.split('.')[-1] + '.lean')
            require(not obj.exists(), 'A new owner object already exists')
            source.write_bytes((ROOT / helper.SOURCES[module]['path']).read_bytes())
            bind(source, helper.SOURCES[module]['source_sha256'])
            aud.write_text(audit_template.replace(helper.PAYLOAD, module))
            bind(aud)
            owner = {'module': module, 'status': 'PENDING', 'accepted': False,
                     'source_origin': {'commit': publication, 'path': helper.SOURCES[module]['path'],
                                       'sha256': helper.SOURCES[module]['source_sha256']},
                     'source_copy': record_file(source), 'audit_source': record_file(aud),
                     'required_owned_names': helper.SOURCES[module]['public_names'], 'stages': {}}
            state['modules'][module] = owner
            state.update(status='VERIFYING_TYPED_SOURCE_FACTS', frozen_inputs=dict(frozen))
            write()
            directory = OUT / module.split('.')[-1]
            directory.mkdir()
            for label, command in [('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(obj), str(source)]),
                                   ('replay', [str(CHECKER), '--verbose', module]),
                                   ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(aud)])]:
                run_stage(owner, label, command, directory / (label.upper() + '.log'))
                if label == 'normal':
                    bind(obj)
                    owner['object'] = record_file(obj)
                    owner['object_companions'] = []
                    for suffix in ['.private', '.server']:
                        companion = Path(str(obj) + suffix)
                        if companion.is_file():
                            bind(companion)
                            owner['object_companions'].append(record_file(companion))
                    state['frozen_inputs'] = dict(frozen)
                    write()
            declarations, inventory, project = helper.read_audit(directory / 'AUDIT.log', module)
            require(set(owner['required_owned_names']) <= {row['name'] for row in declarations}, 'Missing new public declaration')
            require({m for m in imports(directory / 'AUDIT.log') if not m.startswith('ImbalancedChen.')} == expected_external,
                    'New owner imported an unexpected external module')
            declarations_path, inventory_path = directory / 'OWNED_DECLARATIONS.json', directory / 'OWNED_INVENTORY.json'
            declarations_path.write_text(json.dumps(declarations, ensure_ascii=False, indent=2) + '\n')
            inventory_path.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + '\n')
            for path in [declarations_path, inventory_path, *[Path(row['log']) for row in owner['stages'].values()]]:
                bind(path)
            owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                         owned_count=len(declarations), owned_declarations=declarations, actual_project_closure=project,
                         declarations=record_file(declarations_path), inventory=record_file(inventory_path), ended_utc=now())
            state['frozen_inputs'] = dict(frozen)
            context_check()
            write()
            print('P25_TYPED_SOURCE_FACTS_OWNER_ACCEPTED', module, len(declarations), owner['object']['sha256'], flush=True)
        require(set(state['modules']) == {TARGET} and state['modules'][TARGET]['accepted'] and
                len(list((lib/'ImbalancedChen').glob('*.olean'))) == 8 and
                state['dependency_modules_compiled'] == [] and state['accepted_dependency_gates_rerun'] == [] and
                state['private_records_written'] == [] and state['original_transport_owner_compiled'] is False and
                state['reused_owner_receipts'][ROW00] == prior['modules'][ROW00],
                'Final single-owner/reuse policy changed')
        context_check()
        state.update(status='CELL00_TYPED_HEADERS_FACET_INDICES_ACCEPTED', accepted=True,
                     typed_headers_proved=True, typed_facet_indices_proved=True,
                     complete_external_after_matches_before=True, frozen_inputs=dict(frozen), ended_utc=now())
        write()
        print('P25_TYPED_SOURCE_FACTS_RESULT', json.dumps({'status': state['status'], 'accepted': True,
              'new_owned_counts': {TARGET: state['modules'][TARGET]['owned_count']},
              'typed_headers_proved': True, 'typed_facet_indices_proved': True,
              'original_archive_binding_proved_by_this_run': False, 'original_archive_headers_proved': False,
              'original_archive_facet_indices_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
              'result_path': str(OUT/'RESULT.json'), 'result_sha256': digest(OUT/'RESULT.json')}, sort_keys=True), flush=True)
    except BaseException as error:
        if state['status'] != 'MODULE_STAGE_FAILED':
            state['status'] = 'FAILED'
        state.update(accepted=False, error=f'{type(error).__name__}: {error}', ended_utc=now())
        (OUT/'RUNNER_EXCEPTION.log').write_text(traceback.format_exc())
        state['exception_log'] = record_file(OUT/'RUNNER_EXCEPTION.log')
        write()
        print('P25_TYPED_SOURCE_FACTS_FAILED', json.dumps({'status': state['status'], 'error': state['error'][:1600],
              'result_path': str(OUT/'RESULT.json'), 'result_sha256': digest(OUT/'RESULT.json')}, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
