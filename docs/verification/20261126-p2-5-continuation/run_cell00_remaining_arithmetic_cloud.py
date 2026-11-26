#!/usr/bin/env python3
"""SOURCE ONLY: verify the seven remaining cell00 rows and their composition.

Reuse the exact accepted row00 owner and its eight accepted dependencies. A
complete current external snapshot is captured before any new gate. Row00 is
replayed/audited under that snapshot without normal recompilation; its original
owner receipt remains unchanged. Only row01..07 and AllRowsArithmetic receive
new normal compilation. Pass the exact source publication as the sole argument.
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
OUT = ROOT / '.lake/diagnostic/p25-cell00-remaining-arithmetic-attempt001'
PRIOR_PUBLICATION = '8fa1d8c84f8c465da8f8fd00bfce1410e1807ae3'
PRIOR_RESULT_SHA = '7094b47bfe97aaa8236cda1309e805440a3b6a1b48b5d4083fa6ba75cd2e8265'
PRIOR_OBJECT_SHA = '7c8eb471baa5194d264a17adecf198beb5e3d6b46ab3c548ba9d1c9946756d51'
PRIOR_RUNNER = 'docs/verification/20261126-p2-5-continuation/run_cell00_row00_arithmetic_cloud.py'
PRIOR_RUNNER_SHA = '51155a110a8a4519a1ece049425e833b1edde31d7754347fdbe25a018dcc56d2'
RUNNER_REL = 'docs/verification/20261126-p2-5-continuation/run_cell00_remaining_arithmetic_cloud.py'
PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-remaining-arithmetic')
MANIFEST_SHA = '2e8c1196dfb22bec0ff50c9070420e8ad9d3c838d723ec01d14bb9d4fdd4f9a3'
SELECTION_SHA = 'b0d1112bb62caeeb249ffd60371233968030c840e5f0a3a438b97b4dfee001b0'
FILES_SHA = '69941a9d845f40241d33a008e1c65a12fbc886b77fdec81643044feb89a05419'
ROW00 = 'ImbalancedChen.P2Saving16Cell00Row00Arithmetic'
ROWS = ['ImbalancedChen.P2Saving16Cell00Row%02dArithmetic' % i for i in range(1, 8)]
COMPOSITION = 'ImbalancedChen.P2Saving16Cell00AllRowsArithmetic'
TARGETS = ROWS + [COMPOSITION]
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
        'schema': 'p25-cell00-remaining-arithmetic-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600, 'module_order': TARGETS,
        'modules': {}, 'dependency_objects': {}, 'dependency_receipts': {}, 'dependency_modules_compiled': [],
        'reused_owner_receipts': {}, 'private_records_written': [], 'row00_normal_recompiled': False,
        'row00_additional_reuse_validation': None, 'original_cell00_sha256': INPUT_SHA,
        'host_correctness_credit': False, 'other_seven_typed_simplex_guards_proved': False,
        'all_eight_typed_simplex_guards_proved': False, 'typed_geometric_jensen_floors_proved': False,
        'typed_geometric_floor_sum_proved': False, 'original_archive_binding_proved_by_this_run': False,
        'original_archive_simplex_guards_proved': False, 'cellFloorNumerator_proved': False,
        'source_cell_membership_proved': False, 'pulling_ownership_proved': False,
        'all_cell_finite_guards_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
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
        require(module in TARGETS or (module == ROW00 and label in ('replay', 'audit')),
                'Only new owners may receive normal compilation')
        context_check()
        started = time.monotonic()
        stage = {'command': command, 'status': 'RUNNING', 'started_utc': now(), 'log': str(log)}
        owner['stages'][label] = stage
        write()
        print('P25_REMAINING_STAGE_START', module, label, flush=True)
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
        print('P25_REMAINING_STAGE_RESULT', module, label, json.dumps({k: stage[k] for k in
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
        require(git('rev-parse', 'HEAD') in {PRIOR_PUBLICATION, publication}, 'Unexpected current P3 publication')
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
        selection_path = bind(ROOT / PACKAGE / 'SELECTION.json', SELECTION_SHA)
        files_path = bind(ROOT / PACKAGE / 'FILES.json', FILES_SHA)
        manifest = json.loads(manifest_path.read_text())
        selection = json.loads(selection_path.read_text())
        require(manifest['schema'] == 'p25-cell00-remaining-arithmetic-source-candidates-v1' and
                selection['schema'] == 'p25-cell00-remaining-arithmetic-source-selection-v1' and
                selection['new_row_modules'] == ROWS and selection['composition_module'] == COMPOSITION and
                selection['new_owner_count'] == 8 and selection['project_closure_count'] == 17 and
                selection['dependency_recompilations_permitted'] == 0 and
                selection['row00_source_replacement_permitted'] is False, 'Frozen candidate selection differs')
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
        require(set(selection['sources']) == set(original_graph) | set(TARGETS), 'Unexpected source provider or omitted module')
        helper.SOURCES = dict(original_graph)
        for module, selected in selection['sources'].items():
            source = bind(ROOT / selected['path'], selected['source_sha256'])
            require(source.read_bytes() == subprocess.check_output(['git', 'show', publication + ':' + selected['path']],
                                                                   cwd=ROOT, timeout=120), 'Source is not the published version: ' + module)
            actual_imports = [name for line in re.findall(r'^import\s+([^\n]+)$', source.read_text(), re.M)
                              for name in line.split() if name.startswith('ImbalancedChen.')]
            require(actual_imports == selected['project_imports'], 'Project import graph differs: ' + module)
            if module in original_graph:
                require(all(original_graph[module][key] == selected[key]
                            for key in ['path', 'source_sha256', 'project_imports']), 'Accepted source changed')
            else:
                names = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)', source.read_text(), re.M)
                require(len(names) == len(set(names)) == (3 if module == COMPOSITION else 15), 'Public declaration count differs')
                helper.SOURCES[module] = {key: selected[key] for key in ['path', 'source_sha256', 'project_imports']}
                helper.SOURCES[module].update(public_namespace=module, public_names=[module + '.' + name for name in names])
        for row in manifest['row_candidates'] + [manifest['composition_candidate']]:
            spec = helper.SOURCES[row['module']]
            require(row['path'] == spec['path'] and row['sha256'] == spec['source_sha256'] and
                    (ROOT / row['path']).stat().st_size == row['bytes'], 'Candidate manifest identity differs')
        require(len(helper.project_closure(COMPOSITION)) == 17 and
                all(len(helper.project_closure(module)) == 9 for module in ROWS), 'Actual selected closure differs')
        state.update(source_graph=helper.SOURCES, source_selection=record_file(selection_path),
                     source_manifest=record_file(manifest_path),
                     expected_project_imports_by_owner={m: sorted(helper.project_closure(m)) for m in TARGETS})
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
        required_dependencies = set(original_graph)
        require(set(prior['dependency_objects']) == required_dependencies - {ROW00} and
                set(prior['dependency_receipts']) == required_dependencies - {ROW00}, 'Prior dependency inventory differs')
        for module, row in prior['dependency_objects'].items():
            require(row['source_sha256'] == helper.SOURCES[module]['source_sha256'], 'Accepted dependency source differs')
            bind(row['path'], row['sha256'])
            bind(row['isolated_path'], row['sha256'])
            artifact(prior['dependency_receipts'][module])
            copy_dependency(module, row['isolated_path'], row['sha256'])
            state['dependency_receipts'][module] = json.loads(json.dumps(prior['dependency_receipts'][module]))
        copy_dependency(ROW00, row00_owner['object']['path'], PRIOR_OBJECT_SHA)
        state['dependency_receipts'][ROW00] = {**record_file(prior_path), 'original_owner_publication': PRIOR_PUBLICATION,
                                               'owned_count': 21, 'owner_accepted': True}
        require(set(state['dependency_objects']) == required_dependencies and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 9, 'Fresh library must contain only nine accepted objects')

        # The earlier row00 receipt froze the transferred FastDet closure. The
        # complete row00 external set is larger. First-captured hashes here are
        # explicitly current-context pins, never invented historical evidence.
        providers = [LEAN.parent.parent / 'lib/lean', *map(Path, tails)]
        require(len(providers) == len(set(providers)) and all(p.is_dir() and not (p/'ImbalancedChen').exists() for p in providers),
                'External provider roots are missing/repeated or shadow project objects')
        context_path = artifact(prior['runtime_context_receipt'], helper.BASE_RESULT_SHA)
        canonical_context = json.loads(context_path.read_text())
        historical_external_pins = dict(prior['frozen_inputs'])
        for path, row in canonical_context['normal_snapshot_before']['files'].items():
            if any(path.startswith(str(root) + '/') for root in providers) and path.endswith(('.olean', '.olean.private', '.olean.server')):
                require(path not in historical_external_pins or historical_external_pins[path] == row['sha256'],
                        'Canonical and row00 historical external pins disagree')
                historical_external_pins[path] = row['sha256']
        state['additional_historical_context_receipt'] = record_file(context_path)
        snapshot_start = now()
        inherited_count = 0
        for module in sorted(expected_external):
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module), 'Invalid audited module name')
            relative = module.replace('.', '/') + '.olean'
            found = [root / relative for root in providers if (root / relative).is_file()]
            require(len(found) == 1, 'Missing/shadowed external module: ' + module)
            path = found[0]
            inherited = historical_external_pins.get(str(path))
            bind(path, inherited)
            inherited_count += inherited is not None
            companions = []
            for suffix in ['.private', '.server']:
                companion = Path(str(path) + suffix)
                if companion.is_file():
                    bind(companion, historical_external_pins.get(str(companion)))
                    companions.append(record_file(companion))
            external_entries.append({'module': module, 'object': record_file(path), 'companions': companions,
                                     'historical_object_hash_available': inherited is not None,
                                     'historical_object_sha256': inherited})
        snapshot = {
            'schema': 'p25-complete-current-external-snapshot-v1', 'started_utc': snapshot_start, 'finished_utc': now(),
            'provider_roots': list(map(str, providers)), 'module_count': len(external_entries),
            'inherited_historical_object_pins': inherited_count,
            'first_captured_current_object_pins': len(external_entries) - inherited_count,
            'historical_missing_hashes_invented': False, 'entries': external_entries,
        }
        snapshot_path = OUT / 'COMPLETE_EXTERNAL_BEFORE.json'
        snapshot_path.write_text(json.dumps(snapshot, indent=2) + '\n')
        bind(snapshot_path)
        state['complete_external_before'] = record_file(snapshot_path)
        state['frozen_inputs'] = dict(frozen)
        write()
        context_check()

        # Revalidate the unchanged existing owner under this complete frozen
        # environment. Its original normal/owner receipts remain untouched.
        reuse_dir = OUT / 'row00-reuse-validation'
        reuse_dir.mkdir()
        reuse_audit = audit / 'Row00ReuseAudit.lean'
        reuse_audit.write_text(audit_template.replace(helper.PAYLOAD, ROW00))
        bind(reuse_audit)
        reuse = {'module': ROW00, 'status': 'PENDING', 'accepted': False, 'normal_recompiled': False,
                 'source_origin': row00_owner['source_origin'], 'source_copy': row00_owner['source_copy'],
                 'object': record_file(lib / (ROW00.replace('.', '/') + '.olean')),
                 'audit_source': record_file(reuse_audit),
                 'original_owner_receipt': record_file(prior_path), 'stages': {}}
        state['row00_additional_reuse_validation'] = reuse
        for label, command in [('replay', [str(CHECKER), '--verbose', ROW00]),
                               ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(reuse_audit)])]:
            run_stage(reuse, label, command, reuse_dir / (label.upper() + '.log'))
        declarations, inventory, project = helper.read_audit(reuse_dir / 'AUDIT.log', ROW00)
        require(declarations == row00_declarations and inventory == row00_inventory and
                project == row00_owner['actual_project_closure'] and
                {m for m in imports(reuse_dir / 'AUDIT.log') if not m.startswith('ImbalancedChen.')} == expected_external,
                'Row00 full-owned identity/imports changed under current complete snapshot')
        for stage in reuse['stages'].values():
            bind(stage['log'], stage['log_sha256'])
        reuse.update(status='REPLAY_COMPLETE_OWNED_REUSE_VALIDATED', accepted=True, owned_count=21,
                     owned_declarations=declarations, inventory=inventory, actual_project_closure=project,
                     complete_external_before=record_file(snapshot_path), ended_utc=now())
        state['frozen_inputs'] = dict(frozen)
        write()

        for module in TARGETS:
            if module == COMPOSITION:
                require(reuse['accepted'] and all(state['modules'][m]['accepted'] for m in ROWS),
                        'All eight row owners must be accepted before composition')
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
            state.update(status='VERIFYING_REMAINING_ARITHMETIC', frozen_inputs=dict(frozen))
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
            print('P25_REMAINING_OWNER_ACCEPTED', module, len(declarations), owner['object']['sha256'], flush=True)
        require(set(state['modules']) == set(TARGETS) and all(row['accepted'] for row in state['modules'].values()) and
                len(list((lib/'ImbalancedChen').glob('*.olean'))) == 17 and
                state['dependency_modules_compiled'] == [] and state['row00_normal_recompiled'] is False and
                state['reused_owner_receipts'][ROW00] == prior['modules'][ROW00], 'Final owner/reuse policy changed')
        context_check()
        state.update(status='CELL00_ALL_EIGHT_TYPED_ARITHMETIC_ACCEPTED', accepted=True,
                     other_seven_typed_simplex_guards_proved=True, all_eight_typed_simplex_guards_proved=True,
                     typed_geometric_jensen_floors_proved=True, typed_geometric_floor_sum_proved=True,
                     complete_external_after_matches_before=True, frozen_inputs=dict(frozen), ended_utc=now())
        write()
        print('P25_REMAINING_RESULT', json.dumps({'status': state['status'], 'accepted': True,
              'new_owned_counts': {m: state['modules'][m]['owned_count'] for m in TARGETS},
              'all_eight_typed_simplex_guards_proved': True, 'typed_geometric_floor_sum_proved': True,
              'original_archive_binding_proved_by_this_run': False, 'cellFloorNumerator_proved': False,
              'Q96_proved': False, 'P2_5_proved': False, 'result_path': str(OUT/'RESULT.json'),
              'result_sha256': digest(OUT/'RESULT.json')}, sort_keys=True), flush=True)
    except BaseException as error:
        if state['status'] != 'MODULE_STAGE_FAILED':
            state['status'] = 'FAILED'
        state.update(accepted=False, error=f'{type(error).__name__}: {error}', ended_utc=now())
        (OUT/'RUNNER_EXCEPTION.log').write_text(traceback.format_exc())
        state['exception_log'] = record_file(OUT/'RUNNER_EXCEPTION.log')
        write()
        print('P25_REMAINING_FAILED', json.dumps({'status': state['status'], 'error': state['error'][:1600],
              'result_path': str(OUT/'RESULT.json'), 'result_sha256': digest(OUT/'RESULT.json')}, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
