#!/usr/bin/env python3
"""Independent sequential P3 verification of payload and stored-floor owners.

Usage: python3 run_cell00_payload_floors_cloud.py <exact-published-40-hex-commit>

This runner compiles no dependency and runs no host-side correctness check.
Successful data-owner verification does not prove the original typed decoder
returns that data. Stored-floor facts refer to the payload only; geometric
Jensen identities remain separate. Root submits this runner; it makes no
cloud API calls and imports no DecoderChars/Probe component.
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

ROOT = Path('/workspace/p25-q96-20261125')
PREVIOUS_HEAD = '55ef1e4be9d8295ab5ced1335f1210f52a7031b2'
BASE = ROOT / '.lake/diagnostic/p25-cell00-canonical-attempt001/charparse'
OUT = ROOT / '.lake/diagnostic/p25-payload-floors-attempt001'
PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-decoded')
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
MANIFEST_SHA = '76aa078eef969fa6c8d8270529f3d68f50b4bb6762626ba14a484423bbdc4321'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
DEPENDENCIES = {
    'ImbalancedChen.P2OriginalSaving16Decoder':
        'fd25815778e3bae5518d3fcc6a5461724b64251f91c4c08e61312fbae4987b39',
    'ImbalancedChen.P2OriginalSaving16Q96FloorCore':
        '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9',
    'ImbalancedChen.P2OriginalSaving19SourceJson':
        '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7',
}
MODULES = [{'module': 'ImbalancedChen.P2Saving16Cell00TypedPayload',
  'source_package': 'docs/source-only/20261126-p2-5-cell00-decoded',
  'source_sha256': 'e92848bd075bf82fe7325bd46e3ddcde937cba277387d46a3579560c27aa287b',
  'required_owned_names': ['ImbalancedChen.P2Saving16Cell00TypedPayload.cell00Payload'],
  'new_component_dependencies': []},
 {'module': 'ImbalancedChen.P2Saving16Cell00StoredFloors',
  'source_package': 'docs/source-only/20261126-p2-5-cell00-stored-floors',
  'source_sha256': 'a26efccb99e0529d166c2fe91c1f4ba78840cd761893fe9c5946e3ff348d8476',
  'required_owned_names': ['ImbalancedChen.P2Saving16Cell00StoredFloors.simplex04_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.simplex00_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.simplex01_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.simplex02_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.simplex03_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.simplex05_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.simplex06_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.simplex07_stored_jensen_floor',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_simplex_count',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_active8_count',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_vertex_count',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_vertex_dimensions',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_simplex_shape',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_stored_jensen_floors',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_stored_floor_guard',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_stored_jensen_floor_sum',
                           'ImbalancedChen.P2Saving16Cell00StoredFloors.cell00_separate_stored_floor_sum'],
  'new_component_dependencies': ['ImbalancedChen.P2Saving16Cell00TypedPayload']}]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def git(*args, cwd=ROOT):
    return subprocess.check_output(['git', *args], cwd=cwd, timeout=120).decode().strip()


def record_file(path):
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest(path)}


def main():
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]),
            'Pass exactly one full lowercase 40-hex publication commit.')
    publication = sys.argv[1]
    require(ROOT.is_dir(), f'Missing expected P3 checkout: {ROOT}')
    require(not OUT.exists(), f'Preserve prior attempt; output already exists: {OUT}')
    require(git('rev-parse', 'HEAD') in {PREVIOUS_HEAD, publication}, 'Unexpected existing P3 HEAD.')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 worktree is dirty.')
    OUT.mkdir()
    state = {
        'schema': 'p25-payload-floors-strict-v1', 'status': 'PREFLIGHT',
        'accepted': False, 'publication_commit': publication, 'started_utc': now(),
        'runner': record_file(Path(__file__).resolve()), 'strict_flags': FLAGS,
        'stage_wall_limit_seconds': 600, 'module_order': [m['module'] for m in MODULES],
        'modules': {}, 'dependency_modules_compiled': [], 'private_records_written': [],
        'original_cell00_sha256': INPUT_SHA, 'host_correctness_credit': False,
        'typed_decode_proved': False, 'original_archive_binding_proved': False,
        'geometric_jensen_binding_proved': False, 'stored_floor_arithmetic_proved': False,
        'Q96_proved': False, 'P2_5_proved': False,
    }

    def write():
        tmp = OUT / 'RESULT.tmp'
        tmp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
        tmp.replace(OUT / 'RESULT.json')

    def snapshot_hashes():
        return {str(p): digest(p) for p in frozen_files}

    def check_frozen():
        require(snapshot_hashes() == frozen_hashes, 'A frozen source, object, receipt or runtime changed.')

    def run_stage(module_state, label, command, env, log):
        check_frozen()
        start = time.monotonic()
        row = {'command': command, 'started_utc': now(), 'status': 'RUNNING', 'log': str(log)}
        module_state['stages'][label] = row
        write()
        print('P25_PAYLOAD_FLOORS_COMPONENT_STAGE_START', module_state['module'], label, flush=True)
        with log.open('wb') as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            try:
                exit_code = process.wait(timeout=600)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=30)
                exit_code = 124
        row.update(status='PASSED' if exit_code == 0 else 'FAILED',
                   exit_code=exit_code, timed_out=timed_out,
                   seconds=round(time.monotonic() - start, 3), ended_utc=now(),
                   log_sha256=digest(log), log_bytes=log.stat().st_size)
        write()
        summary = {k: row[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}
        print('P25_PAYLOAD_FLOORS_COMPONENT_STAGE_RESULT', module_state['module'], label,
              json.dumps(summary, sort_keys=True), flush=True)
        if exit_code:
            module_state['status'] = label.upper() + '_FAILED'
            state['status'] = 'MODULE_STAGE_FAILED'
            state['failed_module'] = module_state['module']
            state['failed_stage'] = label
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{module_state["module"]} {label} failed with exit {exit_code}.')
        check_frozen()

    write()
    try:
        if git('rev-parse', 'HEAD') != publication:
            with (OUT / 'PUBLICATION.log').open('wb') as stream:
                subprocess.run(['git', 'fetch', '--no-tags', 'origin', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
                subprocess.run(['git', 'checkout', '--detach', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
        require(git('rev-parse', 'HEAD') == publication, 'Publication checkout mismatch.')
        require(not git('status', '--porcelain', '--untracked-files=no'), 'Publication checkout is dirty.')
        state['publication_checked_out'] = publication

        old_path = BASE / 'RESULT.json'
        old = json.loads(old_path.read_text())
        snapshot = old['normal_snapshot_before']
        require(snapshot['mathlib_pin'] == MATHLIB_PIN, 'Unexpected recorded Mathlib pin.')
        require(git('rev-parse', 'HEAD', cwd=Path(snapshot['mathlib_path'])) == MATHLIB_PIN,
                'Current Mathlib checkout differs from accepted dependency context.')
        for binary in [LEAN, CHECKER]:
            expected = snapshot['files'][str(binary)]['sha256']
            require(digest(binary) == expected, f'Pinned executable changed: {binary}')
        state['dependency_receipt_source'] = record_file(old_path)
        state['prior_charparse_status'] = old['status']
        state['runtime'] = {'lean': record_file(LEAN), 'leanchecker': record_file(CHECKER),
                            'mathlib_pin': MATHLIB_PIN, 'mathlib_path': snapshot['mathlib_path']}

        src, lib, audit = OUT / 'src', OUT / 'lib', OUT / 'audit'
        for directory in [src / 'ImbalancedChen', lib / 'ImbalancedChen', audit]:
            directory.mkdir(parents=True)
        tail_paths = old['approved_LEAN_PATH'].split(':')[1:]
        require(tail_paths and all(p and Path(p).is_dir() for p in tail_paths), 'Missing pinned Mathlib path.')
        require(all(Path(p).resolve().is_relative_to(Path('/mathlib').resolve()) for p in tail_paths),
                'Unexpected project fallback path in old approved LEAN_PATH.')
        require(all(not (Path(p) / 'ImbalancedChen').exists() for p in tail_paths),
                'A Mathlib fallback path contains unexpected project modules.')
        env = dict(os.environ)
        env.pop('LEAN_SRC_PATH', None)
        env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
        env['LEAN_PATH'] = ':'.join([str(lib), *tail_paths])
        env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')
        state['approved_LEAN_PATH'] = env['LEAN_PATH']
        state['isolated_source_root'], state['isolated_library'] = str(src), str(lib)
        frozen_files = [old_path, LEAN, CHECKER]
        state['dependency_objects'] = {}
        for module, expected_object in DEPENDENCIES.items():
            prior = old['dependency_objects'][module]
            require(prior['sha256'] == expected_object, f'Unexpected recorded object hash: {module}')
            original, receipt_path = Path(prior['path']), Path(prior['receipt'])
            require(digest(original) == expected_object, f'Accepted dependency object drift: {module}')
            require(digest(receipt_path) == prior['receipt_sha256'], f'Accepted dependency receipt drift: {module}')
            receipt = json.loads(receipt_path.read_text())
            require(receipt['accepted'] is True and receipt['module'] == module,
                    f'Dependency receipt is not accepted: {module}')
            require(receipt['object_sha256'] == expected_object, f'Dependency receipt object mismatch: {module}')
            require(receipt['audit']['exit_code'] == receipt['replay']['exit_code'] == 0,
                    f'Dependency audit/replay did not pass: {module}')
            destination = lib / (module.replace('.', '/') + '.olean')
            shutil.copyfile(original, destination)
            require(digest(destination) == expected_object, f'Dependency copy mismatch: {module}')
            state['dependency_objects'][module] = {
                **prior, 'isolated_path': str(destination),
                'source_sha256': receipt['source_sha256'], 'accepted_receipt_reused': True,
            }
            frozen_files.extend([original, receipt_path, destination])
        require(len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 3,
                'Unexpected initial isolated dependency object.')

        files_path = ROOT / PACKAGE / 'TYPED_PAYLOAD_FILES.json'
        require(digest(files_path) == MANIFEST_SHA, 'Frozen payload file manifest changed.')
        payload_files = json.loads(files_path.read_text())
        payload_module = MODULES[0]['module']
        require(payload_files['module'] == payload_module, 'Payload manifest module mismatch.')
        expected_payload = payload_files['expected_owned_names']
        require(payload_files['expected_owned_declarations'] == len(expected_payload) == len(set(expected_payload)) == 544,
                'Payload manifest must specify exactly 544 distinct owned declarations.')
        require(payload_files['original_input_sha256'] == INPUT_SHA, 'Payload original-input binding drift.')
        state['payload_files_manifest'] = record_file(files_path)
        frozen_files.append(files_path)
        for entry in payload_files['files']:
            path = ROOT / entry['path']
            require(digest(path) == entry['sha256'] and path.stat().st_size == entry['bytes'],
                    f'Frozen payload package file changed: {path}')
            frozen_files.append(path)
        payload_audit_path = ROOT / payload_files['audit_file']
        audit_template = payload_audit_path.read_text()
        state['audit_template'] = record_file(payload_audit_path)

        for spec in MODULES:
            module = spec['module']
            relative = Path(spec['source_package']) / (module.replace('.', '/') + '.lean')
            path = ROOT / relative
            published = subprocess.check_output(['git', 'show', f'{publication}:{relative}'], cwd=ROOT, timeout=120)
            require(published == path.read_bytes(), f'Working source differs from published commit: {module}')
            require(hashlib.sha256(published).hexdigest() == spec['source_sha256'],
                    f'Frozen component source hash mismatch: {module}')
            destination = src / (module.replace('.', '/') + '.lean')
            destination.write_bytes(published)
            audit_path = audit / (module.split('.')[-1] + '.lean')
            audit_path.write_text(audit_template.replace(payload_module, module))
            frozen_files.extend([path, destination, audit_path])
            state['modules'][module] = {
                'module': module, 'status': 'PENDING', 'accepted': False,
                'source_origin': {'commit': publication, 'path': str(relative), 'sha256': spec['source_sha256']},
                'source_copy': record_file(destination), 'audit_source': record_file(audit_path),
                'required_owned_names': spec['required_owned_names'], 'stages': {},
            }
        frozen_files = list(dict.fromkeys(frozen_files))
        frozen_hashes = snapshot_hashes()
        state['frozen_inputs'] = frozen_hashes
        state['status'] = 'VERIFYING_COMPONENTS'
        write()

        for spec in MODULES:
            module = spec['module']
            owner = state['modules'][module]
            owner['status'] = 'RUNNING'
            directory = OUT / module.split('.')[-1]
            directory.mkdir()
            source_path = src / (module.replace('.', '/') + '.lean')
            object_path = lib / (module.replace('.', '/') + '.olean')
            audit_path = audit / (module.split('.')[-1] + '.lean')
            require(not object_path.exists(), f'Target object unexpectedly exists: {module}')
            commands = [
                ('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(object_path), str(source_path)]),
                ('replay', [str(CHECKER), '--verbose', module]),
                ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(audit_path)]),
            ]
            for label, command in commands:
                run_stage(owner, label, command, env, directory / (label.upper() + '.log'))
                if label == 'normal':
                    require(object_path.is_file(), f'Normal compile produced no object: {module}')
                    owner['object'] = record_file(object_path)
                    frozen_files.append(object_path)
                    frozen_hashes[str(object_path)] = digest(object_path)
                    state['frozen_inputs'] = frozen_hashes
                    write()
            lines = (directory / 'AUDIT.log').read_text().splitlines()
            records = [json.loads(s.removeprefix('P0_QUEUE_DECL ')) for s in lines if s.startswith('P0_QUEUE_DECL ')]
            inventories = [json.loads(s.removeprefix('P0_QUEUE_INVENTORY ')) for s in lines if s.startswith('P0_QUEUE_INVENTORY ')]
            imports = [json.loads(s.removeprefix('P0_QUEUE_IMPORTS ')) for s in lines if s.startswith('P0_QUEUE_IMPORTS ')]
            names = sorted(row['name'] for row in records)
            require(len(inventories) == len(imports) == 1 and inventories[0]['module'] == module,
                    f'Missing or duplicate complete audit inventory: {module}')
            require(names and len(names) == len(set(names)) and
                    names == sorted(inventories[0]['serialized']) == sorted(inventories[0]['environment']),
                    f'Complete serialized/environment/declaration inventory mismatch: {module}')
            require(all(row['module'] == module and
                        not any(row[k] for k in ['unsafe', 'partial', 'axiom']) and
                        set(row['axioms']) <= ALLOWED_AXIOMS for row in records),
                    f'Unsafe, partial, axiom, or forbidden transitive axiom in owner: {module}')
            require(set(spec['required_owned_names']) <= set(names), f'Required public declaration missing: {module}')
            if module == payload_module:
                require(names == sorted(expected_payload), 'Actual payload inventory differs from all 544 expected names.')
            actual_project = {m for m in imports[0] if m.startswith('ImbalancedChen.')}
            expected_project = set(DEPENDENCIES) | {module} | set(spec['new_component_dependencies'])
            require(actual_project == expected_project, f'Unexpected project import closure: {module}: {sorted(actual_project)}')
            declarations_path = directory / 'OWNED_DECLARATIONS.json'
            declarations_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n')
            inventory_path = directory / 'OWNED_INVENTORY.json'
            inventory_path.write_text(json.dumps(inventories[0], ensure_ascii=False, indent=2) + '\n')
            owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                         owned_count=len(records), owned_declarations=records,
                         actual_project_closure=sorted(actual_project),
                         declarations=record_file(declarations_path), inventory=record_file(inventory_path),
                         ended_utc=now())
            check_frozen()
            write()
            print('P25_PAYLOAD_FLOORS_COMPONENT_ACCEPTED', module, len(records), owner['object']['sha256'], flush=True)
        require(all(v['accepted'] for v in state['modules'].values()), 'Not all component owners accepted.')
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Publication changed during verification.')
        check_frozen()
        state.update(status='PAYLOAD_AND_STORED_FLOORS_ACCEPTED_BINDINGS_PENDING',
                     accepted=True, stored_floor_arithmetic_proved=True, ended_utc=now())
        write()
        print('P25_PAYLOAD_FLOORS_COMPONENTS_RESULT', json.dumps({
            'status': state['status'], 'accepted': True,
            'owned_counts': {m: v['owned_count'] for m, v in state['modules'].items()},
            'typed_decode_proved': False, 'geometric_jensen_binding_proved': False,
            'stored_floor_arithmetic_proved': True, 'Q96_proved': False, 'P2_5_proved': False,
            'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json'),
        }, sort_keys=True), flush=True)
    except BaseException as exc:
        if state['status'] not in {'MODULE_STAGE_FAILED'}:
            state['status'] = 'FAILED'
        state.update(accepted=False, ended_utc=now(), error=f'{type(exc).__name__}: {exc}')
        (OUT / 'RUNNER_EXCEPTION.log').write_text(traceback.format_exc())
        state['exception_log'] = record_file(OUT / 'RUNNER_EXCEPTION.log')
        write()
        print('P25_PAYLOAD_FLOORS_COMPONENTS_FAILED', json.dumps({
            'status': state['status'], 'error': state['error'][:1800],
            'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json'),
        }, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
