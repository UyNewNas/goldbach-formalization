#!/usr/bin/env python3
"""SOURCE ONLY: strict P3 verification of the cell00 row00 arithmetic owner.

Compile only Row00Arithmetic. Reuse every project dependency from its accepted
receipt, including a transferable P1 FastDet capsule. Never compile a dependency.
The four CLI arguments are publication, accepted.tar.gz, CAPSULE_TRANSPORT.json,
and the independently supplied SHA256 of that transport receipt.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time
import traceback

ROOT = Path('/workspace/p25-q96-20261125')
OUT = ROOT / '.lake/diagnostic/p25-cell00-row00-arithmetic-attempt001'
PAYLOAD_FLOORS = ROOT / '.lake/diagnostic/p25-payload-floors-attempt001'
FINITE_CORE = ROOT / '.lake/diagnostic/p25-finite-core-attempt001'
BASE = ROOT / '.lake/diagnostic/p25-cell00-canonical-attempt001/charparse'
PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-row00-arithmetic')
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
MANIFEST_SHA = 'c98c5ce3827ea6eee30754a7642c210d7dc5dc509c7fb8f8eb5eb7224b501eed'
BASE_RESULT_SHA = '4dca8c2c7b42feb027895420ddb62e0a314d5f6f440d8b772704eeb146ba37eb'
PAYLOAD_RESULT_SHA = '090463b93761d31023f39111c32522e1f2bb3cbcec46e606f7fc429d69d4a204'
FINITE_CORE_RECEIPT_SHA = 'b1f2a463ed670e01335244dc35f1e0a3614ced20bbea791a5a5d72e980e95dd9'
PAYLOAD_FILES_SHA = '76aa078eef969fa6c8d8270529f3d68f50b4bb6762626ba14a484423bbdc4321'
PAYLOAD = 'ImbalancedChen.P2Saving16Cell00TypedPayload'
FLOORS = 'ImbalancedChen.P2Saving16Cell00StoredFloors'
CORE_OWNER = 'ImbalancedChen.P2OriginalSaving16FiniteCore'
FASTDET = 'ImbalancedChen.P2Winner9FastDetPure'
TARGET = 'ImbalancedChen.P2Saving16Cell00Row00Arithmetic'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
KNOWN_OBJECTS = {
    'ImbalancedChen.P2OriginalSaving16Decoder': 'fd25815778e3bae5518d3fcc6a5461724b64251f91c4c08e61312fbae4987b39',
    'ImbalancedChen.P2OriginalSaving16Q96FloorCore': '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9',
    'ImbalancedChen.P2OriginalSaving19SourceJson': '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7',
    'ImbalancedChen.P2OriginalSaving16OriginalInput': '72488821ccb01dec90188d2f09b0e3a73c0087b54c6c4bae4410a109b6f82f91',
    CORE_OWNER: '83923cb30eed3a39509324af01988e9708005913b304bb63fd2f56dcee82604c',
    PAYLOAD: '1c61948df2571b065f3b27ae2eeeff1202b942e39bb16229f93c9cc40b1e8c75',
    FLOORS: 'f7c880efb54b82fe9c42d7e9f6216817eea15e00e50ec7545a0c73578566e3ae',
}

P1_RUNNER_SHA = '9a146941540b51c4acd3815cbc92280b49bc1190b01e77d44f12474821413770'
P1_CONTRACT_SHA = '924cebed6b222f4183e5bf7cd7b6fed8ee06af222a2429f41bb1046dd9145cc3'
MATHLIB_MANIFEST_SHA = '951d5f6dcfce202878cd5b103157bd0ceba69510955db6e11db4183fd866a911'
PACKAGE_PINS = {'plausible': 'b1c4a69a7e247ab7df20460212001673d74f08c0',
 'LeanSearchClient': '0498c7c070c143a3bf7379f4d99a2c63bb9d9715',
 'importGraph': '18a90119a5d316358fde6c86e0ca24e59212e32c',
 'proofwidgets': 'b1436dc749e722c9920036b52cdc43b3451d0b69',
 'aesop': '57d3325be72a842920813bcb40f96a6f7393c185',
 'Qq': 'ee41917ae11d38479fb8fb24745f7ca4bf0a784d',
 'batteries': '41bd267b3f6b7252f6676af46d4ffc6783b64de9',
 'Cli': 'da07ca808b6718cb2aed14dba154e5a08b8f8ecf'}
FASTDET_DIRECT_IMPORTS = ['Mathlib.LinearAlgebra.Matrix.Determinant.Basic',
 'Mathlib.Data.Rat.Defs',
 'Mathlib.Tactic.NormNum',
 'Mathlib.Tactic.Ring']

SOURCES = {'ImbalancedChen.P2OriginalSaving16Decoder': {'path': 'ImbalancedChen/P2OriginalSaving16Decoder.lean',
                                              'source_sha256': 'e1b23e3de928a97c411d1c6aa73f2059b204d7b9f297105edcd591916b9aee80',
                                              'project_imports': ['ImbalancedChen.P2OriginalSaving16Q96FloorCore',
                                                                  'ImbalancedChen.P2OriginalSaving19SourceJson']},
 'ImbalancedChen.P2OriginalSaving16Q96FloorCore': {'path': 'ImbalancedChen/P2OriginalSaving16Q96FloorCore.lean',
                                                   'source_sha256': '9a456807e6c3a167fd12c1c6e5db492d6c54fd700a1de122ea492774f697c778',
                                                   'project_imports': []},
 'ImbalancedChen.P2OriginalSaving19SourceJson': {'path': 'ImbalancedChen/P2OriginalSaving19SourceJson.lean',
                                                 'source_sha256': 'd58e22ba7e2d92b6c9f2d139993361ae9b827d25d6869fcf38f3837ba7bc3d02',
                                                 'project_imports': []},
 'ImbalancedChen.P2OriginalSaving16OriginalInput': {'path': 'ImbalancedChen/P2OriginalSaving16OriginalInput.lean',
                                                    'source_sha256': '792a5adf50263cfc1a0f67fb3d088c7612910388e4d1fa65db45c3c50065aca5',
                                                    'project_imports': []},
 'ImbalancedChen.P2OriginalSaving16FiniteCore': {'path': 'ImbalancedChen/P2OriginalSaving16FiniteCore.lean',
                                                 'source_sha256': '552f7ac2f777173c0f555896d85d98bd17513fc972e520f7a0f4dbc406a96322',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16OriginalInput',
                                                                     'ImbalancedChen.P2OriginalSaving16Decoder',
                                                                     'ImbalancedChen.P2OriginalSaving16Q96FloorCore',
                                                                     'ImbalancedChen.P2OriginalSaving19SourceJson'],
                                                 'public_namespace': 'ImbalancedChen.P2OriginalSaving16OriginalArchive'},
 'ImbalancedChen.P2Saving16Cell00TypedPayload': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00TypedPayload.lean',
                                                 'source_sha256': 'e92848bd075bf82fe7325bd46e3ddcde937cba277387d46a3579560c27aa287b',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16Decoder'],
                                                 'public_namespace': 'ImbalancedChen.P2Saving16Cell00TypedPayload'},
 'ImbalancedChen.P2Saving16Cell00StoredFloors': {'path': 'docs/source-only/20261126-p2-5-cell00-stored-floors/ImbalancedChen/P2Saving16Cell00StoredFloors.lean',
                                                 'source_sha256': 'a26efccb99e0529d166c2fe91c1f4ba78840cd761893fe9c5946e3ff348d8476',
                                                 'project_imports': ['ImbalancedChen.P2Saving16Cell00TypedPayload',
                                                                     'ImbalancedChen.P2OriginalSaving16Q96FloorCore'],
                                                 'public_namespace': 'ImbalancedChen.P2Saving16Cell00StoredFloors'},
 'ImbalancedChen.P2Winner9FastDetPure': {'path': 'docs/source-only/20261126-p2-5-cell00-row00-arithmetic/ImbalancedChen/P2Winner9FastDetPure.lean',
                                         'source_sha256': 'd1a0d2ae8af1cf90e05af11b983c5c41ea97a42387eb6c6b9c32ff176e2258ac',
                                         'project_imports': [],
                                         'public_namespace': 'ImbalancedChen.P2Winner9FastDetPure'},
 'ImbalancedChen.P2Saving16Cell00Row00Arithmetic': {'path': 'docs/source-only/20261126-p2-5-cell00-row00-arithmetic/ImbalancedChen/P2Saving16Cell00Row00Arithmetic.lean',
                                                    'source_sha256': '2d75a057eb12c8bd77ebce748646867bac202fe1cda70fe8c0236598278bee0e',
                                                    'project_imports': ['ImbalancedChen.P2OriginalSaving16FiniteCore',
                                                                        'ImbalancedChen.P2Saving16Cell00TypedPayload',
                                                                        'ImbalancedChen.P2Saving16Cell00StoredFloors',
                                                                        'ImbalancedChen.P2Winner9FastDetPure'],
                                                    'public_namespace': 'ImbalancedChen.P2Saving16Cell00Row00Arithmetic'}}


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

def project_closure(module):
    found = set()

    def visit(name):
        if name in found:
            return
        require(name in SOURCES, f'Unspecified project import: {name}')
        found.add(name)
        for imported in SOURCES[name]['project_imports']:
            visit(imported)

    visit(module)
    return found

def read_audit(log, module):
    lines = log.read_text().splitlines()
    records = [json.loads(s.removeprefix('P0_QUEUE_DECL ')) for s in lines if s.startswith('P0_QUEUE_DECL ')]
    inventories = [json.loads(s.removeprefix('P0_QUEUE_INVENTORY ')) for s in lines if s.startswith('P0_QUEUE_INVENTORY ')]
    imports = [json.loads(s.removeprefix('P0_QUEUE_IMPORTS ')) for s in lines if s.startswith('P0_QUEUE_IMPORTS ')]
    names = sorted(r['name'] for r in records)
    require(len(inventories) == len(imports) == 1 and inventories[0]['module'] == module,
            f'Missing/duplicate full inventory: {module}')
    require(names and len(names) == len(set(names)) and
            names == sorted(inventories[0]['serialized']) == sorted(inventories[0]['environment']),
            f'Incomplete serialized/environment/declaration inventory: {module}')
    require(all(r['module'] == module and not any(r[k] for k in ['axiom', 'partial', 'unsafe']) and
                set(r['axioms']) <= ALLOWED_AXIOMS for r in records), f'Forbidden declaration/axiom: {module}')
    actual = {m for m in imports[0] if m.startswith('ImbalancedChen.')}
    require(actual == project_closure(module), f'Actual project closure mismatch: {module}: {sorted(actual)}')
    return records, inventories[0], sorted(actual)


def main():
    require(len(sys.argv) == 5 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]) and
            re.fullmatch(r'[0-9a-f]{64}', sys.argv[4]),
            'Pass publication40, accepted.tar.gz, CAPSULE_TRANSPORT.json, transport_sha256.')
    publication = sys.argv[1]
    capsule_archive = Path(sys.argv[2]).resolve()
    capsule_transport = Path(sys.argv[3]).resolve()
    transport_sha = sys.argv[4]
    require(ROOT.is_dir() and not OUT.exists(), 'Expected checkout missing or attempt already exists; preserve prior attempts.')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 checkout is dirty.')
    OUT.mkdir()
    state = {
        'schema': 'p25-cell00-row00-arithmetic-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
        'module_order': [TARGET], 'modules': {}, 'dependency_objects': {}, 'dependency_receipts': {},
        'dependency_modules_compiled': [], 'private_records_written': [], 'fastdet_recompiled_on_P3': False,
        'original_cell00_sha256': INPUT_SHA, 'host_correctness_credit': False,
        'row00_typed_arithmetic_proved': False, 'row00_typed_simplex_valid_proved': False,
        'original_parse_proved_by_this_run': False, 'original_archive_binding_proved_by_this_run': False,
        'original_archive_row00_simplex_valid_proved': False, 'geometric_jensen_binding_proved': False,
        'other_seven_simplex_guards_proved': False, 'all_cell_finite_guards_proved': False,
        'source_cell_membership_proved': False, 'pulling_ownership_proved': False,
        'cellFloorNumerator_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
    }
    frozen = {}
    target_names = {TARGET}


    def write():
        temp = OUT / 'RESULT.tmp'
        temp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
        temp.replace(OUT / 'RESULT.json')

    def bind(path, expected=None):
        path = Path(path)
        actual = digest(path)
        require(expected is None or actual == expected, f'Artifact hash mismatch: {path}')
        require(str(path) not in frozen or frozen[str(path)] == actual, f'Artifact changed during preflight: {path}')
        frozen[str(path)] = actual
        return path

    def artifact(row, expected=None):
        path = bind(row['path'], expected or row['sha256'])
        require(digest(path) == row['sha256'] and path.stat().st_size == row['bytes'], f'Artifact record mismatch: {path}')
        return path

    def check_frozen():
        require(all(digest(path) == h for path, h in frozen.items()), 'Frozen source/object/receipt/log/runtime changed.')

    def stage_log(row, override=None):
        require(row['exit_code'] == 0 and not row.get('timed_out', False), 'Dependency stage did not pass.')
        path = Path(override) if override is not None else Path(row['log'])
        if not path.is_absolute():
            path = ROOT / path
        return bind(path, row['log_sha256'])

    def strict_commands(stages, module, source, object_path, audit_source):
        require(stages['replay']['command'] == [str(CHECKER), '--verbose', module], f'Unexpected replay command: {module}')
        for label in ['normal', 'audit']:
            command = stages[label]['command']
            require(command[0] == str(LEAN) and
                    all(flag in command for flag in ['-t0', '-j1', '-M11264', '-DwarningAsError=true']),
                    f'Non-strict accepted stage: {module}/{label}')
        normal = stages['normal']['command']
        require(Path(normal[-1]) == source and Path(normal[normal.index('-o') + 1]) == object_path,
                f'Normal command/source/object binding mismatch: {module}')
        require(Path(stages['audit']['command'][-1]) == audit_source, f'Audit source binding mismatch: {module}')

    def copy_dependency(module, original, expected, provenance):
        require(module in SOURCES and module not in target_names, f'Refuse a target/unknown dependency object: {module}')
        if module in KNOWN_OBJECTS:
            require(expected == KNOWN_OBJECTS[module], f'Known accepted object identity mismatch: {module}')
        original = bind(original, expected)
        destination = lib / (module.replace('.', '/') + '.olean')
        if module in state['dependency_objects']:
            require(state['dependency_objects'][module]['sha256'] == expected and digest(destination) == expected,
                    f'Conflicting accepted object provenance: {module}')
            return
        require(not destination.exists(), f'Unexpected preexisting dependency object: {module}')
        shutil.copyfile(original, destination)
        bind(destination, expected)
        state['dependency_objects'][module] = {
            'path': str(original), 'sha256': expected, 'isolated_path': str(destination),
            'source_sha256': SOURCES[module]['source_sha256'], 'provenance': provenance,
        }

    def modern_owner(container, receipt_path, module):
        owner = container['modules'][module]
        require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                f'Owner not accepted: {module}')
        require(owner['module'] == module and owner['source_origin']['sha256'] == SOURCES[module]['source_sha256'] and
                owner['source_origin']['commit'] == container['publication_commit'] and
                owner['source_origin']['path'] == SOURCES[module]['path'], f'Accepted source-origin binding mismatch: {module}')
        source = artifact(owner['source_copy'], SOURCES[module]['source_sha256'])
        audit_source = artifact(owner['audit_source'])
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, module), f'Changed complete-audit template: {module}')
        object_path = artifact(owner['object'])
        for label in ['normal', 'replay', 'audit']:
            require(owner['stages'][label]['status'] == 'PASSED', f'Owner stage not marked passed: {module}/{label}')
            stage_log(owner['stages'][label])
        strict_commands(owner['stages'], module, source, object_path, audit_source)
        records, inventory, imports = read_audit(Path(owner['stages']['audit']['log']), module)
        require(records == owner['owned_declarations'] and len(records) == owner['owned_count'] and
                json.loads(artifact(owner['declarations']).read_text()) == records and
                json.loads(artifact(owner['inventory']).read_text()) == inventory and
                owner['actual_project_closure'] == imports, f'Owner inventory/receipt/log mismatch: {module}')
        require(set(SOURCES[module]['public_names']) <= {r['name'] for r in records}, f'Accepted public declarations missing: {module}')
        if module == PAYLOAD:
            require(sorted(r['name'] for r in records) == expected_payload, 'Payload inventory is not exactly all 544 expected names.')
        copy_dependency(module, object_path, owner['object']['sha256'], 'Accepted normal/replay/full-owned owner and complete inventory revalidated')
        state['dependency_receipts'][module] = {
            **record_file(receipt_path), 'owner_accepted': True, 'owner_status': owner['status'],
            'owner_publication': owner['source_origin']['commit'], 'owned_count': len(records),
        }

    def legacy_owner(directory, module, receipt_sha):
        receipt_path = bind(directory / 'RESULT.json', receipt_sha)
        receipt = json.loads(receipt_path.read_text())
        require(receipt['accepted'] is True and receipt['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
                receipt['module'] == module and receipt['source_sha256'] == SOURCES[module]['source_sha256'] and
                receipt['object_sha256'] == KNOWN_OBJECTS[module], f'Legacy accepted owner mismatch: {module}')
        require(hashlib.sha256(receipt['source'].encode()).hexdigest() == SOURCES[module]['source_sha256'],
                f'Legacy embedded source mismatch: {module}')
        source = bind(directory / 'src' / (module.replace('.', '/') + '.lean'), SOURCES[module]['source_sha256'])
        object_path = bind(directory / 'lib' / (module.replace('.', '/') + '.olean'), KNOWN_OBJECTS[module])
        audit_source = bind(directory / 'audit/Audit.lean')
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, module), f'Legacy audit template differs: {module}')
        stages = {label: receipt[label] for label in ['normal', 'replay', 'audit']}
        for label, stage in stages.items():
            stage_log(stage, directory / (label.upper() + '.log'))
        strict_commands(stages, module, source, object_path, audit_source)
        records, _, _ = read_audit(directory / 'AUDIT.log', module)
        require(records == receipt['owned_declarations'] and len(records) == receipt['owned_count'],
                f'Legacy owned inventory differs from receipt: {module}')
        require(set(SOURCES[module]['public_names']) <= {r['name'] for r in records}, f'Legacy public declarations missing: {module}')
        copy_dependency(module, object_path, KNOWN_OBJECTS[module], 'Exact accepted legacy owner receipt, logs and full inventory revalidated')
        state['dependency_receipts'][module] = record_file(receipt_path)
        return receipt

    def accepted_private_dependency(module, row):
        """Reuse the exact accepted private receipt already pinned by FiniteCore."""
        require(module in KNOWN_OBJECTS and row['sha256'] == KNOWN_OBJECTS[module],
                f'Private object identity mismatch: {module}')
        receipt_path = bind(row['receipt'], row['receipt_sha256'])
        receipt = json.loads(receipt_path.read_text())
        require(receipt['accepted'] is True and receipt['module'] == module and
                receipt['source_sha256'] == SOURCES[module]['source_sha256'] and
                receipt['object_sha256'] == row['sha256'], f'Private acceptance binding mismatch: {module}')
        for label in ['replay', 'audit']:
            stage_log(receipt[label])
        require(receipt['replay']['command'] == [str(CHECKER), '--verbose', module],
                f'Private replay command differs: {module}')
        command = receipt['audit']['command']
        require(command[0] == str(LEAN) and
                all(flag in command for flag in ['-t0', '-j1', '-M11264', '-DwarningAsError=true']),
                f'Private audit flags differ: {module}')
        if 'normal' in receipt:
            stage_log(receipt['normal'])
        for name, h in receipt.get('artifacts', {}).items():
            path = Path(name)
            if not path.is_absolute():
                path = ROOT / path if str(path).startswith('.lake/') else receipt_path.parent / path
            bind(path, h)
        copy_dependency(module, row['path'], row['sha256'],
                        'Exact accepted private source/object/receipt and recorded stage artifacts revalidated')
        state['dependency_receipts'][module] = record_file(receipt_path)

    def verify_fastdet_capsule():
        """Validate the immutable P1 receipt and remap its external providers."""
        bind(capsule_transport, transport_sha)
        transport = json.loads(capsule_transport.read_text())
        require(transport['schema'] == 'p25-fastdet-capsule-transport-v1' and
                transport['module'] == FASTDET and transport['accepted'] is True and
                re.fullmatch(r'[0-9a-f]{40}', transport['publication_commit']) and
                transport['source_sha256'] == SOURCES[FASTDET]['source_sha256'],
                'FastDet transport is not an accepted capsule for the exact unchanged source.')
        require(transport['archive']['path'] == 'accepted.tar.gz' and
                transport['result']['path'] == 'RESULT.json' and
                transport['manifest']['path'] == 'CAPSULE_FILES.json', 'Unexpected capsule transport paths.')
        bind(capsule_archive, transport['archive']['sha256'])
        require(capsule_archive.stat().st_size == transport['archive']['bytes'], 'Capsule archive size mismatch.')
        capsule = OUT / 'fastdet-capsule'
        capsule.mkdir()
        mandatory = {
            'RESULT.json', 'SOURCE_PROVENANCE.json', 'RUNTIME.json', 'EXTERNAL_IMPORTS.json',
            'PRE_GATE_EXTERNAL_SNAPSHOT.json',
            'OWNED_DECLARATIONS.json', 'OWNED_INVENTORY.json', 'runner/run_p1_fastdet_cloud.py',
            'src/ImbalancedChen/P2Winner9FastDetPure.lean', 'lib/ImbalancedChen/P2Winner9FastDetPure.olean',
            'audit/Audit.lean', 'logs/NORMAL.log', 'logs/REPLAY.log', 'logs/AUDIT.log',
        }
        allowed = mandatory | {'CAPSULE_FILES.json',
            'lib/ImbalancedChen/P2Winner9FastDetPure.olean.private',
            'lib/ImbalancedChen/P2Winner9FastDetPure.olean.server'}
        with tarfile.open(capsule_archive, 'r:gz') as archive:
            members = archive.getmembers()
            names = [m.name for m in members]
            require(len(names) == len(set(names)) and mandatory | {'CAPSULE_FILES.json'} <= set(names)
                    <= allowed, 'Capsule file inventory has duplicates, missing files or unexpected files.')
            require(sum(m.size for m in members) <= 256 * 1024 * 1024, 'Capsule payload exceeds the transfer bound.')
            for member in members:
                relative = PurePosixPath(member.name)
                require(member.isfile() and not member.issym() and not member.islnk() and
                        not relative.is_absolute() and '..' not in relative.parts and
                        str(relative) == member.name and '\\' not in member.name and
                        member.size <= 64 * 1024 * 1024, f'Unsafe capsule member: {member.name}')
                destination = capsule / member.name
                destination.parent.mkdir(parents=True, exist_ok=True)
                stream = archive.extractfile(member)
                require(stream is not None, f'Missing capsule data: {member.name}')
                with stream, destination.open('xb') as output:
                    shutil.copyfileobj(stream, output)

        def capsule_artifact(row, expected=None):
            relative = PurePosixPath(row['path'])
            require(not relative.is_absolute() and '..' not in relative.parts and
                    str(relative) == row['path'] and row['path'] in allowed,
                    f'Invalid capsule-relative artifact path: {row["path"]}')
            path = bind(capsule / row['path'], expected or row['sha256'])
            require(path.stat().st_size == row['bytes'] and digest(path) == row['sha256'],
                    f'Capsule artifact mismatch: {row["path"]}')
            return path

        manifest_path = capsule_artifact(transport['manifest'])
        manifest = json.loads(manifest_path.read_text())
        files = manifest['files']
        file_names = [r['path'] for r in files]
        require(manifest['schema'] == 'p25-fastdet-capsule-files-v1' and manifest['module'] == FASTDET and
                manifest['publication_commit'] == transport['publication_commit'] and
                len(file_names) == len(set(file_names)) and
                set(file_names) == set(names) - {'CAPSULE_FILES.json'} and
                manifest['excluded_to_avoid_hash_cycles'] ==
                ['CAPSULE_FILES.json', 'accepted.tar.gz', 'CAPSULE_TRANSPORT.json'],
                'Capsule exhaustive file manifest does not match the archive.')
        for row in files:
            capsule_artifact(row)
        receipt_path = capsule_artifact(transport['result'])
        receipt = json.loads(receipt_path.read_text())
        require(receipt['schema'] == 'p25-p1-fastdet-strict-v1' and
                receipt['accepted'] is True and receipt['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
                receipt['module'] == FASTDET and receipt['publication_commit'] == transport['publication_commit'] and
                receipt['capsule_root'] == '/workspace/p25-fastdet-20261126' and
                receipt['strict_flags'] == FLAGS and receipt['stage_wall_limit_seconds'] == 600 and
                receipt['dependency_modules_compiled'] == [] and receipt['host_correctness_credit'] is False and
                receipt['remote_checkout_performed'] is False and receipt['remote_git_object_inspection_performed'] is False,
                'FastDet receipt is not the reviewed strict three-gate owner receipt.')
        require(receipt['expected_project_closure'] == receipt['actual_project_closure'] == [FASTDET] and
                receipt['direct_imports'] == FASTDET_DIRECT_IMPORTS and
                receipt['allowed_transitive_axioms'] == sorted(ALLOWED_AXIOMS), 'FastDet owner scope changed.')
        origin = receipt['source_origin']
        require(origin['commit'] == transport['publication_commit'] and origin['path'] == SOURCES[FASTDET]['path'] and
                origin['sha256'] == SOURCES[FASTDET]['source_sha256'] and origin['bytes'] == 6729 and
                origin['binding_kind'] == 'caller-supplied publication identity with frozen exact-source SHA256' and
                origin['independently_verified_remote_git_object'] is False, 'FastDet source-origin binding differs.')
        source = capsule_artifact(receipt['source_copy'], SOURCES[FASTDET]['source_sha256'])
        require(source.read_bytes() == (ROOT / SOURCES[FASTDET]['path']).read_bytes(),
                'FastDet capsule source differs from the selected P3 publication.')
        object_path = capsule_artifact(receipt['object'], transport['object_sha256'])
        require(receipt['object']['path'] == 'lib/ImbalancedChen/P2Winner9FastDetPure.olean' and
                receipt['source_copy']['path'] == 'src/ImbalancedChen/P2Winner9FastDetPure.lean',
                'FastDet source/object module paths differ.')
        audit_source = capsule_artifact(receipt['audit_source'])
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, FASTDET) and
                receipt['audit_source']['path'] == 'audit/Audit.lean' and
                receipt['audit_template_origin']['sha256'] == digest(audit_template_path),
                'FastDet complete-audit template differs.')
        capsule_artifact(receipt['runner'], P1_RUNNER_SHA)
        provenance = json.loads(capsule_artifact(receipt['source_provenance']).read_text())
        require(provenance['schema'] == 'p25-caller-source-transport-v1' and
                provenance['source_origin'] == origin and provenance['source_copy'] == receipt['source_copy'] and
                provenance['source_bytes_verified'] is True and
                provenance['remote_checkout_performed'] is False and provenance['remote_git_object_inspection_performed'] is False,
                'FastDet source provenance record differs.')

        p1_root = Path(receipt['capsule_root'])
        require(set(receipt['stages']) == {'normal', 'replay', 'audit'}, 'FastDet stage inventory differs.')
        expected_commands = {
            'normal': [str(LEAN), *FLAGS, '--root=' + str(p1_root / 'src'), '-o',
                       str(p1_root / receipt['object']['path']), str(p1_root / receipt['source_copy']['path'])],
            'replay': [str(CHECKER), '--verbose', FASTDET],
            'audit': [str(LEAN), *FLAGS, '--root=' + str(p1_root / 'audit'), str(p1_root / 'audit/Audit.lean')],
        }
        for label in ['normal', 'replay', 'audit']:
            stage = receipt['stages'][label]
            require(stage['status'] == 'PASSED' and stage['exit_code'] == 0 and stage['timed_out'] is False and
                    stage['command'] == expected_commands[label] and stage['cwd'] == str(p1_root) and
                    stage['wall_limit_seconds'] == 600 and stage['log'] == 'logs/' + label.upper() + '.log',
                    f'FastDet stage/command binding differs: {label}')
            capsule_artifact({'path': stage['log'], 'sha256': stage['log_sha256'], 'bytes': stage['log_bytes']})
        records, inventory, imports = read_audit(capsule / 'logs/AUDIT.log', FASTDET)
        require(records == receipt['owned_declarations'] and len(records) == receipt['owned_count'] and
                json.loads(capsule_artifact(receipt['declarations']).read_text()) == records and
                json.loads(capsule_artifact(receipt['inventory']).read_text()) == inventory and
                imports == receipt['actual_project_closure'] and
                set(SOURCES[FASTDET]['public_names']) <= {r['name'] for r in records} and
                receipt['required_owned_names'] == [FASTDET + '.fastDet', FASTDET + '.fastDet_eq'],
                'FastDet complete owned inventory differs from log, serialized data or receipt.')

        runtime = json.loads(capsule_artifact(receipt['runtime']).read_text())
        require(runtime['schema'] == 'p25-p1-fastdet-runtime-v1' and runtime['strict_flags'] == FLAGS and
                runtime['stage_wall_limit_seconds'] == 600, 'FastDet runtime schema/strict flags differ.')
        tc, ml = runtime['toolchain'], runtime['mathlib']
        require(tc['expected_commit'] == LEAN_COMMIT and '4.33.0-rc1' in tc['version'] and
                (LEAN_COMMIT in tc['version'] or LEAN_COMMIT[:7] in tc['version']) and
                tc['root'] == str(LEAN.parent.parent) and tc['compiled_lib'] == str(LEAN.parent.parent / 'lib/lean'),
                'P1/P3 Lean runtime identity differs.')
        for name, binary in [('lean', LEAN), ('leanchecker', CHECKER)]:
            require(tc[name]['path'] == str(binary) and tc[name]['bytes'] == binary.stat().st_size,
                    f'FastDet runtime binary record differs: {name}')
            bind(binary, tc[name]['sha256'])
        require(ml['git_commit'] == ml['expected_git_commit'] == MATHLIB_PIN and
                ml['manifest']['sha256'] == MATHLIB_MANIFEST_SHA and
                set(runtime['packages']) == set(PACKAGE_PINS), 'FastDet Mathlib or package pins differ.')
        mathlib_root = Path(state['runtime']['mathlib_path'])
        require(git('rev-parse', 'HEAD', cwd=mathlib_root) == MATHLIB_PIN,
                'Current P3 Mathlib source pin differs from P1.')
        for row, current in [(ml['manifest'], mathlib_root / 'lake-manifest.json'),
                             (ml['lean_toolchain'], mathlib_root / 'lean-toolchain')]:
            bind(current, row['sha256'])
            require(current.stat().st_size == row['bytes'], 'P1/P3 Mathlib metadata size differs.')
        require((mathlib_root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0-rc1' and
                {r['name']: r['rev'] for r in json.loads((mathlib_root / 'lake-manifest.json').read_text())['packages']} ==
                PACKAGE_PINS, 'P3 Mathlib package manifest differs.')
        provider_roots = {'toolchain': LEAN.parent.parent / 'lib/lean',
                          'mathlib': mathlib_root / '.lake/build/lib/lean'}
        package_pins = {}
        for name, pin in PACKAGE_PINS.items():
            row = runtime['packages'][name]
            require(row['git_commit'] == row['expected_git_commit'] == pin, f'P1 package pin differs: {name}')
            root = mathlib_root / '.lake/packages' / name
            require(root.is_dir() and git('rev-parse', 'HEAD', cwd=root) == pin, f'P3 package pin differs: {name}')
            package_pins[name] = {'path': str(root), 'git_commit': pin}
            compiled = root / '.lake/build/lib/lean'
            if row['compiled_lib'] is not None:
                provider_roots['package:' + name] = compiled
        require(set(provider_roots) == set(runtime['providers']), 'Capsule provider inventory differs from its runtime.')
        all_P3_roots = {'toolchain': LEAN.parent.parent / 'lib/lean',
                        'mathlib': mathlib_root / '.lake/build/lib/lean',
                        **{'package:' + name: mathlib_root / '.lake/packages' / name / '.lake/build/lib/lean'
                           for name in PACKAGE_PINS}}
        effective_P3_providers = {name: path for name, path in all_P3_roots.items()
                                  if name == 'toolchain' or str(path) in tails}
        require(set(tails) == {str(path) for name, path in effective_P3_providers.items() if name != 'toolchain'} and
                all(path.is_dir() and not (path / 'ImbalancedChen').exists() for path in effective_P3_providers.values()),
                'P3 effective external paths contain an unknown/missing provider or project-object fallback.')

        external = json.loads(capsule_artifact(receipt['external_imports']).read_text())
        require(receipt['external_pre_gate_snapshot']['path'] == 'PRE_GATE_EXTERNAL_SNAPSHOT.json' and
                receipt['external_pre_gate_snapshot'] == external['external_pre_gate_snapshot'] and
                external['all_actual_imports_match_pre_gate_snapshot'] is True,
                'FastDet pre-gate external snapshot binding is missing or inconsistent.')
        before = json.loads(capsule_artifact(receipt['external_pre_gate_snapshot']).read_text())
        before_entries = before['entries']
        before_keys = [(row['provider'], row['relative_path']) for row in before_entries]
        before_start = datetime.fromisoformat(before['started_utc'])
        before_end = datetime.fromisoformat(before['finished_utc'])
        normal_start = datetime.fromisoformat(receipt['stages']['normal']['started_utc'])
        require(before['schema'] == 'p25-external-olean-before-snapshot-v1' and before['module'] == FASTDET and
                before['provider_roots'] == external['provider_roots'] and
                len(before_keys) == len(set(before_keys)) == before['file_count'] and before_keys and
                all(t.tzinfo is not None for t in [before_start, before_end, normal_start]) and
                before_start <= before_end <= normal_start,
                'FastDet complete external snapshot inventory/timing differs.')
        before_index = {}
        for row in before_entries:
            provider, relative = row['provider'], row['relative_path']
            relative_path = PurePosixPath(relative)
            require(provider in provider_roots and not relative_path.is_absolute() and
                    '..' not in relative_path.parts and str(relative_path) == relative and
                    relative.endswith(('.olean', '.olean.private', '.olean.server')) and
                    Path(row['path']) == Path(external['provider_roots'][provider]) / relative and
                    isinstance(row['bytes'], int) and row['bytes'] >= 0 and re.fullmatch(r'[0-9a-f]{64}', row['sha256']),
                    'Malformed pre-gate external file record.')
            before_index[(provider, relative)] = row
        audit_imports = [json.loads(line.removeprefix('P0_QUEUE_IMPORTS '))
                         for line in (capsule / 'logs/AUDIT.log').read_text().splitlines()
                         if line.startswith('P0_QUEUE_IMPORTS ')][0]
        expected_external = set(audit_imports) - {FASTDET}
        entries = external['entries']
        names = [row['module'] for row in entries]
        require(len(audit_imports) == len(set(audit_imports)) and
                external['schema'] == 'p25-external-olean-closure-v1' and external['module'] == FASTDET and
                external['actual_project_closure'] == [FASTDET] and
                external['source_direct_imports'] == FASTDET_DIRECT_IMPORTS and
                external['audit_direct_extra_imports'] == ['Lean.Util.CollectAxioms'] and
                external['audit_environment_imports'] == sorted(audit_imports) and
                len(names) == len(set(names)) == external['external_module_count'] == receipt['external_module_count'] and
                set(names) == expected_external and set(FASTDET_DIRECT_IMPORTS) <= expected_external and
                external['provider_roots'] == {k: v['compiled_lib'] for k, v in runtime['providers'].items()},
                'FastDet complete external object inventory differs from the audited import environment.')
        external_bindings = []
        for row in entries:
            module, provider = row['module'], row['provider']
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module) and
                    not module.startswith('ImbalancedChen.') and provider in provider_roots,
                    f'Unexpected external module/provider: {module}')
            relative = module.replace('.', '/') + '.olean'
            require(row['relative_path'] == relative and
                    Path(row['path']) == Path(external['provider_roots'][provider]) / relative,
                    f'FastDet external path/module binding differs: {module}')
            before_row = before_index.get((provider, relative))
            require(before_row is not None and
                    all(row[k] == before_row[k] for k in ['path', 'bytes', 'sha256']),
                    f'FastDet actual import differs from its pre-gate snapshot: {module}')
            before_providers = [name for name in external['provider_roots'] if (name, relative) in before_index]
            require(before_providers == [provider], f'FastDet pre-gate imported module was missing or shadowed: {module}')
            providers = [k for k, root in effective_P3_providers.items() if (root / relative).is_file()]
            require(providers == [provider], f'P3 external module is missing or shadowed: {module}')
            current = bind(provider_roots[provider] / relative, row['sha256'])
            require(current.stat().st_size == row['bytes'], f'P1/P3 external object size differs: {module}')
            companions = row['companions']
            companion_names = [r['relative_path'] for r in companions]
            require(len(companion_names) == len(set(companion_names)) and
                    set(companion_names) <= {relative + '.private', relative + '.server'},
                    f'Unexpected external companion inventory: {module}')
            current_companions = {relative + suffix for suffix in ['.private', '.server']
                                  if (provider_roots[provider] / (relative + suffix)).is_file()}
            before_companions = {relative + suffix for suffix in ['.private', '.server']
                                 if (provider, relative + suffix) in before_index}
            require(set(companion_names) == current_companions == before_companions,
                    f'Pre-gate/P1/P3 external companions differ: {module}')
            for companion in companions:
                require(Path(companion['path']) == Path(external['provider_roots'][provider]) / companion['relative_path'],
                        f'P1 companion path binding differs: {module}')
                path = bind(provider_roots[provider] / companion['relative_path'], companion['sha256'])
                require(path.stat().st_size == companion['bytes'], f'P1/P3 companion size differs: {module}')
                prior = before_index[(provider, companion['relative_path'])]
                require(all(companion[k] == prior[k] for k in ['path', 'bytes', 'sha256']),
                        f'FastDet companion differs from its pre-gate snapshot: {module}')
            external_bindings.append({'module': module, 'provider': provider, 'path': str(current),
                                      'sha256': row['sha256']})
        require(receipt['external_direct_imports_before_gates'] ==
                [next(row for row in entries if row['module'] == m) for m in FASTDET_DIRECT_IMPORTS],
                'FastDet direct import fingerprints changed between pre-gate and complete closure capture.')
        original_frozen = {str(p1_root / row['path']): row['sha256'] for row in files if row['path'] != 'RESULT.json'}
        materialized = provenance['materialized_input']
        require(materialized['bytes'] == 6729 and materialized['sha256'] == SOURCES[FASTDET]['source_sha256'],
                'FastDet materialized source hash differs.')
        for row in [materialized, tc['lean'], tc['leanchecker'], ml['manifest'], ml['lean_toolchain']]:
            original_frozen[row['path']] = row['sha256']
        for row in entries:
            original_frozen[row['path']] = row['sha256']
            for companion in row['companions']:
                original_frozen[companion['path']] = companion['sha256']
        require(receipt['frozen_files_sha256'] == original_frozen,
                'FastDet complete frozen snapshot differs from capsule, runtime or import records.')
        copy_dependency(FASTDET, object_path, transport['object_sha256'],
                        'Transferred exact P1 normal/replay/complete-owned capsule; no P3 dependency compilation')
        companions = receipt['object_companions']
        companion_names = [r['path'] for r in companions]
        require(len(companion_names) == len(set(companion_names)) and
                set(companion_names) == set(file_names) - mandatory,
                'FastDet project-object companions differ from capsule manifest.')
        for row in companions:
            original = capsule_artifact(row)
            destination = lib / PurePosixPath(row['path']).relative_to('lib')
            require(not destination.exists(), 'FastDet companion unexpectedly already exists.')
            shutil.copyfile(original, destination)
            bind(destination, row['sha256'])
        state['dependency_objects'][FASTDET]['companions'] = companions
        state['dependency_receipts'][FASTDET] = record_file(receipt_path)
        state['fastdet_capsule'] = {
            'transport': record_file(capsule_transport), 'archive': record_file(capsule_archive),
            'manifest': record_file(manifest_path), 'result': record_file(receipt_path),
            'pre_gate_external_snapshot': receipt['external_pre_gate_snapshot'],
            'publication_commit': transport['publication_commit'], 'owned_count': len(records),
            'source_matches_selected_P3_publication': True, 'external_module_count': len(entries),
            'external_bindings': external_bindings, 'P3_package_pins': package_pins,
            'recompiled_on_P3': False, 'runner_sha256': P1_RUNNER_SHA,
        }


    def run_stage(owner, label, command, log):
        require(owner['module'] == TARGET, 'Only Row00Arithmetic may be compiled by this runner.')
        check_frozen()

        start = time.monotonic()
        row = {'command': command, 'status': 'RUNNING', 'started_utc': now(), 'log': str(log)}
        owner['stages'][label] = row
        write()
        print('P25_ROW00_STAGE_START', owner['module'], label, flush=True)
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
        row.update(status='PASSED' if code == 0 else 'FAILED', exit_code=code, timed_out=timed_out,
                   seconds=round(time.monotonic() - start, 3), ended_utc=now(),
                   log_sha256=digest(log), log_bytes=log.stat().st_size)
        write()
        print('P25_ROW00_STAGE_RESULT', owner['module'], label,
              json.dumps({k: row[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}), flush=True)
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=owner['module'], failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{owner["module"]} {label} failed with exit {code}.')
        check_frozen()

    write()
    try:
        payload_path = bind(PAYLOAD_FLOORS / 'RESULT.json', PAYLOAD_RESULT_SHA)
        payload_receipt = json.loads(payload_path.read_text())
        require(payload_receipt['accepted'] is True and
                payload_receipt['status'] == 'PAYLOAD_AND_STORED_FLOORS_ACCEPTED_BINDINGS_PENDING' and
                set(payload_receipt['modules']) == {PAYLOAD, FLOORS} and
                all(payload_receipt['modules'][m]['accepted'] is True for m in [PAYLOAD, FLOORS]) and
                payload_receipt['dependency_modules_compiled'] == [] and
                re.fullmatch(r'[0-9a-f]{40}', payload_receipt['publication_commit']),
                'The exact accepted payload/floors receipt is required; no failed/pending fallback.')
        state['initial_P3_publication'] = git('rev-parse', 'HEAD')
        if state['initial_P3_publication'] != publication:
            with (OUT / 'PUBLICATION.log').open('wb') as stream:
                subprocess.run(['git', 'fetch', '--no-tags', 'origin', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
                subprocess.run(['git', 'checkout', '--detach', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Target publication mismatch/dirty.')
        state['publication_checked_out'] = publication
        base_path = bind(BASE / 'RESULT.json', BASE_RESULT_SHA)
        base = json.loads(base_path.read_text())
        snapshot = base['normal_snapshot_before']
        require(snapshot['mathlib_pin'] == MATHLIB_PIN and
                git('rev-parse', 'HEAD', cwd=Path(snapshot['mathlib_path'])) == MATHLIB_PIN, 'Mathlib pin mismatch.')
        for binary in [LEAN, CHECKER]:
            bind(binary, snapshot['files'][str(binary)]['sha256'])
        state['runtime'] = {'lean': record_file(LEAN), 'leanchecker': record_file(CHECKER),
                            'mathlib_pin': MATHLIB_PIN, 'mathlib_path': snapshot['mathlib_path']}
        require(payload_receipt['runtime'] == state['runtime'], 'Payload/Floors runtime differs from the accepted P3 baseline.')
        state['runtime_context_receipt'] = record_file(base_path)
        src, lib, audit = OUT / 'src', OUT / 'lib', OUT / 'audit'
        for directory in [src / 'ImbalancedChen', lib / 'ImbalancedChen', audit]:
            directory.mkdir(parents=True)
        tails = base['approved_LEAN_PATH'].split(':')[1:]
        require(tails and len(tails) == len(set(tails)) and all(p and Path(p).is_dir() and
                             Path(p).resolve().is_relative_to(Path('/mathlib').resolve()) and
                             not (Path(p) / 'ImbalancedChen').exists() for p in tails), 'Unexpected Mathlib/project fallback path.')
        env = dict(os.environ)
        env.pop('LEAN_SRC_PATH', None)
        env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
        env['LEAN_PATH'] = ':'.join([str(lib), *tails])
        env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')
        state.update(approved_LEAN_PATH=env['LEAN_PATH'], isolated_library=str(lib), isolated_source_root=str(src))

        manifest_path = bind(ROOT / PACKAGE / 'MANIFEST.json', MANIFEST_SHA)
        manifest = json.loads(manifest_path.read_text())
        require(manifest['schema'] == 'p25-cell00-row00-arithmetic-source-candidate-v1' and
                manifest['candidate']['module'] == TARGET and manifest['candidate']['public_source_declaration_count'] == 15,
                'The row00 candidate manifest differs.')
        for module, source_spec in SOURCES.items():
            path = bind(ROOT / source_spec['path'], source_spec['source_sha256'])
            published = subprocess.check_output(['git', 'show', f'{publication}:{source_spec["path"]}'], cwd=ROOT, timeout=120)
            require(published == path.read_bytes(), f'Source is not exact publication bytes: {module}')
            imports = [n for line in re.findall(r'^import\s+([^\n]+)$', path.read_text(), re.M)
                       for n in line.split() if n.startswith('ImbalancedChen.')]
            require(imports == source_spec['project_imports'], f'Frozen source import graph mismatch: {module}')
            namespace = source_spec.get('public_namespace')
            public = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)', path.read_text(), re.M)
            source_spec['public_names'] = [namespace + '.' + name for name in public] if namespace else []
        candidate = manifest['candidate']
        require(candidate['path'] == SOURCES[TARGET]['path'] and candidate['sha256'] == SOURCES[TARGET]['source_sha256'] and
                (ROOT / candidate['path']).stat().st_size == candidate['bytes'] == 5254 and
                [TARGET + '.' + n for n in candidate['public_source_declarations']] == SOURCES[TARGET]['public_names'] and
                len(SOURCES[TARGET]['public_names']) == len(set(SOURCES[TARGET]['public_names'])) == 15,
                'Row00 source/public inventory differs from its frozen candidate.')
        state['row00_manifest'] = record_file(manifest_path)
        state['source_graph'] = SOURCES
        state['expected_project_imports_by_owner'] = {TARGET: sorted(project_closure(TARGET))}
        for relative, expected in [
            ('docs/verification/20261126-p2-5-continuation/run_p1_fastdet_cloud.py', P1_RUNNER_SHA),
            ('docs/verification/20261126-p2-5-continuation/P1_FASTDET_CAPSULE_CONTRACT.json', P1_CONTRACT_SHA),
        ]:
            path = bind(ROOT / relative, expected)
            published = subprocess.check_output(['git', 'show', f'{publication}:{relative}'], cwd=ROOT, timeout=120)
            require(published == path.read_bytes(), 'P1 runner/contract is not the selected publication version.')
        state['P1_capsule_contract'] = record_file(ROOT / 'docs/verification/20261126-p2-5-continuation/P1_FASTDET_CAPSULE_CONTRACT.json')

        payload_files_path = bind(ROOT / 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_FILES.json', PAYLOAD_FILES_SHA)
        payload_files = json.loads(payload_files_path.read_text())
        expected_payload = sorted(payload_files['expected_owned_names'])
        require(payload_files['module'] == PAYLOAD and payload_files['expected_owned_declarations'] ==
                len(expected_payload) == len(set(expected_payload)) == 544, 'Payload expected inventory differs.')
        for row in payload_files['files']:
            bind(ROOT / row['path'], row['sha256'])
        audit_template_path = bind(ROOT / payload_files['audit_file'])
        audit_template = audit_template_path.read_text()
        state['audit_template'] = record_file(audit_template_path)

        # Revalidate the original accepted receipts. The P3 dependency library is
        # populated solely by copies of these immutable objects, never a compiler.
        for path, h in payload_receipt['frozen_inputs'].items():
            bind(path, h)
        core_receipt = legacy_owner(FINITE_CORE, CORE_OWNER, FINITE_CORE_RECEIPT_SHA)
        require(set(core_receipt['dependencies']) == project_closure(CORE_OWNER) - {CORE_OWNER},
                'FiniteCore accepted dependency set differs from its exact project closure.')
        for module, row in core_receipt['dependencies'].items():
            accepted_private_dependency(module, row)
        require(set(payload_receipt['dependency_objects']) == project_closure(PAYLOAD) - {PAYLOAD},
                'Payload accepted dependency set differs from its exact project closure.')
        for module, row in payload_receipt['dependency_objects'].items():
            core_row = core_receipt['dependencies'][module]
            require(row['source_sha256'] == SOURCES[module]['source_sha256'] and
                    row['sha256'] == state['dependency_objects'][module]['sha256'] == core_row['sha256'] and
                    row['receipt'] == core_row['receipt'] and row['receipt_sha256'] == core_row['receipt_sha256'],
                    f'Accepted Payload and FiniteCore dependency identities differ: {module}')
            bind(row['path'], row['sha256'])
            bind(row['isolated_path'], row['sha256'])
        modern_owner(payload_receipt, payload_path, PAYLOAD)
        modern_owner(payload_receipt, payload_path, FLOORS)
        state['payload_floors_receipt'] = record_file(payload_path)
        verify_fastdet_capsule()

        needed = project_closure(TARGET) - {TARGET}
        require(set(state['dependency_objects']) == needed and len(needed) == 8 and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 8,
                'The isolated library must contain exactly eight accepted dependency objects.')
        source = src / (TARGET.replace('.', '/') + '.lean')
        object_path = lib / (TARGET.replace('.', '/') + '.olean')
        audit_path = audit / 'Audit.lean'
        require(not object_path.exists(), 'Target object already exists; refuse a stale row00 proof.')
        source.write_bytes((ROOT / SOURCES[TARGET]['path']).read_bytes())
        bind(source, SOURCES[TARGET]['source_sha256'])
        audit_path.write_text(audit_template.replace(PAYLOAD, TARGET))
        bind(audit_path)
        owner = {
            'module': TARGET, 'status': 'PENDING', 'accepted': False,
            'source_origin': {'commit': publication, 'path': SOURCES[TARGET]['path'], 'sha256': SOURCES[TARGET]['source_sha256']},
            'source_copy': record_file(source), 'audit_source': record_file(audit_path),
            'required_owned_names': SOURCES[TARGET]['public_names'], 'stages': {},
        }
        state['modules'][TARGET] = owner
        state.update(status='VERIFYING_ROW00_ARITHMETIC', frozen_inputs=dict(frozen))
        check_frozen()
        write()
        directory = OUT / TARGET.split('.')[-1]
        directory.mkdir()
        for label, command in [
            ('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(object_path), str(source)]),
            ('replay', [str(CHECKER), '--verbose', TARGET]),
            ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(audit_path)]),
        ]:
            run_stage(owner, label, command, directory / (label.upper() + '.log'))
            if label == 'normal':
                bind(object_path)
                owner['object'] = record_file(object_path)
                state['frozen_inputs'] = dict(frozen)
                write()
        records, inventory, imports = read_audit(directory / 'AUDIT.log', TARGET)
        require(set(owner['required_owned_names']) <= {r['name'] for r in records}, 'Required public row00 declarations missing.')
        declarations_path, inventory_path = directory / 'OWNED_DECLARATIONS.json', directory / 'OWNED_INVENTORY.json'
        declarations_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n')
        inventory_path.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + '\n')
        owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                     owned_count=len(records), owned_declarations=records, actual_project_closure=imports,
                     declarations=record_file(declarations_path), inventory=record_file(inventory_path), ended_utc=now())
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Publication changed during verification.')
        require(git('rev-parse', 'HEAD', cwd=Path(state['runtime']['mathlib_path'])) == MATHLIB_PIN,
                'Mathlib pin changed during verification.')
        for row in state['fastdet_capsule']['P3_package_pins'].values():
            require(git('rev-parse', 'HEAD', cwd=Path(row['path'])) == row['git_commit'],
                    'External package pin changed during verification.')
        require(state['dependency_modules_compiled'] == [] and state['fastdet_recompiled_on_P3'] is False,
                'Unexpected dependency compilation occurred.')
        check_frozen()
        state.update(status='TYPED_PAYLOAD_ROW00_ARITHMETIC_ACCEPTED', accepted=True,
                     row00_typed_arithmetic_proved=True, row00_typed_simplex_valid_proved=True, ended_utc=now())
        write()
        print('P25_ROW00_RESULT', json.dumps({
            'status': state['status'], 'accepted': True, 'owned_count': len(records),
            'row00_typed_simplex_valid_proved': True, 'original_archive_row00_simplex_valid_proved': False,
            'geometric_jensen_binding_proved': False, 'all_cell_finite_guards_proved': False,
            'Q96_proved': False, 'P2_5_proved': False,
            'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json'),
        }, sort_keys=True), flush=True)
    except BaseException as exc:
        if state['status'] != 'MODULE_STAGE_FAILED':
            state['status'] = 'FAILED'
        state.update(accepted=False, error=f'{type(exc).__name__}: {exc}', ended_utc=now())
        (OUT / 'RUNNER_EXCEPTION.log').write_text(traceback.format_exc())
        state['exception_log'] = record_file(OUT / 'RUNNER_EXCEPTION.log')
        write()
        print('P25_ROW00_FAILED', json.dumps({'status': state['status'], 'error': state['error'][:1800],
              'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json')}, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
