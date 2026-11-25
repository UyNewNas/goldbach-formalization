#!/usr/bin/env python3
"""Strict consumer-only P3 run; materialize this file and pass a publication SHA.

Compile only the three selected consumer owners. Every dependency must already
be accepted. The failed monolithic same-name Decoded owner is never copied.
One isolated object root is used for all three new owners and their dependencies.
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
OUT = ROOT / '.lake/diagnostic/p25-cell00-consumers-attempt001'
FIELD = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt002'
PRIOR_FIELD = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt001'
PRIOR_FIELD_RESULT_SHA = '86afeed917a3361c5457db1b7b3f4546d2e513531288adfab3d3a196ad38eac1'
PRIOR_FIELD_SOURCE_SHA = 'c62cf0315fafe2733393627137963dcb507827c988a49115add3a11422a244ed'
FIELD_TARGET = 'ImbalancedChen.P2Saving16Cell00FieldDecode'
REUSED_FIELD_OBJECTS = {
    'ImbalancedChen.P2Saving16Cell00PayloadBinding': 'f1bff7f79f8e43f8a98e5eca39b520b928b46016a297af9272a6cb2b65f065c8',
    'ImbalancedChen.P2OriginalSaving16DecoderCompose': 'df91e32fa010265bb3ad1dba9f317233ce9c1b48beb0c668e5bca70666c452ed',
    'ImbalancedChen.P2Saving16Cell00ScalarDecode': '6a313fad2e0bb6a42a0a73e8f0c5c3360576b10e6de8f34511139711a6e64aeb',
}
PAYLOAD_FLOORS = ROOT / '.lake/diagnostic/p25-payload-floors-attempt001'
ORIGINAL_JSON = ROOT / '.lake/diagnostic/p25-cell00-original-json-attempt001'
FINITE_CORE = ROOT / '.lake/diagnostic/p25-finite-core-attempt001'
BASE = ROOT / '.lake/diagnostic/p25-cell00-canonical-attempt001/charparse'
PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-consumer')
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
MANIFEST_SHA = '3af0b2dbc64d7e336fc7d653235fa6e75b1ec4f4e4902c1c7e482e7e86c18e52'
BASE_RESULT_SHA = '4dca8c2c7b42feb027895420ddb62e0a314d5f6f440d8b772704eeb146ba37eb'
PAYLOAD_RESULT_SHA = '090463b93761d31023f39111c32522e1f2bb3cbcec46e606f7fc429d69d4a204'
ORIGINAL_JSON_RECEIPT_SHA = '6e40751427d4ed696d0587dc560bf91ee9c465d7b30b77838ee1135fa9a13c14'
FINITE_CORE_RECEIPT_SHA = 'b1f2a463ed670e01335244dc35f1e0a3614ced20bbea791a5a5d72e980e95dd9'
PAYLOAD_FILES_SHA = '76aa078eef969fa6c8d8270529f3d68f50b4bb6762626ba14a484423bbdc4321'
PAYLOAD = 'ImbalancedChen.P2Saving16Cell00TypedPayload'
FLOORS = 'ImbalancedChen.P2Saving16Cell00StoredFloors'
JSON_OWNER = 'ImbalancedChen.P2Saving16Cell00OriginalJson'
CORE_OWNER = 'ImbalancedChen.P2OriginalSaving16FiniteCore'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
KNOWN_OBJECTS = {
    'ImbalancedChen.P2OriginalSaving16Decoder': 'fd25815778e3bae5518d3fcc6a5461724b64251f91c4c08e61312fbae4987b39',
    'ImbalancedChen.P2OriginalSaving16Q96FloorCore': '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9',
    'ImbalancedChen.P2OriginalSaving19SourceJson': '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7',
    'ImbalancedChen.P2Saving16StringCharBinding00': 'a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a',
    'ImbalancedChen.P2OriginalSaving19SourceJsonFuel': '9928b1cd0dd91cc93ff2055f00d0d147d455dd8d27783cf110e58df3d61bd088',
    'ImbalancedChen.P2Saving16Cell00DirectParse': '52cf731b62270e0fdfee8468d813aacfe373853e51035b88c669dd8713393f2a',
    'ImbalancedChen.P2OriginalSaving16OriginalInput': '72488821ccb01dec90188d2f09b0e3a73c0087b54c6c4bae4410a109b6f82f91',
    'ImbalancedChen.P2Saving16CanonicalCell00Binding': 'fa7ad4fd4333a9e4fc13fb64448b91db539d65ecf51c6d572e98322e2ccd1837',
    'ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge': '58bedf6929e16767ea9283b0385f168765bd206d8dbe959ce8527bbeb663015d',
    'ImbalancedChen.P2Saving16Cell00SegmentedParse': 'a24cfc8ab4abd43bfb422e6d0b40dc19a43315eba90a96101523150a44715106',
    JSON_OWNER: 'a1c280a1f6724e6fb7895f474a4a3f02ab7adcbf9b8c178efbedd97b24cc2e62',
    CORE_OWNER: '83923cb30eed3a39509324af01988e9708005913b304bb63fd2f56dcee82604c',
}
FIELD_OWNERS = [
    'ImbalancedChen.P2Saving16Cell00PayloadBinding',
    'ImbalancedChen.P2OriginalSaving16DecoderCompose',
    'ImbalancedChen.P2Saving16Cell00ScalarDecode',
    'ImbalancedChen.P2Saving16Cell00FieldDecode',
]
EXTRA_JSON_DEPENDENCIES = [
    'ImbalancedChen.P2OriginalSaving16OriginalInput',
    'ImbalancedChen.P2Saving16CanonicalCell00Binding',
    'ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge',
    'ImbalancedChen.P2Saving16Cell00SegmentedParse',
]

# Prepared from the selected immutable source files, including their imports.
SOURCES = {'ImbalancedChen.P2Saving16Cell00Decoded': {'path': 'docs/source-only/20261126-p2-5-cell00-consumer/ImbalancedChen/P2Saving16Cell00Decoded.lean',
                                            'source_sha256': 'c91601b44d5b88f753ec2d7beb340a6161269c219bfe366690afdb5a6b3b9e6c',
                                            'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldDecode',
                                                                'ImbalancedChen.P2Saving16Cell00PayloadBinding'],
                                            'public_namespace': 'ImbalancedChen.P2Saving16Cell00Decoded'},
 'ImbalancedChen.P2Saving16Cell00FieldDecode': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00FieldDecode.lean',
                                                'source_sha256': '3bca40fbe7f5484ce50da650d9c505026e1634f0c0accdcda3dfe93ab5698b96',
                                                'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderCompose',
                                                                    'ImbalancedChen.P2Saving16Cell00ScalarDecode'],
                                                'public_namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode'},
 'ImbalancedChen.P2OriginalSaving16DecoderCompose': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2OriginalSaving16DecoderCompose.lean',
                                                     'source_sha256': 'b651fb5defedcee7dea0b0b9beee106a984b8ef59bf27104b579fb453faa7e36',
                                                     'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderChars'],
                                                     'public_namespace': 'ImbalancedChen.P2OriginalSaving16OriginalArchive'},
 'ImbalancedChen.P2OriginalSaving16DecoderChars': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2OriginalSaving16DecoderChars.lean',
                                                   'source_sha256': '01b1e5cff72305ab75aa1feb7c5574469ddfbd51af40cc012d75464a44473ca5',
                                                   'project_imports': ['ImbalancedChen.P2OriginalSaving16Decoder']},
 'ImbalancedChen.P2OriginalSaving16Decoder': {'path': 'ImbalancedChen/P2OriginalSaving16Decoder.lean',
                                              'source_sha256': 'e1b23e3de928a97c411d1c6aa73f2059b204d7b9f297105edcd591916b9aee80',
                                              'project_imports': ['ImbalancedChen.P2OriginalSaving16Q96FloorCore',
                                                                  'ImbalancedChen.P2OriginalSaving19SourceJson']},
 'ImbalancedChen.P2OriginalSaving16Q96FloorCore': {'path': 'ImbalancedChen/P2OriginalSaving16Q96FloorCore.lean',
                                                   'source_sha256': '9a456807e6c3a167fd12c1c6e5db492d6c54fd700a1de122ea492774f697c778',
                                                   'project_imports': []},
 'ImbalancedChen.P2OriginalSaving19SourceJson': {'path': 'ImbalancedChen/P2OriginalSaving19SourceJson.lean',
                                                 'source_sha256': 'd58e22ba7e2d92b6c9f2d139993361ae9b827d25d6869fcf38f3837ba7bc3d02',
                                                 'project_imports': []},
 'ImbalancedChen.P2Saving16Cell00ScalarDecode': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00ScalarDecode.lean',
                                                 'source_sha256': 'ba4424e7db6a4efdcd88278b80c129e15cb9049e193adbf7f0e95825964bb9f3',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderChars',
                                                                     'ImbalancedChen.P2Saving16Cell00TypedPayload'],
                                                 'public_namespace': 'ImbalancedChen.P2Saving16Cell00ScalarDecode'},
 'ImbalancedChen.P2Saving16Cell00TypedPayload': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00TypedPayload.lean',
                                                 'source_sha256': 'e92848bd075bf82fe7325bd46e3ddcde937cba277387d46a3579560c27aa287b',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16Decoder'],
                                                 'public_namespace': 'ImbalancedChen.P2Saving16Cell00TypedPayload'},
 'ImbalancedChen.P2Saving16Cell00PayloadBinding': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00PayloadBinding.lean',
                                                   'source_sha256': '61722aa2f8d764fa757245784217e2f9cd9442393333cb594e334b1883425c1b',
                                                   'project_imports': ['ImbalancedChen.P2Saving16Cell00TypedPayload',
                                                                       'ImbalancedChen.P2Saving16Cell00DirectParse'],
                                                   'public_namespace': 'ImbalancedChen.P2Saving16Cell00PayloadBinding'},
 'ImbalancedChen.P2Saving16Cell00DirectParse': {'path': 'docs/source-only/20261126-p2-5-cell00-segmented/ImbalancedChen/P2Saving16Cell00DirectParse.lean',
                                                'source_sha256': 'fa1c92a5fd127b913958a6a10373e8a041433ac74a4a8c36ab06da709356956c',
                                                'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJsonFuel',
                                                                    'ImbalancedChen.P2Saving16StringCharBinding00']},
 'ImbalancedChen.P2OriginalSaving19SourceJsonFuel': {'path': 'ImbalancedChen/P2OriginalSaving19SourceJsonFuel.lean',
                                                     'source_sha256': '0c98bd29f628bade9657a6828772fa2499c9be8dd2d3b16bfea5cd206405c1e4',
                                                     'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJson']},
 'ImbalancedChen.P2Saving16StringCharBinding00': {'path': 'ImbalancedChen/P2Saving16StringCharBinding00.lean',
                                                  'source_sha256': 'd2353e0a96ce78a8ba2da3d3d47f835593dcf758ea6110fd088c82df038f008c',
                                                  'project_imports': []},
 'ImbalancedChen.P2Saving16Cell00OriginalParse': {'path': 'docs/source-only/20261126-p2-5-cell00-consumer/ImbalancedChen/P2Saving16Cell00OriginalParse.lean',
                                                  'source_sha256': '9bd6429be384519a55cb54dc96b6f45067db2a24b1e4189df7c288688caf0f25',
                                                  'project_imports': ['ImbalancedChen.P2OriginalSaving16FiniteCore',
                                                                      'ImbalancedChen.P2Saving16Cell00OriginalJson',
                                                                      'ImbalancedChen.P2Saving16Cell00Decoded'],
                                                  'public_namespace': 'ImbalancedChen.P2Saving16Cell00OriginalParse'},
 'ImbalancedChen.P2OriginalSaving16FiniteCore': {'path': 'ImbalancedChen/P2OriginalSaving16FiniteCore.lean',
                                                 'source_sha256': '552f7ac2f777173c0f555896d85d98bd17513fc972e520f7a0f4dbc406a96322',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16OriginalInput',
                                                                     'ImbalancedChen.P2OriginalSaving16Decoder',
                                                                     'ImbalancedChen.P2OriginalSaving16Q96FloorCore',
                                                                     'ImbalancedChen.P2OriginalSaving19SourceJson'],
                                                 'public_namespace': 'ImbalancedChen.P2OriginalSaving16OriginalArchive'},
 'ImbalancedChen.P2OriginalSaving16OriginalInput': {'path': 'ImbalancedChen/P2OriginalSaving16OriginalInput.lean',
                                                    'source_sha256': '792a5adf50263cfc1a0f67fb3d088c7612910388e4d1fa65db45c3c50065aca5',
                                                    'project_imports': []},
 'ImbalancedChen.P2Saving16Cell00OriginalJson': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00OriginalJson.lean',
                                                 'source_sha256': '3543baacddde3ff81b566b1f1c597251dd27d0981ba95161eeb25a8563ea3fda',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge',
                                                                     'ImbalancedChen.P2Saving16CanonicalCell00Binding',
                                                                     'ImbalancedChen.P2Saving16Cell00SegmentedParse'],
                                                 'public_namespace': 'ImbalancedChen.P2Saving16Cell00OriginalJson'},
 'ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge': {'path': 'ImbalancedChen/P2OriginalSaving19SourceJsonFuelBridge.lean',
                                                           'source_sha256': 'a6dfc833fd01f1c7463cfb694b1d77da21dd9aab1120f2d7fa6840c7229a4d52',
                                                           'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJsonFuel']},
 'ImbalancedChen.P2Saving16CanonicalCell00Binding': {'path': 'ImbalancedChen/P2Saving16CanonicalCell00Binding.lean',
                                                     'source_sha256': 'a5864c739608bda635f88cf7cf3e39481d63b67c4d279f11b45b2cb99e8290dc',
                                                     'project_imports': ['ImbalancedChen.P2OriginalSaving16OriginalInput',
                                                                         'ImbalancedChen.P2Saving16StringCharBinding00']},
 'ImbalancedChen.P2Saving16Cell00SegmentedParse': {'path': 'ImbalancedChen/P2Saving16Cell00SegmentedParse.lean',
                                                   'source_sha256': 'a08f64469fc99999bfdec271b700cd9b566dbc897eaf2a4dc6ee1f95ea88e680',
                                                   'project_imports': ['ImbalancedChen.P2Saving16Cell00DirectParse']},
 'ImbalancedChen.P2Saving16Cell00OriginalFloors': {'path': 'docs/source-only/20261126-p2-5-cell00-consumer/ImbalancedChen/P2Saving16Cell00OriginalFloors.lean',
                                                   'source_sha256': 'a74eb2b792fafcb697c0112ed462cc28caf9cf3a4321c16bbb8496e9605efaae',
                                                   'project_imports': ['ImbalancedChen.P2Saving16Cell00OriginalParse',
                                                                       'ImbalancedChen.P2Saving16Cell00StoredFloors'],
                                                   'public_namespace': 'ImbalancedChen.P2Saving16Cell00OriginalFloors'},
 'ImbalancedChen.P2Saving16Cell00StoredFloors': {'path': 'docs/source-only/20261126-p2-5-cell00-stored-floors/ImbalancedChen/P2Saving16Cell00StoredFloors.lean',
                                                 'source_sha256': 'a26efccb99e0529d166c2fe91c1f4ba78840cd761893fe9c5946e3ff348d8476',
                                                 'project_imports': ['ImbalancedChen.P2Saving16Cell00TypedPayload',
                                                                     'ImbalancedChen.P2OriginalSaving16Q96FloorCore'],
                                                 'public_namespace': 'ImbalancedChen.P2Saving16Cell00StoredFloors'}}
MODULES = [{'module': 'ImbalancedChen.P2Saving16Cell00Decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00OriginalParse'},
 {'module': 'ImbalancedChen.P2Saving16Cell00OriginalFloors'}]


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
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]),
            'Pass exactly one full lowercase 40-hex publication commit.')
    publication = sys.argv[1]
    require(ROOT.is_dir() and not OUT.exists(), 'Expected checkout missing or attempt already exists; preserve prior attempts.')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 checkout is dirty.')
    OUT.mkdir()
    state = {
        'schema': 'p25-cell00-consumers-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
        'module_order': [s['module'] for s in MODULES], 'modules': {}, 'dependency_objects': {},
        'dependency_receipts': {}, 'dependency_modules_compiled': [], 'private_records_written': [],
        'original_cell00_sha256': INPUT_SHA, 'host_correctness_credit': False,
        'failed_monolithic_Decoded_object_used': False, 'original_cell00_decode_proved': False,
        'original_cell00_stored_floors_proved': False, 'geometric_jensen_binding_proved': False,
        'all_cell_finite_guards_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
    }
    frozen = {}
    target_names = {s['module'] for s in MODULES}

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

    def run_stage(owner, label, command, log):
        check_frozen()
        start = time.monotonic()
        row = {'command': command, 'status': 'RUNNING', 'started_utc': now(), 'log': str(log)}
        owner['stages'][label] = row
        write()
        print('P25_CONSUMER_STAGE_START', owner['module'], label, flush=True)
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
        print('P25_CONSUMER_STAGE_RESULT', owner['module'], label,
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
        field_path = bind(FIELD / 'RESULT.json')
        field = json.loads(field_path.read_text())
        require(field['accepted'] is True and field['status'] == 'FULL_AST_BINDING_AND_RAW_ROOT_TYPED_DECODE_ACCEPTED' and
                set(field['modules']) == set(FIELD_OWNERS) and
                all(field['modules'][m]['accepted'] is True for m in FIELD_OWNERS),
                'The four-owner field stage must already be fully accepted; no failed/pending fallback.')
        require(field['schema'] == 'p25-cell00-field-decode-retry-strict-v1' and
                field['module_order'] == [FIELD_TARGET] and
                field['reused_module_order'] == list(REUSED_FIELD_OBJECTS) and
                field['reused_owners_recompiled'] == [] and field['failed_same_name_field_object_used'] is False and
                set(field['owner_receipt_sources']) == set(REUSED_FIELD_OBJECTS) and
                set(field['reused_owner_objects']) == set(REUSED_FIELD_OBJECTS),
                'Expected the incremental Field-only receipt with three explicitly reused owners.')
        prior_field_path = bind(PRIOR_FIELD / 'RESULT.json', PRIOR_FIELD_RESULT_SHA)
        prior_field = json.loads(prior_field_path.read_text())
        require(prior_field['accepted'] is False and prior_field['status'] == 'MODULE_STAGE_FAILED' and
                prior_field['failed_module'] == FIELD_TARGET and prior_field['failed_stage'] == 'normal' and
                prior_field['modules'][FIELD_TARGET]['accepted'] is False and
                prior_field['modules'][FIELD_TARGET]['source_origin']['sha256'] == PRIOR_FIELD_SOURCE_SHA and
                field['prior_attempt']['path'] == str(prior_field_path) and
                field['prior_attempt']['sha256'] == PRIOR_FIELD_RESULT_SHA and
                field['prior_attempt']['accepted'] is False and field['prior_attempt']['failed_owner_reused'] is False,
                'Prior failed aggregate/source identity was relabeled or differs from the original receipt.')
        for module, expected_object in REUSED_FIELD_OBJECTS.items():
            selected_receipt = field['owner_receipt_sources'][module]
            require(artifact(selected_receipt, PRIOR_FIELD_RESULT_SHA) == prior_field_path and
                    selected_receipt['owner_module'] == module and selected_receipt['owner_accepted'] is True and
                    selected_receipt['aggregate_status'] == prior_field['status'] and
                    selected_receipt['aggregate_accepted'] is False and
                    selected_receipt['owner_source_origin'] == prior_field['modules'][module]['source_origin'] and
                    selected_receipt['owner_object_sha256'] == expected_object and
                    field['modules'][module] == prior_field['modules'][module] and
                    prior_field['modules'][module]['source_origin']['commit'] == prior_field['publication_commit'] and
                    prior_field['modules'][module]['object']['sha256'] == expected_object,
                    f'Reused owner must retain its exact original source/publication/stages: {module}')
            row = field['reused_owner_objects'][module]
            require(row['sha256'] == expected_object and row['source_sha256'] == SOURCES[module]['source_sha256'],
                    f'Reused owner copy identity differs: {module}')
            bind(row['path'], expected_object)
            bind(row['isolated_path'], expected_object)
        payload_path = bind(PAYLOAD_FLOORS / 'RESULT.json', PAYLOAD_RESULT_SHA)
        payload_receipt = json.loads(payload_path.read_text())
        require(payload_receipt['accepted'] is True and
                all(payload_receipt['modules'][m]['accepted'] is True for m in [PAYLOAD, FLOORS]),
                'Accepted payload/floors owners are required.')
        for receipt in [field, payload_receipt]:
            require(re.fullmatch(r'[0-9a-f]{40}', receipt['publication_commit']), 'Invalid dependency publication.')
        require(git('rev-parse', 'HEAD') in {publication, field['publication_commit'], payload_receipt['publication_commit']},
                'Unexpected P3 HEAD before consumer source selection.')
        if git('rev-parse', 'HEAD') != publication:
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
        state['runtime_context_receipt'] = record_file(base_path)
        src, lib, audit = OUT / 'src', OUT / 'lib', OUT / 'audit'
        for directory in [src / 'ImbalancedChen', lib / 'ImbalancedChen', audit]:
            directory.mkdir(parents=True)
        tails = base['approved_LEAN_PATH'].split(':')[1:]
        require(tails and all(p and Path(p).is_dir() and
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
        selected = {r['module']: r for r in manifest['selected_modules']}
        require(set(selected) == target_names, 'Consumer manifest selects unexpected owners.')
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
        for module, row in selected.items():
            require(row['path'] == SOURCES[module]['path'] and row['sha256'] == SOURCES[module]['source_sha256'] and
                    (ROOT / row['path']).stat().st_size == row['bytes'] and
                    [module + '.' + n for n in row['public_declarations']] == SOURCES[module]['public_names'],
                    f'Consumer manifest/source/public names mismatch: {module}')
        state['consumer_manifest'] = record_file(manifest_path)
        state['source_graph'] = SOURCES
        state['expected_project_imports_by_owner'] = {m: sorted(project_closure(m)) for m in target_names}

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

        # Revalidate the completed field stage's frozen source/object/log/receipt
        # chain. No source or object from its failed predecessor owner is used.
        require(field['failed_owner_object_used'] is False and field['dependency_modules_compiled'] == [],
                'Field-stage dependency policy differs from the reviewed plan.')
        for path, h in field['frozen_inputs'].items():
            bind(path, h)
        expected_field_dependencies = set().union(*(project_closure(m) for m in FIELD_OWNERS)) - set(FIELD_OWNERS)
        require(set(field['dependency_objects']) == expected_field_dependencies and len(expected_field_dependencies) == 8,
                'Accepted field-stage dependency set differs from actual source graph.')
        for module, row in field['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'], f'Field reused source hash differs: {module}')
            bind(row['path'], row['sha256'])
            copy_dependency(module, row['isolated_path'], row['sha256'], 'Accepted field-stage exact dependency with frozen receipt chain revalidated')
        for module in FIELD_OWNERS:
            if module in REUSED_FIELD_OBJECTS:
                # Verify the original complete owner receipt against its own
                # publication. Never substitute the new aggregate publication.
                modern_owner(prior_field, prior_field_path, module)
            else:
                require(module == FIELD_TARGET, 'Unexpected fresh owner in incremental field receipt.')
                modern_owner(field, field_path, module)
        modern_owner(payload_receipt, payload_path, PAYLOAD)
        modern_owner(payload_receipt, payload_path, FLOORS)
        state['field_stage_receipt'] = record_file(field_path)
        state['field_owner_receipt_sources'] = {
            module: record_file(prior_field_path if module in REUSED_FIELD_OBJECTS else field_path)
            for module in FIELD_OWNERS
        }
        state['payload_floors_receipt'] = record_file(payload_path)

        json_receipt = legacy_owner(ORIGINAL_JSON, JSON_OWNER, ORIGINAL_JSON_RECEIPT_SHA)
        core_receipt = legacy_owner(FINITE_CORE, CORE_OWNER, FINITE_CORE_RECEIPT_SHA)
        # Only the four still-missing, actually imported JSON dependencies are
        # added. The old receipt also lists CharInput modules; those are excluded.
        for module in EXTRA_JSON_DEPENDENCIES:
            row = json_receipt['dependencies'][module]
            require(row['sha256'] == KNOWN_OBJECTS[module], f'OriginalJson dependency identity differs: {module}')
            if module in ['ImbalancedChen.P2OriginalSaving16OriginalInput', 'ImbalancedChen.P2Saving16CanonicalCell00Binding']:
                receipt_path = bind(row['receipt'], row['receipt_sha256'])
                receipt = json.loads(receipt_path.read_text())
                require(receipt['accepted'] is True and receipt['module'] == module and
                        receipt['source_sha256'] == SOURCES[module]['source_sha256'], f'Original-input/canonical dependency acceptance mismatch: {module}')
                object_key = 'fresh_target_object_sha256' if module.endswith('CanonicalCell00Binding') else 'object_sha256'
                require(receipt[object_key] == KNOWN_OBJECTS[module], f'Accepted input/canonical object hash mismatch: {module}')
                labels = ['normal', 'replay', 'audit'] if 'normal' in receipt else ['replay', 'audit']
                for label in labels:
                    stage_log(receipt[label])
                if 'artifacts' in receipt:
                    for name, h in receipt['artifacts'].items():
                        candidate = Path(name)
                        if not candidate.is_absolute():
                            candidate = ROOT / candidate if str(candidate).startswith('.lake/') else receipt_path.parent / candidate
                        bind(candidate, h)
                state['dependency_receipts'][module] = record_file(receipt_path)
            else:
                reproduced = [r for r in json_receipt['reproduced_accepted_objects'] if r['module'] == module]
                require(len(reproduced) == 1 and reproduced[0]['exact_accepted_object_match'] is True and
                        reproduced[0]['object_sha256'] == KNOWN_OBJECTS[module] and
                        reproduced[0]['source_sha256'] == SOURCES[module]['source_sha256'],
                        f'OriginalJson accepted object reproduction binding mismatch: {module}')
                bind(ORIGINAL_JSON / 'src' / (module.replace('.', '/') + '.lean'), SOURCES[module]['source_sha256'])
                bind(ORIGINAL_JSON / (module.split('.')[-1] + '-REPRODUCE.log'), reproduced[0]['log_sha256'])
                state['dependency_receipts'][module] = {'accepted_original_json_receipt': record_file(ORIGINAL_JSON / 'RESULT.json'),
                                                       'exact_accepted_reproduction': reproduced[0]}
            copy_dependency(module, row['path'], KNOWN_OBJECTS[module], 'Exact accepted OriginalJson dependency with original receipt/reproduction hash validated')
        # Every accepted legacy owner's actual transitive objects must equal
        # the objects in this one root, including objects reused via field stage.
        for owner_module, receipt in [(JSON_OWNER, json_receipt), (CORE_OWNER, core_receipt)]:
            for module in project_closure(owner_module) - {owner_module}:
                row = receipt['dependencies'][module]
                require(module in state['dependency_objects'] and
                        state['dependency_objects'][module]['sha256'] == row['sha256'],
                        f'Accepted legacy import object differs in isolated root: {owner_module}/{module}')
                bind(row['path'], row['sha256'])
        needed = set().union(*(project_closure(m) for m in target_names)) - target_names
        require(set(state['dependency_objects']) == needed and len(needed) == 19 and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 19,
                'The initial isolated library must contain exactly 19 accepted dependency objects.')
        require(all(not (lib / (m.replace('.', '/') + '.olean')).exists() for m in target_names),
                'A selected consumer target already has an object; reject old same-name Decoded fallback.')

        for spec in MODULES:
            module = spec['module']
            source = src / (module.replace('.', '/') + '.lean')
            source.write_bytes((ROOT / SOURCES[module]['path']).read_bytes())
            bind(source, SOURCES[module]['source_sha256'])
            audit_path = audit / (module.split('.')[-1] + '.lean')
            audit_path.write_text(audit_template.replace(PAYLOAD, module))
            bind(audit_path)
            state['modules'][module] = {
                'module': module, 'status': 'PENDING', 'accepted': False,
                'source_origin': {'commit': publication, 'path': SOURCES[module]['path'], 'sha256': SOURCES[module]['source_sha256']},
                'source_copy': record_file(source), 'audit_source': record_file(audit_path),
                'required_owned_names': SOURCES[module]['public_names'], 'stages': {},
            }
        state.update(status='VERIFYING_CONSUMERS', frozen_inputs=dict(frozen))
        check_frozen()
        write()
        for spec in MODULES:
            module = spec['module']
            owner = state['modules'][module]
            owner['status'] = 'RUNNING'
            directory = OUT / module.split('.')[-1]
            directory.mkdir()
            source = src / (module.replace('.', '/') + '.lean')
            object_path = lib / (module.replace('.', '/') + '.olean')
            audit_path = audit / (module.split('.')[-1] + '.lean')
            require(not object_path.exists(), f'Target object already exists: {module}')
            for label, command in [
                ('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(object_path), str(source)]),
                ('replay', [str(CHECKER), '--verbose', module]),
                ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(audit_path)]),
            ]:
                run_stage(owner, label, command, directory / (label.upper() + '.log'))
                if label == 'normal':
                    bind(object_path)
                    owner['object'] = record_file(object_path)
                    state['frozen_inputs'] = dict(frozen)
                    write()
            records, inventory, imports = read_audit(directory / 'AUDIT.log', module)
            require(set(owner['required_owned_names']) <= {r['name'] for r in records}, f'Required public consumer missing: {module}')
            declarations_path, inventory_path = directory / 'OWNED_DECLARATIONS.json', directory / 'OWNED_INVENTORY.json'
            declarations_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n')
            inventory_path.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + '\n')
            owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                         owned_count=len(records), owned_declarations=records, actual_project_closure=imports,
                         declarations=record_file(declarations_path), inventory=record_file(inventory_path), ended_utc=now())
            check_frozen()
            write()
            print('P25_CONSUMER_OWNER_ACCEPTED', module, len(records), owner['object']['sha256'], flush=True)
        require(all(o['accepted'] for o in state['modules'].values()), 'Not all selected consumers accepted.')
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Publication changed during verification.')
        check_frozen()
        state.update(status='ORIGINAL_CELL00_DECODE_AND_STORED_FLOORS_ACCEPTED', accepted=True,
                     original_cell00_decode_proved=True, original_cell00_stored_floors_proved=True, ended_utc=now())
        write()
        print('P25_CONSUMERS_RESULT', json.dumps({
            'status': state['status'], 'accepted': True, 'owned_counts': {m: o['owned_count'] for m, o in state['modules'].items()},
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
        print('P25_CONSUMERS_FAILED', json.dumps({'status': state['status'], 'error': state['error'][:1800],
              'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json')}, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
