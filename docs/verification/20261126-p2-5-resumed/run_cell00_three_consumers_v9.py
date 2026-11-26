#!/usr/bin/env python3
"""Resume three consumers after actual partial v8; reuse 42 exact dependencies.

The completed v8 rematerialization and accepted OriginalParse are immutable
historical evidence. This driver cannot compile recovered dependencies or rerun
Parse gates. Only three unaccepted consumers execute normal/kernel/full-owned
gates in a new actual context. Five old missing envelopes remain explicit gaps.
"""
from datetime import datetime, timezone
import argparse
import types
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
OUT = ROOT / '.lake/diagnostic/p25-cell00-three-consumers-attempt009'
FAILED_PARSE = ROOT / '.lake/diagnostic/p25-cell00-five-consumers-attempt005'
FAILED_PARSE_RESULT_SHA = 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88'
FAILED_PARSE_PUBLICATION = 'be20f0b050bb787ecb98f9afdd9b6a386706f45a'
FAILED_PARSE_RUNNER_SHA = '35fc47af3d3a33eb30e9da43e60b5af02eb6d770da1b8bf4092b978820d6d403'
FAILED_PARSE_NORMAL_SHA = '8c4de444dda9af81f3783f916be29440a89b465ac7096de0d7a5a51247f12d16'
FAILED_PARSE_EXCEPTION_SHA = '7a6f4d4910c9cdf958b3e920f6bc6276be6e5c7dc7bb80bef5cf27cc427f7e27'
DECODED = 'ImbalancedChen.P2Saving16Cell00Decoded'
DECODED_OBJECT_SHA = 'f700e8e866da0192152040a0853e27eab857ee007c0076df61613e3a849e534f'
# Enabled only after the complete actual005 capsule, all four logs, accepted
# Decoded object, and complete owned inventory were verified locally.
DECODED_ARTIFACTS_REVIEWED = True
PARSE_TARGET = 'ImbalancedChen.P2Saving16Cell00OriginalParse'
OLD_PARSE_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-consumer/ImbalancedChen/P2Saving16Cell00OriginalParse.lean'
OLD_PARSE_SOURCE_SHA = '9bd6429be384519a55cb54dc96b6f45067db2a24b1e4189df7c288688caf0f25'
PARSE_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-parse-transport/ImbalancedChen/P2Saving16Cell00OriginalParse.lean'
PARSE_SOURCE_SHA = '522cf6bda9efdec24e9ba25c826a9eed29b06199f7f6af514e360c64369fb30d'
PARSE_OVERRIDE_REL = 'docs/source-only/20261126-p2-5-cell00-parse-transport/SOURCE_OVERRIDE.json'
PARSE_OVERRIDE_SHA = 'aa0e24ddfceea6e160a2d973f89a1320e31d1e63153f42c020b639ccf8a2007b'
PARSE_PRIVATE_HELPERS = [PARSE_TARGET + '.' + name for name in
    ['parsedCell_of_parse_decode', 'parsedCellSuccess_of_parsedCell', 'archive_of_parsedCell']]
FAILED_CONSUMER = ROOT / '.lake/diagnostic/p25-cell00-five-consumers-attempt004'
FAILED_CONSUMER_RESULT_SHA = '2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a'
FAILED_CONSUMER_PUBLICATION = '8fb0faace8f95a4ad4be26f32350575491445ac4'
FAILED_CONSUMER_RUNNER_SHA = 'd9e4360463fc692a0fda62ddd77e77a6f53d837ff5c68f29087bac1fafbbe7ef'
FAILED_CONSUMER_EXCEPTION_SHA = 'e615dca0984636d16301a0a068e02f1dea5bbde7e89157b068023a26dbd7a926'
MIN_INITIAL_FREE_BYTES = 320 * 1024 * 1024
METADATA_HEADROOM_BYTES = 64 * 1024 * 1024
GATE_WORKING_HEADROOM_BYTES = 256 * 1024 * 1024
FIELD = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt006'
PREVIOUS_FINAL = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt005'
EARLIER_FINAL = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt004'
SPLIT = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt003'
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
    DECODED: DECODED_OBJECT_SHA,
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
EXTRA_JSON_DEPENDENCIES = [
    'ImbalancedChen.P2OriginalSaving16OriginalInput',
    'ImbalancedChen.P2Saving16CanonicalCell00Binding',
    'ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge',
    'ImbalancedChen.P2Saving16Cell00SegmentedParse',
]

# Source identities and the complete 45-module import graph are separately
# frozen for review. No proof sources are generated or modified by this driver.
RUNNER_REL = 'docs/verification/20261126-p2-5-resumed/run_cell00_three_consumers_v9.py'
RESOURCE_BASE_REL = 'docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v6.py'
RESOURCE_BASE_SHA = '064fa8414660f7036b51bf6bf336f1aef168913dca5722cd4050b9d005174f7a'
RESOURCE_BASE_PUBLICATION = '4653b261828f127ba0b5082eaf1106a3fea09d46'
ORIGINAL_REVIEWED_DRIVER_REL = 'docs/verification/20261126-p2-5-continuation/run_cell00_five_consumers_cloud.py'
ORIGINAL_REVIEWED_DRIVER_SHA = '4f12d9bcb43b2fd4a0b626d5803dfb27b7ec7f05784d005f7378879ccd0d620f'
ADAPTED_FROM_REL = 'docs/verification/20261126-p2-5-resumed/run_cell00_five_consumers_v5.py'
ADAPTED_FROM_SHA = '35fc47af3d3a33eb30e9da43e60b5af02eb6d770da1b8bf4092b978820d6d403'
SELECTION_REL = 'docs/verification/20261126-p2-5-continuation/cell00-five-consumers/SOURCE_AND_RECEIPT_SELECTION.json'
SELECTION_SHA = 'cd8104cd2a1769c1dfb610f80a1c62250da9bbe81014296453db42ab6e8ca300'
# The complete actual receipt, logs, owned inventory, and object bytes were checked
# before enabling this separate artifact-review gate; the cloud preflight rebinds them.
FIELD_RESULT_SHA = '82123af5bc4f1e9334da8f578de11147effe73da0a7ab90b55459abbb25bcb0e'
FIELD_PUBLICATION = '99ec807044cd865b9713e769c6a967094c4b3e34'
FIELD_RUNNER_SHA = '671ae21664755ca97bdf80a64efec8b4adc966e106b54fa943f1ea9159f1f05d'
FIELD_ARTIFACTS_REVIEWED = True
PRIVATE_HELPER = 'ImbalancedChen.P2Saving16Cell00FieldDecode.decodeCell_of_field_successes'
PRIVATE_HELPER_ACTUAL = '_private.ImbalancedChen.P2Saving16Cell00FieldDecode.0.' + PRIVATE_HELPER
PREVIOUS_FINAL_RESULT_SHA = '812f43171da6572a897020df007846c3dfd4776253c4e851824b91536380f716'
PREVIOUS_FINAL_PUBLICATION = 'b667409e7e7f23094637dfccfdceec6e6d34ee68'
PREVIOUS_FINAL_RUNNER_SHA = '4a091235f716bed318a97a86c179532b89a907187efeb94dbf903806ef3ab956'
PREVIOUS_FINAL_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-field-explicit/ImbalancedChen/P2Saving16Cell00FieldDecode.lean'
PREVIOUS_FINAL_SOURCE_SHA = '46ded7f18f173c94d66551c25157e259b8bef7f6cbf5c04f323a23dec3064a7b'
PREVIOUS_FINAL_NORMAL_SHA = '03ffeec727d76201990021b3d6e14110fb04a81b944685d0c3a995e19c28cc35'
EARLIER_FINAL_RESULT_SHA = 'c8f52525af889be955ffaa245d40ead84f560fea0de0f04e53ae202afeaab1f2'
EARLIER_FINAL_PUBLICATION = '4e69759e3d27495c0e7bccfee23b7a0b42c48ea6'
EARLIER_FINAL_RUNNER_SHA = 'b6619cf9ee5b0a79dfc0554af802dec126c4c6d8629f6b81002802a2779e798a'
BASE_FINAL_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-field-final/ImbalancedChen/P2Saving16Cell00FieldDecode.lean'
BASE_FINAL_SOURCE_SHA = '59cafdc924a5a50d01d25dfb03178208c4f1e13552fdb105d5a5cb43f1f59cc3'
EARLIER_FINAL_NORMAL_SHA = '2445cd3e185b9247e4771d48e31d1b399cd72f2366498fa8a2ec05004e062fc2'
PREVIOUS_SOURCE_OVERRIDE_REL = 'docs/source-only/20261126-p2-5-cell00-field-explicit/SOURCE_OVERRIDE.json'
PREVIOUS_SOURCE_OVERRIDE_SHA = '2b3f10b0a0d63569bb27fc1440735c3e40731544daaffbb285e67431ba2e3898'
SOURCE_OVERRIDE_REL = 'docs/source-only/20261126-p2-5-cell00-field-symbolic/SOURCE_OVERRIDE.json'
SOURCE_OVERRIDE_SHA = '7e278c94105656706371ef827ebc7b6ce5440a866de7d4fadd1ee000fd0f45af'
SPLIT_RESULT_SHA = '00ae4f5be311670b1538e934574a79b56ae0808253711ae1e0c606095d6dfdf0'
SPLIT_PUBLICATION = '2ce35f759db6fdc18373b2842f655d9569fd4f48'
SPLIT_RUNNER_SHA = '3b7740243e09c49d8ebfc0233a5f1a666a865132364d90a075b4980cc965176b'
SPLIT_FAILED_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00FieldDecode.lean'
SPLIT_FAILED_SOURCE_SHA = 'ce7e0131800eb84b3ab2c8dfd8830aaa0b353475594e91b70906b3d1052e77e2'
SPLIT_FAILED_NORMAL_SHA = '623cd44b8f00065842328db445925797cbe3e3ccf8946cc92e12ded6a6a18e0b'
FINAL_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-field-symbolic/ImbalancedChen/P2Saving16Cell00FieldDecode.lean'
FINAL_SOURCE_SHA = 'ad5e8f4f534dd8d23ea6e181e2323b5d11c935affdd76c4d8b64a937aaf0d224'
FIELD_SELECTION_REL = 'docs/verification/20261126-p2-5-continuation/cell00-field-final/SOURCE_AND_RECEIPT_SELECTION.json'
FIELD_SELECTION_SHA = '5a7195c165faa79dfa2e9e9277ef37a8d8ab9819cb6a057692c6e0ff8aba0201'
PRIOR_FIELD_PUBLICATION = 'ecfc75049ab7380048fa0c9992e14b787bc908de'
REMAINING = ROOT / '.lake/diagnostic/p25-cell00-remaining-arithmetic-attempt001'
REMAINING_RESULT_SHA = '1e48fc2e2a45b2e4247ab08597586dae6c8cac3cd9a05788e465b5175d262f7c'
REMAINING_PUBLICATION = '5cc2b181f51be2f20ce316256fe2cdf3e691ca69'
REMAINING_RUNNER_SHA = '17b4b2193968c061a8bbb31ac0e3043c8cbf4eb2b22ee010a0359a57c8de4918'
ROW00 = 'ImbalancedChen.P2Saving16Cell00Row00Arithmetic'
ROW00_RESULT = ROOT / '.lake/diagnostic/p25-cell00-row00-arithmetic-attempt001/RESULT.json'
ROW00_RESULT_SHA = '7094b47bfe97aaa8236cda1309e805440a3b6a1b48b5d4083fa6ba75cd2e8265'
FACTS = ROOT / '.lake/diagnostic/p25-cell00-typed-source-facts-attempt001'
FACTS_MODULE = 'ImbalancedChen.P2Saving16Cell00TypedSourceFacts'
FACTS_RESULT_SHA = '498a435cb515686340b095fc9545cf6130cfad3b26390b61b03c541ee9e6dc8f'
FACTS_PUBLICATION = '38683fcaff45f48bac7376ecf4cb798c9a4ec292'
FACTS_RUNNER_SHA = 'c7b5f96a72803c32f6da3a1888051545a02a335ab79bfd316fce591aae49b689'
FACTS_OBJECT_SHA = '797bb62f0d1f9fcef53d2a4b9ea995fb38942d10cc99436c9fe3c29e418b588b'
EXTERNAL_SNAPSHOT_SHA = 'b94ab99b39a831a616d626c55c4b89c0a921d15c95319de19063d375bc982728'
EXPECTED_EXTERNAL_COUNT = 5312
EXPECTED_EXTERNAL_COMPANIONS = 10624
SUPPORT = 'ImbalancedChen.P2Saving16Cell00FieldSimp'
SCOPE = 'ImbalancedChen.P2Saving16Cell00FieldDecode'
SCOPED_APPENDIX_REL = 'docs/source-only/20261126-p2-5-cell00-field-split/PRIVATE_SCOPED_SIMP_AUDIT_APPENDIX.lean'
SCOPED_APPENDIX_SHA = 'ff82f03c8c798556f2ed6e18ce4ed5a035057fa616b55664a105a9b5886aa202'
FRESH_MODULES = [
    'ImbalancedChen.P2Saving16Cell00Decoded',
    'ImbalancedChen.P2Saving16Cell00OriginalParse',
    'ImbalancedChen.P2Saving16Cell00OriginalFloors',
    'ImbalancedChen.P2Saving16Cell00OriginalArithmetic',
    'ImbalancedChen.P2Saving16Cell00OriginalSourceFacts',
]
# Preserve both historical owner scopes. Decoded and OriginalParse are now
# accepted dependencies; only the final three owners may execute new gates.
V8_CONTINUATION_MODULES = FRESH_MODULES[1:]
CONTINUATION_MODULES = FRESH_MODULES[2:]
FIELD_FRESH_MODULES = [SUPPORT, 'ImbalancedChen.P2Saving16Cell00FieldBase',
    *[f'ImbalancedChen.P2Saving16Cell00Simplex{i:02d}Decode' for i in range(8)], FIELD_TARGET]
FIELD_OWNERS = [*REUSED_FIELD_OBJECTS, *FIELD_FRESH_MODULES]
SPLIT_ACCEPTED_MODULES = FIELD_FRESH_MODULES[:-1]
REUSED_FIELD_OWNERS = [*REUSED_FIELD_OBJECTS, *SPLIT_ACCEPTED_MODULES]
ARITHMETIC_MODULES = [*[f'ImbalancedChen.P2Saving16Cell00Row{i:02d}Arithmetic' for i in range(1, 8)],
                      'ImbalancedChen.P2Saving16Cell00AllRowsArithmetic']
SOURCES = {}
MODULES = [{'module': module} for module in CONTINUATION_MODULES]


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


def audited_imports(log):
    rows = [json.loads(line.removeprefix('P0_QUEUE_IMPORTS '))
            for line in Path(log).read_text().splitlines() if line.startswith('P0_QUEUE_IMPORTS ')]
    require(len(rows) == 1 and len(rows[0]) == len(set(rows[0])),
            'Missing or duplicate full imported-module inventory.')
    return rows[0]


def read_private_scope_audit(log, records, required):
    # Same check as the accepted Field-split 3b774024 driver, with explicit scope.
    marker = 'P25_PRIVATE_SCOPED_SIMP_INTERFACE '
    rows = [json.loads(s.removeprefix(marker)) for s in Path(log).read_text().splitlines() if s.startswith(marker)]
    require(len(rows) == 1, 'Missing or duplicate imported private scoped-simp interface audit.')
    row = rows[0]
    matches = row['matches']
    require(row['module'] == SUPPORT and row['scope'] == SCOPE and
            row['required_count'] == row['matched_count'] == len(matches) == len(required) == 296 and
            [r['user_name'] for r in matches] == required and len({r['actual_name'] for r in matches}) == 296,
            'Private scoped-simp interface inventory differs.')
    owned = {r['name'] for r in records}
    for match in matches:
        candidates = [name for name in owned if name.endswith('.' + match['user_name'])]
        require(candidates == [match['actual_name']] and match['actual_name'].startswith('_private.'),
                'Scoped-simp name is not the unique actual private declaration in the full owned audit.')
    return row


def validate_field_history(field, split, prior):
    """Validate structures only; main independently binds all receipt artifacts."""
    require(split['schema'] == 'p25-cell00-field-split-strict-v1' and split['accepted'] is False and
            split['status'] == 'MODULE_STAGE_FAILED' and split['publication_commit'] == SPLIT_PUBLICATION and
            split['failed_module'] == FIELD_TARGET and split['failed_stage'] == 'normal' and
            split['module_order'] == FIELD_FRESH_MODULES and set(split['modules']) == set(FIELD_OWNERS) and
            all(split['modules'][m]['accepted'] is True for m in REUSED_FIELD_OWNERS) and
            split['modules'][FIELD_TARGET]['accepted'] is False and
            split['reused_module_order'] == list(REUSED_FIELD_OBJECTS) and
            split['reused_owners_recompiled'] == split['old_owner_normal_recompilations'] == [] and
            split['dependency_modules_compiled'] == [] and split['failed_same_name_field_object_used'] is False and
            split['failed_owner_object_used'] is False and split['original_theorem_commands_byte_identical'] is True and
            split['private_scoped_simp_interface_checked'] is True and
            split['complete_external_after_matches_before'] is False and
            split['historical_missing_external_hashes_invented'] is False and
            set(split['owner_receipt_sources']) == set(split['reused_owner_objects']) == set(REUSED_FIELD_OBJECTS) and
            set(split['additional_reuse_validations']) == set(REUSED_FIELD_OBJECTS),
            'Require the unchanged failed split aggregate and its thirteen accepted historical owners.')
    require(prior['publication_commit'] == PRIOR_FIELD_PUBLICATION and prior['accepted'] is False and
            prior['status'] == 'MODULE_STAGE_FAILED' and prior['failed_module'] == FIELD_TARGET and
            prior['failed_stage'] == 'normal' and prior['modules'][FIELD_TARGET]['accepted'] is False and
            prior['modules'][FIELD_TARGET]['source_origin']['sha256'] == PRIOR_FIELD_SOURCE_SHA and
            split['prior_attempt']['path'] == str(PRIOR_FIELD / 'RESULT.json') and
            split['prior_attempt']['sha256'] == PRIOR_FIELD_RESULT_SHA and
            split['prior_attempt']['accepted'] is False and split['prior_attempt']['failed_owner_reused'] is False,
            'Original ecfc provenance or failed aggregate evidence changed.')
    require(field['schema'] == 'p25-cell00-field-final-strict-v1' and field['accepted'] is True and
            field['status'] == 'FINAL_FIELD_TYPED_DECODE_ACCEPTED' and field['publication_commit'] == FIELD_PUBLICATION and
            field['module_order'] == [FIELD_TARGET] and set(field['modules']) == {FIELD_TARGET} and
            field['modules'][FIELD_TARGET]['accepted'] is True and
            field['modules'][FIELD_TARGET]['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
            field['modules'][FIELD_TARGET]['source_origin'] ==
                {'commit': FIELD_PUBLICATION, 'path': FINAL_SOURCE_REL, 'sha256': FINAL_SOURCE_SHA} and
            field['dependency_modules_compiled'] == field['existing_owners_normally_recompiled'] ==
                field['accepted_dependency_gates_rerun'] == [] and
            field['failed_same_name_field_object_used'] is False and
            field['failed_aggregate_relabelled_as_success'] is False and
            field['public_final_statements_unchanged'] is True and
            field['private_scoped_simp_interface_checked'] is True and field['raw_root_typed_decode_proved'] is True and
            field['original_archive_decode_proved'] is False and field['Q96_proved'] is False and field['P2_5_proved'] is False and
            field['complete_external_after_matches_before'] is True and
            field['historical_missing_external_hashes_invented'] is False and
            set(field['reused_original_owner_receipts']) == set(REUSED_FIELD_OWNERS) and
            set(field['source_receipt_by_reused_owner']) == set(REUSED_FIELD_OWNERS),
            'Require the actual one-owner final success without relabeling historical owners.')
    failed = field['failed_split_receipt']
    require(failed['path'] == str(SPLIT / 'RESULT.json') and failed['sha256'] == SPLIT_RESULT_SHA and
            failed['publication_commit'] == SPLIT_PUBLICATION and failed['aggregate_accepted'] is False and
            failed['aggregate_status'] == 'MODULE_STAGE_FAILED' and failed['failed_owner_reused'] is False and
            field['prior_failed_final_owner'] == split['modules'][FIELD_TARGET],
            'The final receipt changed failed split evidence.')
    for module in REUSED_FIELD_OWNERS:
        original = prior if module in REUSED_FIELD_OBJECTS else split
        original_path = PRIOR_FIELD if module in REUSED_FIELD_OBJECTS else SPLIT
        original_sha = PRIOR_FIELD_RESULT_SHA if module in REUSED_FIELD_OBJECTS else SPLIT_RESULT_SHA
        selected = field['source_receipt_by_reused_owner'][module]
        require(field['reused_original_owner_receipts'][module] == original['modules'][module] and
                selected['path'] == str(original_path / 'RESULT.json') and selected['sha256'] == original_sha and
                selected['publication_commit'] == original['publication_commit'] and
                selected['aggregate_accepted'] is False and selected['aggregate_status'] == 'MODULE_STAGE_FAILED' and
                selected['owner_accepted'] is True,
                'Historical owner provenance changed: ' + module)
    require(field['reused_complete_context_validations'] == split['additional_reuse_validations'],
            'Historical supplemental complete-context validations changed.')


def select_sources(selection, final_selection):
    """Apply the exact final source row while preserving both frozen selections."""
    require(selection['schema'] == 'p25-cell00-five-consumers-source-and-receipt-selection-v1' and
            selection['dependency_receipt_selection_complete'] is False and
            selection['dependencies']['field']['sha256'] is None,
            'The frozen consumer draft selection must retain its original incomplete status.')
    require(final_selection['schema'] == 'p25-cell00-field-final-source-and-receipt-selection-v1' and
            final_selection['dependency_receipt_selection_complete'] is True and
            final_selection['final_source_selection_complete'] is True and
            final_selection['fresh_owner_order'] == [FIELD_TARGET] and final_selection['fresh_owner_count'] == 1 and
            final_selection['project_module_count'] == 22 and final_selection['dependency_object_count'] == 21,
            'Final source selection is incomplete or has a different scope.')
    previous = selection['source_graph']
    final = final_selection['source_graph']
    require(len(previous) == 45 and len(final) == 22 and set(final) <= set(previous) and
            previous[FIELD_TARGET]['path'] == SPLIT_FAILED_SOURCE_REL and
            previous[FIELD_TARGET]['source_sha256'] == SPLIT_FAILED_SOURCE_SHA and
            final[FIELD_TARGET]['path'] == BASE_FINAL_SOURCE_REL and
            final[FIELD_TARGET]['source_sha256'] == BASE_FINAL_SOURCE_SHA,
            'Final source path/hash or selected graph changed.')
    require(all(previous[m] == final[m] for m in final if m != FIELD_TARGET),
            'All historical source rows must remain unchanged.')
    require({k: v for k, v in previous[FIELD_TARGET].items() if k not in {'path', 'source_sha256'}} ==
            {k: v for k, v in final[FIELD_TARGET].items() if k not in {'path', 'source_sha256'}},
            'Final source imports or public API changed.')
    return {**previous, FIELD_TARGET: final[FIELD_TARGET]}


def validate_previous_final(field, previous, split, prior):
    """Preserve actual failed attempt005 separately from accepted attempt006."""
    require(previous['schema'] == 'p25-cell00-field-final-strict-v1' and previous['accepted'] is False and
            previous['status'] == 'MODULE_STAGE_FAILED' and previous['publication_commit'] == PREVIOUS_FINAL_PUBLICATION and
            previous['module_order'] == [FIELD_TARGET] and set(previous['modules']) == {FIELD_TARGET} and
            previous['failed_module'] == FIELD_TARGET and previous['failed_stage'] == 'normal' and
            previous['raw_root_typed_decode_proved'] is False and previous['complete_external_after_matches_before'] is False and
            previous['failed_same_name_field_object_used'] is False and
            previous['failed_aggregate_relabelled_as_success'] is False and
            previous['dependency_modules_compiled'] == previous['existing_owners_normally_recompiled'] ==
                previous['accepted_dependency_gates_rerun'] == [] and
            previous['modules'][FIELD_TARGET]['accepted'] is False and
            previous['modules'][FIELD_TARGET]['status'] == 'NORMAL_FAILED' and
            set(previous['modules'][FIELD_TARGET]['stages']) == {'normal'} and
            'object' not in previous['modules'][FIELD_TARGET] and
            previous['modules'][FIELD_TARGET]['source_origin'] ==
                {'commit': PREVIOUS_FINAL_PUBLICATION, 'path': PREVIOUS_FINAL_SOURCE_REL,
                 'sha256': PREVIOUS_FINAL_SOURCE_SHA},
            'Attempt005 must remain the exact failed one-owner final attempt.')
    selected = field['previous_final_attempt']
    require(field['repair_kind'] == 'symbolic-field-composition-after-attempt005' and
            previous['repair_kind'] == 'explicit-field-composition-after-attempt004' and
            selected['path'] == str(PREVIOUS_FINAL / 'RESULT.json') and selected['sha256'] == PREVIOUS_FINAL_RESULT_SHA and
            selected['publication_commit'] == PREVIOUS_FINAL_PUBLICATION and selected['aggregate_accepted'] is False and
            selected['aggregate_status'] == 'MODULE_STAGE_FAILED' and selected['failed_owner_reused'] is False and
            field['previous_final_failed_owner'] == previous['modules'][FIELD_TARGET] and
            previous['failed_split_receipt'] == field['failed_split_receipt'] and
            previous['prior_failed_final_owner'] == split['modules'][FIELD_TARGET],
            'Accepted symbolic final receipt changed attempt005 failure provenance.')
    require(previous['reused_original_owner_receipts'] == field['reused_original_owner_receipts'] and
            all(previous['reused_original_owner_receipts'][m] == prior['modules'][m] for m in REUSED_FIELD_OBJECTS) and
            all(previous['reused_original_owner_receipts'][m] == split['modules'][m] for m in SPLIT_ACCEPTED_MODULES) and
            previous['reused_complete_context_validations'] == split['additional_reuse_validations'],
            'Attempt005 historical owner dictionaries or supplemental validations changed.')


def select_explicit_sources(selection, final_selection, override):
    """Extend the checked original source overlay with the frozen explicit row."""
    sources = select_sources(selection, final_selection)
    replacement = override['source_spec']
    require(override['schema'] == 'p25-cell00-field-explicit-source-override-v1' and override['module'] == FIELD_TARGET and
            override['original_selection']['path'] == FIELD_SELECTION_REL and
            override['original_selection']['sha256'] == FIELD_SELECTION_SHA and
            override['previous_source'] == {'path': BASE_FINAL_SOURCE_REL, 'bytes': 3318,
                                            'sha256': BASE_FINAL_SOURCE_SHA} and
            override['new_source'] == {'path': PREVIOUS_FINAL_SOURCE_REL, 'bytes': 4602,
                                       'sha256': PREVIOUS_FINAL_SOURCE_SHA} and
            override['public_statement_count'] == 4 and override['direct_project_import_count'] == 9 and
            override['unchanged_source_graph_rows'] == 21 and override['original_data_modified'] is False and
            override['new_public_declarations'] == override['new_assumptions'] == [] and
            replacement['path'] == PREVIOUS_FINAL_SOURCE_REL and
            replacement['source_sha256'] == PREVIOUS_FINAL_SOURCE_SHA,
            'Explicit source override changes the selected source, data, or declaration scope.')
    require({k: v for k, v in replacement.items() if k not in {'path', 'source_sha256'}} ==
            {k: v for k, v in sources[FIELD_TARGET].items() if k not in {'path', 'source_sha256'}},
            'Explicit final imports or public API changed.')
    return {**sources, FIELD_TARGET: replacement}


def validate_earlier_final(field, previous, earlier):
    """Keep actual failed attempt004 distinct in both later receipt chains."""
    require(earlier['schema'] == 'p25-cell00-field-final-strict-v1' and earlier['accepted'] is False and
            earlier['status'] == 'MODULE_STAGE_FAILED' and earlier['publication_commit'] == EARLIER_FINAL_PUBLICATION and
            earlier['module_order'] == [FIELD_TARGET] and set(earlier['modules']) == {FIELD_TARGET} and
            earlier['failed_module'] == FIELD_TARGET and earlier['failed_stage'] == 'normal' and
            earlier['raw_root_typed_decode_proved'] is False and earlier['complete_external_after_matches_before'] is False and
            earlier['failed_same_name_field_object_used'] is False and
            earlier['failed_aggregate_relabelled_as_success'] is False and
            earlier['dependency_modules_compiled'] == earlier['existing_owners_normally_recompiled'] ==
                earlier['accepted_dependency_gates_rerun'] == [] and
            earlier['modules'][FIELD_TARGET]['accepted'] is False and
            earlier['modules'][FIELD_TARGET]['status'] == 'NORMAL_FAILED' and
            set(earlier['modules'][FIELD_TARGET]['stages']) == {'normal'} and
            'object' not in earlier['modules'][FIELD_TARGET] and
            earlier['modules'][FIELD_TARGET]['source_origin'] ==
                {'commit': EARLIER_FINAL_PUBLICATION, 'path': BASE_FINAL_SOURCE_REL,
                 'sha256': BASE_FINAL_SOURCE_SHA},
            'Attempt004 must remain the exact failed one-owner final attempt.')
    selected = field['earlier_failed_final_attempt']
    require(selected == previous['previous_final_attempt'] and
            selected['path'] == str(EARLIER_FINAL / 'RESULT.json') and selected['sha256'] == EARLIER_FINAL_RESULT_SHA and
            selected['publication_commit'] == EARLIER_FINAL_PUBLICATION and selected['aggregate_accepted'] is False and
            selected['aggregate_status'] == 'MODULE_STAGE_FAILED' and selected['failed_owner_reused'] is False and
            field['earlier_failed_final_owner'] == previous['previous_final_failed_owner'] == earlier['modules'][FIELD_TARGET] and
            earlier['failed_split_receipt'] == previous['failed_split_receipt'] == field['failed_split_receipt'] and
            earlier['prior_failed_final_owner'] == previous['prior_failed_final_owner'] == field['prior_failed_final_owner'] and
            earlier['reused_original_owner_receipts'] == previous['reused_original_owner_receipts'] ==
                field['reused_original_owner_receipts'] and
            earlier['reused_complete_context_validations'] == previous['reused_complete_context_validations'] ==
                field['reused_complete_context_validations'],
            'Attempt004 failure provenance, original owners, or supplemental validations changed.')


def validate_private_composition(field):
    """Require the actual new private theorem inside the complete owned record."""
    owner = field['modules'][FIELD_TARGET]
    records = owner['owned_declarations']
    names = [row['name'] for row in records]
    require(field['private_composition_helper_audited'] is True and
            field['expected_private_composition_helper'] == PRIVATE_HELPER and
            owner['owned_count'] == len(records) == len(set(names)) == 7 and
            all(row['module'] == FIELD_TARGET and not any(row[k] for k in ['axiom', 'partial', 'unsafe']) and
                set(row['axioms']) <= ALLOWED_AXIOMS for row in records),
            'Accepted final private helper must be part of all seven safe owned declarations.')
    matches = [row for row in records if row['name'].endswith('.' + PRIVATE_HELPER)]
    require(len(matches) == 1 and matches[0]['name'] == PRIVATE_HELPER_ACTUAL and
            matches[0] == field['private_composition_helper_record'],
            'Accepted final private helper record differs from the actual complete owned inventory.')
    return matches[0]


def select_symbolic_sources(selection, final_selection, explicit_override, symbolic_override):
    """Apply the actual accepted symbolic row after both immutable source layers."""
    sources = select_explicit_sources(selection, final_selection, explicit_override)
    replacement = symbolic_override['source_spec']
    require(symbolic_override['schema'] == 'p25-cell00-field-symbolic-source-override-v1' and
            symbolic_override['module'] == FIELD_TARGET and
            symbolic_override['original_selection'] == explicit_override['original_selection'] and
            symbolic_override['previous_source'] == explicit_override['new_source'] and
            symbolic_override['previous_source_override'] ==
                {'path': PREVIOUS_SOURCE_OVERRIDE_REL, 'bytes': 2256, 'sha256': PREVIOUS_SOURCE_OVERRIDE_SHA} and
            symbolic_override['new_source'] == {'path': FINAL_SOURCE_REL, 'bytes': 8128, 'sha256': FINAL_SOURCE_SHA} and
            symbolic_override['public_statement_count'] == 4 and symbolic_override['direct_project_import_count'] == 9 and
            symbolic_override['unchanged_source_graph_rows'] == 21 and symbolic_override['original_data_modified'] is False and
            symbolic_override['new_public_declarations'] == symbolic_override['new_assumptions'] == [] and
            symbolic_override['new_private_helpers'] == [PRIVATE_HELPER] and
            symbolic_override['private_helper_premise_count'] == 19 and
            symbolic_override['all_private_helper_premises_discharged_by_existing_certificates'] is True and
            replacement['path'] == FINAL_SOURCE_REL and replacement['source_sha256'] == FINAL_SOURCE_SHA,
            'Symbolic source override changes the accepted source, data, or declaration scope.')
    require({k: v for k, v in replacement.items() if k not in {'path', 'source_sha256'}} ==
            {k: v for k, v in sources[FIELD_TARGET].items() if k not in {'path', 'source_sha256'}},
            'Symbolic final imports or public API changed.')
    return {**sources, FIELD_TARGET: replacement}


def validate_failed_consumer(previous):
    """Require the exact observed disk failure before any of the five gates."""
    require(previous['schema'] == 'p25-cell00-five-consumers-strict-v4' and
            previous['status'] == 'FAILED' and previous['accepted'] is False and
            previous['publication_commit'] == FAILED_CONSUMER_PUBLICATION and
            previous['error'] == "OSError: [Errno 28] No space left on device: '" +
                str(FAILED_CONSUMER / FRESH_MODULES[0].split('.')[-1]) + "'" and
            previous['runner'] == {'path': '/workspace/p25-five-consumers-v4-20261126.py',
                                   'bytes': 102331, 'sha256': FAILED_CONSUMER_RUNNER_SHA} and
            previous['exception_log'] == {'path': str(FAILED_CONSUMER / 'RUNNER_EXCEPTION.log'),
                                          'bytes': 427, 'sha256': FAILED_CONSUMER_EXCEPTION_SHA},
            'Require the actual consumer attempt004 disk-space failure and exact runner/log identities.')
    require(previous['module_order'] == FRESH_MODULES and set(previous['modules']) == set(FRESH_MODULES) and
            previous['dependency_modules_compiled'] == previous['existing_owners_normally_recompiled'] ==
                previous['accepted_dependency_gates_rerun'] == [] and
            len(previous['dependency_objects']) == 40 and len(previous['source_graph']) == 45 and
            previous['accepted_field_private_composition_helper_checked'] is True and
            previous['accepted_field_actual_artifacts_reviewed_before_publication'] is True and
            previous['field_stage_receipt']['path'] == str(FIELD / 'RESULT.json') and
            previous['field_stage_receipt']['sha256'] == FIELD_RESULT_SHA and
            previous['complete_external_after_matches_before'] is False and
            all(previous[key] is False for key in ['original_cell00_decode_proved',
                'original_cell00_stored_floors_proved', 'original_cell00_simplex_guards_proved',
                'original_cellFloorNumerator_proved', 'original_cell00_headers_proved',
                'original_cell00_facet_indices_proved', 'Q96_proved', 'P2_5_proved']),
            'Disk retry must retain the unaccepted five-owner scope and accepted dependency provenance.')
    for index, module in enumerate(FRESH_MODULES):
        owner = previous['modules'][module]
        source = previous['source_graph'][module]
        require(owner['module'] == module and owner['accepted'] is False and owner['stages'] == {} and
                owner['status'] == ('RUNNING' if index == 0 else 'PENDING') and
                not any(key in owner for key in ['object', 'object_companions', 'owned_count', 'owned_declarations']) and
                owner['source_origin'] == {'commit': FAILED_CONSUMER_PUBLICATION,
                                           'path': source['path'], 'sha256': source['source_sha256']},
                'No previous consumer owner may have started a gate or supplied a target object: ' + module)


def check_disk_space(required_free_bytes, purpose):
    """Read live capacity; no deletion, cache adoption, or storage mutation."""
    require(type(required_free_bytes) is int and required_free_bytes > 0, 'Invalid disk-space requirement.')
    free = shutil.disk_usage(ROOT).free
    require(free >= required_free_bytes,
            f'DISK_SPACE: {purpose}: {free} bytes free; at least {required_free_bytes} required.')
    return {'checked_utc': now(), 'purpose': purpose, 'free_bytes': free,
            'required_free_bytes': required_free_bytes}


def validate_failed_parse(previous, disk_failure):
    """Keep the failed aggregate and its one actually accepted owner distinct."""
    require(previous['schema'] == 'p25-cell00-five-consumers-strict-v5' and
            previous['status'] == 'MODULE_STAGE_FAILED' and previous['accepted'] is False and
            previous['publication_commit'] == FAILED_PARSE_PUBLICATION and
            previous['failed_module'] == PARSE_TARGET and previous['failed_stage'] == 'normal' and
            previous['error'] == 'RuntimeError: ' + PARSE_TARGET + ' normal failed with exit 1.' and
            previous['runner'] == {'path': '/workspace/p25-five-consumers-v5-20261126.py',
                                   'bytes': 110371, 'sha256': FAILED_PARSE_RUNNER_SHA} and
            previous['exception_log'] == {'path': str(FAILED_PARSE / 'RUNNER_EXCEPTION.log'),
                                          'bytes': 426, 'sha256': FAILED_PARSE_EXCEPTION_SHA},
            'Require the actual consumer attempt005 failed aggregate and exact runner/log identities.')
    require(previous['module_order'] == FRESH_MODULES and set(previous['modules']) == set(FRESH_MODULES) and
            previous['source_graph'] == disk_failure['source_graph'] and
            previous['dependency_modules_compiled'] == previous['existing_owners_normally_recompiled'] ==
                previous['accepted_dependency_gates_rerun'] == [] and
            previous['private_records_written'] == [] and len(previous['dependency_objects']) == 40 and
            set(previous['dependency_objects']) == set(disk_failure['dependency_objects']) and
            all(previous['dependency_objects'][module]['sha256'] == row['sha256'] and
                previous['dependency_objects'][module]['source_sha256'] == row['source_sha256']
                for module, row in disk_failure['dependency_objects'].items()) and
            previous['previous_consumer_failed_owners'] == disk_failure['modules'] and
            previous['previous_consumer_failure'] == {
                'path': str(FAILED_CONSUMER / 'RESULT.json'), 'bytes': 5016911,
                'sha256': FAILED_CONSUMER_RESULT_SHA, 'publication_commit': FAILED_CONSUMER_PUBLICATION,
                'accepted': False, 'status': 'FAILED', 'normal_replay_audit_gates_started': 0} and
            previous['reused_original_owner_receipts'] == disk_failure['reused_original_owner_receipts'] and
            previous['reused_complete_context_validations'] == disk_failure['reused_complete_context_validations'] and
            previous['field_stage_receipt'] == disk_failure['field_stage_receipt'] and
            previous['accepted_field_private_composition_helper'] == disk_failure['accepted_field_private_composition_helper'] and
            previous['complete_external_after_matches_before'] is False and
            all(previous[key] is False for key in ['original_cell00_decode_proved',
                'original_cell00_stored_floors_proved', 'original_cell00_simplex_guards_proved',
                'original_cellFloorNumerator_proved', 'original_cell00_headers_proved',
                'original_cell00_facet_indices_proved', 'Q96_proved', 'P2_5_proved']),
            'The failed aggregate must preserve all forty accepted dependencies and separate prior histories.')
    for index, module in enumerate(FRESH_MODULES):
        owner = previous['modules'][module]
        source = previous['source_graph'][module]
        require(owner['module'] == module and owner['source_origin'] == {
                    'commit': FAILED_PARSE_PUBLICATION, 'path': source['path'],
                    'sha256': source['source_sha256']},
                'Original consumer source ownership changed: ' + module)
        if index == 0:
            require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
                    owner['object'] == {'path': str(FAILED_PARSE / 'lib' / (DECODED.replace('.', '/') + '.olean')),
                                        'bytes': 16208, 'sha256': DECODED_OBJECT_SHA} and
                    owner['object_companions'] == [] and owner['owned_count'] == len(owner['owned_declarations']) == 4 and
                    set(owner['stages']) == {'normal', 'replay', 'audit'} and
                    all(stage['status'] == 'PASSED' and stage['exit_code'] == 0 and stage['timed_out'] is False
                        for stage in owner['stages'].values()) and
                    owner['actual_external_import_count'] == EXPECTED_EXTERNAL_COUNT and
                    owner['complete_external_before'] == previous['complete_external_before'],
                    'Require the actual accepted Decoded owner; never rerun or relabel it.')
        elif index == 1:
            normal = owner['stages'].get('normal', {})
            require(owner['accepted'] is False and owner['status'] == 'NORMAL_FAILED' and
                    set(owner['stages']) == {'normal'} and
                    not any(key in owner for key in ['object', 'object_companions', 'owned_count', 'owned_declarations']) and
                    source['path'] == OLD_PARSE_SOURCE_REL and source['source_sha256'] == OLD_PARSE_SOURCE_SHA and
                    normal.get('status') == 'FAILED' and normal.get('exit_code') == 1 and
                    normal.get('timed_out') is False and normal.get('log_bytes') == 1046 and
                    normal.get('log_sha256') == FAILED_PARSE_NORMAL_SHA,
                    'OriginalParse must remain the exact failed normal-only owner without object credit.')
        else:
            require(owner['accepted'] is False and owner['status'] == 'PENDING' and owner['stages'] == {} and
                    not any(key in owner for key in ['object', 'object_companions', 'owned_count', 'owned_declarations']),
                    'Every remaining consumer must be the original pending owner: ' + module)


def select_parse_sources(sources, override):
    require(override['schema'] == 'p25-cell00-original-parse-source-override-v1' and
            override['module'] == PARSE_TARGET and
            override['repair_kind'] == 'symbolic-index-transport-after-consumer-attempt005' and
            override['previous_source'] == {'path': OLD_PARSE_SOURCE_REL, 'bytes': 1433, 'sha256': OLD_PARSE_SOURCE_SHA} and
            override['new_source'] == {'path': PARSE_SOURCE_REL, 'bytes': 3163, 'sha256': PARSE_SOURCE_SHA} and
            sources[PARSE_TARGET]['path'] == OLD_PARSE_SOURCE_REL and
            sources[PARSE_TARGET]['source_sha256'] == OLD_PARSE_SOURCE_SHA and
            override['new_private_expression_helpers'] == PARSE_PRIVATE_HELPERS and
            all(override[key] is True for key in ['imports_unchanged', 'public_statements_unchanged',
                'no_new_generic_Except_lemma', 'no_input_decoder_or_payload_change',
                'no_closed_target_premise_added', 'full_owned_audit_required_for_private_and_generated_declarations']) and
            override['new_formal_credit'] is False,
            'Require the exact reviewed private symbolic transport override and unchanged public scope.')
    replacement = override['source_spec']
    require(replacement['path'] == PARSE_SOURCE_REL and replacement['source_sha256'] == PARSE_SOURCE_SHA and
            {key: value for key, value in replacement.items() if key not in {'path', 'source_sha256'}} ==
                {key: value for key, value in sources[PARSE_TARGET].items() if key not in {'path', 'source_sha256'}},
            'OriginalParse imports, public API, or module scope changed.')
    return {**sources, PARSE_TARGET: replacement}


def validate_parse_helpers(records):
    selected = []
    for helper in PARSE_PRIVATE_HELPERS:
        matches = [row for row in records if row['name'].startswith('_private.' + PARSE_TARGET + '.') and
                   row['name'].endswith('.' + helper)]
        require(len(matches) == 1 and matches[0]['module'] == PARSE_TARGET and
                not any(matches[0][key] for key in ['axiom', 'partial', 'unsafe']) and
                set(matches[0]['axioms']) <= ALLOWED_AXIOMS,
                'The complete owned audit must contain the safe private expression helper: ' + helper)
        selected.append(matches[0])
    return selected


def link_dependency_bytes(original, destination):
    """Link already-bound immutable imports; never overwrite or follow aliases."""
    original, destination = Path(original), Path(destination)
    require(original.is_file() and not original.is_symlink(),
            'Accepted dependency must be a physical regular file: ' + str(original))
    require(not os.path.lexists(destination), 'Preserve existing target: ' + str(destination))
    require(original.stat().st_dev == destination.parent.stat().st_dev,
            'Hardlink reuse requires the same filesystem; no implicit copy fallback')
    os.link(original, destination, follow_symlinks=False)
    require(os.path.samefile(original, destination), 'Dependency hardlink identity differs')


FRESH_SELECTION_REL = 'docs/verification/20261126-p2-5-resumed/cell00-fresh-context/FRESH_CONTEXT_SELECTION.json'
IMMUTABLE_V7_SHA = '4d0b9e19a564f99416fc5f57ccb41f0570df2b3af53d5a61277f31b3ee063197'
IMMUTABLE_RECOVERY_SHA = 'd6d895b80f07c9bd499501cce3e275a271ccd8ddfc166826942953afa960d542'
IMMUTABLE_RECOVERY_SELECTION_SHA = 'cd0b812eaf659d675406c594f7eae66b4ea550bdd30f874b1a2876ebdef04cbf'
IMMUTABLE_BLOCKERS_SHA = '7ad7bdadcf10290d053af16fdd89393e8778a71e5dee08e4fa857dd3a49e4580'
PARTIAL_RESTORE_SHA = 'cf26553c585e5a5e4e2527095935af092d402381c47fc6595d9e5a08093cac17'

# Enabled after the complete actual export and exact selected sources were
# reviewed. Object bytes are independently revalidated on the actual P3 root.
V9_SELECTION_REL = 'docs/verification/20261126-p2-5-resumed/cell00-three-consumers-v9/SOURCE_AND_RECEIPT_SELECTION.json'
PRIOR_V8_OUT = ROOT / '.lake/diagnostic/p25-cell00-four-consumers-attempt008'
PRIOR_V8_PUBLICATION = '2106ae104bb98cd3d647a202df069b380e2de5bc'
PRIOR_V8_RUNNER_REL = 'docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v8.py'
IMMUTABLE_V8_SHA = 'ffcc4aff64705a29d9fa94faf44350753d4ba6faf2abbd0c748d634baf363beb'
IMMUTABLE_FRESH_SELECTION_SHA = '1be717f81e2886e5291bdff7f129dbff8d75453656d6afa88c54cfd8168f01ca'
V8_EXPORT_MANIFEST_REL = 'docs/verification/20261126-p2-5-resumed/consumer-attempt008/EXPORT_MANIFEST.json'
V8_EXPORT_MANIFEST_SHA = '7c532493c4542387ff343808e675ae05fd317d76c036fc95b93f8e36fe7f306a'
PRIOR_V8_RESULT_SHA = 'a95712c736aea7495c6a41916e82b1f27d04772e2584fed50c13486ce6bb33dd'
PRIOR_V8_REMATERIALIZATION_SHA = 'f6c341af667d13db501ac34b5cc37d6cad1409c51f56156ccfd308deb5df82a1'
V8_ARTIFACTS_REVIEWED = True
PARSE_OBJECT_SHA = '5bb7d93c7f336040afae0aedfb5b5f26c5c78f9a61400738ca2f299c0760c03f'
ORIGINAL_FLOORS = FRESH_MODULES[2]
OLD_FLOORS_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-consumer/ImbalancedChen/P2Saving16Cell00OriginalFloors.lean'
OLD_FLOORS_SOURCE_SHA = 'a74eb2b792fafcb697c0112ed462cc28caf9cf3a4321c16bbb8496e9605efaae'
FLOORS_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-floors-transport/ImbalancedChen/P2Saving16Cell00OriginalFloors.lean'
FLOORS_SOURCE_SHA = 'd807f957f4c83157cb4288bc59609bb54995a1864d10a91979dec988beb6a818'
FLOORS_OVERRIDE_REL = 'docs/source-only/20261126-p2-5-cell00-floors-transport/SOURCE_OVERRIDE.json'
FLOORS_OVERRIDE_SHA = 'af6eef3b8d1d09a2b6f4c65ce7c262510445d8b1b50ab8455bf5836305c1d092'
PENDING_SOURCE_REVIEW_REL = 'docs/source-only/20261126-p2-5-cell00-floors-transport/optional-pending-consumers/ROOT_SELECTED_SOURCE_REVIEW.json'
PENDING_SOURCE_REVIEW_SHA = '1f74d16efda89450c01d58a7fa2a75092e7a13fab01eef33d0d4c777e121f4f2'
PENDING_SOURCE_IDENTITIES = {
    FRESH_MODULES[3]: {
        'path': 'docs/source-only/20261126-p2-5-cell00-floors-transport/optional-pending-consumers/after/ImbalancedChen/P2Saving16Cell00OriginalArithmetic.lean',
        'bytes': 2254, 'sha256': '70363c3b1f704889b3b6e68086cb4439170e01e810d6496b7ffe4e66d24ae24f'},
    FRESH_MODULES[4]: {
        'path': 'docs/source-only/20261126-p2-5-cell00-floors-transport/optional-pending-consumers/after/ImbalancedChen/P2Saving16Cell00OriginalSourceFacts.lean',
        'bytes': 2124, 'sha256': 'ca682b04d22c87d47f6adb205e8b7da5074da3074cafd4157f916297336607a7'},
}


def require_v9_pins():
    require(V8_ARTIFACTS_REVIEWED is True and all(isinstance(value, str) and
            re.fullmatch(r'[0-9a-f]{64}', value) for value in
            [PRIOR_V8_RESULT_SHA, PRIOR_V8_REMATERIALIZATION_SHA, FLOORS_OVERRIDE_SHA, PENDING_SOURCE_REVIEW_SHA]),
            'SOURCE_ONLY: complete actual v8 evidence and the final source override must be reviewed and pinned before any workspace access')


def require_new_gate(module, label):
    require(module in CONTINUATION_MODULES and label in {'normal', 'replay', 'audit'},
            'Only the three unaccepted consumers may execute new compiler gates')


def validate_dependency_identities(identities, objects, parse_sha):
    expected = {module: row['sha256'] for module, row in objects.items()}
    require(len(expected) == 41 and PARSE_TARGET not in expected and
            parse_sha == PARSE_OBJECT_SHA, 'Require the 42 exact accepted dependency identities')
    expected[PARSE_TARGET] = parse_sha
    require(identities == expected and len(identities) == 42,
            'Require the 42 exact accepted dependency identities')


def select_floors_sources(sources, override):
    require(override['schema'] == 'p25-cell00-original-floors-source-override-v1' and
            override['module'] == ORIGINAL_FLOORS and
            override['previous_source'] == {'path': OLD_FLOORS_SOURCE_REL,
                'bytes': 3900, 'sha256': OLD_FLOORS_SOURCE_SHA} and
            override['new_source'] == {'path': FLOORS_SOURCE_REL,
                'bytes': 5557, 'sha256': FLOORS_SOURCE_SHA},
            'Exact old/new Floors source selection differs')
    old = sources[ORIGINAL_FLOORS]
    require(old['path'] == OLD_FLOORS_SOURCE_REL and old['source_sha256'] == OLD_FLOORS_SOURCE_SHA,
            'Floors overlay is not based on the actual v8 source')
    spec = dict(old, path=FLOORS_SOURCE_REL, source_sha256=FLOORS_SOURCE_SHA)
    require(override['source_spec'] == spec and all(override[key] is True for key in
            ['imports_unchanged', 'options_unchanged', 'public_statements_unchanged',
             'no_input_decoder_or_payload_change', 'no_closed_target_premise_added',
             'full_owned_audit_required_for_private_and_generated_declarations']) and
            override['new_private_expression_helpers'] == [] and
            override['reused_existing_transport_theorem'] == 'Eq.subst',
            'Floors override changed imports, statements or the reviewed proof-only scope')
    return {**sources, ORIGINAL_FLOORS: spec}


def select_pending_source_overlays(sources, review, original_sources):
    """Apply only the two explicitly selected, still-pending proof expressions."""
    require(len(sources) == len(original_sources) == 45 and set(sources) == set(original_sources) and
            {m for m in sources if sources[m] != original_sources[m]} == {ORIGINAL_FLOORS},
            'Only reviewed Floors may differ before the two pending overlays')
    require(review['schema'] == 'p25-v9-root-selected-pending-source-review-v1' and
            review['status'] == 'ROOT_SELECTED_EXISTING_SOURCE_ONLY_POSTIMAGES_UNCOMPILED' and
            review['actual_prior_result_sha256'] == PRIOR_V8_RESULT_SHA and
            review['actual_prior_aggregate_accepted'] is False and
            review['normal_replay_owned_still_required_for_each_owner'] is True and
            review['proof_statements_or_acceptance_gates_weakened'] is False and
            review['new_formal_credit'] is False and review['P2_5_proved'] is False and
            review['successor_source_scope'] == {
                'accepted_dependencies_reused': 42, 'allowed_changed_sources': CONTINUATION_MODULES,
                'new_owners': 3, 'stages_per_owner': 3, 'total_new_stages': 9,
                'total_source_modules': 45, 'unchanged_source_modules': 42} and
            [row['module'] for row in review['rows']] == CONTINUATION_MODULES[1:] and
            set(PENDING_SOURCE_IDENTITIES) == set(CONTINUATION_MODULES[1:]),
            'Root-selected pending source scope or original outcome differs')
    result = dict(sources)
    for row in review['rows']:
        module = row['module']
        old = original_sources[module]
        new = PENDING_SOURCE_IDENTITIES[module]
        require(row['previous_source_spec'] == sources[module] == old and row['new_source'] == new and
                row['previous_source']['path'] == old['path'] and
                row['previous_source']['sha256'] == old['source_sha256'] and
                row['source_spec'] == dict(old, path=new['path'], source_sha256=new['sha256']) and
                row['prior_actual_status'] == 'PENDING' and row['prior_actual_stages'] == {} and
                row['public_header_count'] == 2 and all(row[key] is True for key in
                    ['imports_unchanged', 'options_unchanged', 'public_headers_unchanged']) and
                row['new_assumptions'] == row['new_private_helpers'] == [] and
                row['current_context_accepted'] is False and row['reused_existing_transport_theorem'] == 'Eq.subst',
                'Pending source identity, unchanged interface or actual pending outcome differs: ' + module)
        result[module] = row['source_spec']
    require({m for m in result if result[m] != original_sources[m]} == set(CONTINUATION_MODULES) and
            {m: row for m, row in result.items() if m not in CONTINUATION_MODULES} ==
                {m: row for m, row in original_sources.items() if m not in CONTINUATION_MODULES} and
            len([m for m in result if m not in CONTINUATION_MODULES]) == 42,
            'The three source overlays changed an accepted dependency or exceeded the exact scope')
    return result


def validate_v8_terminal_metadata(prior, remat, cfg, selected):
    """Validate actual terminal records without granting aggregate success."""
    require(prior['schema'] == 'p25-cell00-four-consumers-fresh-context-strict-v8' and
            prior['publication_commit'] == PRIOR_V8_PUBLICATION and prior['accepted'] is False and
            prior['status'] == 'MODULE_STAGE_FAILED' and prior['failed_module'] == ORIGINAL_FLOORS and
            prior['failed_stage'] == 'normal' and prior['runner']['sha256'] == IMMUTABLE_V8_SHA and
            prior['strict_flags'] == FLAGS and prior['stage_wall_limit_seconds'] == 600 and
            prior['module_order'] == V8_CONTINUATION_MODULES and
            set(prior['modules']) == set(V8_CONTINUATION_MODULES) and
            prior['complete_external_after_matches_before'] is False and 'fresh_context_after' not in prior and
            prior['P2_5_proved'] is False and prior['Q96_proved'] is False,
            'Actual v8 terminal failure/publication/scope differs')
    parse = prior['modules'][PARSE_TARGET]
    require(parse['accepted'] is True and parse['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
            parse['module'] == PARSE_TARGET and parse['source_origin'] == {
                'commit': PRIOR_V8_PUBLICATION, 'path': PARSE_SOURCE_REL, 'sha256': PARSE_SOURCE_SHA} and
            parse['object']['sha256'] == PARSE_OBJECT_SHA and parse['object_companions'] == [] and
            parse['owned_count'] == len(parse['owned_declarations']) == 7 and
            set(parse['stages']) == {'normal', 'replay', 'audit'} and
            all(row['status'] == 'PASSED' and row['exit_code'] == 0 and row['timed_out'] is False
                for row in parse['stages'].values()) and
            prior['private_parse_helpers_audited'] is True and
            validate_parse_helpers(parse['owned_declarations']) == parse['private_expression_helpers'] ==
                prior['private_parse_helper_records'], 'Actual accepted Parse owner/private inventory differs')
    floors = prior['modules'][ORIGINAL_FLOORS]
    failed = floors['stages']['normal']
    require(floors['accepted'] is False and floors['status'] == 'NORMAL_FAILED' and
            set(floors['stages']) == {'normal'} and 'object' not in floors and
            failed['status'] == 'FAILED' and failed['exit_code'] == 124 and failed['timed_out'] is True and
            failed['seconds'] == 600.331 and failed['log_bytes'] == 0 and
            failed['log_sha256'] == hashlib.sha256(b'').hexdigest() and
            failed['command'] == [str(LEAN), *FLAGS, '--root=' + str(PRIOR_V8_OUT / 'src'), '-o',
                str(PRIOR_V8_OUT / 'lib' / (ORIGINAL_FLOORS.replace('.', '/') + '.olean')),
                str(PRIOR_V8_OUT / 'src' / (ORIGINAL_FLOORS.replace('.', '/') + '.lean'))],
            'Actual unaccepted Floors timeout differs')
    for module in CONTINUATION_MODULES[1:]:
        owner = prior['modules'][module]
        require(owner['accepted'] is False and owner['status'] == 'PENDING' and owner['stages'] == {} and
                'object' not in owner, 'A pending v8 consumer acquired unsupported credit: ' + module)
    require(remat['schema'] == 'p25-exact-normal-rematerialization-fresh-context-v8' and
            remat['publication_commit'] == PRIOR_V8_PUBLICATION and remat['runner_sha256'] == IMMUTABLE_V8_SHA and
            remat['selection_sha256'] == IMMUTABLE_FRESH_SELECTION_SHA and
            remat['status'] == 'EXACT_OBJECTS_READY_FOR_NEW_CONSUMER_CONTEXT' and
            remat['exact_objects_ready'] is True and remat['accepted'] is False and
            remat['new_formal_credit'] is False and remat['P2_5_proved'] is False and
            remat['replay_stages'] == remat['owned_audit_stages'] == [] and
            remat['old_receipts_changed'] is False and remat['old_snapshots_synthesized'] is False and
            remat['old_v7_preflight_passed'] is False,
            'Actual completed normal rematerialization metadata differs')
    order = selected['normal_order']
    require(len(order) == len(set(order)) == 10 and
            [row['module'] for row in remat['normal_stages']] == order ==
                prior['dependency_modules_compiled'] == prior['existing_owners_normally_recompiled'] and
            remat['normal_stages'] == prior['normal_rematerialization_stages'] and
            set(remat['available_objects_reused_without_normal']) == set(cfg['objects']) - set(order) and
            len(remat['available_objects_reused_without_normal']) == 31 and
            prior['accepted_dependency_gates_rerun'] == prior['consumer_phase_dependency_modules_compiled'] == [] and
            prior['decoded_gates_rerun'] == [] and prior['failed_parse_aggregate_relabelled'] is False and
            prior['old_v7_preflight_passed'] is False and prior['old_recovery_complete'] is False and
            prior['old_snapshots_synthesized'] is False and
            prior['historical_archive_gaps'] == remat['historical_archive_gaps'] and
            len(prior['historical_archive_gaps']) == 5 and
            {r['path']: r for r in prior['historical_archive_gaps']} ==
                {r['path']: r for r in selected['historical_envelope_exceptions']} and
            prior['fresh_context_before'] == remat['fresh_context_before'],
            'Actual v8 31/10 partition, historical records or failed aggregates changed')
    expected_witnesses = {r['realpath']: (r['bytes'], r['sha256']) for r in cfg['witnesses']}
    for stage in remat['normal_stages']:
        module = stage['module']
        row = cfg['objects'][module]
        obj = PRIOR_V8_OUT / 'rematerialization/lib' / (module.replace('.', '/') + '.olean')
        source = PRIOR_V8_OUT / 'rematerialization/src' / (module.replace('.', '/') + '.lean')
        witness = stage['input_snapshot_before']
        require(stage['purpose'] == 'exact-historical-byte-rematerialization' and
                stage['status'] == 'PASSED' and stage['exit_code'] == 0 and stage['timed_out'] is False and
                stage['exact_historical_object_match'] is True and
                stage['expected_object_sha256'] == stage['object']['sha256'] == row['sha256'] and
                stage['observed_object'] == stage['object'] and stage['object']['path'] == str(obj) and
                stage['object_companions'] == [] and stage['cwd'] == str(ROOT) and
                stage['LEAN_PATH'] == remat['approved_LEAN_PATH'] and
                stage['command'] == [str(LEAN), *FLAGS,
                    '--root=' + str(PRIOR_V8_OUT / 'rematerialization/src'), '-o', str(obj), str(source)] and
                stage['input_snapshot_after'] == witness and len(witness) == 14 and
                {r['realpath']: (r['bytes'], r['sha256']) for r in witness} == expected_witnesses and
                all(r['path'] == r['realpath'] for r in witness),
                'Actual historical normal command/object/witness binding differs: ' + module)
    identities = {m: r['sha256'] for m, r in prior['dependency_objects'].items()}
    require(set(identities) == set(cfg['objects']) and all(identities[m] == r['sha256']
            for m, r in cfg['objects'].items()), 'Actual v8 41-dependency identity set differs')
    identities[PARSE_TARGET] = parse['object']['sha256']
    validate_dependency_identities(identities, cfg['objects'], PARSE_OBJECT_SHA)


def verify_prior_v8(prepared, exact, published):
    """Read every actual exported artifact and all prior frozen bytes; no gaps added."""
    require_v9_pins()
    manifest_path = published(V8_EXPORT_MANIFEST_REL, V8_EXPORT_MANIFEST_SHA)
    exported = json.loads(manifest_path.read_text())
    require(len(exported['files']) == 40 and exported['result_sha256'] == PRIOR_V8_RESULT_SHA and
            exported['result_bytes'] == 5274478 and exported['sha256'] ==
                'cff4756b09dddc35e63a56121f0dcff23c83f5d5e01c80ab21de789f29269e5b',
            'Actual v8 export scope differs')
    for name, row in exported['files'].items():
        require(Path(name).is_relative_to(PRIOR_V8_OUT) and '..' not in Path(name).parts,
                'Unexpected v8 exported artifact path')
        exact(name, row['sha256'], row['bytes'])
    path = exact(PRIOR_V8_OUT / 'RESULT.json', PRIOR_V8_RESULT_SHA, 5274478)
    remat_path = exact(PRIOR_V8_OUT / 'rematerialization/RESULT.json', PRIOR_V8_REMATERIALIZATION_SHA, 2879970)
    prior, remat = json.loads(path.read_text()), json.loads(remat_path.read_text())
    validate_v8_terminal_metadata(prior, remat, prepared['cfg'], prepared['selection'])
    require(prior['source_graph'] == prepared['prior_v8_source_graph'], 'Original v8 source graph changed')
    require(prior['normal_rematerialization_receipt'] == record_file(remat_path) and
            prior['prior_partial_restore'] == remat['prior_partial_restore'] == prepared['partial_restore'],
            'Original v8 rematerialization/partial-restore descriptors differ')
    old_runner = exact(prior['runner']['path'], IMMUTABLE_V8_SHA, prior['runner']['bytes'])
    require(subprocess.check_output(['git', '-c', 'protocol.allow=never', 'show',
                PRIOR_V8_PUBLICATION + ':' + PRIOR_V8_RUNNER_REL], cwd=ROOT, timeout=120) == old_runner.read_bytes(),
            'Actual v8 runner bytes differ from their original publication')
    for container in (prior, remat):
        require(not any(row['path'] in container['frozen_inputs'] for row in container['historical_archive_gaps']),
                'A prior missing envelope is falsely represented as verified bytes')
        for name, expected in container['frozen_inputs'].items():
            exact(name, expected)
    prior_runtime = {p: h for p, h in prior['frozen_inputs'].items()
                     if p.startswith(('/mathlib/', '/workspace/toolchains/'))}
    require(prior_runtime == prepared['runtime_pins'] and len(prior_runtime) == 15940,
            'Actual v8 runtime pin set differs')
    snapshots = [prior['fresh_context_before'], remat['fresh_context_after'], prior['complete_external_before']]
    # The preserved upstream envelope also has historical-availability annotations.
    # v8's real observations serialize these three identity fields only. Keep every
    # module/object/companion record, without inventing the absent annotations.
    expected_entries = [{'module': row['module'], 'object': row['object'], 'companions': row['companions']}
                        for row in prepared['external_entries']]
    for descriptor in snapshots:
        snapshot_path = exact(descriptor['path'], descriptor['sha256'], descriptor['bytes'])
        snapshot = json.loads(snapshot_path.read_text())
        require(snapshot['provider_roots'] == list(map(str, prepared['providers'])) and
                snapshot['module_count'] == 5312 and snapshot['entries'] == expected_entries and
                snapshot['source_complete_snapshot'] == prepared['upstream_record'] and
                snapshot['source_accepted_receipt'] == prepared['upstream_receipt'] and
                snapshot['historical_missing_hashes_invented'] is False,
                'Actual v8 before/rematerialization-after current context differs')
    require(not os.path.lexists(PRIOR_V8_OUT / 'FRESH_CONTEXT_AFTER.json'),
            'Do not add a success-only root context to the failed v8 attempt')
    exception = prior['exception_log']
    exact(exception['path'], exception['sha256'], exception['bytes'])
    parse = prior['modules'][PARSE_TARGET]
    for key in ['source_copy', 'audit_source', 'object', 'declarations', 'inventory']:
        row = parse[key]
        exact(row['path'], row['sha256'], row['bytes'])
        require(prior['frozen_inputs'].get(row['path']) == row['sha256'], 'Accepted Parse artifact was not frozen')
    require(parse['object']['path'] == str(PRIOR_V8_OUT / 'lib' / (PARSE_TARGET.replace('.', '/') + '.olean')) and
            not any(os.path.lexists(parse['object']['path'] + suffix) for suffix in ('.private', '.server')),
            'Actual accepted Parse object location/companions differ')
    for label, stage in parse['stages'].items():
        exact(stage['log'], stage['log_sha256'], stage['log_bytes'])
        require(prior['frozen_inputs'].get(stage['log']) == stage['log_sha256'], 'Accepted Parse stage log was not frozen')
    require(parse['stages']['normal']['command'] == [str(LEAN), *FLAGS, '--root=' + str(PRIOR_V8_OUT / 'src'),
                '-o', parse['object']['path'], parse['source_copy']['path']] and
            parse['stages']['replay']['command'] == [str(CHECKER), '--verbose', PARSE_TARGET] and
            parse['stages']['audit']['command'] == [str(LEAN), *FLAGS, '--root=' + str(PRIOR_V8_OUT / 'audit'),
                parse['audit_source']['path']], 'Actual accepted Parse strict commands differ')
    records, inventory, imports = read_audit(Path(parse['stages']['audit']['log']), PARSE_TARGET)
    require(records == parse['owned_declarations'] == json.loads(Path(parse['declarations']['path']).read_text()) and
            inventory == json.loads(Path(parse['inventory']['path']).read_text()) and
            imports == parse['actual_project_closure'] and
            validate_parse_helpers(records) == parse['private_expression_helpers'] == prior['private_parse_helper_records'],
            'Actual accepted Parse complete audit and serialized inventories differ')
    for stage in remat['normal_stages']:
        exact(stage['log'], stage['log_sha256'], stage['log_bytes'])
        row = stage['object']
        exact(row['path'], row['sha256'], row['bytes'])
        require(not any(os.path.lexists(row['path'] + suffix) for suffix in ('.private', '.server')),
                'Unexpected companions on an exact reconstructed object')
    require(not any(os.path.lexists(PRIOR_V8_OUT / 'lib' / (m.replace('.', '/') + '.olean'))
                    for m in CONTINUATION_MODULES), 'An unaccepted v8 target object exists; never reuse it')
    prepared.update(prior_v8=prior, prior_v8_rematerialization=remat,
                    prior_v8_receipt=record_file(path), prior_v8_rematerialization_receipt=record_file(remat_path))


def inspect_history_requirements(requirements, exceptions, object_aliases):
    """Read actual bytes; unavailable envelopes and pending objects are not bound."""
    allowed = {row['path']: row for row in exceptions}
    require(len(allowed) == len(exceptions), 'Duplicate historical envelope tuple')
    frozen, gaps, pending = {}, [], {}
    for name, expected in requirements.items():
        path = Path(name)
        if name in allowed:
            row = allowed[name]
            require(row['sha256'] == expected and row['bytes'] == 4302154,
                    'Wrong historical envelope tuple: ' + name)
        if os.path.lexists(path):
            require(path.is_file() and not path.is_symlink() and digest(path) == expected,
                    'Historical bytes differ: ' + name)
            if name in allowed:
                require(path.stat().st_size == allowed[name]['bytes'], 'Historical envelope size differs: ' + name)
            frozen[name] = expected
        elif name in allowed:
            gaps.append(allowed[name])
        elif name in object_aliases:
            require(object_aliases[name]['sha256'] == expected, 'Pending object alias identity differs: ' + name)
            pending[name] = object_aliases[name]
        else:
            raise RuntimeError('Unapproved missing historical input: ' + name)
    return {'frozen': frozen, 'archive_gaps': gaps, 'pending_object_paths': pending}


def resolve_external_entries(entries, providers):
    """Observe real provider/companion resolution, with no Path or hash substitution."""
    require(len(providers) == len(set(map(str, providers))) and
            all(p.is_dir() and not (p / 'ImbalancedChen').exists() for p in providers),
            'Duplicate or project-containing external provider')
    names, observed = set(), []
    for row in entries:
        name = row['module']
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name)
                and name not in names, 'Invalid or duplicate external module')
        names.add(name)
        relative = name.replace('.', '/') + '.olean'
        found = [p / relative for p in providers if (p / relative).is_file()]
        require(len(found) == 1 and str(found[0]) == row['object']['path'],
                'Missing or shadowed external provider: ' + name)
        actual_companions = [str(found[0]) + suffix for suffix in ('.private', '.server')
                             if Path(str(found[0]) + suffix).is_file()]
        require(actual_companions == [r['path'] for r in row['companions']],
                'External companion inventory changed: ' + name)
        for record in [row['object'], *row['companions']]:
            path = Path(record['path'])
            require(path.is_file() and not path.is_symlink() and path.stat().st_size == record['bytes']
                    and digest(path) == record['sha256'], 'External bytes differ: ' + str(path))
        observed.append({'module': name, 'object': dict(row['object']),
                         'companions': [dict(r) for r in row['companions']]})
    return observed


def full_missing_order(objects, available, allowed):
    """Traverse every accepted object, including cached intermediaries, then filter."""
    available, allowed = set(available), set(allowed)
    require(available <= set(objects) and set(objects) - available <= allowed <= set(objects),
            'Missing objects exceed the exact normal whitelist')
    done, active, order = set(), set(), []

    def visit(name):
        require(name in objects, 'Unknown project dependency: ' + name)
        require(name not in active, 'Cyclic complete accepted-object graph')
        if name in done:
            return
        active.add(name)
        for dependency in objects[name]['project_imports']:
            visit(dependency)
        active.remove(name)
        done.add(name)
        order.append(name)

    for name in sorted(objects):
        visit(name)
    return [name for name in order if name not in available]


def verify_frozen(frozen):
    require(all(Path(path).is_file() and digest(path) == expected for path, expected in frozen.items()),
            'Frozen input changed or disappeared')


def current_context(prepared, phase):
    """A newly timed observation, never a replacement for an old envelope."""
    started = now()
    require(git('rev-parse', 'HEAD') == prepared['publication'] and
            not git('status', '--porcelain', '--untracked-files=no'), 'Current publication changed')
    require(git('rev-parse', 'HEAD', cwd=Path('/mathlib')) == MATHLIB_PIN, 'Current mathlib pin changed')
    require(all(not os.path.lexists(row['path']) for row in prepared['archive_gaps']),
            'An archival gap changed availability during this fresh context')
    verify_frozen(prepared['frozen'])
    entries = resolve_external_entries(prepared['external_entries'], prepared['providers'])
    require(len(entries) == EXPECTED_EXTERNAL_COUNT and
            sum(len(row['companions']) for row in entries) == EXPECTED_EXTERNAL_COMPANIONS,
            'Current external scope changed')
    return {'schema': 'p25-actual-fresh-external-context-v9', 'phase': phase,
            'started_utc': started, 'finished_utc': now(),
            'provider_roots': list(map(str, prepared['providers'])), 'module_count': len(entries),
            'companion_count': EXPECTED_EXTERNAL_COMPANIONS, 'runtime_pin_count': 15940,
            'source_complete_snapshot': prepared['upstream_record'],
            'source_accepted_receipt': prepared['upstream_receipt'],
            'historical_missing_hashes_invented': False, 'entries': entries}


def fresh_preflight(publication, selection_path, selection_sha, runner_sha):
    """Read-only successor preparation; all 42 dependencies must already exist."""
    global SOURCES
    require_v9_pins()
    require(sys.flags.optimize == 0, 'Strict assertions require Python without -O')
    require(re.fullmatch(r'[0-9a-f]{40}', publication or '') and
            re.fullmatch(r'[0-9a-f]{64}', selection_sha or '') and
            re.fullmatch(r'[0-9a-f]{64}', runner_sha or ''), 'Exact publication/runner/selection pins required')
    require(ROOT.resolve() == ROOT and git('rev-parse', 'HEAD') == publication and
            not git('status', '--porcelain', '--untracked-files=no'), 'Use the exact clean published P3 checkout')
    require(not os.path.lexists(OUT), 'Preserve existing attempt009')
    frozen = {}

    def exact(path, expected, size=None):
        path = Path(path)
        require(path.is_file() and not path.is_symlink() and digest(path) == expected
                and (size is None or path.stat().st_size == size), 'Pinned input differs: ' + str(path))
        frozen[str(path)] = expected
        return path

    def published(relative, expected, size=None, actual=None):
        path = exact(ROOT / relative if actual is None else actual, expected, size)
        blob = subprocess.check_output(['git', '-c', 'protocol.allow=never', 'show', publication + ':' + relative],
                                       cwd=ROOT, timeout=120)
        require(blob == path.read_bytes(), 'Input differs from published Git bytes: ' + relative)
        return path

    published(RUNNER_REL, runner_sha, actual=Path(__file__).resolve())
    preserved_v6 = subprocess.check_output(
        ['git', '-c', 'protocol.allow=never', 'show', RESOURCE_BASE_PUBLICATION + ':' + RESOURCE_BASE_REL],
        cwd=ROOT, timeout=120)
    require(hashlib.sha256(preserved_v6).hexdigest() == RESOURCE_BASE_SHA,
            'Required preserved v6 Git blob differs or is unavailable before successor work')
    require(Path(selection_path) == ROOT / V9_SELECTION_REL, 'Use the fixed v9 successor selection path')
    successor_path = published(V9_SELECTION_REL, selection_sha)
    successor = json.loads(successor_path.read_text())
    require(successor['schema'] == 'p25-cell00-three-consumers-successor-selection-v1' and
            successor['status'] == 'ACTUAL_PARTIAL_V8_EVIDENCE_REVIEWED_FOR_SUCCESSOR' and
            successor['target_root'] == str(ROOT) and successor['output_root'] == str(OUT) and
            successor['consumer_modules'] == CONTINUATION_MODULES and successor['dependency_object_count'] == 42 and
            successor['dependency_modules_to_compile'] == successor['parse_gates_to_rerun'] == [] and
            successor['prior_v8'] == {'path': str(PRIOR_V8_OUT / 'RESULT.json'), 'bytes': 5274478,
                'sha256': PRIOR_V8_RESULT_SHA, 'publication_commit': PRIOR_V8_PUBLICATION, 'accepted': False} and
            successor['prior_v8_rematerialization'] == {'path': str(PRIOR_V8_OUT / 'rematerialization/RESULT.json'),
                'bytes': 2879970, 'sha256': PRIOR_V8_REMATERIALIZATION_SHA, 'accepted': False, 'new_formal_credit': False} and
            successor['source_overrides'] == [
                {'module': ORIGINAL_FLOORS, 'path': FLOORS_OVERRIDE_REL, 'sha256': FLOORS_OVERRIDE_SHA},
                *[{'module': module, 'path': PENDING_SOURCE_REVIEW_REL, 'sha256': PENDING_SOURCE_REVIEW_SHA}
                  for module in CONTINUATION_MODULES[1:]]] and
            successor['parse_object_sha256'] == PARSE_OBJECT_SHA and
            successor['external_counts'] == {'modules': 5312, 'companions': 10624, 'runtime_pins': 15940, 'providers': 9} and
            successor['strict_flags'] == FLAGS and successor['stage_wall_limit_seconds'] == 600 and
            successor['initial_free_reserve_bytes'] == MIN_INITIAL_FREE_BYTES and
            successor['per_stage_free_reserve_bytes'] == GATE_WORKING_HEADROOM_BYTES and
            successor['P2_5_proved'] is False and successor['Q96_proved'] is False,
            'Exact v9 successor receipt/source/42-dependency scope differs')
    for name, relative, expected in [
            ('v8_runner', PRIOR_V8_RUNNER_REL, IMMUTABLE_V8_SHA),
            ('v8_export_manifest', V8_EXPORT_MANIFEST_REL, V8_EXPORT_MANIFEST_SHA),
            ('v8_selection', FRESH_SELECTION_REL, IMMUTABLE_FRESH_SELECTION_SHA)]:
        row = successor['inputs'][name]
        require(row['path'] == relative and row['sha256'] == expected, 'Successor control identity differs: ' + name)
        published(relative, expected, row['bytes'])
    selection_file = published(FRESH_SELECTION_REL, IMMUTABLE_FRESH_SELECTION_SHA)
    selected = json.loads(selection_file.read_text())
    require(selected['schema'] == 'p25-cell00-fresh-context-selection-v1' and
            selected['target_root'] == str(ROOT) and selected['output_root'] == str(PRIOR_V8_OUT) and
            selected['consumer_modules'] == V8_CONTINUATION_MODULES and
            selected['external_counts'] == {'modules': 5312, 'companions': 10624, 'runtime_pins': 15940, 'providers': 9},
            'Fresh selection scope changed')
    pins = {'v7_runner': IMMUTABLE_V7_SHA, 'recovery_runner': IMMUTABLE_RECOVERY_SHA,
            'recovery_selection': IMMUTABLE_RECOVERY_SELECTION_SHA, 'archive_blockers': IMMUTABLE_BLOCKERS_SHA,
            'consumer005_receipt': FAILED_PARSE_RESULT_SHA}
    for name, expected in pins.items():
        require(selected['inputs'][name]['sha256'] == expected, 'Immutable control identity changed: ' + name)
    for name, row in selected['inputs'].items():
        # This exact raw receipt is supplied by the published bootstrap capsules.
        # It is deliberately not claimed to be a tracked raw Git blob.
        if name == 'consumer005_receipt':
            exact(ROOT / row['path'], row['sha256'], row['bytes'])
        else:
            published(row['path'], row['sha256'], row['bytes'])
    recovery_path = ROOT / selected['inputs']['recovery_runner']['path']
    recovery = types.ModuleType('p25_immutable_readonly_recovery_helpers_v9')
    recovery.__file__ = str(recovery_path)
    exec(compile(recovery_path.read_bytes(), str(recovery_path), 'exec'), recovery.__dict__)
    cfg = json.loads((ROOT / selected['inputs']['recovery_selection']['path']).read_text())
    consumer = json.loads((ROOT / selected['inputs']['consumer005_receipt']['path']).read_text())
    witnesses_path = published(cfg['witness_manifest']['path'], cfg['witness_manifest']['sha256'])
    inventory_path = published(cfg['object_inventory']['path'], cfg['object_inventory']['sha256'])
    witness_manifest, inventory = json.loads(witnesses_path.read_text()), json.loads(inventory_path.read_text())
    recovery.check_selection_contract(cfg, consumer, witness_manifest)
    require(cfg['schema'] == 'p25-cache-rematerialization-selection-v1' and cfg['target_root'] == str(ROOT)
            and len(cfg['requirements']) == 722 and len(cfg['objects']) == 41 and len(cfg['witnesses']) == 14
            and recovery.p3_inventory_complete(inventory) and cfg['p3_object_inventory_complete'] is True,
            'Completed original 41-object/source/witness inventory differs')
    require(selected['only_normal_modules'] == cfg['allowed_normal_rebuild_modules']
            and set(selected['only_normal_modules']) == set(inventory['missing_modules'])
            and len(selected['only_normal_modules']) == 10
            and {m:r['historical_object_sha256'] for m,r in inventory['objects'].items()} ==
                {m:r['sha256'] for m,r in cfg['objects'].items()}, 'Exact ten-object allowance changed')
    require(cfg['runtime']['strict_flags'] == FLAGS and cfg['normal_stage_wall_seconds'] == 600
            and cfg['initial_free_reserve_bytes'] == MIN_INITIAL_FREE_BYTES
            and cfg['per_stage_free_reserve_bytes'] == GATE_WORKING_HEADROOM_BYTES,
            'Strict flags/time/space controls changed')
    restore_pin = selected['prior_partial_restore']
    require(restore_pin['path'] == str(ROOT / '.lake/diagnostic/p25-cache-rematerialization-attempt001/RECOVERY_RESULT.json')
            and restore_pin['sha256'] == PARTIAL_RESTORE_SHA, 'Actual partial-restore receipt differs')
    restore_path = exact(restore_pin['path'], PARTIAL_RESTORE_SHA)
    restored = json.loads(restore_path.read_text())
    require(restored['schema'] == 'p25-cache-rematerialization-result-v1'
            and restored['status'] == 'PARTIAL_RESTORE_ONLY'
            and restored['runner_sha256'] == IMMUTABLE_RECOVERY_SHA
            and restored['selection_sha256'] == IMMUTABLE_RECOVERY_SELECTION_SHA
            and restored['normal_stages'] == restored['replay_stages'] == restored['owned_audit_stages'] == []
            and restored['runtime_after']['accepted'] is True and restored['runtime_after']['required_path_count'] == 15940
            and restored['ready_for_original_v7_preflight'] is False
            and restored['original_v7_executed'] is False and restored['original_v7_preflight_claimed_passed'] is False,
            'Require the actual partial restore without legacy success or compiler credit')
    blockers = json.loads((ROOT / selected['inputs']['archive_blockers']['path']).read_text())
    exceptions = selected['historical_envelope_exceptions']
    require(len(exceptions) == 5 and exceptions == [dict(row['historical_target'], receipt=row['receipt'],
                attempt=row['attempt']) for row in blockers['attempts']], 'Exact five archive exceptions changed')
    runtime_pins = {p:h for p,h in consumer['frozen_inputs'].items()
                    if p.startswith(('/mathlib/', '/workspace/toolchains/'))}
    require(len(runtime_pins) == 15940, 'Complete runtime pin count differs')
    branches = []
    for row in exceptions:
        descriptor = {k:row[k] for k in ('path', 'bytes', 'sha256')}
        receipt_path = exact(ROOT / row['receipt']['path'], row['receipt']['sha256'], row['receipt']['bytes'])
        receipt = json.loads(receipt_path.read_text())
        require(receipt['complete_external_before'] == descriptor and
                receipt['frozen_inputs'].get(row['path']) == row['sha256'], 'Original envelope descriptor changed')
        old_runtime = {p:h for p,h in receipt['frozen_inputs'].items()
                       if p.startswith(('/mathlib/', '/workspace/toolchains/'))}
        require(all(runtime_pins.get(p) == h for p,h in old_runtime.items()), 'Historical runtime hash differs')
        branches.append(receipt)
    requirements = {r['path']:r['sha256'] for r in cfg['requirements']}
    aliases = {p:{'module':m, 'sha256':row['sha256']} for m,row in cfg['objects'].items() for p in row['aliases']}
    require(len(aliases) == sum(len(row['aliases']) for row in cfg['objects'].values()) == 244
            and set(aliases) == {p for p in requirements if p.endswith('.olean')}
            and all(requirements[p] == row['sha256'] for p,row in aliases.items()), 'Exact historical object aliases changed')
    old_missing = {p:h for p,h in requirements.items() if p in {r['path'] for r in exceptions}
                   or p in aliases and aliases[p]['module'] in selected['only_normal_modules']}
    require(len(old_missing) == 74 and {r['path']:r['sha256'] for r in restored['unresolved_paths']} == old_missing,
            'Actual restore gaps are not precisely the old 69 object aliases and five envelopes')
    history = inspect_history_requirements(requirements, exceptions, aliases)
    frozen.update(history['frozen'])
    frozen.update(inspect_history_requirements(runtime_pins, [], {})['frozen'])
    available = {}
    for module, row in cfg['objects'].items():
        for name in row['aliases']:
            if name in history['frozen']:
                require(not any(os.path.lexists(name + suffix) for suffix in ('.private', '.server')),
                        'Unexpected accepted project companions: ' + module)
                available.setdefault(module, name)
    normal_order = full_missing_order(cfg['objects'], available, selected['only_normal_modules'])
    require(len(available) == 41 and set(available) == set(cfg['objects']) and
            normal_order == [] and history['pending_object_paths'] == {},
            'All 41 exact accepted objects and historical aliases must exist; v9 never rebuilds them')
    require(selected['normal_order'] == full_missing_order(cfg['objects'],
                set(cfg['objects']) - set(selected['only_normal_modules']), selected['only_normal_modules']),
            'Reviewed complete-DAG normal order differs')
    require(not any(os.path.lexists(p) for p in cfg['forbidden_v7_target_objects'])
            and not os.path.lexists(cfg['future_v7_output']), 'Preserve old unaccepted targets and attempt007')
    source_selections = {}
    for name, row in selected['source_selection_inputs'].items():
        require(row['path'] == globals()[name + '_REL'] and row['sha256'] == globals()[name + '_SHA'],
                'Original source selection pin changed: ' + name)
        source_selections[name] = json.loads(published(row['path'], row['sha256'], row['bytes']).read_text())
    sources = select_symbolic_sources(source_selections['SELECTION'], source_selections['FIELD_SELECTION'],
                                     source_selections['PREVIOUS_SOURCE_OVERRIDE'], source_selections['SOURCE_OVERRIDE'])
    require(sources == consumer['source_graph'], 'Original accepted 45-source graph differs')
    sources = select_parse_sources(sources, source_selections['PARSE_OVERRIDE'])
    prior_v8_sources = sources
    floors_override_path = published(FLOORS_OVERRIDE_REL, FLOORS_OVERRIDE_SHA)
    floors_override = json.loads(floors_override_path.read_text())
    sources = select_floors_sources(sources, floors_override)
    published(OLD_FLOORS_SOURCE_REL, OLD_FLOORS_SOURCE_SHA, 3900)
    published(FLOORS_SOURCE_REL, FLOORS_SOURCE_SHA, 5557)
    pending_review_path = published(PENDING_SOURCE_REVIEW_REL, PENDING_SOURCE_REVIEW_SHA, 7804)
    pending_review = json.loads(pending_review_path.read_text())
    sources = select_pending_source_overlays(sources, pending_review, prior_v8_sources)
    for row in pending_review['rows']:
        for key in ['previous_source', 'new_source']:
            descriptor = row[key]
            published(descriptor['path'], descriptor['sha256'], descriptor['bytes'])
    SOURCES = sources
    for module, row in sources.items():
        source = published(row['path'], row['source_sha256'])
        imports = [n for line in re.findall(r'^import\s+([^\n]+)$', source.read_text(), re.M)
                   for n in line.split() if n.startswith('ImbalancedChen.')]
        require(imports == row['project_imports'], 'Published source import graph differs: ' + module)
    upstream_path = exact(REMAINING / 'COMPLETE_EXTERNAL_BEFORE.json', EXTERNAL_SNAPSHOT_SHA,
                          selected['upstream_snapshot']['bytes'])
    upstream_receipt_path = exact(REMAINING / 'RESULT.json', REMAINING_RESULT_SHA,
                                  selected['upstream_accepted_receipt']['bytes'])
    upstream = json.loads(upstream_path.read_text())
    upstream_receipt = json.loads(upstream_receipt_path.read_text())
    require(upstream['schema'] == 'p25-complete-current-external-snapshot-v1'
            and upstream['historical_missing_hashes_invented'] is False
            and upstream_receipt['accepted'] is True and upstream_receipt['complete_external_after_matches_before'] is True,
            'Preserved accepted upstream context differs')
    providers = [LEAN.parent.parent / 'lib/lean', *map(Path, consumer['approved_LEAN_PATH'].split(':')[1:])]
    require(len(providers) == 9 and list(map(str, providers)) == selected['external_provider_roots']
            == upstream['provider_roots'] and len(upstream['entries']) == upstream['module_count'] == 5312
            and sum(len(r['companions']) for r in upstream['entries']) == 10624,
            'Upstream current inventory/provider scope differs')
    for row in upstream['entries']:
        for record in [row['object'], *row['companions']]:
            require(runtime_pins.get(record['path']) == record['sha256']
                    and upstream_receipt['frozen_inputs'].get(record['path']) == record['sha256']
                    and all(branch['frozen_inputs'].get(record['path']) == record['sha256'] for branch in branches),
                    'Historical branch did not freeze the exact external record: ' + record['path'])
    witness_before = recovery.witness_snapshot(cfg['witnesses'])
    require(not any(str(p) in frozen for p in [row['path'] for row in history['archive_gaps']]),
            'Missing archival envelope was falsely bound')
    prepared = {'publication': publication, 'selection': selected, 'successor_selection': successor,
                'cfg': cfg, 'recovery': recovery,
                'consumer': consumer, 'frozen': frozen, 'archive_gaps': history['archive_gaps'],
                'exceptions': exceptions, 'requirements': requirements, 'aliases': aliases,
                'pending_object_paths': history['pending_object_paths'], 'available': available,
                'normal_order': normal_order, 'providers': providers,
                'external_entries': upstream['entries'], 'upstream_record': record_file(upstream_path),
                'upstream_receipt': record_file(upstream_receipt_path), 'witness_before': witness_before,
                'partial_restore': record_file(restore_path), 'source_graph': sources,
                'prior_v8_source_graph': prior_v8_sources, 'runtime_pins': runtime_pins,
                'runner_sha256': runner_sha, 'selection_sha256': selection_sha}
    verify_prior_v8(prepared, exact, published)
    validate_dependency_identities({**{m:r['sha256'] for m,r in cfg['objects'].items()},
                                   PARSE_TARGET: prepared['prior_v8']['modules'][PARSE_TARGET]['object']['sha256']},
                                  cfg['objects'], PARSE_OBJECT_SHA)
    observation = current_context(prepared, 'read-only-preflight')
    recovery.no_symlink_ancestors(OUT)
    disk = check_disk_space(MIN_INITIAL_FREE_BYTES, 'before fresh attempt009')
    prepared['plan'] = {'schema': 'p25-cell00-three-consumers-successor-plan-v9', 'publication_commit': publication,
        'runner_sha256': runner_sha, 'selection_sha256': selection_sha, 'observed_utc': now(),
        'prior_partial_restore': prepared['partial_restore'], 'historical_archive_gaps': history['archive_gaps'],
        'available_objects': 42, 'original_available_objects': len(available), 'normal_rematerialization_order': [],
        'prior_v8_receipt': prepared['prior_v8_receipt'], 'prior_v8_aggregate_accepted': False,
        'historical_v8_normal_rematerialization_receipt': prepared['prior_v8_rematerialization_receipt'],
        'historical_v8_normal_modules': prepared['prior_v8']['dependency_modules_compiled'],
        'accepted_parse_object': prepared['prior_v8']['modules'][PARSE_TARGET]['object'],
        'accepted_parse_owned_count': 7, 'parse_gates_to_rerun': [],
        'pending_exact_object_alias_count': len(history['pending_object_paths']),
        'project_objects': 42, 'consumer_modules': CONTINUATION_MODULES,
        'external_modules': 5312, 'external_companions': 10624, 'runtime_pins': 15940,
        'current_inventory_sha256': hashlib.sha256(json.dumps(observation['entries'], sort_keys=True).encode()).hexdigest(),
        'frozen_existing_file_count': len(frozen), 'disk_check': disk, 'writes_performed': False,
        'normal_stages': [], 'old_v7_preflight_passed': False, 'P2_5_proved': False}
    return prepared


def create_successor_context(prepared):
    """Create only a new observation; no recovery, alias installation or Lean."""
    require_v9_pins()
    require(not os.path.lexists(OUT), 'Preserve existing attempt009')
    prepared['recovery'].no_symlink_ancestors(OUT)
    current_context(prepared, 'immediate-before-create')
    check_disk_space(MIN_INITIAL_FREE_BYTES, 'before writing attempt009 context')
    OUT.mkdir()
    prepared['created_output'] = True
    before = current_context(prepared, 'before-three-consumer-reuse')
    path = OUT / 'FRESH_CONTEXT_BEFORE.json'
    with path.open('x') as stream:
        stream.write(json.dumps(before, indent=2) + '\n')
    prepared['frozen'][str(path)] = digest(path)
    prepared['fresh_context_before'] = record_file(path)
    prepared['normal_stages'] = []
    prepared['normal_modules'] = []
    return prepared


def run_consumers(publication, prepared):
    global SOURCES
    require(isinstance(FIELD_RESULT_SHA, str) and re.fullmatch(r'[0-9a-f]{64}', FIELD_RESULT_SHA) and
            isinstance(FIELD_PUBLICATION, str) and re.fullmatch(r'[0-9a-f]{40}', FIELD_PUBLICATION) and
            FIELD_ARTIFACTS_REVIEWED is True,
            'SOURCE_ONLY: actual successful Field attempt006 receipt, exact publication, and complete local artifact review are required before any mutation or execution.')
    require(DECODED_ARTIFACTS_REVIEWED is True and
            isinstance(FAILED_PARSE_RESULT_SHA, str) and re.fullmatch(r'[0-9a-f]{64}', FAILED_PARSE_RESULT_SHA) and
            isinstance(FAILED_PARSE_PUBLICATION, str) and re.fullmatch(r'[0-9a-f]{40}', FAILED_PARSE_PUBLICATION),
            'SOURCE_ONLY: complete actual attempt005 receipt, Decoded logs/inventory/object, and local artifact review are required before any mutation or execution.')
    require(re.fullmatch(r'[0-9a-f]{40}', publication) and prepared['publication'] == publication,
            'Use the prepared exact publication commit.')
    preserved_v6 = subprocess.check_output(['git', 'show', RESOURCE_BASE_PUBLICATION + ':' + RESOURCE_BASE_REL], cwd=ROOT, timeout=120)
    require(hashlib.sha256(preserved_v6).hexdigest() == RESOURCE_BASE_SHA,
            'Preserved v6 proof-validation driver differs')
    require_v9_pins()
    require(ROOT.is_dir() and OUT.is_dir() and not (OUT / 'RESULT.json').exists()
            and prepared['prior_v8_receipt']['path'] == str(PRIOR_V8_OUT / 'RESULT.json')
            and digest(prepared['prior_v8_receipt']['path']) == PRIOR_V8_RESULT_SHA
            and prepared['normal_modules'] == prepared['normal_stages'] == prepared['normal_order'] == [],
            'Require exact historical v8 evidence and a new context without any dependency gate.')
    prior_v8, prior_v8_path = prepared['prior_v8'], Path(prepared['prior_v8_receipt']['path'])
    failed_consumer_path = FAILED_CONSUMER / 'RESULT.json'
    require(digest(failed_consumer_path) == FAILED_CONSUMER_RESULT_SHA and
            failed_consumer_path.stat().st_size == 5016911, 'Actual failed consumer receipt bytes differ.')
    failed_consumer = json.loads(failed_consumer_path.read_text())
    validate_failed_consumer(failed_consumer)
    require(all(not (FAILED_CONSUMER / 'lib' / (module.replace('.', '/') + '.olean')).exists()
                for module in FRESH_MODULES), 'An old same-name consumer target object unexpectedly exists.')
    failed_parse_path = FAILED_PARSE / 'RESULT.json'
    require(digest(failed_parse_path) == FAILED_PARSE_RESULT_SHA and
            failed_parse_path.stat().st_size == 5049315, 'Actual failed OriginalParse receipt bytes differ.')
    failed_parse = json.loads(failed_parse_path.read_text())
    validate_failed_parse(failed_parse, failed_consumer)
    require(all(not (FAILED_PARSE / 'lib' / (module.replace('.', '/') + '.olean')).exists()
                for module in V8_CONTINUATION_MODULES), 'An old unaccepted continuation target object unexpectedly exists.')
    exact_copy_bytes = sum(Path(row['path']).stat().st_size +
                           sum(Path(companion['path']).stat().st_size for companion in row['companions'])
                           for row in failed_consumer['dependency_objects'].values())
    exact_copy_bytes += Path(failed_parse['modules'][DECODED]['object']['path']).stat().st_size
    exact_copy_bytes += Path(prior_v8['modules'][PARSE_TARGET]['object']['path']).stat().st_size
    initial_disk_check = check_disk_space(max(MIN_INITIAL_FREE_BYTES,
                                              METADATA_HEADROOM_BYTES + GATE_WORKING_HEADROOM_BYTES),
                                         'before fresh output and exact accepted dependency hardlinks')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 checkout is dirty.')
    state = {
        'schema': 'p25-cell00-three-consumers-successor-strict-v9', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
        'dependency_storage': 'same-filesystem-hardlinks-with-before-and-after-hashes',
        'preserved_v6_driver': {'commit': RESOURCE_BASE_PUBLICATION, 'path': RESOURCE_BASE_REL, 'sha256': RESOURCE_BASE_SHA},
        'dependency_payload_bytes_reused_without_copy': exact_copy_bytes,
        'initial_free_reserve_bytes': MIN_INITIAL_FREE_BYTES,
        'per_stage_free_reserve_bytes': GATE_WORKING_HEADROOM_BYTES,
        'module_order': [s['module'] for s in MODULES], 'modules': {}, 'dependency_objects': {},
        'dependency_receipts': {}, 'dependency_modules_compiled': prepared['normal_modules'], 'private_records_written': [],
        'normal_rematerialization_stages': [],
        'historical_v8_normal_rematerialization_stages': prepared['prior_v8_rematerialization']['normal_stages'],
        'historical_v8_normal_rematerialization_receipt': prepared['prior_v8_rematerialization_receipt'],
        'historical_v8_normal_modules': prior_v8['dependency_modules_compiled'],
        'prior_v8_receipt': prepared['prior_v8_receipt'],
        'prior_v8_aggregate_accepted': False,
        'prior_v8_aggregate_status': prior_v8['status'],
        'prior_v8_failed_owner': prior_v8['modules'][CONTINUATION_MODULES[0]],
        'prior_v8_pending_owners': {m: prior_v8['modules'][m] for m in CONTINUATION_MODULES[1:]},
        'prior_v8_aggregate_relabelled': False,
        'reused_parse_owner_receipt': prior_v8['modules'][PARSE_TARGET],
        'reused_parse_owner_receipt_source': prepared['prior_v8_receipt'],
        'accepted_parse_exported_evidence_reviewed_before_publication': V8_ARTIFACTS_REVIEWED,
        'accepted_parse_object_bytes_revalidated_in_this_preflight': True,
        'parse_gates_rerun': [],
        'consumer_phase_dependency_modules_compiled': [],
        'prior_partial_restore': prepared['partial_restore'],
        'historical_archive_gaps': prepared['archive_gaps'],
        'fresh_context_before': prepared['fresh_context_before'],
        'old_v7_preflight_passed': False, 'old_recovery_complete': False,
        'old_snapshots_synthesized': False,
        'original_cell00_sha256': INPUT_SHA, 'host_correctness_credit': False,
        'failed_monolithic_Decoded_object_used': False, 'original_cell00_decode_proved': False,
        'original_cell00_stored_floors_proved': False, 'geometric_jensen_binding_proved': False,
        'original_cell00_simplex_guards_proved': False, 'original_cellFloorNumerator_proved': False,
        'original_cell00_geometric_jensen_binding_proved': False,
        'original_cell00_headers_proved': False, 'original_cell00_facet_indices_proved': False,
        'source_cell_membership_proved': False, 'all96_vertex_inequalities_proved': False,
        'positive_normal_balance_proved': False, 'facet_incidence_proved': False, 'pulling_ownership_proved': False,
        'all_cell_finite_guards_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
        'accepted_dependency_gates_rerun': [],
        'accepted_dependency_gates_rerun_scope': 'no new normal, independent-kernel, or full-owned dependency gates; ten historical v8 normals recorded separately',
        'existing_owners_normally_recompiled': prepared['normal_modules'],
        'complete_external_after_matches_before': False, 'historical_missing_external_hashes_invented': False,
        'reused_original_owner_receipts': {}, 'reused_complete_context_validations': {},
        'failed_split_aggregate_relabelled': False, 'historical_owner_publications_preserved': False,
        'accepted_field_private_composition_helper_checked': False,
        'accepted_field_actual_artifacts_reviewed_before_publication': FIELD_ARTIFACTS_REVIEWED,
        'retry_kind': 'explicit-motive-floors-transport-after-actual-v8-timeout',
        'previous_consumer_failure': {**record_file(failed_consumer_path),
            'publication_commit': FAILED_CONSUMER_PUBLICATION, 'accepted': False,
            'status': 'FAILED', 'normal_replay_audit_gates_started': 0},
        'previous_consumer_failed_owners': failed_consumer['modules'],
        'previous_parse_failure': {**record_file(failed_parse_path),
            'publication_commit': FAILED_PARSE_PUBLICATION, 'aggregate_accepted': False,
            'aggregate_status': 'MODULE_STAGE_FAILED', 'failed_module': PARSE_TARGET,
            'failed_stage': 'normal', 'failed_owner_reused': False},
        'previous_parse_failed_owner': failed_parse['modules'][PARSE_TARGET],
        'previous_parse_pending_owners': {module: failed_parse['modules'][module] for module in CONTINUATION_MODULES},
        'reused_decoded_owner_receipt': failed_parse['modules'][DECODED],
        'reused_decoded_owner_receipt_source': record_file(failed_parse_path),
        'accepted_decoded_actual_artifacts_reviewed_before_publication': DECODED_ARTIFACTS_REVIEWED,
        'decoded_gates_rerun': [], 'failed_parse_aggregate_relabelled': False,
        'private_parse_helpers_audited': False,
        'failed_consumer_object_used': False, 'storage_cleanup_performed': False,
        'exact_accepted_dependency_copy_bytes': exact_copy_bytes,
        'disk_checks': [initial_disk_check],
    }
    frozen = dict(prepared['frozen'])
    envelope_allowance = {row['path']: row for row in prepared['exceptions']}
    unavailable_envelopes = {row['path'] for row in prepared['archive_gaps']}
    external_entries, providers = [], []
    expected_external = set()
    target_names = set(CONTINUATION_MODULES)

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

    def historical_pin(path, expected):
        """Only a reviewed absent envelope can be ledgered without calling bind."""
        name = str(path)
        if name in envelope_allowance:
            descriptor = envelope_allowance[name]
            require(expected == descriptor['sha256'] and descriptor['bytes'] == 4302154,
                    'Historical envelope tuple differs')
            if not os.path.lexists(name):
                require(name in unavailable_envelopes and name not in frozen,
                        'Unreviewed or falsely frozen archival gap')
                return
        bind(path, expected)

    def check_frozen():
        require(all(digest(path) == h for path, h in frozen.items()), 'Frozen source/object/receipt/log/runtime changed.')

    def external_resolutions():
        require(len(external_entries) == len(expected_external) == EXPECTED_EXTERNAL_COUNT,
                'Complete current external context has not been initialized.')
        for row in external_entries:
            relative = row['module'].replace('.', '/') + '.olean'
            found = [provider / relative for provider in providers if (provider / relative).is_file()]
            require([str(path) for path in found] == [row['object']['path']],
                    'External import provider changed: ' + row['module'])
            companions = [str(found[0]) + suffix for suffix in ['.private', '.server']
                          if Path(str(found[0]) + suffix).is_file()]
            require(companions == [entry['path'] for entry in row['companions']],
                    'External companion inventory changed: ' + row['module'])

    def context_check():
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Selected publication changed during gates.')
        require(git('rev-parse', 'HEAD', cwd=Path(state['runtime']['mathlib_path'])) == MATHLIB_PIN,
                'Mathlib source pin changed during gates.')
        external_resolutions()
        check_frozen()
        require(all(not os.path.lexists(name) for name in unavailable_envelopes),
                'Historical envelope availability changed during fresh gates')

    def require_external(log, expected_count=EXPECTED_EXTERNAL_COUNT):
        external = {m for m in audited_imports(log) if not m.startswith('ImbalancedChen.')}
        require(external <= expected_external and len(external) == expected_count,
                'Audited external imports are not the selected accepted subset of the complete current snapshot: ' + str(log))
        return external

    def stage_log(row, override=None):
        require(row['exit_code'] == 0 and not row.get('timed_out', False), 'Dependency stage did not pass.')
        path = Path(override) if override is not None else Path(row['log'])
        if not path.is_absolute():
            path = ROOT / path
        bound = bind(path, row['log_sha256'])
        require('log_bytes' not in row or bound.stat().st_size == row['log_bytes'], 'Stage log byte count mismatch.')
        return bound

    def strict_commands(stages, module, source, object_path, audit_source):
        require(stages['replay']['command'] == [str(CHECKER), '--verbose', module], f'Unexpected replay command: {module}')
        for label in ['normal', 'audit']:
            command = stages[label]['command']
            require(command[0] == str(LEAN) and
                    all(flag in command for flag in FLAGS),
                    f'Non-strict accepted stage: {module}/{label}')
        normal = stages['normal']['command']
        require(Path(normal[-1]) == source and Path(normal[normal.index('-o') + 1]) == object_path,
                f'Normal command/source/object binding mismatch: {module}')
        require(Path(stages['audit']['command'][-1]) == audit_source, f'Audit source binding mismatch: {module}')

    def copy_dependency(module, original, expected, provenance, companions=None):
        require(module in SOURCES and module not in target_names, f'Refuse a target/unknown dependency object: {module}')
        if module in KNOWN_OBJECTS:
            require(expected == KNOWN_OBJECTS[module], f'Known accepted object identity mismatch: {module}')
        original = bind(original, expected)
        companions = [] if companions is None else companions
        actual_companions = [str(original) + suffix for suffix in ['.private', '.server']
                             if Path(str(original) + suffix).is_file()]
        require(actual_companions == [row['path'] for row in companions],
                f'Project object companion set differs from accepted inventory: {module}')
        for row in companions:
            artifact(row)
        destination = lib / (module.replace('.', '/') + '.olean')
        if module in state['dependency_objects']:
            previous = state['dependency_objects'][module]
            require(previous['sha256'] == expected and digest(destination) == expected,
                    f'Conflicting accepted object provenance: {module}')
            previous_companions = [(Path(row['path']).suffix, row['sha256']) for row in previous['companions']]
            require(previous_companions == [(Path(row['path']).suffix, row['sha256']) for row in companions],
                    f'Conflicting accepted companion provenance: {module}')
            return
        require(not destination.exists(), f'Unexpected preexisting dependency object: {module}')
        link_dependency_bytes(original, destination)
        bind(destination, expected)
        copied_companions = []
        for row in companions:
            target = Path(str(destination) + Path(row['path']).suffix)
            require(not target.exists(), f'Unexpected existing companion: {target}')
            link_dependency_bytes(Path(row['path']), target)
            bind(target, row['sha256'])
            copied_companions.append(record_file(target))
        state['dependency_objects'][module] = {
            'path': str(original), 'sha256': expected, 'isolated_path': str(destination),
            'source_sha256': SOURCES[module]['source_sha256'], 'provenance': provenance,
            'companions': copied_companions,
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
        required_audit = audit_template.replace(PAYLOAD, module) + (appendix_text if module == SUPPORT else '')
        require(audit_source.read_text() == required_audit, f'Changed complete-audit template: {module}')
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
        require_external(owner['stages']['audit']['log'])
        if module == SUPPORT:
            scope = read_private_scope_audit(owner['stages']['audit']['log'], records, expected_private)
            require(json.loads(artifact(owner['private_scoped_simp_interface']).read_text()) == scope,
                    'FieldSimp stored scoped interface differs from actual full-owned audit marker.')
        copy_dependency(module, object_path, owner['object']['sha256'],
                        'Accepted normal/replay/full-owned owner and complete inventory revalidated',
                        owner.get('object_companions', []))
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
        require_external(directory / 'AUDIT.log', 2872 if module == JSON_OWNER else EXPECTED_EXTERNAL_COUNT)
        require(records == receipt['owned_declarations'] and len(records) == receipt['owned_count'],
                f'Legacy owned inventory differs from receipt: {module}')
        require(set(SOURCES[module]['public_names']) <= {r['name'] for r in records}, f'Legacy public declarations missing: {module}')
        copy_dependency(module, object_path, KNOWN_OBJECTS[module], 'Exact accepted legacy owner receipt, logs and full inventory revalidated')
        state['dependency_receipts'][module] = record_file(receipt_path)
        return receipt

    def verify_reuse_validation(reuse, original_owner, original_receipt_path, container):
        module = original_owner['module']
        require(reuse['module'] == module and reuse['accepted'] is True and
                reuse['status'] == 'REPLAY_COMPLETE_OWNED_REUSE_VALIDATED' and
                reuse['normal_recompiled'] is False and set(reuse['stages']) == {'replay', 'audit'} and
                reuse['source_origin'] == original_owner['source_origin'] and
                reuse['source_copy'] == original_owner['source_copy'] and
                reuse['object']['sha256'] == original_owner['object']['sha256'] and
                artifact(reuse['original_owner_receipt']) == original_receipt_path,
                'Supplemental complete-context validation changed its original owner provenance: ' + module)
        artifact(reuse['source_copy'], SOURCES[module]['source_sha256'])
        artifact(reuse['object'], original_owner['object']['sha256'])
        audit_source = artifact(reuse['audit_source'])
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, module),
                'Supplemental full-owned audit template differs: ' + module)
        for label in ['replay', 'audit']:
            row = reuse['stages'][label]
            require(row['status'] == 'PASSED', 'Supplemental stage not accepted: ' + module + '/' + label)
            stage_log(row)
        require(reuse['stages']['replay']['command'] == [str(CHECKER), '--verbose', module],
                'Supplemental replay command differs: ' + module)
        command = reuse['stages']['audit']['command']
        require(command[0] == str(LEAN) and all(flag in command for flag in FLAGS) and
                Path(command[-1]) == audit_source, 'Supplemental full-owned command differs: ' + module)
        records, inventory, imports = read_audit(Path(reuse['stages']['audit']['log']), module)
        require_external(reuse['stages']['audit']['log'])
        require(records == reuse['owned_declarations'] == original_owner['owned_declarations'] and
                len(records) == reuse['owned_count'] == original_owner['owned_count'] and
                inventory == reuse['inventory'] == json.loads(artifact(original_owner['inventory']).read_text()) and
                imports == reuse['actual_project_closure'] == original_owner['actual_project_closure'] and
                reuse['complete_external_before'] == container['complete_external_before'],
                'Supplemental complete-context audit differs from the original full owner: ' + module)
        artifact(reuse['complete_external_before'])
        state['reused_complete_context_validations'][module] = reuse

    def verify_container_objects(container):
        # Every project module actually imported by a reused owner must resolve
        # to the very same accepted object bytes in the one new isolated root.
        objects = dict(container['dependency_objects'])
        objects.update({module: owner['object'] for module, owner in container['modules'].items()
                        if owner.get('accepted') is True})
        for module, row in objects.items():
            require(module in state['dependency_objects'] and
                    row['sha256'] == state['dependency_objects'][module]['sha256'],
                    'Accepted container project object differs in this isolated root: ' + module)

    def run_stage(owner, label, command, log):
        require_new_gate(owner['module'], label)
        require(owner['module'] in target_names, 'Selected three-consumer target differs')
        context_check()
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
        bind(log, row['log_sha256'])
        state['frozen_inputs'] = dict(frozen)
        write()
        print('P25_CONSUMER_STAGE_RESULT', owner['module'], label,
              json.dumps({k: row[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}), flush=True)
        context_check()
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=owner['module'], failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{owner["module"]} {label} failed with exit {code}.')

    write()
    try:
        # Retain the complete failed-before-gate evidence; no failed target is reused.
        bind(failed_consumer_path, FAILED_CONSUMER_RESULT_SHA)
        require(json.loads(failed_consumer_path.read_text()) == failed_consumer,
                'Failed consumer receipt changed during disk preflight.')
        artifact(failed_consumer['runner'], FAILED_CONSUMER_RUNNER_SHA)
        artifact(failed_consumer['exception_log'], FAILED_CONSUMER_EXCEPTION_SHA)
        for path, expected in failed_consumer['frozen_inputs'].items():
            historical_pin(path, expected)
        bind(failed_parse_path, FAILED_PARSE_RESULT_SHA)
        require(json.loads(failed_parse_path.read_text()) == failed_parse,
                'Actual partially accepted consumer receipt changed during disk preflight.')
        artifact(failed_parse['runner'], FAILED_PARSE_RUNNER_SHA)
        artifact(failed_parse['exception_log'], FAILED_PARSE_EXCEPTION_SHA)
        failed_parse_owner = failed_parse['modules'][PARSE_TARGET]
        failed_parse_source = artifact(failed_parse_owner['source_copy'], OLD_PARSE_SOURCE_SHA)
        failed_parse_normal = failed_parse_owner['stages']['normal']
        require(failed_parse_normal['command'] == [str(LEAN), *FLAGS, '--root=' + str(FAILED_PARSE / 'src'),
                    '-o', str(FAILED_PARSE / 'lib' / (PARSE_TARGET.replace('.', '/') + '.olean')),
                    str(failed_parse_source)], 'Actual failed OriginalParse normal command differs.')
        failed_parse_log = bind(failed_parse_normal['log'], FAILED_PARSE_NORMAL_SHA)
        require(failed_parse_log.stat().st_size == 1046, 'Actual complete failed OriginalParse log size differs.')
        for path, expected in failed_parse['frozen_inputs'].items():
            historical_pin(path, expected)
        # Read the actual successful receipts. No dependency gate is rerun.
        field_path = bind(FIELD / 'RESULT.json', FIELD_RESULT_SHA)
        field = json.loads(field_path.read_text())
        split_path = bind(SPLIT / 'RESULT.json', SPLIT_RESULT_SHA)
        split = json.loads(split_path.read_text())
        prior_field_path = bind(PRIOR_FIELD / 'RESULT.json', PRIOR_FIELD_RESULT_SHA)
        prior_field = json.loads(prior_field_path.read_text())
        previous_path = bind(PREVIOUS_FINAL / 'RESULT.json', PREVIOUS_FINAL_RESULT_SHA)
        previous = json.loads(previous_path.read_text())
        earlier_path = bind(EARLIER_FINAL / 'RESULT.json', EARLIER_FINAL_RESULT_SHA)
        earlier = json.loads(earlier_path.read_text())
        validate_field_history(field, split, prior_field)
        validate_previous_final(field, previous, split, prior_field)
        validate_earlier_final(field, previous, earlier)
        validate_private_composition(field)
        require(artifact(field['previous_final_attempt'], PREVIOUS_FINAL_RESULT_SHA) == previous_path,
                'Accepted final receipt selected a different attempt005 receipt.')
        previous_owner = previous['modules'][FIELD_TARGET]
        previous_source = artifact(previous_owner['source_copy'], PREVIOUS_FINAL_SOURCE_SHA)
        previous_normal = previous_owner['stages']['normal']
        require(previous_normal['status'] == 'FAILED' and previous_normal['exit_code'] == 1 and
                previous_normal['timed_out'] is False and previous_normal['log_sha256'] == PREVIOUS_FINAL_NORMAL_SHA and
                previous_normal['log_bytes'] == 192 and previous_normal['command'] ==
                    [str(LEAN), *FLAGS, '--root=' + str(PREVIOUS_FINAL / 'src'), '-o',
                     str(PREVIOUS_FINAL / 'lib' / (FIELD_TARGET.replace('.', '/') + '.olean')), str(previous_source)],
                'Attempt005 normal command or complete failure log identity differs.')
        previous_log = bind(previous_normal['log'], PREVIOUS_FINAL_NORMAL_SHA)
        require(previous_log.stat().st_size == 192, 'Attempt005 complete failure log size differs.')
        state['previous_final_attempt'] = field['previous_final_attempt']
        state['previous_final_failed_owner'] = previous_owner
        require(artifact(field['earlier_failed_final_attempt'], EARLIER_FINAL_RESULT_SHA) == earlier_path,
                'Accepted final receipt selected a different attempt004 receipt.')
        earlier_owner = earlier['modules'][FIELD_TARGET]
        earlier_source = artifact(earlier_owner['source_copy'], BASE_FINAL_SOURCE_SHA)
        earlier_normal = earlier_owner['stages']['normal']
        require(earlier_normal['status'] == 'FAILED' and earlier_normal['exit_code'] == 1 and
                earlier_normal['timed_out'] is False and earlier_normal['log_sha256'] == EARLIER_FINAL_NORMAL_SHA and
                earlier_normal['log_bytes'] == 487 and earlier_normal['command'] ==
                    [str(LEAN), *FLAGS, '--root=' + str(EARLIER_FINAL / 'src'), '-o',
                     str(EARLIER_FINAL / 'lib' / (FIELD_TARGET.replace('.', '/') + '.olean')), str(earlier_source)],
                'Attempt004 normal command or complete failure log identity differs.')
        earlier_log = bind(earlier_normal['log'], EARLIER_FINAL_NORMAL_SHA)
        require(earlier_log.stat().st_size == 487, 'Attempt004 complete failure log size differs.')
        state['earlier_failed_final_attempt'] = field['earlier_failed_final_attempt']
        state['earlier_failed_final_owner'] = earlier_owner
        artifact(field['failed_split_receipt'], SPLIT_RESULT_SHA)
        failed_owner = split['modules'][FIELD_TARGET]
        require(failed_owner['module'] == FIELD_TARGET and failed_owner['status'] == 'NORMAL_FAILED' and
                failed_owner['source_origin'] == {'commit': SPLIT_PUBLICATION, 'path': SPLIT_FAILED_SOURCE_REL,
                                                   'sha256': SPLIT_FAILED_SOURCE_SHA} and
                set(failed_owner['stages']) == {'normal'}, 'The historical failed final owner changed.')
        failed_source = artifact(failed_owner['source_copy'], SPLIT_FAILED_SOURCE_SHA)
        failed_normal = failed_owner['stages']['normal']
        require(failed_normal['status'] == 'FAILED' and failed_normal['exit_code'] != 0 and
                failed_normal['timed_out'] is False and failed_normal['log_sha256'] == SPLIT_FAILED_NORMAL_SHA and
                failed_normal['command'] == [str(LEAN), *FLAGS, '--root=' + str(SPLIT / 'src'), '-o',
                    str(SPLIT / 'lib' / (FIELD_TARGET.replace('.', '/') + '.olean')), str(failed_source)],
                'The historical final failure is not the selected ordinary normal-check failure.')
        failed_log = bind(failed_normal['log'], SPLIT_FAILED_NORMAL_SHA)
        require(failed_log.stat().st_size == failed_normal['log_bytes'], 'Historical failure log size changed.')
        state['failed_split_receipt'] = field['failed_split_receipt']
        state['prior_failed_final_owner'] = failed_owner
        remaining_path = bind(REMAINING / 'RESULT.json', REMAINING_RESULT_SHA)
        remaining = json.loads(remaining_path.read_text())
        require(remaining['accepted'] is True and remaining['schema'] == 'p25-cell00-remaining-arithmetic-strict-v1' and
                remaining['status'] == 'CELL00_ALL_EIGHT_TYPED_ARITHMETIC_ACCEPTED' and
                remaining['publication_commit'] == REMAINING_PUBLICATION and
                remaining['module_order'] == ARITHMETIC_MODULES and set(remaining['modules']) == set(ARITHMETIC_MODULES) and
                all(owner['accepted'] is True for owner in remaining['modules'].values()) and
                remaining['dependency_modules_compiled'] == [] and remaining['row00_normal_recompiled'] is False and
                remaining['complete_external_after_matches_before'] is True,
                'Require the actual accepted AllRows arithmetic receipt.')
        row00_path = bind(ROW00_RESULT, ROW00_RESULT_SHA)
        row00 = json.loads(row00_path.read_text())
        require(row00['accepted'] is True and set(row00['modules']) == {ROW00} and
                row00['modules'][ROW00]['accepted'] is True and
                remaining['prior_row00_receipt'] == record_file(row00_path) and
                remaining['reused_owner_receipts'] == {ROW00: row00['modules'][ROW00]},
                'Row00 exact original owner receipt must be preserved.')
        facts_path = bind(FACTS / 'RESULT.json', FACTS_RESULT_SHA)
        facts = json.loads(facts_path.read_text())
        require(facts['accepted'] is True and facts['schema'] == 'p25-cell00-typed-source-facts-strict-v1' and
                facts['status'] == 'CELL00_TYPED_HEADERS_FACET_INDICES_ACCEPTED' and
                facts['publication_commit'] == FACTS_PUBLICATION and
                facts['module_order'] == [FACTS_MODULE] and set(facts['modules']) == {FACTS_MODULE} and
                facts['modules'][FACTS_MODULE]['accepted'] is True and
                facts['modules'][FACTS_MODULE]['owned_count'] == 6 and
                facts['modules'][FACTS_MODULE]['object']['sha256'] == FACTS_OBJECT_SHA and
                facts['dependency_modules_compiled'] == facts['accepted_dependency_gates_rerun'] == [] and
                facts['typed_headers_proved'] is True and facts['typed_facet_indices_proved'] is True and
                facts['complete_external_after_matches_before'] is True,
                'Require the actual accepted TypedSourceFacts owner and complete context.')
        payload_path = bind(PAYLOAD_FLOORS / 'RESULT.json', PAYLOAD_RESULT_SHA)
        payload_receipt = json.loads(payload_path.read_text())
        require(payload_receipt['accepted'] is True and
                all(payload_receipt['modules'][m]['accepted'] is True for m in [PAYLOAD, FLOORS]),
                'Accepted payload/floors owners are required.')
        initial_head = git('rev-parse', 'HEAD')
        if initial_head != publication:
            with (OUT / 'PUBLICATION.log').open('wb') as stream:
                subprocess.run(['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false',
                                'fetch', '--no-tags', 'origin', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
                ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', initial_head, publication],
                                          cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, timeout=120)
                require(ancestor.returncode == 0, 'Clean P3 HEAD is not an ancestor of the selected publication.')
                subprocess.run(['git', 'checkout', '--detach', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Target publication mismatch/dirty.')
        state['initial_checkout'] = {'commit': initial_head, 'ancestor_of_selected_publication': True}
        state['publication_checked_out'] = publication
        runner_path = Path(__file__).resolve()
        published_runner = subprocess.check_output(['git', 'show', publication + ':' + RUNNER_REL], cwd=ROOT, timeout=120)
        require(published_runner == runner_path.read_bytes(), 'Executing runner bytes differ from the selected publication blob.')
        bind(runner_path, hashlib.sha256(published_runner).hexdigest())
        state['runner_publication_binding'] = {'commit': publication, 'path': RUNNER_REL,
            'sha256': digest(runner_path), 'executed_path': str(runner_path)}
        selection_path = bind(ROOT / SELECTION_REL, SELECTION_SHA)
        require(subprocess.check_output(['git', 'show', publication + ':' + SELECTION_REL], cwd=ROOT, timeout=120) == selection_path.read_bytes(),
                'Source/receipt selection differs from publication bytes.')
        selection = json.loads(selection_path.read_text())
        require(selection['schema'] == 'p25-cell00-five-consumers-source-and-receipt-selection-v1' and
                selection['dependency_receipt_selection_complete'] is False and
                selection['fresh_owner_order'] == FRESH_MODULES and selection['fresh_owner_count'] == 5 and
                selection['new_public_source_declaration_count'] == 20 and selection['project_module_count'] == 45 and
                selection['dependency_object_count'] == 40 and
                selection['normal_recompilation_of_existing_owners_permitted'] is False and
                selection['failed_same_name_objects_permitted'] is False and
                selection['original_ecfc_owner_receipts_preserved'] is True,
                'Frozen selection is incomplete or changes the five-owner reuse scope.')
        for key, path, sha, commit in [('remaining_arithmetic', remaining_path, REMAINING_RESULT_SHA, REMAINING_PUBLICATION),
                                      ('typed_source_facts', facts_path, FACTS_RESULT_SHA, FACTS_PUBLICATION)]:
            spec = selection['dependencies'][key]
            require(ROOT / spec['path'] == path and spec['sha256'] == sha and spec['publication_commit'] == commit,
                    'Selected dependency receipt identity differs: ' + key)
        require(selection['dependencies']['field']['path'] == str(SPLIT.relative_to(ROOT) / 'RESULT.json') and
                selection['dependencies']['field']['sha256'] is None and
                selection['dependencies']['field']['publication_commit'] == SPLIT_PUBLICATION and
                selection['dependencies']['field']['runner_sha256'] == SPLIT_RUNNER_SHA and
                selection['dependencies']['field']['expected_old_owner_modules'] == list(REUSED_FIELD_OBJECTS) and
                selection['dependencies']['field']['expected_fresh_owner_modules'] == FIELD_FRESH_MODULES and
                selection['dependencies']['remaining_arithmetic']['expected_fresh_owner_modules'] == ARITHMETIC_MODULES and
                selection['dependencies']['typed_source_facts']['object_sha256'] == FACTS_OBJECT_SHA,
                'Selected dependency owner partition changed.')
        field_selection_path = bind(ROOT / FIELD_SELECTION_REL, FIELD_SELECTION_SHA)
        require(subprocess.check_output(['git', 'show', publication + ':' + FIELD_SELECTION_REL], cwd=ROOT, timeout=120) ==
                field_selection_path.read_bytes(), 'Final source selection differs from publication bytes.')
        field_selection = json.loads(field_selection_path.read_text())
        previous_override_path = bind(ROOT / PREVIOUS_SOURCE_OVERRIDE_REL, PREVIOUS_SOURCE_OVERRIDE_SHA)
        require(subprocess.check_output(['git', 'show', publication + ':' + PREVIOUS_SOURCE_OVERRIDE_REL], cwd=ROOT, timeout=120) ==
                previous_override_path.read_bytes(), 'Previous explicit source override differs from publication bytes.')
        previous_override = json.loads(previous_override_path.read_text())
        override_path = bind(ROOT / SOURCE_OVERRIDE_REL, SOURCE_OVERRIDE_SHA)
        require(subprocess.check_output(['git', 'show', publication + ':' + SOURCE_OVERRIDE_REL], cwd=ROOT, timeout=120) ==
                override_path.read_bytes(), 'Symbolic source override differs from publication bytes.')
        override = json.loads(override_path.read_text())
        SOURCES = select_symbolic_sources(selection, field_selection, previous_override, override)
        require(field['source_graph'] == {m: SOURCES[m] for m in field_selection['source_graph']} and
                artifact(field['source_and_receipt_selection'], FIELD_SELECTION_SHA) == field_selection_path and
                artifact(field['source_selection_override'], SOURCE_OVERRIDE_SHA) == override_path and
                field['source_override_details'] == override and
                previous['source_graph'] == {**field_selection['source_graph'], FIELD_TARGET: previous_override['source_spec']} and
                artifact(previous['source_and_receipt_selection'], FIELD_SELECTION_SHA) == field_selection_path and
                artifact(previous['source_selection_override'], PREVIOUS_SOURCE_OVERRIDE_SHA) == previous_override_path and
                previous['source_override_details'] == previous_override and
                earlier['source_graph'] == field_selection['source_graph'],
                'Accepted symbolic receipt does not bind the exact source overlay and both failed final graphs.')
        state['source_selection_override'] = {
            'original_consumer_selection': record_file(selection_path),
            'original_final_selection': record_file(field_selection_path),
            'previous_explicit_source_override': record_file(previous_override_path),
            'accepted_symbolic_source_override': record_file(override_path),
            'changed_module': FIELD_TARGET,
            'old_source': selection['source_graph'][FIELD_TARGET], 'new_source': SOURCES[FIELD_TARGET],
            'unchanged_source_rows': 44, 'dependency_receipt_selection_complete': True,
            'final_receipt': record_file(field_path)}
        require(len(SOURCES) == 45 and set(FRESH_MODULES) <= set(SOURCES), 'Unexpected source graph size/targets.')
        require(failed_consumer['source_graph'] == SOURCES and
                failed_consumer['field_stage_receipt'] == record_file(field_path) and
                failed_consumer['accepted_field_private_composition_helper'] == field['private_composition_helper_record'],
                'Disk retry changed the prior source graph or accepted Field prerequisite.')
        original_sources = SOURCES
        require(failed_parse['source_graph'] == original_sources,
                'Actual partial consumer source graph differs from the original five-owner selection.')
        parse_override_path = bind(ROOT / PARSE_OVERRIDE_REL, PARSE_OVERRIDE_SHA)
        require(subprocess.check_output(['git', 'show', publication + ':' + PARSE_OVERRIDE_REL], cwd=ROOT, timeout=120) ==
                parse_override_path.read_bytes(), 'Parse transport override differs from publication bytes.')
        parse_override = json.loads(parse_override_path.read_text())
        SOURCES = select_parse_sources(original_sources, parse_override)
        old_parse_source = bind(ROOT / OLD_PARSE_SOURCE_REL, OLD_PARSE_SOURCE_SHA)
        new_parse_source = bind(ROOT / PARSE_SOURCE_REL, PARSE_SOURCE_SHA)
        public_headers = lambda text: re.findall(r'^theorem\s+(\w+)\s*:(.*?)\s*:=\s*by', text, re.M | re.S)
        require(public_headers(old_parse_source.read_text()) == public_headers(new_parse_source.read_text()) and
                len(public_headers(new_parse_source.read_text())) == 3 and
                [PARSE_TARGET + '.' + name for name in re.findall(r'^private theorem (\w+)', new_parse_source.read_text(), re.M)] == PARSE_PRIVATE_HELPERS,
                'Parse transport changed a public theorem statement or the reviewed private helper scope.')
        require(SOURCES == prior_v8['source_graph'], 'The accepted Parse original 45-source graph changed')
        state['parse_source_selection_override'] = {
            **record_file(parse_override_path), 'details': parse_override,
            'old_source': original_sources[PARSE_TARGET], 'new_source': SOURCES[PARSE_TARGET],
            'unchanged_source_rows': 44, 'new_private_expression_helpers': PARSE_PRIVATE_HELPERS,
            'historical_v8_owner_order': V8_CONTINUATION_MODULES, 'historical_v8_public_source_declarations': 17,
            'fresh_owner_order': CONTINUATION_MODULES, 'fresh_public_source_declarations': 14,
            'reused_decoded_public_source_declarations': 3, 'reused_decoded_owned_declarations': 4}
        floors_override_path = bind(ROOT / FLOORS_OVERRIDE_REL, FLOORS_OVERRIDE_SHA)
        floors_override = json.loads(floors_override_path.read_text())
        SOURCES = select_floors_sources(SOURCES, floors_override)
        pending_review_path = bind(ROOT / PENDING_SOURCE_REVIEW_REL, PENDING_SOURCE_REVIEW_SHA)
        pending_review = json.loads(pending_review_path.read_text())
        SOURCES = select_pending_source_overlays(SOURCES, pending_review, prior_v8['source_graph'])
        require(SOURCES == prepared['source_graph'], 'Fresh source graph differs from read-only v9 plan')
        state['floors_source_selection_override'] = {**record_file(floors_override_path), 'details': floors_override}
        state['pending_source_selection_addendum'] = {**record_file(pending_review_path), 'details': pending_review,
            'allowed_changed_sources': CONTINUATION_MODULES, 'unchanged_source_rows': 42,
            'prior_status_of_additional_owners': 'PENDING', 'prior_stages_of_additional_owners': {}}
        old_driver = bind(ROOT / selection['adapted_from']['path'], '4678b1b316d2741a5a0e80a47969ed42addbfc5ed067b6a27ecf4302f43db5a0')
        require(old_driver.stat().st_size == selection['adapted_from']['bytes'] == 50239,
                'The old consumer driver must remain byte-identical.')
        state['original_consumer_driver'] = record_file(old_driver)
        reviewed_driver = bind(ROOT / ORIGINAL_REVIEWED_DRIVER_REL, ORIGINAL_REVIEWED_DRIVER_SHA)
        require(reviewed_driver.stat().st_size == 70770, 'The original reviewed five-consumer driver changed.')
        state['original_reviewed_five_consumer_driver'] = record_file(reviewed_driver)
        adapted_driver = bind(ROOT / ADAPTED_FROM_REL, ADAPTED_FROM_SHA)
        require(adapted_driver.stat().st_size == 110371, 'The preserved v5 consumer driver changed.')
        state['adapted_from_unchanged_driver'] = record_file(adapted_driver)
        state['source_and_receipt_selection'] = record_file(selection_path)
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

        for key, receipt, expected_runner in [('field_final', field, FIELD_RUNNER_SHA),
                                               ('field_split_history', split, SPLIT_RUNNER_SHA),
                                               ('failed_final_history', previous, PREVIOUS_FINAL_RUNNER_SHA),
                                               ('earlier_failed_final_history', earlier, EARLIER_FINAL_RUNNER_SHA),
                                               ('remaining_arithmetic', remaining, REMAINING_RUNNER_SHA),
                                               ('typed_source_facts', facts, FACTS_RUNNER_SHA),
                                               ('accepted_decoded_failed_consumer', failed_parse, FAILED_PARSE_RUNNER_SHA),
                                               ('accepted_parse_failed_v8', prior_v8, IMMUTABLE_V8_SHA)]:
            require(receipt['runtime'] == state['runtime'] and receipt['strict_flags'] == FLAGS and
                    receipt['approved_LEAN_PATH'].split(':')[1:] == tails,
                    'Accepted dependency runtime or external path differs: ' + key)
            artifact(receipt['runner'], expected_runner)
            for path, sha in receipt['frozen_inputs'].items():
                historical_pin(path, sha)
        state['package_metadata'] = []
        for row in [*selection['package_pins'], *field_selection['package_pins']]:
            path = bind(ROOT / row['path'], row['sha256'])
            require(path.stat().st_size == row['bytes'] and
                    subprocess.check_output(['git', 'show', publication + ':' + row['path']], cwd=ROOT, timeout=120) == path.read_bytes(),
                    'Selected immutable package metadata differs from publication: ' + row['path'])
            state['package_metadata'].append(record_file(path))
        manifest_path = bind(ROOT / PACKAGE / 'MANIFEST.json', MANIFEST_SHA)
        manifest = json.loads(manifest_path.read_text())
        selected = {row['module']: row for row in manifest['selected_modules']}
        require(set(selected) == set(FRESH_MODULES[:3]), 'The original consumer manifest must still select exactly its three unchanged owners.')
        for module, source_spec in SOURCES.items():
            path = bind(ROOT / source_spec['path'], source_spec['source_sha256'])
            published = subprocess.check_output(['git', 'show', f'{publication}:{source_spec["path"]}'], cwd=ROOT, timeout=120)
            require(published == path.read_bytes(), f'Source is not exact publication bytes: {module}')
            imports = [name for line in re.findall(r'^import\s+([^\n]+)$', path.read_text(), re.M)
                       for name in line.split() if name.startswith('ImbalancedChen.')]
            require(imports == source_spec['project_imports'], f'Frozen source import graph mismatch: {module}')
            namespace = source_spec.get('public_namespace')
            names = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)', path.read_text(), re.M)
            actual_public = [namespace + '.' + name for name in names] if namespace else []
            require(source_spec['public_names'] == actual_public, 'Frozen public source names differ: ' + module)
        for module, row in selected.items():
            require(row['path'] == original_sources[module]['path'] and row['sha256'] == original_sources[module]['source_sha256'] and
                    (ROOT / row['path']).stat().st_size == row['bytes'] and
                    [module + '.' + name for name in row['public_declarations']] == SOURCES[module]['public_names'],
                    f'Original consumer manifest/source/public names changed: {module}')
        require(sum(len(SOURCES[module]['public_names']) for module in FRESH_MODULES) == 20,
                'Exactly twenty public source declarations across the original five-owner scope are selected.')
        require(sum(len(SOURCES[module]['public_names']) for module in CONTINUATION_MODULES) == 14 and
                len(SOURCES[DECODED]['public_names']) == len(SOURCES[PARSE_TARGET]['public_names']) == 3 and
                DECODED not in target_names and PARSE_TARGET not in target_names,
                'Exactly fourteen public source declarations are fresh; accepted Decoded and Parse are dependencies.')
        expected_closures = {module: sorted(project_closure(module)) for module in FRESH_MODULES}
        require(selection['expected_project_closures'] == expected_closures and
                set().union(*(set(value) for value in expected_closures.values())) == set(SOURCES),
                'Selected source graph has missing or extraneous project modules.')
        state['consumer_manifest'] = record_file(manifest_path)
        state['source_graph'] = SOURCES
        state['expected_project_imports_by_owner'] = expected_closures
        appendix_path = bind(ROOT / SCOPED_APPENDIX_REL, SCOPED_APPENDIX_SHA)
        appendix_text = appendix_path.read_text()
        expected_private = [SCOPE + '.' + name for name in re.findall(r'^private theorem ([A-Za-z0-9_]+)\b',
                            (ROOT / SOURCES[SUPPORT]['path']).read_text(), re.M)]
        require(len(expected_private) == len(set(expected_private)) == 296 and
                expected_private == split['source_identity_check']['private_user_names'] and
                re.findall(r'^    "(ImbalancedChen\.[^"]+)"[,\]]', appendix_text, re.M) == expected_private,
                'The imported FieldSimp audit must cover every original private theorem.')
        require(split['command_identity']['sha256'] == '9f33526038f4d7e403cdbf3e422b386af2d861733e743ea0c0a690f66a7c5657' and
                split['source_identity_check']['original_commands'] == 442 and
                split['source_identity_check']['all_commands_byte_identical'] is True and
                split['scoped_simp_audit_appendix']['sha256'] == SCOPED_APPENDIX_SHA,
                'Field command/scoped-simp identity evidence differs.')

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

        # The accepted current snapshot is reused exactly, including companions.
        # Original missing historical hashes are never filled in retroactively.
        current_snapshot_path = artifact(remaining['complete_external_before'], EXTERNAL_SNAPSHOT_SHA)
        require(current_snapshot_path == REMAINING / 'COMPLETE_EXTERNAL_BEFORE.json' and
                selection['external_context']['sha256'] == EXTERNAL_SNAPSHOT_SHA,
                'Complete current external snapshot selection differs.')
        current_snapshot = json.loads(current_snapshot_path.read_text())
        providers = [LEAN.parent.parent / 'lib/lean', *map(Path, tails)]
        require(len(providers) == len(set(providers)) and
                all(provider.is_dir() and not (provider / 'ImbalancedChen').exists() for provider in providers) and
                current_snapshot['provider_roots'] == list(map(str, providers)) and
                current_snapshot['schema'] == 'p25-complete-current-external-snapshot-v1' and
                current_snapshot['module_count'] == EXPECTED_EXTERNAL_COUNT and
                current_snapshot['historical_missing_hashes_invented'] is False,
                'Complete accepted current snapshot/provider/provenance differs.')
        expected_external = {row['module'] for row in current_snapshot['entries']}
        require(len(expected_external) == len(current_snapshot['entries']) == EXPECTED_EXTERNAL_COUNT and
                sum(len(row['companions']) for row in current_snapshot['entries']) == EXPECTED_EXTERNAL_COMPANIONS,
                'Complete current external module/companion inventory differs.')
        context_start = now()
        for row in current_snapshot['entries']:
            module = row['module']
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module),
                    'Invalid external module name.')
            relative = module.replace('.', '/') + '.olean'
            found = [provider / relative for provider in providers if (provider / relative).is_file()]
            require(len(found) == 1 and str(found[0]) == row['object']['path'],
                    'Missing or shadowed accepted current external provider: ' + module)
            obj = artifact(row['object'])
            require(remaining['frozen_inputs'].get(str(obj)) == row['object']['sha256'],
                    'Accepted current context did not freeze this external object: ' + module)
            actual_companions = [str(obj) + suffix for suffix in ['.private', '.server']
                                 if Path(str(obj) + suffix).is_file()]
            require(actual_companions == [item['path'] for item in row['companions']],
                    'Accepted current external companion inventory changed: ' + module)
            for companion in row['companions']:
                artifact(companion)
                require(remaining['frozen_inputs'].get(companion['path']) == companion['sha256'],
                        'Accepted current context did not freeze this external companion: ' + module)
            external_entries.append({'module': module, 'object': row['object'], 'companions': row['companions']})
        expected_external_records = {row['module']: (row['object'], row['companions']) for row in external_entries}
        for label, container in [('field_final', field), ('field_split_history', split),
                                 ('failed_final_history', previous), ('earlier_failed_final_history', earlier),
                                 ('typed_source_facts', facts), ('accepted_decoded_failed_consumer', failed_parse),
                                 ('accepted_parse_failed_v8', prior_v8)]:
            descriptor = container['complete_external_before']
            if descriptor['path'] in unavailable_envelopes:
                expected = envelope_allowance[descriptor['path']]
                require(descriptor == {k:expected[k] for k in ('path', 'bytes', 'sha256')}
                        and not os.path.lexists(descriptor['path']), 'Unreviewed unavailable historical envelope')
                # The old envelope is unavailable. Its descriptor is preserved;
                # every current external record is checked against this old map below.
            else:
                accepted_snapshot = json.loads(artifact(descriptor).read_text())
                require(accepted_snapshot['provider_roots'] == list(map(str, providers)) and
                        accepted_snapshot['module_count'] == EXPECTED_EXTERNAL_COUNT and
                        len(accepted_snapshot['entries']) == EXPECTED_EXTERNAL_COUNT and
                        {row['module']: (row['object'], row['companions']) for row in accepted_snapshot['entries']} == expected_external_records,
                        'A reused proof branch has a different complete current external context: ' + label)
            for row in external_entries:
                for record in [row['object'], *row['companions']]:
                    require(container['frozen_inputs'].get(record['path']) == record['sha256'],
                            'Reused proof branch did not freeze an external object or companion: ' + label + '/' + row['module'])
        before = {'schema': 'p25-complete-current-external-snapshot-reuse-v1',
                  'started_utc': context_start, 'finished_utc': now(), 'provider_roots': list(map(str, providers)),
                  'module_count': len(external_entries), 'source_accepted_receipt': record_file(remaining_path),
                  'source_complete_snapshot': record_file(current_snapshot_path),
                  'all_hashes_reused_from_accepted_current_snapshot': True,
                  'historical_missing_hashes_invented': False, 'entries': external_entries}
        before_path = OUT / 'COMPLETE_EXTERNAL_BEFORE.json'
        before_path.write_text(json.dumps(before, indent=2) + '\n')
        bind(before_path)
        state['complete_external_before'] = record_file(before_path)
        state['external_context_receipt'] = record_file(remaining_path)
        state['expected_external_imports'] = sorted(expected_external)

        # Read original owner dictionaries under their original aggregate and
        # publication. The failed aggregates never become successful containers.
        for module, expected_object in REUSED_FIELD_OBJECTS.items():
            selected_receipt = split['owner_receipt_sources'][module]
            require(artifact(selected_receipt, PRIOR_FIELD_RESULT_SHA) == prior_field_path and
                    selected_receipt['owner_module'] == module and selected_receipt['owner_accepted'] is True and
                    selected_receipt['aggregate_status'] == prior_field['status'] and selected_receipt['aggregate_accepted'] is False and
                    selected_receipt['owner_source_origin'] == prior_field['modules'][module]['source_origin'] and
                    selected_receipt['owner_object_sha256'] == expected_object and
                    split['modules'][module] == prior_field['modules'][module] and
                    prior_field['modules'][module]['source_origin']['commit'] == PRIOR_FIELD_PUBLICATION and
                    prior_field['modules'][module]['object']['sha256'] == expected_object,
                    'An original Field owner was relabeled or its accepted bytes changed: ' + module)
            row = split['reused_owner_objects'][module]
            require(row['sha256'] == expected_object and row['source_sha256'] == SOURCES[module]['source_sha256'],
                    'Field reused object/source identity differs: ' + module)
            bind(row['path'], expected_object)
            bind(row['isolated_path'], expected_object)
        expected_field_dependencies = set().union(*(project_closure(module) for module in FIELD_OWNERS)) - set(FIELD_OWNERS)
        require(set(split['dependency_objects']) == expected_field_dependencies and len(expected_field_dependencies) == 8,
                'Historical Field dependency set differs from the actual split source graph.')
        state['disk_checks'].append(check_disk_space(max(MIN_INITIAL_FREE_BYTES,
                                                         METADATA_HEADROOM_BYTES + GATE_WORKING_HEADROOM_BYTES),
                                                    'immediately before accepted dependency hardlinking'))
        write()
        for module, row in split['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'], 'Field reused source hash differs: ' + module)
            bind(row['path'], row['sha256'])
            copy_dependency(module, row['isolated_path'], row['sha256'],
                            'Accepted Field base object under unchanged historical receipt provenance', row.get('companions', []))
        for module in REUSED_FIELD_OWNERS:
            origin = prior_field if module in REUSED_FIELD_OBJECTS else split
            origin_path = prior_field_path if module in REUSED_FIELD_OBJECTS else split_path
            require(artifact(field['source_receipt_by_reused_owner'][module]) == origin_path,
                    'Final receipt points to a different historical owner receipt: ' + module)
            modern_owner(origin, origin_path, module)
            state['reused_original_owner_receipts'][module] = origin['modules'][module]
        for module in REUSED_FIELD_OBJECTS:
            verify_reuse_validation(split['additional_reuse_validations'][module],
                                    prior_field['modules'][module], prior_field_path, split)
        expected_final_dependencies = set(field_selection['source_graph']) - {FIELD_TARGET}
        require(set(field['dependency_objects']) == expected_final_dependencies and len(expected_final_dependencies) == 21,
                'The accepted final Field owner must reuse exactly its original 21 dependencies.')
        for module, row in field['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'] and
                    module in state['dependency_objects'] and row['sha256'] == state['dependency_objects'][module]['sha256'],
                    'Accepted final dependency differs from original historical object: ' + module)
            bind(row['path'], row['sha256'])
            copy_dependency(module, row['isolated_path'], row['sha256'],
                            'Exact accepted final dependency matched to historical object provenance', row.get('companions', []))
        modern_owner(field, field_path, FIELD_TARGET)
        state['accepted_field_private_composition_helper'] = validate_private_composition(field)
        state['accepted_field_private_composition_helper_checked'] = True
        modern_owner(payload_receipt, payload_path, PAYLOAD)
        modern_owner(payload_receipt, payload_path, FLOORS)
        state['field_stage_receipt'] = record_file(field_path)
        state['field_owner_receipt_sources'] = {
            module: record_file(prior_field_path if module in REUSED_FIELD_OBJECTS else
                                field_path if module == FIELD_TARGET else split_path)
            for module in FIELD_OWNERS}
        state['historical_owner_publications_preserved'] = True
        state['payload_floors_receipt'] = record_file(payload_path)

        expected_arithmetic_dependencies = set().union(*(project_closure(module) for module in ARITHMETIC_MODULES)) - set(ARITHMETIC_MODULES)
        require(set(remaining['dependency_objects']) == expected_arithmetic_dependencies and len(expected_arithmetic_dependencies) == 9,
                'Accepted arithmetic dependency set differs from source graph.')
        for module, row in remaining['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'], 'Arithmetic reused source hash differs: ' + module)
            bind(row['path'], row['sha256'])
            copy_dependency(module, row['isolated_path'], row['sha256'],
                            'Accepted AllRows dependency with original Row00/P1 capsule receipt chain preserved', row.get('companions', []))
        modern_owner(row00, row00_path, ROW00)
        state['reused_original_owner_receipts'][ROW00] = row00['modules'][ROW00]
        verify_reuse_validation(remaining['row00_additional_reuse_validation'], row00['modules'][ROW00], row00_path, remaining)
        for module in ARITHMETIC_MODULES:
            modern_owner(remaining, remaining_path, module)
        state['remaining_arithmetic_receipt'] = record_file(remaining_path)
        require(set(facts['dependency_objects']) == project_closure(FACTS_MODULE) - {FACTS_MODULE} and
                len(facts['dependency_objects']) == 7, 'TypedSourceFacts source graph differs.')
        for module, row in facts['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'], 'TypedSourceFacts reused source hash differs: ' + module)
            bind(row['path'], row['sha256'])
            copy_dependency(module, row['isolated_path'], row['sha256'],
                            'Accepted TypedSourceFacts dependency under the same complete external snapshot', row.get('companions', []))
        modern_owner(facts, facts_path, FACTS_MODULE)
        state['typed_source_facts_receipt'] = record_file(facts_path)
        for container in [prior_field, split, earlier, previous, field, remaining, row00, facts, payload_receipt]:
            verify_container_objects(container)

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
        # This accepted owner is read from the still-failed actual aggregate.
        # modern_owner rechecks its original source, three logs, complete audit,
        # owned inventory, object, companions, and original publication.
        modern_owner(failed_parse, failed_parse_path, DECODED)
        verify_container_objects(failed_parse)
        require(state['dependency_receipts'][DECODED]['owner_publication'] == FAILED_PARSE_PUBLICATION and
                state['dependency_objects'][DECODED]['sha256'] == DECODED_OBJECT_SHA and
                state['reused_decoded_owner_receipt'] == failed_parse['modules'][DECODED],
                'The exact accepted Decoded owner must be reused under its original provenance.')
        modern_owner(prior_v8, prior_v8_path, PARSE_TARGET)
        verify_container_objects(prior_v8)
        parse_owner = prior_v8['modules'][PARSE_TARGET]
        parse_helpers = validate_parse_helpers(parse_owner['owned_declarations'])
        require(parse_helpers == parse_owner['private_expression_helpers'] == prior_v8['private_parse_helper_records']
                and parse_owner['owned_count'] == len(parse_owner['owned_declarations']) == 7
                and state['dependency_receipts'][PARSE_TARGET]['owner_publication'] == PRIOR_V8_PUBLICATION
                and state['dependency_objects'][PARSE_TARGET]['sha256'] == PARSE_OBJECT_SHA,
                'Accepted Parse owner, complete seven-record audit or three private helpers changed')
        state['private_parse_helper_records'] = parse_helpers
        state['private_parse_helpers_audited'] = True
        needed = set().union(*(project_closure(m) for m in target_names)) - target_names
        validate_dependency_identities({m: r['sha256'] for m, r in state['dependency_objects'].items()},
                                       prepared['cfg']['objects'], PARSE_OBJECT_SHA)
        require(set(state['dependency_objects']) == needed and len(needed) == 42 and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 42,
                'The initial isolated library must contain exactly 42 accepted dependency objects.')
        require(all(not (lib / (m.replace('.', '/') + '.olean')).exists() for m in target_names),
                'A selected unaccepted consumer target already has an object.')

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
        require(set(failed_consumer['dependency_objects']) == set(state['dependency_objects']) - {DECODED, PARSE_TARGET} and
                all(failed_consumer['dependency_objects'][module]['sha256'] == row['sha256'] and
                    failed_consumer['dependency_objects'][module]['source_sha256'] == row['source_sha256']
                    for module, row in state['dependency_objects'].items() if module not in {DECODED, PARSE_TARGET}) and
                failed_consumer['reused_original_owner_receipts'] == state['reused_original_owner_receipts'] and
                failed_consumer['reused_complete_context_validations'] == state['reused_complete_context_validations'],
                'Continuation changed one of the forty qualified earlier dependencies or historical owner identities.')
        state.update(status='VERIFYING_THREE_CONSUMERS', frozen_inputs=dict(frozen))
        context_check()
        write()
        for spec in MODULES:
            module = spec['module']
            owner = state['modules'][module]
            state['disk_checks'].append(check_disk_space(GATE_WORKING_HEADROOM_BYTES,
                                                         'before fresh owner directory: ' + module))
            owner['status'] = 'RUNNING'
            directory = OUT / module.split('.')[-1]
            directory.mkdir()
            source = src / (module.replace('.', '/') + '.lean')
            object_path = lib / (module.replace('.', '/') + '.olean')
            audit_path = audit / (module.split('.')[-1] + '.lean')
            require(not object_path.exists(), f'Target object already exists: {module}')
            require(all(name in state['dependency_objects'] or
                        (name in state['modules'] and state['modules'][name]['accepted'] is True)
                        for name in project_closure(module) - {module}),
                    'A selected consumer dependency has not passed every gate: ' + module)
            for label, command in [
                ('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(object_path), str(source)]),
                ('replay', [str(CHECKER), '--verbose', module]),
                ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(audit_path)]),
            ]:
                state['disk_checks'].append(check_disk_space(GATE_WORKING_HEADROOM_BYTES,
                                                             'before fresh gate: ' + module + '/' + label))
                write()
                run_stage(owner, label, command, directory / (label.upper() + '.log'))
                if label == 'normal':
                    bind(object_path)
                    owner['object'] = record_file(object_path)
                    owner['object_companions'] = []
                    for suffix in ['.private', '.server']:
                        companion = Path(str(object_path) + suffix)
                        if companion.exists():
                            bind(companion)
                            owner['object_companions'].append(record_file(companion))
                    state['frozen_inputs'] = dict(frozen)
                    write()
            records, inventory, imports = read_audit(directory / 'AUDIT.log', module)
            require(set(owner['required_owned_names']) <= {r['name'] for r in records}, f'Required public consumer missing: {module}')
            external = require_external(directory / 'AUDIT.log')
            owner['actual_external_import_count'] = len(external)
            owner['complete_external_before'] = record_file(before_path)
            declarations_path, inventory_path = directory / 'OWNED_DECLARATIONS.json', directory / 'OWNED_INVENTORY.json'
            declarations_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n')
            inventory_path.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + '\n')
            bind(declarations_path)
            bind(inventory_path)
            state['frozen_inputs'] = dict(frozen)
            owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                         owned_count=len(records), owned_declarations=records, actual_project_closure=imports,
                         declarations=record_file(declarations_path), inventory=record_file(inventory_path), ended_utc=now())
            context_check()
            write()
            print('P25_CONSUMER_OWNER_ACCEPTED', module, len(records), owner['object']['sha256'], flush=True)
        require(set(state['modules']) == target_names and all(owner['accepted'] is True for owner in state['modules'].values()) and
                state['module_order'] == CONTINUATION_MODULES and
                state['dependency_modules_compiled'] == state['existing_owners_normally_recompiled'] == prepared['normal_modules'] and
                state['consumer_phase_dependency_modules_compiled'] == state['accepted_dependency_gates_rerun'] == [] and
                prepared['normal_modules'] == prepared['normal_order'] == prepared['normal_stages'] == [] and
                state['normal_rematerialization_stages'] == [] and state['parse_gates_rerun'] == [] and
                state['historical_v8_normal_rematerialization_stages'] == prior_v8['normal_rematerialization_stages'] and
                state['historical_v8_normal_modules'] == prior_v8['dependency_modules_compiled'] and
                state['prior_v8_aggregate_accepted'] is False and state['prior_v8_aggregate_relabelled'] is False and
                state['reused_parse_owner_receipt'] == prior_v8['modules'][PARSE_TARGET] and
                state['reused_parse_owner_receipt']['accepted'] is True and
                set(state['reused_original_owner_receipts']) == {*REUSED_FIELD_OWNERS, ROW00} and
                set(state['reused_complete_context_validations']) == {*REUSED_FIELD_OBJECTS, ROW00} and
                all(state['reused_original_owner_receipts'][module] == prior_field['modules'][module] for module in REUSED_FIELD_OBJECTS) and
                all(state['reused_original_owner_receipts'][module] == split['modules'][module] for module in SPLIT_ACCEPTED_MODULES) and
                state['reused_original_owner_receipts'][ROW00] == row00['modules'][ROW00] and
                state['failed_split_receipt']['aggregate_accepted'] is False and
                state['prior_failed_final_owner'] == split['modules'][FIELD_TARGET] and
                state['previous_final_attempt']['aggregate_accepted'] is False and
                state['previous_final_failed_owner'] == previous['modules'][FIELD_TARGET] and
                state['historical_owner_publications_preserved'] is True and
                state['private_parse_helpers_audited'] is True and
                state['reused_decoded_owner_receipt'] == failed_parse['modules'][DECODED] and
                state['reused_decoded_owner_receipt']['accepted'] is True and
                state['previous_parse_failed_owner'] == failed_parse['modules'][PARSE_TARGET] and
                state['previous_parse_failure']['aggregate_accepted'] is False and
                state['decoded_gates_rerun'] == [] and state['failed_parse_aggregate_relabelled'] is False and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 45,
                'Three fresh owners, accepted Decoded/Parse, unchanged historical receipts or zero-rerun policy changed.')
        context_check()
        after = current_context(prepared, 'after-three-consumer-gates')
        before = json.loads(Path(prepared['fresh_context_before']['path']).read_text())
        require(after['provider_roots'] == before['provider_roots'] and after['entries'] == before['entries'],
                'Actual fresh external context changed across successor reuse and consumer gates')
        after_path = OUT / 'FRESH_CONTEXT_AFTER.json'
        after_path.write_text(json.dumps(after, indent=2) + '\n')
        bind(after_path)
        state['fresh_context_after'] = record_file(after_path)
        context_check()
        state.update(status='ORIGINAL_CELL00_THREE_SUCCESSOR_CONSUMERS_ACCEPTED', accepted=True,
                     original_cell00_decode_proved=True, original_cell00_stored_floors_proved=True,
                     original_cell00_simplex_guards_proved=True, original_cellFloorNumerator_proved=True,
                     original_cellFloorNumerator_value=13236428172062120,
                     original_cell00_headers_proved=True, original_cell00_facet_indices_proved=True,
                     original_cell00_geometric_jensen_binding_proved=True,
                     complete_external_after_matches_before=True, frozen_inputs=dict(frozen), ended_utc=now())
        write()
        print('P25_THREE_CONSUMERS_RESULT', json.dumps({
            'status': state['status'], 'accepted': True, 'owned_counts': {module: owner['owned_count'] for module, owner in state['modules'].items()},
            'original_archive_cell': 0, 'cellFloorNumerator': 13236428172062120,
            'accepted_decoded_reused': True, 'reused_decoded_owned_count': 4,
            'accepted_parse_reused': True, 'reused_parse_owned_count': 7, 'new_dependency_normal_count': 0,
            'private_parse_helpers_audited': True,
            'original_all_eight_simplex_guards': True, 'original_headers': True, 'original_facet_indices': True,
            'source_cell_membership_proved': False, 'all96_vertex_inequalities_proved': False,
            'pulling_ownership_proved': False, 'all_cell_finite_guards_proved': False,
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
        print('P25_THREE_CONSUMERS_FAILED', json.dumps({'status': state['status'], 'error': state['error'][:1800],
              'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json')}, sort_keys=True), flush=True)
        raise SystemExit(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication')
    parser.add_argument('--runner-sha256', required=True)
    parser.add_argument('--selection-sha256', required=True)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--plan', action='store_true', help='read-only preflight; the default')
    modes.add_argument('--execute', action='store_true', help='new attempt009 context and only three consumer normal/kernel/owned gates')
    args = parser.parse_args()
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    sys.dont_write_bytecode = True
    prepared = None
    try:
        prepared = fresh_preflight(args.publication, ROOT / V9_SELECTION_REL,
                                   args.selection_sha256, args.runner_sha256)
        if not args.execute:
            print('P25_V9_READ_ONLY_PLAN ' + json.dumps(prepared['plan'], sort_keys=True), flush=True)
            return 0
        create_successor_context(prepared)
        run_consumers(args.publication, prepared)
        return 0
    except BaseException as error:
        if prepared is not None and prepared.get('created_output') is True and not (OUT / 'RESULT.json').exists():
            value = {'schema': 'p25-cell00-three-consumers-successor-strict-v9', 'status': 'FAILED',
                     'accepted': False, 'publication_commit': args.publication,
                     'runner_sha256': args.runner_sha256, 'selection_sha256': args.selection_sha256,
                     'ended_utc': now(), 'error': type(error).__name__ + ': ' + str(error),
                     'failed_phase': 'successor-context-or-three-consumer-preflight',
                     'historical_archive_gaps': prepared['archive_gaps'],
                     'normal_rematerialization_stages': [], 'dependency_modules_compiled': [],
                     'parse_gates_rerun': [], 'prior_v8_receipt': prepared['prior_v8_receipt'],
                     'historical_v8_normal_rematerialization_receipt': prepared['prior_v8_rematerialization_receipt'],
                     'prior_v8_aggregate_accepted': False,
                     'old_v7_preflight_passed': False, 'old_recovery_complete': False,
                     'old_snapshots_synthesized': False, 'Q96_proved': False, 'P2_5_proved': False}
            (OUT / 'RESULT.json').write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
        print('P25_V9_STOP ' + type(error).__name__ + ': ' + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == '__main__':
    sys.exit(main())
