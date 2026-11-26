#!/usr/bin/env python3
"""Resource-only recovery of the five unchanged Cell00 consumers.

The exact v4 attempt004 failed with ENOSPC before any compiler gate. Preserve its
complete failure receipt, all source/context artifacts, and every unaccepted
owner. Reuse the accepted attempt006 FieldDecode and the same forty accepted
dependencies. A new attempt005 runs only the same five owners after checking live
space for exact copies and fresh gate evidence. All v4 verification helpers are
unchanged. This driver performs no storage cleanup or accepted gate rerun.
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
OUT = ROOT / '.lake/diagnostic/p25-cell00-five-consumers-attempt005'
FAILED_CONSUMER = ROOT / '.lake/diagnostic/p25-cell00-five-consumers-attempt004'
FAILED_CONSUMER_RESULT_SHA = '2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a'
FAILED_CONSUMER_PUBLICATION = '8fb0faace8f95a4ad4be26f32350575491445ac4'
FAILED_CONSUMER_RUNNER_SHA = 'd9e4360463fc692a0fda62ddd77e77a6f53d837ff5c68f29087bac1fafbbe7ef'
FAILED_CONSUMER_EXCEPTION_SHA = 'e615dca0984636d16301a0a068e02f1dea5bbde7e89157b068023a26dbd7a926'
MIN_INITIAL_FREE_BYTES = 1024 * 1024 * 1024
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
RUNNER_REL = 'docs/verification/20261126-p2-5-resumed/run_cell00_five_consumers_v5.py'
ORIGINAL_REVIEWED_DRIVER_REL = 'docs/verification/20261126-p2-5-continuation/run_cell00_five_consumers_cloud.py'
ORIGINAL_REVIEWED_DRIVER_SHA = '4f12d9bcb43b2fd4a0b626d5803dfb27b7ec7f05784d005f7378879ccd0d620f'
ADAPTED_FROM_REL = 'docs/verification/20261126-p2-5-resumed/run_cell00_five_consumers_v4.py'
ADAPTED_FROM_SHA = 'd9e4360463fc692a0fda62ddd77e77a6f53d837ff5c68f29087bac1fafbbe7ef'
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
FIELD_FRESH_MODULES = [SUPPORT, 'ImbalancedChen.P2Saving16Cell00FieldBase',
    *[f'ImbalancedChen.P2Saving16Cell00Simplex{i:02d}Decode' for i in range(8)], FIELD_TARGET]
FIELD_OWNERS = [*REUSED_FIELD_OBJECTS, *FIELD_FRESH_MODULES]
SPLIT_ACCEPTED_MODULES = FIELD_FRESH_MODULES[:-1]
REUSED_FIELD_OWNERS = [*REUSED_FIELD_OBJECTS, *SPLIT_ACCEPTED_MODULES]
ARITHMETIC_MODULES = [*[f'ImbalancedChen.P2Saving16Cell00Row{i:02d}Arithmetic' for i in range(1, 8)],
                      'ImbalancedChen.P2Saving16Cell00AllRowsArithmetic']
SOURCES = {}
MODULES = [{'module': module} for module in FRESH_MODULES]


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


def main():
    global SOURCES
    require(isinstance(FIELD_RESULT_SHA, str) and re.fullmatch(r'[0-9a-f]{64}', FIELD_RESULT_SHA) and
            isinstance(FIELD_PUBLICATION, str) and re.fullmatch(r'[0-9a-f]{40}', FIELD_PUBLICATION) and
            FIELD_ARTIFACTS_REVIEWED is True,
            'SOURCE_ONLY: actual successful Field attempt006 receipt, exact publication, and complete local artifact review are required before any mutation or execution.')
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]),
            'Pass exactly one full lowercase 40-hex publication commit.')
    publication = sys.argv[1]
    require(ROOT.is_dir() and not OUT.exists(), 'Expected checkout missing or attempt already exists; preserve prior attempts.')
    failed_consumer_path = FAILED_CONSUMER / 'RESULT.json'
    require(digest(failed_consumer_path) == FAILED_CONSUMER_RESULT_SHA and
            failed_consumer_path.stat().st_size == 5016911, 'Actual failed consumer receipt bytes differ.')
    failed_consumer = json.loads(failed_consumer_path.read_text())
    validate_failed_consumer(failed_consumer)
    require(all(not (FAILED_CONSUMER / 'lib' / (module.replace('.', '/') + '.olean')).exists()
                for module in FRESH_MODULES), 'An old same-name consumer target object unexpectedly exists.')
    exact_copy_bytes = sum(Path(row['path']).stat().st_size +
                           sum(Path(companion['path']).stat().st_size for companion in row['companions'])
                           for row in failed_consumer['dependency_objects'].values())
    initial_disk_check = check_disk_space(max(MIN_INITIAL_FREE_BYTES,
                                              exact_copy_bytes + GATE_WORKING_HEADROOM_BYTES),
                                         'before fresh output and exact accepted dependency copies')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 checkout is dirty.')
    OUT.mkdir()
    state = {
        'schema': 'p25-cell00-five-consumers-strict-v5', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
        'module_order': [s['module'] for s in MODULES], 'modules': {}, 'dependency_objects': {},
        'dependency_receipts': {}, 'dependency_modules_compiled': [], 'private_records_written': [],
        'original_cell00_sha256': INPUT_SHA, 'host_correctness_credit': False,
        'failed_monolithic_Decoded_object_used': False, 'original_cell00_decode_proved': False,
        'original_cell00_stored_floors_proved': False, 'geometric_jensen_binding_proved': False,
        'original_cell00_simplex_guards_proved': False, 'original_cellFloorNumerator_proved': False,
        'original_cell00_geometric_jensen_binding_proved': False,
        'original_cell00_headers_proved': False, 'original_cell00_facet_indices_proved': False,
        'source_cell_membership_proved': False, 'all96_vertex_inequalities_proved': False,
        'positive_normal_balance_proved': False, 'facet_incidence_proved': False, 'pulling_ownership_proved': False,
        'all_cell_finite_guards_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
        'accepted_dependency_gates_rerun': [], 'existing_owners_normally_recompiled': [],
        'complete_external_after_matches_before': False, 'historical_missing_external_hashes_invented': False,
        'reused_original_owner_receipts': {}, 'reused_complete_context_validations': {},
        'failed_split_aggregate_relabelled': False, 'historical_owner_publications_preserved': False,
        'accepted_field_private_composition_helper_checked': False,
        'accepted_field_actual_artifacts_reviewed_before_publication': FIELD_ARTIFACTS_REVIEWED,
        'retry_kind': 'disk-space-recovery-after-consumer-attempt004',
        'previous_consumer_failure': {**record_file(failed_consumer_path),
            'publication_commit': FAILED_CONSUMER_PUBLICATION, 'accepted': False,
            'status': 'FAILED', 'normal_replay_audit_gates_started': 0},
        'previous_consumer_failed_owners': failed_consumer['modules'],
        'failed_consumer_object_used': False, 'storage_cleanup_performed': False,
        'exact_accepted_dependency_copy_bytes': exact_copy_bytes,
        'disk_checks': [initial_disk_check],
    }
    frozen = {}
    external_entries, providers = [], []
    expected_external = set()
    target_names = set(FRESH_MODULES)

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
        shutil.copyfile(original, destination)
        bind(destination, expected)
        copied_companions = []
        for row in companions:
            target = Path(str(destination) + Path(row['path']).suffix)
            require(not target.exists(), f'Unexpected existing companion: {target}')
            shutil.copyfile(row['path'], target)
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
        require(owner['module'] in target_names and label in {'normal', 'replay', 'audit'},
                'Only the five fresh consumers may execute compiler gates.')
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
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=owner['module'], failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{owner["module"]} {label} failed with exit {code}.')
        context_check()

    write()
    try:
        # Retain the complete failed-before-gate evidence; no failed target is reused.
        bind(failed_consumer_path, FAILED_CONSUMER_RESULT_SHA)
        require(json.loads(failed_consumer_path.read_text()) == failed_consumer,
                'Failed consumer receipt changed during disk preflight.')
        artifact(failed_consumer['runner'], FAILED_CONSUMER_RUNNER_SHA)
        artifact(failed_consumer['exception_log'], FAILED_CONSUMER_EXCEPTION_SHA)
        for path, expected in failed_consumer['frozen_inputs'].items():
            bind(path, expected)
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
        old_driver = bind(ROOT / selection['adapted_from']['path'], '4678b1b316d2741a5a0e80a47969ed42addbfc5ed067b6a27ecf4302f43db5a0')
        require(old_driver.stat().st_size == selection['adapted_from']['bytes'] == 50239,
                'The old consumer driver must remain byte-identical.')
        state['original_consumer_driver'] = record_file(old_driver)
        reviewed_driver = bind(ROOT / ORIGINAL_REVIEWED_DRIVER_REL, ORIGINAL_REVIEWED_DRIVER_SHA)
        require(reviewed_driver.stat().st_size == 70770, 'The original reviewed five-consumer driver changed.')
        state['original_reviewed_five_consumer_driver'] = record_file(reviewed_driver)
        adapted_driver = bind(ROOT / ADAPTED_FROM_REL, ADAPTED_FROM_SHA)
        require(adapted_driver.stat().st_size == 102331, 'The preserved v4 consumer driver changed.')
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
                                               ('typed_source_facts', facts, FACTS_RUNNER_SHA)]:
            require(receipt['runtime'] == state['runtime'] and receipt['strict_flags'] == FLAGS and
                    receipt['approved_LEAN_PATH'].split(':')[1:] == tails,
                    'Accepted dependency runtime or external path differs: ' + key)
            artifact(receipt['runner'], expected_runner)
            for path, sha in receipt['frozen_inputs'].items():
                bind(path, sha)
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
            require(row['path'] == SOURCES[module]['path'] and row['sha256'] == SOURCES[module]['source_sha256'] and
                    (ROOT / row['path']).stat().st_size == row['bytes'] and
                    [module + '.' + name for name in row['public_declarations']] == SOURCES[module]['public_names'],
                    f'Original consumer manifest/source/public names changed: {module}')
        require(sum(len(SOURCES[module]['public_names']) for module in FRESH_MODULES) == 20,
                'Exactly twenty public source declarations across the five new owners are selected.')
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
                                 ('typed_source_facts', facts)]:
            accepted_snapshot = json.loads(artifact(container['complete_external_before']).read_text())
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
                                                         exact_copy_bytes + GATE_WORKING_HEADROOM_BYTES),
                                                    'immediately before accepted dependency copying'))
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
        needed = set().union(*(project_closure(m) for m in target_names)) - target_names
        require(set(state['dependency_objects']) == needed and len(needed) == 40 and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 40,
                'The initial isolated library must contain exactly 40 accepted dependency objects.')
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
        require(set(failed_consumer['dependency_objects']) == set(state['dependency_objects']) and
                all(failed_consumer['dependency_objects'][module]['sha256'] == row['sha256'] and
                    failed_consumer['dependency_objects'][module]['source_sha256'] == row['source_sha256']
                    for module, row in state['dependency_objects'].items()) and
                failed_consumer['reused_original_owner_receipts'] == state['reused_original_owner_receipts'] and
                failed_consumer['reused_complete_context_validations'] == state['reused_complete_context_validations'],
                'Disk retry changed qualified accepted dependency or historical owner identities.')
        state.update(status='VERIFYING_FIVE_CONSUMERS', frozen_inputs=dict(frozen))
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
                state['module_order'] == FRESH_MODULES and state['dependency_modules_compiled'] == [] and
                state['existing_owners_normally_recompiled'] == state['accepted_dependency_gates_rerun'] == [] and
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
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 45,
                'Five-owner selection, unchanged original receipts, or dependency reuse policy changed.')
        context_check()
        state.update(status='ORIGINAL_CELL00_FIVE_CONSUMERS_ACCEPTED', accepted=True,
                     original_cell00_decode_proved=True, original_cell00_stored_floors_proved=True,
                     original_cell00_simplex_guards_proved=True, original_cellFloorNumerator_proved=True,
                     original_cellFloorNumerator_value=13236428172062120,
                     original_cell00_headers_proved=True, original_cell00_facet_indices_proved=True,
                     original_cell00_geometric_jensen_binding_proved=True,
                     complete_external_after_matches_before=True, frozen_inputs=dict(frozen), ended_utc=now())
        write()
        print('P25_FIVE_CONSUMERS_RESULT', json.dumps({
            'status': state['status'], 'accepted': True, 'owned_counts': {module: owner['owned_count'] for module, owner in state['modules'].items()},
            'original_archive_cell': 0, 'cellFloorNumerator': 13236428172062120,
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
        print('P25_FIVE_CONSUMERS_FAILED', json.dumps({'status': state['status'], 'error': state['error'][:1800],
              'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json')}, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
