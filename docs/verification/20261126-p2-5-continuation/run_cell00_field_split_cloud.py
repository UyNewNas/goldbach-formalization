#!/usr/bin/env python3
"""SOURCE ONLY: strictly accept mechanically split FieldDecode owners on P3.

Pass the exact publication commit as argv1. Revalidate and copy eight accepted
base dependencies and the three accepted attempt001 owners; compile none of
them. Preserve their source origins and complete owner receipts unchanged.
The eleven fresh owners partition all 442 original theorem commands verbatim.
Each fresh owner requires normal compilation, kernel replay, and a complete
serialized/environment owner audit before it may be reused. The support audit
also checks all 296 imported private theorems in the activated scoped simp set.
The two failed monolithic Field objects and the progress probe supply no credit.
Reuse the exact accepted current 5312-module external snapshot, validating every
provider, object and companion before/after gates. The three old owners receive
only supplemental replay/full-owned checks under that current snapshot; their
old receipt dictionaries are retained and no historical external hash is invented.
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
BASE = ROOT / '.lake/diagnostic/p25-cell00-canonical-attempt001/charparse'
OUT = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt003'
PRIOR = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt001'
PRIOR_RESULT_SHA = '86afeed917a3361c5457db1b7b3f4546d2e513531288adfab3d3a196ad38eac1'
PRIOR_FAILED_SOURCE_SHA = 'c62cf0315fafe2733393627137963dcb507827c988a49115add3a11422a244ed'
PRIOR_FAILED_NORMAL_LOG_SHA = '4528afb43ddd36cf5825ebfe8fe6a82ca7b200ac4f93fbe18a0d5833e9b02a25'
TARGET = 'ImbalancedChen.P2Saving16Cell00FieldDecode'
RUNNER_REL = 'docs/verification/20261126-p2-5-continuation/run_cell00_field_split_cloud.py'
CURRENT_EXTERNAL = ROOT / '.lake/diagnostic/p25-cell00-remaining-arithmetic-attempt001'
CURRENT_EXTERNAL_PUBLICATION = '5cc2b181f51be2f20ce316256fe2cdf3e691ca69'
CURRENT_EXTERNAL_RESULT_SHA = '1e48fc2e2a45b2e4247ab08597586dae6c8cac3cd9a05788e465b5175d262f7c'
CURRENT_EXTERNAL_SNAPSHOT_SHA = 'b94ab99b39a831a616d626c55c4b89c0a921d15c95319de19063d375bc982728'
CURRENT_EXTERNAL_RUNNER_SHA = '17b4b2193968c061a8bbb31ac0e3043c8cbf4eb2b22ee010a0359a57c8de4918'
EXPECTED_EXTERNAL_COUNT = 5312
SUPPORT = 'ImbalancedChen.P2Saving16Cell00FieldSimp'
SPLIT_PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-field-split')
SPLIT_MANIFEST_SHA = '0296bef555e3ccd90780ce6f31b9b7004d30cc2e93881292e1be9ee008453fd5'
IDENTITY_SHA = '9f33526038f4d7e403cdbf3e422b386af2d861733e743ea0c0a690f66a7c5657'
SCOPED_AUDIT_APPENDIX_SHA = 'ff82f03c8c798556f2ed6e18ce4ed5a035057fa616b55664a105a9b5886aa202'
MONOLITH = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt002'
MONOLITH_RESULT_SHA = '3af403db2e1e5bb09b0e9cd82d23984305e05265a7ee43d9abd4d12d517e2392'
MONOLITH_PUBLICATION = '8fa1d8c84f8c465da8f8fd00bfce1410e1807ae3'
MONOLITH_FIELD_PATH = 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00FieldDecode.lean'
MONOLITH_FIELD_SHA = '3bca40fbe7f5484ce50da650d9c505026e1634f0c0accdcda3dfe93ab5698b96'
EMPTY_SHA = 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
PROGRESS_RESULT_SHA = '35850abf610d8ff3c8be5071414034e5ba47f3958276ed154ec91e12c3b48955'
PROGRESS_NORMAL_SHA = '62e8cb8e43f98fcdc5fd6506198e8324c859db050f42c2d2a1a471be9f20f294'
PROGRESS_MAP_SHA = '6fa615c0419c010aad5b6515b00a532a94678564a51f64337a299e3c136edbcd'
PROGRESS = ROOT / '.lake/diagnostic/p25-field-progress-attempt001'

REUSED_OBJECTS = {
    'ImbalancedChen.P2Saving16Cell00PayloadBinding': 'f1bff7f79f8e43f8a98e5eca39b520b928b46016a297af9272a6cb2b65f065c8',
    'ImbalancedChen.P2OriginalSaving16DecoderCompose': 'df91e32fa010265bb3ad1dba9f317233ce9c1b48beb0c668e5bca70666c452ed',
    'ImbalancedChen.P2Saving16Cell00ScalarDecode': '6a313fad2e0bb6a42a0a73e8f0c5c3360576b10e6de8f34511139711a6e64aeb',
}
PAYLOAD_RESULT_SHA = '090463b93761d31023f39111c32522e1f2bb3cbcec46e606f7fc429d69d4a204'
CHARS_RESULT_SHA = '315bb7c65ca80f821bd109deb226587296e75dca26e9d94d45c92f885e8d92f9'
REPRODUCED = ROOT / '.lake/diagnostic/p25-cell00-decoded-attempt002'
PAYLOAD_RESULT = ROOT / '.lake/diagnostic/p25-payload-floors-attempt001/RESULT.json'
CHARS_RESULT = ROOT / '.lake/diagnostic/p25-decoder-chars-attempt004/RESULT.json'
PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-decoded')
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
OLD_RESULT_SHA = '4dca8c2c7b42feb027895420ddb62e0a314d5f6f440d8b772704eeb146ba37eb'
PAYLOAD_FILES_SHA = '76aa078eef969fa6c8d8270529f3d68f50b4bb6762626ba14a484423bbdc4321'
FUEL_RECEIPT_SHA = '9792af6d5093daf404acebe2a7aeecd0167ff7158ecf07e13b8354c67615e26a'
DIRECT_RECEIPT_SHA = 'a05d2bf89fbf2d57f03d4aa9fae512de96928a38b323bab65bb782520613b8dd'
PAYLOAD = 'ImbalancedChen.P2Saving16Cell00TypedPayload'
CHARS = 'ImbalancedChen.P2OriginalSaving16DecoderChars'
FUEL = 'ImbalancedChen.P2OriginalSaving19SourceJsonFuel'
DIRECT = 'ImbalancedChen.P2Saving16Cell00DirectParse'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
BASE_OBJECTS = {
    'ImbalancedChen.P2OriginalSaving16Decoder':
        'fd25815778e3bae5518d3fcc6a5461724b64251f91c4c08e61312fbae4987b39',
    'ImbalancedChen.P2OriginalSaving16Q96FloorCore':
        '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9',
    'ImbalancedChen.P2OriginalSaving19SourceJson':
        '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7',
    'ImbalancedChen.P2Saving16StringCharBinding00':
        'a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a',
}
REPRODUCED_OBJECTS = {
    FUEL: '9928b1cd0dd91cc93ff2055f00d0d147d455dd8d27783cf110e58df3d61bd088',
    DIRECT: '52cf731b62270e0fdfee8468d813aacfe373853e51035b88c669dd8713393f2a',
}

# Filled from the frozen, inspected source files when this runner is prepared.
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
 'ImbalancedChen.P2Saving16StringCharBinding00': {'path': 'ImbalancedChen/P2Saving16StringCharBinding00.lean',
                                                  'source_sha256': 'd2353e0a96ce78a8ba2da3d3d47f835593dcf758ea6110fd088c82df038f008c',
                                                  'project_imports': []},
 'ImbalancedChen.P2OriginalSaving19SourceJsonFuel': {'path': 'ImbalancedChen/P2OriginalSaving19SourceJsonFuel.lean',
                                                     'source_sha256': '0c98bd29f628bade9657a6828772fa2499c9be8dd2d3b16bfea5cd206405c1e4',
                                                     'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJson']},
 'ImbalancedChen.P2Saving16Cell00DirectParse': {'path': 'ImbalancedChen/P2Saving16Cell00DirectParse.lean',
                                                'source_sha256': 'fa1c92a5fd127b913958a6a10373e8a041433ac74a4a8c36ab06da709356956c',
                                                'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJsonFuel',
                                                                    'ImbalancedChen.P2Saving16StringCharBinding00']},
 'ImbalancedChen.P2Saving16Cell00TypedPayload': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00TypedPayload.lean',
                                                 'source_sha256': 'e92848bd075bf82fe7325bd46e3ddcde937cba277387d46a3579560c27aa287b',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16Decoder']},
 'ImbalancedChen.P2OriginalSaving16DecoderChars': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2OriginalSaving16DecoderChars.lean',
                                                   'source_sha256': '01b1e5cff72305ab75aa1feb7c5574469ddfbd51af40cc012d75464a44473ca5',
                                                   'project_imports': ['ImbalancedChen.P2OriginalSaving16Decoder']},
 'ImbalancedChen.P2Saving16Cell00PayloadBinding': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00PayloadBinding.lean',
                                                   'source_sha256': '61722aa2f8d764fa757245784217e2f9cd9442393333cb594e334b1883425c1b',
                                                   'project_imports': ['ImbalancedChen.P2Saving16Cell00TypedPayload',
                                                                       'ImbalancedChen.P2Saving16Cell00DirectParse']},
 'ImbalancedChen.P2OriginalSaving16DecoderCompose': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2OriginalSaving16DecoderCompose.lean',
                                                     'source_sha256': 'b651fb5defedcee7dea0b0b9beee106a984b8ef59bf27104b579fb453faa7e36',
                                                     'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderChars']},
 'ImbalancedChen.P2Saving16Cell00ScalarDecode': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00ScalarDecode.lean',
                                                 'source_sha256': 'ba4424e7db6a4efdcd88278b80c129e15cb9049e193adbf7f0e95825964bb9f3',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderChars',
                                                                     'ImbalancedChen.P2Saving16Cell00TypedPayload']},
 'ImbalancedChen.P2Saving16Cell00FieldDecode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00FieldDecode.lean',
                                                'source_sha256': 'ce7e0131800eb84b3ab2c8dfd8830aaa0b353475594e91b70906b3d1052e77e2',
                                                'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldBase',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex00Decode',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex01Decode',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex02Decode',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex03Decode',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex04Decode',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex05Decode',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex06Decode',
                                                                    'ImbalancedChen.P2Saving16Cell00Simplex07Decode']},
 'ImbalancedChen.P2Saving16Cell00FieldSimp': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00FieldSimp.lean',
                                              'source_sha256': '1e43f44c0cbc858d505ef968499390bf85c25426d7307d69c833e2f89c455aa4',
                                              'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderCompose',
                                                                  'ImbalancedChen.P2Saving16Cell00ScalarDecode']},
 'ImbalancedChen.P2Saving16Cell00FieldBase': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00FieldBase.lean',
                                              'source_sha256': 'd25a0ddf04a1f56729160274a4bcd8bb306a66018e27d7574b0817df3120f50c',
                                              'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex00Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex00Decode.lean',
                                                    'source_sha256': 'b9d32f760ac1cafe0a4b7a06ef10a9dbcd8f1f8118cde48742880b5f5e6e6f00',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex01Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex01Decode.lean',
                                                    'source_sha256': 'fbf7c016509f67c2f7299823e3c0026027f10e3678c877ff4def3269b4079fde',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex02Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex02Decode.lean',
                                                    'source_sha256': '6cc3aa3e41c4397ad4bd7a9012e4f63a4334b72dd1f90eb977e2f502d4bea277',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex03Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex03Decode.lean',
                                                    'source_sha256': 'a501e0b6b4d46b4ab698b0872e8438402da222206992d95a1d8c04335defad2f',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex04Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex04Decode.lean',
                                                    'source_sha256': '3f3bd0d70ddb6c79bf99cd5c6644523bb7dcc72a5f69c01865f8a4aa1f3c9462',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex05Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex05Decode.lean',
                                                    'source_sha256': 'e87ffb71a5673108985add191e020235065a535f409057a55a7f02866f5313e4',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex06Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex06Decode.lean',
                                                    'source_sha256': 'edffc47a38f8b601f1edc58d33776666665c9e70813ae654553f2e86d0eac054',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']},
 'ImbalancedChen.P2Saving16Cell00Simplex07Decode': {'path': 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00Simplex07Decode.lean',
                                                    'source_sha256': 'b4873475f8cbff43fddb7eb88451b704bc4156d602fd47c6b62e8834ea2c906f',
                                                    'project_imports': ['ImbalancedChen.P2Saving16Cell00FieldSimp']}}
MODULES = [{'module': 'ImbalancedChen.P2Saving16Cell00PayloadBinding',
  'namespace': 'ImbalancedChen.P2Saving16Cell00PayloadBinding',
  'public_count': 1,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00PayloadBinding.rootValue_eq_rawRoot'},
 {'module': 'ImbalancedChen.P2OriginalSaving16DecoderCompose',
  'namespace': 'ImbalancedChen.P2OriginalSaving16OriginalArchive',
  'public_count': 6,
  'required_final_name': 'ImbalancedChen.P2OriginalSaving16OriginalArchive.decodeArray_arr'},
 {'module': 'ImbalancedChen.P2Saving16Cell00ScalarDecode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00ScalarDecode',
  'public_count': 227,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00ScalarDecode.integer015_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00FieldSimp',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 0,
  'public_names': [],
  'private_theorem_commands': 296,
  'required_final_name': None},
 {'module': 'ImbalancedChen.P2Saving16Cell00FieldBase',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 54,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_dimension',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_physical_jacobian',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_cell_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_left_masks',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_right_masks',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_facet_original_indices',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_positive_normal_balance',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_normal_rank',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_active8_enumeration',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_vertices',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_vertex_values',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_all_original_constraint_minima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_facet_vertices',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_face_ledger',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_simplices',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.lookup_integral_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.cellId_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.cellId_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.dimension_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.dimension_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.physicalJacobian_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.physicalJacobian_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.leftMasks_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.leftMasks_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.rightMasks_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.rightMasks_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.facetOriginalIndices_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.facetOriginalIndices_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.normalRank_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.normalRank_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.facetVertices_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.facetVertices_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.positiveNormalBalance_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.positiveNormalBalance_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.allOriginalMinima_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.allOriginalMinima_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex00_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex01_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex02_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex03_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex04_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex05_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex06_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex07_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex08_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex09_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex10_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex11_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex12_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex13_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex14_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertex15_decoded',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.vertices_mapped'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.vertices_mapped'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex00Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex00_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex01Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex01_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex02Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex02_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex03Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex03_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex04Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex04_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex05Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex05_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex06Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex06_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00Simplex07Decode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 11,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_simplex_id',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_vertex_ids',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_physical_volume',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_mean_gap',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_factor_maxima',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_gap_weighted_means',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_max_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_jensen_bound',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_max_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_lookup_jensen_floor_Q96',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.simplex07_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 4,
  'public_names': ['ImbalancedChen.P2Saving16Cell00FieldDecode.simplices_mapped',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.physicalVolume_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.integralGap_field',
                   'ImbalancedChen.P2Saving16Cell00FieldDecode.rawRoot_decoded'],
  'private_theorem_commands': 0,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.rawRoot_decoded'}]


FRESH_SPECS = MODULES[3:]
FRESH_MODULES = [s['module'] for s in FRESH_SPECS]


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
    seen = set()

    def visit(name):
        if name in seen:
            return
        require(name in SOURCES, f'Unspecified project dependency: {name}')
        seen.add(name)
        for imported in SOURCES[name]['project_imports']:
            visit(imported)

    visit(module)
    return seen


def audited_imports(log):
    values = [json.loads(line.removeprefix('P0_QUEUE_IMPORTS '))
              for line in Path(log).read_text().splitlines() if line.startswith('P0_QUEUE_IMPORTS ')]
    require(len(values) == 1 and len(values[0]) == len(set(values[0])),
            'Missing or duplicate audited import inventory.')
    return values[0]


def read_audit(log, module):
    lines = log.read_text().splitlines()
    records = [json.loads(s.removeprefix('P0_QUEUE_DECL ')) for s in lines if s.startswith('P0_QUEUE_DECL ')]
    inventories = [json.loads(s.removeprefix('P0_QUEUE_INVENTORY ')) for s in lines if s.startswith('P0_QUEUE_INVENTORY ')]
    imports = [json.loads(s.removeprefix('P0_QUEUE_IMPORTS ')) for s in lines if s.startswith('P0_QUEUE_IMPORTS ')]
    names = sorted(r['name'] for r in records)
    require(len(inventories) == len(imports) == 1 and inventories[0]['module'] == module,
            f'Missing or duplicate full audit inventory: {module}')
    require(names and len(names) == len(set(names)) and
            names == sorted(inventories[0]['serialized']) == sorted(inventories[0]['environment']),
            f'Complete serialized/environment/declaration inventory mismatch: {module}')
    require(all(r['module'] == module and not any(r[k] for k in ['unsafe', 'partial', 'axiom']) and
                set(r['axioms']) <= ALLOWED_AXIOMS for r in records),
            f'Unsafe/partial/axiom or forbidden transitive axiom: {module}')
    actual = {m for m in imports[0] if m.startswith('ImbalancedChen.')}
    require(actual == project_closure(module), f'Unexpected actual project imports for {module}: {sorted(actual)}')
    return records, inventories[0], sorted(actual)


def theorem_commands(text):
    """Extract the frozen source's paragraph-sized theorem commands exactly."""
    result = []
    for match in re.finditer(r'^(private )?theorem ([A-Za-z0-9_]+)\b', text, re.M):
        end = text.index('\n\n', match.start())
        command = text[match.start():end]
        result.append({'name': match.group(2), 'private': bool(match.group(1)),
                       'command': command,
                       'command_sha256': hashlib.sha256(command.encode()).hexdigest()})
    return result


def verify_split_identity(manifest, identity):
    require(manifest['schema'] == 'p25-cell00-field-owner-split-v1' and
            manifest['new_owner_count'] == 11 and
            manifest['original_public_commands'] == 146 and
            manifest['original_private_commands'] == 296 and
            manifest['original_publication'] == MONOLITH_PUBLICATION and
            manifest['original_source'] == {'path': MONOLITH_FIELD_PATH, 'sha256': MONOLITH_FIELD_SHA} and
            manifest['actual_failure']['result_sha256'] == MONOLITH_RESULT_SHA and
            manifest['bounded_progress']['result_sha256'] == PROGRESS_RESULT_SHA and
            manifest['field_decode_proved'] is False and manifest['P2_5_proved'] is False,
            'Split manifest scope/source/failure evidence differs.')
    require(manifest['command_identity'] == {
                'path': str(SPLIT_PACKAGE / 'COMMAND_IDENTITY.json'), 'sha256': IDENTITY_SHA} and
            identity['all_original_theorem_commands_byte_identical'] is True and
            identity['count'] == 442 and identity['public_count'] == 146 and identity['private_count'] == 296,
            'Split command identity manifest differs.')
    original_text = (ROOT / MONOLITH_FIELD_PATH).read_text()
    original = theorem_commands(original_text)
    require(len(original) == 442 and len({r['name'] for r in original}) == 442 and
            sum(r['private'] for r in original) == 296,
            'Original frozen theorem inventory is not 296 private plus 146 public commands.')
    actual = []
    original_by_name = {r['name']: r for r in original}
    require([r['module'] for r in manifest['modules']] == FRESH_MODULES,
            'Split owner order differs.')
    for row, spec in zip(manifest['modules'], FRESH_SPECS):
        module = spec['module']
        path = ROOT / SOURCES[module]['path']
        require(row['path'] == SOURCES[module]['path'] and
                row['sha256'] == SOURCES[module]['source_sha256'] and
                row['bytes'] == path.stat().st_size and
                row['project_imports'] == SOURCES[module]['project_imports'] and
                row['public_namespace'] == spec['namespace'] and
                row['public_names'] == spec['public_names'] and
                row['public_count'] == spec['public_count'] and
                row['private_theorem_commands'] == spec['private_theorem_commands'] and
                row['required_final_name'] == spec['required_final_name'],
                f'Split owner metadata differs: {module}')
        text = path.read_text()
        require(not re.search(r'^module\b', text, re.M),
                'Private scoped simp transport requires the reviewed legacy importAll mode.')
        commands = theorem_commands(text)
        require(sum(r['private'] for r in commands) == spec['private_theorem_commands'] and
                [spec['namespace'] + '.' + r['name'] for r in commands if not r['private']] == spec['public_names'],
                f'Split public/private theorem partition differs: {module}')
        if module == SUPPORT:
            first_public = next(re.finditer(r'^theorem ', original_text, re.M)).start()
            old_attributes = re.findall(r'^attribute \[local simp\] .*$', original_text[:first_public], re.M)
            new_attributes = re.findall(r'^attribute \[scoped simp\] .*$', text, re.M)
            require(new_attributes == [a.replace('[local simp]', '[scoped simp]') for a in old_attributes] and
                    'open scoped' not in text and not re.search(r'^attribute \[local simp\]', text, re.M),
                    'Support attributes differ by more than the reviewed local-to-scoped transport.')
        else:
            require(text.count('open scoped ImbalancedChen.P2Saving16Cell00FieldDecode') == 1,
                    f'Consuming owner does not activate the private simp scope exactly once: {module}')
        for command in commands:
            name = command['name']
            require(name in original_by_name and command == original_by_name[name],
                    f'Original theorem command changed: {module}/{name}')
            if not command['private']:
                require(text.count('\nattribute [local simp] ' + name + '\n') == 1,
                        f'Original local theorem attribute missing or duplicated: {module}/{name}')
            actual.append({'name': name, 'module': module, 'private': command['private'],
                           'command_sha256': command['command_sha256']})
    require(actual == identity['commands'] and
            [r['name'] for r in actual] == [r['name'] for r in original],
            'The 442 source commands were not partitioned exactly once in original order.')
    final = (ROOT / SOURCES[TARGET]['path']).read_text()
    final_registration = re.findall(r'^attribute \[local simp\] (.+)$', final, re.M)[0].split()
    expected_registration = [n.rsplit('.', 1)[1] for n in FRESH_SPECS[1]['public_names']] + [
        f'simplex{i:02d}_decoded' for i in range(8)]
    require(final_registration == expected_registration and len(final_registration) == 62,
            'Final owner must register exactly 54 Base equations and eight complete simplex equations.')
    return {'original_commands': 442, 'public_commands': 146, 'private_commands': 296,
            'all_commands_byte_identical': True, 'new_owner_count': 11,
            'all_legacy_import_all': True, 'final_imported_simp_equations': 62,
            'private_user_names': [FRESH_SPECS[0]['namespace'] + '.' + r['name']
                                   for r in original if r['private']]}


def read_private_scope_audit(log, records, required):
    marker = 'P25_PRIVATE_SCOPED_SIMP_INTERFACE '
    lines = [json.loads(s.removeprefix(marker)) for s in log.read_text().splitlines() if s.startswith(marker)]
    require(len(lines) == 1, 'Missing or duplicate imported private scoped-simp interface audit.')
    row = lines[0]
    matches = row['matches']
    require(row['module'] == SUPPORT and row['scope'] == FRESH_SPECS[0]['namespace'] and
            row['required_count'] == row['matched_count'] == len(matches) == len(required) == 296 and
            [r['user_name'] for r in matches] == required and
            len({r['actual_name'] for r in matches}) == 296,
            'Private scoped-simp interface inventory differs.')
    owned = {r['name'] for r in records}
    for match in matches:
        candidates = [name for name in owned if name.endswith('.' + match['user_name'])]
        require(candidates == [match['actual_name']] and match['actual_name'].startswith('_private.'),
                'Scoped-simp name is not the unique actual private declaration in the full owned audit.')
    return row


def main():
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]),
            'Pass exactly one full lowercase 40-hex publication commit.')
    publication = sys.argv[1]
    require(ROOT.is_dir(), 'Expected P3 checkout is missing.')
    require(not OUT.exists(), f'Preserve prior attempt: {OUT}')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 worktree is dirty.')
    OUT.mkdir()
    state = {
        'schema': 'p25-cell00-field-split-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
        'module_order': FRESH_MODULES, 'modules': {},
        'original_theorem_commands_byte_identical': False, 'private_scoped_simp_interface_checked': False,
        'additional_reuse_validations': {}, 'old_owner_normal_recompilations': [],
        'complete_external_after_matches_before': False, 'historical_missing_external_hashes_invented': False,
        'reused_module_order': list(REUSED_OBJECTS), 'reused_owner_objects': {}, 'owner_receipt_sources': {},
        'reused_owners_recompiled': [], 'failed_same_name_field_object_used': False,
        'dependency_modules_compiled': [], 'dependency_objects': {}, 'dependency_receipts': {},
        'private_records_written': [], 'original_cell00_sha256': INPUT_SHA,
        'failed_owner_object_used': False, 'host_correctness_credit': False,
        'certified_reader_ast_binding_proved': False, 'raw_root_typed_decode_proved': False,
        'original_string_typed_decode_proved': False, 'geometric_jensen_binding_proved': False,
        'Q96_proved': False, 'P2_5_proved': False,
    }
    frozen = {}
    external_entries = []
    expected_external = set()
    providers = []

    def write():
        temp = OUT / 'RESULT.tmp'
        temp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
        temp.replace(OUT / 'RESULT.json')

    def bind(path, expected=None):
        path = Path(path)
        actual = digest(path)
        require(expected is None or actual == expected, f'Frozen artifact hash mismatch: {path}')
        require(str(path) not in frozen or frozen[str(path)] == actual, f'Artifact changed during preflight: {path}')
        frozen[str(path)] = actual
        return path

    def artifact(row, expected=None):
        path = bind(row['path'], expected or row['sha256'])
        require(digest(path) == row['sha256'], f'Artifact record hash mismatch: {path}')
        require(path.stat().st_size == row['bytes'], f'Artifact byte count mismatch: {path}')
        return path

    def check_frozen():
        require(all(digest(p) == h for p, h in frozen.items()), 'A frozen source/object/log/receipt/runtime changed.')

    def external_resolutions():
        require(len(external_entries) == len(expected_external) == EXPECTED_EXTERNAL_COUNT,
                'The complete current external context has not been initialized.')
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
                not git('status', '--porcelain', '--untracked-files=no'),
                'Selected source publication changed during compiler gates.')
        require(git('rev-parse', 'HEAD', cwd=Path(state['runtime']['mathlib_path'])) == MATHLIB_PIN,
                'Mathlib source pin changed during compiler gates.')
        external_resolutions()
        check_frozen()

    def stage_log(row, override=None):
        require(row['exit_code'] == 0 and not row.get('timed_out', False), 'Dependency stage did not pass.')
        path = Path(override) if override is not None else Path(row['log'])
        if not path.is_absolute():
            path = ROOT / path
        return bind(path, row['log_sha256'])

    def copy_dependency(module, original, expected, provenance):
        require(module in SOURCES and module != TARGET and module not in state['dependency_objects'],
                f'Unknown, failed-target or duplicate dependency source: {module}')
        original = bind(original, expected)
        destination = lib / (module.replace('.', '/') + '.olean')
        require(not destination.exists(), f'Dependency copy target already exists: {module}')
        shutil.copyfile(original, destination)
        bind(destination, expected)
        state['dependency_objects'][module] = {
            'path': str(original), 'sha256': expected, 'isolated_path': str(destination),
            'source_sha256': SOURCES[module]['source_sha256'], 'provenance': provenance,
        }

    def verify_component(receipt_path, receipt, module):
        bind(receipt_path)
        owner = receipt['modules'][module]
        require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                f'Required future owner is not accepted: {module}')
        require(owner['module'] == module and owner['source_origin']['sha256'] == SOURCES[module]['source_sha256'],
                f'Accepted future source identity mismatch: {module}')
        require(owner['source_origin']['commit'] == receipt['publication_commit'] and
                owner['source_origin']['path'] == SOURCES[module]['path'],
                f'Accepted future publication/path binding mismatch: {module}')
        source_copy = artifact(owner['source_copy'], SOURCES[module]['source_sha256'])
        audit_source = artifact(owner['audit_source'])
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, module),
                f'Accepted owner used a different complete-audit template: {module}')
        object_path = artifact(owner['object'])
        for label in ['normal', 'replay', 'audit']:
            stage = owner['stages'][label]
            require(stage['status'] == 'PASSED', f'Accepted owner stage is not marked passed: {module}/{label}')
            stage_log(stage)
            command = stage['command']
            if label == 'replay':
                require(command == [str(CHECKER), '--verbose', module], f'Unexpected accepted replay command: {module}')
            else:
                require(command[0] == str(LEAN) and all(f in command for f in ['-t0', '-j1', '-M11264', '-DwarningAsError=true']),
                        f'Accepted owner was not compiled/audited with strict flags: {module}/{label}')
        normal_command = owner['stages']['normal']['command']
        require(Path(normal_command[-1]) == source_copy and
                Path(normal_command[normal_command.index('-o') + 1]) == object_path,
                f'Accepted normal command does not bind this source/object pair: {module}')
        require(Path(owner['stages']['audit']['command'][-1]) == audit_source,
                f'Accepted audit command/source mismatch: {module}')
        records, inventory, imports = read_audit(Path(owner['stages']['audit']['log']), module)
        require(records == owner['owned_declarations'] and len(records) == owner['owned_count'],
                f'Accepted owner declaration receipt differs from actual audit log: {module}')
        require(json.loads(artifact(owner['declarations']).read_text()) == records and
                json.loads(artifact(owner['inventory']).read_text()) == inventory,
                f'Accepted owner inventory/declaration file mismatch: {module}')
        require(owner['actual_project_closure'] == imports, f'Accepted import closure receipt mismatch: {module}')
        if module == PAYLOAD:
            require(sorted(r['name'] for r in records) == expected_payload, 'Accepted payload is not all 544 expected declarations.')
            require(owner['object']['sha256'] == '1c61948df2571b065f3b27ae2eeeff1202b942e39bb16229f93c9cc40b1e8c75',
                    'Accepted payload object identity differs.')
        elif module == CHARS:
            required = {'ImbalancedChen.P2OriginalSaving16OriginalArchive.' + n
                        for n in ['parseInteger_ofList', 'parseRational_ofList', 'decodeNat_number_ofList']}
            require(required <= {r['name'] for r in records}, 'Accepted Chars public equations are incomplete.')
            require(owner['object']['sha256'] == 'af720770a2f637e468c1f153b76891e0c6efedd627d3d144ca20024e638a1c7d',
                    'Accepted Chars object identity differs.')
        else:
            require(module in REUSED_OBJECTS and owner['object']['sha256'] == REUSED_OBJECTS[module],
                    'Only one of the three exact prior accepted owners may be reused.')
            spec = next(s for s in MODULES if s['module'] == module)
            public = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)',
                                source_copy.read_text(), re.M)
            required = [spec['namespace'] + '.' + n for n in public]
            require(len(public) == len(set(public)) == spec['public_count'] == owner['owned_count'] and
                    owner['required_owned_names'] == required and spec['required_final_name'] in required and
                    set(required) <= {r['name'] for r in records},
                    'Prior accepted owner public/full declaration inventory differs.')
        for dependency in project_closure(module) - {module}:
            require(dependency in state['dependency_objects'], f'Accepted dependency not yet present: {dependency}')
            expected = state['dependency_objects'][dependency]['sha256']
            row = receipt['dependency_objects'][dependency]
            require(row['sha256'] == expected and
                    row['source_sha256'] == SOURCES[dependency]['source_sha256'],
                    f'Accepted owner dependency binding mismatch: {dependency}')
            bind(row['path'], expected)
            bind(row['isolated_path'], expected)
        copy_dependency(module, object_path, owner['object']['sha256'],
                        'Accepted owner entry with normal/replay/full-owned logs and complete inventory revalidated')
        state['dependency_receipts'][module] = {
            **record_file(receipt_path), 'owner_status': owner['status'], 'owner_accepted': True,
            'aggregate_status': receipt['status'], 'aggregate_accepted': receipt['accepted'],
            'owned_count': len(records), 'source_origin': owner['source_origin'],
        }

    def verify_reproduced_original_acceptance():
        # Bind the original local acceptance packages, not the failed Decoded owner.
        fuel_dir = ROOT / 'docs/verification/20261126-p2-5-continuation/fuel_stability'
        fuel_receipt_path = bind(fuel_dir / 'verification.json', FUEL_RECEIPT_SHA)
        fuel_receipt = json.loads(fuel_receipt_path.read_text())
        require(fuel_receipt['module'] == FUEL and fuel_receipt['status'] == 'passed' and
                fuel_receipt['source_sha256'] == SOURCES[FUEL]['source_sha256'] and
                fuel_receipt['object_sha256'] == REPRODUCED_OBJECTS[FUEL] and
                fuel_receipt['inputs_unchanged'] is True and
                fuel_receipt['full_owned_declarations_all_safe_total_nonaxiom'] is True,
                'Original Fuel acceptance receipt is incomplete or mismatched.')
        require([s['label'] for s in fuel_receipt['stages']] == ['strict-compile', 'replay', 'full-owned-audit'],
                'Fuel acceptance stages differ.')
        for row in fuel_receipt['stages']:
            stage_log(row, fuel_dir / Path(row['log']).name)
        fuel_records, _, _ = read_audit(fuel_dir / 'full-owned-audit.log', FUEL)
        require(len(fuel_records) == fuel_receipt['full_owned_declaration_count'], 'Fuel owned-count mismatch.')
        direct_dir = ROOT / 'docs/source-only/20261126-p2-5-cell00-segmented'
        direct_receipt_path = bind(direct_dir / 'RESULT.json', DIRECT_RECEIPT_SHA)
        direct_receipt = json.loads(direct_receipt_path.read_text())
        entries = [r for r in direct_receipt['modules'] if r['module'] == DIRECT]
        require(len(entries) == 1, 'DirectParse acceptance owner is absent or duplicated.')
        entry = entries[0]
        require(entry['accepted_local_strict_replay_full_owned'] is True and
                entry['source_sha256'] == SOURCES[DIRECT]['source_sha256'] and
                entry['object_sha256'] == REPRODUCED_OBJECTS[DIRECT], 'DirectParse original acceptance mismatch.')
        require([s['mode'] for s in entry['stages']] == ['normal', 'kernel', 'audit'], 'DirectParse acceptance stages differ.')
        for stage in entry['stages']:
            path = bind(direct_dir / stage['receipt'], stage['receipt_sha256'])
            row = json.loads(path.read_text())
            require(row['module'] == DIRECT and row['mode'] == stage['mode'] and row['exit_code'] == 0 and
                    row['termination_reason'] is None and row['source_sha256'] == SOURCES[DIRECT]['source_sha256'] and
                    row['object_sha256'] == REPRODUCED_OBJECTS[DIRECT], 'DirectParse original stage binding mismatch.')
            bind(path.with_suffix('.log'), row['log_sha256'])
            if stage['mode'] == 'audit':
                require(row['audit_passed'] and row['inventory_complete'] and row['all_safe_total_nonaxiom'],
                        'DirectParse original full-owned audit was not accepted.')
                records, _, _ = read_audit(path.with_suffix('.log'), DIRECT)
                require(len(records) == row['full_owned_count'] == entry['declaration_count'], 'DirectParse inventory count mismatch.')
                bind(path.with_suffix('.lean'), row['audit_source_sha256'])
        state['original_reproduced_acceptance'] = {
            FUEL: record_file(fuel_receipt_path), DIRECT: record_file(direct_receipt_path)}

    def run_stage(owner, label, command, log):
        require(owner['module'] in FRESH_MODULES or
                owner['module'] in REUSED_OBJECTS and label in {'replay', 'audit'} and
                owner.get('normal_recompiled') is False,
                'Only fresh owner gates or explicitly supplemental old-owner replay/audit are permitted.')
        context_check()
        start = time.monotonic()
        row = {'command': command, 'started_utc': now(), 'status': 'RUNNING', 'log': str(log)}
        owner['stages'][label] = row
        write()
        print('P25_FIELD_DECODE_STAGE_START', owner['module'], label, flush=True)
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
        print('P25_FIELD_DECODE_STAGE_RESULT', owner['module'], label,
              json.dumps({k: row[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}), flush=True)
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=owner['module'], failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{owner["module"]} {label} failed with exit {code}.')
        bind(log)
        state['frozen_inputs'] = dict(frozen)
        context_check()

    write()
    try:
        prior_path = bind(PRIOR / 'RESULT.json', PRIOR_RESULT_SHA)
        prior_run = json.loads(prior_path.read_text())
        require(prior_run['schema'] == 'p25-cell00-field-decode-strict-v1' and
                prior_run['accepted'] is False and prior_run['status'] == 'MODULE_STAGE_FAILED' and
                prior_run['failed_module'] == TARGET and prior_run['failed_stage'] == 'normal' and
                set(prior_run['modules']) == {*REUSED_OBJECTS, TARGET} and
                prior_run['dependency_modules_compiled'] == [] and prior_run['failed_owner_object_used'] is False and
                re.fullmatch(r'[0-9a-f]{40}', prior_run['publication_commit']),
                'Expected exact failed attempt001 aggregate with three accepted owners.')
        failed_owner = prior_run['modules'][TARGET]
        require(failed_owner['accepted'] is False and failed_owner['status'] == 'NORMAL_FAILED' and
                failed_owner['source_origin']['sha256'] == PRIOR_FAILED_SOURCE_SHA and
                failed_owner['source_origin']['commit'] == prior_run['publication_commit'] and
                failed_owner['source_origin']['path'] == MONOLITH_FIELD_PATH and
                failed_owner['stages']['normal']['exit_code'] != 0 and
                failed_owner['stages']['normal']['log_sha256'] == PRIOR_FAILED_NORMAL_LOG_SHA and
                failed_owner['stages']['normal']['log_bytes'] == 58970,
                'Prior failed FieldDecode evidence differs; no same-name owner fallback is permitted.')
        old_failed_source = artifact(failed_owner['source_copy'], PRIOR_FAILED_SOURCE_SHA)
        old_failed_log = bind(failed_owner['stages']['normal']['log'], PRIOR_FAILED_NORMAL_LOG_SHA)
        require(old_failed_log.stat().st_size == 58970, 'Prior full diagnostic log is incomplete.')
        for module in REUSED_OBJECTS:
            owner = prior_run['modules'][module]
            require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
                    owner['object']['sha256'] == REUSED_OBJECTS[module],
                    f'Prior owner is not the exact accepted reusable object: {module}')
        state['prior_attempt'] = {
            **record_file(prior_path), 'status': prior_run['status'], 'accepted': False,
            'publication_commit': prior_run['publication_commit'], 'failed_module': TARGET,
            'failed_source_copy': record_file(old_failed_source), 'full_failed_normal_log': record_file(old_failed_log),
            'failed_owner_reused': False,
        }
        monolith_path = bind(MONOLITH / 'RESULT.json', MONOLITH_RESULT_SHA)
        monolith_run = json.loads(monolith_path.read_text())
        require(monolith_run['schema'] == 'p25-cell00-field-decode-retry-strict-v1' and
                monolith_run['status'] == 'MODULE_STAGE_FAILED' and monolith_run['accepted'] is False and
                monolith_run['publication_commit'] == MONOLITH_PUBLICATION and
                monolith_run['failed_module'] == TARGET and monolith_run['failed_stage'] == 'normal' and
                monolith_run['module_order'] == [TARGET] and
                set(monolith_run['modules']) == {*REUSED_OBJECTS, TARGET} and
                monolith_run['dependency_modules_compiled'] == [] and
                monolith_run['reused_owners_recompiled'] == [] and
                monolith_run['failed_same_name_field_object_used'] is False,
                'Expected exact timeout of the frozen 442-command monolith.')
        monolith_owner = monolith_run['modules'][TARGET]
        normal = monolith_owner['stages']['normal']
        require(monolith_owner['accepted'] is False and monolith_owner['status'] == 'NORMAL_FAILED' and
                monolith_owner['source_origin'] == {
                    'commit': MONOLITH_PUBLICATION, 'path': MONOLITH_FIELD_PATH, 'sha256': MONOLITH_FIELD_SHA} and
                set(monolith_owner['stages']) == {'normal'} and normal['exit_code'] == 124 and
                normal['timed_out'] is True and normal['seconds'] == 600.572 and
                normal['log_bytes'] == 0 and normal['log_sha256'] == EMPTY_SHA and
                'object' not in monolith_owner,
                'Monolith timeout evidence differs; no failed Field object can be reused.')
        monolith_source = artifact(monolith_owner['source_copy'], MONOLITH_FIELD_SHA)
        monolith_log = bind(normal['log'], EMPTY_SHA)
        require(monolith_log.stat().st_size == 0 and
                all(monolith_run['modules'][m] == prior_run['modules'][m] for m in REUSED_OBJECTS),
                'Monolith timeout or reused original owner receipts were changed.')
        state['prior_monolith_attempt'] = {
            **record_file(monolith_path), 'status': monolith_run['status'], 'accepted': False,
            'publication_commit': MONOLITH_PUBLICATION, 'failed_module': TARGET,
            'failed_source_copy': record_file(monolith_source), 'full_failed_normal_log': record_file(monolith_log),
            'classification': 'Observed normal-stage timeout without a reported Lean error; no proof-gap conclusion',
            'failed_owner_reused': False,
        }
        # Missing/pending future owners fail here before compilation or checkout.
        future = {}
        for path, module, receipt_sha in [(PAYLOAD_RESULT, PAYLOAD, PAYLOAD_RESULT_SHA),
                                          (CHARS_RESULT, CHARS, CHARS_RESULT_SHA)]:
            receipt = json.loads(bind(path, receipt_sha).read_text())
            owner = receipt['modules'][module]
            require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                    f'Preflight requires accepted {module}; no failed/pending object fallback.')
            require(re.fullmatch(r'[0-9a-f]{40}', receipt['publication_commit']), 'Invalid dependency publication commit.')
            future[module] = receipt
        initial_head = git('rev-parse', 'HEAD')
        if initial_head != publication:
            with (OUT / 'PUBLICATION.log').open('wb') as stream:
                subprocess.run(['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false',
                                'fetch', '--no-tags', 'origin', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
                ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', initial_head, publication],
                                          cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, timeout=120)
                require(ancestor.returncode == 0,
                        'Current clean P3 HEAD is not an ancestor of the selected exact publication.')
                subprocess.run(['git', 'checkout', '--detach', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
        state['initial_checkout'] = {'commit': initial_head, 'ancestor_of_selected_publication': True}
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Publication checkout mismatch/dirty.')
        state['publication_checked_out'] = publication
        runner_path = Path(__file__).resolve()
        published_runner = subprocess.check_output(['git', 'show', publication + ':' + RUNNER_REL],
                                                   cwd=ROOT, timeout=120)
        require(runner_path.read_bytes() == published_runner and
                digest(runner_path) == state['runner']['sha256'],
                'The exact executing runner bytes are not the selected published runner.')
        bind(runner_path, state['runner']['sha256'])
        state['runner_publication_binding'] = {
            'commit': publication, 'path': RUNNER_REL,
            'sha256': hashlib.sha256(published_runner).hexdigest(), 'executed_path': str(runner_path),
        }
        old_path = bind(BASE / 'RESULT.json', OLD_RESULT_SHA)
        old = json.loads(old_path.read_text())
        snapshot = old['normal_snapshot_before']
        require(snapshot['mathlib_pin'] == MATHLIB_PIN and
                git('rev-parse', 'HEAD', cwd=Path(snapshot['mathlib_path'])) == MATHLIB_PIN, 'Mathlib pin mismatch.')
        for binary in [LEAN, CHECKER]:
            bind(binary, snapshot['files'][str(binary)]['sha256'])
        state['runtime'] = {'lean': record_file(LEAN), 'leanchecker': record_file(CHECKER),
                            'mathlib_pin': MATHLIB_PIN, 'mathlib_path': snapshot['mathlib_path']}
        require(prior_run['runtime'] == monolith_run['runtime'] == state['runtime'],
                'Prior accepted owners or failed monolith used a different runtime.')
        state['canonical_dependency_receipt_source'] = record_file(old_path)
        state['prior_charparse_status'] = old['status']
        src, lib, audit = OUT / 'src', OUT / 'lib', OUT / 'audit'
        for directory in [src / 'ImbalancedChen', lib / 'ImbalancedChen', audit]:
            directory.mkdir(parents=True)
        tails = old['approved_LEAN_PATH'].split(':')[1:]
        require(tails and all(p and Path(p).is_dir() and
                             Path(p).resolve().is_relative_to(Path('/mathlib').resolve()) and
                             not (Path(p) / 'ImbalancedChen').exists() for p in tails),
                'Pinned Mathlib paths missing or contain project fallback modules.')
        env = dict(os.environ)
        env.pop('LEAN_SRC_PATH', None)
        env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
        env['LEAN_PATH'] = ':'.join([str(lib), *tails])
        env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')
        state.update(approved_LEAN_PATH=env['LEAN_PATH'], isolated_library=str(lib), isolated_source_root=str(src))

        # Bind all project source hashes and verify the explicit import graph.
        for module, spec in SOURCES.items():
            path = bind(ROOT / spec['path'], spec['source_sha256'])
            published = subprocess.check_output(['git', 'show', f'{publication}:{spec["path"]}'], cwd=ROOT, timeout=120)
            require(published == path.read_bytes(), f'Project source differs from exact publication: {module}')
            imports = [name for line in re.findall(r'^import\s+([^\n]+)$', path.read_text(), re.M)
                       for name in line.split() if name.startswith('ImbalancedChen.')]
            require(imports == spec['project_imports'], f'Frozen source import graph mismatch: {module}')
        state['source_graph'] = SOURCES
        state['expected_project_imports_by_owner'] = {s['module']: sorted(project_closure(s['module'])) for s in MODULES}
        # The old c62 monolith remains preserved in attempt001's source copy.
        # Its published path now holds the frozen 3bca monolith from attempt002;
        # the new split owners are additive paths and do not edit that monolith.
        superseded = ROOT / MONOLITH_FIELD_PATH
        require(prior_run['frozen_inputs'].get(str(superseded)) == PRIOR_FAILED_SOURCE_SHA,
                'The old frozen source map does not contain the expected failed target.')
        for path, h in prior_run['frozen_inputs'].items():
            if Path(path) == superseded:
                continue
            require(Path(path) != PRIOR / 'lib' / (TARGET.replace('.', '/') + '.olean'),
                    'A failed target object unexpectedly appears in the prior_run frozen proof inputs.')
            bind(path, h)
        state['superseded_failed_source'] = {
            'path': str(superseded), 'old_sha256': PRIOR_FAILED_SOURCE_SHA,
            'new_sha256': MONOLITH_FIELD_SHA,
            'preserved_old_copy': record_file(old_failed_source),
            'reason': 'Original c62 source copy preserved; published 3bca monolith stays unchanged while split owners use additive paths.',
        }

        bind(superseded, MONOLITH_FIELD_SHA)
        for path, h in monolith_run['frozen_inputs'].items():
            require(Path(path) != MONOLITH / 'lib' / (TARGET.replace('.', '/') + '.olean'),
                    'A failed monolith object unexpectedly appears in frozen proof inputs.')
            bind(path, h)
        state['preserved_monolith_frozen_inputs'] = len(monolith_run['frozen_inputs'])
        progress_result = bind(PROGRESS / 'RESULT.json', PROGRESS_RESULT_SHA)
        progress_normal = bind(PROGRESS / 'NORMAL.log', PROGRESS_NORMAL_SHA)
        progress_map = bind(PROGRESS / 'PROGRESS_MAP.json', PROGRESS_MAP_SHA)
        progress_run = json.loads(progress_result.read_text())
        require(progress_run['schema'] == 'p25-bounded-field-progress-v1' and
                progress_run['accepted'] is False and progress_run['formal_credit'] is False and
                progress_run['diagnostic_only'] is True and progress_run['timed_out'] is True and
                progress_run['seconds'] == 90.223 and progress_run['last_marker'] == 900393 and
                progress_run['next_command_at_last_marker']['name'] == 'simplex03_decoded' and
                progress_run['dependency_modules_compiled'] == [] and
                progress_run['prior_result_sha256'] == MONOLITH_RESULT_SHA,
                'Bounded progress evidence differs; it is diagnostic only.')
        state['bounded_progress_evidence'] = {
            'result': record_file(progress_result), 'normal_log': record_file(progress_normal),
            'progress_map': record_file(progress_map), 'formal_acceptance': False,
            'interpretation': 'Declaration boundary progress only; async prior proofs and eventual final hotspot not established',
        }
        split_manifest_path = bind(ROOT / SPLIT_PACKAGE / 'MANIFEST.json', SPLIT_MANIFEST_SHA)
        split_manifest = json.loads(split_manifest_path.read_text())
        identity_path = bind(ROOT / SPLIT_PACKAGE / 'COMMAND_IDENTITY.json', IDENTITY_SHA)
        identity = json.loads(identity_path.read_text())
        appendix_path = bind(ROOT / SPLIT_PACKAGE / 'PRIVATE_SCOPED_SIMP_AUDIT_APPENDIX.lean', SCOPED_AUDIT_APPENDIX_SHA)
        appendix_record = split_manifest['scoped_simp_interface_audit_appendix']
        require(appendix_record['path'] == str(SPLIT_PACKAGE / appendix_path.name) and
                appendix_record['sha256'] == SCOPED_AUDIT_APPENDIX_SHA and
                appendix_record['bytes'] == appendix_path.stat().st_size and
                appendix_record['expected_private_count'] == 296,
                'Private scoped-simp audit appendix manifest differs.')
        for path in [split_manifest_path, identity_path, appendix_path, superseded]:
            relative = str(path.relative_to(ROOT))
            published = subprocess.check_output(['git', 'show', f'{publication}:{relative}'], cwd=ROOT, timeout=120)
            require(published == path.read_bytes(), f'Split metadata/evidence differs from exact publication: {relative}')
        identity_check = verify_split_identity(split_manifest, identity)
        expected_private = identity_check['private_user_names']
        appendix_text = appendix_path.read_text()
        appendix_expected = re.findall(r'^    "(ImbalancedChen\.[^"]+)"[,\]]', appendix_text, re.M)
        require(appendix_expected == expected_private,
                'Private scoped-simp audit must check every original private theorem exactly once.')
        state['split_manifest'] = record_file(split_manifest_path)
        state['command_identity'] = record_file(identity_path)
        state['scoped_simp_audit_appendix'] = record_file(appendix_path)
        state['source_identity_check'] = identity_check
        state['original_theorem_commands_byte_identical'] = True

        for module, expected_object in BASE_OBJECTS.items():
            prior = old['dependency_objects'][module]
            require(prior['sha256'] == expected_object, f'Canonical dependency hash mismatch: {module}')
            receipt_path = bind(prior['receipt'], prior['receipt_sha256'])
            receipt = json.loads(receipt_path.read_text())
            require(receipt['accepted'] is True and receipt['module'] == module, f'Base dependency is not accepted: {module}')
            if module.endswith('P2Saving16StringCharBinding00'):
                require(receipt['primary_object_sha256'] == expected_object and
                        receipt['candidate_sha256'] == SOURCES[module]['source_sha256'] and
                        receipt['full_owned_audit_accepted'] is True, 'Raw character binding acceptance mismatch.')
                for label in ['normal', 'replay', 'audit']:
                    stage_log(receipt[label])
                for relative, h in receipt['artifacts'].items():
                    bind(receipt_path.parent / relative, h)
                bind(receipt['audit_source'], receipt['audit_source_sha256'])
            else:
                require(receipt['object_sha256'] == expected_object and
                        receipt['source_sha256'] == SOURCES[module]['source_sha256'],
                        f'Base accepted source/object pair mismatch: {module}')
                for label in ['replay', 'audit']:
                    stage_log(receipt[label])
                for relative, h in receipt['artifacts'].items():
                    bind(ROOT / relative, h)
            copy_dependency(module, prior['path'], expected_object, 'Exact canonical accepted dependency receipt/object reused')
            state['dependency_receipts'][module] = record_file(receipt_path)

        files_path = bind(ROOT / PACKAGE / 'TYPED_PAYLOAD_FILES.json', PAYLOAD_FILES_SHA)
        payload_files = json.loads(files_path.read_text())
        expected_payload = sorted(payload_files['expected_owned_names'])
        require(payload_files['module'] == PAYLOAD and payload_files['expected_owned_declarations'] ==
                len(expected_payload) == len(set(expected_payload)) == 544, 'Expected payload inventory differs.')
        require(payload_files['original_input_sha256'] == INPUT_SHA, 'Payload original input hash mismatch.')
        for entry in payload_files['files']:
            bind(ROOT / entry['path'], entry['sha256'])
        audit_template_path = bind(ROOT / payload_files['audit_file'])
        audit_template = audit_template_path.read_text()
        state['payload_files_manifest'] = record_file(files_path)
        state['audit_template'] = record_file(audit_template_path)
        verify_component(PAYLOAD_RESULT, future[PAYLOAD], PAYLOAD)
        verify_component(CHARS_RESULT, future[CHARS], CHARS)

        verify_reproduced_original_acceptance()
        reproduced_path = bind(REPRODUCED / 'RESULT.json')
        reproduced = json.loads(reproduced_path.read_text())
        require(reproduced['module'] == 'ImbalancedChen.P2Saving16Cell00Decoded', 'Unexpected reproduction container owner.')
        state['reproduction_container'] = {
            **record_file(reproduced_path), 'container_status': reproduced['status'],
            'container_owner_used': False, 'only_exact_accepted_reproductions_used': True,
        }
        for module, expected_object in REPRODUCED_OBJECTS.items():
            rows = [r for r in reproduced['reproduced_accepted_objects'] if r['module'] == module]
            require(len(rows) == 1, f'Accepted reproduced module missing/duplicated: {module}')
            row = rows[0]
            require(row['exact_accepted_object_match'] is True and row['object_sha256'] == expected_object and
                    row['source_sha256'] == SOURCES[module]['source_sha256'], f'Reproduced object binding mismatch: {module}')
            dependency = reproduced['dependencies'][module]
            require(dependency['sha256'] == expected_object and dependency['source_sha256'] == SOURCES[module]['source_sha256'],
                    f'Reproduction dependency metadata mismatch: {module}')
            object_path = REPRODUCED / 'lib' / (module.replace('.', '/') + '.olean')
            require(Path(dependency['path']) == object_path, f'Unexpected reproduction object location: {module}')
            bind(REPRODUCED / 'src' / (module.replace('.', '/') + '.lean'), SOURCES[module]['source_sha256'])
            log = bind(REPRODUCED / (module.split('.')[-1] + '-REPRODUCE.log'), row['log_sha256'])
            copy_dependency(module, object_path, expected_object, 'Byte-identical reproduction of separately accepted strict/replay/full-owned object')
            state['dependency_receipts'][module] = {'reproduction_receipt': record_file(reproduced_path),
                                                  'reproduction_log': record_file(log), 'entry': row}
        needed = set().union(*(project_closure(s['module']) for s in MODULES)) - {s['module'] for s in MODULES}
        require(set(state['dependency_objects']) == needed, 'Isolated dependency set differs from actual source graph.')
        require(len(list((lib / 'ImbalancedChen').glob('*.olean'))) == len(needed) == 8, 'Unexpected dependency object in isolated library.')
        require(set(prior_run['dependency_objects']) == needed,
                'Prior aggregate base-dependency inventory differs from the reviewed source graph.')
        for module, row in prior_run['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'] and
                    row['sha256'] == state['dependency_objects'][module]['sha256'],
                    f'Prior accepted owner dependency identity differs in the fresh root: {module}')
            bind(row['path'], row['sha256'])
            bind(row['isolated_path'], row['sha256'])
        for module in REUSED_OBJECTS:
            verify_component(prior_path, prior_run, module)
            state['reused_owner_objects'][module] = state['dependency_objects'].pop(module)
            # Preserve the original publication, stage logs, paths, timestamps
            # and owner status exactly. The new aggregate is a selection view.
            state['modules'][module] = json.loads(json.dumps(prior_run['modules'][module]))
            state['owner_receipt_sources'][module] = {
                **record_file(prior_path), 'owner_module': module,
                'owner_source_origin': prior_run['modules'][module]['source_origin'],
                'owner_object_sha256': REUSED_OBJECTS[module],
                'aggregate_status': prior_run['status'], 'aggregate_accepted': False,
                'owner_accepted': True,
            }
        existing = needed | set(REUSED_OBJECTS)
        require(set(state['dependency_objects']) == needed and len(needed) == 8 and
                set(state['reused_owner_objects']) == set(REUSED_OBJECTS) and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == len(existing) == 11 and
                not (lib / (TARGET.replace('.', '/') + '.olean')).exists(),
                'The fresh library must contain exactly eight base dependencies and three prior accepted owners.')
        state.update(reused_owners_accepted=True, certified_reader_ast_binding_proved=True,
                     reused_owner_receipt_policy='Exact original owner entries, publication identities and complete stage receipts retained')

        # Reuse a complete already accepted current snapshot; never pretend its
        # first-captured current hashes existed in the original Field receipts.
        current_result_path = bind(CURRENT_EXTERNAL / 'RESULT.json', CURRENT_EXTERNAL_RESULT_SHA)
        current_result = json.loads(current_result_path.read_text())
        require(current_result['schema'] == 'p25-cell00-remaining-arithmetic-strict-v1' and
                current_result['status'] == 'CELL00_ALL_EIGHT_TYPED_ARITHMETIC_ACCEPTED' and
                current_result['accepted'] is True and
                current_result['publication_commit'] == CURRENT_EXTERNAL_PUBLICATION and
                current_result['complete_external_after_matches_before'] is True and
                current_result['runtime'] == state['runtime'] and
                current_result['strict_flags'] == FLAGS and current_result['dependency_modules_compiled'] == [],
                'The complete accepted current external context receipt differs.')
        artifact(current_result['runner'], CURRENT_EXTERNAL_RUNNER_SHA)
        current_snapshot_path = artifact(current_result['complete_external_before'], CURRENT_EXTERNAL_SNAPSHOT_SHA)
        require(current_snapshot_path == CURRENT_EXTERNAL / 'COMPLETE_EXTERNAL_BEFORE.json',
                'Unexpected accepted current external snapshot path.')
        current_snapshot = json.loads(current_snapshot_path.read_text())
        providers = [LEAN.parent.parent / 'lib/lean', *map(Path, tails)]
        require(len(providers) == len(set(providers)) and
                all(p.is_dir() and not (p / 'ImbalancedChen').exists() for p in providers) and
                current_snapshot['provider_roots'] == list(map(str, providers)) and
                current_snapshot['schema'] == 'p25-complete-current-external-snapshot-v1' and
                current_snapshot['module_count'] == EXPECTED_EXTERNAL_COUNT and
                current_snapshot['historical_missing_hashes_invented'] is False,
                'Current snapshot provider roots/module count/provenance differ.')
        expected_external = {row['module'] for row in current_snapshot['entries']}
        require(len(expected_external) == len(current_snapshot['entries']) == EXPECTED_EXTERNAL_COUNT,
                'Current external snapshot contains missing or duplicated modules.')
        for module in REUSED_OBJECTS:
            imported = audited_imports(prior_run['modules'][module]['stages']['audit']['log'])
            require({m for m in imported if not m.startswith('ImbalancedChen.')} == expected_external,
                    'Original reused owner external imports differ from the selected current snapshot: ' + module)
        context_start = now()
        for row in current_snapshot['entries']:
            module = row['module']
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module),
                    'Invalid audited external module name.')
            relative = module.replace('.', '/') + '.olean'
            found = [root / relative for root in providers if (root / relative).is_file()]
            require(len(found) == 1 and str(found[0]) == row['object']['path'],
                    'Missing or shadowed current external provider: ' + module)
            obj = artifact(row['object'])
            require(current_result['frozen_inputs'].get(str(obj)) == row['object']['sha256'],
                    'Current accepted receipt does not freeze this external object: ' + module)
            expected_companions = [str(obj) + suffix for suffix in ['.private', '.server']
                                   if Path(str(obj) + suffix).is_file()]
            require(expected_companions == [entry['path'] for entry in row['companions']],
                    'Current external companion inventory differs: ' + module)
            for companion in row['companions']:
                artifact(companion)
                require(current_result['frozen_inputs'].get(companion['path']) == companion['sha256'],
                        'Current accepted receipt does not freeze this external companion: ' + module)
            external_entries.append({'module': module, 'object': row['object'], 'companions': row['companions']})
        before = {
            'schema': 'p25-complete-current-external-snapshot-reuse-v1',
            'started_utc': context_start, 'finished_utc': now(),
            'provider_roots': list(map(str, providers)), 'module_count': len(external_entries),
            'source_accepted_receipt': record_file(current_result_path),
            'source_complete_snapshot': record_file(current_snapshot_path),
            'all_hashes_reused_from_accepted_current_snapshot': True,
            'original_field_historical_missing_hashes_invented': False,
            'entries': external_entries,
        }
        before_path = OUT / 'COMPLETE_EXTERNAL_BEFORE.json'
        before_path.write_text(json.dumps(before, indent=2) + '\n')
        bind(before_path)
        state['complete_external_before'] = record_file(before_path)
        state['current_external_context_source'] = {
            'receipt': record_file(current_result_path), 'snapshot': record_file(current_snapshot_path),
            'publication_commit': CURRENT_EXTERNAL_PUBLICATION,
            'formal_proof_owners_reused_from_remaining_arithmetic': [],
            'purpose': 'Only exact current external object/companion hashes are reused; old Field historical evidence is not relabeled.',
        }
        state['expected_external_imports'] = sorted(expected_external)
        state['frozen_inputs'] = dict(frozen)
        write()
        context_check()

        # No existing complete-context validation of these three objects exists
        # in the selected remaining-arithmetic receipt. Supplement only their
        # replay/audit; retain every original ecfc owner dictionary unchanged.
        for module in REUSED_OBJECTS:
            original_owner = prior_run['modules'][module]
            directory = OUT / (module.split('.')[-1] + '-reuse-validation')
            directory.mkdir()
            reuse_audit = audit / (module.split('.')[-1] + 'ReuseAudit.lean')
            reuse_audit.write_text(audit_template.replace(PAYLOAD, module))
            bind(reuse_audit)
            reuse_object = lib / (module.replace('.', '/') + '.olean')
            require(digest(reuse_object) == REUSED_OBJECTS[module], 'Supplemental reuse object identity differs.')
            reuse = {
                'module': module, 'status': 'PENDING', 'accepted': False, 'normal_recompiled': False,
                'source_origin': original_owner['source_origin'], 'source_copy': original_owner['source_copy'],
                'object': record_file(reuse_object), 'audit_source': record_file(reuse_audit),
                'original_owner_receipt': record_file(prior_path), 'stages': {},
            }
            state['additional_reuse_validations'][module] = reuse
            state['frozen_inputs'] = dict(frozen)
            write()
            for label, command in [('replay', [str(CHECKER), '--verbose', module]),
                                   ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(reuse_audit)])]:
                run_stage(reuse, label, command, directory / (label.upper() + '.log'))
            records, inventory, imports = read_audit(directory / 'AUDIT.log', module)
            external = {m for m in audited_imports(directory / 'AUDIT.log') if not m.startswith('ImbalancedChen.')}
            require(records == original_owner['owned_declarations'] and
                    inventory == json.loads(artifact(original_owner['inventory']).read_text()) and
                    imports == original_owner['actual_project_closure'] and external == expected_external,
                    'Supplemental reuse complete inventory or imports differ from the original accepted owner.')
            reuse.update(status='REPLAY_COMPLETE_OWNED_REUSE_VALIDATED', accepted=True,
                         owned_count=len(records), owned_declarations=records, inventory=inventory,
                         actual_project_closure=imports, actual_external_import_count=len(external),
                         complete_external_before=record_file(before_path), ended_utc=now())
            state['frozen_inputs'] = dict(frozen)
            context_check()
            write()
            print('P25_FIELD_SPLIT_REUSE_VALIDATED', module, len(records), REUSED_OBJECTS[module], flush=True)

        for spec in FRESH_SPECS:
            module = spec['module']
            source_path = ROOT / SOURCES[module]['path']
            source_copy = src / (module.replace('.', '/') + '.lean')
            source_copy.write_bytes(source_path.read_bytes())
            bind(source_copy, SOURCES[module]['source_sha256'])
            public = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)', source_path.read_text(), re.M)
            require(len(public) == len(set(public)) == spec['public_count'], f'Frozen public declaration count mismatch: {module}')
            required = [spec['namespace'] + '.' + n for n in public]
            require(required == spec['public_names'] and
                    (spec['required_final_name'] is None and not required or
                     spec['required_final_name'] in required), f'Required final/public declarations differ: {module}')
            audit_path = audit / (module.split('.')[-1] + '.lean')
            audit_text = audit_template.replace(PAYLOAD, module)
            if module == SUPPORT:
                audit_text += appendix_text
            audit_path.write_text(audit_text)
            bind(audit_path)
            state['modules'][module] = {
                'module': module, 'status': 'PENDING', 'accepted': False,
                'source_origin': {'commit': publication, 'path': SOURCES[module]['path'],
                                  'sha256': SOURCES[module]['source_sha256']},
                'source_copy': record_file(source_copy), 'audit_source': record_file(audit_path),
                'required_owned_names': required,
                'required_private_user_names': expected_private if module == SUPPORT else [],
                'stages': {},
            }
        state.update(status='VERIFYING_SPLIT_OWNERS', frozen_inputs=dict(frozen))
        check_frozen()
        write()

        for spec in FRESH_SPECS:
            module = spec['module']
            owner = state['modules'][module]
            for dependency in project_closure(module) - {module}:
                require(dependency in state['dependency_objects'] or
                        dependency in state['modules'] and state['modules'][dependency]['accepted'] is True,
                        f'Fresh owner dependency has not passed all acceptance gates: {module}/{dependency}')
            owner['status'] = 'RUNNING'
            directory = OUT / module.split('.')[-1]
            directory.mkdir()
            source_path = src / (module.replace('.', '/') + '.lean')
            object_path = lib / (module.replace('.', '/') + '.olean')
            audit_path = audit / (module.split('.')[-1] + '.lean')
            require(not object_path.exists(), f'Unexpected existing target object: {module}')
            commands = [
                ('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(object_path), str(source_path)]),
                ('replay', [str(CHECKER), '--verbose', module]),
                ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(audit_path)]),
            ]
            for label, command in commands:
                run_stage(owner, label, command, directory / (label.upper() + '.log'))
                if label == 'normal':
                    require(object_path.is_file(), f'Normal compile produced no object: {module}')
                    bind(object_path)
                    owner['object'] = record_file(object_path)
                    owner['object_companions'] = []
                    for suffix in ['.private', '.server']:
                        companion = Path(str(object_path) + suffix)
                        if companion.is_file():
                            bind(companion)
                            owner['object_companions'].append(record_file(companion))
                    state['frozen_inputs'] = dict(frozen)
                    write()
            records, inventory, imports = read_audit(directory / 'AUDIT.log', module)
            require(set(owner['required_owned_names']) <= {r['name'] for r in records}, f'Public theorem missing from full owned audit: {module}')
            external = {m for m in audited_imports(directory / 'AUDIT.log') if not m.startswith('ImbalancedChen.')}
            require(external == expected_external, 'New split owner imported an unexpected external module: ' + module)
            owner['actual_external_import_count'] = len(external)
            owner['complete_external_before'] = record_file(before_path)
            if module == SUPPORT:
                scope_check = read_private_scope_audit(directory / 'AUDIT.log', records, expected_private)
                scope_path = directory / 'PRIVATE_SCOPED_SIMP_INTERFACE.json'
                scope_path.write_text(json.dumps(scope_check, ensure_ascii=False, indent=2) + '\n')
                bind(scope_path)
                owner['private_scoped_simp_interface'] = record_file(scope_path)
                state['private_scoped_simp_interface_checked'] = True
            declarations_path = directory / 'OWNED_DECLARATIONS.json'
            declarations_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n')
            inventory_path = directory / 'OWNED_INVENTORY.json'
            inventory_path.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + '\n')
            bind(declarations_path)
            bind(inventory_path)
            state['frozen_inputs'] = dict(frozen)
            owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                         owned_count=len(records), owned_declarations=records, actual_project_closure=imports,
                         declarations=record_file(declarations_path), inventory=record_file(inventory_path), ended_utc=now())
            context_check()
            write()
            print('P25_FIELD_DECODE_OWNER_ACCEPTED', module, len(records), owner['object']['sha256'], flush=True)
        require(all(o['accepted'] for o in state['modules'].values()), 'Not all fourteen selected composition owners accepted.')
        require(set(state['modules']) == {s['module'] for s in MODULES} and
                state['module_order'] == FRESH_MODULES and state['reused_owners_recompiled'] == [] and
                state['original_theorem_commands_byte_identical'] is True and
                state['private_scoped_simp_interface_checked'] is True and
                state['old_owner_normal_recompilations'] == [] and
                set(state['additional_reuse_validations']) == set(REUSED_OBJECTS) and
                all(r['accepted'] is True and r['normal_recompiled'] is False and
                    set(r['stages']) == {'replay', 'audit'} for r in state['additional_reuse_validations'].values()) and
                state['dependency_modules_compiled'] == [] and state['failed_same_name_field_object_used'] is False,
                'Incremental target/reuse policy changed.')
        require(all(state['modules'][m] == prior_run['modules'][m] for m in REUSED_OBJECTS),
                'A reused owner entry was relabeled or modified.')
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Publication changed during verification.')
        context_check()
        state.update(complete_external_after_matches_before=True, frozen_inputs=dict(frozen))
        state.update(status='FULL_AST_BINDING_AND_RAW_ROOT_TYPED_DECODE_ACCEPTED', accepted=True,
                     certified_reader_ast_binding_proved=True, raw_root_typed_decode_proved=True, ended_utc=now())
        write()
        print('P25_FIELD_DECODE_RESULT', json.dumps({
            'status': state['status'], 'accepted': True,
            'owned_counts': {m: o['owned_count'] for m, o in state['modules'].items()},
            'original_string_typed_decode_proved': False, 'geometric_jensen_binding_proved': False,
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
        print('P25_FIELD_DECODE_FAILED', json.dumps({
            'status': state['status'], 'error': state['error'][:1800],
            'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json'),
        }, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
