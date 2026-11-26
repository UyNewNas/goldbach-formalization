import sys
import base64
import datetime
import hashlib
import json
import os
import shutil
import stat
import tarfile
import urllib.request
from pathlib import Path, PurePosixPath

PIN = {'archives': [{'archive': {'bytes': 5933976, 'sha256': '06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f'}, 'existing_path': '/workspace/p29-omitted-inputs-20261126-b23868d/archives/unit128.tar.xz', 'expanded_member_bytes': 105617839, 'expected_original_stat': [27, 3155138, 33152, 1, 5933976, 1795680279485134430, 1795680279485134430], 'format': 'xz', 'id': 'unit128_existing', 'manifest': {'bytes': 22426, 'member': 'FILE_MANIFEST.json', 'schema': 'p29_unit_tail_complete_current_receiver_evidence_v1', 'sha256': 'f6246295885137041434ed75c773e4e1d578345bdd552c1033caba016fe36ec3', 'shape': 'files_dictionary'}, 'max_expanded_bytes': 105617839, 'member_count': 128, 'original_manifest_record': {'bytes': 22426, 'git_blob': '6b50800b0c47626fc8d61dfd132d3ecc4a5f227c', 'path': '/workspace/p29-omitted-inputs-20261126-b23868d/provenance/unit128/FILE_MANIFEST.json', 'sha256': 'f6246295885137041434ed75c773e4e1d578345bdd552c1033caba016fe36ec3', 'stat': [27, 3155140, 33152, 1, 22426, 1795680280422325751, 1795680280422325751]}, 'transport': 'EXISTING_P2_FILE_ONLY_NO_DOWNLOAD_ROUTE'}, {'archive': {'bytes': 102274, 'sha256': 'c48f8974537d91d1113a9d67b71ca7a3ee0407a67ced3476456f1f85ece56cbb'}, 'expanded_member_bytes': None, 'format': 'gz', 'id': 'nonradial15_Git_fallback', 'manifest': {'bytes': None, 'bytes_binding': 'Exact complete archive SHA and exact original manifest SHA bind its original length; observed length is bounded and recorded.', 'member': 'FILE_MANIFEST.json', 'schema': 'p29_nonradial_object_archive_manifest_v1', 'sha256': '0fbfafc4f8d37fcf129d615a2fb710508d096be94590873de7627ef7135c0019', 'shape': 'files_dictionary'}, 'max_expanded_bytes': 16777216, 'member_count': 15, 'original_accepted_receipt_sha256': '70335088765bca1a2f6475b998a9e587343901a6767ed6748bca7a20fa5e8f45', 'parts': [{'bytes': 102274, 'git_blob': '8a8702a17098ae6129603a421d94f48526cfd653', 'index': 0, 'offset': 0, 'sha256': 'c48f8974537d91d1113a9d67b71ca7a3ee0407a67ced3476456f1f85ece56cbb'}], 'transport': 'EXISTING_SINGLE_GIT_ARCHIVE_ONLY_IF_MISSING_MEMBER'}, {'accepted_root_blob': 'a095d954717e09ea2b42e96ba31d581d585a6a42', 'archive': {'bytes': 3894004, 'sha256': 'eb39540322acb1fc4d19b7a126a80df5430fdaf81208438e6c6f1bcd1eceb99b'}, 'expanded_member_bytes': 62395504, 'format': 'xz', 'id': 'gate76_existing_Git_parts', 'manifest': {'bytes': 12647, 'member': 'FILE_MANIFEST.json', 'schema': 'p29_gate_complete_current_receiver_evidence_v1', 'sha256': '83c6f183ad9b228961899a842ff5bddb29c4ebabf078d0fe9e079822fe9da106', 'shape': 'files_dictionary'}, 'max_expanded_bytes': 62395504, 'member_count': 76, 'parts': [{'bytes': 1350000, 'git_blob': '7e33e2b7da09abfab5f976f9cda35a8368c948b4', 'index': 0, 'offset': 0, 'sha256': '1989d388ba749583230dfbe0059b55becfe89a05e94baa0632497ee24a36aaec'}, {'bytes': 1350000, 'git_blob': '653d3ecf2fbfb9af106723ab538caa91b514b487', 'index': 1, 'offset': 1350000, 'sha256': 'a131eb581fa000221ad42a2f79d9d3e95f49e3fba5cc7a6ee6bd3003b6d39d35'}, {'bytes': 1194004, 'git_blob': 'f7b58192336202e3bcf2bfd3db4484f22f01ea90', 'index': 2, 'offset': 2700000, 'sha256': '274a2700b15aa70c8b1d6d12b51a18a1b3a1888d2abf2de4c0232935c00db15d'}], 'transport': 'EXISTING_GIT_PARTS_ONCE_IF_NEEDED'}], 'base': '/workspace/p29-nonempty-inputs-20261126-14206fd', 'input_index': {'bytes': 65615, 'git_blob': '14206fd1313675e2d855e9765b89e4594e36c994', 'sha256': '2b8b20b150f16b54c1be3ccb39df33f292c92767ef1f94bbd011b9a6536cce7f'}, 'limits': {'maximum_captured_member_bytes': 4194304, 'maximum_receipt_bytes': 131072, 'minimum_free_bytes': 67108864, 'requested_cpu_threads': 1, 'requested_memory_mb': 512, 'requested_timeout_seconds': 300}, 'objects': [{'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5DerivativeBudget.olean'], 'bytes': 637080, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5DerivativeBudget.olean', 'module': 'ImbalancedChen.P2FiniteMarkedGamma5DerivativeBudget', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5DerivativeBudget.olean', 'old_owned_count': 36, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '3d7bca5a0936df25817fda343d6a94ac6402a7fb5fa7414bddd1c9c706fe4786', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2FiniteMarkedGamma5DerivativeBudget.lean'], 'bytes': 8827, 'git_blob': 'ee86de19d6ccd0c0a2b0ebf5e23daf00312cce91', 'member': 'verification/borrowed-sources/ImbalancedChen/P2FiniteMarkedGamma5DerivativeBudget.lean', 'sha256': '0a84add117c53379c6ee0c80a1aec24beea0841ad8a9ce55a8b84bcefe5e04e0'}, 'source_destination_relative': 'sources/ImbalancedChen/P2FiniteMarkedGamma5DerivativeBudget.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5EulerWordBudget.olean'], 'bytes': 278024, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5EulerWordBudget.olean', 'module': 'ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5EulerWordBudget.olean', 'old_owned_count': 19, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '4a621b47c2f2b7739eb08e876779d85822d65131a98ad2b324ae14d031ab882a', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2FiniteMarkedGamma5EulerWordBudget.lean'], 'bytes': 9269, 'git_blob': '37f17bea5ff8988f0b3853d1da45acf9560f490d', 'member': 'verification/borrowed-sources/ImbalancedChen/P2FiniteMarkedGamma5EulerWordBudget.lean', 'sha256': '761063d2147c7de6dc02bf6f616d1c4cb7be6d6f8da26f86c5e41c74755782a5'}, 'source_destination_relative': 'sources/ImbalancedChen/P2FiniteMarkedGamma5EulerWordBudget.lean'}, {'P2_candidates': [], 'bytes': 942264, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5GateAffine.olean', 'module': 'ImbalancedChen.P2FiniteMarkedGamma5GateAffine', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5GateAffine.olean', 'old_owned_count': 81, 'provider': 'gate76_existing_Git_parts', 'qualification_group': 'gate_original_accepted_76_members', 'sha256': '375947c766716ad8da5d114c395217f52fc6cc5adbe64327490b1c11aad02944', 'source': {'P2_candidates': [], 'bytes': 10694, 'git_blob': 'fb1ab9c164ecd705653903a57b9ee53838303de9', 'member': 'project/ImbalancedChen/P2FiniteMarkedGamma5GateAffine.lean', 'sha256': '18967fcc3ced75318d5b8d7e6ee40153b30d6dfc8678527a6f37753550f9a6db'}, 'source_destination_relative': 'sources/ImbalancedChen/P2FiniteMarkedGamma5GateAffine.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5LogProfileCore.olean'], 'bytes': 546560, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5LogProfileCore.olean', 'module': 'ImbalancedChen.P2FiniteMarkedGamma5LogProfileCore', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5LogProfileCore.olean', 'old_owned_count': 142, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '4429507c62a0477a44c3e5811e0d49f466387480d11a69c769d5956d4c4f549c', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2FiniteMarkedGamma5LogProfileCore.lean'], 'bytes': 4194, 'git_blob': 'ef29c0152780a3a19e53175ba31f84461bfcba14', 'member': 'verification/borrowed-sources/ImbalancedChen/P2FiniteMarkedGamma5LogProfileCore.lean', 'sha256': '324f9fca702643ed21baf54ccf00869b2d4f8c881fab19709e7b03875bb2c6cb'}, 'source_destination_relative': 'sources/ImbalancedChen/P2FiniteMarkedGamma5LogProfileCore.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5NonradialSupport.olean'], 'bytes': 129416, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5NonradialSupport.olean', 'module': 'ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport', 'object_member': 'objects/ImbalancedChen/P2FiniteMarkedGamma5NonradialSupport.olean', 'old_owned_count': 6, 'provider': 'nonradial15_Git_fallback', 'qualification_group': 'nonradial_original_accepted_six', 'sha256': '0285b3ed20b8b8d3b5a540dab4f2c6e60a8120a0c6eead3f081036ae8dbe5883', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2FiniteMarkedGamma5NonradialSupport.lean'], 'bytes': 5112, 'git_blob': '2091608eaeec53f3f8b60224fb7b10048642805e', 'member': 'source/ImbalancedChen/P2FiniteMarkedGamma5NonradialSupport.lean', 'sha256': '3d6f71b982a984e7fdd880b21ab496237ebeb656bed24990dedcfec96dff74bd'}, 'source_destination_relative': 'sources/ImbalancedChen/P2FiniteMarkedGamma5NonradialSupport.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5PhysicalEulerBudget.olean'], 'bytes': 632472, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5PhysicalEulerBudget.olean', 'module': 'ImbalancedChen.P2FiniteMarkedGamma5PhysicalEulerBudget', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5PhysicalEulerBudget.olean', 'old_owned_count': 20, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '2f61e1347e804251ff763c678146c62ed8daa246ed95153539b932876510cde4', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2FiniteMarkedGamma5PhysicalEulerBudget.lean'], 'bytes': 14425, 'git_blob': '02ed4e488c8ab37853c10eee0b58d0e8ddd6e2ad', 'member': 'verification/borrowed-sources/ImbalancedChen/P2FiniteMarkedGamma5PhysicalEulerBudget.lean', 'sha256': '2d5bf41aabe57cf035ad443f9b4ae44608aa3f4d0d9636494413f7f746c426ac'}, 'source_destination_relative': 'sources/ImbalancedChen/P2FiniteMarkedGamma5PhysicalEulerBudget.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5PhysicalExtension.olean'], 'bytes': 371520, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5PhysicalExtension.olean', 'module': 'ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5PhysicalExtension.olean', 'old_owned_count': 35, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': 'c80ed8b590734eb936bafd1a50889d1f431a8617bf21d059d7f4f30c4d68138c', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2FiniteMarkedGamma5PhysicalExtension.lean'], 'bytes': 13094, 'git_blob': '2f776e2b4f9d5125b1df887d0e5da01e2c52dd1b', 'member': 'verification/borrowed-sources/ImbalancedChen/P2FiniteMarkedGamma5PhysicalExtension.lean', 'sha256': 'f54dfd8c30c3c0bb1982ac09bb91d7c39f7ed01342d32f1e18b63eb15e3395a5'}, 'source_destination_relative': 'sources/ImbalancedChen/P2FiniteMarkedGamma5PhysicalExtension.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2OriginalEulerWordConjugacyCore.olean'], 'bytes': 289312, 'destination_relative': 'lib/lean/ImbalancedChen/P2OriginalEulerWordConjugacyCore.olean', 'module': 'ImbalancedChen.P2OriginalEulerWordConjugacyCore', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2OriginalEulerWordConjugacyCore.olean', 'old_owned_count': 25, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': 'd7de1edfd0cd0661e68a73f9e554a33eab46cf1d9def24dc9c478bae4e4ef838', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2OriginalEulerWordConjugacyCore.lean'], 'bytes': 7135, 'git_blob': 'f5baa91c576972d9f58bfd16c550bd661675734b', 'member': 'verification/borrowed-sources/ImbalancedChen/P2OriginalEulerWordConjugacyCore.lean', 'sha256': '29b4397331ac573e1da3c5d3eb972790f58bc9f12f21834dfe4e1398d0f73d8f'}, 'source_destination_relative': 'sources/ImbalancedChen/P2OriginalEulerWordConjugacyCore.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2SeedOmegaCutoffConstants.olean'], 'bytes': 11976, 'destination_relative': 'lib/lean/ImbalancedChen/P2SeedOmegaCutoffConstants.olean', 'module': 'ImbalancedChen.P2SeedOmegaCutoffConstants', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2SeedOmegaCutoffConstants.olean', 'old_owned_count': 6, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '133126a5701675bf745bcd5f60c57938d2ac709a2a592eea940d52f84fda60df', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2SeedOmegaCutoffConstants.lean'], 'bytes': 538, 'git_blob': 'afbc7d3ed60fe835c505474bed349c796c397038', 'member': 'verification/borrowed-sources/ImbalancedChen/P2SeedOmegaCutoffConstants.lean', 'sha256': 'e08b413fbe728b2def25c22eb88a3786b85b12bb9db2ea9ad7157612615dc0a8'}, 'source_destination_relative': 'sources/ImbalancedChen/P2SeedOmegaCutoffConstants.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2SmoothLogFloorDerivativeCore.olean'], 'bytes': 151664, 'destination_relative': 'lib/lean/ImbalancedChen/P2SmoothLogFloorDerivativeCore.olean', 'module': 'ImbalancedChen.P2SmoothLogFloorDerivativeCore', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2SmoothLogFloorDerivativeCore.olean', 'old_owned_count': 4, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '0fe2ffe476bc30fe476081943f417ea58fac86d9bc55ceb25d19230f33b6c0cd', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2SmoothLogFloorDerivativeCore.lean'], 'bytes': 3252, 'git_blob': '8b00ad6245067e129fa3a214fe99cfbdea445adb', 'member': 'verification/borrowed-sources/ImbalancedChen/P2SmoothLogFloorDerivativeCore.lean', 'sha256': 'bc9fd90fadf2c967df05e4e9a0be2491d642b63369f060cd2aed25bee6c7b472'}, 'source_destination_relative': 'sources/ImbalancedChen/P2SmoothLogFloorDerivativeCore.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P2SmoothPositiveArgumentCore.olean'], 'bytes': 136296, 'destination_relative': 'lib/lean/ImbalancedChen/P2SmoothPositiveArgumentCore.olean', 'module': 'ImbalancedChen.P2SmoothPositiveArgumentCore', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2SmoothPositiveArgumentCore.olean', 'old_owned_count': 7, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '677e39fcb0ae11aa830176b400970ca59f1357433660c158c1d96d0082d0f03f', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P2SmoothPositiveArgumentCore.lean'], 'bytes': 2080, 'git_blob': 'edfa7173eff8f9f6ffc1b5b8afcc6b3edbfe410f', 'member': 'verification/borrowed-sources/ImbalancedChen/P2SmoothPositiveArgumentCore.lean', 'sha256': 'ca41044b480a835b5242f930e166f83159ec7386cd8c0bb78643f09f056481d4'}, 'source_destination_relative': 'sources/ImbalancedChen/P2SmoothPositiveArgumentCore.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P4BSmoothGateUpperStep.olean'], 'bytes': 181256, 'destination_relative': 'lib/lean/ImbalancedChen/P4BSmoothGateUpperStep.olean', 'module': 'ImbalancedChen.P4BSmoothGateUpperStep', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P4BSmoothGateUpperStep.olean', 'old_owned_count': 18, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': 'c55f340219e01672a9777379a86f1d453956fa9aa3f5d5daf90ddb8caf74ef15', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P4BSmoothGateUpperStep.lean'], 'bytes': 7103, 'git_blob': '975207ba10a479f6e3c3ac2659922608e30f4d4b', 'member': 'verification/borrowed-sources/ImbalancedChen/P4BSmoothGateUpperStep.lean', 'sha256': '7f51e436ec635bf89fbcf69f02e8c35f8b1a46df1183322f04c61dc69ea43764'}, 'source_destination_relative': 'sources/ImbalancedChen/P4BSmoothGateUpperStep.lean'}, {'P2_candidates': ['/workspace/p2-9-20261125/.lake/p2-private/lib/ImbalancedChen/P4BSmoothStepDerivativeBudget.olean'], 'bytes': 137816, 'destination_relative': 'lib/lean/ImbalancedChen/P4BSmoothStepDerivativeBudget.olean', 'module': 'ImbalancedChen.P4BSmoothStepDerivativeBudget', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P4BSmoothStepDerivativeBudget.olean', 'old_owned_count': 8, 'provider': 'unit128_existing', 'qualification_group': 'unit128_old18_original_qualification', 'sha256': '0eeb4b09869d76cdf83c8e2f5fae80d97c125b21a9135d10f6ad552098ec48b5', 'source': {'P2_candidates': ['/workspace/p2-9-20261125/ImbalancedChen/P4BSmoothStepDerivativeBudget.lean'], 'bytes': 6499, 'git_blob': 'a69431f7b7c81bf0490e896efe07250b2a54a364', 'member': 'verification/borrowed-sources/ImbalancedChen/P4BSmoothStepDerivativeBudget.lean', 'sha256': 'b2eb98634d337d9af63ecc951f34771dac8489361e64961332a7712bb1ef69d4'}, 'source_destination_relative': 'sources/ImbalancedChen/P4BSmoothStepDerivativeBudget.lean'}], 'old18_receiver_receipt': {'bytes': 84932, 'git_blob': '9ab8131c222dd65d98b92b652cc558efb4c5c5e8', 'path': '/workspace/p29-omitted-inputs-20261126-b23868d/BYTE_RECEPTION_RECEIPT.json', 'sha256': '855300937a4938f0a83fa1127476abd87263161d51a885ef4fad86a5a693838b'}, 'schema': 'p29_nonempty_P2_thirteen_existing_object_byte_reception_contract_v1', 'scope': {'Lean_invocations': 0, 'P3_Power_variant_introduced': False, 'actual_native_standard_graph_qualification': False, 'future_Omitted_output_read_or_written': False, 'new_proof_credit': 0, 'normal_kernel_owned_replays': 0, 'old58_objects_modified': False, 'only_thirteen_existing_objects': True}}
BASE = Path(PIN['base'])
MIN_FREE_BYTES = PIN['limits']['minimum_free_bytes']
MAX_CAPTURE_BYTES = PIN['limits']['maximum_captured_member_bytes']
MAX_STDOUT_BYTES = PIN['limits']['maximum_receipt_bytes']
created = False
current_stage = 'before-exclusive-root'
events = []
downloads = {}
protected = {}

def identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}


def stamp(s):
    return [s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('ascii')


def write_new(relative, data):
    path = BASE / relative
    assert path.is_relative_to(BASE) and '..' not in path.parts
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)
        stream.flush()
    before = stamp(path.stat())
    with path.open('rb') as stream:
        assert stamp(os.fstat(stream.fileno())) == before
        actual = stream.read(len(data) + 1)
        assert stamp(os.fstat(stream.fileno())) == before
    assert actual == data and stamp(path.stat()) == before
    return {'path': str(path), **identity(data), 'stat': before}


def stage(name):
    global current_stage
    current_stage = name
    event = {'stage': name, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    events.append(event)
    if created:
        with (BASE / 'EVENTS.jsonl').open('ab') as stream:
            stream.write((json.dumps(event, sort_keys=True) + '\n').encode('ascii'))


def fetch_blob(pin):
    blob = pin['git_blob']
    assert len(blob) == 40 and all(c in '0123456789abcdef' for c in blob)
    assert isinstance(pin['bytes'], int) and 0 < pin['bytes'] <= 2 * 1024 * 1024
    assert blob not in downloads, 'A Git blob must be fetched only once by this receiver.'
    url = 'https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/' + blob
    bound = 3 * ((4 * (pin['bytes'] + 2)) // 3) + 65536
    with urllib.request.urlopen(url, timeout=45) as response:
        raw = response.read(bound + 1)
    assert len(raw) <= bound
    value = json.loads(raw)
    assert value['encoding'] == 'base64' and value['sha'] == blob and value['size'] == pin['bytes']
    data = base64.b64decode(''.join(value['content'].split()), validate=True)
    actual = identity(data)
    assert actual == {k: pin[k] for k in ('bytes', 'sha256', 'git_blob')}
    downloads[blob] = {'url': url, **actual, 'fetch_count': 1}
    return data


def observe_candidate(path, expected):
    result = {'path': path, 'selected_for_reuse': False}
    try:
        logical = os.lstat(path)
    except FileNotFoundError:
        return {**result, 'classification': 'NO_ENTRY_AT_THIS_EXACT_CANDIDATE'}
    except OSError as exc:
        return {**result, 'classification': 'STAT_ERROR', 'errno': exc.errno, 'message': str(exc)}
    result['logical_lstat'] = stamp(logical)
    try:
        target = os.stat(path)
    except OSError as exc:
        return {**result, 'classification': 'TARGET_STAT_ERROR', 'errno': exc.errno, 'message': str(exc)}
    result['target_stat'] = stamp(target)
    result['observed_bytes'] = target.st_size
    if not stat.S_ISREG(target.st_mode):
        return {**result, 'classification': 'NONREGULAR_TARGET_NOT_REUSED'}
    if target.st_size != expected['bytes']:
        return {**result, 'classification': 'DIFFERENT_SIZE_NOT_HASHED_OR_MODIFIED', 'sha256': None}
    try:
        with open(path, 'rb') as stream:
            assert stamp(os.fstat(stream.fileno())) == result['target_stat']
            data = stream.read(expected['bytes'] + 1)
            assert stamp(os.fstat(stream.fileno())) == result['target_stat']
        assert stamp(os.lstat(path)) == result['logical_lstat']
        assert stamp(os.stat(path)) == result['target_stat']
        assert len(data) == expected['bytes']
        result['sha256'] = hashlib.sha256(data).hexdigest()
        result['classification'] = ('SAME_PIN_STABLE_CANDIDATE' if result['sha256'] == expected['sha256']
                                    else 'DIFFERENT_SHA256_NOT_MODIFIED')
    except (OSError, AssertionError) as exc:
        result['classification'] = 'READ_OR_STABILITY_ERROR_NOT_REUSED'
        result['message'] = str(exc)
    return result


def read_fixed_existing(path, pin, expected_stat=None):
    path = Path(path)
    logical = stamp(path.lstat())
    target = stamp(path.stat())
    assert stat.S_ISREG(path.lstat().st_mode), ('required existing regular file', str(path))
    assert target[4] == pin['bytes']
    if expected_stat is not None:
        assert logical == target == expected_stat
    with path.open('rb') as stream:
        assert stamp(os.fstat(stream.fileno())) == target
        data = stream.read(pin['bytes'] + 1)
        assert stamp(os.fstat(stream.fileno())) == target
    assert stamp(path.lstat()) == logical and stamp(path.stat()) == target
    actual = identity(data)
    assert actual['bytes'] == pin['bytes'] and actual['sha256'] == pin['sha256']
    if pin.get('git_blob') is not None:
        assert actual['git_blob'] == pin['git_blob']
    protected[str(path)] = {'logical_lstat': logical, 'target_stat': target, **actual}
    return data, {'path': str(path), 'logical_lstat': logical, 'stat': target, **actual}


def select_old_candidate(paths, pin):
    observations = [observe_candidate(path, pin) for path in paths]
    match = next((x for x in observations if x['classification'] == 'SAME_PIN_STABLE_CANDIDATE'), None)
    if match is None:
        return None, observations
    match['selected_for_reuse'] = True
    return {'selected_path': match['path'], 'selection': 'REUSE_EXISTING_SAME_PIN',
            'bytes': pin['bytes'], 'sha256': pin['sha256'], 'original_candidate': dict(match)}, observations


def acquire_archive(group):
    if group['transport'] == 'EXISTING_P2_FILE_ONLY_NO_DOWNLOAD_ROUTE':
        assert group['id'] == 'unit128_existing' and 'parts' not in group
        path = Path(group['existing_path'])
        logical = stamp(path.lstat())
        before = stamp(path.stat())
        assert stat.S_ISREG(path.lstat().st_mode)
        assert logical == before == group['expected_original_stat']
        assert before[4] == group['archive']['bytes']
        digest, length = hashlib.sha256(), 0
        with path.open('rb') as stream:
            assert stamp(os.fstat(stream.fileno())) == before
            while True:
                chunk = stream.read(1024 * 1024)
                if not chunk:
                    break
                length += len(chunk)
                assert length <= group['archive']['bytes']
                digest.update(chunk)
            assert stamp(os.fstat(stream.fileno())) == before
        assert stamp(path.lstat()) == logical and stamp(path.stat()) == before
        assert length == group['archive']['bytes'] and digest.hexdigest() == group['archive']['sha256']
        protected[str(path)] = {'logical_lstat': logical, 'target_stat': before,
                                'bytes': length, 'sha256': digest.hexdigest()}
        return path, {'transport': 'EXISTING_P2_ARCHIVE_READ_ONCE_FOR_HASH',
            'path': str(path), 'bytes': length, 'sha256': digest.hexdigest(),
            'stat': before, 'archive_downloads': 0, 'original_receipt_stat_matched': True}
    assert group['transport'] in ('EXISTING_GIT_PARTS_ONCE_IF_NEEDED',
                                  'EXISTING_SINGLE_GIT_ARCHIVE_ONLY_IF_MISSING_MEMBER')
    suffix = '.tar.xz' if group['format'] == 'xz' else '.tar.gz'
    path = BASE / 'archives' / (group['id'] + suffix)
    path.parent.mkdir(parents=True, exist_ok=True)
    digest, offset, parts = hashlib.sha256(), 0, []
    with path.open('xb') as stream:
        for index, pin in enumerate(group['parts']):
            assert pin['index'] == index and pin['offset'] == offset
            data = fetch_blob(pin)
            stream.write(data)
            offset += len(data)
            digest.update(data)
            parts.append({k: pin[k] for k in ('index', 'offset', 'bytes', 'sha256', 'git_blob')})
        stream.flush()
    assert offset == group['archive']['bytes'] and digest.hexdigest() == group['archive']['sha256']
    before = stamp(path.stat())
    assert before[4] == offset
    return path, {'transport': group['transport'], 'path': str(path),
        'bytes': offset, 'sha256': digest.hexdigest(), 'stat': before,
        'parts': parts, 'archive_downloads': 1, 'each_part_fetched_once': True}


def capture_original_members(group, path, acquisition, needed, existing_manifest=None):
    before = stamp(path.stat())
    assert before == acquisition['stat']
    wanted = needed | {group['manifest']['member']}
    found, seen, total = {}, {}, 0
    with tarfile.open(path, mode='r|' + group['format']) as archive:
        for member in archive:
            pure = PurePosixPath(member.name)
            assert member.isfile() and not pure.is_absolute() and '..' not in pure.parts
            assert str(pure) == member.name and member.name not in seen
            assert member.size >= 0
            seen[member.name] = member.size
            total += member.size
            assert total <= group['max_expanded_bytes']
            if member.name not in wanted:
                continue
            assert member.size <= MAX_CAPTURE_BYTES
            stream = archive.extractfile(member)
            assert stream is not None
            data = stream.read(member.size + 1)
            assert len(data) == member.size
            found[member.name] = data
    assert stamp(path.stat()) == before
    assert len(seen) == group['member_count'] and set(found) == wanted
    if group['expanded_member_bytes'] is not None:
        assert total == group['expanded_member_bytes']
    manifest_bytes = found[group['manifest']['member']]
    if group['manifest']['bytes'] is not None:
        assert len(manifest_bytes) == group['manifest']['bytes']
    assert hashlib.sha256(manifest_bytes).hexdigest() == group['manifest']['sha256']
    manifest = json.loads(manifest_bytes)
    assert group['manifest']['shape'] == 'files_dictionary'
    assert manifest['schema'] == group['manifest']['schema']
    table = manifest['files']
    assert isinstance(table, dict)
    assert set(table) == set(seen) - {group['manifest']['member']}
    assert all(seen[name] == entry['bytes'] for name, entry in table.items())
    assert total == len(manifest_bytes) + sum(entry['bytes'] for entry in table.values())
    for name in needed:
        assert len(found[name]) == table[name]['bytes']
        assert hashlib.sha256(found[name]).hexdigest() == table[name]['sha256']
    if existing_manifest is not None:
        previous_bytes, manifest_record = existing_manifest
        assert group['id'] == 'unit128_existing' and manifest_bytes == previous_bytes
    else:
        manifest_record = write_new('provenance/' + group['id'] + '/FILE_MANIFEST.json', manifest_bytes)
    return found, {**acquisition, 'group': group['id'], 'member_count': len(seen),
        'total_original_member_bytes': total, 'manifest': manifest_record,
        'captured_members': sorted(wanted), 'other_member_payloads_materialized_or_audited': False,
        'original_archive_fully_hashed': True, 'single_member_extraction_pass': True}


def finalize_choice(choice, pin):
    assert (choice['bytes'], choice['sha256']) == (pin['bytes'], pin['sha256'])
    path = choice['selected_path']
    if choice['selection'] == 'REUSE_EXISTING_SAME_PIN':
        old = choice['original_candidate']
        assert stamp(os.lstat(path)) == old['logical_lstat']
        assert stamp(os.stat(path)) == old['target_stat']
        choice['final_stat'] = old['target_stat']
    else:
        assert choice['selection'] == 'NEW_EXCLUSIVE_COPY_OF_ORIGINAL_PIN'
        assert stamp(os.stat(path)) == choice['new_file']['stat']
        choice['final_stat'] = choice['new_file']['stat']


try:
    assert isinstance(SOURCE_TEXT, str)
    assert not BASE.exists() and not BASE.is_symlink(), 'No automatic rerun; preserve the existing receiver and inspect its evidence.'
    rows = PIN['objects']
    assert len(rows) == len({r['module'] for r in rows}) == 13
    assert sum(r['bytes'] for r in rows) == 4445656
    assert sum(r['source']['bytes'] for r in rows) == 92222
    assert {r['provider'] for r in rows} == {'unit128_existing', 'nonradial15_Git_fallback', 'gate76_existing_Git_parts'}
    assert 'ImbalancedChen.PowerErrorBudget' not in {r['module'] for r in rows}
    assert 'ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall' not in {r['module'] for r in rows}
    free_before = shutil.disk_usage('/workspace').free
    assert free_before >= MIN_FREE_BYTES
    BASE.mkdir(mode=0o700, parents=False, exist_ok=False)
    created = True
    receiver_record = write_new('receiver.py', SOURCE_TEXT.encode())
    contract_record = write_new('PIN_CONTRACT.json', encode(PIN))
    stage('fixed-input-index-and-existing-Unit128-receipt')
    index_bytes = fetch_blob(PIN['input_index'])
    index = json.loads(index_bytes)
    index_record = write_new('provenance/NONEMPTY_EXISTING_INPUT_INDEX.json', index_bytes)
    assert set(index['new_branch_existing_objects']) == {r['module'] for r in rows}
    assert index['counts']['Unit_old_project_objects'] == 11
    assert index['counts']['Gate_old_object'] == index['counts']['Nonradial_old_object'] == 1
    for row in rows:
        original = index['new_branch_existing_objects'][row['module']]
        assert (row['bytes'], row['sha256']) == (original['object']['bytes'], original['object']['sha256'])
        assert row['object_member'] == original['object']['archive_member']
        assert row['P2_candidates'] == [x['path'] for x in original['recorded_host_paths'] if x['host'] == 'P2']
        source_pin = row['source']
        assert (source_pin['bytes'], source_pin['sha256'], source_pin['git_blob']) == (
            original['source']['bytes'], original['source']['sha256'], original['source']['derived_git_oid'])
        assert source_pin['member'] == original['source']['archive_member']
        expected_source_candidates = ([str(Path('/workspace/p2-9-20261125') /
            (row['module'].replace('.', '/') + '.lean'))] if row['P2_candidates'] else [])
        assert source_pin['P2_candidates'] == expected_source_candidates
        assert row['destination_relative'] == 'lib/lean/' + row['module'].replace('.', '/') + '.olean'
        assert row['source_destination_relative'] == 'sources/' + row['module'].replace('.', '/') + '.lean'
    receipt_pin = PIN['old18_receiver_receipt']
    prior_bytes, prior_record = read_fixed_existing(receipt_pin['path'], receipt_pin)
    prior = json.loads(prior_bytes)
    assert prior['status'] == 'PASS_EXACT_BYTES_ONLY_NOT_MATHEMATICAL_OR_ACTUAL_IMPORT_QUALIFICATION'
    assert prior['receiver']['git_blob'] == 'f20e1aae21a19d26aa9aa39f3912eb2d0640410b'
    assert prior['pin_contract']['git_blob'] == 'ec9396407e3ab379687ead798c78fa948f97868c'
    unit = next(g for g in PIN['archives'] if g['id'] == 'unit128_existing')
    old_unit = next(g for g in prior['archives'] if g['group'] == 'unit128')
    assert unit['existing_path'] == old_unit['path']
    assert unit['archive'] == {k: old_unit[k] for k in ('bytes', 'sha256')}
    assert unit['expected_original_stat'] == old_unit['archive_stat']
    assert unit['original_manifest_record'] == old_unit['manifest']
    original_manifest_pin = unit['original_manifest_record']
    unit_manifest_bytes, unit_manifest_record = read_fixed_existing(
        original_manifest_pin['path'], original_manifest_pin, original_manifest_pin['stat'])
    assert hashlib.sha256(unit_manifest_bytes).hexdigest() == unit['manifest']['sha256']
    unit_manifest = json.loads(unit_manifest_bytes)
    assert unit_manifest['schema'] == unit['manifest']['schema']
    for row in rows:
        if row['provider'] == 'unit128_existing':
            for pin, member in ((row, row['object_member']), (row['source'], row['source']['member'])):
                assert unit_manifest['files'][member] == {k: pin[k] for k in ('bytes', 'sha256')}
    gate_group = next(g for g in PIN['archives'] if g['id'] == 'gate76_existing_Git_parts')
    old_gate = index['qualification_groups']['gate_original_accepted_76_members']['archive_parts_record']
    assert gate_group['archive'] == {k: old_gate[k] for k in ('bytes', 'sha256')}
    assert gate_group['manifest']['sha256'] == old_gate['manifest_sha256']
    assert len(gate_group['parts']) == len(old_gate['parts'])
    for planned, old in zip(gate_group['parts'], old_gate['parts']):
        assert all(planned[k] == old[k] for k in ('index', 'bytes', 'sha256', 'git_blob'))
    ngroup = next(g for g in PIN['archives'] if g['id'] == 'nonradial15_Git_fallback')
    old_nonradial = index['qualification_groups']['nonradial_original_accepted_six']
    assert ngroup['archive'] == {k: old_nonradial['object_evidence_archive'][k] for k in ('bytes', 'sha256')}
    assert ngroup['parts'][0]['git_blob'] == old_nonradial['object_evidence_archive']['git_blob']
    assert ngroup['manifest']['sha256'] == old_nonradial['object_archive_manifest_sha256']

    stage('exact-old-P2-object-and-source-candidates')
    selected_objects, selected_sources, observations = {}, {}, {}
    for row in rows:
        module = row['module']
        object_choice, object_observations = select_old_candidate(row['P2_candidates'], row)
        source_choice, source_observations = select_old_candidate(row['source']['P2_candidates'], row['source'])
        observations[module] = {'objects': object_observations, 'sources': source_observations}
        if object_choice is not None:
            selected_objects[module] = object_choice
        if source_choice is not None:
            selected_sources[module] = source_choice

    archive_receipts = []
    for group in PIN['archives']:
        group_rows = [r for r in rows if r['provider'] == group['id']]
        needed = {r['object_member'] for r in group_rows if r['module'] not in selected_objects}
        needed |= {r['source']['member'] for r in group_rows if r['module'] not in selected_sources}
        if not needed:
            archive_receipts.append({'group': group['id'], 'status': 'NOT_OPENED_ALL_REQUIRED_MEMBERS_REUSED',
                'archive_downloads': 0, 'archive_extraction_passes': 0})
            continue
        stage('needed-original-members-' + group['id'])
        archive_path, acquisition = acquire_archive(group)
        existing_manifest = ((unit_manifest_bytes, unit_manifest_record)
            if group['id'] == 'unit128_existing' else None)
        captured, archive_receipt = capture_original_members(group, archive_path, acquisition, needed, existing_manifest)
        archive_receipts.append(archive_receipt)
        for row in group_rows:
            module = row['module']
            for selections, pin, member, destination in (
                (selected_objects, row, row['object_member'], row['destination_relative']),
                (selected_sources, row['source'], row['source']['member'], row['source_destination_relative'])):
                if module in selections:
                    continue
                data = captured.pop(member)
                actual = identity(data)
                assert (actual['bytes'], actual['sha256']) == (pin['bytes'], pin['sha256'])
                if pin.get('git_blob') is not None:
                    assert actual['git_blob'] == pin['git_blob']
                record = write_new(destination, data)
                selections[module] = {'selected_path': record['path'], 'selection': 'NEW_EXCLUSIVE_COPY_OF_ORIGINAL_PIN',
                    'bytes': pin['bytes'], 'sha256': pin['sha256'], 'new_file': record}
        assert set(captured) == {group['manifest']['member']}

    stage('final-continuity-and-exact-thirteen-byte-receipt')
    assert len(selected_objects) == len(selected_sources) == 13
    for row in rows:
        module = row['module']
        finalize_choice(selected_objects[module], row)
        finalize_choice(selected_sources[module], row['source'])
        selected_objects[module]['source'] = selected_sources[module]
        selected_objects[module]['provenance'] = {'input_index_blob': PIN['input_index']['git_blob'],
            'provider': row['provider'], 'object_member': row['object_member'],
            'source_member': row['source']['member'], 'source_git_blob': row['source']['git_blob'],
            'qualification_group': row['qualification_group'], 'old_owned_count_not_new_credit': row['old_owned_count']}
    for path, original in protected.items():
        assert stamp(os.lstat(path)) == original['logical_lstat']
        assert stamp(os.stat(path)) == original['target_stat']
    result = {'schema': 'p29_nonempty_P2_exact13_existing_byte_reception_v1',
        'status': 'PASS_EXACT_OLD_BYTES_ONLY_NOT_MATHEMATICAL_OR_ACTUAL_IMPORT_QUALIFICATION',
        'root': str(BASE), 'receiver': receiver_record, 'pin_contract': contract_record,
        'input_index': index_record, 'prior18_receipt': prior_record,
        'original_unit128_manifest': unit_manifest_record, 'selected_objects': selected_objects,
        'authorized_candidate_observations': observations, 'archives': archive_receipts,
        'downloads': downloads, 'existing_protected_files_unchanged': protected,
        'counts': {'objects': 13, 'source_files': 13, 'object_bytes': 4445656, 'source_bytes': 92222,
            'reused_existing_objects': sum(v['selection'] == 'REUSE_EXISTING_SAME_PIN' for v in selected_objects.values()),
            'reused_existing_sources': sum(v['selection'] == 'REUSE_EXISTING_SAME_PIN' for v in selected_sources.values()),
            'object_candidates_checked': sum(len(v['objects']) for v in observations.values()),
            'source_candidates_checked': sum(len(v['sources']) for v in observations.values()),
            'Unit_archive_downloads': 0, 'Git_raw_bytes_received': sum(v['bytes'] for v in downloads.values())},
        'capacity': {'free_bytes_before': free_before, 'minimum_free_bytes': MIN_FREE_BYTES,
            'requested_memory_mb': 512, 'requested_cpu_threads': 1, 'requested_timeout_seconds': 300,
            'maximum_captured_member_bytes': MAX_CAPTURE_BYTES},
        'scope': {'old58_modified': False, 'future_Omitted_output_read_or_written': False,
            'P3_Power_variant_introduced': False, 'different_candidate_overwritten': False,
            'unlisted_paths_scanned': False, 'global_absence_claim': False,
            'Lean_invocations': 0, 'normal_kernel_owned_replays': 0, 'new_proof_credit': 0,
            'actual_compiled_header_or_native_standard_graph_qualified': False,
            'next_stage': 'Use these exact selected paths in the single real downstream input binding.'},
        'events': events, 'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    raw = encode(result)
    assert len(raw) < MAX_STDOUT_BYTES
    write_new('BYTE_RECEPTION_RECEIPT.json', raw)
    print('P29_NONEMPTY_P2_BYTE_RECEPTION ' + json.dumps(result, sort_keys=True, separators=(',', ':')), flush=True)
except Exception as exc:
    failure = {'schema': 'p29_nonempty_P2_byte_receiver_first_failure_v1',
        'stage': current_stage, 'exception_type': type(exc).__name__, 'message': str(exc),
        'root': str(BASE), 'new_root_created': created, 'completed_downloads': downloads,
        'events': events, 'Lean_invocations': 0, 'new_proof_credit': 0,
        'automatic_retry_or_redownload': False}
    if created and not (BASE / 'FIRST_FAILURE.json').exists():
        write_new('FIRST_FAILURE.json', encode(failure))
    print('P29_NONEMPTY_P2_BYTE_RECEPTION_FAILURE ' + json.dumps(failure, sort_keys=True), flush=True)
    raise
