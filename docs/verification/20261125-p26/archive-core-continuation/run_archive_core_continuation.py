#!/usr/bin/env python3
"""Strict single-owner new Core or RowNumerics acceptance, reusing actual old receipts.
No old Core build, prerequisite rebuild, receipt relabeling or invented readiness.
This candidate is source-only until Root publishes and runs it.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-p26-core-continuation-v1')
P1_BASE = '298670f119d24874b719facb3ef756f1e01223a1'
PREFIX = 'docs/verification/20261125-p26/archive-core-continuation/'
MANIFEST = PREFIX + 'SOURCE_TARGETS.json'
MANIFEST_SHA = 'cfca56bd7bf9e7685f904e9cba3527dda2aaa43715f58d9c2ccc78e4ae7a35b8'
OWNER_ORDER = ['ImbalancedChen.P2OriginalSaving19ArchiveCore', 'ImbalancedChen.P2OriginalSaving19RowNumerics']
OWNERS = set(OWNER_ORDER)
FORBIDDEN_DEPENDENCIES = set(['ImbalancedChen.P2OriginalSaving19Archive', 'ImbalancedChen.P2OriginalSaving19Original28918', 'ImbalancedChen.P2OriginalSaving19OwnedSource', 'ImbalancedChen.P2OriginalSaving19PullingReuse'])
CATALOG_COUNT = 252
REVIEW_INPUT_PINS = {'docs/verification/20261125-p26/archive-core-continuation/reviews/archive-schema-SOURCE_MANIFEST.json': 'cc65afc9a2c9cf1bbeeb50ff65812daa327791cb018b6ba50e059851331b01e4', 'docs/verification/20261125-p26/archive-core-continuation/reviews/row-numerics-SOURCE_MANIFEST.json': '8ebb8ffb5e667a3c467c6957dd2f7325b1042836452fa8ad492312ed818c3ce5'}
LEGACY_GROUPS = {'v4_inputs': {'source_commit': '07826355aedef5a01e76c36ad304bc6b115f3c2b', 'driver_path': 'docs/verification/20261125-p26/archive-v4/verify/run_archive_v4_inputs.py', 'driver_sha256': 'c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75', 'manifest_path': 'docs/verification/20261125-p26/archive-v4/verify/SOURCE_TARGETS.json', 'manifest_sha256': '29819ebed6b1a1ef036fd49f86db4e546cca74d93a73aa30f69d858908131f43', 'manifest_schema': 'p26_archive_v4_strict_input_targets_v1', 'manifest_owner_count': 32, 'binding_schema': 'p26_archive_v4_strict_single_input_owner_v1', 'receipt_root': '/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1', 'owners': ['ImbalancedChen.P2OriginalSaving19PackedChars', 'ImbalancedChen.P2OriginalSaving19CharInputBridge', 'ImbalancedChen.P2OriginalSaving19SourceJsonCharInput', 'ImbalancedChen.P2OriginalSaving19ArchivePackedLoader', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData12', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData01', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData02', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData03', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData04', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData06', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData07', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData08', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData09', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData10', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData11', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData00', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData01', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData02', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData03', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData04', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData05', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData06', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData07', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData08', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData09', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData10', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData11', 'ImbalancedChen.P2OriginalSaving19ArchivePackedInputs'], 'known_receipt_pins': {'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00': {'BINDING.json': {'bytes': 21697, 'sha256': '5b4cb409b430e83fdf2834ac9f4948a736805f16436857cf7838cf7209291f4e'}, 'normal/ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00/NORMAL_PASS.json': {'bytes': 5726, 'sha256': '92f997e5be4c9c2c091605ab8b6fe45987cd42cababc5085b4b87a4241cf6548'}, 'audits/1eb9badbf232a244df0e/AUDIT_PLAN.json': {'bytes': 2789, 'sha256': '2c72e6696b460c324c6a205eb83097e45504fda8af821d34012d7c67bb1486a8'}, 'audits/1eb9badbf232a244df0e/lane-0/VALIDATION_RESULTS.json': {'bytes': 7142, 'sha256': '981ca645f277be084c889ca5e850c4ce7944c07da58e94a0a5387b7460152ef3'}, 'runs/attempt-00000/RESULT.json': {'bytes': 17625, 'sha256': '3a52c3dc0a41a5397ffd89867341bf4fac709e6160ce8afd200f36ea2ee681aa'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 20686, 'sha256': '0c4c74c3c0f04a1fc74062174241ba79ad38ea4c52e1423e813d0009c9b07ce6'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 20686, 'sha256': '0c4c74c3c0f04a1fc74062174241ba79ad38ea4c52e1423e813d0009c9b07ce6'}, 'runs/attempt-00000/LOADER_INPUTS_BEFORE.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}, 'runs/attempt-00000/LOADER_INPUTS_AFTER.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}}, 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12': {'BINDING.json': {'bytes': 21759, 'sha256': 'a80483d93629dce5a14887b13666e4f0842b1c1b110eebe89da90ea80877de1b'}, 'normal/ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12/NORMAL_PASS.json': {'bytes': 5727, 'sha256': '1aea9bd96c38538fb6ade59f44de90f2269340592d4b75412947718e75980585'}, 'audits/98dd3a568c9463943bfe/AUDIT_PLAN.json': {'bytes': 2789, 'sha256': 'b053cdd394256df8cb687c2f16dbf89f9365ded2478ca696b8f576b3e5e74953'}, 'audits/98dd3a568c9463943bfe/lane-0/VALIDATION_RESULTS.json': {'bytes': 7143, 'sha256': 'fdddbb3523e3cb1f8a715c44e2a6ee080c81986d08e03715dac4113f694d398a'}, 'runs/attempt-00000/RESULT.json': {'bytes': 17687, 'sha256': '452eff797d2736349fc2f6769a27916c574691b65511b3d32de9dd877f67cba9'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 20750, 'sha256': '42385f7d9b1465538ce6d50f289ad8a64720714e29fdbc5d5712ffaad722bbec'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 20750, 'sha256': '42385f7d9b1465538ce6d50f289ad8a64720714e29fdbc5d5712ffaad722bbec'}, 'runs/attempt-00000/LOADER_INPUTS_BEFORE.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}, 'runs/attempt-00000/LOADER_INPUTS_AFTER.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}}, 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData12': {'BINDING.json': {'bytes': 21809, 'sha256': 'f57abae176fad921434e20c0821ae84a75693190391527f134d65076e49d30c4'}, 'normal/ImbalancedChen.P2OriginalSaving19ArchiveMomentData12/NORMAL_PASS.json': {'bytes': 5699, 'sha256': 'f7646c6a2c5fb423aa900dc9a54742318efb1bdc60b6bbb3db827dded133f214'}, 'audits/2948a261ab46103e3c6c/AUDIT_PLAN.json': {'bytes': 2769, 'sha256': '838fedb542200a07abee4db0f951c35caad90aa4837f62cf9bf97d2c7d1ec9cf'}, 'audits/2948a261ab46103e3c6c/lane-0/VALIDATION_RESULTS.json': {'bytes': 7097, 'sha256': '6f2d7155ca03e3533a634c557f94ffced51c555eff1f6ac68d57af6991a1b52c'}, 'runs/attempt-00000/RESULT.json': {'bytes': 17735, 'sha256': '14a31c01d420dce50bbb23ae24fa0ffb65a6054f31a9ce5369e1ac4f9938cb89'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 20802, 'sha256': '53dca790a39ca1a3edf3c9bc860918a66649dd9e6a912323cc22c8f5aaa3da64'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 20802, 'sha256': '53dca790a39ca1a3edf3c9bc860918a66649dd9e6a912323cc22c8f5aaa3da64'}, 'runs/attempt-00000/LOADER_INPUTS_BEFORE.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}, 'runs/attempt-00000/LOADER_INPUTS_AFTER.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}}, 'ImbalancedChen.P2OriginalSaving19ArchivePackedLoader': {'BINDING.json': {'bytes': 21164, 'sha256': '5a511450fba145845c834b69019a58f267569e3516b51338ecf9bc1a3fd386db'}, 'normal/ImbalancedChen.P2OriginalSaving19ArchivePackedLoader/NORMAL_PASS.json': {'bytes': 5152, 'sha256': '165d2fd423c53ec63eb99add6e51986781c93050a1eb7c5a120841d2bdbe844a'}, 'audits/82f7e10b95ee76a19b58/AUDIT_PLAN.json': {'bytes': 2577, 'sha256': 'bfa799ba51bbbb71b56e3a4a2e0fcdcf503db8269d6d1c2198a9898fc5dde396'}, 'audits/82f7e10b95ee76a19b58/lane-0/VALIDATION_RESULTS.json': {'bytes': 6968, 'sha256': '47fab6e4dd1f7a5e2ff358ddb12498ee5e4a9bd0723a979183cfeb1b7cbe507b'}, 'runs/attempt-00000/RESULT.json': {'bytes': 17090, 'sha256': 'f824e2e9361c75a896b461c986445876a4b603acc643275ec5ee238ccb7e3ab3'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 19588, 'sha256': '5d71701012d4603b05906db30dd05b4d474b6a9711861917ecedd4f2354c4a83'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 19588, 'sha256': '5d71701012d4603b05906db30dd05b4d474b6a9711861917ecedd4f2354c4a83'}, 'runs/attempt-00000/LOADER_INPUTS_BEFORE.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}, 'runs/attempt-00000/LOADER_INPUTS_AFTER.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}}, 'ImbalancedChen.P2OriginalSaving19CharInputBridge': {'BINDING.json': {'bytes': 20665, 'sha256': '8341086f2073c02af7662a4ada576affd524ba4db00ed75b1db2fa25bbf0477e'}, 'normal/ImbalancedChen.P2OriginalSaving19CharInputBridge/NORMAL_PASS.json': {'bytes': 4567, 'sha256': 'bd12bfb830fc1017e7f5f1993c7a8f34cc9213c3e93b8aeccff67866470eba9d'}, 'audits/3539b6bc88b222670f1f/AUDIT_PLAN.json': {'bytes': 2361, 'sha256': 'ec097524f05903a273cfad078ee70c23c76f8ab3567cfbc04603b6f1f4b85f37'}, 'audits/3539b6bc88b222670f1f/lane-0/VALIDATION_RESULTS.json': {'bytes': 6756, 'sha256': 'ce30e5fd76f90bc6d357a405d23d671a3bb0087ff1c06d9d6af7cf165f04f0b9'}, 'runs/attempt-00000/RESULT.json': {'bytes': 16587, 'sha256': '6ce6ba666dc38f73b43d2a4071834629e571d0df01545279764d5d58516f6cf6'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 18541, 'sha256': 'a031926a87093dac148d02c4569fa31cb8aa9347386c536905ead461cf5acb93'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 18541, 'sha256': 'a031926a87093dac148d02c4569fa31cb8aa9347386c536905ead461cf5acb93'}, 'runs/attempt-00000/LOADER_INPUTS_BEFORE.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}, 'runs/attempt-00000/LOADER_INPUTS_AFTER.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}}, 'ImbalancedChen.P2OriginalSaving19PackedChars': {'BINDING.json': {'bytes': 20641, 'sha256': '8e257883a9f0315794a71bfb976dad01a05739e2230dacba0b6a02cdc107a33b'}, 'normal/ImbalancedChen.P2OriginalSaving19PackedChars/NORMAL_PASS.json': {'bytes': 4513, 'sha256': '8b51c29f5675171bd25e1e2c98d8d7a5f6cebf6b26eb6bb2d048f6c800388b3f'}, 'audits/3004ec20d4a5f670c252/AUDIT_PLAN.json': {'bytes': 2321, 'sha256': 'd50b03d90a764a7df30f0b2dbd87544ed9d6ede80d8d4138d5b0008313a88d5a'}, 'audits/3004ec20d4a5f670c252/lane-0/VALIDATION_RESULTS.json': {'bytes': 6670, 'sha256': '2af2381cdb25be01f917b9d2e986c9cabcbb871834d49506fbf9befb78ec5aa7'}, 'runs/attempt-00000/RESULT.json': {'bytes': 16559, 'sha256': 'e6828760b0ed9caedd5e11532e22a87c8d9d7399256d3f6c6fa2f47920c049e8'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 18517, 'sha256': 'c3db8e91e39599e50948d3fe2d6915c3d6ddcad7356d66ca834b2f02a01b54ed'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 18517, 'sha256': 'c3db8e91e39599e50948d3fe2d6915c3d6ddcad7356d66ca834b2f02a01b54ed'}, 'runs/attempt-00000/LOADER_INPUTS_BEFORE.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}, 'runs/attempt-00000/LOADER_INPUTS_AFTER.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}}, 'ImbalancedChen.P2OriginalSaving19SourceJsonCharInput': {'BINDING.json': {'bytes': 21653, 'sha256': 'a774a7917c4211f197467ee257c14906d892dc52c35eafb33c9e5b02a0bd4b1f'}, 'normal/ImbalancedChen.P2OriginalSaving19SourceJsonCharInput/NORMAL_PASS.json': {'bytes': 5683, 'sha256': 'b38b05905e75a922a54fa0f784e89c74d27261b71916d4dea8526452b6abc837'}, 'audits/dbe93a715b249f62f6be/AUDIT_PLAN.json': {'bytes': 2759, 'sha256': '1181f30f3617e47bc985c6bf9ada37d429d51203cc918d63710f3ec8760c97e6'}, 'audits/dbe93a715b249f62f6be/lane-0/VALIDATION_RESULTS.json': {'bytes': 7092, 'sha256': 'f3690b077a95bd4e53509093c926515a4fd67eb42068e443117c35d8e26ffe3c'}, 'runs/attempt-00000/RESULT.json': {'bytes': 17579, 'sha256': 'c895e5a2817aa79a6dbd2f982ce98a0ac75478244bb445b5e06cec17e397d478'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 20627, 'sha256': '58f1b6143583b220804ad99724149a7dc4730b306943baadf9efc2cb02fa0d4b'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 20627, 'sha256': '58f1b6143583b220804ad99724149a7dc4730b306943baadf9efc2cb02fa0d4b'}, 'runs/attempt-00000/LOADER_INPUTS_BEFORE.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}, 'runs/attempt-00000/LOADER_INPUTS_AFTER.json': {'bytes': 13803, 'sha256': '37238f7105a323b4cc8bcc0ccf7573e715f639f15ca2dfa61e2dddd142e1db23'}}}}, 'schema': {'source_commit': '77c23a2a530ce8d34ec79f88181817072024d4a9', 'driver_path': 'docs/verification/20261125-p26/independent-owner-verify/run_independent_owner.py', 'driver_sha256': 'a2f9528662278b6aa994fb160013b5d0c2f5d762a455dec536afa90004b8443e', 'manifest_path': 'docs/verification/20261125-p26/independent-owner-verify/SOURCE_TARGETS.json', 'manifest_sha256': '1366f95d28811c303f3a7d0f0079f1335752365251148cd041062a948a36746d', 'manifest_schema': 'p26_independent_strict_single_owner_targets_v1', 'manifest_owner_count': 5, 'binding_schema': 'p26_independent_strict_single_owner_v1', 'receipt_root': '/workspace/p1-complete-proof/20261125-p26-independent-owners-v1', 'owners': ['ImbalancedChen.P2OriginalSaving19ArchiveSchema'], 'known_receipt_pins': {}}}
CORE = 'ImbalancedChen.P2OriginalSaving19ArchiveCore'
CORE_PREIMAGE = 'df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182'
ARCHIVE_SHA = 'f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOL_SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
CONFIG_OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'
CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
EVIDENCE_PINS = {CONFIG_OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614', CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'}
CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')




def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)


def check_configs(project, configuration, d):
    need(all((project / p).is_file() and not (project / p).is_symlink() for p in CONFIGS) and
         {p: d.fingerprint(project / p) for p in CONFIGS} == configuration and
         not os.path.lexists(project / 'lakefile.lean'),
         'configuration differs from the selected pinned basis')


def source_origin(source_commit, module, h):
    path = h.module_path(module)
    return {'commit': source_commit, 'path': path}


def source_slot(project, module, payload, h, manifest):
    path = project / h.module_path(module)
    need(path.parent.is_dir() and not path.parent.is_symlink() and not path.is_symlink(),
         'target or target directory is a symlink or missing directory: ' + str(path))
    if not os.path.lexists(path):
        return {'exists': False, 'sha256': None, 'bytes': None, 'action': 'CREATE_NEW_ABSENT'}
    need(path.is_file(), 'target is not a regular file: ' + str(path))
    data = path.read_bytes()
    digest = sha(data)
    allowed = {sha(payload)} | set(manifest['modules'][module]['known_preimages'])
    need(digest in allowed, 'UNKNOWN_SOURCE_PREIMAGE ' + json.dumps(
        {'module': module, 'actual_sha256': digest, 'allowed_sha256': sorted(allowed)}, sort_keys=True))
    return {'exists': True, 'sha256': digest, 'bytes': len(data),
            'action': 'ALREADY_AFTER_NOOP' if digest == sha(payload) else 'INSTALL_BACKED_UP_PREIMAGE'}


def validate_manifest(manifest, module, h):
    need(manifest.get('schema') == 'p26_archive_core_continuation_targets_v1' and
         manifest.get('owners') == OWNER_ORDER and manifest.get('owner_count') == 2 and
         set(manifest.get('modules', {})) == OWNERS and module in OWNERS and
         manifest.get('review_input_pins') == REVIEW_INPUT_PINS and
         manifest.get('legacy_groups') == LEGACY_GROUPS and
         manifest.get('production_archive_allowed_sha256') == [ARCHIVE_SHA] and
         manifest.get('old_core_224_exports_credit_transferred') is False and
         manifest.get('old_receipts_relabeled') is False and
         manifest.get('archive_complete') is False,
         'continuation target scope or reviewed manifest differs')
    catalog = manifest.get('all_project_source_catalog', {})
    need(isinstance(catalog, dict) and len(catalog) == CATALOG_COUNT and
         OWNERS <= set(catalog) and not (FORBIDDEN_DEPENDENCIES & set(catalog)),
         'frozen continuation source catalog differs or includes a closed-guard owner')
    for m, row in catalog.items():
        need(row.get('path') == h.module_path(m) and row.get('source_path') == h.module_path(m) and
             re.fullmatch(r'[0-9a-f]{64}', row.get('sha256', '')) is not None and
             type(row.get('bytes')) is int and row['bytes'] > 0 and
             isinstance(row.get('imports'), list) and all(isinstance(x, str) for x in row['imports']),
             'frozen continuation project source differs: ' + m)
    graph = {m: [x for x in row['imports'] if x.startswith('ImbalancedChen.')]
             for m, row in catalog.items()}
    for m, row in manifest['modules'].items():
        closure = h.closure(graph, [m])
        expected_groups = ['v4_inputs', 'schema'] if m == CORE else ['schema']
        expected_owners = [x for group in expected_groups for x in LEGACY_GROUPS[group]['owners']]
        need(all(row.get(k) == catalog[m][k] for k in catalog[m]) and
             row.get('known_preimages') == ([CORE_PREIMAGE] if m == CORE else []) and
             row.get('target_absent_allowed') == (m != CORE) and
             row.get('project_closure_count') == (251 if m == CORE else 6) == len(closure) and
             row.get('required_legacy_groups') == expected_groups and
             row.get('required_legacy_owners') == expected_owners and
             set(expected_owners) <= closure and
             row.get('raw_fixture_reads_required') == (m == CORE),
             'continuation owner preimage, closure or legacy prerequisites differ: ' + m)
    need(len(manifest.get('original_loader_inputs', [])) == 26,
         'continuation must retain all original loader inputs')


def production_archive_snapshot(project, d, manifest):
    path = project / 'ImbalancedChen/P2OriginalSaving19Archive.lean'
    need(path.is_file() and not path.is_symlink(), 'production Archive is not a regular source file')
    record = {'path': str(path), **d.fingerprint(path)}
    need(record['sha256'] in manifest['production_archive_allowed_sha256'],
         'production Archive is not an explicitly reviewed preimage/target; this runner never changes it')
    return record


def loader_input_snapshot(project, d, expected):
    records, differences = [], []
    for family, stem, suffix in (
        ('geometry', 'eighth-third-minorant-extension-20261009-a23-s23_low-', '-cell.witness.json'),
        ('moment', 'eighth-third-moment-refinement-20261009-a23-low-', '.witness.json')):
        for cell in range(13):
            relative = '../goldbach-research/' + stem + f'{cell:02d}' + suffix
            path = project / relative
            logical = os.path.abspath(path)
            try:
                resolved = path.resolve(strict=True)
                need(path.is_file(), 'loader input is not a regular file')
                record = {'family': family, 'cell': cell, 'loader_relative_path': relative,
                          'loader_absolute_path': logical, 'resolved_actual_path': str(resolved),
                          **d.fingerprint(path)}
                need(path.resolve(strict=True) == resolved, 'loader input target changed while hashing')
                records.append(record)
            except (OSError, RuntimeError) as error:
                differences.append({'family': family, 'cell': cell, 'loader_relative_path': relative,
                                    'loader_absolute_path': logical, 'error': str(error)})
    need(not differences, 'ARCHIVE_LOADER_INPUTS_UNAVAILABLE ' + json.dumps(differences, sort_keys=True))
    need(len(records) == 26 and len({r['loader_absolute_path'] for r in records}) == 26,
         'Archive loader input scope differs')
    need(records == expected, 'ARCHIVE_ORIGINAL_BYTES_DIFFER_FROM_REVIEWED_26_INPUTS')
    return records


def legacy_inputs(args, raw, h, manifest, selected):
    """Pin old driver/manifests and old Git sources without claiming receipt readiness."""
    result = {}
    catalog = manifest['all_project_source_catalog']
    for name in manifest['modules'][args.module]['required_legacy_groups']:
        desc = LEGACY_GROUPS[name]
        commit = desc['source_commit']
        for kind in ('driver', 'manifest'):
            data = git(args.source_repo, commit, desc[kind + '_path'])
            need(sha(data) == desc[kind + '_sha256'],
                 'actual legacy source evidence differs: ' + name + '/' + kind)
            raw['legacy-' + name + '-' + kind + ('.py' if kind == 'driver' else '.json')] = data
        old_manifest = json.loads(raw['legacy-' + name + '-manifest.json'])
        need(old_manifest['schema'] == desc['manifest_schema'] and
             old_manifest['owner_count'] == desc['manifest_owner_count'] and
             all(m in old_manifest['owners'] for m in desc['owners']) and
             CORE not in desc['owners'], 'legacy manifest scope differs: ' + name)
        old_catalog = old_manifest['all_project_source_catalog']
        old_graph = {m: [x for x in row['imports'] if x.startswith('ImbalancedChen.')]
                     for m, row in old_catalog.items()}
        old_closure = h.closure(old_graph, desc['owners'])
        need(old_closure <= selected, 'legacy closure is outside selected consumer: ' + name)
        differences = []
        for m in sorted(old_closure):
            row = old_catalog[m]
            data = git(args.source_repo, commit, h.module_path(m))
            imports = h.imports(data)
            need(sha(data) == row['sha256'] and len(data) == row['bytes'] and imports == row['imports'],
                 'legacy catalog is not its actual original Git source: ' + m)
            current = catalog[m]
            if any(current[k] != row[k] for k in ('bytes', 'sha256', 'imports')):
                differences.append({'module': m, 'legacy_commit': commit, 'legacy': row,
                                    'consumer_commit': args.source_commit, 'consumer': current})
        need(not differences, 'LEGACY_CROSS_COMMIT_SOURCE_OR_IMPORT_MISMATCH ' +
             json.dumps(differences, sort_keys=True))
        if name == 'v4_inputs':
            need(old_manifest['original_loader_inputs'] == manifest['original_loader_inputs'] and
                 old_manifest['production_archive_allowed_sha256'] == [ARCHIVE_SHA],
                 'legacy raw input or production Archive binding differs')
        result[name] = {'descriptor': desc, 'manifest': old_manifest,
                        'graph': old_graph, 'catalog': old_catalog}
    return result


def inputs(args):
    need(re.fullmatch(r'[0-9a-f]{40}', args.source_commit) is not None,
         'source-commit must be a full lowercase Git SHA')
    need(subprocess.check_output(['git', 'cat-file', '-t', args.source_commit],
                                 cwd=args.source_repo).strip() == b'commit', 'source commit unavailable')
    need(subprocess.run(['git', 'merge-base', '--is-ancestor', P1_BASE, args.source_commit],
                        cwd=args.source_repo, check=False).returncode == 0,
         'source commit must descend from the reviewed P1 baseline')
    raw = {API_PATH: git(args.source_repo, API_COMMIT, API_PATH)}
    need(sha(raw[API_PATH]) == API_SHA, 'published Batch13 API pin differs')
    api = types.ModuleType('published_batch13_primitives')
    api.__file__ = '<pinned Git object: ' + API_PATH + '>'
    exec(compile(raw[API_PATH], api.__file__, 'exec'), api.__dict__)
    need(api.PROJECT == PROJECT and api.REPO == REPO and api.TOOLS == TOOL_SOURCE,
         'published helper environment differs')
    for path, digest in api.PINS.items():
        raw[path] = git(args.source_repo, TOOL_SOURCE, path)
        need(sha(raw[path]) == digest, 'unchanged helper pin differs: ' + path)
    for path, digest in EVIDENCE_PINS.items():
        raw[path] = git(args.source_repo, P1_BASE, path)
        need(sha(raw[path]) == digest, 'accepted configuration evidence differs: ' + path)
    h, ops, d = (api.load(raw[api.HELPER], 'batch5'), api.load(raw[api.OPS], 'batch6'),
                 api.load(raw[api.PRIMITIVES], 'snapshot_primitives'))
    for path, digest in REVIEW_INPUT_PINS.items():
        raw[path] = git(args.source_repo, args.source_commit, path)
        need(sha(raw[path]) == digest, 'reviewed Archive source manifest or public contract changed: ' + path)
    raw[MANIFEST] = git(args.source_repo, args.source_commit, MANIFEST)
    need(sha(raw[MANIFEST]) == MANIFEST_SHA, 'independent-owner strict target manifest pin differs')
    manifest = json.loads(raw[MANIFEST])
    validate_manifest(manifest, args.module, h)
    catalog = manifest['all_project_source_catalog']
    catalog_graph = {m: [x for x in row['imports'] if x.startswith('ImbalancedChen.')]
                     for m, row in catalog.items()}
    selected = h.closure(catalog_graph, [args.module])
    required = manifest['modules'][args.module]['required_legacy_owners']
    checked = h.closure(catalog_graph, [args.module, *required])
    all_graph, all_sources, payload = {}, {}, None
    for m in sorted(checked):
        origin = source_origin(args.source_commit, m, h)
        data = git(args.source_repo, origin['commit'], origin['path'])
        row = catalog[m]
        imports = h.imports(data)
        need(sha(data) == row['sha256'] and len(data) == row['bytes'] and imports == row['imports'],
             'reviewed project owner/dependency differs from frozen catalog: ' + m)
        all_sources[m] = sha(data)
        all_graph[m] = [x for x in imports if x.startswith('ImbalancedChen.')]
        if m == args.module:
            payload = data
            raw[origin['path']] = data
    graph = {m: all_graph[m] for m in sorted(selected)}
    sources = {m: all_sources[m] for m in sorted(selected)}
    need(payload is not None and len(graph) == manifest['modules'][args.module]['project_closure_count'] and
         not (FORBIDDEN_DEPENDENCIES & set(graph)), 'selected owner missing, wrong closure size, or forbidden production/data owner imported')
    h.closure(graph, [args.module])
    legacy = legacy_inputs(args, raw, h, manifest, selected)
    slot = source_slot(args.project, args.module, payload, h, manifest)
    need(args.module != CORE or slot['exists'], 'Core requires the known existing old v2 or exact new source slot')
    differences = []
    for m in sorted(selected - {args.module}):
        actual_path = args.project / h.module_path(m)
        data = actual_path.read_bytes() if actual_path.is_file() and not actual_path.is_symlink() else None
        actual_sha = sha(data) if data is not None else None
        actual_imports = [x for x in h.imports(data) if x.startswith('ImbalancedChen.')] if data is not None else None
        if actual_sha != sources[m] or actual_imports != graph[m]:
            differences.append({'module': m, 'expected_source_commit': args.source_commit,
                                'expected_sha256': sources[m], 'actual_sha256': actual_sha,
                                'expected_imports': graph[m], 'actual_imports': actual_imports})
    need(not differences, 'COHERENT_P1_DEPENDENCY_CLOSURE_MISMATCH ' + json.dumps(differences, sort_keys=True))
    source_config = {}
    for path in CONFIGS:
        raw[path] = git(args.source_repo, args.source_commit, path)
        source_config[path] = {'bytes': len(raw[path]), 'sha256': sha(raw[path])}
    observed = json.loads(raw[CONFIG_OBSERVATION])['configs']
    review = json.loads(raw[CONFIG_REVIEW])
    runtime_config = review['runtime_configuration_bindings']
    need(review['source_configuration_bindings'] == source_config and
         runtime_config == {p: {k: observed[p][k] for k in ('bytes', 'sha256')} for p in CONFIGS} and
         all(observed[p]['exists'] and not observed[p]['is_symlink'] for p in CONFIGS) and
         not observed['lakefile.lean']['exists'] and not observed['lakefile.lean']['is_symlink'],
         'configuration observation/review binding differs')
    check_configs(args.project, source_config if args.config_basis == 'source' else runtime_config, d)
    if args.config_basis == 'runtime':
        need(d.runtime_binding(h) == review['existing_runtime_bindings'], 'accepted existing runtime differs')
    need(all(sha((args.project / h.module_path(m)).read_bytes()) == digest for m, digest in h.FOUR_ROOTS.items()),
         'protected original roots changed')
    production = production_archive_snapshot(args.project, d, manifest)
    loader_inputs = (loader_input_snapshot(args.project, d, manifest['original_loader_inputs'])
                     if manifest['modules'][args.module]['raw_fixture_reads_required'] else None)
    provenance = {
        'schema': 'p26_core_continuation_strict_single_owner_v1',
        'source_commit': args.source_commit, 'reviewed_p1_baseline': P1_BASE, 'module': args.module,
        'manifest_path': MANIFEST, 'manifest_sha256': sha(raw[MANIFEST]), 'manifest_owner_count': 2,
        'target_source_sha256': sources[args.module],
        'allowed_existing_target_sha256': sorted({sources[args.module]} |
            set(manifest['modules'][args.module]['known_preimages'])),
        'all_project_sources_from_one_commit': True,
        'project_source_origins': {m: source_origin(args.source_commit, m, h) for m in sorted(sources)},
        'project_sources_after_single_target_install': sources,
        'source_closure_count': len(sources), 'project_import_graph': graph,
        'retained_dependencies_only_checked_for_readiness': sorted(selected - OWNERS - set(required)),
        'required_legacy_owners': required,
        'legacy_source_commits': {g: LEGACY_GROUPS[g]['source_commit'] for g in legacy},
        'legacy_receipts_validated_during_readonly_preflight': False,
        'production_archive_source': production, 'loader_inputs': loader_inputs,
        'raw_fixture_reads_required': manifest['modules'][args.module]['raw_fixture_reads_required'],
        'loader_input_identity_scope': 'all_26_original_paths_bytes_sha' if loader_inputs is not None else 'not_applicable_no_raw_file_reads',
        'selected_owner_only': True, 'old_core_224_exports_credit_transferred': False,
        'old_receipts_relabeled': False, 'archive_complete': False, 'only_cell00_proved': False,
        'proved_parse_cells': [], 'archive_shape_or_row_guards_proved': False,
        'actual_row_numeric_or_floor_claim': False, 'whole_P1_complete': False, 'whole_P2_complete': False,
    }
    return types.SimpleNamespace(api=api, h=h, ops=ops, d=d, raw=raw, payload=payload,
        graph=graph, sources=sources, provenance=provenance, all_graph=all_graph,
        all_sources=all_sources, manifest=manifest, legacy=legacy, source_config=source_config,
        runtime_config=runtime_config, slot=slot, source_commit=args.source_commit,
        source_repo=args.source_repo, module=args.module)


def binding(spec):
    return {**spec.provenance, 'project': str(PROJECT), 'api_commit': API_COMMIT,
            'tooling_commit': TOOL_SOURCE, 'input_sha256': {p: sha(b) for p, b in spec.raw.items()},
            'driver_sha256': sha(Path(__file__).read_bytes()), 'configuration_basis': 'runtime',
            'source_configuration': spec.source_config, 'runtime_configuration': spec.runtime_config,
            'runtime': spec.d.runtime_binding(spec.h)}


def install_one(spec, run):
    h, d, m = spec.h, spec.d, spec.module
    slot = source_slot(PROJECT, m, spec.payload, h, spec.manifest)
    need(m != CORE or slot['exists'], 'Core cannot be created in an absent source slot')
    d.save(run / 'SOURCE_PREFLIGHT_BEFORE.json', slot)
    path = h.module_path(m)
    if not slot['exists']:
        d.write_frozen(PROJECT / path, spec.payload)
        records = [{'module': m, 'path': path, 'actual_before_sha256': None,
                    'actual_after_sha256': sha((PROJECT / path).read_bytes()),
                    'mutated': True, 'action': 'CREATE_NEW_ABSENT'}]
    else:
        updates = [{'module': m, 'path': path, 'before_sha256': slot['sha256'],
                    'after_sha256': sha(spec.payload), 'cloud_source_mutation_required': m == CORE}]
        payloads = {path: spec.payload}
        spec.api.preflight_sources(PROJECT, updates, payloads, h)
        records = h.install_sources(PROJECT, updates, payloads, run / 'source-backups')
    need(sha((PROJECT / path).read_bytes()) == spec.sources[m], 'selected owner installation differs')
    d.save(run / 'SOURCE_INSTALL.json', {**spec.provenance, 'sources': records})


def check_installed(spec, runtime):
    check_configs(PROJECT, spec.runtime_config, spec.d)
    graph, actual = spec.h.project_graph(PROJECT, [spec.module])
    need(graph == spec.graph and {m: row['sha256'] for m, row in actual.items()} == spec.sources,
         'installed project source context changed')
    need(spec.d.runtime_binding(spec.h) == runtime, 'existing runtime changed')
    spec.h.check_roots()
    need(production_archive_snapshot(PROJECT, spec.d, spec.manifest) ==
         spec.provenance['production_archive_source'],
         'unselected production Archive source changed during input acceptance')


def require_legacy_acceptance(spec, frozen, loader_current):
    """Validate every prior owner under its real old commit. Never build/audit one."""
    api, h, d = spec.api, spec.h, spec.d
    summaries = []
    for group_name in spec.manifest['modules'][spec.module]['required_legacy_groups']:
        group = spec.legacy[group_name]
        desc, old_manifest = group['descriptor'], group['manifest']
        old_commit = desc['source_commit']
        for module in desc['owners']:
            need(module != CORE, 'old ArchiveCore can never supply continuation credit')
            root = Path(desc['receipt_root']) / old_commit / module
            need(root.is_dir() and not root.is_symlink(), 'LEGACY_OWNER_NOT_READY ' + str(root))
            pinned = desc['known_receipt_pins'].get(module, {})
            for relative, expected in pinned.items():
                path = root / relative
                need(path.is_file() and not path.is_symlink() and d.fingerprint(path) == expected,
                     'known original receipt changed or missing: ' + str(path))
            prior_path = root / 'BINDING.json'
            need(prior_path.is_file() and not prior_path.is_symlink(),
                 'legacy original BINDING missing or not regular: ' + module)
            prior = api.read_json(prior_path)
            closure = h.closure(group['graph'], [module])
            graph = {m: group['graph'][m] for m in sorted(closure)}
            sources = {m: group['catalog'][m]['sha256'] for m in sorted(closure)}
            origins = {m: source_origin(old_commit, m, h) for m in sorted(closure)}
            need(prior.get('schema') == desc['binding_schema'] and
                 prior.get('source_commit') == old_commit and prior.get('module') == module and
                 prior.get('manifest_path') == desc['manifest_path'] and
                 prior.get('manifest_sha256') == desc['manifest_sha256'] and
                 prior.get('manifest_owner_count') == desc['manifest_owner_count'] and
                 prior.get('driver_sha256') == desc['driver_sha256'] and
                 prior.get('source_closure_count') == len(closure) and
                 prior.get('target_source_sha256') == sources[module] and
                 prior.get('project_import_graph') == graph and
                 prior.get('project_sources_after_single_target_install') == sources and
                 prior.get('project_source_origins') == origins and
                 prior.get('required_preceding_strict_owners') ==
                    old_manifest['modules'][module]['required_accepted_owners'] and
                 all(prior[k] == frozen[k] for k in ('project', 'runtime', 'runtime_configuration',
                    'source_configuration', 'configuration_basis', 'api_commit', 'tooling_commit')),
                 'legacy original binding or accepted runtime differs: ' + module)
            need({m: spec.sources[m] for m in closure} == sources and
                 {m: spec.graph[m] for m in closure} == graph,
                 'legacy source/import closure differs from consumer: ' + module)
            if group_name == 'v4_inputs':
                need(prior.get('loader_inputs') == loader_current == frozen['loader_inputs'] and
                     prior.get('production_archive_source') == frozen['production_archive_source'] and
                     prior.get('old_core_224_exports_credit_transferred') is False,
                     'legacy raw26 or unselected Archive source differs: ' + module)
            else:
                need(prior.get('raw_fixture_reads_required') is False and
                     prior.get('old_receipts_relabeled') is False,
                     'legacy Schema receipt scope differs')
            normal_path = root / 'normal' / module / 'NORMAL_PASS.json'
            need(normal_path.is_file() and not normal_path.is_symlink(),
                 'legacy normal receipt missing or not regular: ' + module)
            normal = api.read_json(normal_path)
            old_current = api.context(old_commit, PROJECT, module, graph, sources, h, d)
            api.normal_valid(old_commit, PROJECT, module, normal, old_current, h, d)
            accepted, audits = set(), []
            for directory in sorted((root / 'audits').glob('*')):
                need(directory.is_dir() and not directory.is_symlink() and
                     (directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                     'legacy partial audit requires inspection: ' + str(directory))
                plan_path = directory / 'AUDIT_PLAN.json'
                validation_path = directory / 'lane-0/VALIDATION_RESULTS.json'
                accepted.update(api.audit_valid(old_commit, PROJECT, directory,
                    api.read_json(plan_path), {module: normal}, graph, sources, h, d))
                audits.append({'plan': {'path': str(plan_path), **d.fingerprint(plan_path)},
                    'validation': {'path': str(validation_path), **d.fingerprint(validation_path)}})
            need(accepted == {module}, 'LEGACY_OWNER_LACKS_FULL_STRICT_ACCEPTANCE ' + module)
            successful = []
            for result_path in sorted((root / 'runs').glob('attempt-*/RESULT.json')):
                result = api.read_json(result_path)
                if result.get('status') != api.PASS or result.get('error') is not None:
                    continue
                need(result.get('schema') == desc['binding_schema'] and
                     result.get('source_commit') == old_commit and result.get('module') == module and
                     result.get('manifest_path') == desc['manifest_path'] and
                     result.get('manifest_sha256') == desc['manifest_sha256'] and
                     result.get('normal_passed') == [module] and
                     result.get('accepted_owners') == [module] and
                     result.get('all_selected_owners_accepted') is True and
                     result.get('accepted_for_actual_P1_context_only') is True and
                     result.get('project_source_origins') == origins and
                     result.get('project_sources_after_single_target_install') == sources and
                     result.get('project_import_graph') == graph and
                     all(result.get(k) is False for k in ('archive_complete', 'only_cell00_proved',
                         'archive_shape_or_row_guards_proved', 'whole_P1_complete', 'whole_P2_complete')),
                     'legacy original wrapper completion differs: ' + module)
                evidence = [result_path]
                for name in ('P1_DEPENDENCY_CONTEXT_BEFORE.json', 'P1_DEPENDENCY_CONTEXT_AFTER.json'):
                    path = result_path.parent / name
                    need(api.read_json(path)['context'] == old_current,
                         'legacy stored source/object/trace/config/runtime context changed: ' + module)
                    evidence.append(path)
                if group_name == 'v4_inputs':
                    need(result.get('loader_inputs') == loader_current and
                         result.get('production_archive_source') == frozen['production_archive_source'] and
                         result.get('old_core_224_exports_credit_transferred') is False,
                         'legacy wrapper raw26/Archive scope differs')
                    for name in ('LOADER_INPUTS_BEFORE.json', 'LOADER_INPUTS_AFTER.json'):
                        path = result_path.parent / name
                        need(api.read_json(path) == loader_current,
                             'legacy original raw26 path/bytes/hash snapshot differs: ' + module)
                        evidence.append(path)
                else:
                    need(result.get('old_receipts_relabeled') is False,
                         'legacy Schema completion has wrong receipt scope')
                successful.append([{'path': str(p), **d.fingerprint(p)} for p in evidence])
            need(successful, 'LEGACY_OWNER_LACKS_SUCCESSFUL_WRAPPER_CONTEXT ' + module)
            consumer_view = api.context(spec.source_commit, PROJECT, module, spec.graph, spec.sources, h, d)
            need({k: v for k, v in old_current.items() if k != 'source_commit'} ==
                 {k: v for k, v in consumer_view.items() if k != 'source_commit'},
                 'legacy/new consumer source/object/trace/config/runtime equivalence failed: ' + module)
            summaries.append({'legacy_group': group_name, 'legacy_owner': module,
                'legacy_source_commit': old_commit, 'consumer_source_commit': spec.source_commit,
                'receipt_root': str(root), 'binding': {'path': str(prior_path), **d.fingerprint(prior_path)},
                'normal_receipt': {'path': str(normal_path), **d.fingerprint(normal_path)},
                'audit_receipts': audits, 'successful_wrapper_runs': successful,
                'legacy_context_under_actual_commit': old_current,
                'consumer_view_of_same_closure': consumer_view,
                'legacy_source_plus_five_outputs': normal['source_plus_five_outputs'],
                'receipt_relabeled': False, 'recompiled': False, 'reaudited': False})
    need([r['legacy_owner'] for r in summaries] ==
         spec.provenance['required_legacy_owners'], 'legacy owner inventory incomplete')
    return summaries


def worker(spec, root, run):
    api, h, ops, d, m = spec.api, spec.h, spec.ops, spec.d, spec.module
    d.verify_lane(h)
    frozen = api.read_json(root / 'BINDING.json')
    need(frozen == binding(spec), 'serialized worker binding changed')
    passed, accepted, error, before = {}, set(), None, None
    legacy_before, loader_before = None, None
    try:
        if spec.provenance['raw_fixture_reads_required']:
            loader_before = loader_input_snapshot(PROJECT, d, spec.manifest['original_loader_inputs'])
            d.save(run / 'LOADER_INPUTS_BEFORE.json', loader_before)
            need(loader_before == frozen['loader_inputs'], 'raw26 changed before Core acceptance')
        legacy_before = require_legacy_acceptance(spec, frozen, loader_before)
        d.save(run / 'LEGACY_ACCEPTANCE_BEFORE.json', legacy_before)
        install_one(spec, run)
        check_installed(spec, frozen['runtime'])
        before = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_BEFORE.json', {'provenance': spec.provenance, 'context': before})
        passed[m] = api.normal_one(spec.source_commit, PROJECT, root, m, spec.graph, spec.sources, h, ops, d)
        api.audit(spec.source_commit, PROJECT, root, passed, spec.graph, spec.sources, h, ops, d, run, accepted)
    except Exception as caught:
        error = str(caught)
        ops.emit('P26_CORE_CONTINUATION_HELD_OR_FAILED', module=m, reason=error)
    try:
        check_installed(spec, frozen['runtime'])
        after = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_AFTER.json', {'provenance': spec.provenance, 'context': after})
        need(before is not None and after == before,
             'source/object/trace/configuration/runtime context changed during acceptance')
    except Exception as caught:
        message = str(caught)
        d.save(run / 'CONTEXT_AFTER_ERROR.json', {'error': message})
        error = message if error is None else error + '; POST_CONTEXT: ' + message
    loader_after = None
    try:
        if spec.provenance['raw_fixture_reads_required']:
            loader_after = loader_input_snapshot(PROJECT, d, spec.manifest['original_loader_inputs'])
            d.save(run / 'LOADER_INPUTS_AFTER.json', loader_after)
            need(loader_before == loader_after == frozen['loader_inputs'], 'raw26 changed during Core acceptance')
        legacy_after = require_legacy_acceptance(spec, frozen, loader_after)
        d.save(run / 'LEGACY_ACCEPTANCE_AFTER.json', legacy_after)
        need(legacy_before is not None and legacy_before == legacy_after,
             'original legacy receipts or context changed during selected acceptance')
    except Exception as caught:
        message = str(caught)
        d.save(run / 'LEGACY_OR_LOADER_AFTER_ERROR.json', {'error': message})
        error = message if error is None else error + '; POST_LEGACY_OR_RAW: ' + message
    complete = accepted == {m} and error is None
    result = {**spec.provenance, 'status': api.PASS if complete else 'HELD_OR_FAILED',
        'normal_passed': sorted(passed), 'accepted_owners': sorted(accepted), 'error': error,
        'accepted_for_actual_P1_context_only': complete, 'all_selected_owners_accepted': complete,
        'archive_complete': False, 'only_cell00_proved': False, 'proved_parse_cells': [],
        'archive_shape_or_row_guards_proved': False, 'actual_row_numeric_or_floor_claim': False,
        'old_core_224_exports_credit_transferred': False, 'old_receipts_relabeled': False}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0 if complete else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--module', choices=sorted(OWNERS), required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--config-basis', choices=('runtime', 'source'), default='runtime')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    args.source_repo, args.project = args.source_repo.resolve(), args.project.resolve()
    need(args.config_basis == 'runtime' or (args.check and args.project != PROJECT),
         'source configuration basis is limited to read-only local checks')
    if args.run:
        need(args.source_repo == REPO and args.project == PROJECT,
             'execution is restricted to the existing P1 cloud project/repository')
    spec = inputs(args)
    api, h, ops, d = spec.api, spec.h, spec.ops, spec.d
    root = ROOT / args.source_commit / args.module
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        print(json.dumps({**spec.provenance, 'target_installation_preflight': spec.slot,
              'status': 'SOURCE_CONFIG_ONLY_NOT_CLOUD_READY' if args.config_basis == 'source' else
                        'READ_ONLY_SOURCE_RUNTIME_CHECK_PASS_NOT_ACCEPTANCE',
              'source_installation_performed': False, 'cloud_compilation_performed': False}, sort_keys=True))
        return 0
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid run directory')
        return worker(spec, root, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(REPO)
    d.save(root / 'BINDING.json', binding(spec))
    for path, data in spec.raw.items():
        destination = ('source-configuration/' + path if path in CONFIGS else
                       'review-inputs/' + path if path in REVIEW_INPUT_PINS else
                       'e9.py' if path == api.E9 else Path(path).name)
        d.write_frozen(root / 'inputs' / destination, data)
    executed = root / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--source-commit', args.source_commit,
             '--module', args.module, '--run', '--inside-lane', '--run-dir', str(run)]
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(REPO)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty Git source worktree changed')

if __name__ == '__main__':
    raise SystemExit(main())
