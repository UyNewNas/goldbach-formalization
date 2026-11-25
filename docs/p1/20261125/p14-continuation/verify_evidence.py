#!/usr/bin/env python3
"""Offline consistency check of the fixed P1.4 checkpoints; never rebuild.

Checks the fixed archive, reported cloud commands, complete owned inventory,
cross-receipt source/object fingerprints and current target source bytes. The
archive does not contain compiled objects: this is not a local kernel replay.
"""
import argparse
import base64
import collections
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile

ARCHIVE_SHA = '61a6c9eb309baea57a2ef5e7fda4d2473131552e432e1f1601f0982eb38c8c9e'
AUDIT_TEMPLATE_SHA = '535d5e697ff5c719dbbd90ff04e358be7071cdc9a0b145cf4d3edf2fff002248'
AUDIT_BODY_SHA = 'dcc7d001d2e82fd9a4ff9fd2d0ad2b1fb8b7223bc1f3e8cf8aa0505644017d92'
AUDIT_RUNNER_SHA = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'
GROUPS = {
    'p14_new': ['P1FifthGrid400UnitBoxPartition', 'P1OriginalFifthRawBoxGateSoundness',
                'P1OriginalFifthCorrelatedRawBoxGates', 'P1OriginalFifthCorrelatedDecodedGates'],
    'p15_shared_repairs_reused': ['P1ActualVariableFifthGlobalPositiveLimit',
        'P1OriginalFifthMiddleShellFiniteBudget', 'P1OriginalFifthMovingScaleLimit',
        'P1OriginalVariableFourthActiveMeshCover', 'P1OriginalVariableFourthFullActivePositiveLimit',
        'P1OriginalVariableFourthUntruncatedDomination'],
    'prior_fourth_integral_reused': ['P1OriginalFourthUntruncatedIntegral'],
}
EXPECTED = {'ImbalancedChen.' + m: group for group, modules in GROUPS.items() for m in modules}
CHECKPOINTS = {
    '01': {'sha256': ARCHIVE_SHA, 'bytes': 266688, 'files': 502, 'groups': GROUPS,
           'shared_root': 'p15_shared', 'shared_exit_code': 0, 'shared_failures': [],
           'owned': 312, 'public': 301},
    '02': {'sha256': 'fb92a04371670d9f04b35420c0cfa7ac6afefd039eae1bca2f9ae0e584924ef5',
           'bytes': 196276, 'files': 309,
           'groups': {
               'p14_new': ['P1FifthRawKeyThirdOwnerPersistence',
                   'P1OriginalFifthFiniteTableRefinementConstructor', 'P1OriginalFifthPositiveBufferSchedule'],
               'p15_shared_repairs_reused': ['P1FifthMiddleNormalizedPointwise',
                   'P1OriginalVariableFourthFullActiveIntegral', 'P1OriginalVariableFourthFullSmallSource']},
           'shared_root': 'p15_shared_round02', 'shared_exit_code': 1,
           'shared_failures': ['ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit'],
           'owned': 113, 'public': 112},
    '03': {'sha256': 'b538605b5dfad63279f9a59a2e771afcf0c1cc658b63578115e8dce0c5e09bbe',
     'bytes': 325052,
     'files': 725,
     'groups': {'p14_new': ['P5OriginalCommonRefinedSeedHull'],
                'p15_shared_repairs_reused': ['P1ActualVariableFifthSmallLastGeometry',
                                              'P1ActualVariableFifthTailPointwise',
                                              'P1ActualVariableFifthUniformTail',
                                              'P1ActualVariableFifthUntruncatedDomination',
                                              'P1OriginalFifthMiddleShellMovingLimit',
                                              'P1OriginalFifthMiddleShellRemainderSplit',
                                              'P1OriginalFifthUniformSmallRemainder',
                                              'P1OriginalFifthUntruncatedIntegral',
                                              'P1OriginalFifthZeroCutoffLimit',
                                              'P1OriginalVariableFourthFullSmallRemainder',
                                              'P1OriginalVariableFourthFullSourceAssembly',
                                              'P1OriginalVariableFourthFullSourceMean']},
     'shared_runs': [{'path': 'p15_shared_round03/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSourceAssembly'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthSmallLastGeometry',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round03/runs/attempt-00001',
                      'accepted': ['ImbalancedChen.P1OriginalFifthMiddleShellRemainderSplit'],
                      'failures': [],
                      'exit_code': 0},
                     {'path': 'p15_shared_round04/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1ActualVariableFifthSmallLastGeometry'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean',
                                   'ImbalancedChen.P1ActualVariableFifthTailPointwise',
                                   'ImbalancedChen.P1ActualVariableFifthUniformTail',
                                   'ImbalancedChen.P1ActualVariableFifthUntruncatedDomination',
                                   'ImbalancedChen.P1OriginalFifthUniformSmallRemainder',
                                   'ImbalancedChen.P1OriginalFifthUntruncatedIntegral',
                                   'ImbalancedChen.P1OriginalFifthZeroCutoffLimit',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSourceMean'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round05/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder',
                                   'ImbalancedChen.P1ActualVariableFifthTailPointwise',
                                   'ImbalancedChen.P1OriginalFifthUniformSmallRemainder'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean',
                                   'ImbalancedChen.P1ActualVariableFifthUniformTail',
                                   'ImbalancedChen.P1ActualVariableFifthUntruncatedDomination',
                                   'ImbalancedChen.P1OriginalFifthUntruncatedIntegral',
                                   'ImbalancedChen.P1OriginalFifthZeroCutoffLimit',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSourceMean'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round06/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1OriginalVariableFourthFullSourceMean',
                                   'ImbalancedChen.P1ActualVariableFifthUniformTail',
                                   'ImbalancedChen.P1OriginalFifthZeroCutoffLimit',
                                   'ImbalancedChen.P1OriginalFifthUntruncatedIntegral'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean',
                                   'ImbalancedChen.P1ActualVariableFifthUntruncatedDomination'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round07/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1ActualVariableFifthUntruncatedDomination'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean'],
                      'exit_code': 1}],
     'shared_failures': ['ImbalancedChen.P1ActualVariableFifthFullMean'],
     'excluded_failed_owners': ['ImbalancedChen.P1HistoricalFifthNpyFrame',
                                'ImbalancedChen.P1HistoricalFifthOriginalByteLiteral',
                                'ImbalancedChen.P1ActualVariableFifthFullMean'],
     'owned': 197,
     'public': 176},
    '04': {'sealed': True,
     'sha256': '76eff073f9d8f6e97e2d704f25bba1424c6cdb2f57c74fd259e9b4a59a0ec93b',
     'bytes': 227004, 'files': 386, 'owned': 310, 'public': 299,
     'paired_owner_lane': 'p14/bytes-frame-retry/c6d6d5eed2b4a4c5a288645864e781716c7e5771/audits/df6e4be1191b00ae1b5e/lane-0',
     'paired_owners': ['ImbalancedChen.P1HistoricalFifthNpyFrame',
                       'ImbalancedChen.P1HistoricalFifthOriginalByteLiteral'],
     'cancelled_unaccepted_owner': 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange',
     'cancelled_partial_root': 'p14/typed-archive-range/4d294de6b2a3128a6fb281426e4f204a8514beaa',
     'cancelled_source_commit': '4d294de6b2a3128a6fb281426e4f204a8514beaa',
     'cancelled_driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
     'observer_path': 'docs/p1/20261125/p14-continuation/evidence/checkpoint-04-observations/job_1cea508c1b3745b694cb5ff810334b66/OBSERVER.json',
     'observer_sha256': '738497c0645c5b1f61e688fe93ce71e12fb89ebfa8ff90e61c92b8a043ed69f5',
     'groups': {
         'p14_new': ['P1HistoricalFifthOriginalByteLiteral', 'P1HistoricalFifthNpyFrame',
                     'P1FifthUnitBoxGainDecomposition', 'P1OriginalFifthActualOwnerGateCrossing',
                     'P1HistoricalFifthTypedArchiveShape'],
         'p15_shared_repairs_reused': ['P1ActualVariableFifthFullMean']},
     'shared_runs': [{'path': 'p15_shared_round08/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1ActualVariableFifthFullMean'],
                      'failures': [], 'exit_code': 0}],
     'shared_failures': [],
     'excluded_failed_owners': ['ImbalancedChen.P1FifthUnitBoxLiteralGainLower',
                                'ImbalancedChen.P1FifthMask5RawOwnerLicence',
                                'ImbalancedChen.P1FifthMask6RawOwnerLicence',
                                'ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge'],
     'pipeline_paths': [
         'p14_pipeline/c6d6d5eed2b4a4c5a288645864e781716c7e5771/PIPELINE_RESULT.json',
         'p14_pipeline/439a6189094202185336fd70d652f8f5544b93e9/PIPELINE_RESULT.json'],
     'retained_review': {
         'path': 'p15_shared_round08_review/retained-29295f6a7196c523b525104f864da20035cc15d9.json',
         'sha256': 'a5dbdb1865f95e1b886cc1ce1fd7f84e3a5e09ae631eaa3e4e3b04fb289a8f31'}},
    '05': {'sealed': True,
     'sha256': '1e22c13ae22dffc8faa3db38958c30e62733fdbbbdd2b2d25b9f5f46e7fb1e5e',
     'bytes': 165232, 'files': 295, 'owned': 71, 'public': 66,
     'paired_owner_lane': 'p14/owner-expression-retry/8237d0b698ca01153a7e2823510cf67148083c0a/audits/6b2c547a584b52b0f129/lane-0',
     'paired_owners': ['ImbalancedChen.P1FifthUnitBoxLiteralGainLower',
                       'ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge'],
     'groups': {'p14_new': ['P1FifthUnitBoxLiteralGainLower',
                           'P1OriginalFifthMovingMeshFubiniBridge',
                           'P1OriginalFifthLiteralKernelModulus',
                           'P1HistoricalFifthTypedArchiveRangeCore',
                           'P1HistoricalFifthTypedArchiveRangeBlock000']},
     'shared_runs': [], 'shared_failures': [],
     'excluded_failed_owners': ['ImbalancedChen.P1FifthCheckedUnitBoxWholeGain',
                                'ImbalancedChen.P1FifthMask5RawOwnerLicence',
                                'ImbalancedChen.P1FifthMask6RawOwnerLicence',
                                'ImbalancedChen.P1FifthPositivePartActualOwner',
                                'ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics',
                                'ImbalancedChen.P1OriginalFifthActualOwnerCrossingVolume',
                                'ImbalancedChen.P1OriginalFifthMovingMeshFiberBands',
                                'ImbalancedChen.P5OldFifthExact64ChildTiling'],
     'protected_roots': {
         'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
         'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
         'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
         'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
     'pipelines': [{
         'path': 'p14_pipeline/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
         'source_commit': '8237d0b698ca01153a7e2823510cf67148083c0a',
         'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
         'completed_stages': ['owner-expression-retry', 'npy-positional',
                              'unit-literal-consumers', 'owner-fibre-volume'],
         'held_stages': ['owner-gamma-volume', 'owner-crossing-sections', 'owner-b13-error',
                         'adopted-owner-bank', 'uniform-adopted-error', 'indexed-owner-archive',
                         'indexed-bank-error', 'buffer-owner-geometry']}, {
         'path': 'p14_pipeline/61566a18871e26b80cced0a4408944294d793071/PIPELINE_RESULT.json',
         'source_commit': '61566a18871e26b80cced0a4408944294d793071',
         'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
         'completed_stages': ['typed-range-core', 'typed-range-block000'], 'held_stages': []}]},
    '06': {'sealed': True,
     'sha256': '82d632652726995425ec992c3ac022f91f0ea2202cfeb5cff38b6c9338b480af',
     'bytes': 186308, 'files': 262, 'owned': 161, 'public': 137,
     'reused_pipeline_sha256': '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01',
     'paired_owner_lanes': [
         {'path': 'p14/owner-license-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/audits/4c8eec7354e1bd355c52/lane-0',
          'owners': ['ImbalancedChen.P1FifthMask5RawOwnerLicence',
                     'ImbalancedChen.P1FifthMask6RawOwnerLicence']},
         {'path': 'p14/literal-positive-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/audits/6577907e9be7d5bc526f/lane-0',
          'owners': ['ImbalancedChen.P1FifthCheckedUnitBoxWholeGain',
                     'ImbalancedChen.P1FifthPositivePartActualOwner']}],
     'groups': {'p14_new': ['P1FifthMask5RawOwnerLicence', 'P1FifthMask6RawOwnerLicence',
                           'P1FifthPositivePartActualOwner', 'P1FifthCheckedUnitBoxWholeGain',
                           'P1HistoricalFifthNpyPositionalSemantics',
                           'P1OriginalFifthActualOwnerCrossingVolume']},
     'shared_runs': [], 'shared_failures': [],
     'excluded_failed_owners': ['ImbalancedChen.P1OriginalFifthMovingMeshFiberBands',
                                'ImbalancedChen.P5OldFifthExact64ChildTiling',
                                'ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume'],
     'protected_roots': {
         'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
         'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
         'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
         'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
     'pipelines': [{
         'path': 'p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
         'source_commit': 'c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
         'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
         'completed_stages': ['owner-license-retry', 'literal-positive-retry', 'npy-positional-retry'],
         'held_stages': []}, {
         'path': 'p14_pipeline/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
         'source_commit': 'a700772dbddaa09df497590c7d1b54d6e488f812',
         'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
         'completed_stages': ['owner-fibre-volume-retry', 'exact64-tiling-retry', 'owner-gamma-volume'],
         'held_stages': ['owner-crossing-sections', 'owner-b13-error', 'adopted-owner-bank',
                         'uniform-adopted-error', 'indexed-owner-archive', 'indexed-bank-error',
                         'buffer-owner-geometry', 'common-policy-inputs']}]},
    '07': {'sealed': True,
     'sha256': '52c1d11e5ec42319890c8a8d3b62e233b0687cd7b24c293c365db4aeb24da327',
     'bytes': 112376, 'files': 201, 'owned': 37, 'public': 37,
     'single_owner_lanes': {
         'p14/typed-range-blocks-001-010/5ba405bc08aaef020868399aa62a429ca4281eda/audits/e927b101b183182d50f0/lane-0':
             ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks001010'],
         'p14/frozen-upper-surrogate/8682bf05456060c0677bdddb210df38f33229817/audits/5a6d25d9d34ce9111a9b/lane-0':
             ['ImbalancedChen.P5OldFifthFrozenUpperSurrogate'],
         'p14/typed-base-core/e4dfe229579714b69c302e667d88649a14b58a0c/audits/7634b125f412af9a6cfc/lane-0':
             ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryCore'],
         'p14/typed-base-block000/e4dfe229579714b69c302e667d88649a14b58a0c/audits/0a29729e31b4c3137c3a/lane-0':
             ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlock000']},
     'groups': {'p14_new': ['P1HistoricalFifthTypedArchiveRangeBlocks001010',
                           'P5OldFifthFrozenUpperSurrogate', 'P1HistoricalFifthTypedBaseGeometryCore',
                           'P1HistoricalFifthTypedBaseGeometryBlock000']},
     'shared_runs': [], 'shared_failures': [],
     'excluded_failed_owners': ['ImbalancedChen.P5OldFifthFrozenGapConcavity'],
     'protected_roots': {
         'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
         'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
         'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
         'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
     'prior_pipeline_paths': [
         'p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
         'p14_pipeline/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json'],
     'prior_pipeline_sha256': [
         '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01',
         'f999d0bd6b1b7ba4c4a8eb7712ccbb0f3ca44891430c7a4fcfc100bcb91ecd09'],
     'pipelines': [{
         'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-001-010/PIPELINE_RESULT.json',
         'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
         'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
         'completed_stages': ['typed-range-blocks-001-010'], 'held_stages': []}, {
         'path': 'p14_pipeline/8682bf05456060c0677bdddb210df38f33229817/PIPELINE_RESULT.json',
         'source_commit': '8682bf05456060c0677bdddb210df38f33229817',
         'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
         'completed_stages': ['frozen-upper-surrogate', 'frozen-gap-concavity'],
         'held_stages': ['one-coordinate-chord']}, {
         'path': 'p14_pipeline/e4dfe229579714b69c302e667d88649a14b58a0c/PIPELINE_RESULT.json',
         'source_commit': 'e4dfe229579714b69c302e667d88649a14b58a0c',
         'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
         'completed_stages': ['typed-base-core', 'typed-base-block000'], 'held_stages': []}]},
    '08': {'sealed': True,
     'sha256': '29cd648a03ce97bb329b8614a81392302c1988dc26ed126f6e2f816d8e179e87',
     'bytes': 188588,
     'files': 415,
     'owned': 142,
     'public': 134,
     'single_owner_lanes': {'p14/exact64-disjoint-retry/93501ca11da26d233922739b6aece9987a877d93/audits/85fc878aa372f27517e6/lane-0': ['ImbalancedChen.P5OldFifthExact64ChildTiling'],
                            'p14/frozen-gap-expression-retry/c247cbcf8bfcf307a4898e3520e900da41148662/audits/43901c56533243dd29c0/lane-0': ['ImbalancedChen.P5OldFifthFrozenGapConcavity'],
                            'p14/owner-fibre-cast-retry/93501ca11da26d233922739b6aece9987a877d93/audits/4392cc0ecfe589510ec4/lane-0': ['ImbalancedChen.P1OriginalFifthMovingMeshFiberBands'],
                            'p14/owner-gamma-beta-retry/89db42762b5f303602608587b3d610cd7ebe9a54/audits/4dea4f5c50c0a18c511b/lane-0': ['ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume'],
                            'p14/typed-base-blocks-001-010/649440b8436a3a94cabb096a56385307056f6dcc/audits/7f054a497d0eb876b739/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks001010'],
                            'p14/typed-range-blocks-011-020/5ba405bc08aaef020868399aa62a429ca4281eda/audits/985dc9ec8dfb11b10741/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks011020'],
                            'p14/typed-range-blocks-021-030/5ba405bc08aaef020868399aa62a429ca4281eda/audits/0fdaaf0a48ec43daa240/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks021030']},
     'groups': {'p14_new': ['P1OriginalFifthMovingMeshFiberBands',
                            'P5OldFifthExact64ChildTiling',
                            'P1HistoricalFifthTypedArchiveRangeBlocks011020',
                            'P1HistoricalFifthTypedArchiveRangeBlocks021030',
                            'P5OldFifthFrozenGapConcavity',
                            'P1HistoricalFifthTypedBaseGeometryBlocks001010',
                            'P1OriginalFifthGammaRateOwnerVolume']},
     'shared_runs': [],
     'shared_failures': [],
     'excluded_failed_owners': ['ImbalancedChen.P1FifthMask5NamedParent1Owner',
                                'ImbalancedChen.P1FifthMask6NamedParent0Owner',
                                'ImbalancedChen.P1OriginalFifthActualCrossingSections',
                                'ImbalancedChen.P5OldFifthOneCoordinateVertexChord'],
     'protected_roots': {'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
                         'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
                         'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
                         'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
     'reuse_locations': {'c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b': {'checkpoint': '06',
                                                                      'path': 'p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                                                      'sha256': '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01'},
                         'a700772dbddaa09df497590c7d1b54d6e488f812': {'checkpoint': '06',
                                                                      'path': 'p14_pipeline/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                                                      'sha256': 'f999d0bd6b1b7ba4c4a8eb7712ccbb0f3ca44891430c7a4fcfc100bcb91ecd09'},
                         '8682bf05456060c0677bdddb210df38f33229817': {'checkpoint': '07',
                                                                      'path': 'p14_pipeline/8682bf05456060c0677bdddb210df38f33229817/PIPELINE_RESULT.json',
                                                                      'sha256': '0fbac892f53285b6caf2f1d665e18f5b24794df12dd77fbb47765d47beacdb96'},
                         '93501ca11da26d233922739b6aece9987a877d93': {'checkpoint': '08',
                                                                      'path': 'p14_pipeline/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                                                      'sha256': '3fa68feb2f6070286165883499f7ac9150f150f08b01644712c3f3694df2ee2c'}},
     'pipelines': [{'path': 'p14_pipeline/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                    'sha256': '3fa68feb2f6070286165883499f7ac9150f150f08b01644712c3f3694df2ee2c',
                    'source_commit': '93501ca11da26d233922739b6aece9987a877d93',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['owner-fibre-cast-retry',
                                         'exact64-disjoint-retry',
                                         'owner-gamma-expression-retry'],
                    'held_stages': ['one-coordinate-chord',
                                    'owner-crossing-sections',
                                    'owner-b13-error',
                                    'adopted-owner-bank',
                                    'uniform-adopted-error',
                                    'indexed-owner-archive',
                                    'indexed-bank-error',
                                    'buffer-owner-geometry',
                                    'common-policy-inputs'],
                    'reused_sources': ['c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                                       'a700772dbddaa09df497590c7d1b54d6e488f812',
                                       '8682bf05456060c0677bdddb210df38f33229817']},
                   {'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-011-030/PIPELINE_RESULT.json',
                    'sha256': 'ca3b1bef32e657788b14f7dca698e6c41761905b487378ef73279fac512883b0',
                    'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['typed-range-blocks-011-020', 'typed-range-blocks-021-030'],
                    'held_stages': [],
                    'reused_sources': []},
                   {'path': 'p14_pipeline/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json',
                    'sha256': '4f38ec268ec5c0baff349e612e4a4c93ca0ee024a8699222622ef2ee2db60c38',
                    'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['frozen-gap-expression-retry',
                                         'named-parent0-owner',
                                         'named-parent1-owner',
                                         'one-coordinate-chord'],
                    'held_stages': ['named-parents-concrete-j5',
                                    'named-parent-actual-integral',
                                    'five-coordinate-tree',
                                    'barycentric',
                                    'child-gap-integral'],
                    'reused_sources': ['c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                                       'a700772dbddaa09df497590c7d1b54d6e488f812',
                                       '8682bf05456060c0677bdddb210df38f33229817',
                                       '93501ca11da26d233922739b6aece9987a877d93']},
                   {'path': 'p14_pipeline/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-001-010/PIPELINE_RESULT.json',
                    'sha256': '16ccdeab8e6ad0672e1890da75a4dddf0b833849f602915c2f6e10120059e0f9',
                    'source_commit': '649440b8436a3a94cabb096a56385307056f6dcc',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['typed-base-blocks-001-010'],
                    'held_stages': [],
                    'reused_sources': []},
                   {'path': 'p14_pipeline/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json',
                    'sha256': '6b57261b2316f51a376174d747b9b92b0cf172ce30e5deb1eb0673cd5a1301e9',
                    'source_commit': '89db42762b5f303602608587b3d610cd7ebe9a54',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['owner-gamma-beta-retry', 'owner-crossing-sections'],
                    'held_stages': ['owner-b13-error',
                                    'adopted-owner-bank',
                                    'uniform-adopted-error',
                                    'indexed-owner-archive',
                                    'indexed-bank-error',
                                    'buffer-owner-geometry',
                                    'common-policy-inputs'],
                    'reused_sources': ['c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                                       'a700772dbddaa09df497590c7d1b54d6e488f812',
                                       '93501ca11da26d233922739b6aece9987a877d93']}],
     'failed_attempts': [{'source_commit': '93501ca11da26d233922739b6aece9987a877d93',
                          'stage': 'owner-gamma-expression-retry',
                          'module': 'ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume',
                          'source_sha256': 'c70b10a85e14426d2266f9287298c1aea44cb5d7a16494f6d9c81fcb29bb2060',
                          'project_error_count': 2,
                          'reported_error_sections': 2},
                         {'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                          'stage': 'named-parent0-owner',
                          'module': 'ImbalancedChen.P1FifthMask6NamedParent0Owner',
                          'source_sha256': 'ed66da17c8badd078e7660758a2f452da2c62aac7c6c5aa3ec51a37e7c399990',
                          'project_error_count': 3,
                          'reported_error_sections': 3},
                         {'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                          'stage': 'named-parent1-owner',
                          'module': 'ImbalancedChen.P1FifthMask5NamedParent1Owner',
                          'source_sha256': 'f3c532a3eb33638e059ce2473f77e52162dfe02048e2a31073e37a546f22e9d6',
                          'project_error_count': 3,
                          'reported_error_sections': 3},
                         {'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                          'stage': 'one-coordinate-chord',
                          'module': 'ImbalancedChen.P5OldFifthOneCoordinateVertexChord',
                          'source_sha256': '9322c3ffb8b2da54a5833c97424627ac2298c35e8f0878d1f710348c0017da2d',
                          'project_error_count': 5,
                          'reported_error_sections': 5},
                         {'source_commit': '89db42762b5f303602608587b3d610cd7ebe9a54',
                          'stage': 'owner-crossing-sections',
                          'module': 'ImbalancedChen.P1OriginalFifthActualCrossingSections',
                          'source_sha256': 'e3327e62af26b957159a6a959a2fbb914a615ff16566f2cf8afde7bad1cdb092',
                          'project_error_count': 24,
                          'reported_error_sections': 12}]},
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
BUILT = re.compile(r'^\s*[✔⚠ℹ]\ufe0f?\s+\[[^\]\r\n]+\]\s+Built\s+'
                   r'(ImbalancedChen(?:\.[A-Za-z0-9_]+)+)(?::olean)?(?=\s|$)', re.M)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def checkpoint04_observation(repo):
    """Read the fixed cancelled task's verbatim MCP payloads, not proof receipts."""
    config = CHECKPOINTS['04']
    path = repo / config['observer_path']
    raw = path.read_bytes()
    need(sha(raw) == config['observer_sha256'], 'checkpoint04 observer manifest binding')
    observer = json.loads(raw)
    task_id = 'job_1cea508c1b3745b694cb5ff810334b66'
    need(observer['schema'] == 'p14_mcp_task_observer_transport_v1' and
         observer['task_id'] == task_id and observer['counts_as_acceptance'] is False and
         observer['whole_P1_4_complete'] is False, 'checkpoint04 observer scope')
    names = ['get_task.json', 'read_task_output-00000000.json', 'read_task_output-00032768.json']
    need([r['path'] for r in observer['files']] == names, 'checkpoint04 observer files')
    payloads = {}
    for row in observer['files']:
        data = (path.parent / row['path']).read_bytes()
        need(sha(data) == row['sha256'] and len(data) == row['bytes'], 'checkpoint04 MCP payload hash')
        payloads[row['path']] = json.loads(data)
        need(row['request']['task_id'] == task_id, 'checkpoint04 MCP request identity')
    metadata = payloads[names[0]]
    need(metadata['task_id'] == task_id and metadata['status'] == 'cancelled' and
         metadata['cancel_requested'] is True and metadata['exit_code'] == -9 and
         metadata['finished_at'] is not None and not metadata['output_truncated'] and
         metadata['runtime_seconds'] < metadata['timeout_seconds'], 'checkpoint04 cancellation outcome')
    need("source='" + config['cancelled_source_commit'] + "'" in metadata['command'],
         'checkpoint04 cancelled task source binding')
    chunks, offset = [], 0
    for name in names[1:]:
        page = payloads[name]
        data = base64.b64decode(page['data_base64'], validate=True)
        need(page['task_id'] == task_id and page['offset'] == offset and
             page['bytes'] == len(data) and page['next_offset'] == offset + len(data) and
             data.decode() == page['output'] and not page['output_truncated'], 'checkpoint04 output pagination')
        chunks.append(data)
        offset += len(data)
    stdout = b''.join(chunks)
    need(page['eof'] is True and observer['eof'] is True and not observer['output_truncated'] and
         len(stdout) == metadata['output_bytes'] == observer['stdout_bytes'] == 32861 and
         sha(stdout) == observer['stdout_sha256'], 'checkpoint04 complete observed stdout')
    events = [json.loads(line) for line in stdout.decode().splitlines() if line.startswith('{')]
    module = config['cancelled_unaccepted_owner']
    need(sum(e.get('batch6') == 'NORMAL_START' and e.get('module') == module for e in events) == 1,
         'checkpoint04 Range normal-start observation')
    need(not any(e.get('batch6') == 'PROJECT_ERROR' and module.replace('.', '/') + '.lean' in
                 e.get('text', '') for e in events), 'checkpoint04 Range proof diagnostic appeared')
    return metadata, events


def verify(archive, repo, checkpoint='01'):
    config = CHECKPOINTS[checkpoint]
    need(checkpoint not in ('04', '05', '06', '07', '08') or config['sealed'],
         'checkpoint ' + checkpoint + ' is unsealed: await terminal receipts, export and fixed archive/count pins')
    groups = config['groups']
    expected = {'ImbalancedChen.' + m: group for group, modules in groups.items() for m in modules}
    raw = archive.read_bytes()
    need(len(raw) == config['bytes'] and sha(raw) == config['sha256'], 'checkpoint ' + checkpoint + ' archive differs')
    files = {}
    with tarfile.open(archive, 'r:xz') as tar:
        for member in tar.getmembers():
            path = PurePosixPath(member.name)
            need(not path.is_absolute() and '..' not in path.parts, 'unsafe archive path')
            need(member.isfile() or member.isdir(), 'archive contains a nonregular entry')
            if member.isfile():
                need(member.name not in files, 'duplicate archive file')
                files[member.name] = tar.extractfile(member).read()
    get = lambda path: json.loads(files[str(path)])
    manifest = get('EXPORT_MANIFEST.json')
    need(manifest['schema'] == 'p14_receipt_export_v1' and not manifest['whole_P1_4_complete'], 'export scope')
    need(len(manifest['files']) == config['files'], 'export file count')
    if checkpoint in ('02', '03', '04', '05', '06', '07', '08'):
        predecessor = {'02': '01', '03': '02', '04': '03', '05': '04', '06': '05', '07': '06', '08': '07'}[checkpoint]
        need(manifest['checkpoint'] == checkpoint and
             manifest['prior_checkpoint_sha256'] == CHECKPOINTS[predecessor]['sha256'], 'checkpoint predecessor binding')
    originals = {}
    for row in manifest['files']:
        data = files[row['path']]
        need(len(data) == row['bytes'] and sha(data) == row['sha256'], 'export hash: ' + row['path'])
        need(row['original_path'] not in originals, 'duplicate original receipt path')
        originals[row['original_path']] = row['path']
    need(set(files) == {r['path'] for r in manifest['files']} | {'EXPORT_MANIFEST.json'}, 'unlisted archive file')
    partial_report, partial_missing_git_after = None, []
    if checkpoint == '04':
        cancelled_metadata, observed_events = checkpoint04_observation(repo)
        partial_root = config['cancelled_partial_root']
        need(config['cancelled_unaccepted_owner'] not in expected, 'cancelled owner counted as accepted')
        need(any(p.startswith(partial_root + '/') for p in files), 'cancelled Range partial evidence missing')
        need(not any(p.startswith(partial_root + '/') and
             (p.endswith('/NORMAL_PASS.json') or p.endswith('/VALIDATION_RESULTS.json') or
              re.search(r'/runs/attempt-[0-9]{5}/RESULT\.json$', p)) for p in files),
             'cancelled Range unexpectedly has completion/acceptance receipts; inspect originals')
    git_pairs = [p for p in files if p.endswith('/GIT_BEFORE.json')]
    for path in git_pairs:
        after = path.replace('/GIT_BEFORE.json', '/GIT_AFTER.json')
        if after not in files:
            need(checkpoint == '04' and path == config['cancelled_partial_root'] +
                 '/runs/attempt-00000/GIT_BEFORE.json', 'missing Git-after receipt outside cancelled Range')
            partial_missing_git_after.append(after)
        else:
            need(get(path) == get(after), 'original Git checkout changed')
    shared_expected = {m for m, g in expected.items() if g == 'p15_shared_repairs_reused'}
    shared_specs = config['shared_runs'] if 'shared_runs' in config else [{
        'path': config['shared_root'] + '/runs/attempt-00000', 'accepted': sorted(shared_expected),
        'failures': config['shared_failures'], 'exit_code': config['shared_exit_code']}]
    shared_by_owner, shared_protected = {}, None
    for spec in shared_specs:
        shared_run = PurePosixPath(spec['path'])
        shared_result = get(shared_run / 'RESULT.json')
        shared_context = get(shared_run / 'CONTEXT_BEFORE.json')
        need(shared_context == get(shared_run / 'CONTEXT_AFTER.json'), 'shared source/runtime context changed')
        need(shared_result['all_selected_owners_accepted'] is (not spec['failures']) and
             set(shared_result['failures']) == set(spec['failures']) and
             shared_result['worker_exit_code'] == spec['exit_code'] and
             not shared_result['whole_P1_complete'], 'shared outer result')
        need(set(shared_result['accepted_owners']) == set(spec['accepted']) and
             set(shared_result['targets']) == set(spec['accepted']) | set(spec['failures']), 'shared outer owner set')
        if shared_protected is None:
            shared_protected = shared_context['protected_roots']
        need(shared_context['protected_roots'] == shared_protected, 'shared protected roots differ')
        for module in spec['accepted']:
            need(module not in shared_by_owner, 'duplicate shared acceptance')
            shared_by_owner[module] = (shared_result, shared_context)
    need(set(shared_by_owner) == shared_expected, 'shared accepted owner union differs')
    if checkpoint in ('05', '06', '07', '08'):
        shared_protected = config['protected_roots']
        need(all(sha((repo / (m.replace('.', '/') + '.lean')).read_bytes()) == digest
                 for m, digest in shared_protected.items()), 'checkpoint' + checkpoint + ' protected root source differs')
    deployments = [get(p) for p in files if '/source-materialization/' in p and p.endswith('/RESULT.json')]
    need(all(d['status'] == 'SOURCE_DEPLOYMENT_ONLY_NOT_ACCEPTANCE' and d['acceptance_claimed'] is False
             and 'accepted_owners' not in d for d in deployments), 'source deployment misstates acceptance')
    pipeline_accepted, pipeline_results = [], set()

    def check_completed_stages(stages, source_commit, driver_sha256):
        accepted_so_far = set()
        for stage in stages:
            if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                need('result_path' not in stage and not stage.get('accepted_owners') and
                     not set(stage['requires']) <= accepted_so_far, 'held stage misstates acceptance')
                continue
            result_path = originals[stage['result_path']]
            need(result_path not in pipeline_results, 'duplicate pipeline result')
            pipeline_results.add(result_path)
            outer = get(result_path)
            binding = get(PurePosixPath(result_path).parents[2] / 'BINDING.json')
            need(outer['source_commit'] == source_commit == binding['source_commit'] and
                 outer['stage'] == stage['stage'] and
                 driver_sha256 == binding['driver_sha256'], 'pipeline source/driver binding')
            need(outer['targets'] == binding['targets'] and
                 outer['protected_roots'] == binding['protected_roots'] == shared_protected and
                 outer['whole_P1_4_complete'] is False, 'pipeline target/protected binding')
            accepted = set(outer['accepted_owners'])
            need(accepted == set(stage['accepted_owners']) and
                 accepted <= set(outer['normal_passed']) <= set(outer['targets']), 'pipeline accepted owners')
            complete = (accepted == set(outer['targets']) and
                        not outer['normal_failed_or_held'] and outer['audit_error'] is None)
            need(stage['exit_code'] == (0 if complete else 1), 'pipeline stage exit differs')
            accepted_so_far.update(accepted)
            pipeline_accepted.extend(accepted)
        return accepted_so_far

    if checkpoint == '04':
        review = config['retained_review']
        need(sha(files[review['path']]) == review['sha256'], 'retained23 review binding differs')
        retained = get(review['path'])
        retained_owners = {'ImbalancedChen.' + m for prior in CHECKPOINTS.values()
                           for group, modules in prior['groups'].items() if group != 'p14_new'
                           for m in modules}
        need(retained['schema'] == 'p15_retained_actual_means_review_v1' and
             retained['all_23_accepted'] is True and retained['compilation_performed'] is False and
             retained['context_and_inventory_stable'] is True and
             retained['context_before'] == retained['context_after'] and
             retained['git_before'] == retained['git_after'] and not retained['changed_files'] and
             not retained['changed_receipts'] and not retained['failures'] and
             retained['whole_P1_complete'] is False, 'retained23 review scope/context differs')
        need(set(retained['owners']) == retained_owners and len(retained_owners) == 23 and
             sum(r['total_owned_exports'] for r in retained['owners'].values()) == 378 and
             sum(r['total_public_exports'] for r in retained['owners'].values()) == 349,
             'retained23 owner set/counts differ')
        for module, row in retained['owners'].items():
            need(sha((repo / (module.replace('.', '/') + '.lean')).read_bytes()) == row['source_sha256'],
                 'retained23 current source differs: ' + module)
        for path in config['pipeline_paths']:
            pipeline = get(path)
            need(pipeline['whole_P1_4_complete'] is False, 'pipeline overstates completion')
            accepted_so_far = check_completed_stages(pipeline['stages'], pipeline['source_commit'],
                                                     pipeline['driver_sha256'])
            need(accepted_so_far == set(pipeline['accepted_owners']), 'pipeline accepted union differs')
        # These are original stdout events, not a reconstructed PIPELINE_RESULT.
        observed_stages = [e['pipeline_stage_result'] if 'pipeline_stage_result' in e else e
                           for e in observed_events if 'pipeline_stage_result' in e or
                           e.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED']
        need([r['stage'] for r in observed_stages] == [
             'unit-box-gain-measure', 'unit-box-consumers', 'unit-owner-geometry',
             'unit-literal-consumers', 'owner-fibre-volume', 'owner-gamma-volume',
             'typed-archive-shape-cast'], 'cancelled task completed/held stage observations differ')
        check_completed_stages(observed_stages, config['cancelled_source_commit'],
                               config['cancelled_driver_sha256'])
        need(pipeline_results == {p for p in files if p.startswith('p14/') and
             re.search(r'/runs/attempt-[0-9]{5}/RESULT\.json$', p)}, 'pipeline stage export differs')
        need(collections.Counter(pipeline_accepted) == collections.Counter(
             m for m, group in expected.items() if group == 'p14_new'), 'pipeline owner counted twice or omitted')
        partial_binding = get(partial_root + '/BINDING.json')
        partial_normal = partial_root + '/normal/' + config['cancelled_unaccepted_owner'] + '/attempt-00000'
        partial_context = get(partial_normal + '/CONTEXT_BEFORE.json')
        need(partial_binding['source_commit'] == partial_context['source_commit'] ==
             config['cancelled_source_commit'] and partial_binding['protected_roots'] == shared_protected,
             'cancelled Range source/protected binding')
        need(set(partial_binding['targets']) == {config['cancelled_unaccepted_owner']} and
             partial_binding['targets'][config['cancelled_unaccepted_owner']] ==
             partial_context['project_sources'][config['cancelled_unaccepted_owner']], 'cancelled Range target binding')
        need(partial_normal + '/normal.log' in files, 'cancelled Range original partial log missing')
        partial_report = {
            'module': config['cancelled_unaccepted_owner'], 'source_commit': config['cancelled_source_commit'],
            'partial_root': partial_root, 'accepted': False,
            'classification': 'OPERATOR_CANCELLED_TO_UNBLOCK_GEOMETRY_NOT_PROOF_FAILURE',
            'task_id': cancelled_metadata['task_id'], 'status': cancelled_metadata['status'],
            'exit_code': cancelled_metadata['exit_code'], 'cancel_requested': cancelled_metadata['cancel_requested'],
            'runtime_seconds': cancelled_metadata['runtime_seconds'],
            'observer_manifest': config['observer_path'], 'observer_manifest_sha256': config['observer_sha256'],
            'observer_is_compiler_acceptance_receipt': False,
            'missing_original_git_after_receipts': partial_missing_git_after,
            'completed_original_stage_result_present': False,
            'normal_acceptance_receipt_present': False,
            'no_range_proof_diagnostic_in_observed_task_output': True,
            'partial_normal_log_sha256': sha(files[partial_normal + '/normal.log']),
            'original_receipts_synthesized': False}

    if checkpoint in ('05', '06', '07', '08'):
        for spec in config['pipelines']:
            pipeline = get(spec['path'])
            need(pipeline['source_commit'] == spec['source_commit'] and
                 pipeline['driver_sha256'] == spec['driver_sha256'] and
                 pipeline['whole_P1_4_complete'] is False, 'checkpoint' + checkpoint + ' pipeline source/driver binding')
            need([s['stage'] for s in pipeline['stages'] if 'result_path' in s] == spec['completed_stages'],
                 'checkpoint' + checkpoint + ' completed pipeline stage list differs')
            need([s['stage'] for s in pipeline['stages'] if s.get('status') ==
                  'HELD_UPSTREAM_NOT_ACCEPTED'] == spec['held_stages'],
                 'checkpoint' + checkpoint + ' held pipeline stage list differs')
            accepted_so_far = check_completed_stages(pipeline['stages'], spec['source_commit'],
                                                     spec['driver_sha256'])
            need(accepted_so_far == set(pipeline['accepted_owners']), 'pipeline accepted union differs')
        need(pipeline_results == {p for p in files if p.startswith('p14/') and
             re.search(r'/runs/attempt-[0-9]{5}/RESULT\.json$', p)}, 'pipeline stage export differs')
        need(collections.Counter(pipeline_accepted) == collections.Counter(expected.keys()),
             'checkpoint' + checkpoint + ' pipeline owner counted twice or omitted')

    if checkpoint == '06':
        c490_spec, a700_spec = config['pipelines']
        c490, a700 = get(c490_spec['path']), get(a700_spec['path'])
        reused_pipeline = a700['reused_pipeline']
        need('reused_pipeline' not in c490 and set(reused_pipeline) ==
             {'path', 'sha256', 'source_commit', 'accepted_owners'}, 'checkpoint06 reuse schema')
        need(originals[reused_pipeline['path']] == c490_spec['path'] and
             reused_pipeline['source_commit'] == c490_spec['source_commit'] and
             reused_pipeline['sha256'] == sha(files[c490_spec['path']]) == config['reused_pipeline_sha256'],
             'checkpoint06 reused pipeline source/hash binding')
        need(reused_pipeline['accepted_owners'] == c490['accepted_owners'] and
             len(set(reused_pipeline['accepted_owners'])) == 5 and
             set(reused_pipeline['accepted_owners']).isdisjoint(a700['accepted_owners']),
             'checkpoint06 reused owner set differs or counted again')
        # Check held stages against all actually available owners, including the
        # five reused C490 owners. Only executed-stage acceptances are counted.
        available = set(reused_pipeline['accepted_owners'])
        for stage in a700['stages']:
            if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                need(not set(stage['requires']) <= available, 'checkpoint06 held stage ignores available reuse')
            else:
                available.update(stage['accepted_owners'])
        need(available == set(expected), 'checkpoint06 available owner union differs')
        reuse_report = {'path': c490_spec['path'], 'source_commit': c490_spec['source_commit'],
            'sha256': reused_pipeline['sha256'], 'accepted_owners': reused_pipeline['accepted_owners'],
            'source_hash_owner_binding_verified': True, 'additional_accepted_owners': 0,
            'held_stages_checked_with_reused_owners_available': True}

    if checkpoint == '07':
        prior_config = CHECKPOINTS['06']
        prior_archive = repo / 'docs/p1/20261125/p14-continuation/evidence/checkpoint-06.tar.xz'
        prior_raw = prior_archive.read_bytes()
        need(len(prior_raw) == prior_config['bytes'] and sha(prior_raw) == prior_config['sha256'],
             'checkpoint07 prior archive binding differs')
        with tarfile.open(fileobj=io.BytesIO(prior_raw), mode='r:xz') as prior_tar:
            prior_manifest = json.load(prior_tar.extractfile('EXPORT_MANIFEST.json'))
            prior_files = {p: prior_tar.extractfile(p).read() for p in config['prior_pipeline_paths']}
        prior_rows = {r['path']: r for r in prior_manifest['files']}
        need(prior_manifest['checkpoint'] == '06' and
             [s['path'] for s in prior_config['pipelines']] == config['prior_pipeline_paths'],
             'checkpoint07 prior pipeline scope differs')
        frozen = get(config['pipelines'][1]['path'])
        references = frozen['reused_pipelines']
        need(len(references) == 2 and all('reused_pipeline' not in get(s['path']) and
             ('reused_pipelines' not in get(s['path']) or s == config['pipelines'][1])
             for s in config['pipelines']), 'checkpoint07 reuse schema/scope differs')
        reused, reference_reports = set(), []
        for reference, spec, pinned_sha in zip(references, prior_config['pipelines'],
                                               config['prior_pipeline_sha256']):
            data, row = prior_files[spec['path']], prior_rows[spec['path']]
            original = json.loads(data)
            need(set(reference) == {'path', 'sha256', 'source_commit', 'accepted_owners'} and
                 reference['path'] == row['original_path'] and len(data) == row['bytes'] and
                 reference['sha256'] == row['sha256'] == sha(data) == pinned_sha and
                 reference['source_commit'] == spec['source_commit'] == original['source_commit'] and
                 original['driver_sha256'] == spec['driver_sha256'] and
                 original['whole_P1_4_complete'] is False, 'checkpoint07 reused source/path/hash binding')
            owners = reference['accepted_owners']
            need(owners == original['accepted_owners'] and len(owners) == len(set(owners)) and
                 reused.isdisjoint(owners) and set(owners).isdisjoint(expected),
                 'checkpoint07 reused owners differ or counted again')
            reused.update(owners)
            reference_reports.append({'path': spec['path'], 'source_commit': spec['source_commit'],
                'sha256': pinned_sha, 'accepted_owners': owners})
        need(reused == {'ImbalancedChen.' + m for m in prior_config['groups']['p14_new']},
             'checkpoint07 reused owner union differs')
        available = set(reused)
        for stage in frozen['stages']:
            if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                need(stage['requires'] == ['ImbalancedChen.P5OldFifthFrozenGapConcavity',
                     'ImbalancedChen.P5OldFifthExact64ChildTiling'] and
                     not set(stage['requires']) <= available, 'checkpoint07 held stage ignores available reuse')
            else:
                available.update(stage['accepted_owners'])
        need(available == reused | set(frozen['accepted_owners']), 'checkpoint07 available owner union differs')
        reuse_report = {'checkpoint': '06', 'archive_sha256': prior_config['sha256'],
            'references': reference_reports, 'source_hash_owner_binding_verified': True,
            'reused_owner_count': len(reused), 'additional_accepted_owners': 0,
            'additional_owned_declarations': 0, 'held_stages_checked_with_reused_owners_available': True}
        failure_root = 'p14/frozen-gap-concavity/' + frozen['source_commit']
        failed_owner = config['excluded_failed_owners'][0]
        failure_command = get(failure_root + '/normal/' + failed_owner + '/attempt-00000/normal-command.json')
        failure_log = files[originals[failure_command['log']]]
        need(failure_command['exit_code'] == 1 and failure_command['actual_failed_modules'] == [failed_owner] and
             failure_command['actual_built_modules'] == [] and failure_command['project_error_count'] == 2 and
             len(failure_command['project_error_sections']) == 2 and
             sha(failure_log) == failure_command['log_sha256'] and len(failure_log) == failure_command['log_bytes'],
             'checkpoint07 failed normal history differs')
        failure_report = {'module': failed_owner, 'normal_exit_code': 1, 'project_error_count': 2,
            'normal_log_sha256': failure_command['log_sha256'], 'accepted': False,
            'held_stage': frozen['stages'][-1], 'additional_accepted_owners': 0}

    if checkpoint == '08':
        # Fixed joins to the sealed 06/07 archives and this archive's 935 pipeline.
        reference_data, reference_rows = {}, {}
        for prior_checkpoint in ['06', '07']:
            prior_config = CHECKPOINTS[prior_checkpoint]
            prior_archive = repo / ('docs/p1/20261125/p14-continuation/evidence/checkpoint-' +
                                    prior_checkpoint + '.tar.xz')
            prior_raw = prior_archive.read_bytes()
            need(len(prior_raw) == prior_config['bytes'] and sha(prior_raw) == prior_config['sha256'],
                 'checkpoint08 prior archive binding differs')
            with tarfile.open(fileobj=io.BytesIO(prior_raw), mode='r:xz') as prior_tar:
                prior_manifest = json.load(prior_tar.extractfile('EXPORT_MANIFEST.json'))
                need(prior_manifest['checkpoint'] == prior_checkpoint, 'checkpoint08 prior manifest differs')
                prior_rows = {r['path']: r for r in prior_manifest['files']}
                for source, spec in config['reuse_locations'].items():
                    if spec['checkpoint'] == prior_checkpoint:
                        reference_data[source] = prior_tar.extractfile(spec['path']).read()
                        reference_rows[source] = prior_rows[spec['path']]
        current_rows = {r['path']: r for r in manifest['files']}
        for source, spec in config['reuse_locations'].items():
            if spec['checkpoint'] == '08':
                reference_data[source], reference_rows[source] = files[spec['path']], current_rows[spec['path']]
        reference_reports, reuse_consumers, used_references = {}, [], set()
        for spec in config['pipelines']:
            pipeline = get(spec['path'])
            need(sha(files[spec['path']]) == spec['sha256'] and 'reused_pipeline' not in pipeline,
                 'checkpoint08 pipeline hash/reuse schema differs')
            references = pipeline.get('reused_pipelines', [])
            need([r['source_commit'] for r in references] == spec['reused_sources'] and
                 bool(references) == ('reused_pipelines' in pipeline), 'checkpoint08 reused source list differs')
            reused = set()
            for reference in references:
                source = reference['source_commit']
                location_spec = config['reuse_locations'][source]
                data, row = reference_data[source], reference_rows[source]
                original = json.loads(data)
                need(set(reference) == {'path', 'sha256', 'source_commit', 'accepted_owners'} and
                     source == original['source_commit'] and reference['path'] == row['original_path'] and
                     len(data) == row['bytes'] and
                     reference['sha256'] == row['sha256'] == sha(data) == location_spec['sha256'] and
                     original['driver_sha256'] == spec['driver_sha256'] and
                     original['whole_P1_4_complete'] is False, 'checkpoint08 reused source/path/hash binding')
                owners = reference['accepted_owners']
                need(owners == original['accepted_owners'] and len(owners) == len(set(owners)) and
                     reused.isdisjoint(owners) and set(owners).isdisjoint(pipeline['accepted_owners']),
                     'checkpoint08 reused owners differ or counted again')
                reused.update(owners)
                used_references.add(source)
                reference_reports[source] = {'checkpoint': location_spec['checkpoint'],
                    'path': location_spec['path'], 'sha256': location_spec['sha256'], 'accepted_owners': owners}
            available = set(reused)
            for stage in pipeline['stages']:
                if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                    need(not set(stage['requires']) <= available, 'checkpoint08 held stage ignores available reuse')
                else:
                    available.update(stage['accepted_owners'])
            need(available == reused | set(pipeline['accepted_owners']), 'checkpoint08 available owner union differs')
            if references:
                reuse_consumers.append({'source_commit': spec['source_commit'],
                    'reused_source_commits': spec['reused_sources'], 'reused_owners': sorted(reused),
                    'held_stages_checked_with_reused_owners_available': True})
        need(used_references == set(config['reuse_locations']), 'checkpoint08 unused or missing reuse reference')
        reuse_report = {'prior_archive_sha256': {c: CHECKPOINTS[c]['sha256'] for c in ['06', '07']},
            'references': reference_reports, 'consumers': reuse_consumers,
            'source_hash_owner_binding_verified': True, 'additional_accepted_owners': 0,
            'additional_owned_declarations': 0}
        failed_attempts, failed_command_paths = [], set()
        for spec in config['failed_attempts']:
            module = spec['module']
            stage_root = 'p14/' + spec['stage'] + '/' + spec['source_commit']
            attempt = stage_root + '/normal/' + module + '/attempt-00000'
            command_path = attempt + '/normal-command.json'
            failed_command_paths.add(command_path)
            record = get(command_path)
            outer, binding = get(stage_root + '/runs/attempt-00000/RESULT.json'), get(stage_root + '/BINDING.json')
            context = get(attempt + '/CONTEXT_BEFORE.json')
            need(outer['stage'] == spec['stage'] and outer['source_commit'] == binding['source_commit'] ==
                 context['source_commit'] == spec['source_commit'] and module in outer['normal_failed_or_held'] and
                 module not in outer['accepted_owners'] and outer['targets'][module] == binding['targets'][module] ==
                 context['project_sources'][module] == spec['source_sha256'], 'checkpoint08 failed source/stage binding')
            log = files[originals[record['log']]]
            need(record['exit_code'] == 1 and record['cwd'] == '/workspace/blue-member-build' and
                 record['argv'] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
                 '/workspace/blue-build-tools/member-runtime-evidence/state.json', 'lake', 'build', '+' + module + ':olean'] and
                 record['actual_failed_modules'] == [module] and record['actual_built_modules'] == [] and
                 record['project_error_count'] == spec['project_error_count'] and
                 len(record['project_error_sections']) == spec['reported_error_sections'] and
                 len(log) == record['log_bytes'] and sha(log) == record['log_sha256'],
                 'checkpoint08 failed command/log differs')
            failed_attempts.append({**spec, 'normal_exit_code': 1, 'normal_log_sha256': record['log_sha256'],
                'accepted': False, 'current_failed_preimage_identity_not_claimed': True})
        need(failed_command_paths == {p for p in files if p.endswith('/normal-command.json') and
             get(p)['exit_code'] != 0}, 'checkpoint08 failed normal attempt set differs')
        gamma = 'ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume'
        need({s['module'] for s in config['failed_attempts']} & set(expected) == {gamma},
             'checkpoint08 same-module failure/success scope differs')
        gamma_stage = get('p14/owner-gamma-beta-retry/89db42762b5f303602608587b3d610cd7ebe9a54/runs/attempt-00000/RESULT.json')
        need(gamma_stage['accepted_owners'] == [gamma] and gamma_stage['targets'][gamma] ==
             'd9b792ee4d078aad6da25066d3f2cc861f79c56f979132bd492c7f63edb01e76',
             'checkpoint08 later Gamma acceptance differs')
        failure_report = {'failed_attempts': failed_attempts, 'failed_attempt_count': 5,
            'held_stage_count': sum(len(s['held_stages']) for s in config['pipelines']),
            'classification_is_source_and_stage_specific': True,
            'gamma_accepted_source_commit': gamma_stage['source_commit'],
            'gamma_accepted_stage': gamma_stage['stage'], 'additional_accepted_owners': 0}

    def location(path, base=''):
        return originals[path] if PurePosixPath(path).is_absolute() else str(PurePosixPath(base) / path)

    def command(record, base, expected_argv=None):
        need(record['exit_code'] == 0 and record['cwd'] == '/workspace/blue-member-build', 'command failed or cwd differs')
        if expected_argv is not None:
            need(record['argv'][4:] == expected_argv, 'command arguments differ')
        need(record['argv'][:3] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state'], 'unguarded command')
        log = location(record['log'], base)
        need(sha(files[log]) == record['log_sha256'], 'command log hash: ' + log)
        if 'log_bytes' in record:
            need(len(files[log]) == record['log_bytes'], 'command log size')
        return ANSI.sub('', files[log].decode())

    normals = {}
    for path in files:
        if path.endswith('/NORMAL_PASS.json'):
            item = get(path)
            need(item['module'] not in normals, 'duplicate successful normal receipt')
            normals[item['module']] = (path, item)
    need(set(normals) == set(expected), 'successful normal owner set differs')
    successes = collections.Counter()
    for path in files:
        if path.endswith('/normal-command.json'):
            record = get(path)
            if record['exit_code'] == 0:
                built = BUILT.findall(command(record, ''))
                need(built == record['actual_built_modules'] and len(built) == 1, 'normal rebuilt extra modules')
                successes.update(built)
    need(successes == collections.Counter({m: 1 for m in expected}), 'successful normal was duplicated or omitted')

    reports = []
    seen = set()
    validation_paths = sorted(p for p in files if p.endswith('/VALIDATION_RESULTS.json'))
    if checkpoint == '07':
        need({str(PurePosixPath(p).parent): sorted(get(p)['modules']) for p in validation_paths} ==
             config['single_owner_lanes'], 'checkpoint07 exact audit lane/owner scope differs')
    if checkpoint == '08':
        need({str(PurePosixPath(p).parent): sorted(get(p)['modules']) for p in validation_paths} ==
             config['single_owner_lanes'], 'checkpoint08 exact audit lane/owner scope differs')
    need(all(get(path)['modules'] for path in validation_paths), 'empty audited lane')
    validation_targets = [(path, module) for path in validation_paths
        for module in sorted(get(path)['modules'])]
    for path, module in validation_targets:
        v = get(path)
        lane = PurePosixPath(path).parent
        audit_root = lane.parent
        need(v['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS', 'audit status')
        lane_modules = sorted(v['modules'])
        need(len(lane_modules) == 1 or (checkpoint in ('04', '05') and
             str(lane) == config['paired_owner_lane'] and lane_modules == config['paired_owners']) or
             (checkpoint == '06' and any(str(lane) == spec['path'] and lane_modules == spec['owners']
                                        for spec in config['paired_owner_lanes'])),
             'checkpoint lane scope')
        digest = v['modules'][module]
        need(module in expected and module not in seen, 'duplicate or unexpected audited owner')
        seen.add(module)
        need(all(v[k] is True for k in ['full_owned_including_private_generated', 'only_standard_axioms',
            'pp_all_true_no_elisions', 'source_plus_five_outputs_unchanged_across_kernel_and_audit',
            'successful_normal_not_repeated']) and v['whole_P1_complete'] is False, 'audit flags')
        normal_path, normal = normals[module]
        nc = normal['normal_command']
        normal_log = command(nc, '', ['lake', 'build', '+' + module + ':olean'])
        need(BUILT.findall(normal_log) == [module] and nc['actual_built_modules'] == [module], 'normal build markers')
        need(nc['actual_failed_modules'] == [] and nc['project_error_count'] == 0 and nc['project_error_sections'] == [], 'normal errors')
        command_path = location(nc['command_receipt'])
        need(sha(files[command_path]) == nc['command_sha256'], 'normal command receipt hash')
        need(get(command_path) == {k: x for k, x in nc.items() if k not in ['command_receipt', 'command_sha256']}, 'normal receipt contents')
        attempt = PurePosixPath(command_path).parent
        context = normal['dependency_context']
        need(get(attempt / 'CONTEXT_BEFORE.json') == context, 'normal dependency context changed')
        need(normal['source_commit'] == context['source_commit'], 'normal source commit differs')
        deps = get(attempt / 'directdeps-command.json')
        need('--no-build' in deps['argv'] and BUILT.findall(command(deps, str(attempt))) == [], 'direct dependencies were rebuilt')
        ready = get(attempt / 'target-ready-command.json')
        need(ready['exit_code'] == 3 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == [module], 'target was not held as missing before build')
        need('--no-build' in ready['argv'] and sha(files[location(ready['log'], str(attempt))]) == ready['log_sha256'], 'target readiness binding')

        plan = get(audit_root / 'AUDIT_PLAN.json')
        plan_binding = get(audit_root / 'PLAN_BINDING.json')
        need(sha(files[str(audit_root / 'AUDIT_PLAN.json')]) == v['plan_sha256'] == plan_binding['sha256'], 'audit plan hash')
        need(plan_binding['runner_sha256'] == AUDIT_RUNNER_SHA and plan_binding['no_compiler_invoked_by_preparation'], 'audit runner binding')
        need(v['audit_template_sha256'] == plan['audit_template']['sha256'] == AUDIT_TEMPLATE_SHA, 'audit template pin')
        need(get(lane / 'MODULES.json') == get(audit_root / 'TARGETS.json') == lane_modules, 'module inventory scope')
        need(plan['source_review_head'] == normal['source_commit'], 'normal/audit source commits differ')
        lane_sources = {m: plan['expected_project_sources'][m] for owner in lane_modules
                        for m in plan['modules'][owner]['project_closure']}
        need(v['project_dependency_sources'] == get(lane / 'PROJECT_SOURCE_BINDING.json') == lane_sources,
             'plan lane source closure differs')
        sources = {m: lane_sources[m] for m in plan['modules'][module]['project_closure']}
        need(sources == context['project_sources'], 'normal/audit source closure differs')
        need(sources[module] == plan['modules'][module]['source_sha256'] == digest, 'target source binding')
        if expected[module] == 'p14_new':
            owner_root = PurePosixPath(normal_path).parents[2]
            binding = get(owner_root / 'BINDING.json')
            outer = get(owner_root / 'runs/attempt-00000/RESULT.json')
            need(binding['source_commit'] == outer['source_commit'] == normal['source_commit'], 'outer source commit differs')
            need(binding['targets'][module] == outer['targets'][module] == digest and
                 module in outer['accepted_owners'] and module in outer['normal_passed'], 'outer accepted target differs')
            need(binding['protected_roots'] == outer['protected_roots'] == shared_protected, 'protected root hashes differ')
            need(sha(files[str(owner_root / 'executed-driver.py')]) == binding['driver_sha256'], 'executed driver hash differs')
            need(sha((repo / binding['manifest_path']).read_bytes()) == binding['manifest_sha256'], 'current stage manifest differs')
            need(all(binding['project_sources'][m] == s for m, s in sources.items()), 'outer source closure differs')
        elif expected[module] == 'p15_shared_repairs_reused':
            owner_shared_result, owner_shared_context = shared_by_owner[module]
            need(normal['source_commit'] == owner_shared_result['source_commit'] and
                 all(owner_shared_context['project_sources'][m] == s for m, s in sources.items()), 'shared outer source binding differs')
        snapshot = v['source_plus_five_outputs'][module]
        need(snapshot == normal['source_plus_five_outputs'] == get(lane / 'BEFORE_KERNEL.json')[module], 'source/object fingerprints changed')
        source_path = module.replace('.', '/') + '.lean'
        current = (repo / source_path).read_bytes()
        need(sha(current) == snapshot[source_path]['sha256'] == digest and len(current) == snapshot[source_path]['bytes'], 'current target source differs: ' + module)
        reused = v['reused_normal_evidence']
        need(reused == get(lane / 'REUSED_NORMAL_EVIDENCE.json') and set(reused) == set(lane_modules), 'normal reuse record')
        record = reused[module]
        need(record['source_commit'] == normal['source_commit'] and record['sha256'] == nc['log_sha256'], 'reused normal binding')
        need(record['all_actual_built_modules'] == [module] and record['selected_sources'] == {module: digest}, 'reused normal target')
        for header in record['selected_actual_built_headers']:
            need(header['module'] == module and normal_log.splitlines()[header['line'] - 1] == header['text'], 'actual Built header differs')
        need(len(record['selected_actual_built_headers']) == 1, 'missing actual Built header')

        kernel = v['kernel_commands'][module]
        need(get(lane / (module.split('.')[-1] + '-kernel-command.json')) == kernel, 'kernel command sidecar')
        kernel_log = command(kernel, str(lane), ['lake', 'env', 'leanchecker', '--verbose', module])
        need(kernel_log.strip() == 'replaying ' + module, 'kernel replay target log')
        audit = v['audit_command']
        need(get(lane / 'all-owned-types-axioms-command.json') == audit, 'audit command sidecar')
        text = command(audit, str(lane))
        need(audit['argv'][4:7] == ['lake', 'env', 'lean'], 'full-owned audit command')
        records = [json.loads(s.removeprefix('AUDIT_RECORD ')) for s in text.splitlines() if s.startswith('AUDIT_RECORD ')]
        inventory = [json.loads(s.removeprefix('MEMBER_OWNED_NAMES '))['names'] for s in text.splitlines() if s.startswith('MEMBER_OWNED_NAMES ')]
        counts = [json.loads(s.removeprefix('MEMBER_OWNED_MODULE ')) for s in text.splitlines() if s.startswith('MEMBER_OWNED_MODULE ')]
        totals = [int(s.removeprefix('MEMBER_OWNED_COUNT ')) for s in text.splitlines() if s.startswith('MEMBER_OWNED_COUNT ')]
        names = [r['name'] for r in records]
        need(records == get(lane / 'OWNED_EXPORTS.json'), 'owned export records differ from log')
        need(len(inventory) == 1 and sorted(inventory[0]) == sorted(names) and len(set(names)) == len(names), 'owned inventory incomplete')
        need(counts == [{'count': sum(r['module'] == owner for r in records), 'module': owner}
                        for owner in lane_modules] and totals == [len(records)], 'owned module count')
        need(len(records) == v['total_owned_exports'] and sum(not r['is_private'] for r in records) == v['total_public_exports'], 'owned/public count')
        need(all(r['module'] in lane_modules and r['kind'] != 'axiom' and set(r['axioms']) <= ALLOWED_AXIOMS and
                 r['type'] and r['type_expression'].startswith('Lean.Expr.') for r in records), 'type or axiom audit')
        need(not any(s in text for s in ['sorryAx', '…', '⋯', '...']), 'type dump has elisions or sorry')
        audit_source = files[str(lane / 'PublicAudit.lean')].decode()
        body = re.sub(r'^import ImbalancedChen\.[^\n]+\n', '', audit_source, flags=re.M)
        body = re.sub(r'let modules := #\[[^\n]*\]', 'let modules := #[__MODULES__]', body, count=1)
        need(sha(body.encode()) == AUDIT_BODY_SHA, 'full environment audit program differs')
        need(audit_source.startswith(''.join('import ' + owner + '\n' for owner in lane_modules)) and
             'let modules := #[' + ', '.join('`' + owner for owner in lane_modules) + ']' in audit_source,
             'audit program target')
        for key in ['stock_readiness_before', 'stock_readiness_after']:
            rec = v[key]
            need(get(lane / (key.replace('_', '-') + '-command.json')) == rec, 'readiness command sidecar')
            need(BUILT.findall(command(rec, str(lane), ['lake', '--no-build', 'build'] +
                 ['+' + owner + ':olean' for owner in lane_modules])) == [], 'audit repeated a normal build')
        records = [r for r in records if r['module'] == module]
        public_count = sum(not r['is_private'] for r in records)
        reports.append({'module': module, 'group': expected[module], 'source_commit': normal['source_commit'],
            'current_source_sha256': digest, 'owned_declarations': len(records), 'public_declarations': public_count,
            'private_declarations': len(records) - public_count, 'source_closure_modules': len(sources),
            'normal_seconds': nc['elapsed_seconds'], 'kernel_seconds': kernel['elapsed_seconds'],
            'normal_log_sha256': nc['log_sha256'], 'kernel_log_sha256': kernel['log_sha256'],
            'owned_log_sha256': audit['log_sha256'], 'normal_receipt': normal_path,
            'validation_receipt': path, 'validation_receipt_sha256': sha(files[path]),
            'normal_exit_code': 0, 'kernel_exit_code': 0, 'full_owned_audit_exit_code': 0,
            'normal_built_only_target_once_in_archive': True, 'current_source_matches': True})
    need(seen == set(expected), 'accepted owner set differs')
    totals = {g: {'owners': sum(r['group'] == g for r in reports),
                  'owned_declarations': sum(r['owned_declarations'] for r in reports if r['group'] == g)} for g in groups}
    need(sum(r['owned_declarations'] for r in reports) == config['owned'], 'checkpoint owned total differs')
    need(sum(r['public_declarations'] for r in reports) == config['public'], 'checkpoint public total differs')
    limits = [
        'Cloud command exits are validated as archived receipts; no compiler or kernel was rerun locally.',
        'Source and five output fingerprints agree between normal, before-kernel and final audit receipts; binary objects are not in this export.',
        'Current target source bytes match the receipts; historical Git commit/source associations are cross-checked through archived bindings, not new Git retrieval.']
    if checkpoint == '01':
        limits.extend([
            'The prior FourthUntruncatedIntegral export contains its complete owner receipts, but not its original batch-level outer RESULT.json.',
            'This checkpoint excludes later FiniteTableRefinementConstructor and subsequent stages.'])
    elif checkpoint == '02':
        limits.extend([
            'The shared B2 batch exited 1: only its three individually accepted owners are counted; failed MiddleShellMovingLimit is excluded.',
            'Source-materialization receipts describe deployment, not acceptance, and add no accepted owner.'])
    elif checkpoint == '03':
        limits.extend([
            'Shared rounds 03 through 07 contain failed and held attempts; only the twelve individually accepted source-bound owners are counted.',
            'The bytes-frame-seed stage accepted only P5OriginalCommonRefinedSeedHull. ByteLiteral, NpyFrame and the round07 FullMean failure are excluded.',
            'Later retries and pipelines outside the six fixed export roots are not included in checkpoint 03.'])
    elif checkpoint == '04':
        limits.extend([
            'Only the individually accepted owners in the fixed c6/439/4d pipelines and shared round08 are counted; failed and held stages remain history.',
            'The fixed ByteLiteral/NpyFrame lane contains both owners: all 99 declarations and both kernel commands are checked, with each source and normal receipt checked separately.',
            'The retained23 review is bound by its original receipt hash and adds no duplicate owner or declaration; earlier owners remain in checkpoints 01 through 03.',
            'Root cancelled job_1cea during TypedArchiveRange to unblock geometry. Its partial files and separately pinned verbatim MCP observations are not acceptance, a timeout or a proved mathematical failure.',
            'No original Range RESULT/GIT_AFTER or final 4d PIPELINE_RESULT is synthesized; any missing Range Git-after receipt is reported without claiming that partial run has a verified before/after pair.',
            'The full original-NPY association and complete stored-floor obligations are not discharged by these reader, frame, typed-shape and owner-geometry acceptances.'])
    elif checkpoint == '05':
        limits.extend([
            'Only five individually accepted owners in the fixed 8237 and 61566 completed pipelines are counted; failed and held attempts remain history.',
            'Any paired audit lane is restricted to its exact exported path and module-owner list; declaration ownership is determined by the audit module field, not a namespace prefix.',
            'RangeCore and RangeBlock000 are bounded suppliers; they do not certify all original rows or complete the original-NPY association.',
            'The later c490 pipeline and other stages outside the six fixed roots are not included in checkpoint 05.'])
    elif checkpoint == '06':
        limits.extend([
            'Only the six individually accepted owners in the fixed C490 and A700 executed stages are counted; failed and held attempts remain history.',
            'A700 reuses C490 acceptance evidence: its original source/hash/owner reference must match the C490 pipeline in this archive, without adding any duplicate acceptance.',
            'Paired audit lanes are restricted to their exact exported paths and exact owner lists; no general multi-owner allowance is used.',
            'Later Range, numeric and BaseGeometry pipelines outside the six fixed roots are not included in checkpoint 06.'])
    elif checkpoint == '07':
        limits.extend([
            'Only four individually accepted owners in the fixed 5ba405, 8682 and e4dfe2 pipelines are counted; FrozenGapConcavity failure and OneCoordinateVertexChord held history are excluded.',
            'The 8682 pipeline references C490 and A700 receipts in checkpoint06. These references must match that pinned archive and add no duplicate acceptance.',
            'RangeBlocks001010 and the BaseGeometry core/first block are bounded suppliers; remaining blocks, later pipelines and final P1.4 consumers are outside this checkpoint.'])
    else:
        limits.extend([
            'Only seven individually accepted owners in the twelve fixed executed roots and five final pipelines are counted; five failed normal attempts and twenty-one held stages remain history.',
            'Reused C490/A700 and 8682 references must join the pinned checkpoint06/07 archives; references to the 935 pipeline must join this archive. They only extend original held-stage availability and add no duplicate acceptance.',
            'GammaRateOwnerVolume failed at source935/owner-gamma-expression-retry and passed at source89db/owner-gamma-beta-retry. Failure classification is source/stage specific; only the later accepted source is checked against the current target.',
            'Range011030 and Base001010 are bounded suppliers. Later numeric/geometry retries, subsequent data blocks and final P1.4 consumers are outside this checkpoint.'])
    return {'schema': 'p14_checkpoint' + checkpoint + '_offline_receipt_verification_v1',
        'status': 'PASS_ARCHIVED_CLOUD_RECEIPT_CONSISTENCY_AND_CURRENT_TARGET_SOURCE_IDENTITY',
        'archive_sha256': config['sha256'], 'archive_bytes': len(raw), 'export_manifest_sha256': sha(files['EXPORT_MANIFEST.json']),
        'exported_files_verified': len(manifest['files']),
        'unchanged_original_git_pairs_verified': len(git_pairs) - len(partial_missing_git_after),
        'groups': totals, 'owners': reports,
        'total_owners': len(expected), 'total_owned_declarations': config['owned'], 'total_public_declarations': config['public'],
        'total_private_declarations': config['owned'] - config['public'], 'permitted_transitive_axioms': sorted(ALLOWED_AXIOMS),
        'excluded_failed_owners': config.get('excluded_failed_owners', config['shared_failures']),
        'nonaccepting_source_deployments': len(deployments),
        'normal_build_repeated_by_this_verifier': False, 'local_kernel_replay_performed': False,
        'compiled_object_binaries_exported_or_rehashed_locally': False,
        'historical_git_blobs_independently_resolved': False,
        'verification_limits': limits,
        **({'cancelled_unaccepted_partial_history': partial_report,
            'noncounting_retained_review': {'path': review['path'], 'sha256': review['sha256'],
                'owners': 23, 'owned_declarations': 378, 'public_declarations': 349,
                'all_current_owner_sources_match': True, 'additional_accepted_owners': 0,
                'additional_owned_declarations': 0}} if checkpoint == '04' else {}),
        **({'noncounting_pipeline_reuse': reuse_report} if checkpoint in ('06', '07', '08') else {}),
        **({'unaccepted_failure_and_held_history': failure_report} if checkpoint == '07' else {}),
        **({'source_stage_failed_attempt_history': failure_report} if checkpoint == '08' else {}),
        'whole_P1_4_complete': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', choices=['01', '02', '03', '04', '05', '06', '07', '08'], default='01')
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    archive = args.archive or args.repo / ('docs/p1/20261125/p14-continuation/evidence/checkpoint-' + args.checkpoint + '.tar.xz')
    result = verify(archive, args.repo, args.checkpoint)
    result['verifier_sha256'] = sha(Path(__file__).read_bytes())
    payload = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(json.dumps({k: result[k] for k in ['status', 'groups', 'total_owners', 'total_owned_declarations',
          'local_kernel_replay_performed', 'whole_P1_4_complete']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
