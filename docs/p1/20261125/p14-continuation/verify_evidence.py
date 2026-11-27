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
    '09': {'sealed': True,
     'sha256': '022491a027cdfb27317b89516e16eaf5086a3debd191028aaa52ac6f6775a06c',
     'bytes': 195340,
     'files': 642,
     'owned': 255,
     'public': 255,
     'audit_lanes': {'p14/five-coordinate-tree-expression-retry/8eabdf5c9563ae73eb091242f376a5b28456f97f/audits/9cefba16468c05db4259/lane-0': ['ImbalancedChen.P5OldFifthFiveCoordinateTree'],
                     'p14/named-parent-owner-expression-retry/8eabdf5c9563ae73eb091242f376a5b28456f97f/audits/26637257a0de43f2d2e0/lane-0': ['ImbalancedChen.P1FifthMask5NamedParent1Owner',
                                                                                                                                             'ImbalancedChen.P1FifthMask6NamedParent0Owner'],
                     'p14/one-coordinate-chord-retry/8eabdf5c9563ae73eb091242f376a5b28456f97f/audits/f05f6299dd3ef75f7fae/lane-0': ['ImbalancedChen.P5OldFifthOneCoordinateVertexChord'],
                     'p14/typed-base-blocks-011-020/649440b8436a3a94cabb096a56385307056f6dcc/audits/e547ffa80adfa208109f/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks011020'],
                     'p14/typed-base-blocks-021-030/649440b8436a3a94cabb096a56385307056f6dcc/audits/f0657d29414cc37dbb23/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks021030'],
                     'p14/typed-base-blocks-031-040/649440b8436a3a94cabb096a56385307056f6dcc/audits/b9212639d57507e45fd5/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks031040'],
                     'p14/typed-base-blocks-041-050/649440b8436a3a94cabb096a56385307056f6dcc/audits/73ed241e4594bf43faed/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks041050'],
                     'p14/typed-base-blocks-051-060/649440b8436a3a94cabb096a56385307056f6dcc/audits/ef1d7e54add456628385/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks051060'],
                     'p14/typed-base-blocks-061-070/649440b8436a3a94cabb096a56385307056f6dcc/audits/d250634db659b0687bc4/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks061070'],
                     'p14/typed-range-blocks-031-040/5ba405bc08aaef020868399aa62a429ca4281eda/audits/f5af300315ad32193bde/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks031040'],
                     'p14/typed-range-blocks-041-050/5ba405bc08aaef020868399aa62a429ca4281eda/audits/5ab0fb93d515241f93f6/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks041050'],
                     'p14/typed-range-blocks-051-060/5ba405bc08aaef020868399aa62a429ca4281eda/audits/04ffe9a493c5c5209088/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks051060'],
                     'p14/typed-range-blocks-061-070/5ba405bc08aaef020868399aa62a429ca4281eda/audits/097413574491157d7e8e/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks061070']},
     'paired_owner_lane': 'p14/named-parent-owner-expression-retry/8eabdf5c9563ae73eb091242f376a5b28456f97f/audits/26637257a0de43f2d2e0/lane-0',
     'paired_owners': ['ImbalancedChen.P1FifthMask5NamedParent1Owner', 'ImbalancedChen.P1FifthMask6NamedParent0Owner'],
     'groups': {'p14_new': ['P1HistoricalFifthTypedArchiveRangeBlocks031040',
                            'P1HistoricalFifthTypedArchiveRangeBlocks041050',
                            'P1HistoricalFifthTypedArchiveRangeBlocks051060',
                            'P1HistoricalFifthTypedArchiveRangeBlocks061070',
                            'P1HistoricalFifthTypedBaseGeometryBlocks011020',
                            'P1HistoricalFifthTypedBaseGeometryBlocks021030',
                            'P1HistoricalFifthTypedBaseGeometryBlocks031040',
                            'P1HistoricalFifthTypedBaseGeometryBlocks041050',
                            'P1HistoricalFifthTypedBaseGeometryBlocks051060',
                            'P1HistoricalFifthTypedBaseGeometryBlocks061070',
                            'P1FifthMask6NamedParent0Owner',
                            'P1FifthMask5NamedParent1Owner',
                            'P5OldFifthOneCoordinateVertexChord',
                            'P5OldFifthFiveCoordinateTree']},
     'shared_runs': [],
     'shared_failures': [],
     'excluded_failed_owners': ['ImbalancedChen.P1FifthNamedParentsConcreteJ5',
                                'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric'],
     'protected_roots': {'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
                         'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
                         'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
                         'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
     'reuse_locations': {'/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-011-030/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                                                 'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-011-030/PIPELINE_RESULT.json',
                                                                                                                                                                                 'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                                 'sha256': 'ca3b1bef32e657788b14f7dca698e6c41761905b487378ef73279fac512883b0',
                                                                                                                                                                                 'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks011020',
                                                                                                                                                                                                     'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks021030']},
                         '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-031-050/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                                 'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-031-050/PIPELINE_RESULT.json',
                                                                                                                                                                                 'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                                 'sha256': '8f800b610665799be5ed6342fa3a17b6529d7c8a1581092bc83fe088f3259de2',
                                                                                                                                                                                 'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks031040',
                                                                                                                                                                                                     'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks041050']},
                         '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-001-010/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                                                'path': 'p14_pipeline/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-001-010/PIPELINE_RESULT.json',
                                                                                                                                                                                'source_commit': '649440b8436a3a94cabb096a56385307056f6dcc',
                                                                                                                                                                                'sha256': '16ccdeab8e6ad0672e1890da75a4dddf0b833849f602915c2f6e10120059e0f9',
                                                                                                                                                                                'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks001010']},
                         '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json': {'checkpoint': '05',
                                                                                                                                                            'path': 'p14_pipeline/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
                                                                                                                                                            'source_commit': '8237d0b698ca01153a7e2823510cf67148083c0a',
                                                                                                                                                            'sha256': '6629d933bdd7f5baa5d94bab5ba0a46f76c30fb316215be01b149669a957b264',
                                                                                                                                                            'accepted_owners': ['ImbalancedChen.P1FifthUnitBoxLiteralGainLower',
                                                                                                                                                                                'ImbalancedChen.P1OriginalFifthLiteralKernelModulus',
                                                                                                                                                                                'ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge']},
                         '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json': {'checkpoint': '06',
                                                                                                                                                            'path': 'p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                                                                                                                                            'source_commit': 'c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                                                                                                                                                            'sha256': '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01',
                                                                                                                                                            'accepted_owners': ['ImbalancedChen.P1FifthCheckedUnitBoxWholeGain',
                                                                                                                                                                                'ImbalancedChen.P1FifthMask5RawOwnerLicence',
                                                                                                                                                                                'ImbalancedChen.P1FifthMask6RawOwnerLicence',
                                                                                                                                                                                'ImbalancedChen.P1FifthPositivePartActualOwner',
                                                                                                                                                                                'ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics']},
                         '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                            'path': 'p14_pipeline/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                                                                                                                                            'source_commit': '93501ca11da26d233922739b6aece9987a877d93',
                                                                                                                                                            'sha256': '3fa68feb2f6070286165883499f7ac9150f150f08b01644712c3f3694df2ee2c',
                                                                                                                                                            'accepted_owners': ['ImbalancedChen.P1OriginalFifthMovingMeshFiberBands',
                                                                                                                                                                                'ImbalancedChen.P5OldFifthExact64ChildTiling']},
                         '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                            'path': 'p14_pipeline/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json',
                                                                                                                                                            'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                                                                                                                                                            'sha256': '4f38ec268ec5c0baff349e612e4a4c93ca0ee024a8699222622ef2ee2db60c38',
                                                                                                                                                            'accepted_owners': ['ImbalancedChen.P5OldFifthFrozenGapConcavity']}},
     'pipelines': [{'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-031-050/PIPELINE_RESULT.json',
                    'sha256': '8f800b610665799be5ed6342fa3a17b6529d7c8a1581092bc83fe088f3259de2',
                    'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['typed-range-blocks-031-040', 'typed-range-blocks-041-050'],
                    'held_stages': [],
                    'reuse_field': 'reused_pipeline',
                    'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-011-030/PIPELINE_RESULT.json']},
                   {'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-051-070/PIPELINE_RESULT.json',
                    'sha256': '661800b533cd754036dab20200997d01f1d6c243c48e489471bee506ecfe8d05',
                    'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['typed-range-blocks-051-060', 'typed-range-blocks-061-070'],
                    'held_stages': [],
                    'reuse_field': 'reused_pipeline',
                    'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-031-050/PIPELINE_RESULT.json']},
                   {'path': 'p14_pipeline/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-011-070/PIPELINE_RESULT.json',
                    'sha256': '0c496c330926cb1a1f9409fd0ee31495d648b5caf4480440eb383fd65a5c0bc5',
                    'source_commit': '649440b8436a3a94cabb096a56385307056f6dcc',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['typed-base-blocks-011-020',
                                         'typed-base-blocks-021-030',
                                         'typed-base-blocks-031-040',
                                         'typed-base-blocks-041-050',
                                         'typed-base-blocks-051-060',
                                         'typed-base-blocks-061-070'],
                    'held_stages': [],
                    'reuse_field': 'reused_pipeline',
                    'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-001-010/PIPELINE_RESULT.json']},
                   {'path': 'p14_pipeline/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
                    'sha256': '0ea4e2ae9dcbd2aad8468846b5c65aa3a0439ac784397b239b9b0339a47d1895',
                    'source_commit': '8eabdf5c9563ae73eb091242f376a5b28456f97f',
                    'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                    'completed_stages': ['named-parent-owner-expression-retry',
                                         'named-parents-concrete-j5',
                                         'one-coordinate-chord-retry',
                                         'five-coordinate-tree-expression-retry',
                                         'barycentric'],
                    'held_stages': ['named-parent-actual-integral',
                                    'child-gap-integral',
                                    'pointwise-q',
                                    'named-payload-semantics',
                                    'named-all-children',
                                    'named-child-specific-ratio',
                                    'sharp-directed-log',
                                    'first-f-concavity',
                                    'child-q-jensen',
                                    'actual-child-jensen-integral',
                                    'selected-owner-jensen-reserve',
                                    'named-all-children-selected-jensen',
                                    'named-q80-floor-soundness',
                                    'original-child-integer-wire'],
                    'reuse_field': 'reused_pipelines',
                    'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
                                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json']}],
     'failed_attempts': [{'source_commit': '8eabdf5c9563ae73eb091242f376a5b28456f97f',
                          'stage': 'named-parents-concrete-j5',
                          'module': 'ImbalancedChen.P1FifthNamedParentsConcreteJ5',
                          'source_sha256': 'e11be996ad700f965904f43bb9b0cdfaf6c060789b6262448825989305b8700d',
                          'project_error_count': 5,
                          'reported_error_sections': 5},
                         {'source_commit': '8eabdf5c9563ae73eb091242f376a5b28456f97f',
                          'stage': 'barycentric',
                          'module': 'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric',
                          'source_sha256': 'd98bb7f33cdd9558f0b9a7810c7c0c8cdb3c0377987f697d9705a8c593f2505f',
                          'project_error_count': 22,
                          'reported_error_sections': 12}]},
    '10': {'sealed': True,
            'sha256': '96d7f5980d69b794a60e641a306a72fb89d7f12b47de92a0feada2fe1481509a',
            'bytes': 134960,
            'files': 149,
            'owned': 26,
            'public': 26,
            'audit_lanes': {'p14/named-parents-concrete-j5-expression-retry/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/audits/d799df2fbef0800ff8c9/lane-0': ['ImbalancedChen.P1FifthNamedParentsConcreteJ5'],
                            'p14/typed-key-uniqueness-core/504f9546a9d919ed1977c396517d5838ffd0284c/audits/0eeda616f9249af51a77/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore']},
            'owned_names_by_module': {'ImbalancedChen.P1FifthNamedParentsConcreteJ5': ['ImbalancedChen.P1FifthNamedParentsConcreteJ5.namedJ5',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent0_cell_mem_namedJ5',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent0_mem_selected_namedJ5',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent0_namedJ5_rawOwnerDomain',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent0_original_stop_and_rough',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent1_cell_mem_namedJ5',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent1_mem_selected_namedJ5',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent1_namedJ5_rawOwnerDomain',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent1_original_stop_and_rough',
                                                                                       'ImbalancedChen.P1FifthNamedParentsConcreteJ5.parent0_original_stop_and_rough._proof_1'],
                                      'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore': ['ImbalancedChen.P1HistoricalFifthTypedKeyPartition.AdjacentStrict',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.adjacentStrictDecidable',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.adjacentStrict_head_lt',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.adjacentStrict_nodup',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.adjacentStrict_tail',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.codeOfKey',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.sortedCodes',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.typedCodes',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.AdjacentStrict._f',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.AdjacentStrict._sunfold',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.AdjacentStrict._unsafe_rec',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.AdjacentStrict.match_1',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.adjacentStrictDecidable._proof_1',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.adjacentStrictDecidable._proof_2',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.adjacentStrictDecidable._proof_3',
                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedKeyPartition.codeOfKey._proof_1']},
            'groups': {'p14_new': ['P1FifthNamedParentsConcreteJ5', 'P1HistoricalFifthTypedKeyUniquenessCore']},
            'shared_runs': [],
            'shared_failures': [],
            'excluded_failed_owners': ['ImbalancedChen.P1FifthNamedParentActualIntegral',
                                       'ImbalancedChen.P1OriginalFifthActualCrossingSections',
                                       'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate'],
            'protected_roots': {'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
                                'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
                                'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
                                'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
            'reuse_locations': {'/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json': {'checkpoint': '06',
                                                                                                                                                                   'path': 'p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                                                                                                                                                   'source_commit': 'c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                                                                                                                                                                   'sha256': '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01',
                                                                                                                                                                   'accepted_owners': ['ImbalancedChen.P1FifthCheckedUnitBoxWholeGain',
                                                                                                                                                                                       'ImbalancedChen.P1FifthMask5RawOwnerLicence',
                                                                                                                                                                                       'ImbalancedChen.P1FifthMask6RawOwnerLicence',
                                                                                                                                                                                       'ImbalancedChen.P1FifthPositivePartActualOwner',
                                                                                                                                                                                       'ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics']},
                                '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json': {'checkpoint': '06',
                                                                                                                                                                   'path': 'p14_pipeline/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                                                                                                                                                   'source_commit': 'a700772dbddaa09df497590c7d1b54d6e488f812',
                                                                                                                                                                   'sha256': 'f999d0bd6b1b7ba4c4a8eb7712ccbb0f3ca44891430c7a4fcfc100bcb91ecd09',
                                                                                                                                                                   'accepted_owners': ['ImbalancedChen.P1OriginalFifthActualOwnerCrossingVolume']},
                                '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                                   'path': 'p14_pipeline/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                                                                                                                                                   'source_commit': '93501ca11da26d233922739b6aece9987a877d93',
                                                                                                                                                                   'sha256': '3fa68feb2f6070286165883499f7ac9150f150f08b01644712c3f3694df2ee2c',
                                                                                                                                                                   'accepted_owners': ['ImbalancedChen.P1OriginalFifthMovingMeshFiberBands',
                                                                                                                                                                                       'ImbalancedChen.P5OldFifthExact64ChildTiling']},
                                '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                                   'path': 'p14_pipeline/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json',
                                                                                                                                                                   'source_commit': '89db42762b5f303602608587b3d610cd7ebe9a54',
                                                                                                                                                                   'sha256': '6b57261b2316f51a376174d747b9b92b0cf172ce30e5deb1eb0673cd5a1301e9',
                                                                                                                                                                   'accepted_owners': ['ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume']},
                                '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                                    'path': 'p14_pipeline/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
                                                                                                                                                                                    'source_commit': '8eabdf5c9563ae73eb091242f376a5b28456f97f',
                                                                                                                                                                                    'sha256': '0ea4e2ae9dcbd2aad8468846b5c65aa3a0439ac784397b239b9b0339a47d1895',
                                                                                                                                                                                    'accepted_owners': ['ImbalancedChen.P1FifthMask5NamedParent1Owner',
                                                                                                                                                                                                        'ImbalancedChen.P1FifthMask6NamedParent0Owner',
                                                                                                                                                                                                        'ImbalancedChen.P5OldFifthFiveCoordinateTree',
                                                                                                                                                                                                        'ImbalancedChen.P5OldFifthOneCoordinateVertexChord']}},
            'pipelines': [{'path': 'p14_pipeline/c547bc436499d85513e7e6a251b9f1c898ba22e4/PIPELINE_RESULT.json',
                           'sha256': '9ef684dc66658ed063ac74b5e334d8e1e6f5e1f4144c01e45ea96d959f0378db',
                           'source_commit': 'c547bc436499d85513e7e6a251b9f1c898ba22e4',
                           'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                           'completed_stages': ['owner-crossing-sections-expression-retry'],
                           'held_stages': ['owner-b13-error',
                                           'adopted-owner-bank',
                                           'uniform-adopted-error',
                                           'indexed-owner-archive',
                                           'indexed-bank-error',
                                           'buffer-owner-geometry',
                                           'common-policy-inputs'],
                           'reuse_field': 'reused_pipelines',
                           'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                            '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                            '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                            '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json']},
                          {'path': 'p14_pipeline/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json',
                           'sha256': '9445e6f4d9ad887cff065c3e501d7e60ec1984261b001029353619e252d9dc3e',
                           'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                           'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                           'completed_stages': ['named-parents-concrete-j5-expression-retry',
                                                'named-parent-actual-integral'],
                           'held_stages': [],
                           'reuse_field': 'reused_pipeline',
                           'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json']},
                          {'path': 'p14_pipeline/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json',
                           'sha256': '6a7f93437ebe3d802360af8993fd513b5e9a8c028e63d9d854b83247e57d758f',
                           'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c',
                           'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                           'completed_stages': ['typed-key-uniqueness-core', 'typed-key-uniqueness-certificate'],
                           'held_stages': [],
                           'reuse_field': None,
                           'reused_paths': []}],
            'key_pipeline_path': 'p14_pipeline/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json',
            'failed_attempts': [{'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                                 'stage': 'named-parent-actual-integral',
                                 'module': 'ImbalancedChen.P1FifthNamedParentActualIntegral',
                                 'source_sha256': 'c41b2904b26034bbc1a8d03e65b0062e038d0f95ace8ffe7d3e9745ecab191ac',
                                 'project_error_count': 2,
                                 'reported_error_sections': 2},
                                {'source_commit': 'c547bc436499d85513e7e6a251b9f1c898ba22e4',
                                 'stage': 'owner-crossing-sections-expression-retry',
                                 'module': 'ImbalancedChen.P1OriginalFifthActualCrossingSections',
                                 'source_sha256': '299e2507e0a7502a5d019a8823c913d550f2a7030af98dfb5705583d02df996b',
                                 'project_error_count': 4,
                                 'reported_error_sections': 4},
                                {'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c',
                                 'stage': 'typed-key-uniqueness-certificate',
                                 'module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate',
                                 'source_sha256': '996a8791130bd9ad6db3017d534ef25136a089a66422ec26a32eba97f47f8da3',
                                 'project_error_count': 2,
                                 'reported_error_sections': 2}]},
    '11': {'sealed': True,
        'sha256': '1c150b185c21ddd65d8aafd2a57f22823c2ae49a76c5b3ca94e817050bb989c7',
        'bytes': 102260,
        'files': 452,
        'owned': 184,
        'public': 184,
        'audit_lanes': {'p14/typed-base-blocks-071-080/649440b8436a3a94cabb096a56385307056f6dcc/audits/54f25f48e20311b1e753/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks071080'],
                        'p14/typed-base-blocks-081-090/649440b8436a3a94cabb096a56385307056f6dcc/audits/4f673eff94e00a199f24/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks081090'],
                        'p14/typed-base-blocks-091-100/649440b8436a3a94cabb096a56385307056f6dcc/audits/79a501cc56b898320eab/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks091100'],
                        'p14/typed-base-blocks-101-110/649440b8436a3a94cabb096a56385307056f6dcc/audits/5603d98d3c2d0e8ff770/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks101110'],
                        'p14/typed-base-blocks-111-120/649440b8436a3a94cabb096a56385307056f6dcc/audits/2656c54b28ed28eb66b1/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks111120'],
                        'p14/typed-base-blocks-121-130/649440b8436a3a94cabb096a56385307056f6dcc/audits/db1fc99a4797e8a0b436/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks121130'],
                        'p14/typed-base-blocks-131-140/649440b8436a3a94cabb096a56385307056f6dcc/audits/190cf5bdd6a020f95854/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks131140'],
                        'p14/typed-base-blocks-141-142/649440b8436a3a94cabb096a56385307056f6dcc/audits/bb4caed3d780dc26b677/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks141142'],
                        'p14/typed-range-blocks-071-080/5ba405bc08aaef020868399aa62a429ca4281eda/audits/b2eb3674225ab7a44cc1/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks071080'],
                        'p14/typed-range-blocks-081-090/5ba405bc08aaef020868399aa62a429ca4281eda/audits/1b2288cdc5a15b863694/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks081090']},
        'owned_names_by_module': {'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks071080': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block071_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block072_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block073_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block074_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block075_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block076_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block077_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block078_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block079_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block080_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block071_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block072_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block073_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block074_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block075_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block076_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block077_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block078_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block079_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block080_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks081090': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block081_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block082_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block083_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block084_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block085_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block086_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block087_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block088_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block089_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block090_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block081_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block082_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block083_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block084_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block085_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block086_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block087_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block088_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block089_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block090_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks091100': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block091_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block092_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block093_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block094_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block095_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block096_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block097_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block098_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block099_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block100_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block091_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block092_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block093_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block094_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block095_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block096_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block097_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block098_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block099_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block100_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks101110': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block101_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block102_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block103_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block104_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block105_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block106_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block107_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block108_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block109_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block110_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block101_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block102_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block103_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block104_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block105_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block106_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block107_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block108_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block109_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block110_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks111120': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block111_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block112_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block113_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block114_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block115_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block116_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block117_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block118_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block119_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block120_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block111_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block112_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block113_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block114_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block115_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block116_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block117_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block118_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block119_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block120_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks121130': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block121_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block122_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block123_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block124_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block125_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block126_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block127_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block128_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block129_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block130_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block121_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block122_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block123_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block124_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block125_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block126_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block127_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block128_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block129_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block130_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks131140': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block131_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block132_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block133_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block134_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block135_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block136_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block137_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block138_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block139_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block140_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block131_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block132_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block133_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block134_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block135_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block136_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block137_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block138_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block139_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block140_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks141142': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block141_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block142_lower_key_bounds',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block141_lower_key_bounds._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedBaseGeometry.block142_lower_key_bounds._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks071080': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block071_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block072_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block073_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block074_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block075_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block076_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block077_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block078_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block079_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block080_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block071_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block072_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block073_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block074_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block075_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block076_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block077_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block078_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block079_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block080_typed_valid._proof_1_1'],
                                  'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks081090': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block081_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block082_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block083_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block084_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block085_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block086_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block087_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block088_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block089_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block090_typed_valid',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block081_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block082_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block083_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block084_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block085_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block086_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block087_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block088_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block089_typed_valid._proof_1_1',
                                                                                                    'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block090_typed_valid._proof_1_1']},
        'groups': {'p14_new': ['P1HistoricalFifthTypedBaseGeometryBlocks071080',
                               'P1HistoricalFifthTypedBaseGeometryBlocks081090',
                               'P1HistoricalFifthTypedBaseGeometryBlocks091100',
                               'P1HistoricalFifthTypedBaseGeometryBlocks101110',
                               'P1HistoricalFifthTypedBaseGeometryBlocks111120',
                               'P1HistoricalFifthTypedBaseGeometryBlocks121130',
                               'P1HistoricalFifthTypedBaseGeometryBlocks131140',
                               'P1HistoricalFifthTypedBaseGeometryBlocks141142',
                               'P1HistoricalFifthTypedArchiveRangeBlocks071080',
                               'P1HistoricalFifthTypedArchiveRangeBlocks081090']},
        'shared_runs': [],
        'shared_failures': [],
        'excluded_failed_owners': [],
        'protected_roots': {'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
                            'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
                            'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
                            'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
        'roots': {'p14/typed-base-blocks-071-080/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-071-080/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-base-blocks-081-090/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-081-090/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-base-blocks-091-100/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-091-100/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-base-blocks-101-110/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-101-110/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-base-blocks-111-120/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-111-120/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-base-blocks-121-130/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-121-130/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-base-blocks-131-140/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-131-140/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-base-blocks-141-142/649440b8436a3a94cabb096a56385307056f6dcc': '20261125-p14-continuation/typed-base-blocks-141-142/649440b8436a3a94cabb096a56385307056f6dcc',
                  'p14/typed-range-blocks-071-080/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-071-080/5ba405bc08aaef020868399aa62a429ca4281eda',
                  'p14/typed-range-blocks-081-090/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-081-090/5ba405bc08aaef020868399aa62a429ca4281eda'},
        'single_files': {'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json',
                         'p14_pipeline/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-071-142/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-071-142/PIPELINE_RESULT.json'},
        'reuse_locations': {'/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-051-070/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                                    'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-051-070/PIPELINE_RESULT.json',
                                                                                                                                                                                    'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                                    'sha256': '661800b533cd754036dab20200997d01f1d6c243c48e489471bee506ecfe8d05',
                                                                                                                                                                                    'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks051060',
                                                                                                                                                                                                        'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks061070']},
                            '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-011-070/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                                   'path': 'p14_pipeline/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-011-070/PIPELINE_RESULT.json',
                                                                                                                                                                                   'source_commit': '649440b8436a3a94cabb096a56385307056f6dcc',
                                                                                                                                                                                   'sha256': '0c496c330926cb1a1f9409fd0ee31495d648b5caf4480440eb383fd65a5c0bc5',
                                                                                                                                                                                   'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks011020',
                                                                                                                                                                                                       'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks021030',
                                                                                                                                                                                                       'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks031040',
                                                                                                                                                                                                       'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks041050',
                                                                                                                                                                                                       'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks051060',
                                                                                                                                                                                                       'ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks061070']}},
        'pipelines': [{'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json',
                       'sha256': 'f9b8e340021dd52e1553867b55f7b2a29303530c1d54bcef545d6b705c78e2ee',
                       'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                       'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                       'completed_stages': ['typed-range-blocks-071-080', 'typed-range-blocks-081-090'],
                       'held_stages': [],
                       'reuse_field': 'reused_pipeline',
                       'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-051-070/PIPELINE_RESULT.json']},
                      {'path': 'p14_pipeline/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-071-142/PIPELINE_RESULT.json',
                       'sha256': '14959aee48c09d8e94c4ee5d5c6821c502cbd0f3828f27fd2c82d0f45aea221b',
                       'source_commit': '649440b8436a3a94cabb096a56385307056f6dcc',
                       'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                       'completed_stages': ['typed-base-blocks-071-080',
                                            'typed-base-blocks-081-090',
                                            'typed-base-blocks-091-100',
                                            'typed-base-blocks-101-110',
                                            'typed-base-blocks-111-120',
                                            'typed-base-blocks-121-130',
                                            'typed-base-blocks-131-140',
                                            'typed-base-blocks-141-142'],
                       'held_stages': [],
                       'reuse_field': 'reused_pipeline',
                       'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/649440b8436a3a94cabb096a56385307056f6dcc/base-blocks-011-070/PIPELINE_RESULT.json']}],
        'failed_attempts': []},
}
# Checkpoint 12 is fixed to the original successful read-only export.
# Later retries/aggregates are outside these eight roots and five final pipelines.
CHECKPOINTS['12'] = {'sealed': True,
 'sha256': 'eb46e63447c97654056ae0c94003470729c9415c95f721f9d3e55e31b92d8071',
 'bytes': 175240,
 'files': 262,
 'owned': 96,
 'public': 89,
 'export_manifest_sha256': 'cd34e2489f82c7c1dcf20f610098d37d8257c0e2ffe85bc102cbcacdb3107f8d',
 'audit_lanes': {'p14/named-parent-actual-integral-kernel-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/audits/bd94eb1a2b8b5cbd989a/lane-0': ['ImbalancedChen.P1FifthNamedParentActualIntegral'],
                 'p14/owner-crossing-sections-projection-cast-retry/957c7c773bef05a6271fb504c06d967d67ce2908/audits/1064a90312ca309c8cc2/lane-0': ['ImbalancedChen.P1OriginalFifthActualCrossingSections'],
                 'p14/typed-range-blocks-091-100/5ba405bc08aaef020868399aa62a429ca4281eda/audits/b732fce66ccbbab6c6d2/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks091100'],
                 'p14/typed-range-blocks-101-110/5ba405bc08aaef020868399aa62a429ca4281eda/audits/1f224363fcf478efc1ca/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks101110']},
 'owned_names_by_module': {'ImbalancedChen.P1FifthNamedParentActualIntegral': ['ImbalancedChen.P1FifthNamedParentActualIntegral.actual_selected_integral_eq_two_named_parents',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.namedRecords',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_family_gates',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_grid',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_keys_injective',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_mask',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_raw_boxes_disjoint',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent0_all_decoded_gates',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent0_complete_raw_gate',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent0_original_eligible',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent1_all_decoded_gates',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent1_complete_raw_gate',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent1_original_eligible',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent_keys_ne',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parents_ne',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.rawBoxGateCheck_of_loss_le',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.selected_namedJ5_eq',
                                                                               'ImbalancedChen.P1FifthGrid400UnitBoxPartition.rowKey.eq_1',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.actual_selected_integral_eq_two_named_parents._simp_1_2',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.namedRecords.eq_1',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_family_gates._simp_1_2',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_family_gates._simp_1_3',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_grid._simp_1_2',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_grid._simp_1_3',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_keys_injective._simp_1_2',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_keys_injective._simp_1_3',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_mask._simp_1_2',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.named_mask._simp_1_3',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent0_complete_raw_gate._proof_1_1',
                                                                               'ImbalancedChen.P1FifthNamedParentActualIntegral.parent1_complete_raw_gate._proof_1_1'],
                           'ImbalancedChen.P1OriginalFifthActualCrossingSections': ['ImbalancedChen.P1OriginalFifthActualCrossingSections.Base',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.Point',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.actualGammaBand',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.actualGammaBand_volume_le',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.actual_crossing_fiber_subset_three_bands',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.actual_ownerSymmDiff_fiber_volume_le',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.actual_ownerSymmDiff_volume_le',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.actual_section_gamma_quasirise',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.fiber',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.insertFirst',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.insertFirst_rest',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.insertFirst_zero',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.owner_index_eq_of_coordinate_eq',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.owner_index_le_of_coordinate_le',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.splitEquiv',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.zeroGamma',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualCrossingSections.0.ImbalancedChen.P1OriginalFifthActualCrossingSections.box_full_at_zero',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualCrossingSections.0.ImbalancedChen.P1OriginalFifthActualCrossingSections.box_lx_cast',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualCrossingSections.0.ImbalancedChen.P1OriginalFifthActualCrossingSections.fixedBase_mesh',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualCrossingSections.0.ImbalancedChen.P1OriginalFifthActualCrossingSections.fixedBase_raw',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualCrossingSections.0.ImbalancedChen.P1OriginalFifthActualCrossingSections.real_between_of_directed_crossing',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.owner_index_le_of_coordinate_le._proof_1_1',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.splitEquiv._proof_1',
                                                                                    'ImbalancedChen.P1OriginalFifthActualCrossingSections.zeroGamma.eq_1',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualCrossingSections.0.ImbalancedChen.P1OriginalFifthActualCrossingSections.fixedBase_mesh._simp_1_1',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualCrossingSections.0.ImbalancedChen.P1OriginalFifthActualCrossingSections.fixedBase_raw._simp_1_1'],
                           'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks091100': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block091_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block092_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block093_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block094_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block095_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block096_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block097_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block098_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block099_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block100_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block091_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block092_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block093_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block094_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block095_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block096_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block097_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block098_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block099_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block100_typed_valid._proof_1_1'],
                           'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks101110': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block101_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block102_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block103_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block104_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block105_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block106_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block107_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block108_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block109_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block110_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block101_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block102_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block103_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block104_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block105_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block106_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block107_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block108_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block109_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block110_typed_valid._proof_1_1']},
 'owned_export_sha256_by_lane': {'p14/named-parent-actual-integral-kernel-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/audits/bd94eb1a2b8b5cbd989a/lane-0': '4959ad0073f362c586e014d114b0b7556424bb7d359022a2698441f1ad65b5b8',
                                 'p14/owner-crossing-sections-projection-cast-retry/957c7c773bef05a6271fb504c06d967d67ce2908/audits/1064a90312ca309c8cc2/lane-0': '7bfd672b39025b777e8ad944db478d9f5b264b9e9e7f880b04e069e48b735da4',
                                 'p14/typed-range-blocks-091-100/5ba405bc08aaef020868399aa62a429ca4281eda/audits/b732fce66ccbbab6c6d2/lane-0': '6a2844a01ded628ca559ab69e154c9071512341a6f7081d857bd90cedbf59bfe',
                                 'p14/typed-range-blocks-101-110/5ba405bc08aaef020868399aa62a429ca4281eda/audits/1f224363fcf478efc1ca/lane-0': '11aeea8117d23e0c5cb31303500c51f7adac2b0c5251336dfa906b92bfdf93d9'},
 'groups': {'p14_new': ['P1FifthNamedParentActualIntegral',
                        'P1HistoricalFifthTypedArchiveRangeBlocks091100',
                        'P1HistoricalFifthTypedArchiveRangeBlocks101110',
                        'P1OriginalFifthActualCrossingSections']},
 'shared_runs': [],
 'shared_failures': [],
 'excluded_failed_owners': ['ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate',
                            'ImbalancedChen.P1OriginalFifthActualB13IntegralError',
                            'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric'],
 'protected_roots': {'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
                     'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
                     'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
                     'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
 'roots': {'p14/barycentric-expression-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a': '20261125-p14-continuation/barycentric-expression-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
           'p14/named-parent-actual-integral-kernel-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a': '20261125-p14-continuation/named-parent-actual-integral-kernel-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
           'p14/owner-b13-error/957c7c773bef05a6271fb504c06d967d67ce2908': '20261125-p14-continuation/owner-b13-error/957c7c773bef05a6271fb504c06d967d67ce2908',
           'p14/owner-b13-label-norm-retry/295f055328ea89ad465b7c2d33d7a171dbcd78f8': '20261125-p14-continuation/owner-b13-label-norm-retry/295f055328ea89ad465b7c2d33d7a171dbcd78f8',
           'p14/owner-crossing-sections-projection-cast-retry/957c7c773bef05a6271fb504c06d967d67ce2908': '20261125-p14-continuation/owner-crossing-sections-projection-cast-retry/957c7c773bef05a6271fb504c06d967d67ce2908',
           'p14/typed-key-uniqueness-certificate-syntax-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a': '20261125-p14-continuation/typed-key-uniqueness-certificate-syntax-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
           'p14/typed-range-blocks-091-100/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-091-100/5ba405bc08aaef020868399aa62a429ca4281eda',
           'p14/typed-range-blocks-101-110/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-101-110/5ba405bc08aaef020868399aa62a429ca4281eda'},
 'single_files': {'p14_pipeline/295f055328ea89ad465b7c2d33d7a171dbcd78f8/owner-b13-and-label5-consumers/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/295f055328ea89ad465b7c2d33d7a171dbcd78f8/owner-b13-and-label5-consumers/PIPELINE_RESULT.json',
                  'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-091-110/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-091-110/PIPELINE_RESULT.json',
                  'p14_pipeline/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json',
                  'p14_pipeline/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json',
                  'p14_pipeline/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/typed-key-uniqueness-syntax-retry/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/typed-key-uniqueness-syntax-retry/PIPELINE_RESULT.json'},
 'stage_bindings': {'p14/barycentric-expression-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a': {'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                                                                                                  'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/barycentric-expression-retry.json',
                                                                                                  'manifest_sha256': 'cb5faf85c884b8032e51dd78616a732d4ae78dfbfb0ca4ce4072ef0195fd0920',
                                                                                                  'targets': {'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric': 'c63382a28fd0efba9b86beac5b08429d56624cbcf092d9f053fe0fd8343e9fda'}},
                    'p14/named-parent-actual-integral-kernel-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a': {'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                                                                                                               'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                               'manifest_path': 'docs/p1/20261125/p14-continuation/stages/named-parent-actual-integral-kernel-retry.json',
                                                                                                               'manifest_sha256': '3a53d8c6e94c97640eb7298e4d6dce30f2b4797911d1779b0fb2c4280df02dc4',
                                                                                                               'targets': {'ImbalancedChen.P1FifthNamedParentActualIntegral': '7601b7fe3232c739bdf3cd11568368828f0e7c18dff1107e0f837af550e30e6f'}},
                    'p14/owner-b13-error/957c7c773bef05a6271fb504c06d967d67ce2908': {'source_commit': '957c7c773bef05a6271fb504c06d967d67ce2908',
                                                                                     'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                     'manifest_path': 'docs/p1/20261125/p14-continuation/stages/owner-b13-error.json',
                                                                                     'manifest_sha256': '62f9a0240e15f255d3cee39c912ecebf702637ed307d71b61a35ef385785d573',
                                                                                     'targets': {'ImbalancedChen.P1OriginalFifthActualB13IntegralError': '16f5d88e0b74ee73d5519871317fc72c685f250412d7c112113882197410bd16'}},
                    'p14/owner-b13-label-norm-retry/295f055328ea89ad465b7c2d33d7a171dbcd78f8': {'source_commit': '295f055328ea89ad465b7c2d33d7a171dbcd78f8',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/owner-b13-label-norm-retry.json',
                                                                                                'manifest_sha256': '0ec9ed3c818f354a495d9286ca1dd4dca499b7f42b64b595b02c954a021c6615',
                                                                                                'targets': {'ImbalancedChen.P1OriginalFifthActualB13IntegralError': '9216438e1268084a2ae839605d60e794d2c09857036f0ea044a24b22a884363f'}},
                    'p14/owner-crossing-sections-projection-cast-retry/957c7c773bef05a6271fb504c06d967d67ce2908': {'source_commit': '957c7c773bef05a6271fb504c06d967d67ce2908',
                                                                                                                   'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                                   'manifest_path': 'docs/p1/20261125/p14-continuation/stages/owner-crossing-sections-projection-cast-retry.json',
                                                                                                                   'manifest_sha256': '15c85671fa03fa61999f19422b845a4d08925759df09d3981c7b15f5e7168d24',
                                                                                                                   'targets': {'ImbalancedChen.P1OriginalFifthActualCrossingSections': '7dcd1f46ce5443a58c57d6cc4fbd7280b5bffd3010daf81efbd48b3acb0dbfc9'}},
                    'p14/typed-key-uniqueness-certificate-syntax-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a': {'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                                                                                                                   'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                                   'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-key-uniqueness-certificate-syntax-retry.json',
                                                                                                                   'manifest_sha256': '9fa7d5c03b05e399e9664693e7ed380e7e6933817be7545c7e66bdc5fd4e9af6',
                                                                                                                   'targets': {'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate': 'f7053379fd6427b3c78aeff1c2942bee913426b36b3155773acdd735eb4455f8'}},
                    'p14/typed-range-blocks-091-100/5ba405bc08aaef020868399aa62a429ca4281eda': {'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-range-blocks-091-100.json',
                                                                                                'manifest_sha256': '7b246d433bdb5251176254f9792b8b7e8878d55262e682cd382618046f88408a',
                                                                                                'targets': {'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks091100': 'd70930ba717ab8fea2b7cc875114929a49fcd2f1d139082dd6eacd130eff88a3'}},
                    'p14/typed-range-blocks-101-110/5ba405bc08aaef020868399aa62a429ca4281eda': {'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-range-blocks-101-110.json',
                                                                                                'manifest_sha256': '8e9a7a3ad22da682fe608f73b761b5e403242b49fa0fbec2018a957642e1dc6f',
                                                                                                'targets': {'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks101110': '9fa9d116aae50671e73c814cfdba07851059716ecb4c5aa3ab4ce641129b8a0e'}}},
 'reuse_locations': {'/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json': {'checkpoint': '06',
                                                                                                                                                        'path': 'p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                                                                                                                                        'source_commit': 'c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                                                                                                                                                        'sha256': '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01',
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1FifthCheckedUnitBoxWholeGain',
                                                                                                                                                                            'ImbalancedChen.P1FifthMask5RawOwnerLicence',
                                                                                                                                                                            'ImbalancedChen.P1FifthMask6RawOwnerLicence',
                                                                                                                                                                            'ImbalancedChen.P1FifthPositivePartActualOwner',
                                                                                                                                                                            'ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json': {'checkpoint': '06',
                                                                                                                                                        'path': 'p14_pipeline/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                                                                                                                                        'source_commit': 'a700772dbddaa09df497590c7d1b54d6e488f812',
                                                                                                                                                        'sha256': 'f999d0bd6b1b7ba4c4a8eb7712ccbb0f3ca44891430c7a4fcfc100bcb91ecd09',
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthActualOwnerCrossingVolume']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                        'path': 'p14_pipeline/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                                                                                                                                        'source_commit': '93501ca11da26d233922739b6aece9987a877d93',
                                                                                                                                                        'sha256': '3fa68feb2f6070286165883499f7ac9150f150f08b01644712c3f3694df2ee2c',
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthMovingMeshFiberBands',
                                                                                                                                                                            'ImbalancedChen.P5OldFifthExact64ChildTiling']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                        'path': 'p14_pipeline/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json',
                                                                                                                                                        'source_commit': '89db42762b5f303602608587b3d610cd7ebe9a54',
                                                                                                                                                        'sha256': '6b57261b2316f51a376174d747b9b92b0cf172ce30e5deb1eb0673cd5a1301e9',
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json': {'checkpoint': '10',
                                                                                                                                                                             'path': 'p14_pipeline/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json',
                                                                                                                                                                             'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c',
                                                                                                                                                                             'sha256': '6a7f93437ebe3d802360af8993fd513b5e9a8c028e63d9d854b83247e57d758f',
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json': {'checkpoint': '05',
                                                                                                                                                        'path': 'p14_pipeline/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
                                                                                                                                                        'source_commit': '8237d0b698ca01153a7e2823510cf67148083c0a',
                                                                                                                                                        'sha256': '6629d933bdd7f5baa5d94bab5ba0a46f76c30fb316215be01b149669a957b264',
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1FifthUnitBoxLiteralGainLower',
                                                                                                                                                                            'ImbalancedChen.P1OriginalFifthLiteralKernelModulus',
                                                                                                                                                                            'ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                        'path': 'p14_pipeline/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json',
                                                                                                                                                        'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                                                                                                                                                        'sha256': '4f38ec268ec5c0baff349e612e4a4c93ca0ee024a8699222622ef2ee2db60c38',
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P5OldFifthFrozenGapConcavity']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                         'path': 'p14_pipeline/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
                                                                                                                                                                         'source_commit': '8eabdf5c9563ae73eb091242f376a5b28456f97f',
                                                                                                                                                                         'sha256': '0ea4e2ae9dcbd2aad8468846b5c65aa3a0439ac784397b239b9b0339a47d1895',
                                                                                                                                                                         'accepted_owners': ['ImbalancedChen.P1FifthMask5NamedParent1Owner',
                                                                                                                                                                                             'ImbalancedChen.P1FifthMask6NamedParent0Owner',
                                                                                                                                                                                             'ImbalancedChen.P5OldFifthFiveCoordinateTree',
                                                                                                                                                                                             'ImbalancedChen.P5OldFifthOneCoordinateVertexChord']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json': {'checkpoint': '10',
                                                                                                                                                                       'path': 'p14_pipeline/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json',
                                                                                                                                                                       'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                                                                                                                                                                       'sha256': '9445e6f4d9ad887cff065c3e501d7e60ec1984261b001029353619e252d9dc3e',
                                                                                                                                                                       'accepted_owners': ['ImbalancedChen.P1FifthNamedParentsConcreteJ5']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json': {'checkpoint': '11',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': 'f9b8e340021dd52e1553867b55f7b2a29303530c1d54bcef545d6b705c78e2ee',
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks071080',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks081090']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json': {'checkpoint': '12',
                                                                                                                                                        'path': 'p14_pipeline/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json',
                                                                                                                                                        'source_commit': '957c7c773bef05a6271fb504c06d967d67ce2908',
                                                                                                                                                        'sha256': '1b087a482fbf661d2b1b2a2ddc02d0cbc0b73547249ebc25e005dc1b554c8911',
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthActualCrossingSections']}},
 'pipelines': [{'path': 'p14_pipeline/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json',
                'sha256': '1b087a482fbf661d2b1b2a2ddc02d0cbc0b73547249ebc25e005dc1b554c8911',
                'source_commit': '957c7c773bef05a6271fb504c06d967d67ce2908',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['owner-crossing-sections-projection-cast-retry', 'owner-b13-error'],
                'held_stages': ['adopted-owner-bank',
                                'uniform-adopted-error',
                                'indexed-owner-archive',
                                'indexed-bank-error',
                                'buffer-owner-geometry',
                                'common-policy-inputs'],
                'reuse_field': 'reused_pipelines',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json']},
               {'path': 'p14_pipeline/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/typed-key-uniqueness-syntax-retry/PIPELINE_RESULT.json',
                'sha256': 'c9e3d1998165e23da3853c35880ae9f03a8502479355574eac66fdbd003fa225',
                'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['typed-key-uniqueness-certificate-syntax-retry'],
                'held_stages': [],
                'reuse_field': 'reused_pipeline',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json']},
               {'path': 'p14_pipeline/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json',
                'sha256': '751a4fef4a9774c45dad46e5d10afc81a135571262d83d9c50ac5bf76ce4bda8',
                'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['named-parent-actual-integral-kernel-retry',
                                     'barycentric-expression-retry'],
                'held_stages': ['child-gap-namespace-retry',
                                'pointwise-q-namespace-retry',
                                'named-payload-semantics',
                                'named-all-children',
                                'named-child-specific-ratio',
                                'sharp-directed-log',
                                'first-f-concavity-namespace-retry',
                                'child-q-jensen-namespace-retry',
                                'actual-child-jensen-integral',
                                'selected-owner-jensen-reserve',
                                'named-all-children-selected-jensen',
                                'named-q80-floor-soundness',
                                'original-child-integer-wire'],
                'reuse_field': 'reused_pipelines',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json']},
               {'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-091-110/PIPELINE_RESULT.json',
                'sha256': '1731ce3651588d9e89b06f0c68c6909bc9f6967df8f3887e81f423f4d1dd0e9e',
                'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['typed-range-blocks-091-100', 'typed-range-blocks-101-110'],
                'held_stages': [],
                'reuse_field': 'reused_pipeline',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json']},
               {'path': 'p14_pipeline/295f055328ea89ad465b7c2d33d7a171dbcd78f8/owner-b13-and-label5-consumers/PIPELINE_RESULT.json',
                'sha256': '7613c8bc216cd39e2596dd2358265133fcec7c0697a9e58db3c2dab24c636c68',
                'source_commit': '295f055328ea89ad465b7c2d33d7a171dbcd78f8',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['owner-b13-label-norm-retry'],
                'held_stages': ['adopted-owner-bank-label5-retry',
                                'uniform-adopted-error',
                                'indexed-owner-archive-label5-retry',
                                'indexed-bank-error',
                                'buffer-owner-geometry-label5-retry',
                                'common-policy-inputs'],
                'reuse_field': 'reused_pipelines',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json']}],
 'failed_attempts': [{'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                      'stage': 'barycentric-expression-retry',
                      'module': 'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric',
                      'source_sha256': 'c63382a28fd0efba9b86beac5b08429d56624cbcf092d9f053fe0fd8343e9fda',
                      'project_error_count': 4,
                      'reported_error_sections': 4,
                      'normal_log_sha256': '0d8d75c6767cb4659bc09cce10c5547edfb6d62e244fefa7044e488b148d07e6'},
                     {'source_commit': '957c7c773bef05a6271fb504c06d967d67ce2908',
                      'stage': 'owner-b13-error',
                      'module': 'ImbalancedChen.P1OriginalFifthActualB13IntegralError',
                      'source_sha256': '16f5d88e0b74ee73d5519871317fc72c685f250412d7c112113882197410bd16',
                      'project_error_count': 4,
                      'reported_error_sections': 4,
                      'normal_log_sha256': '7300eac3e3a89dfe802208b68f0b66b899b9312bd5fd245fccda7c705db25d83'},
                     {'source_commit': '295f055328ea89ad465b7c2d33d7a171dbcd78f8',
                      'stage': 'owner-b13-label-norm-retry',
                      'module': 'ImbalancedChen.P1OriginalFifthActualB13IntegralError',
                      'source_sha256': '9216438e1268084a2ae839605d60e794d2c09857036f0ea044a24b22a884363f',
                      'project_error_count': 3,
                      'reported_error_sections': 3,
                      'normal_log_sha256': '3c6a6ce048636842c5ae853c51c062aaed25ca110d2ddde769d6ad70d7407405'},
                     {'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                      'stage': 'typed-key-uniqueness-certificate-syntax-retry',
                      'module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate',
                      'source_sha256': 'f7053379fd6427b3c78aeff1c2942bee913426b36b3155773acdd735eb4455f8',
                      'project_error_count': 1,
                      'reported_error_sections': 1,
                      'normal_log_sha256': '04420a0add4a41d344cdb5ac059b767061e2d6e2daaa9b33db4a1e4cef311c2c'}]}

CHECKPOINTS['13'] = {'sealed': True,
 'sha256': 'a5c6b79fe9af63d181047e04eaccd374fea27f17d63fb7a5f6fc8bd111a46c75',
 'bytes': 235224,
 'files': 494,
 'owned': 164,
 'public': 158,
 'export_manifest_sha256': '8cf57d1f9533696bc27e348965a6e061571570d1b7b90384f150b4e7a4268cd3',
 'audit_lanes': {'p14/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/audits/9f019ec9766b683a5d4a/lane-0': ['ImbalancedChen.P1OriginalFifthAdoptedOwnerBank'],
                 'p14/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4/audits/7e0eab52d066a9b5937b/lane-0': ['ImbalancedChen.P5OldFifthFiveCoordinateBarycentric'],
                 'p14/owner-b13-typed-bound-retry/bb377de86aa1e92f461c3d01471010cb0791dad5/audits/3ef6ea27499d9564b04c/lane-0': ['ImbalancedChen.P1OriginalFifthActualB13IntegralError'],
                 'p14/typed-range-aggregate/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb/audits/7b4867943eeb44a4de5a/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange'],
                 'p14/typed-range-blocks-111-120/5ba405bc08aaef020868399aa62a429ca4281eda/audits/d063d1b9d7d286fef684/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks111120'],
                 'p14/typed-range-blocks-121-130/5ba405bc08aaef020868399aa62a429ca4281eda/audits/93cf512340f3c46786d3/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks121130'],
                 'p14/typed-range-blocks-131-140/5ba405bc08aaef020868399aa62a429ca4281eda/audits/b6ebbb6e0173d01b0292/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks131140'],
                 'p14/typed-range-blocks-141-142/5ba405bc08aaef020868399aa62a429ca4281eda/audits/7f3fa530fe7b50bd3c41/lane-0': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks141142'],
                 'p14/uniform-adopted-error-add-cast-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/audits/0a339e2c14ff0c7aef58/lane-0': ['ImbalancedChen.P1OriginalFifthUniformAdoptedBankError']},
 'owned_names_by_module': {'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank': ['ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.Point',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedDomain',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedDomain_measurable',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedDomain_subset_fixedParent',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedOwners',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedOwners_firstStop_buffer',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedOwners_firstStop_zero',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedOwners_original_decoded',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedOwners_selected_buffer',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedOwners_selected_zero',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adopted_ownerIntegral_B13',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.decodedLabels',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.fixedParent',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.fixedParent_eq_exact_box',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.fixedParent_measurable',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.fixedParent_subset_positiveCube',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.fixedParent_volume_exact',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedMass',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedMass_eq_parent_sub_baseline',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedMass_le_exact_volumeCost',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedMass_nonneg',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedParent',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedParent_eq_exact_decoded_remainders',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedParent_measurable',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedParents_pairwise_disjoint',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedVolumeCost',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedVolumeCost_nonneg',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.ownerIntegral',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.parentIntegral',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.adoptedDomain.eq_1',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.fixedParent._proof_1',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.fixedParent._proof_2',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedMass.eq_1',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.omittedParent.eq_1',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.ownerIntegral.eq_1',
                                                                              'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank.parentIntegral.eq_1'],
                           'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric': ['ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.Point',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.childVolume',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.corner',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.corner_eq_vertexPoint',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.endpoint',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.factor',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.factor_endpoint_other',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.fraction_endpoint_other',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.integral_fraction_Ico',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.integral_one_sub_fraction_Ico',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.integral_vertexWeight_eq_childVolume_div_32',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.weightedVertexTree_eq_32_words',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.wordWeight',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.wordWeight_eq_vertexWeight',
                                                                                  'ImbalancedChen.P5OldFifthExact64ChildTiling.childBox.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.childVolume.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.corner._proof_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.corner.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.endpoint.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.factor.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.integral_vertexWeight_eq_childVolume_div_32._simp_1_2',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.wordWeight.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateTree.allFiveCoordinates.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateTree.vertexWeight.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateTree.weightedVertexTree.eq_1',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateTree.weightedVertexTree.eq_2',
                                                                                  'ImbalancedChen.P5OldFifthFiveCoordinateTree.weightedVertexTree.eq_def',
                                                                                  'ImbalancedChen.P5OldFifthOneCoordinateVertexChord.coordinateFraction.eq_1',
                                                                                  '_private.ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.0.ImbalancedChen.P5OldFifthFiveCoordinateTree.weightedVertexTree.match_1.eq_1',
                                                                                  '_private.ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.0.ImbalancedChen.P5OldFifthFiveCoordinateTree.weightedVertexTree.match_1.eq_2',
                                                                                  '_private.ImbalancedChen.P5OldFifthFiveCoordinateBarycentric.0.ImbalancedChen.P5OldFifthFiveCoordinateTree.weightedVertexTree.match_1.splitter'],
                           'ImbalancedChen.P1OriginalFifthActualB13IntegralError': ['ImbalancedChen.P1OriginalFifthActualB13IntegralError.Point',
                                                                                    'ImbalancedChen.P1OriginalFifthActualB13IntegralError.actual_ownerUnion_subset_positiveCube',
                                                                                    'ImbalancedChen.P1OriginalFifthActualB13IntegralError.actual_selected_owner_B13',
                                                                                    'ImbalancedChen.P1OriginalFifthActualB13IntegralError.positiveKernel',
                                                                                    'ImbalancedChen.P1OriginalFifthActualB13IntegralError.positiveKernel_integrableOn_of_subset',
                                                                                    'ImbalancedChen.P1OriginalFifthActualB13IntegralError.positiveKernel_integral_motion_le',
                                                                                    'ImbalancedChen.P1OriginalFifthActualB13IntegralError.rawBox_volume',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualB13IntegralError.0.ImbalancedChen.P1OriginalFifthActualB13IntegralError.nonnegative_setIntegral_domain_difference',
                                                                                    'ImbalancedChen.P1OriginalFifthActualB13IntegralError.positiveKernel.eq_1',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualB13IntegralError.0.ImbalancedChen.P1OriginalFifthActualB13IntegralError.nonnegative_setIntegral_domain_difference._simp_1_1',
                                                                                    '_private.ImbalancedChen.P1OriginalFifthActualB13IntegralError.0.ImbalancedChen.P1OriginalFifthActualB13IntegralError.nonnegative_setIntegral_domain_difference._simp_1_2'],
                           'ImbalancedChen.P1HistoricalFifthTypedArchiveRange': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.rows_grid_eq400',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.rows_grid_mask_valid',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.rows_mask_nonnegative',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.rows_signed64_range',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.rows_typed_valid',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.typed_encoded_frame_roundtrip',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.typed_encoded_payload_roundtrip',
                                                                                 'ImbalancedChen.P1HistoricalFifthNpyFrame.rowCount.eq_1',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.rows_typed_valid._simp_1_1',
                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.rows_typed_valid._simp_1_2'],
                           'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks111120': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block111_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block112_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block113_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block114_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block115_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block116_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block117_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block118_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block119_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block120_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block111_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block112_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block113_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block114_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block115_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block116_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block117_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block118_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block119_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block120_typed_valid._proof_1_1'],
                           'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks121130': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block121_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block122_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block123_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block124_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block125_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block126_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block127_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block128_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block129_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block130_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block121_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block122_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block123_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block124_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block125_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block126_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block127_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block128_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block129_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block130_typed_valid._proof_1_1'],
                           'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks131140': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block131_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block132_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block133_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block134_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block135_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block136_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block137_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block138_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block139_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block140_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block131_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block132_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block133_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block134_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block135_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block136_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block137_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block138_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block139_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block140_typed_valid._proof_1_1'],
                           'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks141142': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block141_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block142_typed_valid',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block141_typed_valid._proof_1_1',
                                                                                             'ImbalancedChen.P1HistoricalFifthTypedArchiveRange.block142_typed_valid._proof_1_1'],
                           'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError': ['ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.baselineBankIntegral',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.exists_uniform_adopted_bank_error_parameters',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.parentBankIntegral',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.parentBank_sub_baseline_eq_trimMass',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.retainedBankIntegral',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.retainedBank_parent_error_le',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.retainedBank_sub_baseline_abs_le',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.trimMassBank',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.trimMassBank_le_volumeBank',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.trimMassBank_nonneg',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.trimVolumeBank',
                                                                                     'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError.trimVolumeBank_nonneg']},
 'owned_export_sha256_by_lane': {'p14/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/audits/9f019ec9766b683a5d4a/lane-0': 'e38b1f48cb632650cd1c90f484d7381741ca7639fd757d33c6e1bf4d7b362077',
                                 'p14/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4/audits/7e0eab52d066a9b5937b/lane-0': 'a37bf3b95cbda0cd72873d15157b96fe42ee11c8886bfbc30f246bc7bb4705c3',
                                 'p14/owner-b13-typed-bound-retry/bb377de86aa1e92f461c3d01471010cb0791dad5/audits/3ef6ea27499d9564b04c/lane-0': '1567977f7e69f6c02310797d52034081cf25b672cd5112084867be0f4e2068bc',
                                 'p14/typed-range-aggregate/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb/audits/7b4867943eeb44a4de5a/lane-0': '76c370b165752c12631e7ca44c1762b36f0185a9f169b3dfbbfdbea4ba2fc8d7',
                                 'p14/typed-range-blocks-111-120/5ba405bc08aaef020868399aa62a429ca4281eda/audits/d063d1b9d7d286fef684/lane-0': '7bc8661dd37fdcecdfdcb4b91709133951ef7584bdae124e4655b58117eceb6f',
                                 'p14/typed-range-blocks-121-130/5ba405bc08aaef020868399aa62a429ca4281eda/audits/93cf512340f3c46786d3/lane-0': 'febbec0312f32456589c0f64f6ae2d4f7bca27b2c909645b827000ef99d0694e',
                                 'p14/typed-range-blocks-131-140/5ba405bc08aaef020868399aa62a429ca4281eda/audits/b6ebbb6e0173d01b0292/lane-0': '8548b35e26d24c913c5beeb642471f9ac21161482233097a4de7264db06851a7',
                                 'p14/typed-range-blocks-141-142/5ba405bc08aaef020868399aa62a429ca4281eda/audits/7f3fa530fe7b50bd3c41/lane-0': '19f5573914b4f388020111834d8b1e0a91f7aad5c77f108ed453805743835e5a',
                                 'p14/uniform-adopted-error-add-cast-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/audits/0a339e2c14ff0c7aef58/lane-0': '91183d560964fcc1d04d04f5a0822bf43aef3f87aa5c547501e2b025eb53c706'},
 'groups': {'p14_new': ['P1HistoricalFifthTypedArchiveRange',
                        'P1HistoricalFifthTypedArchiveRangeBlocks111120',
                        'P1HistoricalFifthTypedArchiveRangeBlocks121130',
                        'P1HistoricalFifthTypedArchiveRangeBlocks131140',
                        'P1HistoricalFifthTypedArchiveRangeBlocks141142',
                        'P1OriginalFifthActualB13IntegralError',
                        'P1OriginalFifthAdoptedOwnerBank',
                        'P1OriginalFifthUniformAdoptedBankError',
                        'P5OldFifthFiveCoordinateBarycentric']},
 'shared_runs': [],
 'shared_failures': [],
 'excluded_failed_owners': ['ImbalancedChen.P5OldFifthChildGapIntegral',
                            'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate'],
 'protected_roots': {'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
                     'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
                     'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
                     'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'},
 'roots': {'p14/adopted-owner-bank-label5-retry/bb377de86aa1e92f461c3d01471010cb0791dad5': '20261125-p14-continuation/adopted-owner-bank-label5-retry/bb377de86aa1e92f461c3d01471010cb0791dad5',
           'p14/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27': '20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27',
           'p14/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4': '20261125-p14-continuation/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4',
           'p14/child-gap-expression-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52': '20261125-p14-continuation/child-gap-expression-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
           'p14/child-gap-namespace-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4': '20261125-p14-continuation/child-gap-namespace-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4',
           'p14/owner-b13-typed-bound-retry/bb377de86aa1e92f461c3d01471010cb0791dad5': '20261125-p14-continuation/owner-b13-typed-bound-retry/bb377de86aa1e92f461c3d01471010cb0791dad5',
           'p14/typed-key-uniqueness-kernel-exception-diagnostic/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52': '20261125-p14-continuation/typed-key-uniqueness-kernel-exception-diagnostic/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
           'p14/typed-range-aggregate/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb': '20261125-p14-continuation/typed-range-aggregate/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb',
           'p14/typed-range-blocks-111-120/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-111-120/5ba405bc08aaef020868399aa62a429ca4281eda',
           'p14/typed-range-blocks-121-130/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-121-130/5ba405bc08aaef020868399aa62a429ca4281eda',
           'p14/typed-range-blocks-131-140/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-131-140/5ba405bc08aaef020868399aa62a429ca4281eda',
           'p14/typed-range-blocks-141-142/5ba405bc08aaef020868399aa62a429ca4281eda': '20261125-p14-continuation/typed-range-blocks-141-142/5ba405bc08aaef020868399aa62a429ca4281eda',
           'p14/uniform-adopted-error-add-cast-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52': '20261125-p14-continuation/uniform-adopted-error-add-cast-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52'},
 'single_files': {'p14_pipeline/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb/typed-range-aggregate-after-known-deployment/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb/typed-range-aggregate-after-known-deployment/PIPELINE_RESULT.json',
                  'p14_pipeline/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json',
                  'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json',
                  'p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/CANDIDATE_BINDING.json': '20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/CANDIDATE_BINDING.json',
                  'p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/PIPELINE_RESULT.json',
                  'p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/child-gap-expression-retry.log': '20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/child-gap-expression-retry.log',
                  'p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/typed-key-uniqueness-kernel-exception-diagnostic.log': '20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/typed-key-uniqueness-kernel-exception-diagnostic.log',
                  'p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/uniform-adopted-error-add-cast-retry.log': '20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/uniform-adopted-error-add-cast-retry.log',
                  'p14_pipeline/bb377de86aa1e92f461c3d01471010cb0791dad5/owner-b13-typed-bound-and-consumers/PIPELINE_RESULT.json': '20261125-p14-continuation-bootstrap/bb377de86aa1e92f461c3d01471010cb0791dad5/owner-b13-typed-bound-and-consumers/PIPELINE_RESULT.json'},
 'stage_bindings': {'p14/adopted-owner-bank-label5-retry/bb377de86aa1e92f461c3d01471010cb0791dad5': {'source_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5',
                                                                                                     'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                     'manifest_path': 'docs/p1/20261125/p14-continuation/stages/adopted-owner-bank-label5-retry.json',
                                                                                                     'manifest_sha256': '0c5b89f5d9286c2abc769e090026ebb740950dc375af445f326a03ed79a305f5',
                                                                                                     'targets': {'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank': 'a4323f849758517eb8a82f35f4e35f98cbced5ca08732971712b1689cefcc09b'}},
                    'p14/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27': {'source_commit': '14845975a892974d2633c283f73f03cb87faae27',
                                                                                                          'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                          'manifest_path': 'docs/p1/20261125/p14-continuation/stages/adopted-owner-bank-typed-bound-retry.json',
                                                                                                          'manifest_sha256': 'f1d4ab0f068ecb48e9a834a6f94f1e60786295fdaf08415d2c91a5c95d0f0872',
                                                                                                          'targets': {'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank': '3d326d98699f1d6b99290e20fbd50bdfbd08de0bda20a8a64dd1bab8ff6eec69'}},
                    'p14/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4': {'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/barycentric-id-power-retry.json',
                                                                                                'manifest_sha256': '8afac275362a7d5afdec9413c667993af5bcf00fe3da86ec81edd6076d5626c7',
                                                                                                'targets': {'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric': '3777f1200e46cf909cac65802868b9fbadcbfb00dd70e77428013e83eb7b4728'}},
                    'p14/child-gap-expression-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52': {'source_commit': 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/child-gap-expression-retry.json',
                                                                                                'manifest_sha256': 'e9ffb4e403e81ebe509765409d0abbf712765325c452b559fca981b932881838',
                                                                                                'targets': {'ImbalancedChen.P5OldFifthChildGapIntegral': '8ab2b85ae8dbbdef067ff12e439a24e248bc08efeafabdd7f3df69abf744be69'}},
                    'p14/child-gap-namespace-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4': {'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                                                                                               'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                               'manifest_path': 'docs/p1/20261125/p14-continuation/stages/child-gap-namespace-retry.json',
                                                                                               'manifest_sha256': '204e2296e79d3636c413502536f6c345bfd42a647896939e83931c88891af394',
                                                                                               'targets': {'ImbalancedChen.P5OldFifthChildGapIntegral': '709220f1d167d2abb8962e18c9a101206099ae73e77cea5749273fa3852995b8'}},
                    'p14/owner-b13-typed-bound-retry/bb377de86aa1e92f461c3d01471010cb0791dad5': {'source_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5',
                                                                                                 'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                 'manifest_path': 'docs/p1/20261125/p14-continuation/stages/owner-b13-typed-bound-retry.json',
                                                                                                 'manifest_sha256': '34713e5c2c067738e767edf7ca319ecd00eb421eb88c5718dd4d213c85be1d77',
                                                                                                 'targets': {'ImbalancedChen.P1OriginalFifthActualB13IntegralError': '92ef1e56b5f7fdbba1c669fb2e520ff6a0656e3e0e160e6a653d1d806b2ff8a5'}},
                    'p14/typed-key-uniqueness-kernel-exception-diagnostic/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52': {'source_commit': 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
                                                                                                                      'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                                      'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-key-uniqueness-kernel-exception-diagnostic.json',
                                                                                                                      'manifest_sha256': 'c428e0a1e0ca261489d3d60e1f4e455e0c38fa46b400b31e334a7f37a2cc1ef7',
                                                                                                                      'targets': {'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate': '7b1a664fca62612a8f2d198a15e512420bb853a2d155eddf7950cec05660973b'}},
                    'p14/typed-range-aggregate/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb': {'source_commit': '0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb',
                                                                                           'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                           'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-range-aggregate.json',
                                                                                           'manifest_sha256': '786faf4626265a977d9ca25920e30cc62a0007365967d7b8bc0b613b74c36a0f',
                                                                                           'targets': {'ImbalancedChen.P1HistoricalFifthTypedArchiveRange': '609ba2dce8e12ef50a7cb086e2eed3056dbfa6ace237757131bd9d2ed220151e'}},
                    'p14/typed-range-blocks-111-120/5ba405bc08aaef020868399aa62a429ca4281eda': {'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-range-blocks-111-120.json',
                                                                                                'manifest_sha256': 'b3318a0fe7a3d41a825480a10217e768c031bb3a868ff0e3ed1e30d19e1795fd',
                                                                                                'targets': {'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks111120': '0a0e63134ca9fc9b26da9e1f08f0db088dcdb1b26d1c00c15966d95b7aadf127'}},
                    'p14/typed-range-blocks-121-130/5ba405bc08aaef020868399aa62a429ca4281eda': {'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-range-blocks-121-130.json',
                                                                                                'manifest_sha256': '15e5684b4a57bd4a9ec474654e33e7f851b75437185178763462553ff70c58a1',
                                                                                                'targets': {'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks121130': '44b2976f29955675e8bbd79c6b463018dce026e34d2b32a82dabc11d5136b015'}},
                    'p14/typed-range-blocks-131-140/5ba405bc08aaef020868399aa62a429ca4281eda': {'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-range-blocks-131-140.json',
                                                                                                'manifest_sha256': '265a6b95036f3fe191da2c5cf5fb5621653c30f38a99a9ba05abc1a0bff2fc42',
                                                                                                'targets': {'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks131140': '78d23dac94213c0392b91b2472c0ae368ef2b3cb40e91cd9885e372db06c8a88'}},
                    'p14/typed-range-blocks-141-142/5ba405bc08aaef020868399aa62a429ca4281eda': {'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                'manifest_path': 'docs/p1/20261125/p14-continuation/stages/typed-range-blocks-141-142.json',
                                                                                                'manifest_sha256': 'fc452c9cf215485feca7d1fc3eb6463eda12a5332d96a86ab8de395eab796862',
                                                                                                'targets': {'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks141142': 'c9e54e28e7511fe6013c32dbb6ac2d25aa4d47fd684c3c5cc56885b65886efca'}},
                    'p14/uniform-adopted-error-add-cast-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52': {'source_commit': 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
                                                                                                          'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                                                                                                          'manifest_path': 'docs/p1/20261125/p14-continuation/stages/uniform-adopted-error-add-cast-retry.json',
                                                                                                          'manifest_sha256': '1a9245dcc1ca6955e40b02f3f6592f9b65e213866d74a50a70e42a6f7d554dcc',
                                                                                                          'targets': {'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError': '1c194e52f20b7d5ab65038c8b467b57a38e29d3d36e033775a0b5aaca882b8f0'}}},
 'reuse_locations': {'/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-091-110/PIPELINE_RESULT.json': {'checkpoint': '12',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-091-110/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': '1731ce3651588d9e89b06f0c68c6909bc9f6967df8f3887e81f423f4d1dd0e9e',
                                                                                                                                                                             'bytes': 1742,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks091100',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks101110']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json': {'checkpoint': '06',
                                                                                                                                                        'path': 'p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': 'c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                                                                                                                                                        'sha256': '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01',
                                                                                                                                                        'bytes': 1627,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1FifthCheckedUnitBoxWholeGain',
                                                                                                                                                                            'ImbalancedChen.P1FifthMask5RawOwnerLicence',
                                                                                                                                                                            'ImbalancedChen.P1FifthMask6RawOwnerLicence',
                                                                                                                                                                            'ImbalancedChen.P1FifthPositivePartActualOwner',
                                                                                                                                                                            'ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json': {'checkpoint': '06',
                                                                                                                                                        'path': 'p14_pipeline/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': 'a700772dbddaa09df497590c7d1b54d6e488f812',
                                                                                                                                                        'sha256': 'f999d0bd6b1b7ba4c4a8eb7712ccbb0f3ca44891430c7a4fcfc100bcb91ecd09',
                                                                                                                                                        'bytes': 3538,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthActualOwnerCrossingVolume']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                        'path': 'p14_pipeline/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': '93501ca11da26d233922739b6aece9987a877d93',
                                                                                                                                                        'sha256': '3fa68feb2f6070286165883499f7ac9150f150f08b01644712c3f3694df2ee2c',
                                                                                                                                                        'bytes': 4736,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthMovingMeshFiberBands',
                                                                                                                                                                            'ImbalancedChen.P5OldFifthExact64ChildTiling']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                        'path': 'p14_pipeline/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': '89db42762b5f303602608587b3d610cd7ebe9a54',
                                                                                                                                                        'sha256': '6b57261b2316f51a376174d747b9b92b0cf172ce30e5deb1eb0673cd5a1301e9',
                                                                                                                                                        'bytes': 3909,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json': {'checkpoint': '12',
                                                                                                                                                        'path': 'p14_pipeline/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': '957c7c773bef05a6271fb504c06d967d67ce2908',
                                                                                                                                                        'sha256': '1b087a482fbf661d2b1b2a2ddc02d0cbc0b73547249ebc25e005dc1b554c8911',
                                                                                                                                                        'bytes': 4163,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1OriginalFifthActualCrossingSections']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json': {'checkpoint': '05',
                                                                                                                                                        'path': 'p14_pipeline/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': '8237d0b698ca01153a7e2823510cf67148083c0a',
                                                                                                                                                        'sha256': '6629d933bdd7f5baa5d94bab5ba0a46f76c30fb316215be01b149669a957b264',
                                                                                                                                                        'bytes': 3469,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1FifthUnitBoxLiteralGainLower',
                                                                                                                                                                            'ImbalancedChen.P1OriginalFifthLiteralKernelModulus',
                                                                                                                                                                            'ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                        'path': 'p14_pipeline/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                                                                                                                                                        'sha256': '4f38ec268ec5c0baff349e612e4a4c93ca0ee024a8699222622ef2ee2db60c38',
                                                                                                                                                        'bytes': 4345,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P5OldFifthFrozenGapConcavity']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                         'path': 'p14_pipeline/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
                                                                                                                                                                         'reference_kind': 'pipeline',
                                                                                                                                                                         'source_commit': '8eabdf5c9563ae73eb091242f376a5b28456f97f',
                                                                                                                                                                         'sha256': '0ea4e2ae9dcbd2aad8468846b5c65aa3a0439ac784397b239b9b0339a47d1895',
                                                                                                                                                                         'bytes': 7441,
                                                                                                                                                                         'accepted_owners': ['ImbalancedChen.P1FifthMask5NamedParent1Owner',
                                                                                                                                                                                             'ImbalancedChen.P1FifthMask6NamedParent0Owner',
                                                                                                                                                                                             'ImbalancedChen.P5OldFifthFiveCoordinateTree',
                                                                                                                                                                                             'ImbalancedChen.P5OldFifthOneCoordinateVertexChord']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json': {'checkpoint': '10',
                                                                                                                                                                       'path': 'p14_pipeline/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json',
                                                                                                                                                                       'reference_kind': 'pipeline',
                                                                                                                                                                       'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                                                                                                                                                                       'sha256': '9445e6f4d9ad887cff065c3e501d7e60ec1984261b001029353619e252d9dc3e',
                                                                                                                                                                       'bytes': 1535,
                                                                                                                                                                       'accepted_owners': ['ImbalancedChen.P1FifthNamedParentsConcreteJ5']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json': {'checkpoint': '12',
                                                                                                                                                                               'path': 'p14_pipeline/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json',
                                                                                                                                                                               'reference_kind': 'pipeline',
                                                                                                                                                                               'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                                                                                                                                                                               'sha256': '751a4fef4a9774c45dad46e5d10afc81a135571262d83d9c50ac5bf76ce4bda8',
                                                                                                                                                                               'bytes': 7137,
                                                                                                                                                                               'accepted_owners': ['ImbalancedChen.P1FifthNamedParentActualIntegral']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/61566a18871e26b80cced0a4408944294d793071/PIPELINE_RESULT.json': {'checkpoint': '05',
                                                                                                                                                        'path': 'p14_pipeline/61566a18871e26b80cced0a4408944294d793071/PIPELINE_RESULT.json',
                                                                                                                                                        'reference_kind': 'pipeline',
                                                                                                                                                        'source_commit': '61566a18871e26b80cced0a4408944294d793071',
                                                                                                                                                        'sha256': '2b3d386c386364a5f3e80789e75b8955dbd79a58c2e9d19363debef5b21917be',
                                                                                                                                                        'bytes': 1041,
                                                                                                                                                        'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlock000',
                                                                                                                                                                            'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeCore']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-001-010/PIPELINE_RESULT.json': {'checkpoint': '07',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-001-010/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': '3c1c3547dbd97f7eeda2da4ef18456a67ee551e90bd9217ff03831253bd88b94',
                                                                                                                                                                             'bytes': 764,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks001010']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-011-030/PIPELINE_RESULT.json': {'checkpoint': '08',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-011-030/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': 'ca3b1bef32e657788b14f7dca698e6c41761905b487378ef73279fac512883b0',
                                                                                                                                                                             'bytes': 1232,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks011020',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks021030']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-031-050/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-031-050/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': '8f800b610665799be5ed6342fa3a17b6529d7c8a1581092bc83fe088f3259de2',
                                                                                                                                                                             'bytes': 1742,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks031040',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks041050']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-051-070/PIPELINE_RESULT.json': {'checkpoint': '09',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-051-070/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': '661800b533cd754036dab20200997d01f1d6c243c48e489471bee506ecfe8d05',
                                                                                                                                                                             'bytes': 1742,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks051060',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks061070']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json': {'checkpoint': '11',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': 'f9b8e340021dd52e1553867b55f7b2a29303530c1d54bcef545d6b705c78e2ee',
                                                                                                                                                                             'bytes': 1742,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks071080',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks081090']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json': {'checkpoint': '13',
                                                                                                                                                                             'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                                                                                                                                                                             'sha256': 'a2a14a8e959ac992925b5b06a91bd21a9fee44ba172499dd455816902e7965bd',
                                                                                                                                                                             'bytes': 2678,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks111120',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks121130',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks131140',
                                                                                                                                                                                                 'ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks141142']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4/runs/attempt-00000/RESULT.json': {'checkpoint': '13',
                                                                                                                                                                                   'path': 'p14/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4/runs/attempt-00000/RESULT.json',
                                                                                                                                                                                   'reference_kind': 'stage_result',
                                                                                                                                                                                   'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                                                                                                                                                                                   'sha256': '1bd8ef938e3fec3ff550a6d79828923699db05d9c026284749d797c4d9cd42e7',
                                                                                                                                                                                   'bytes': 1050,
                                                                                                                                                                                   'accepted_owners': ['ImbalancedChen.P5OldFifthFiveCoordinateBarycentric']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json': {'checkpoint': '13',
                                                                                                                                                                                           'path': 'p14_pipeline/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json',
                                                                                                                                                                                           'reference_kind': 'pipeline',
                                                                                                                                                                                           'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                                                                                                                                                                                           'sha256': 'a9e670f74bee98fd8a65ba3ea6de824a804fbcb1b5cffe8782a88463b755be61',
                                                                                                                                                                                           'bytes': 7339,
                                                                                                                                                                                           'accepted_owners': ['ImbalancedChen.P5OldFifthFiveCoordinateBarycentric']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/runs/attempt-00000/RESULT.json': {'checkpoint': '13',
                                                                                                                                                                                             'path': 'p14/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/runs/attempt-00000/RESULT.json',
                                                                                                                                                                                             'reference_kind': 'stage_result',
                                                                                                                                                                                             'source_commit': '14845975a892974d2633c283f73f03cb87faae27',
                                                                                                                                                                                             'sha256': '1092a877b78475b016368ae49f314938092b38d32eb94d8d5e34b8841c4493f8',
                                                                                                                                                                                             'bytes': 1048,
                                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1OriginalFifthAdoptedOwnerBank']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation/typed-key-uniqueness-core/504f9546a9d919ed1977c396517d5838ffd0284c/runs/attempt-00000/RESULT.json': {'checkpoint': '10',
                                                                                                                                                                                  'path': 'p14/typed-key-uniqueness-core/504f9546a9d919ed1977c396517d5838ffd0284c/runs/attempt-00000/RESULT.json',
                                                                                                                                                                                  'reference_kind': 'stage_result',
                                                                                                                                                                                  'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c',
                                                                                                                                                                                  'sha256': 'ea85ed439655b1a7ad20f4932831abe4c5a71ed2ce81f0a3f92f8cdc2b424388',
                                                                                                                                                                                  'bytes': 1061,
                                                                                                                                                                                  'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore']},
                     '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json': {'checkpoint': '10',
                                                                                                                                                                             'path': 'p14_pipeline/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json',
                                                                                                                                                                             'reference_kind': 'pipeline',
                                                                                                                                                                             'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c',
                                                                                                                                                                             'sha256': '6a7f93437ebe3d802360af8993fd513b5e9a8c028e63d9d854b83247e57d758f',
                                                                                                                                                                             'bytes': 996,
                                                                                                                                                                             'accepted_owners': ['ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore']}},
 'pipelines': [{'path': 'p14_pipeline/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb/typed-range-aggregate-after-known-deployment/PIPELINE_RESULT.json',
                'sha256': 'f79badbbb227f40945c63802eee949e31b54b1fe4c5c1906c62c750a890cc2f9',
                'source_commit': '0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['typed-range-aggregate'],
                'held_stages': [],
                'reuse_field': 'reused_pipelines',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/61566a18871e26b80cced0a4408944294d793071/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-001-010/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-011-030/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-031-050/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-051-070/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-071-090/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-091-110/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json']},
               {'path': 'p14_pipeline/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json',
                'sha256': 'a9e670f74bee98fd8a65ba3ea6de824a804fbcb1b5cffe8782a88463b755be61',
                'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['barycentric-id-power-retry', 'child-gap-namespace-retry'],
                'held_stages': ['pointwise-q-namespace-retry',
                                'named-payload-semantics',
                                'named-all-children',
                                'named-child-specific-ratio',
                                'sharp-directed-log',
                                'first-f-concavity-namespace-retry',
                                'child-q-jensen-namespace-retry',
                                'actual-child-jensen-integral',
                                'selected-owner-jensen-reserve',
                                'named-all-children-selected-jensen',
                                'named-q80-floor-soundness',
                                'original-child-integer-wire'],
                'reuse_field': 'reused_pipelines',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json']},
               {'path': 'p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json',
                'sha256': 'a2a14a8e959ac992925b5b06a91bd21a9fee44ba172499dd455816902e7965bd',
                'source_commit': '5ba405bc08aaef020868399aa62a429ca4281eda',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['typed-range-blocks-111-120',
                                     'typed-range-blocks-121-130',
                                     'typed-range-blocks-131-140',
                                     'typed-range-blocks-141-142'],
                'held_stages': [],
                'reuse_field': 'reused_pipeline',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-091-110/PIPELINE_RESULT.json']},
               {'path': 'p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/PIPELINE_RESULT.json',
                'sha256': '7b17f1dce749eb319b1411dd075212ce5945b1042713b9d7f004eed15e43d6bf',
                'source_commit': 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['child-gap-expression-retry',
                                     'uniform-adopted-error-add-cast-retry',
                                     'typed-key-uniqueness-kernel-exception-diagnostic'],
                'held_stages': [],
                'reuse_field': 'reused_original_stage_results',
                'reused_original_stage_results': [{'pipeline_path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json',
                                                   'pipeline_raw_bytes': 7339,
                                                   'pipeline_raw_sha256': 'a9e670f74bee98fd8a65ba3ea6de824a804fbcb1b5cffe8782a88463b755be61',
                                                   'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4/runs/attempt-00000/RESULT.json',
                                                   'result_raw_bytes': 1050,
                                                   'result_raw_sha256': '1bd8ef938e3fec3ff550a6d79828923699db05d9c026284749d797c4d9cd42e7',
                                                   'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                                                   'source_sha256': '3777f1200e46cf909cac65802868b9fbadcbfb00dd70e77428013e83eb7b4728',
                                                   'stage': 'barycentric-id-power-retry',
                                                   'target_module': 'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric'},
                                                  {'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/runs/attempt-00000/RESULT.json',
                                                   'result_raw_bytes': 1048,
                                                   'result_raw_sha256': '1092a877b78475b016368ae49f314938092b38d32eb94d8d5e34b8841c4493f8',
                                                   'source_commit': '14845975a892974d2633c283f73f03cb87faae27',
                                                   'source_sha256': '3d326d98699f1d6b99290e20fbd50bdfbd08de0bda20a8a64dd1bab8ff6eec69',
                                                   'stage': 'adopted-owner-bank-typed-bound-retry',
                                                   'target_module': 'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank'},
                                                  {'pipeline_path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json',
                                                   'pipeline_raw_bytes': 996,
                                                   'pipeline_raw_sha256': '6a7f93437ebe3d802360af8993fd513b5e9a8c028e63d9d854b83247e57d758f',
                                                   'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/typed-key-uniqueness-core/504f9546a9d919ed1977c396517d5838ffd0284c/runs/attempt-00000/RESULT.json',
                                                   'result_raw_bytes': 1061,
                                                   'result_raw_sha256': 'ea85ed439655b1a7ad20f4932831abe4c5a71ed2ce81f0a3f92f8cdc2b424388',
                                                   'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c',
                                                   'source_sha256': 'f475f4f9f11b339883b2ee6e09db226cb437803df1f574fdb0717f702a7809ac',
                                                   'stage': 'typed-key-uniqueness-core',
                                                   'target_module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore'}],
                'candidate_binding_path': 'p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/CANDIDATE_BINDING.json',
                'candidate_binding_sha256': '7047ce6b689a5f58876e96e4732a0aadcc2cdcb74dc9e53455c69ce9eff000ba',
                'candidate_specs': [{'manifest': 'docs/p1/20261125/p14-continuation/stages/child-gap-expression-retry.json',
                                     'manifest_sha256': 'e9ffb4e403e81ebe509765409d0abbf712765325c452b559fca981b932881838',
                                     'prerequisite': {'pipeline_path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json',
                                                      'pipeline_raw_bytes': 7339,
                                                      'pipeline_raw_sha256': 'a9e670f74bee98fd8a65ba3ea6de824a804fbcb1b5cffe8782a88463b755be61',
                                                      'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4/runs/attempt-00000/RESULT.json',
                                                      'result_raw_bytes': 1050,
                                                      'result_raw_sha256': '1bd8ef938e3fec3ff550a6d79828923699db05d9c026284749d797c4d9cd42e7',
                                                      'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                                                      'source_sha256': '3777f1200e46cf909cac65802868b9fbadcbfb00dd70e77428013e83eb7b4728',
                                                      'stage': 'barycentric-id-power-retry',
                                                      'target_module': 'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric'},
                                     'stage': 'child-gap-expression-retry',
                                     'target': {'after_sha256': '8ab2b85ae8dbbdef067ff12e439a24e248bc08efeafabdd7f3df69abf744be69',
                                                'before_sha256': '709220f1d167d2abb8962e18c9a101206099ae73e77cea5749273fa3852995b8',
                                                'module': 'ImbalancedChen.P5OldFifthChildGapIntegral',
                                                'path': 'ImbalancedChen/P5OldFifthChildGapIntegral.lean',
                                                'preimage_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4'}},
                                    {'manifest': 'docs/p1/20261125/p14-continuation/stages/uniform-adopted-error-add-cast-retry.json',
                                     'manifest_sha256': '1a9245dcc1ca6955e40b02f3f6592f9b65e213866d74a50a70e42a6f7d554dcc',
                                     'prerequisite': {'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/runs/attempt-00000/RESULT.json',
                                                      'result_raw_bytes': 1048,
                                                      'result_raw_sha256': '1092a877b78475b016368ae49f314938092b38d32eb94d8d5e34b8841c4493f8',
                                                      'source_commit': '14845975a892974d2633c283f73f03cb87faae27',
                                                      'source_sha256': '3d326d98699f1d6b99290e20fbd50bdfbd08de0bda20a8a64dd1bab8ff6eec69',
                                                      'stage': 'adopted-owner-bank-typed-bound-retry',
                                                      'target_module': 'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank'},
                                     'stage': 'uniform-adopted-error-add-cast-retry',
                                     'target': {'after_sha256': '1c194e52f20b7d5ab65038c8b467b57a38e29d3d36e033775a0b5aaca882b8f0',
                                                'before_sha256': '5c0012206c93e05871ead313c5e410217e751073f81e76b3abf6c2806c59973d',
                                                'module': 'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError',
                                                'path': 'ImbalancedChen/P1OriginalFifthUniformAdoptedBankError.lean',
                                                'preimage_commit': '14845975a892974d2633c283f73f03cb87faae27'}},
                                    {'manifest': 'docs/p1/20261125/p14-continuation/stages/typed-key-uniqueness-kernel-exception-diagnostic.json',
                                     'manifest_sha256': 'c428e0a1e0ca261489d3d60e1f4e455e0c38fa46b400b31e334a7f37a2cc1ef7',
                                     'prerequisite': {'pipeline_path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json',
                                                      'pipeline_raw_bytes': 996,
                                                      'pipeline_raw_sha256': '6a7f93437ebe3d802360af8993fd513b5e9a8c028e63d9d854b83247e57d758f',
                                                      'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/typed-key-uniqueness-core/504f9546a9d919ed1977c396517d5838ffd0284c/runs/attempt-00000/RESULT.json',
                                                      'result_raw_bytes': 1061,
                                                      'result_raw_sha256': 'ea85ed439655b1a7ad20f4932831abe4c5a71ed2ce81f0a3f92f8cdc2b424388',
                                                      'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c',
                                                      'source_sha256': 'f475f4f9f11b339883b2ee6e09db226cb437803df1f574fdb0717f702a7809ac',
                                                      'stage': 'typed-key-uniqueness-core',
                                                      'target_module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore'},
                                     'stage': 'typed-key-uniqueness-kernel-exception-diagnostic',
                                     'target': {'after_sha256': '7b1a664fca62612a8f2d198a15e512420bb853a2d155eddf7950cec05660973b',
                                                'before_sha256': '8204516c6c83ad76e08faf0e9a2ab5a7519075ca96473f94da664dbe47ea157d',
                                                'module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate',
                                                'path': 'ImbalancedChen/P1HistoricalFifthTypedKeyUniquenessCertificate.lean',
                                                'preimage_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5'}}]},
               {'path': 'p14_pipeline/bb377de86aa1e92f461c3d01471010cb0791dad5/owner-b13-typed-bound-and-consumers/PIPELINE_RESULT.json',
                'sha256': '25e90db2819b581adc5bd682d47270956cfb8dad648ee0d4d4d657aa1183e4d2',
                'source_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5',
                'driver_sha256': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
                'completed_stages': ['owner-b13-typed-bound-retry', 'adopted-owner-bank-label5-retry'],
                'held_stages': ['uniform-adopted-error',
                                'indexed-owner-archive-label5-retry',
                                'indexed-bank-error',
                                'buffer-owner-geometry-label5-retry',
                                'common-policy-inputs'],
                'reuse_field': 'reused_pipelines',
                'reused_paths': ['/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/89db42762b5f303602608587b3d610cd7ebe9a54/PIPELINE_RESULT.json',
                                 '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json']}],
 'standalone_accepted_stage': {'source_commit': '14845975a892974d2633c283f73f03cb87faae27',
                               'stage': 'adopted-owner-bank-typed-bound-retry',
                               'original_task_id': 'job_b43f2ea79d2245a8bb4319398472df53',
                               'archive_member': 'p14/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/runs/attempt-00000/RESULT.json',
                               'original_path': '/workspace/p1-complete-proof/20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/runs/attempt-00000/RESULT.json',
                               'original_file_sha256': '1092a877b78475b016368ae49f314938092b38d32eb94d8d5e34b8841c4493f8',
                               'original_file_bytes': 1048,
                               'reported_accepted_owners': ['ImbalancedChen.P1OriginalFifthAdoptedOwnerBank'],
                               'original_task_final_pipeline_exists': False,
                               'missing_final_pipeline_synthesized': False,
                               'scope': 'Only this independently completed accepted stage root, including '
                                        'its original normal/kernel/all-owned receipts. Other stages from '
                                        'the interrupted source148 task are outside this minimal fixed '
                                        'scope.',
                               'excluded_missing_final_pipeline': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/14845975a892974d2633c283f73f03cb87faae27/adopted-indexed-typed-bound-and-consumers/PIPELINE_RESULT.json'},
 'failed_attempts': [{'source_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5',
                      'stage': 'adopted-owner-bank-label5-retry',
                      'module': 'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank',
                      'source_sha256': 'a4323f849758517eb8a82f35f4e35f98cbced5ca08732971712b1689cefcc09b',
                      'project_error_count': 1,
                      'reported_error_sections': 1,
                      'normal_log_sha256': 'e9dd6d26199495c9f621a7ada9d5b7f7ba99be07fab26c7a93184937e81571b3'},
                     {'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                      'stage': 'child-gap-namespace-retry',
                      'module': 'ImbalancedChen.P5OldFifthChildGapIntegral',
                      'source_sha256': '709220f1d167d2abb8962e18c9a101206099ae73e77cea5749273fa3852995b8',
                      'project_error_count': 9,
                      'reported_error_sections': 9,
                      'normal_log_sha256': 'a81f05f15ff854af923b762f29b0dac748c6ba28d78fc91354b55fd2d6ea8152'},
                     {'source_commit': 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
                      'stage': 'child-gap-expression-retry',
                      'module': 'ImbalancedChen.P5OldFifthChildGapIntegral',
                      'source_sha256': '8ab2b85ae8dbbdef067ff12e439a24e248bc08efeafabdd7f3df69abf744be69',
                      'project_error_count': 2,
                      'reported_error_sections': 2,
                      'normal_log_sha256': 'dbc53ed0a7c0d110c8eec7388a210eda77f15515d4d27f36bed6eeb4417c558b'},
                     {'source_commit': 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52',
                      'stage': 'typed-key-uniqueness-kernel-exception-diagnostic',
                      'module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate',
                      'source_sha256': '7b1a664fca62612a8f2d198a15e512420bb853a2d155eddf7950cec05660973b',
                      'project_error_count': 1,
                      'reported_error_sections': 1,
                      'normal_log_sha256': '45318627bc4cd41a12cd3fc426fbb11cdde2a29d23d8e7e9925bf3eae9243b79'}],
 'failed_then_accepted': {'module': 'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank',
                          'failed_stage': 'adopted-owner-bank-label5-retry',
                          'failed_source_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5',
                          'accepted_stage': 'adopted-owner-bank-typed-bound-retry',
                          'accepted_source_commit': '14845975a892974d2633c283f73f03cb87faae27',
                          'accepted_source_sha256': '3d326d98699f1d6b99290e20fbd50bdfbd08de0bda20a8a64dd1bab8ff6eec69'}}

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


def checkpoint12_scope(files, manifest, originals, repo, expected, git_pairs):
    """Join the fixed original receipts; never turn reuse, failures or held stages into acceptance."""
    config = CHECKPOINTS['12']
    get = lambda p: json.loads(files[p])
    need(len(git_pairs) == 8 and manifest['roots'] == config['roots'] and
         manifest['single_files'] == config['single_files'] and not manifest['omitted_nonreceipt_files'] and
         sha(files['EXPORT_MANIFEST.json']) == config['export_manifest_sha256'],
         'checkpoint12 exact manifest/root/pipeline/Git scope differs')
    need(set(config['stage_bindings']) == set(config['roots']), 'checkpoint12 stage binding scope differs')
    for root, pinned in config['stage_bindings'].items():
        binding = get(root + '/BINDING.json')
        need({k: binding[k] for k in pinned} == pinned and binding['whole_P1_4_complete'] is False and
             binding['protected_roots'] == config['protected_roots'] and
             sha(files[root + '/executed-driver.py']) == pinned['driver_sha256'] and
             sha((repo / pinned['manifest_path']).read_bytes()) == pinned['manifest_sha256'],
             'checkpoint12 original stage/source/driver/manifest binding differs')

    reference_data, reference_rows = {}, {}
    prior_checkpoints = ['05', '06', '08', '09', '10', '11']
    for prior_checkpoint in prior_checkpoints:
        prior_config = CHECKPOINTS[prior_checkpoint]
        prior_archive = repo / ('docs/p1/20261125/p14-continuation/evidence/checkpoint-' +
                                prior_checkpoint + '.tar.xz')
        prior_raw = prior_archive.read_bytes()
        need(len(prior_raw) == prior_config['bytes'] and sha(prior_raw) == prior_config['sha256'],
             'checkpoint12 prior archive binding differs')
        with tarfile.open(fileobj=io.BytesIO(prior_raw), mode='r:xz') as prior_tar:
            prior_manifest = json.load(prior_tar.extractfile('EXPORT_MANIFEST.json'))
            need(prior_manifest['checkpoint'] == prior_checkpoint, 'checkpoint12 prior manifest differs')
            prior_rows = {r['path']: r for r in prior_manifest['files']}
            for original_path, spec in config['reuse_locations'].items():
                if spec['checkpoint'] == prior_checkpoint:
                    reference_data[original_path] = prior_tar.extractfile(spec['path']).read()
                    reference_rows[original_path] = prior_rows[spec['path']]
    current_rows = {r['path']: r for r in manifest['files']}
    for original_path, spec in config['reuse_locations'].items():
        if spec['checkpoint'] == '12':
            need(originals[original_path] == spec['path'], 'checkpoint12 same-checkpoint original path differs')
            reference_data[original_path], reference_rows[original_path] = files[spec['path']], current_rows[spec['path']]
    need(set(reference_data) == set(config['reuse_locations']), 'checkpoint12 missing reference archive')
    reference_reports, reuse_consumers, used_references, held_history = {}, [], set(), []
    reference_count, same_checkpoint_count = 0, 0
    for spec in config['pipelines']:
        pipeline = get(spec['path'])
        need(sha(files[spec['path']]) == spec['sha256'], 'checkpoint12 original pipeline hash differs')
        if spec['reuse_field'] == 'reused_pipeline':
            need('reused_pipeline' in pipeline and 'reused_pipelines' not in pipeline,
                 'checkpoint12 singleton reuse schema differs')
            references = [pipeline['reused_pipeline']]
        else:
            need(spec['reuse_field'] == 'reused_pipelines' and 'reused_pipelines' in pipeline and
                 'reused_pipeline' not in pipeline, 'checkpoint12 plural reuse schema differs')
            references = pipeline['reused_pipelines']
        need([r['path'] for r in references] == spec['reused_paths'] and
             len(spec['reused_paths']) == len(set(spec['reused_paths'])),
             'checkpoint12 exact reused path list differs')
        reused = set()
        for reference in references:
            original_path = reference['path']
            location_spec = config['reuse_locations'][original_path]
            data, row = reference_data[original_path], reference_rows[original_path]
            original = json.loads(data)
            need(set(reference) == {'path', 'sha256', 'source_commit', 'accepted_owners'} and
                 reference['source_commit'] == original['source_commit'] == location_spec['source_commit'] and
                 reference['path'] == row['original_path'] == original_path and len(data) == row['bytes'] and
                 reference['sha256'] == row['sha256'] == sha(data) == location_spec['sha256'] and
                 original['driver_sha256'] == spec['driver_sha256'] and
                 original['whole_P1_4_complete'] is False, 'checkpoint12 reused path/source/hash binding')
            owners = reference['accepted_owners']
            reference_expected = {'ImbalancedChen.' + m for modules in
                CHECKPOINTS[location_spec['checkpoint']]['groups'].values() for m in modules}
            need(owners == original['accepted_owners'] == location_spec['accepted_owners'] and
                 len(owners) == len(set(owners)) and reused.isdisjoint(owners) and
                 set(owners) <= reference_expected and set(owners).isdisjoint(pipeline['accepted_owners']),
                 'checkpoint12 reused owners differ or counted again')
            if location_spec['checkpoint'] == '12':
                need(spec['source_commit'] == '295f055328ea89ad465b7c2d33d7a171dbcd78f8' and
                     location_spec['source_commit'] == '957c7c773bef05a6271fb504c06d967d67ce2908' and
                     owners == ['ImbalancedChen.P1OriginalFifthActualCrossingSections'] and
                     not pipeline['accepted_owners'], 'checkpoint12 unexpected same-checkpoint acceptance')
                same_checkpoint_count += 1
            else:
                need(set(owners).isdisjoint(expected), 'checkpoint12 prior owner counted as new')
            reference_count += 1
            reused.update(owners)
            used_references.add(original_path)
            reference_reports[original_path] = {'checkpoint': location_spec['checkpoint'],
                'path': location_spec['path'], 'source_commit': location_spec['source_commit'],
                'sha256': location_spec['sha256'], 'accepted_owners': owners,
                'same_checkpoint_reference': location_spec['checkpoint'] == '12'}
        available = set(reused)
        for stage in pipeline['stages']:
            if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                need(not set(stage['requires']) <= available and 'result_path' not in stage and
                     not stage.get('accepted_owners'), 'checkpoint12 held stage ignores available reuse')
                held_history.append({'pipeline_path': spec['path'], 'source_commit': spec['source_commit'],
                    'stage': stage['stage'], 'status': stage['status'], 'requires': stage['requires'],
                    'counts_as_acceptance': False})
            else:
                available.update(stage['accepted_owners'])
        need(available == reused | set(pipeline['accepted_owners']), 'checkpoint12 available owner union differs')
        if 'planned_stages' in pipeline:
            need(pipeline['planned_stages'] == spec['completed_stages'] and
                 pipeline['stop_after_first_failed_group'] is True and not spec['held_stages'],
                 'checkpoint12 completed Range091110 batch differs')
        if 'typed-key-uniqueness-syntax-retry' in spec['path']:
            need(pipeline['complete_actual_sorted_witness_required'] is True,
                 'checkpoint12 key core does not discharge complete sorted witness')
        if spec['source_commit'] == '295f055328ea89ad465b7c2d33d7a171dbcd78f8':
            need(pipeline['accepted_crossing_reused_without_recompilation'] is True and
                 pipeline['held_label5_repairs_are_static_not_prior_normal_failures'] is True,
                 'checkpoint12 source295 reuse/held classification differs')
        reuse_consumers.append({'path': spec['path'], 'source_commit': spec['source_commit'],
            'reused_pipeline_paths': spec['reused_paths'], 'reused_owners': sorted(reused),
            'held_stages_checked_with_reused_owners_available': True,
            'additional_accepted_owners': 0, 'additional_owned_declarations': 0})
    need(used_references == set(config['reuse_locations']) and len(used_references) == 11 and
         reference_count == 17 and same_checkpoint_count == 1 and len(held_history) == 25,
         'checkpoint12 fixed reference/held counts differ')
    reuse_report = {'prior_archive_sha256': {c: CHECKPOINTS[c]['sha256'] for c in prior_checkpoints},
        'references': reference_reports, 'consumers': reuse_consumers, 'reference_count': reference_count,
        'distinct_reference_count': len(used_references), 'same_checkpoint_reference_count': same_checkpoint_count,
        'identity_key': ['original_pipeline_path', 'source_commit', 'sha256'],
        'source_commit_alone_is_not_a_reference_key': True, 'source_hash_owner_binding_verified': True,
        'additional_accepted_owners': 0, 'additional_owned_declarations': 0}

    need(len(config['failed_attempts']) == 4, 'checkpoint12 fixed failed-attempt count differs')
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
             not outer['accepted_owners'] and not outer['normal_passed'] and
             outer['targets'][module] == binding['targets'][module] == context['project_sources'][module] ==
             spec['source_sha256'], 'checkpoint12 failed source/stage binding')
        log = files[originals[record['log']]]
        need(record['exit_code'] == 1 and record['cwd'] == '/workspace/blue-member-build' and
             record['argv'] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
             '/workspace/blue-build-tools/member-runtime-evidence/state.json', 'lake', 'build', '+' + module + ':olean'] and
             record['actual_failed_modules'] == [module] and record['actual_built_modules'] == [] and
             record['project_error_count'] == spec['project_error_count'] and
             len(record['project_error_sections']) == spec['reported_error_sections'] and
             len(log) == record['log_bytes'] and sha(log) == record['log_sha256'] == spec['normal_log_sha256'],
             'checkpoint12 failed command/log differs')
        log_lines = ANSI.sub('', log.decode()).splitlines()
        for section in record['project_error_sections']:
            need(0 < section['line'] <= len(log_lines) and
                 section['text'].splitlines()[0] == log_lines[section['line'] - 1],
                 'checkpoint12 original failure diagnostic line differs')
        need(not any(p.startswith(stage_root + '/') and
             (p.endswith('/NORMAL_PASS.json') or p.endswith('/VALIDATION_RESULTS.json')) for p in files),
             'checkpoint12 failed stage contains an acceptance receipt')
        failed_attempts.append({**spec, 'normal_exit_code': 1, 'accepted': False,
            'current_failed_preimage_identity_not_claimed': True})
    need(failed_command_paths == {p for p in files if p.endswith('/normal-command.json') and
         get(p)['exit_code'] != 0}, 'checkpoint12 failed normal attempt set differs')
    need(set(config['excluded_failed_owners']) == {s['module'] for s in config['failed_attempts']} and
         set(config['excluded_failed_owners']).isdisjoint(expected), 'checkpoint12 failed owners counted as accepted')
    failure_report = {'failed_attempts': failed_attempts, 'failed_attempt_count': 4,
        'held_stages': held_history, 'held_stage_count': 25,
        'classification_is_source_and_stage_specific': True, 'additional_accepted_owners': 0}

    validation_paths = sorted(p for p in files if p.endswith('/VALIDATION_RESULTS.json'))
    need({str(PurePosixPath(p).parent): sorted(get(p)['modules']) for p in validation_paths} ==
         config['audit_lanes'] and len(validation_paths) == 4, 'checkpoint12 exact audit lane/owner scope differs')
    owned_names_by_module, inventory_rows = {}, []
    for lane, lane_owners in config['audit_lanes'].items():
        need(len(lane_owners) == 1, 'checkpoint12 unexpected multi-owner lane')
        need(sha(files[lane + '/OWNED_EXPORTS.json']) == config['owned_export_sha256_by_lane'][lane],
             'checkpoint12 original complete inventory bytes differ')
        exports = get(lane + '/OWNED_EXPORTS.json')
        for owner in lane_owners:
            need(owner not in owned_names_by_module, 'checkpoint12 duplicate inventory owner')
            owned_names_by_module[owner] = [r['name'] for r in exports if r['module'] == owner]
        for row in exports:
            need(set(row) == {'axioms', 'is_private', 'kind', 'module', 'name', 'type',
                            'type_expression', 'universe_parameters'} and
                 isinstance(row['universe_parameters'], list) and
                 all(isinstance(level, str) for level in row['universe_parameters']) and
                 isinstance(row['is_private'], bool), 'checkpoint12 complete type/universe/axiom row differs')
        inventory_rows.extend(exports)
    need(owned_names_by_module == config['owned_names_by_module'] and
         len(inventory_rows) == 96 and sum(r['is_private'] for r in inventory_rows) == 7,
         'checkpoint12 original module-owned inventory/counts differ')
    inventory_report = {'owned_names_by_module': owned_names_by_module,
        'owned_exports_sha256_by_lane': config['owned_export_sha256_by_lane'],
        'ownership_source': 'original environment-owned module field and complete audited inventory',
        'namespace_prefix_filter_used': False, 'full_type_expression_universes_and_axioms_checked_for_all_rows': True,
        'private_owned_names': [r['name'] for r in inventory_rows if r['is_private']],
        'additional_accepted_owners': 0, 'additional_owned_declarations': 0}
    return reuse_report, failure_report, inventory_report


def checkpoint13_scope(files, manifest, originals, repo, expected, git_pairs):
    """Check the thirteen original stage instances without manufacturing a source148 pipeline."""
    config = CHECKPOINTS['13']
    get = lambda p: json.loads(files[p])
    need(len(git_pairs) == 13 and manifest['roots'] == config['roots'] and
         manifest['single_files'] == config['single_files'] and not manifest['omitted_nonreceipt_files'] and
         sha(files['EXPORT_MANIFEST.json']) == config['export_manifest_sha256'],
         'checkpoint13 exact manifest/root/pipeline/Git scope differs')
    need(set(config['stage_bindings']) == set(config['roots']), 'checkpoint13 stage binding scope differs')
    for root, pinned in config['stage_bindings'].items():
        binding = get(root + '/BINDING.json')
        need({k: binding[k] for k in pinned} == pinned and binding['whole_P1_4_complete'] is False and
             binding['protected_roots'] == config['protected_roots'] and
             sha(files[root + '/executed-driver.py']) == pinned['driver_sha256'] and
             sha((repo / pinned['manifest_path']).read_bytes()) == pinned['manifest_sha256'],
             'checkpoint13 original stage/source/driver/manifest binding differs')

    reference_data, reference_rows = {}, {}
    prior_checkpoints = ['05', '06', '07', '08', '09', '10', '11', '12']
    for prior_checkpoint in prior_checkpoints:
        prior_config = CHECKPOINTS[prior_checkpoint]
        prior_archive = repo / ('docs/p1/20261125/p14-continuation/evidence/checkpoint-' +
                                prior_checkpoint + '.tar.xz')
        prior_raw = prior_archive.read_bytes()
        need(len(prior_raw) == prior_config['bytes'] and sha(prior_raw) == prior_config['sha256'],
             'checkpoint13 prior archive binding differs')
        with tarfile.open(fileobj=io.BytesIO(prior_raw), mode='r:xz') as prior_tar:
            prior_manifest = json.load(prior_tar.extractfile('EXPORT_MANIFEST.json'))
            need(prior_manifest['checkpoint'] == prior_checkpoint, 'checkpoint13 prior manifest differs')
            prior_rows = {r['path']: r for r in prior_manifest['files']}
            for original_path, spec in config['reuse_locations'].items():
                if spec['checkpoint'] == prior_checkpoint:
                    reference_data[original_path] = prior_tar.extractfile(spec['path']).read()
                    reference_rows[original_path] = prior_rows[spec['path']]
    current_rows = {r['path']: r for r in manifest['files']}
    for original_path, spec in config['reuse_locations'].items():
        if spec['checkpoint'] == '13':
            need(originals[original_path] == spec['path'], 'checkpoint13 same-checkpoint original path differs')
            reference_data[original_path], reference_rows[original_path] = files[spec['path']], current_rows[spec['path']]
    need(set(reference_data) == set(config['reuse_locations']), 'checkpoint13 missing reference archive')
    reference_reports, reuse_consumers, used_references, held_history = {}, [], set(), []
    counts = {'files': 0, 'pipelines': 0, 'stages': 0, 'same_checkpoint': 0}

    def reference(original_path, source_commit, digest, size, kind, driver_sha256, consumer_owners):
        location_spec = config['reuse_locations'][original_path]
        data, row = reference_data[original_path], reference_rows[original_path]
        original = json.loads(data)
        need(kind == location_spec['reference_kind'] and
             source_commit == original['source_commit'] == location_spec['source_commit'] and
             original_path == row['original_path'] and
             len(data) == row['bytes'] == location_spec['bytes'] and (size is None or size == len(data)) and
             digest == row['sha256'] == sha(data) == location_spec['sha256'] and
             original['whole_P1_4_complete'] is False, 'checkpoint13 reused path/source/raw-file binding')
        owners = original['accepted_owners']
        reference_expected = {'ImbalancedChen.' + m for modules in
            CHECKPOINTS[location_spec['checkpoint']]['groups'].values() for m in modules}
        need(owners == location_spec['accepted_owners'] and len(owners) == len(set(owners)) and
             set(owners) <= reference_expected and set(owners).isdisjoint(consumer_owners),
             'checkpoint13 reused owners differ or counted again')
        if kind == 'pipeline':
            need(original['driver_sha256'] == driver_sha256, 'checkpoint13 reused pipeline driver differs')
            counts['pipelines'] += 1
        else:
            need(kind == 'stage_result' and len(owners) == 1 and
                 original['normal_passed'] == owners and set(original['targets']) == set(owners) and
                 not original['normal_failed_or_held'] and original['audit_error'] is None and
                 original['protected_roots'] == config['protected_roots'],
                 'checkpoint13 reused standalone/stage receipt is not individually accepted')
            counts['stages'] += 1
        if location_spec['checkpoint'] == '13':
            counts['same_checkpoint'] += 1
        else:
            need(set(owners).isdisjoint(expected), 'checkpoint13 prior owner counted as new')
        counts['files'] += 1
        used_references.add(original_path)
        reference_reports[original_path] = {**location_spec,
            'same_checkpoint_reference': location_spec['checkpoint'] == '13'}
        return original

    for spec in config['pipelines']:
        pipeline = get(spec['path'])
        need(sha(files[spec['path']]) == spec['sha256'], 'checkpoint13 original pipeline hash differs')
        reused, reused_paths = set(), []
        if spec['reuse_field'] == 'reused_original_stage_results':
            need('reused_pipeline' not in pipeline and 'reused_pipelines' not in pipeline and
                 pipeline['reused_original_stage_results'] == spec['reused_original_stage_results'] and
                 len(pipeline['reused_original_stage_results']) == 3,
                 'checkpoint13 three-singleton original prerequisite scope differs')
            candidate = get(spec['candidate_binding_path'])
            need(sha(files[spec['candidate_binding_path']]) == spec['candidate_binding_sha256'] and
                 set(candidate) == {'source_commit', 'specs', 'whole_P1_4_complete'} and
                 candidate['source_commit'] == pipeline['source_commit'] and
                 candidate['whole_P1_4_complete'] is False and candidate['specs'] == spec['candidate_specs'] and
                 [s['prerequisite'] for s in candidate['specs']] == pipeline['reused_original_stage_results'] and
                 [s['stage'] for s in candidate['specs']] == spec['completed_stages'] and
                 len(pipeline['checks']) == len(pipeline['stages']) == 3,
                 'checkpoint13 candidate binding scope/source/hash differs')
            for candidate_spec, check, stage in zip(candidate['specs'], pipeline['checks'], pipeline['stages']):
                target = candidate_spec['target']
                stage_root = 'p14/' + candidate_spec['stage'] + '/' + pipeline['source_commit']
                binding = get(stage_root + '/BINDING.json')
                need(candidate_spec['stage'] == check['stage'] == stage['stage'] and
                     binding['manifest_path'] == candidate_spec['manifest'] and
                     binding['manifest_sha256'] == candidate_spec['manifest_sha256'] and
                     binding['targets'] == {target['module']: target['after_sha256']} and
                     target['path'] == target['module'].replace('.', '/') + '.lean' and
                     target['before_sha256'] != target['after_sha256'],
                     'checkpoint13 original candidate manifest/target binding differs')
                check_path = str(PurePosixPath(spec['path']).parent / 'checks' / (stage['stage'] + '.log'))
                check_log = get(check_path)
                need(check['exit_code'] == 0 and sha(files[check_path]) == check['log_sha256'] and
                     check_log == {'status': 'READ_ONLY_SOURCE_CHECK_PASS_NOT_ACCEPTANCE',
                         'source_commit': pipeline['source_commit'], 'targets': [target['module']],
                         'source_closure_count': check['source_closure_count'],
                         'protected_roots': config['protected_roots']} and
                     check['source_closure_count'] == len(binding['project_sources']) and
                     stage['result_sha256'] == sha(files[originals[stage['result_path']]]),
                     'checkpoint13 original read-only check or stage-result raw binding differs')
                prerequisite = candidate_spec['prerequisite']
                previous = reference(prerequisite['result_path'], prerequisite['source_commit'],
                    prerequisite['result_raw_sha256'], prerequisite['result_raw_bytes'], 'stage_result',
                    spec['driver_sha256'], pipeline['accepted_owners'])
                need(previous['stage'] == prerequisite['stage'] and
                     previous['targets'] == {prerequisite['target_module']: prerequisite['source_sha256']} and
                     previous['accepted_owners'] == [prerequisite['target_module']] and
                     binding['project_sources'][prerequisite['target_module']] == prerequisite['source_sha256'],
                     'checkpoint13 prerequisite accepted target/source differs')
                reused.update(previous['accepted_owners'])
                reused_paths.append(prerequisite['result_path'])
                if 'pipeline_path' in prerequisite:
                    previous_pipeline = reference(prerequisite['pipeline_path'], prerequisite['source_commit'],
                        prerequisite['pipeline_raw_sha256'], prerequisite['pipeline_raw_bytes'], 'pipeline',
                        spec['driver_sha256'], pipeline['accepted_owners'])
                    previous_stages = [s for s in previous_pipeline['stages'] if
                        s.get('result_path') == prerequisite['result_path']]
                    need(len(previous_stages) == 1 and previous_stages[0]['stage'] == prerequisite['stage'] and
                         previous_stages[0]['exit_code'] == 0 and
                         previous_stages[0]['accepted_owners'] == previous['accepted_owners'] and
                         previous['accepted_owners'] == previous_pipeline['accepted_owners'],
                         'checkpoint13 original prerequisite pipeline/stage join differs')
                    reused_paths.append(prerequisite['pipeline_path'])
                else:
                    need(prerequisite['result_path'] == config['standalone_accepted_stage']['original_path'] and
                         not any(k.startswith('pipeline_') for k in prerequisite),
                         'checkpoint13 source148 missing original final pipeline was synthesized')
            need(not spec['held_stages'], 'checkpoint13 independent singleton batch unexpectedly held')
        else:
            if spec['reuse_field'] == 'reused_pipeline':
                need('reused_pipeline' in pipeline and 'reused_pipelines' not in pipeline,
                     'checkpoint13 singleton reuse schema differs')
                references = [pipeline['reused_pipeline']]
            else:
                need(spec['reuse_field'] == 'reused_pipelines' and 'reused_pipelines' in pipeline and
                     'reused_pipeline' not in pipeline, 'checkpoint13 plural reuse schema differs')
                references = pipeline['reused_pipelines']
            need([r['path'] for r in references] == spec['reused_paths'] and
                 len(spec['reused_paths']) == len(set(spec['reused_paths'])),
                 'checkpoint13 exact reused path list differs')
            for r in references:
                need(set(r) == {'path', 'sha256', 'source_commit', 'accepted_owners'},
                     'checkpoint13 original pipeline reuse row schema differs')
                previous = reference(r['path'], r['source_commit'], r['sha256'], None, 'pipeline',
                                     spec['driver_sha256'], pipeline['accepted_owners'])
                need(r['accepted_owners'] == previous['accepted_owners'] and
                     reused.isdisjoint(r['accepted_owners']), 'checkpoint13 reused owner list differs or repeats')
                reused.update(r['accepted_owners'])
                reused_paths.append(r['path'])
        available = set(reused)
        for stage in pipeline['stages']:
            if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                need(not set(stage['requires']) <= available and 'result_path' not in stage and
                     not stage.get('accepted_owners'), 'checkpoint13 held stage ignores available original reuse')
                held_history.append({'pipeline_path': spec['path'], 'source_commit': spec['source_commit'],
                    'stage': stage['stage'], 'status': stage['status'], 'requires': stage['requires'],
                    'counts_as_acceptance': False})
            else:
                available.update(stage['accepted_owners'])
        need(available == reused | set(pipeline['accepted_owners']), 'checkpoint13 available owner union differs')
        if 'planned_stages' in pipeline:
            need(pipeline['planned_stages'] == spec['completed_stages'] and
                 pipeline['stop_after_first_failed_group'] is True and not spec['held_stages'],
                 'checkpoint13 completed Range111142 batch differs')
        if 'all_143_original_blocks_reused' in pipeline:
            need(pipeline['all_143_original_blocks_reused'] is True and
                 pipeline['scope'] == 'TypedValid range and typed-encoded signed64 frame only; not original NPY identity.',
                 'checkpoint13 Range aggregate original scope differs')
        if spec['source_commit'] == 'bb377de86aa1e92f461c3d01471010cb0791dad5':
            need(pipeline['accepted_crossing_reused_without_recompilation'] is True and
                 pipeline['held_label5_repairs_are_static_not_prior_normal_failures'] is True and
                 not pipeline['source_preimage_installations'], 'checkpoint13 sourcebb original reuse/scope differs')
        if spec['source_commit'] == '28faf9d2b028997dfe7669b6750c0be5649c9ee4':
            need(not pipeline['source_preimage_installations'] and
                 pipeline['additional_imports_rely_on_existing_no_build_gate'] ==
                 ['ImbalancedChen.ActualRosserLowerLimit', 'ImbalancedChen.P2DirectedLogRounding'],
                 'checkpoint13 source28 original no-build import scope differs')
        reuse_consumers.append({'path': spec['path'], 'source_commit': spec['source_commit'],
            'reused_original_file_paths': reused_paths, 'reused_owners': sorted(reused),
            'held_stages_checked_with_original_reused_owners_available': True,
            'later_acceptance_does_not_reclassify_original_held_stages': True,
            'additional_accepted_owners': 0, 'additional_owned_declarations': 0})
    need(used_references == set(config['reuse_locations']) and len(used_references) == 23 and
         counts == {'files': 26, 'pipelines': 23, 'stages': 3, 'same_checkpoint': 4} and
         len(held_history) == 17, 'checkpoint13 fixed reference/held counts differ')
    reuse_report = {'prior_archive_sha256': {c: CHECKPOINTS[c]['sha256'] for c in prior_checkpoints},
        'references': reference_reports, 'consumers': reuse_consumers, 'reference_count': counts['files'],
        'pipeline_reference_count': counts['pipelines'], 'stage_result_reference_count': counts['stages'],
        'distinct_reference_count': len(used_references), 'same_checkpoint_reference_count': counts['same_checkpoint'],
        'identity_key': ['original_file_path', 'source_commit', 'sha256'],
        'source_commit_alone_is_not_a_reference_key': True, 'source_hash_owner_binding_verified': True,
        'three_original_candidate_checks_are_nonaccepting': True,
        'additional_accepted_owners': 0, 'additional_owned_declarations': 0}

    need(len(config['failed_attempts']) == 4, 'checkpoint13 fixed failed-attempt count differs')
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
             not outer['accepted_owners'] and not outer['normal_passed'] and
             outer['targets'][module] == binding['targets'][module] == context['project_sources'][module] ==
             spec['source_sha256'], 'checkpoint13 failed source/stage binding')
        log = files[originals[record['log']]]
        need(record['exit_code'] == 1 and record['cwd'] == '/workspace/blue-member-build' and
             record['argv'] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
             '/workspace/blue-build-tools/member-runtime-evidence/state.json', 'lake', 'build', '+' + module + ':olean'] and
             record['actual_failed_modules'] == [module] and record['actual_built_modules'] == [] and
             record['project_error_count'] == spec['project_error_count'] and
             len(record['project_error_sections']) == spec['reported_error_sections'] and
             len(log) == record['log_bytes'] and sha(log) == record['log_sha256'] == spec['normal_log_sha256'],
             'checkpoint13 failed command/log differs')
        log_lines = ANSI.sub('', log.decode()).splitlines()
        for section in record['project_error_sections']:
            need(0 < section['line'] <= len(log_lines) and
                 section['text'].splitlines()[0] == log_lines[section['line'] - 1],
                 'checkpoint13 original failure diagnostic line differs')
        need(not any(p.startswith(stage_root + '/') and
             (p.endswith('/NORMAL_PASS.json') or p.endswith('/VALIDATION_RESULTS.json')) for p in files),
             'checkpoint13 failed stage contains an acceptance receipt')
        normal_kernel_memory_diagnostic = spec['stage'] == 'typed-key-uniqueness-kernel-exception-diagnostic'
        if normal_kernel_memory_diagnostic:
            need('(kernel) excessive memory consumption detected' in ANSI.sub('', log.decode()),
                 'checkpoint13 original normal-command memory diagnostic missing')
        failed_attempts.append({**spec, 'normal_exit_code': 1, 'accepted': False,
            'current_failed_preimage_identity_not_claimed': True,
            'normal_command_kernel_memory_diagnostic': normal_kernel_memory_diagnostic,
            'independent_leanchecker_failure_claimed': False})
    need(failed_command_paths == {p for p in files if p.endswith('/normal-command.json') and
         get(p)['exit_code'] != 0}, 'checkpoint13 failed normal attempt set differs')
    failed_owner_names = {s['module'] for s in config['failed_attempts']}
    later = config['failed_then_accepted']
    need(failed_owner_names & set(expected) == {later['module']} and
         set(config['excluded_failed_owners']) == failed_owner_names - {later['module']} and
         set(config['excluded_failed_owners']).isdisjoint(expected),
         'checkpoint13 failed source/stage was confused with later accepted source')
    failed_instance = [s for s in config['failed_attempts'] if s['module'] == later['module']]
    accepted_root = 'p14/' + later['accepted_stage'] + '/' + later['accepted_source_commit']
    accepted_result = get(accepted_root + '/runs/attempt-00000/RESULT.json')
    need(len(failed_instance) == 1 and failed_instance[0]['stage'] == later['failed_stage'] and
         failed_instance[0]['source_commit'] == later['failed_source_commit'] and
         accepted_result['stage'] == later['accepted_stage'] and
         accepted_result['source_commit'] == later['accepted_source_commit'] and
         accepted_result['accepted_owners'] == [later['module']] and
         accepted_result['targets'] == {later['module']: later['accepted_source_sha256']} and
         failed_instance[0]['source_sha256'] != later['accepted_source_sha256'],
         'checkpoint13 failed-bb/accepted-148 distinct source binding differs')
    failure_report = {'failed_attempts': failed_attempts, 'failed_attempt_count': 4,
        'held_stages': held_history, 'held_stage_count': 17, 'failed_then_accepted_source_instances': later,
        'classification_is_source_and_stage_specific': True, 'additional_accepted_owners': 0}

    validation_paths = sorted(p for p in files if p.endswith('/VALIDATION_RESULTS.json'))
    need({str(PurePosixPath(p).parent): sorted(get(p)['modules']) for p in validation_paths} ==
         config['audit_lanes'] and len(validation_paths) == 9, 'checkpoint13 exact audit lane/owner scope differs')
    owned_names_by_module, inventory_rows = {}, []
    for lane, lane_owners in config['audit_lanes'].items():
        need(len(lane_owners) == 1, 'checkpoint13 unexpected multi-owner lane')
        need(sha(files[lane + '/OWNED_EXPORTS.json']) == config['owned_export_sha256_by_lane'][lane],
             'checkpoint13 original complete inventory bytes differ')
        exports = get(lane + '/OWNED_EXPORTS.json')
        for owner in lane_owners:
            need(owner not in owned_names_by_module, 'checkpoint13 duplicate inventory owner')
            owned_names_by_module[owner] = [r['name'] for r in exports if r['module'] == owner]
        for row in exports:
            need(set(row) == {'axioms', 'is_private', 'kind', 'module', 'name', 'type',
                            'type_expression', 'universe_parameters'} and
                 isinstance(row['universe_parameters'], list) and
                 all(isinstance(level, str) for level in row['universe_parameters']) and
                 isinstance(row['is_private'], bool), 'checkpoint13 complete type/universe/axiom row differs')
        inventory_rows.extend(exports)
    need(owned_names_by_module == config['owned_names_by_module'] and
         len(inventory_rows) == 164 and sum(r['is_private'] for r in inventory_rows) == 6,
         'checkpoint13 original module-owned inventory/counts differ')
    inventory_report = {'owned_names_by_module': owned_names_by_module,
        'owned_exports_sha256_by_lane': config['owned_export_sha256_by_lane'],
        'ownership_source': 'original environment-owned module field and complete audited inventory',
        'namespace_prefix_filter_used': False, 'full_type_expression_universes_and_axioms_checked_for_all_rows': True,
        'private_owned_names': [r['name'] for r in inventory_rows if r['is_private']],
        'additional_accepted_owners': 0, 'additional_owned_declarations': 0}
    return reuse_report, failure_report, inventory_report


def verify(archive, repo, checkpoint='01'):
    config = CHECKPOINTS[checkpoint]
    need(checkpoint not in ('04', '05', '06', '07', '08', '09', '10', '11', '12', '13') or config['sealed'],
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
    if checkpoint in ('02', '03', '04', '05', '06', '07', '08', '09', '10', '11', '12', '13'):
        predecessor = {'02': '01', '03': '02', '04': '03', '05': '04', '06': '05', '07': '06', '08': '07', '09': '08', '10': '09', '11': '10', '12': '11', '13': '12'}[checkpoint]
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
    if checkpoint in ('05', '06', '07', '08', '09', '10', '11', '12', '13'):
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

    if checkpoint in ('05', '06', '07', '08', '09', '10', '11', '12', '13'):
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
        if checkpoint == '13':
            # This is the original independently completed source148 RESULT. Its
            # interrupted parent task has no final pipeline; none is reconstructed.
            standalone = config['standalone_accepted_stage']
            result_path = standalone['archive_member']
            outer = get(result_path)
            binding = get(PurePosixPath(result_path).parents[2] / 'BINDING.json')
            need(originals[standalone['original_path']] == result_path and result_path not in pipeline_results and
                 len(files[result_path]) == standalone['original_file_bytes'] and
                 sha(files[result_path]) == standalone['original_file_sha256'] and
                 standalone['original_task_final_pipeline_exists'] is False and
                 standalone['missing_final_pipeline_synthesized'] is False and
                 standalone['excluded_missing_final_pipeline'] not in originals,
                 'checkpoint13 original standalone stage/raw-file scope differs')
            need(outer['source_commit'] == binding['source_commit'] == standalone['source_commit'] and
                 outer['stage'] == standalone['stage'] and
                 outer['targets'] == binding['targets'] and
                 outer['protected_roots'] == binding['protected_roots'] == shared_protected and
                 outer['whole_P1_4_complete'] is False and
                 outer['accepted_owners'] == outer['normal_passed'] == standalone['reported_accepted_owners'] and
                 set(outer['targets']) == set(outer['accepted_owners']) and
                 not outer['normal_failed_or_held'] and outer['audit_error'] is None,
                 'checkpoint13 standalone source/target/individual acceptance differs')
            pipeline_results.add(result_path)
            pipeline_accepted.extend(outer['accepted_owners'])
            standalone_report = {**standalone,
                'original_stage_receipt_verified': True,
                'normal_kernel_all_owned_receipts_verified_below': True,
                'counted_once_as_individually_accepted_stage': True}
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

    if checkpoint == '09':
        # The two 5ba batches have the same source commit but distinct receipt paths.
        reference_data, reference_rows = {}, {}
        for prior_checkpoint in ['05', '06', '08']:
            prior_config = CHECKPOINTS[prior_checkpoint]
            prior_archive = repo / ('docs/p1/20261125/p14-continuation/evidence/checkpoint-' +
                                    prior_checkpoint + '.tar.xz')
            prior_raw = prior_archive.read_bytes()
            need(len(prior_raw) == prior_config['bytes'] and sha(prior_raw) == prior_config['sha256'],
                 'checkpoint09 prior archive binding differs')
            with tarfile.open(fileobj=io.BytesIO(prior_raw), mode='r:xz') as prior_tar:
                prior_manifest = json.load(prior_tar.extractfile('EXPORT_MANIFEST.json'))
                need(prior_manifest['checkpoint'] == prior_checkpoint, 'checkpoint09 prior manifest differs')
                prior_rows = {r['path']: r for r in prior_manifest['files']}
                for original_path, spec in config['reuse_locations'].items():
                    if spec['checkpoint'] == prior_checkpoint:
                        reference_data[original_path] = prior_tar.extractfile(spec['path']).read()
                        reference_rows[original_path] = prior_rows[spec['path']]
        current_rows = {r['path']: r for r in manifest['files']}
        for original_path, spec in config['reuse_locations'].items():
            if spec['checkpoint'] == '09':
                reference_data[original_path] = files[spec['path']]
                reference_rows[original_path] = current_rows[spec['path']]
        reference_reports, reuse_consumers, used_references = {}, [], set()
        for spec in config['pipelines']:
            pipeline = get(spec['path'])
            need(sha(files[spec['path']]) == spec['sha256'], 'checkpoint09 pipeline hash differs')
            if spec['reuse_field'] == 'reused_pipeline':
                need('reused_pipeline' in pipeline and 'reused_pipelines' not in pipeline,
                     'checkpoint09 singleton reuse schema differs')
                references = [pipeline['reused_pipeline']]
            else:
                need(spec['reuse_field'] == 'reused_pipelines' and 'reused_pipeline' not in pipeline and
                     'reused_pipelines' in pipeline, 'checkpoint09 plural reuse schema differs')
                references = pipeline['reused_pipelines']
            need([r['path'] for r in references] == spec['reused_paths'],
                 'checkpoint09 exact reused pipeline path list differs')
            reused = set()
            for reference in references:
                original_path = reference['path']
                location_spec = config['reuse_locations'][original_path]
                data, row = reference_data[original_path], reference_rows[original_path]
                original = json.loads(data)
                need(set(reference) == {'path', 'sha256', 'source_commit', 'accepted_owners'} and
                     reference['source_commit'] == original['source_commit'] == location_spec['source_commit'] and
                     reference['path'] == row['original_path'] == original_path and len(data) == row['bytes'] and
                     reference['sha256'] == row['sha256'] == sha(data) == location_spec['sha256'] and
                     original['driver_sha256'] == spec['driver_sha256'] and
                     original['whole_P1_4_complete'] is False, 'checkpoint09 reused path/source/hash binding')
                owners = reference['accepted_owners']
                need(owners == original['accepted_owners'] == location_spec['accepted_owners'] and
                     len(owners) == len(set(owners)) and reused.isdisjoint(owners) and
                     set(owners).isdisjoint(pipeline['accepted_owners']),
                     'checkpoint09 reused owners differ or counted again')
                reused.update(owners)
                used_references.add(original_path)
                reference_reports[original_path] = {'checkpoint': location_spec['checkpoint'],
                    'path': location_spec['path'], 'source_commit': location_spec['source_commit'],
                    'sha256': location_spec['sha256'], 'accepted_owners': owners}
            available = set(reused)
            for stage in pipeline['stages']:
                if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                    need(not set(stage['requires']) <= available, 'checkpoint09 held stage ignores available reuse')
                else:
                    available.update(stage['accepted_owners'])
            need(available == reused | set(pipeline['accepted_owners']), 'checkpoint09 available owner union differs')
            reuse_consumers.append({'path': spec['path'], 'source_commit': spec['source_commit'],
                'reused_pipeline_paths': spec['reused_paths'], 'reused_owners': sorted(reused),
                'held_stages_checked_with_reused_owners_available': True})
        need(used_references == set(config['reuse_locations']) and len(used_references) == 7,
             'checkpoint09 unused or missing reuse reference')
        reuse_report = {'prior_archive_sha256': {c: CHECKPOINTS[c]['sha256'] for c in ['05', '06', '08']},
            'references': reference_reports, 'consumers': reuse_consumers,
            'identity_key': ['original_pipeline_path', 'source_commit', 'sha256'],
            'source_commit_alone_is_not_a_reference_key': True,
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
                 context['project_sources'][module] == spec['source_sha256'], 'checkpoint09 failed source/stage binding')
            log = files[originals[record['log']]]
            need(record['exit_code'] == 1 and record['cwd'] == '/workspace/blue-member-build' and
                 record['argv'] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
                 '/workspace/blue-build-tools/member-runtime-evidence/state.json', 'lake', 'build', '+' + module + ':olean'] and
                 record['actual_failed_modules'] == [module] and record['actual_built_modules'] == [] and
                 record['project_error_count'] == spec['project_error_count'] and
                 len(record['project_error_sections']) == spec['reported_error_sections'] and
                 len(log) == record['log_bytes'] and sha(log) == record['log_sha256'],
                 'checkpoint09 failed command/log differs')
            failed_attempts.append({**spec, 'normal_exit_code': 1, 'normal_log_sha256': record['log_sha256'],
                'accepted': False, 'current_failed_preimage_identity_not_claimed': True})
        need(failed_command_paths == {p for p in files if p.endswith('/normal-command.json') and
             get(p)['exit_code'] != 0}, 'checkpoint09 failed normal attempt set differs')
        need(set(config['excluded_failed_owners']) == {s['module'] for s in config['failed_attempts']} and
             set(config['excluded_failed_owners']).isdisjoint(expected), 'checkpoint09 failed owners counted as accepted')
        failure_report = {'failed_attempts': failed_attempts, 'failed_attempt_count': 2,
            'held_stage_count': sum(len(s['held_stages']) for s in config['pipelines']),
            'classification_is_source_and_stage_specific': True, 'additional_accepted_owners': 0}

    if checkpoint == '10':
        # Five fixed prior pipelines remain distinct by original path, source and hash.
        need(len(git_pairs) == 5, 'checkpoint10 exact Git pair count differs')
        need(sum(len(s['held_stages']) for s in config['pipelines']) == 7,
             'checkpoint10 fixed held-stage count differs')
        need(get(config['key_pipeline_path'])['complete_actual_sorted_witness_required'] is True,
             'checkpoint10 core cannot stand in for the complete sorted witness')
        reference_data, reference_rows = {}, {}
        for prior_checkpoint in ['06', '08', '09']:
            prior_config = CHECKPOINTS[prior_checkpoint]
            prior_archive = repo / ('docs/p1/20261125/p14-continuation/evidence/checkpoint-' +
                                    prior_checkpoint + '.tar.xz')
            prior_raw = prior_archive.read_bytes()
            need(len(prior_raw) == prior_config['bytes'] and sha(prior_raw) == prior_config['sha256'],
                 'checkpoint10 prior archive binding differs')
            with tarfile.open(fileobj=io.BytesIO(prior_raw), mode='r:xz') as prior_tar:
                prior_manifest = json.load(prior_tar.extractfile('EXPORT_MANIFEST.json'))
                need(prior_manifest['checkpoint'] == prior_checkpoint, 'checkpoint10 prior manifest differs')
                prior_rows = {r['path']: r for r in prior_manifest['files']}
                for original_path, spec in config['reuse_locations'].items():
                    if spec['checkpoint'] == prior_checkpoint:
                        reference_data[original_path] = prior_tar.extractfile(spec['path']).read()
                        reference_rows[original_path] = prior_rows[spec['path']]
        reference_reports, reuse_consumers, used_references = {}, [], set()
        for spec in config['pipelines']:
            pipeline = get(spec['path'])
            need(sha(files[spec['path']]) == spec['sha256'], 'checkpoint10 pipeline hash differs')
            if spec['reuse_field'] is None:
                need('reused_pipeline' not in pipeline and 'reused_pipelines' not in pipeline,
                     'checkpoint10 unexpected reuse fields')
                references = []
            elif spec['reuse_field'] == 'reused_pipeline':
                need('reused_pipeline' in pipeline and 'reused_pipelines' not in pipeline,
                     'checkpoint10 singleton reuse schema differs')
                references = [pipeline['reused_pipeline']]
            else:
                need(spec['reuse_field'] == 'reused_pipelines' and 'reused_pipeline' not in pipeline and
                     'reused_pipelines' in pipeline, 'checkpoint10 plural reuse schema differs')
                references = pipeline['reused_pipelines']
            need([r['path'] for r in references] == spec['reused_paths'],
                 'checkpoint10 exact reused pipeline path list differs')
            reused = set()
            for reference in references:
                original_path = reference['path']
                location_spec = config['reuse_locations'][original_path]
                data, row = reference_data[original_path], reference_rows[original_path]
                original = json.loads(data)
                need(set(reference) == {'path', 'sha256', 'source_commit', 'accepted_owners'} and
                     reference['source_commit'] == original['source_commit'] == location_spec['source_commit'] and
                     reference['path'] == row['original_path'] == original_path and len(data) == row['bytes'] and
                     reference['sha256'] == row['sha256'] == sha(data) == location_spec['sha256'] and
                     original['driver_sha256'] == spec['driver_sha256'] and
                     original['whole_P1_4_complete'] is False, 'checkpoint10 reused path/source/hash binding')
                owners = reference['accepted_owners']
                need(owners == original['accepted_owners'] == location_spec['accepted_owners'] and
                     len(owners) == len(set(owners)) and reused.isdisjoint(owners) and
                     set(owners).isdisjoint(pipeline['accepted_owners']),
                     'checkpoint10 reused owners differ or counted again')
                reused.update(owners)
                used_references.add(original_path)
                reference_reports[original_path] = {'checkpoint': location_spec['checkpoint'],
                    'path': location_spec['path'], 'source_commit': location_spec['source_commit'],
                    'sha256': location_spec['sha256'], 'accepted_owners': owners}
            available = set(reused)
            for stage in pipeline['stages']:
                if stage.get('status') == 'HELD_UPSTREAM_NOT_ACCEPTED':
                    need(not set(stage['requires']) <= available, 'checkpoint10 held stage ignores available reuse')
                else:
                    available.update(stage['accepted_owners'])
            need(available == reused | set(pipeline['accepted_owners']), 'checkpoint10 available owner union differs')
            reuse_consumers.append({'path': spec['path'], 'source_commit': spec['source_commit'],
                'reused_pipeline_paths': spec['reused_paths'], 'reused_owners': sorted(reused),
                'held_stages_checked_with_reused_owners_available': True})
        need(used_references == set(config['reuse_locations']) and len(used_references) == 5,
             'checkpoint10 unused or missing reuse reference')
        reuse_report = {'prior_archive_sha256': {c: CHECKPOINTS[c]['sha256'] for c in ['06', '08', '09']},
            'references': reference_reports, 'consumers': reuse_consumers,
            'identity_key': ['original_pipeline_path', 'source_commit', 'sha256'],
            'source_commit_alone_is_not_a_reference_key': True,
            'source_hash_owner_binding_verified': True, 'additional_accepted_owners': 0,
            'additional_owned_declarations': 0}
        need(len(config['failed_attempts']) == 3, 'checkpoint10 fixed failed-attempt count differs')
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
                 context['project_sources'][module] == spec['source_sha256'], 'checkpoint10 failed source/stage binding')
            log = files[originals[record['log']]]
            need(record['exit_code'] == 1 and record['cwd'] == '/workspace/blue-member-build' and
                 record['argv'] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
                 '/workspace/blue-build-tools/member-runtime-evidence/state.json', 'lake', 'build', '+' + module + ':olean'] and
                 record['actual_failed_modules'] == [module] and record['actual_built_modules'] == [] and
                 record['project_error_count'] == spec['project_error_count'] and
                 len(record['project_error_sections']) == spec['reported_error_sections'] and
                 len(log) == record['log_bytes'] and sha(log) == record['log_sha256'],
                 'checkpoint10 failed command/log differs')
            failed_attempts.append({**spec, 'normal_exit_code': 1, 'normal_log_sha256': record['log_sha256'],
                'accepted': False, 'current_failed_preimage_identity_not_claimed': True})
        need(failed_command_paths == {p for p in files if p.endswith('/normal-command.json') and
             get(p)['exit_code'] != 0}, 'checkpoint10 failed normal attempt set differs')
        need(set(config['excluded_failed_owners']) == {s['module'] for s in config['failed_attempts']} and
             set(config['excluded_failed_owners']).isdisjoint(expected), 'checkpoint10 failed owners counted as accepted')
        failure_report = {'failed_attempts': failed_attempts, 'failed_attempt_count': 3,
            'held_stage_count': sum(len(s['held_stages']) for s in config['pipelines']),
            'classification_is_source_and_stage_specific': True, 'additional_accepted_owners': 0}

    if checkpoint == '11':
        # These two successful group batches reuse distinct checkpoint09 pipelines.
        need(len(git_pairs) == 10 and manifest['roots'] == config['roots'] and
             manifest['single_files'] == config['single_files'] and not manifest['omitted_nonreceipt_files'],
             'checkpoint11 exact completed root/pipeline/Git scope differs')
        need(not config['failed_attempts'] and not config['excluded_failed_owners'] and
             not any(p.endswith('/normal-command.json') and get(p)['exit_code'] != 0 for p in files),
             'checkpoint11 unexpected failed normal attempt')
        prior_config = CHECKPOINTS['09']
        prior_archive = repo / 'docs/p1/20261125/p14-continuation/evidence/checkpoint-09.tar.xz'
        prior_raw = prior_archive.read_bytes()
        need(len(prior_raw) == prior_config['bytes'] and sha(prior_raw) == prior_config['sha256'],
             'checkpoint11 prior archive binding differs')
        reference_data, reference_rows = {}, {}
        with tarfile.open(fileobj=io.BytesIO(prior_raw), mode='r:xz') as prior_tar:
            prior_manifest = json.load(prior_tar.extractfile('EXPORT_MANIFEST.json'))
            need(prior_manifest['checkpoint'] == '09', 'checkpoint11 prior manifest differs')
            prior_rows = {r['path']: r for r in prior_manifest['files']}
            for original_path, spec in config['reuse_locations'].items():
                need(spec['checkpoint'] == '09', 'checkpoint11 reuse checkpoint differs')
                reference_data[original_path] = prior_tar.extractfile(spec['path']).read()
                reference_rows[original_path] = prior_rows[spec['path']]
        reference_reports, reuse_consumers, used_references = {}, [], set()
        for spec in config['pipelines']:
            pipeline = get(spec['path'])
            need(sha(files[spec['path']]) == spec['sha256'] and
                 pipeline['planned_stages'] == spec['completed_stages'] and
                 pipeline['stop_after_first_failed_group'] is True and not spec['held_stages'] and
                 all(s['exit_code'] == 0 and s.get('status') != 'HELD_UPSTREAM_NOT_ACCEPTED'
                     for s in pipeline['stages']), 'checkpoint11 completed pipeline/history differs')
            need(spec['reuse_field'] == 'reused_pipeline' and 'reused_pipeline' in pipeline and
                 'reused_pipelines' not in pipeline, 'checkpoint11 singleton reuse schema differs')
            reference = pipeline['reused_pipeline']
            need([reference['path']] == spec['reused_paths'], 'checkpoint11 exact reused path differs')
            original_path = reference['path']
            location_spec = config['reuse_locations'][original_path]
            data, row = reference_data[original_path], reference_rows[original_path]
            original = json.loads(data)
            need(set(reference) == {'path', 'sha256', 'source_commit', 'accepted_owners'} and
                 reference['source_commit'] == original['source_commit'] == location_spec['source_commit'] and
                 reference['path'] == row['original_path'] == original_path and len(data) == row['bytes'] and
                 reference['sha256'] == row['sha256'] == sha(data) == location_spec['sha256'] and
                 original['driver_sha256'] == spec['driver_sha256'] and
                 original['whole_P1_4_complete'] is False, 'checkpoint11 reused path/source/hash binding')
            owners = reference['accepted_owners']
            need(owners == original['accepted_owners'] == location_spec['accepted_owners'] and
                 len(owners) == len(set(owners)) and set(owners).isdisjoint(expected),
                 'checkpoint11 reused owners differ or counted again')
            need(original_path not in used_references, 'checkpoint11 duplicate reuse reference')
            used_references.add(original_path)
            reference_reports[original_path] = {'checkpoint': '09', 'path': location_spec['path'],
                'source_commit': location_spec['source_commit'], 'sha256': location_spec['sha256'],
                'accepted_owners': owners}
            reuse_consumers.append({'path': spec['path'], 'source_commit': spec['source_commit'],
                'reused_pipeline_paths': spec['reused_paths'], 'reused_owners': owners,
                'held_stages': [], 'additional_accepted_owners': 0})
        need(used_references == set(config['reuse_locations']) and len(used_references) == 2,
             'checkpoint11 unused or missing reuse reference')
        reuse_report = {'prior_archive_sha256': {'09': prior_config['sha256']},
            'references': reference_reports, 'consumers': reuse_consumers,
            'identity_key': ['original_pipeline_path', 'source_commit', 'sha256'],
            'source_commit_alone_is_not_a_reference_key': True,
            'source_hash_owner_binding_verified': True, 'additional_accepted_owners': 0,
            'additional_owned_declarations': 0}
        failure_report = {'failed_attempts': [], 'failed_attempt_count': 0, 'held_stage_count': 0,
            'classification_is_source_and_stage_specific': True, 'additional_accepted_owners': 0}

    if checkpoint == '12':
        reuse_report, failure_report, owned_inventory_report = checkpoint12_scope(
            files, manifest, originals, repo, expected, git_pairs)

    if checkpoint == '13':
        reuse_report, failure_report, owned_inventory_report = checkpoint13_scope(
            files, manifest, originals, repo, expected, git_pairs)

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
    if checkpoint == '09':
        need({str(PurePosixPath(p).parent): sorted(get(p)['modules']) for p in validation_paths} ==
             config['audit_lanes'], 'checkpoint09 exact audit lane/owner scope differs')
    if checkpoint == '10':
        need({str(PurePosixPath(p).parent): sorted(get(p)['modules']) for p in validation_paths} ==
             config['audit_lanes'], 'checkpoint10 exact audit lane/owner scope differs')
        owned_names_by_module = {}
        for lane, lane_owners in config['audit_lanes'].items():
            exports = get(lane + '/OWNED_EXPORTS.json')
            for owner in lane_owners:
                need(owner not in owned_names_by_module, 'checkpoint10 duplicate inventory owner')
                owned_names_by_module[owner] = [r['name'] for r in exports if r['module'] == owner]
        need(owned_names_by_module == config['owned_names_by_module'],
             'checkpoint10 original module-owned inventory differs')
        owned_inventory_report = {'owned_names_by_module': owned_names_by_module,
            'ownership_source': 'original environment-owned module field and complete audited inventory',
            'namespace_prefix_filter_used': False, 'additional_accepted_owners': 0,
            'additional_owned_declarations': 0}
    if checkpoint == '11':
        need({str(PurePosixPath(p).parent): sorted(get(p)['modules']) for p in validation_paths} ==
             config['audit_lanes'], 'checkpoint11 exact audit lane/owner scope differs')
        owned_names_by_module = {}
        for lane, lane_owners in config['audit_lanes'].items():
            exports = get(lane + '/OWNED_EXPORTS.json')
            for owner in lane_owners:
                need(owner not in owned_names_by_module, 'checkpoint11 duplicate inventory owner')
                owned_names_by_module[owner] = [r['name'] for r in exports if r['module'] == owner]
        need(owned_names_by_module == config['owned_names_by_module'],
             'checkpoint11 original module-owned inventory differs')
        owned_inventory_report = {'owned_names_by_module': owned_names_by_module,
            'ownership_source': 'original environment-owned module field and complete audited inventory',
            'namespace_prefix_filter_used': False, 'additional_accepted_owners': 0,
            'additional_owned_declarations': 0}
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
                                        for spec in config['paired_owner_lanes'])) or
             (checkpoint == '09' and str(lane) == config['paired_owner_lane'] and
              lane_modules == config['paired_owners']),
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
        if checkpoint == '13' and module == 'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError':
            # The original successful command has one fixed Lake repository warning.
            # Match its exact lane, original raw hash and complete two-line log;
            # do not strip arbitrary warnings or change any earlier checkpoint gate.
            need(str(lane) == 'p14/uniform-adopted-error-add-cast-retry/'
                 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/audits/0a339e2c14ff0c7aef58/lane-0' and
                 kernel['log_sha256'] == 'f86b8c6dc93b9842baca1d3552695f22035f90e9c8d016d79fc62bb098f71377' and
                 kernel_log == "warning: goldbach: repository '/workspace/blue-member-build/.lake/packages/goldbach' "
                 'has local changes\nreplaying ImbalancedChen.P1OriginalFifthUniformAdoptedBankError\n',
                 'checkpoint13 exact original Uniform successful kernel log differs')
        else:
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
    elif checkpoint == '08':
        limits.extend([
            'Only seven individually accepted owners in the twelve fixed executed roots and five final pipelines are counted; five failed normal attempts and twenty-one held stages remain history.',
            'Reused C490/A700 and 8682 references must join the pinned checkpoint06/07 archives; references to the 935 pipeline must join this archive. They only extend original held-stage availability and add no duplicate acceptance.',
            'GammaRateOwnerVolume failed at source935/owner-gamma-expression-retry and passed at source89db/owner-gamma-beta-retry. Failure classification is source/stage specific; only the later accepted source is checked against the current target.',
            'Range011030 and Base001010 are bounded suppliers. Later numeric/geometry retries, subsequent data blocks and final P1.4 consumers are outside this checkpoint.'])
    elif checkpoint == '09':
        limits.extend([
            'Only fourteen individually accepted owners in the fifteen fixed executed roots and four final pipelines are counted; the original J5 five-error and Barycentric twenty-two-error normal failures and fourteen held stages remain history.',
            'The fixed NamedParents audit lane contains exactly two owners: all fourteen declarations, both independent kernel commands and each separate normal/source receipt are checked.',
            'Seven reuse pointers join by original path, source commit, SHA256 and exact accepted-owner list to checkpoint05/06/08 or the earlier Range batch in this archive. Same-commit batches remain distinct; no reused owner or declaration is counted again.',
            'Range031070 and Base011070 are bounded suppliers. Later block groups, J5/Barycentric retries, TypedKey certificates and final P1.4 consumers are outside this checkpoint.'])
    elif checkpoint == '10':
        limits.extend([
            'Only two individually accepted owners in five fixed executed roots and three final pipelines are counted; the original Crossing four-error, ActualIntegral two-error and KeyCertificate two-error normal failures and seven held stages remain history.',
            'NamedParentsConcreteJ5 owns ten declarations. TypedKeyUniquenessCore owns sixteen declarations in the TypedKeyPartition namespace: ownership follows the original environment module field and complete inventory, never a filename-prefix filter.',
            'Five reuse pointers join by original path, source commit, SHA256 and exact ordered accepted-owner list to checkpoint06/08/09. Reused owners and declarations are not counted again.',
            'The key core supplies definitions and lemmas, not the failed complete actual sorted witness. Named parents do not cover the full stored table; later retries, original-NPY association and the final P1.4 consumers are outside this checkpoint.'])
    elif checkpoint == '11':
        limits.extend([
            'Only ten individually accepted owners in the ten fixed completed roots and two successful final pipelines are counted; this fixed scope contains no failed normal attempt or held stage.',
            'The eight Base071142 groups own 144 declarations and the two Range071090 groups own 40 declarations. Complete original environment inventories, including generated auxiliaries, determine ownership; block counts and namespace prefixes do not.',
            'Two earlier-group reuse pointers join by original path, source commit, SHA256 and exact ordered accepted-owner list to checkpoint09. Same-commit batches remain distinct and reused owners or declarations are not counted again.',
            'These group suppliers do not establish either full aggregate theorem, original-NPY association, complete stored-floor equality or the final P1.4 conclusion. Later Range groups and every stage outside the fixed scope are excluded.'])
    elif checkpoint == '12':
        limits.extend([
            'Only four individually accepted owners in eight fixed executed roots and five original final pipelines are counted; four normal failures and twenty-five held stage instances remain source/stage-specific history.',
            'ActualIntegral owns thirty public declarations; CrossingSections owns nineteen public and seven private declarations; Range091110 owns forty public declarations. All ninety-six original environment-owned type, AST, universe and axiom rows are checked without namespace-prefix filtering.',
            'Seventeen reuse pointers join eleven distinct original pipelines in checkpoint05/06/08/09/10/11 and this checkpoint. The source295 reference to source957 adds no duplicate CrossingSections owner or declaration.',
            'Later Barycentric, KeyCertificate, B13, Label5 consumers, remaining Range blocks and Range aggregates are outside this fixed checkpoint. These suppliers do not establish original-NPY association, complete stored-floor equality or the final P1.4 conclusion.'])
    elif checkpoint == '13':
        limits.extend([
            'Only nine individually accepted owners in thirteen fixed original stage roots and five original final pipelines are counted. The separately completed source148 Adopted stage has no parent final pipeline; its own original normal/kernel/all-owned receipts are checked without synthesizing one.',
            'All 164 original environment-owned declaration rows are checked, including 158 public and six private/generated rows, complete types, Lean.Expr trees, universe parameters and transitive axioms. Owner counts are not proof-tree node counts.',
            'Four original normal failures and seventeen held stage instances remain source/stage-specific history. Adopted failed at sourcebb and passed at source148; the later acceptance does not rewrite the earlier pipeline or its held consumers.',
            'The sourcea6 KeyCertificate memory diagnostic occurred in its failed normal command. It supplies neither normal acceptance nor independent leanchecker acceptance and is not reclassified as an independent leanchecker failure.',
            'The sourcea6 Uniform independent leanchecker command exited zero. Its original two-line log contains one fixed Lake goldbach-package local-changes warning before replaying the exact module; the complete log, lane and raw SHA256 are pinned. No arbitrary warning filtering is allowed, and original Git/source/object invariants are still checked.',
            'Twenty-six noncounting file joins cover twenty-three distinct original files: twenty-three pipeline pointers and three stage-result pointers, with four same-checkpoint references. Sourcea6 read-only candidate checks add no acceptance.',
            'The accepted Range aggregate establishes its stated TypedValid and typed-encoded signed64 scope. It does not establish original NPY identity, complete stored-floor equality or the final P1.4 conclusion. Later ChildGap/Key candidates, Indexed attempts and every stage outside the fixed scope are excluded.'])
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
        **({'noncounting_pipeline_reuse': reuse_report} if checkpoint in ('06', '07', '08', '09', '10', '11', '12', '13') else {}),
        **({'unaccepted_failure_and_held_history': failure_report} if checkpoint == '07' else {}),
        **({'source_stage_failed_attempt_history': failure_report} if checkpoint in ('08', '09', '10', '11', '12', '13') else {}),
        **({'owned_module_inventory_binding': owned_inventory_report} if checkpoint in ('10', '11', '12', '13') else {}),
        **({'standalone_accepted_stage_without_parent_final_pipeline': standalone_report} if checkpoint == '13' else {}),
        'whole_P1_4_complete': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', choices=['01', '02', '03', '04', '05', '06', '07', '08', '09', '10', '11', '12', '13'], default='01')
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
