"""Fail-closed source intake for the P3.1 actual coefficient and label budget.

All acceptance pins below are static verifier code, independently checked at
intake. Manifests cannot authorize source edits or replacement rules. This module
only extends source validation; the existing strict/replay/axiom/object pipeline
is unchanged in verify_part3_continuation.py.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Callable

DOCS = "docs/part3-distribution/p31-actual-mass-budget-20261127"
PRIOR_CLOSURE = "docs/part3-distribution/p31-common-hard-tail-20261127/PROJECT_IMPORT_CLOSURE.json"
PRIOR_CLOSURE_SHA256 = "971bc2081d9fef443df60eebef12abb74e2fc34b58337e5763b70547dfef1d22"
BASE_COMMIT = "e63206af301eb31c3518794fe5f9a1816e61f3b6"
ACCEPTED_SOURCE_COMMIT = "a7e34b33f540dff1e507909f8ba42cea446e87cb"

# BEGIN STATIC INTAKE PINS
TARGETS = ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
 'ImbalancedChen.Part3ActualHardTailLabelBudget',
 'ImbalancedChen.Part3ActualLabelBudgetCardinality',
 'ImbalancedChen.Part3ActualModeSmoothMassTail')

EXPECTED_PROVIDER_COUNT = 81

EXPECTED_PROJECT_COUNT = 85

EXPECTED_DECLARATION_COUNTS = {'recovered': 37, 'new': 11, 'total': 48}

EXPECTED_FRAGMENT_COUNTS = {'byte_exact': 22, 'mechanically_adapted': 1, 'fixed_replacement_steps': 1}

SOURCE_PINS = {'ImbalancedChen.Part3ActualModeCoefficientNormsCore': (10105,
                                                        'f962b424fecdbd1e4542c61daeefa6abfcf6fe884a7c9860fc1f2ab6c4274365'),
 'ImbalancedChen.Part3ActualHardTailLabelBudget': (3851,
                                                   '3e2c1759b1bdf777681c1262b78a4f82a99e5eefe8b9803f2a76fb762bb1fc1e'),
 'ImbalancedChen.Part3ActualLabelBudgetCardinality': (7095,
                                                   '5c8e7cc495566acdf6ec67c2abda1865fc5b9b229ccec493e772010688e20f4e'),
 'ImbalancedChen.Part3ActualModeSmoothMassTail': (9057,
                                                  '2226799a29adfd54fb0f763cb73bb18123ff04a00722c98bebdec4245c7ccd14')}

DONOR_PINS = {'S1': ('ImbalancedChen/Part3ActualCompletedHardTailMass.lean',
        'docs/part3-distribution/p31-common-hard-tail-20261127/upstream/Part3ActualCompletedHardTailMass.lean.txt',
        9910,
        '2c84a397d5620e43c3e845046e75c5d506ae3ba0e27e1baddd3fd71a0ce2e188',
        'b23e2e000301008244372e076411750ad4daa2bb'),
 'S2': ('ImbalancedChen/Part3ActualModeJointBetaPositiveCount.lean',
        'docs/part3-distribution/p31-actual-mass-budget-20261127/upstream/Part3ActualModeJointBetaPositiveCount.lean.txt',
        8681,
        'f56bd1ee5294fb62a1f5c0fc003908f61daa190a2cf4c4ade84e7a0e9f74504e',
        'cd7095c80aedaa4073f93946831ff27cfe5d4efd'),
 'S3': ('ImbalancedChen/Part3ActualM2FinitePoissonAdapter.lean',
        'docs/part3-distribution/p31-actual-mass-budget-20261127/upstream/Part3ActualM2FinitePoissonAdapter.lean.txt',
        16539,
        'a608ffd41a6425eea9b03ab99cac5bd6971417082ac20c115a3baac887ed5b5f',
        'ba8e1eeb633013a4da29f3a139c724d3bbc48cf4'),
 'S4': ('ImbalancedChen/Part3ActualSeparatedRowLogModeSupplier.lean',
        'docs/part3-distribution/p31-actual-mass-budget-20261127/upstream/Part3ActualSeparatedRowLogModeSupplier.lean.txt',
        136642,
        'd78396829cbd5257345423f03dd39b4a3abace23f596466a906d330a20b89bb8',
        '03b5be64535090929448d59e6faf1113175d3eb1'),
 'S5': ('ImbalancedChen/Part3ActualSeparatedRowFiniteMatcher.lean',
        'docs/part3-distribution/p31-smooth-mass-lanes-20261127/upstream/Part3ActualSeparatedRowFiniteMatcher.lean.txt',
        116891,
        'c668788542424f65003dec6586af9aee814b4e9f4fd7246714eec7815b1f1fe0',
        'c90d4709b3dde3704006ddb8b959c5dc85bcb60a'),
 'S8': ('ImbalancedChen/Part3ElementaryE1RealEndpoint.lean',
        'docs/part3-distribution/p31-actual-mass-budget-20261127/upstream/Part3ElementaryE1RealEndpoint.lean.txt',
        10764,
        '5c386ee17594c075b81b15d56143284fd0f77364f87129d0a96632f17064f8ad',
        'a129f1583f9a5d5782bdc548491eb88f2c38e956'),
 'S7': ('ImbalancedChen/Part3ActualCompletedZeroDifferencePayment.lean',
        'docs/part3-distribution/p31-actual-mass-budget-20261127/upstream/Part3ActualCompletedZeroDifferencePayment.lean.txt',
        33745,
        'd492722a53eb3bf6a5e7cc5dd60fa7ebc50d4743ed56c7c9b00a883917cd05b6',
        'c9e790baf7e031b40fa5ed211c5f15b9e66d21d6')}

FRAGMENT_PINS = {'S5_396_405': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                'S5',
                'recovered_declarations',
                17974,
                485,
                '75d8f6ae9c234a220fadf635b93eebf75d4994a75a5315852730309ab668720b',
                ('ImbalancedChen.Part3.GeneralDActivePairCountSourceOnly.factorCarrier_bounds',)),
 'S5_1760_1760': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S5',
                  'recovered_scope_context',
                  85815,
                  30,
                  '7ed35641eddf560c2c1ac7851135b44b07efe4f94f4c5933587da8755e479903',
                  ()),
 'S5_1766_1769': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S5',
                  'recovered_declarations',
                  86046,
                  227,
                  '9820b4f9b944a9b0ab798fdcd885ebc2f1c12b98fd1d02d0c5de0953815213bf',
                  ('ImbalancedChen.Part3.GeneralDRootResidueCostSourceOnly.rootT',)),
 'S5_2068_2069': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S5',
                  'recovered_declarations',
                  100734,
                  98,
                  '97ad76b3755a7ebfb14cc87c7be554a6f2c759e485e3b6af9adbc7d83bd8e78c',
                  ('ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.natUnit',)),
 'S5_2103_2103': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S5',
                  'recovered_declarations',
                  102207,
                  92,
                  'ed6967c600580fedeb797b2a04a129de7e45b2852afc901c7acf47ac75a6cb64',
                  ('ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.branch',)),
 'S5_2291_2297': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S5',
                  'recovered_declarations',
                  111472,
                  403,
                  '035a6120c4d8d533d74042a364d55167d6e5a266dcb7dbab2bc9594017a81703',
                  ('ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.commonLambda',
                   'ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.commonOmega')),
 'S4_27_30': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
              'S4',
              'recovered_declarations',
              973,
              168,
              'b467e77201032603976bd92bec46ad80b88b51bf66ba1005eae791c97b7ce191',
              ('P3TwoLogMixed22SourceOnly.period_pos', 'P3TwoLogMixed22SourceOnly.basis')),
 'S4_375_375': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                'S4',
                'recovered_declarations',
                16737,
                80,
                'b526e24b5fce509a6cf4b204ab38a4791e448399ed2fe81e8a20696ddfb3f9d0',
                ('P3TwoLogMixed22SourceOnly.norm_basis',)),
 'S4_1683_1684': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  81203,
                  78,
                  '5d3715d918b275d2f7bd564f51045abe64e8052ecceb51759f916066638341d2',
                  ('P3ActualLogAdapterSourceOnly.Hnat', 'P3ActualLogAdapterSourceOnly.Hreal')),
 'S4_1689_1689': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  81534,
                  60,
                  '58cd94f29919689078be309c7b118a83b9c7b4592211c86e7d6abd09042fe93a',
                  ('P3ActualLogAdapterSourceOnly.Uu',)),
 'S4_1823_1828': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  88195,
                  410,
                  'fd2b5d8bbcc7ce6f8dc23e7cd3af7be8cacc0c0e70bbdbe81275ff08c9c5cd88',
                  ('P3ActualLogAdapterSourceOnly.window',
                   'P3ActualLogAdapterSourceOnly.dyadicKey',
                   'P3ActualLogAdapterSourceOnly.block')),
 'S4_2015_2016': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  98239,
                  177,
                  '177cff7119a07a0146fca7d50d99287f522b38522f2f3c309704cc3373e469e2',
                  ('P3ActualLogAdapterSourceOnly.innerPhase', 'P3ActualLogAdapterSourceOnly.hPhase')),
 'S4_2019_2022': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  98563,
                  247,
                  'e797e7e928148e674d3fc09dfffa336538d5e72aef6756a7dbc6bde41a21ad54',
                  ('P3ActualLogAdapterSourceOnly.innerMultiplier',
                   'P3ActualLogAdapterSourceOnly.hMode')),
 'S4_2119_2120': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  103614,
                  189,
                  '36e365a82a4fe5e9ed3979fe8f732516e825515b47c637645895594a0ec08038',
                  ('P3ActualLogAdapterSourceOnly.norm_innerPhase',
                   'P3ActualLogAdapterSourceOnly.norm_hPhase')),
 'S4_2132_2137': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  104328,
                  230,
                  'addf33b9f2449bf1473dcb0baabe415921c09a9e80792b69b7eb84217ad83fde',
                  ('P3ActualLogAdapterSourceOnly.norm_hMode_le',)),
 'S4_2445_2450': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
                  'S4',
                  'recovered_declarations',
                  121612,
                  382,
                  '49849a82b42045d81e6e16a598f0bee033fa290ba95aa02f8f2c96fdfafcce8d',
                  ('ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly.modeW',
                   'ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly.modeOmega')),
 'S3_53_66': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
              'S3',
              'recovered_declarations',
              2607,
              913,
              '3fced376e13d7f417df7d168cb9ba7377e4df9c78e486fede7e6a48d9db2b531',
              ('ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly.actualModeLambda',
               'ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly.actualModeOmega')),
 'S2_22_56': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
              'S2',
              'recovered_declarations',
              1046,
              1748,
              'e5ee7d7d309922971f90aede52bb74d9701f5fd89915c386ad37a8ee6d00c036',
              ('ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_branch_eq (private)',
               'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_rootT_eq (private)',
               'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.baseCarrier_original_window '
               '(private)',
               'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.original_innerMultiplier_norm_le '
               '(private)')),
 'S2_58_85': ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
              'S2',
              'recovered_declarations',
              2795,
              1477,
              '59800bd3b4d8ccbeaa70dd89a7495266fcd5eef30df46082176b0a0e698dd4de',
              ('ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualModeLambda_norm_le',
               'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualModeOmega_norm_le')),
 'S8_21_37': ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
              'S8',
              'recovered_declarations',
              834,
              776,
              'fa247bee8d2394031b368bac4f735ac682375bd77bae18129a7ffd423bd882b5',
              ('ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one',)),
 'S5_885_890': ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
                'S5',
                'recovered_declarations',
                41620,
                337,
                '8f019d748dcd5605d70c2869bd6e3010e525a53bdebb5c2868b395acb3971acc',
                ('ImbalancedChen.Part3.GeneralDPhysicalTailCountSourceOnly.factorCarrier_card_le_add_one',)),
 'S7_90_98': ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
              'S7',
              'recovered_declarations',
              4631,
              668,
              'fe0b93f8457566e399156494af83c0be10296e981098097bbd63d9502f31061f',
              ('ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly.frequency_card_le',)),
 'S1_107_138': ('ImbalancedChen.Part3ActualHardTailLabelBudget',
                'S1',
                'recovered_declarations',
                5835,
                1940,
                '68ea773b0bf300babbe8a75a70401c193431d7207dfe6fc918cbe721c56ab9ba',
                ('ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b.rawLabelBudget',
                 'ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b.sourceAbsMass_le_rawLabelBudget'))}

DECLARATION_PINS = (('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.GeneralDActivePairCountSourceOnly.factorCarrier_bounds',
  'theorem',
  'theorem',
  'named',
  False,
  'recovered',
  'S5_396_405'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.GeneralDRootResidueCostSourceOnly.rootT',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S5_1766_1769'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.natUnit',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S5_2068_2069'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.branch',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S5_2103_2103'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.commonLambda',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S5_2291_2297'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.commonOmega',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S5_2291_2297'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3TwoLogMixed22SourceOnly.period_pos',
  'instance',
  'theorem',
  'named',
  True,
  'recovered',
  'S4_27_30'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3TwoLogMixed22SourceOnly.basis',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_27_30'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3TwoLogMixed22SourceOnly.norm_basis',
  'lemma',
  'theorem',
  'named',
  False,
  'recovered',
  'S4_375_375'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.Hnat',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_1683_1684'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.Hreal',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_1683_1684'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.Uu',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_1689_1689'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.window',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_1823_1828'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.dyadicKey',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_1823_1828'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.block',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_1823_1828'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.innerPhase',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_2015_2016'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.hPhase',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_2015_2016'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.innerMultiplier',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_2019_2022'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.hMode',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_2019_2022'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.norm_innerPhase',
  'lemma',
  'theorem',
  'named',
  False,
  'recovered',
  'S4_2119_2120'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.norm_hPhase',
  'lemma',
  'theorem',
  'named',
  False,
  'recovered',
  'S4_2119_2120'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'P3ActualLogAdapterSourceOnly.norm_hMode_le',
  'lemma',
  'theorem',
  'named',
  False,
  'recovered',
  'S4_2132_2137'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly.modeW',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_2445_2450'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly.modeOmega',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S4_2445_2450'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly.actualModeLambda',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S3_53_66'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly.actualModeOmega',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S3_53_66'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_branch_eq',
  'theorem',
  'theorem',
  'private',
  False,
  'recovered',
  'S2_22_56'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_rootT_eq',
  'theorem',
  'theorem',
  'private',
  False,
  'recovered',
  'S2_22_56'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.baseCarrier_original_window',
  'theorem',
  'theorem',
  'private',
  False,
  'recovered',
  'S2_22_56'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.original_innerMultiplier_norm_le',
  'theorem',
  'theorem',
  'private',
  False,
  'recovered',
  'S2_22_56'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualModeLambda_norm_le',
  'theorem',
  'theorem',
  'named',
  False,
  'recovered',
  'S2_58_85'),
 ('ImbalancedChen.Part3ActualModeCoefficientNormsCore',
  'ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualModeOmega_norm_le',
  'theorem',
  'theorem',
  'named',
  False,
  'recovered',
  'S2_58_85'),
 ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
  'ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one',
  'theorem',
  'theorem',
  'named',
  False,
  'recovered',
  'S8_21_37'),
 ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
  'ImbalancedChen.Part3.GeneralDPhysicalTailCountSourceOnly.factorCarrier_card_le_add_one',
  'theorem',
  'theorem',
  'named',
  False,
  'recovered',
  'S5_885_890'),
 ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
  'ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly.frequency_card_le',
  'theorem',
  'theorem',
  'named',
  False,
  'recovered',
  'S7_90_98'),
 ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
  'ImbalancedChen.Part3.ActualLabelBudgetCardinality20261127.baseCarrier_card_le_add_one',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
  'ImbalancedChen.Part3.ActualLabelBudgetCardinality20261127.full_signed_interval_card_le',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
  'ImbalancedChen.Part3.ActualLabelBudgetCardinality20261127.actual_scaleF_nonneg',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualLabelBudgetCardinality',
  'ImbalancedChen.Part3.ActualLabelBudgetCardinality20261127.actual_rawLabelBudget_le',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualHardTailLabelBudget',
  'ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b.rawLabelBudget',
  'def',
  'definition',
  'named',
  False,
  'recovered',
  'S1_107_138'),
 ('ImbalancedChen.Part3ActualHardTailLabelBudget',
  'ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b.sourceAbsMass_le_rawLabelBudget',
  'theorem',
  'theorem',
  'named',
  False,
  'recovered',
  'S1_107_138'),
 ('ImbalancedChen.Part3ActualHardTailLabelBudget',
  'ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b.sourceAbsMass_mono',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualHardTailLabelBudget',
  'ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b.sourceAbsMass_nonzero_le',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualModeSmoothMassTail',
  'ImbalancedChen.Part3.ActualModeSmoothMassTail20261127.actualMode_sourceAbsMass_le_rawLabelBudget',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualModeSmoothMassTail',
  'ImbalancedChen.Part3.ActualModeSmoothMassTail20261127.actualMode_sixSmoothMass_common_hard_tail',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualModeSmoothMassTail',
  'ImbalancedChen.Part3.ActualModeSmoothMassTail20261127.common_cutoff_xepsilon',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualModeSmoothMassTail',
  'ImbalancedChen.Part3.ActualModeSmoothMassTail20261127.actualMode_sixSmoothMass_common_hard_tail_xepsilon',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None),
 ('ImbalancedChen.Part3ActualModeSmoothMassTail',
  'ImbalancedChen.Part3.ActualModeSmoothMassTail20261127.actualMode_sixSmoothMass_common_hard_tail_xepsilon_cardinality',
  'theorem',
  'theorem',
  'named',
  False,
  'new',
  None))

ADAPTER_RULES = {'S1_107_138': [{'kind': 'strict_linter_unreachable_tactic',
                 'original': '      simp only '
                             '[rawCarrier,finiteInnerCarrier,Finset.card_product,Nat.cast_mul,rawLabelBudget,pow_two] '
                             '<;> ring\n',
                 'replacement': '      simp only '
                                '[rawCarrier,finiteInnerCarrier,Finset.card_product,Nat.cast_mul,rawLabelBudget,pow_two]\n',
                 'expected_occurrences': 1,
                 'reason': 'P1 probe1 job_9d54d225d0224ecb80e60fdb70bdd527 reports line 55:108: error: '
                           'ring tactic does nothing. The unchanged restricted simp closes the final '
                           'cardinality equality; remove only the redundant trailing <;> ring. The '
                           'theorem statement, conclusion, hypotheses and strict lint configuration are '
                           'unchanged.',
                 'diagnostic': 'ImbalancedChen/Part3ActualHardTailLabelBudget.lean:55:108: error: '
                               "'ring' tactic does nothing",
                 'reported_probe': 'job_9d54d225d0224ecb80e60fdb70bdd527'}]}
# END STATIC INTAKE PINS


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError("Actual mass intake: " + message)


def _digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def _line_range(data: bytes, offset: int, size: int) -> list[int]:
    return [data[:offset].count(b"\n") + 1,
            data[:offset + size - 1].count(b"\n") + 1]


def validate_actual_mass_intake(
        root: Path, modules: tuple[str, ...],
        source_imports: Callable[[str, str], tuple[str, ...]],
        validate_project_closure: Callable[[Path, dict, tuple[str, ...]], tuple[str, ...]],
) -> dict:
    """Validate this group's fixed sources without changing the common proof gate."""
    _require(modules == TARGETS, "selected target order changed")
    names = ("SOURCE_INTAKE.json", "SOURCE_FRAGMENTS.json", "PROJECT_IMPORT_CLOSURE.json",
             "SOURCE_DECLARATIONS.json", "MECHANICAL_REPAIRS.json")
    manifest_paths = [root / DOCS / name for name in names]
    intake, fragments, closure, declarations, repairs = [
        json.loads(path.read_text()) for path in manifest_paths]
    for document, schema in (
            (intake, "p31-actual-mass-intake-v1"),
            (fragments, "p31-actual-mass-source-fragments-v1"),
            (closure, "p31-actual-mass-project-closure-v1"),
            (declarations, "p31-actual-mass-source-declarations-v1"),
            (repairs, "p31-actual-mass-fixed-mechanical-repairs-v1")):
        _require(isinstance(document, dict) and document.get("schema") == schema,
                 "manifest schema changed: " + schema)
    _require(intake.get("base_commit") == BASE_COMMIT
             and intake.get("previous_accepted_source_commit") == ACCEPTED_SOURCE_COMMIT,
             "accepted starting point changed")
    _require(intake.get("whole_p31_complete") is False,
             "finite budget must not claim whole P3.1 completion")
    _require(declarations.get("generated_declarations_counted_as_new_proofs") is False,
             "generated declarations must not be counted as new proofs")
    _require(repairs.get("by_fragment") == ADAPTER_RULES,
             "mechanical repairs differ from the verifier allowlist")

    sources = intake.get("sources", [])
    _require([item.get("module") for item in sources] == list(TARGETS),
             "source identities differ from the exact target list")
    source_bytes = {}
    for item in sources:
        module = item["module"]
        relative = module.replace(".", "/") + ".lean"
        size, digest = SOURCE_PINS[module]
        data = (root / relative).read_bytes()
        _require(item.get("path") == relative
                 and type(item.get("bytes")) is int and item["bytes"] == size
                 and item.get("sha256") == digest and len(data) == size
                 and _digest(data) == digest
                 and item.get("imports") == list(source_imports(data.decode(), relative)),
                 "whole source or namespace context changed: " + relative)
        source_bytes[module] = data

    original_records = intake.get("original_sources", [])
    original_ids = [item.get("id") for item in original_records]
    _require(len(original_ids) == len(DONOR_PINS)
             and len(set(original_ids)) == len(original_ids)
             and set(original_ids) == set(DONOR_PINS)
             and fragments.get("original_sources") == original_records,
             "original donor inventory changed")
    original_bytes = {}
    archive_paths = []
    for item in original_records:
        source_id = item["id"]
        source_path, archive_path, size, digest, blob = DONOR_PINS[source_id]
        _require(item.get("source_path") == source_path
                 and item.get("archive_path") == archive_path
                 and type(item.get("bytes")) is int and item["bytes"] == size
                 and item.get("sha256") == digest and item.get("git_blob") == blob,
                 "original donor pin changed: " + source_id)
        path = root / archive_path
        data = path.read_bytes()
        _require(len(data) == size and _digest(data) == digest and _git_blob(data) == blob,
                 "original donor archive changed: " + source_id)
        original_bytes[source_id] = data
        archive_paths.append(path)

    segments = fragments.get("fragments", [])
    _require([item.get("id") for item in segments] == list(FRAGMENT_PINS)
             and intake.get("fragments") == segments,
             "fragment inventory/order differs from the independent pins")
    exact_count = adapted_count = replacement_count = 0
    for segment in segments:
        fragment_id = segment["id"]
        module, source_id, kind, offset, size, digest, declared = FRAGMENT_PINS[fragment_id]
        original = original_bytes[source_id]
        _require(segment.get("module") == module and segment.get("source_id") == source_id
                 and segment.get("kind") == kind and segment.get("declarations") == list(declared)
                 and segment.get("original_path") == DONOR_PINS[source_id][0]
                 and segment.get("original_git_blob") == DONOR_PINS[source_id][4]
                 and type(segment.get("original_byte_offset")) is int
                 and segment["original_byte_offset"] == offset
                 and type(segment.get("original_bytes")) is int
                 and segment["original_bytes"] == size
                 and segment.get("original_sha256") == digest
                 and 0 <= offset < offset + size <= len(original)
                 and segment.get("original_lines_1based_inclusive") == _line_range(original, offset, size),
                 "original fragment identity changed: " + fragment_id)
        expected_body = original[offset:offset + size]
        _require(_digest(expected_body) == digest,
                 "original fragment bytes changed: " + fragment_id)
        fixed_repairs = ADAPTER_RULES.get(fragment_id, [])
        _require(segment.get("mechanical_repairs") == fixed_repairs
                 and segment.get("byte_exact") is (not fixed_repairs),
                 "fragment adaptation is not allowlisted: " + fragment_id)
        for repair in fixed_repairs:
            old, new = repair["original"].encode(), repair["replacement"].encode()
            _require(type(repair["expected_occurrences"]) is int
                     and repair["expected_occurrences"] == 1
                     and expected_body.count(old) == 1,
                     "fixed replacement is not unique: " + fragment_id)
            expected_body = expected_body.replace(old, new, 1)
            replacement_count += 1
        if fixed_repairs:
            adapted_count += 1
        else:
            exact_count += 1
        data = source_bytes[module]
        _require(data.count(expected_body) == 1,
                 "installed fragment is missing or ambiguous: " + fragment_id)
        installed_offset = data.index(expected_body)
        _require(segment.get("installed_path") == module.replace(".", "/") + ".lean"
                 and type(segment.get("installed_byte_offset")) is int
                 and segment["installed_byte_offset"] == installed_offset
                 and type(segment.get("installed_bytes")) is int
                 and segment["installed_bytes"] == len(expected_body)
                 and segment.get("installed_sha256") == _digest(expected_body)
                 and segment.get("installed_lines_1based_inclusive")
                     == _line_range(data, installed_offset, len(expected_body)),
                 "installed fragment record differs from its fixed source bytes: " + fragment_id)
    accounting = {"byte_exact": exact_count, "mechanically_adapted": adapted_count,
                  "fixed_replacement_steps": replacement_count}
    _require(accounting == EXPECTED_FRAGMENT_COUNTS, "recovered fragment accounting changed")

    fields = ("module", "name", "source_kind", "kind", "visibility", "local_instance",
              "origin", "fragment_id")
    recorded = declarations.get("declarations", [])
    _require(tuple(tuple(item.get(field) for field in fields) for item in recorded) == DECLARATION_PINS,
             "source declaration names, ownership or classification changed")
    _require(all(type(item.get("local_instance")) is bool for item in recorded)
             and len({(item["module"], item["name"]) for item in recorded}) == len(recorded),
             "duplicate or malformed source declaration")
    counts = {"recovered": sum(item["origin"] == "recovered" for item in recorded),
              "new": sum(item["origin"] == "new" for item in recorded), "total": len(recorded)}
    _require(counts == EXPECTED_DECLARATION_COUNTS
             and declarations.get("counts") == counts
             and intake.get("source_named_declaration_counts") == counts,
             "source declaration accounting changed")
    recovered = sorted(name.removesuffix(" (private)")
                       for pin in FRAGMENT_PINS.values() for name in pin[-1])
    _require(recovered == sorted(item["name"] for item in recorded if item["origin"] == "recovered"),
             "recovered declaration inventory differs from donor fragments")

    prior_path = root / PRIOR_CLOSURE
    prior_data = prior_path.read_bytes()
    _require(_digest(prior_data) == PRIOR_CLOSURE_SHA256, "accepted provider closure manifest changed")
    prior = json.loads(prior_data)
    prior_records = prior["project_sources"]
    prior_by_module = {item["module"]: item for item in prior_records}
    _require(len(prior_records) == len(prior_by_module) == EXPECTED_PROVIDER_COUNT,
             "accepted provider count changed")
    closure_modules = validate_project_closure(root, closure, TARGETS)
    _require(len(closure_modules) == EXPECTED_PROJECT_COUNT
             and set(closure_modules) == set(prior_by_module) | set(TARGETS)
             and not set(prior_by_module) & set(TARGETS),
             "project closure is not exactly new targets plus accepted providers")
    providers = intake.get("provider_sources", [])
    provider_modules = [item.get("module") for item in providers]
    _require(len(provider_modules) == len(set(provider_modules)) == EXPECTED_PROVIDER_COUNT
             and set(provider_modules) == set(prior_by_module),
             "provider inventory differs from the accepted closure")
    closure_by_module = {item["module"]: item for item in closure["project_sources"]}
    for item in providers:
        module = item["module"]
        expected = prior_by_module[module]
        relative = module.replace(".", "/") + ".lean"
        data = (root / relative).read_bytes()
        _require(item.get("path") == relative and type(item.get("bytes")) is int
                 and item["bytes"] == len(data) and _digest(data) == expected["sha256"]
                 and all(item.get(key) == expected[key] == closure_by_module[module].get(key)
                         for key in ("path", "sha256", "imports")),
                 "frozen accepted provider source changed: " + relative)

    paths = [root / (module.replace(".", "/") + ".lean") for module in closure_modules]
    paths += [*manifest_paths, *archive_paths, prior_path,
              root / "verification/p31_actual_mass_intake.py",
              root / "verification/test_part3_source_object_gate.py"]
    return {
        "closure_modules": closure_modules, "closure": closure, "paths": paths,
        "report": {
            "scope": ("Original actual-mode coefficient norms, ordered raw-label mass and finite "
                      "cardinality budgets composed with the accepted common-six hard tail and "
                      "exact x^epsilon/10 cutoff substitution; no uniform original-family error, "
                      "outer mode recombination, original-row reconstruction, m=0 payment, "
                      "external spectral J/A or whole P3.1 completion"),
            "whole_p31_complete": False,
            "project_import_closure": closure,
            "source_intake": intake,
            "source_fragments": fragments,
            "source_declarations": declarations,
            "mechanical_repairs": repairs,
            "source_named_declaration_counts": counts,
            "recovered_fragment_accounting": accounting,
            "frozen_accepted_provider_modules": sorted(prior_by_module),
            "new_consumer_modules": [TARGETS[-1]],
        },
    }
