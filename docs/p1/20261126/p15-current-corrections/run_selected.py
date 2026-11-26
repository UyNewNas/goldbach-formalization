#!/usr/bin/env python3
"""Run an explicit subset of the P-anchored 21-root current P1 graph.

Previously accepted Support@B, HB@F, Cutoff@K, Licensed@M and PerGroup@O
are excluded from compilation and revalidated only inside the actual dependency closure.

Published Git binds all 360 sources; live checks cover only the selected closure.
Original accepted suppliers keep their own source commits, receipts and artifacts.
This driver never installs sources, imports cache files or rebuilds a supplier.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
RUNNER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
OBSERVATIONS = 'docs/p1/20261126/p15-current-corrections/FIXED_DEPENDENCY_OBSERVATIONS.json'
SOURCE_ANCHOR = 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f'
API = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
MODULE = re.compile(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9']*)+")
SHA256 = re.compile(r'[0-9a-f]{64}')
MANIFEST_SHA = 'b37216a0928fbd7ebb0c14ff4cb51dfbfda568cd1d606db61966417dbb5077a6'
OBSERVATIONS_SHA = '54fe15ebb2f2468246ffa196bc9874faeb9f624ac66da451ae2616c862ff5895'
TARGETS = ['ImbalancedChen.P1OriginalSingletonProperPower', 'ImbalancedChen.P1OriginalHistoricalProperPower', 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary', 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy', 'ImbalancedChen.P1OriginalSingletonSmoothLicence', 'ImbalancedChen.P1OriginalSingletonAtlasProperPower', 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid', 'ImbalancedChen.P1OriginalSingletonAtlasTrim', 'ImbalancedChen.P1OriginalSingletonSupportData', 'ImbalancedChen.P1OriginalSingletonCutoffData', 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches', 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime', 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses', 'ImbalancedChen.P5LicensedOriginalIntegerProfile', 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward', 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily', 'ImbalancedChen.Part3AllKLambdaChartCorrection', 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound', 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment', 'ImbalancedChen.P5OriginalSharpPrimeSynthesis', 'ImbalancedChen.P5PrimeDivisorMeanCorrection']
SUPPLIER_IDENTITIES = {'initial4': ('d20acdf13882e17d97833064f5e7c54f3192b03c', 316, '/workspace/p1-complete-proof/20261125-p15-singleton-proper-power-v1'), 'atlas10': ('418ad4b9a5f2d992871062258a2eefd7fdf4b9ee', 68, '/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1/atlas10'), 'core': ('ef450be0a89b6a3f88b3bca19d06e04e7967fa18', 168, '/workspace/p1-complete-proof/20261125-p15-original-atlas-proper-power-v1'), 'mellin': ('21789da92213323d645122cfcc7dff9c10dc82d6', 168, '/workspace/p1-complete-proof/20261125-p15-original-atlas-proper-power-v1'), 'brun': ('418ad4b9a5f2d992871062258a2eefd7fdf4b9ee', 77, '/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1/p3-20')}


# Fixed one-target overlay; original B acceptance is reused only inside the actual selected closure.
PREVIOUSLY_ACCEPTED_TARGETS = {'ImbalancedChen.P1OriginalSingletonSupportData': {'group': 'support_b',
                                                   'source_commit': '3d292e4cd193ab422ca990e80a25165d5aca33a1',
                                                   'source_sha256': '7b8225f32fe7ae0b23ceaf6bc8bfec0cadf90997e9f0237c5ab5884de4f4c8b7',
                                                   'live_source_closure_count': 109,
                                                   'historical_group': {'source_commit': '3d292e4cd193ab422ca990e80a25165d5aca33a1',
                                                                        'compiler_job': 'job_216f3dbd13b24dab8524da9ada0cac1b',
                                                                        'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                                                                        'run': 'runs/attempt-00000',
                                                                        'owners': ['ImbalancedChen.P1OriginalSingletonSupportData'],
                                                                        'driver': {'commit': '3d292e4cd193ab422ca990e80a25165d5aca33a1',
                                                                                   'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
                                                                                   'bytes': 41262,
                                                                                   'sha256': 'ad45eb501f9a89ce1e594497a7105e4f3fac3587963e9249f40021691a82d725'},
                                                                        'source_graph': {'commit': '3d292e4cd193ab422ca990e80a25165d5aca33a1',
                                                                                         'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
                                                                                         'bytes': 324881,
                                                                                         'sha256': '198861fae512aa5213a1e779bac287b5bc5551991f4e7508e4d51fe819755d73'},
                                                                        'published_source_count': 360,
                                                                        'public_evidence': {'commit': '545566753bae9464560a871bea87ea663f90aa53',
                                                                                            'path': 'docs/p1/20261125/p15-current-public-acceptance/SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json',
                                                                                            'bytes': 1894,
                                                                                            'sha256': '25a6333e4b89b03ca541d72a26b5d7f9273849bb7cc8aed6cc351db99bbc3c1a'},
                                                                        'evidence_kind': 'bounded_public_acceptance'}}}


# HB is retained under F, independently of the unchanged Support@B adapter.
HB_F_MODULE = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
HB_F_CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
HB_F_SOURCE_ANCHOR = '1103fd45507a5889d79ba1629cc36ae0e69a9672'
HB_F_PREVIOUSLY_ACCEPTED_TARGET = {'group': 'hb_f',
 'source_commit': '080d4178711ae042235104f7f4768649f51da2ab',
 'source_sha256': '00af3647913f94a08870c659a6a051858e4b4f39c39db460861693e67b73694e',
 'live_source_closure_count': 67,
 'historical_group': {'source_commit': '080d4178711ae042235104f7f4768649f51da2ab',
                      'compiler_job': 'job_f0761da7e6124e818d654afef54ff5c5',
                      'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                      'run': 'runs/attempt-00000',
                      'owners': ['ImbalancedChen.P5OriginalPrimeChartHBWitnesses'],
                      'driver': {'commit': '080d4178711ae042235104f7f4768649f51da2ab',
                                 'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
                                 'bytes': 48571,
                                 'sha256': '9fffe0f6608eec153c5d58d8269f5ddb1b8f0552d8b862ae73b03451d4eda45c'},
                      'source_graph': {'commit': '080d4178711ae042235104f7f4768649f51da2ab',
                                       'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
                                       'bytes': 330884,
                                       'sha256': '12c8898624290d088a7f51065db87fefa0e7f6ee72954a7fb582a28e17f4f609'},
                      'published_source_count': 360,
                      'public_evidence': {'commit': 'f6fdd7fffe17803c60914bf28b39b55715d34464',
                                          'path': 'docs/p1/20261125/p15-current-public-acceptance/HB_F_PUBLIC_ACCEPTANCE.json',
                                          'bytes': 3109,
                                          'sha256': 'b1c9bbf219d3d1fea2294683f71dce391c91b9abe7d6bb80ceb0238b40081598'},
                      'evidence_kind': 'bounded_public_acceptance'},
 'owned_count': 7,
 'public_count': 7,
 'audit_id': '471e1b1b999850566f97'}
PREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, HB_F_MODULE: HB_F_PREVIOUSLY_ACCEPTED_TARGET}


# Cutoff@K public summary is fixed at L 972c2220d87669869a65c03fa64dc04562e37f0d; acceptance remains at K.
# The original K success is attempt-00000, not the later failed attempt-00001.
CUTOFF_K_MODULE = 'ImbalancedChen.P1OriginalSingletonCutoffData'
CUTOFF_K_SOURCE_ANCHOR = '7c59a3d125d99010a501c14f1ecc60710483f918'
CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET = {
    'group': 'cutoff_k',
    'source_commit': '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e',
    'source_sha256': 'ceb0d90a99b41455124802c5446d16499e11207f1042b790f0646d4c19272b22',
    'live_source_closure_count': 68,
    'historical_group': {
        'source_commit': '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e',
        'compiler_job': 'job_fce62dd5906d4d26ac8cb17790fbec32',
        'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
        'run': 'runs/attempt-00000',
        'owners': ['ImbalancedChen.P1OriginalSingletonCutoffData'],
        'driver': {
            'commit': '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e',
            'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
            'bytes': 59950,
            'sha256': '575fcc9737d0b239cb0d994ad286ad8cae5dbf4406ca898157d7c2e87782c293'},
        'source_graph': {
            'commit': '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e',
            'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
            'bytes': 333254,
            'sha256': 'f683cfc328b7323d4e1840e10dc1eca0b24c4b55b644756ef2e5d910152a27e5'},
        'published_source_count': 360,
        'public_evidence': {
            'commit': '972c2220d87669869a65c03fa64dc04562e37f0d',
            'path': 'docs/p1/20261125/p15-current-public-acceptance/CUTOFF_K_PUBLIC_ACCEPTANCE.json',
            'bytes': 4286,
            'sha256': 'd7154414aa34e42a0b34e4e6cc7283b2b91fb55c114c0f44e9a9f7c4e582ed74'},
        'evidence_kind': 'bounded_public_acceptance'},
    'owned_count': 16,
    'public_count': 8,
    'audit_id': '1e6cc20cbf6f23c9f612'}
PREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS,
                              CUTOFF_K_MODULE: CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET}


# Licensed@M public evidence is published at N; the original M acceptance stays fixed.
# Reuse the unchanged historical normal/full-owned readers only in the actual closure.
LICENSED_M_MODULE = 'ImbalancedChen.P5LicensedOriginalIntegerProfile'
LICENSED_M_FAILED_MODULE = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
LICENSED_M_SOURCE_ANCHOR = '972c2220d87669869a65c03fa64dc04562e37f0d'
LICENSED_M_PUBLIC_PATH = 'docs/p1/20261125/p15-current-public-acceptance/LICENSED_M_PUBLIC_ACCEPTANCE.json'
LICENSED_M_RESULT = {'bytes': 37943, 'sha256': 'a1173904f25955de383622f4641d1bd5de6ff04b4b077357cf5623c6b21211f5'}
LICENSED_M_WORKER = {'bytes': 37827, 'sha256': '24de7742786b14f0841e40aa242538512c8f5f1f7d2536d4d9cd09f9b1d4c60a'}
LICENSED_M_ORIGINAL_TARGETS = [
    'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
    'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime',
    'ImbalancedChen.P5LicensedOriginalIntegerProfile',
    'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward',
    'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily',
    'ImbalancedChen.Part3AllKLambdaChartCorrection',
    'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound',
    'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection',
]
LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET = {
    'group': 'licensed_m',
    'source_commit': '54c6e72732ce3a6d209960c396956f9cb2fe3f59',
    'source_sha256': '675cea556d3f85f4ca5e4e4c197b95ddd11e2e60f85e86de52388fe9b2531679',
    'live_source_closure_count': 68,
    'historical_group': {
        'source_commit': '54c6e72732ce3a6d209960c396956f9cb2fe3f59',
        'compiler_job': 'job_11072d40ef774d1abb6afb1c38b215b1',
        'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
        'run': 'runs/attempt-00000',
        'owners': ['ImbalancedChen.P5LicensedOriginalIntegerProfile'],
        'driver': {
            'commit': '54c6e72732ce3a6d209960c396956f9cb2fe3f59',
            'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
            'bytes': 72984,
            'sha256': 'a956f87fa00e360156c6e10dba3de857e038486b7e6a97aefebfe80e9a05ccfa'},
        'source_graph': {
            'commit': '54c6e72732ce3a6d209960c396956f9cb2fe3f59',
            'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
            'bytes': 335974,
            'sha256': '0ce2649ad047edaba54c63c62f369d3df1046c5b2bd4cf4a916cac9584348a8d'},
        'published_source_count': 360,
        'public_evidence': {
            'commit': 'c47ea640bf40c22423aec7066c13e5b05956d349',
            'path': 'docs/p1/20261125/p15-current-public-acceptance/LICENSED_M_PUBLIC_ACCEPTANCE.json',
            'bytes': 6083,
            'sha256': '6707a719bc053d687a6ad0a170990a43757b9945d80d124c7cf6f014fad5a543'},
        'evidence_kind': 'bounded_public_acceptance'},
    'owned_count': 33,
    'public_count': 33,
    'audit_id': '43cb6e04e72ce50bfc8e',
}
PREVIOUSLY_ACCEPTED_TARGETS = {
    **PREVIOUSLY_ACCEPTED_TARGETS, LICENSED_M_MODULE: LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET}


def licensed_m_source_binding(s, graph, sources, prior):
    require(prior == LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET and
            prior['source_sha256'] == sources[LICENSED_M_MODULE] and
            len(s.h.closure(graph, [LICENSED_M_MODULE])) == prior['live_source_closure_count'] == 68,
            'fixed Licensed@M source/68-module closure differs')
    fixed, public = prior['historical_group'], prior['historical_group']['public_evidence']
    require(fixed['source_commit'] == prior['source_commit'] and fixed['owners'] == [LICENSED_M_MODULE] and
            fixed['published_source_count'] == 360 and fixed['run'] == 'runs/attempt-00000' and
            re.fullmatch('job_[0-9a-f]{32}', fixed['compiler_job'] or '') and
            re.fullmatch('[0-9a-f]{40}', public['commit'] or '') and
            isinstance(LICENSED_M_PUBLIC_PATH, str) and public['path'] == LICENSED_M_PUBLIC_PATH and
            valid_fingerprint({key: public[key] for key in ('bytes', 'sha256')}) and
            type(prior['owned_count']) is int and type(prior['public_count']) is int and
            0 <= prior['public_count'] <= prior['owned_count'] and
            isinstance(prior['audit_id'], str) and re.fullmatch('[0-9a-f]{20}', prior['audit_id']),
            'Licensed@M original run or measured public publication binding is still unbound')


def require_licensed_m_public_scope(prior, public):
    fixed = prior['historical_group']
    require(public['schema'] == 'p15_M_original_accepted_prefix_public_acceptance_v1' and
            public['status'] == 'ORIGINAL_M_ACCEPTED_OWNERS_REVALIDATED_WITHOUT_EXECUTION' and
            public['source_commit'] == prior['source_commit'] and
            public['compiler_job'] == fixed['compiler_job'] and public['original_run'] == fixed['run'] and
            public['driver'] == fixed['driver'] and public['source_manifest'] == fixed['source_graph'] and
            public['source_anchor_commit'] == LICENSED_M_SOURCE_ANCHOR and
            public['published_source_count'] == 360 and public['original_group_live_closure_count'] == 157 and
            public['selected_owner_live_closure_count'] == 68 and public['preserved_dependency_count'] == 67 and
            public['selected_owners_revalidated'] == [LICENSED_M_MODULE] and
            set(public['owners']) == {LICENSED_M_MODULE} and
            public['original_group_worker_exit_code'] == 1 and
            public['original_group_all_selected_owners_accepted'] is False and
            public['original_group_accepted_owners'] == [LICENSED_M_MODULE] and
            public['original_group_failed_modules'] == [LICENSED_M_FAILED_MODULE] and
            len(public['original_group_not_accepted_modules']) == 14 and
            set(public['original_group_not_accepted_modules']) ==
                set(LICENSED_M_ORIGINAL_TARGETS) - {LICENSED_M_MODULE} and
            public['source_runtime_and_original_receipts_unchanged'] is True and
            type(public['normal_or_kernel_commands_executed']) is int and
            public['normal_or_kernel_commands_executed'] == 0 and
            public['original_result'] == LICENSED_M_RESULT and
            public['original_worker_result'] == LICENSED_M_WORKER and
            public['types_or_archives_exported'] is False and public['axiom_union_exported'] is False and
            public['whole_P1_5_complete'] is False,
            'fixed Licensed@M bounded public identity or original partial run differs')
    owner = public['owners'][LICENSED_M_MODULE]
    require(owner['source_commit'] == prior['source_commit'] and
            owner['source_sha256'] == prior['source_sha256'] and
            type(owner['owned_count']) is int and type(owner['public_count']) is int and
            (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
                (prior['owned_count'], prior['public_count'], prior['audit_id']) and
            owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
            owner['source_plus_five_and_all_21_artifacts_bound_to_original_result'] is True and
            owner['receipt_rebound_to_current_commit'] is False and
            all(valid_fingerprint(owner['receipt_bindings'].get(key)) for key in
                ('normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence')) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and
                valid_fingerprint(pair['before']) and pair['before'] == pair['after']
                for pair in public['original_context_pairs'].values()),
            'Licensed@M complete receipt/count/context pins differ')
    require(public['original_final_stock_readiness'] == {
                'recorded': False, 'reason': 'original_attempt_stopped_after_owner_failure',
                'executed_again_by_collector': False},
            'Licensed@M original partial run did not perform final group stock readiness')


def require_licensed_m_run_scope(public, original, worker):
    for record in (original, worker):
        require(record['source_commit'] == public['source_commit'] and
                len(record['targets']) == 15 and set(record['targets']) == set(LICENSED_M_ORIGINAL_TARGETS) and
                record['targets'][:2] == [LICENSED_M_MODULE, LICENSED_M_FAILED_MODULE] and
                record['accepted_owners'] == [LICENSED_M_MODULE] and
                set(record['failures']) == {LICENSED_M_FAILED_MODULE} and
                set(record['acceptance_bindings']) == {LICENSED_M_MODULE} and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == 157 and
                record['accepted_supplier_recompile_requested'] is False and
                record['dependency_rebuild_requested'] is False and record['old_receipts_rebound'] is False and
                record['old_P3_REUSE_changed'] is False and record['reused_complete_selected_owners'] == [] and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error',
                                                 'final_stock_readiness')),
                'Licensed@M original first-15 partial run differs')
    require('dispatch_error' not in worker and original['dispatch_error'] == 'serialized worker exited 1' and
            original['worker_exit_code'] == 1 and original['all_selected_owners_accepted'] is False and
            all(original[key] == worker[key] for key in
                ('targets', 'failures', 'acceptance_bindings', 'direct_import_readiness',
                 'original_supplier_acceptance_bindings')),
            'Licensed@M original partial RESULT/WORKER identity differs')
    ready = original['direct_import_readiness'][LICENSED_M_MODULE]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and
            ready['actual_failed_modules'] == [], 'Licensed@M accepted owner import readiness differs')
    owner = public['owners'][LICENSED_M_MODULE]
    base = ROOT / public['source_commit'] / LICENSED_M_MODULE
    audit = base / 'audits' / owner['audit_id']
    receipts, binding = owner['receipt_bindings'], original['acceptance_bindings'][LICENSED_M_MODULE]
    require(binding['module'] == LICENSED_M_MODULE and
            binding['normal_receipt'] == {
                'path': str(base / 'normal' / LICENSED_M_MODULE / 'NORMAL_PASS.json'), **receipts['normal']} and
            binding['audits'] == [{
                'plan': {'path': str(audit / 'AUDIT_PLAN.json'), **receipts['audit_plan']},
                'result': {'path': str(audit / 'lane-0/VALIDATION_RESULTS.json'), **receipts['audit_result']}}],
            'Licensed@M public receipt paths/pins differ from original acceptance')


def retained_licensed_m_target(s, spec, module):
    require(module == LICENSED_M_MODULE and module in spec.active and module not in spec.selected,
            'Licensed@M reuse is outside the actual dependency scope')
    prior = spec.manifest['previously_accepted_targets'][module]
    licensed_m_source_binding(s, spec.graph, spec.sources, prior)
    require(module not in spec.manifest['accepted_suppliers'] and
            prior['group'] not in spec.manifest['accepted_supplier_groups'], 'Licensed@M overlay group collides')
    fixed = prior['historical_group']
    public = json.loads(published_binding(fixed['public_evidence']))
    require_licensed_m_public_scope(prior, public)
    run = Path(fixed['evidence_root']) / prior['source_commit'] / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', public['original_result']))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', public['original_worker_result']))
    require_licensed_m_run_scope(public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'Licensed@M original context/Git differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Licensed@M live source/full21 artifacts differ from original accepted binding')
    # Share all state maps and the exact active set. The old normal/full-owned
    # reader retains M's identity even though its original full group failed.
    shadow = SimpleNamespace(**spec.__dict__)
    shadow.manifest = {**spec.manifest,
        'accepted_suppliers': {**spec.manifest['accepted_suppliers'], module: {
            'group': prior['group'], 'source_commit': prior['source_commit'],
            'source_sha256': prior['source_sha256']}},
        'accepted_supplier_groups': {**spec.manifest['accepted_supplier_groups'], prior['group']: fixed}}
    owner = retained_owner(s, shadow, module, validate_live=True)
    evidence, published_owner = spec.supplier_evidence[module], public['owners'][module]
    require(evidence['source_commit'] == prior['source_commit'] and
            evidence['selected_supplier_live_closure_count'] == 68 and
            evidence['original_group_worker_exit_code'] == 1 and
            evidence['owned_count'] == published_owner['owned_count'] and
            evidence['public_count'] == published_owner['public_count'] and
            Path(evidence['audit_plan']['path']).parent.name == published_owner['audit_id'] and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Licensed@M full audit/count/source/full21 post-validation differs')
    spec.dependency_pins[module] = expected
    return owner


# PerGroup remains accepted at O. P publishes only its bounded original receipts
# and the repaired AllK source; the failed fourteen-target run stays failed.
PERGROUP_O_MODULE = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
PERGROUP_O_FAILED_MODULE = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
PERGROUP_O_SOURCE_ANCHOR = 'c47ea640bf40c22423aec7066c13e5b05956d349'
PERGROUP_O_RESULT = {'bytes': 39901, 'sha256': '48934d443e7598fb71c8c20eead738e63af03b4fa7ad11f5c00943b723db2bee'}
PERGROUP_O_WORKER = {'bytes': 39785, 'sha256': 'd0886d01d8b06fc23db731d730fdd05bcb2445faa9fc45799cab766df9bd6cfd'}
PERGROUP_O_ORIGINAL_TARGETS = ['ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward',
 'ImbalancedChen.Part3AllKLambdaChartCorrection',
 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily',
 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound',
 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
 'ImbalancedChen.P1OriginalSingletonSmoothLicence',
 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
 'ImbalancedChen.P5PrimeDivisorMeanCorrection',
 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
PERGROUP_O_PREVIOUSLY_ACCEPTED_TARGET = {'group': 'pergroup_o',
 'source_commit': 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d',
 'source_sha256': '83ac50b41f5927c3e408611cb01cdc5d3712d730b49a507923179eba951606d6',
 'live_source_closure_count': 69,
 'historical_group': {'source_commit': 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d',
                      'compiler_job': 'job_cda017c5183c4b5ba80a8a2182f446ba',
                      'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                      'run': 'runs/attempt-00000',
                      'owners': ['ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'],
                      'driver': {'bytes': 87907,
                                 'commit': 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d',
                                 'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
                                 'sha256': '9e673a755108d8cf58f02db2165654a1df97e701b0137275078e33da2136f5d9'},
                      'source_graph': {'bytes': 339019,
                                       'commit': 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d',
                                       'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
                                       'sha256': '0801ba4e04eacfa8c8d9f99ec657898035d1af3153bcc4023de54bb20833ed2f'},
                      'published_source_count': 360,
                      'public_evidence': {'commit': 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f',
                                          'path': 'docs/p1/20261125/p15-current-public-acceptance/PERGROUP_O_PUBLIC_ACCEPTANCE.json',
                                          'bytes': 6477,
                                          'sha256': '3d69364fab09231361e4f551c2318147966c092ba2e56f3c8292675d6fb196c6'},
                      'evidence_kind': 'bounded_public_acceptance'},
 'owned_count': 68,
 'public_count': 58,
 'audit_id': '370ebae525106ac7bd2e'}
PREVIOUSLY_ACCEPTED_TARGETS = {
    **PREVIOUSLY_ACCEPTED_TARGETS, PERGROUP_O_MODULE: PERGROUP_O_PREVIOUSLY_ACCEPTED_TARGET}


def pergroup_o_source_binding(s, graph, sources, prior):
    require(prior == PERGROUP_O_PREVIOUSLY_ACCEPTED_TARGET and
            sources[PERGROUP_O_MODULE] == prior['source_sha256'] and
            len(s.h.closure(graph, [PERGROUP_O_MODULE])) == prior['live_source_closure_count'] == 69,
            'fixed PerGroup@O source/69-module closure differs')


def require_pergroup_o_scope(prior, public, original, worker):
    fixed, module = prior['historical_group'], PERGROUP_O_MODULE
    expected = {
        'schema': 'p15_O_original_accepted_prefix_public_acceptance_v1',
        'status': 'ORIGINAL_O_ACCEPTED_OWNERS_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': prior['source_commit'], 'source_anchor_commit': PERGROUP_O_SOURCE_ANCHOR,
        'compiler_job': fixed['compiler_job'], 'driver': fixed['driver'],
        'source_manifest': fixed['source_graph'], 'original_run': fixed['run'],
        'published_source_count': 360, 'original_group_live_closure_count': 157,
        'selected_owner_live_closure_count': 69, 'preserved_dependency_count': 68,
        'selected_owners_revalidated': [module], 'original_targets': PERGROUP_O_ORIGINAL_TARGETS,
        'original_group_accepted_owners': [module],
        'original_group_failed_modules': [PERGROUP_O_FAILED_MODULE],
        'original_group_not_accepted_modules': PERGROUP_O_ORIGINAL_TARGETS[1:],
        'original_group_not_started_modules': PERGROUP_O_ORIGINAL_TARGETS[2:],
        'original_group_worker_exit_code': 1, 'original_group_all_selected_owners_accepted': False,
        'original_result': PERGROUP_O_RESULT, 'original_worker_result': PERGROUP_O_WORKER,
        'source_runtime_and_original_receipts_unchanged': True,
        'normal_or_kernel_commands_executed': 0, 'types_or_archives_exported': False,
        'axiom_union_exported': False, 'whole_P1_5_complete': False,
        'original_final_stock_readiness': {'recorded': False,
            'reason': 'original_attempt_stopped_after_owner_failure', 'executed_again_by_collector': False},
    }
    require(all(public.get(key) == value and type(public.get(key)) is type(value)
                for key, value in expected.items()) and set(public['owners']) == {module},
            'fixed PerGroup@O bounded public identity or original partial run differs')
    owner = public['owners'][module]
    require(owner['source_commit'] == prior['source_commit'] and
            owner['source_sha256'] == prior['source_sha256'] and
            type(owner['owned_count']) is int and type(owner['public_count']) is int and
            (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
                (prior['owned_count'], prior['public_count'], prior['audit_id']) and
            owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
            owner['source_plus_five_and_all_21_artifacts_bound_to_original_result'] is True and
            owner['receipt_rebound_to_current_commit'] is False and
            all(valid_fingerprint(owner['receipt_bindings'].get(key)) for key in
                ('normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence')) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and valid_fingerprint(pair['before']) and
                pair['before'] == pair['after'] for pair in public['original_context_pairs'].values()),
            'PerGroup@O complete receipt/count/context pins differ')
    for record in (original, worker):
        require(record['source_commit'] == prior['source_commit'] and
                record['targets'] == PERGROUP_O_ORIGINAL_TARGETS and
                record['accepted_owners'] == [module] and set(record['acceptance_bindings']) == {module} and
                set(record['failures']) == {PERGROUP_O_FAILED_MODULE} and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == 157 and
                record['whole_P1_complete'] is False and record['whole_P1_5_complete'] is False and
                record['accepted_supplier_recompile_requested'] is False and
                record['dependency_rebuild_requested'] is False and record['old_receipts_rebound'] is False and
                record['old_P3_REUSE_changed'] is False and record['reused_complete_selected_owners'] == [] and
                set(record['direct_import_readiness']) == {module, PERGROUP_O_FAILED_MODULE} and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error',
                                                 'final_stock_readiness')),
                'PerGroup@O original first-14 partial run differs')
    require('dispatch_error' not in worker and original['dispatch_error'] == 'serialized worker exited 1' and
            original['worker_exit_code'] == 1 and original['all_selected_owners_accepted'] is False and
            all(original[key] == worker[key] for key in
                ('targets', 'failures', 'acceptance_bindings', 'direct_import_readiness',
                 'original_supplier_acceptance_bindings')),
            'PerGroup@O original partial RESULT/WORKER identity differs')
    ready = original['direct_import_readiness'][module]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and
            ready['actual_failed_modules'] == [], 'PerGroup@O accepted owner import readiness differs')
    base = Path(fixed['evidence_root']) / prior['source_commit'] / module
    audit, receipts = base / 'audits' / owner['audit_id'], owner['receipt_bindings']
    binding = original['acceptance_bindings'][module]
    require(binding['module'] == module and binding['normal_receipt'] == {
                'path': str(base / 'normal' / module / 'NORMAL_PASS.json'), **receipts['normal']} and
            binding['audits'] == [{
                'plan': {'path': str(audit / 'AUDIT_PLAN.json'), **receipts['audit_plan']},
                'result': {'path': str(audit / 'lane-0/VALIDATION_RESULTS.json'), **receipts['audit_result']}}],
            'PerGroup@O public receipt paths/pins differ from original acceptance')


def retained_pergroup_o_target(s, spec, module):
    require(module == PERGROUP_O_MODULE and module in spec.active and module not in spec.selected,
            'PerGroup@O reuse is outside the actual dependency scope')
    prior = spec.manifest['previously_accepted_targets'][module]
    pergroup_o_source_binding(s, spec.graph, spec.sources, prior)
    require(module not in spec.manifest['accepted_suppliers'] and
            prior['group'] not in spec.manifest['accepted_supplier_groups'], 'PerGroup@O overlay group collides')
    fixed = prior['historical_group']
    public = json.loads(published_binding(fixed['public_evidence']))
    run = Path(fixed['evidence_root']) / prior['source_commit'] / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', PERGROUP_O_RESULT))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', PERGROUP_O_WORKER))
    require_pergroup_o_scope(prior, public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'PerGroup@O original context/Git differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'PerGroup@O live source/full21 artifacts differ from original accepted binding')
    # Only this temporary manifest view exposes PerGroup to the original generic
    # historical_group/retained_owner readers. All state maps and active are shared.
    shadow = SimpleNamespace(**spec.__dict__)
    shadow.manifest = {**spec.manifest,
        'accepted_suppliers': {**spec.manifest['accepted_suppliers'], module: {
            'group': prior['group'], 'source_commit': prior['source_commit'],
            'source_sha256': prior['source_sha256']}},
        'accepted_supplier_groups': {**spec.manifest['accepted_supplier_groups'], prior['group']: fixed}}
    owner = retained_owner(s, shadow, module, validate_live=True)
    evidence, published_owner = spec.supplier_evidence[module], public['owners'][module]
    require(evidence['source_commit'] == prior['source_commit'] and
            evidence['selected_supplier_live_closure_count'] == 69 and
            evidence['original_group_worker_exit_code'] == 1 and
            evidence['owned_count'] == published_owner['owned_count'] and
            evidence['public_count'] == published_owner['public_count'] and
            Path(evidence['audit_plan']['path']).parent.name == published_owner['audit_id'] and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'PerGroup@O full audit/count/source/full21 post-validation differs')
    spec.dependency_pins[module] = expected
    return owner


def require(ok, message):
    if not ok:
        raise ValueError(message)


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def pinned(commit, path, digest):
    raw = git_file(commit, path)
    require(hashlib.sha256(raw).hexdigest() == digest, 'published pin differs: ' + path)
    return raw


def helpers():
    raw = pinned(API_COMMIT, API, API_SHA)
    api = ModuleType('published_batch13')
    api.__file__ = API
    exec(compile(raw, API, 'exec'), api.__dict__)
    require((api.REPO, api.PROJECT, api.TOOLS) == (REPO, PROJECT, TOOLS), 'unexpected helper environment')
    code = {p: pinned(TOOLS, p, sha) for p, sha in api.PINS.items()}
    return SimpleNamespace(api=api, h=api.load(code[api.HELPER], 'batch5'),
                           ops=api.load(code[api.OPS], 'batch6'),
                           d=api.load(code[api.PRIMITIVES], 'primitives'), e9=code[api.E9])


def file_binding(path):
    require(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular_fingerprint(s, path):
    require(path.is_file() and not path.is_symlink(),
            'expected existing regular cache file; adoption is separate: ' + str(path))
    return s.d.fingerprint(path)


def run_owner(s, commit, base, run, m, graph, sources):
    folder = base / m
    s.d.write_frozen(folder / 'inputs/e9.py', s.e9)
    # A different Git commit can have the identical proof/dependency context.
    # Hold its retained computation for inspection; the pinned API still owns
    # receipt validation, and this wrapper never rebases an acceptance receipt.
    previous = [p / m for p in ROOT.iterdir()
                if p.is_dir() and p.name != commit and re.fullmatch('[0-9a-f]{40}', p.name)
                and (p / m).is_dir()]
    normal_dir = folder / 'normal' / m
    if not os.path.lexists(normal_dir / 'NORMAL_PASS.json') and any(normal_dir.glob('attempt-*/normal-started.json')):
        previous.append(folder)
    if previous:
        current = s.api.context(commit, PROJECT, m, graph, sources, s.h, s.d)
        current = {k: v for k, v in current.items() if k != 'source_commit'}
        for old in previous:
            normal = old / 'normal' / m
            bindings = []
            receipt = normal / 'NORMAL_PASS.json'
            if receipt.is_file():
                bindings.append((receipt, json.loads(receipt.read_bytes())['dependency_context']))
            for started in normal.glob('attempt-*/normal-started.json'):
                context = started.parent / 'CONTEXT_BEFORE.json'
                require(context.is_file(), 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(started))
                bindings.append((started, json.loads(context.read_bytes())))
            for path, binding in bindings:
                identity = {k: v for k, v in binding.items() if k != 'source_commit'}
                require(identity.keys() == current.keys() and binding.get('source_commit') == old.parent.name,
                        'RETAINED_HISTORY_REQUIRES_INSPECTION: incomplete or misbound context in ' + str(path))
                require(identity != current, 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(path))
            require(bindings or (not any((old / 'plans').glob('*.json')) and
                                 not any((old / 'audits').glob('*'))),
                    'RETAINED_HISTORY_REQUIRES_INSPECTION: missing normal context in ' + str(old))
    # Preserve a partial audit even if its normal later becomes unavailable.
    for plan in (folder / 'plans').glob('*.json'):
        require((folder / 'audits' / plan.stem / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(plan))
    for directory in (folder / 'audits').glob('*'):
        require((directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(directory))
    passed = s.api.normal_one(commit, PROJECT, folder, m, graph, sources, s.h, s.ops, s.d)
    accepted = set()
    s.api.audit(commit, PROJECT, folder, {m: passed}, graph, sources, s.h, s.ops,
                s.d, run / m, accepted)
    require(accepted == {m}, 'owner missing from validated audit receipt')


def artifact_paths(module):
    require(MODULE.fullmatch(module), 'invalid module name')
    relative = module.replace('.', '/')
    lib = '.lake/build/lib/lean/' + relative
    ir = '.lake/build/ir/' + relative
    return [lib + ext for ext in ('.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
                                  '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash',
                                  '.trace', '.ir', '.ir.hash', '.ir.sig')] + [
        ir + ext for ext in ('.c', '.c.hash', '.setup.json', '.bc', '.bc.hash', '.o', '.o.hash',
                            '.o.export', '.o.export.hash')]


def module_artifacts(s, module):
    result = {}
    for relative in artifact_paths(module):
        path = PROJECT / relative
        if os.path.lexists(path):
            require(path.is_file() and not path.is_symlink(), 'unexpected artifact entry: ' + relative)
            result[relative] = s.d.fingerprint(path)
        else:
            result[relative] = None
    return result


def require_fresh_owner(module, artifacts):
    present = [path for path, value in artifacts.items() if value is not None]
    require(not present, 'UNEXPECTED_EXISTING_TARGET_ARTIFACT_REQUIRES_INSPECTION: ' +
            module + ': ' + ', '.join(present))


def existing_owner(s, commit, spec, module):
    folder = ROOT / commit / module
    artifacts = module_artifacts(s, module)
    normal_path = folder / 'normal' / module / 'NORMAL_PASS.json'
    if not os.path.lexists(normal_path):
        require_fresh_owner(module, artifacts)
        return {'status': 'MISSING_WITHOUT_NORMAL_RECEIPT', 'artifacts': artifacts}
    normal = s.api.read_json(normal_path)
    s.api.normal_valid(commit, PROJECT, module, normal,
                       s.api.context(commit, PROJECT, module, spec.graph, spec.sources, s.h, s.d), s.h, s.d)
    return {'status': 'BOUND_CURRENT_NORMAL_RECEIPT', 'artifacts': artifacts, 'normal': normal}


def require_completed_existing_owner(s, commit, spec, module, state):
    require(state['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT',
            'NONSELECTED_TARGET_DEPENDENCY_REQUIRES_OWN_COMPLETE_ACCEPTANCE: ' + module)
    folder = ROOT / commit / module
    for plan in (folder / 'plans').glob('*.json'):
        require((folder / 'audits' / plan.stem / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(plan))
    accepted = set()
    for directory in (folder / 'audits').glob('*'):
        require(directory.is_dir() and not directory.is_symlink() and
                (directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(directory))
        accepted.update(s.api.audit_valid(commit, PROJECT, directory,
            s.api.read_json(directory / 'AUDIT_PLAN.json'), {module: state['normal']},
            spec.graph, spec.sources, s.h, s.d))
    require(accepted == {module}, 'NONSELECTED_TARGET_DEPENDENCY_NOT_ACCEPTED: ' + module)


def acceptance_binding(s, commit, module):
    folder = ROOT / commit / module
    normal = folder / 'normal' / module / 'NORMAL_PASS.json'
    audits = []
    for directory in sorted((folder / 'audits').glob('*')):
        result = directory / 'lane-0/VALIDATION_RESULTS.json'
        plan = directory / 'AUDIT_PLAN.json'
        audits.append({'plan': {'path': str(plan), **regular_fingerprint(s, plan)},
                       'result': {'path': str(result), **regular_fingerprint(s, result)}})
    require(audits, 'missing completed owner audit')
    return {'module': module, 'normal_receipt': {'path': str(normal), **regular_fingerprint(s, normal)},
            'audits': audits, 'source_plus_five_outputs': s.d.snapshot(PROJECT, module),
            'all_observed_target_artifacts': module_artifacts(s, module)}


def direct_import_readiness(s, spec, module, run):
    imports = spec.manifest['project_sources'][module]['all_imports']
    require(imports and all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", dep) for dep in imports),
            'EMPTY_OR_UNKNOWN_DIRECT_IMPORT_SET_REQUIRES_INSPECTION: ' + module)
    command = s.ops.run(run / module, 'direct-import-stock-readiness',
        s.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in imports]), cwd=PROJECT)
    require(command['exit_code'] == 0 and command['actual_built_modules'] == [] and
            command['actual_failed_modules'] == [], 'DIRECT_IMPORTS_NOT_READY_NO_REBUILD_ALLOWED: ' + module)
    return command


def selection(requested):
    require(requested and len(requested) == len(set(requested)), 'explicit unique nonempty --targets required')
    require(set(requested) <= set(TARGETS), 'outside the fixed 21-owner correction whitelist')
    require(not set(requested).intersection(PREVIOUSLY_ACCEPTED_TARGETS),
            'PREVIOUSLY_ACCEPTED_TARGET_MUST_NOT_BE_RECOMPILED')
    return [module for module in TARGETS if module in requested]


def valid_fingerprint(value):
    return (isinstance(value, dict) and set(value) == {'bytes', 'sha256'} and
            isinstance(value['bytes'], int) and not isinstance(value['bytes'], bool) and value['bytes'] >= 0 and
            isinstance(value['sha256'], str) and SHA256.fullmatch(value['sha256']) is not None)


def published_binding(binding):
    require(set(binding) >= {'commit', 'path', 'bytes', 'sha256'} and
            re.fullmatch('[0-9a-f]{40}', binding['commit']) and
            not Path(binding['path']).is_absolute() and '..' not in Path(binding['path']).parts,
            'invalid published binding')
    raw = pinned(binding['commit'], binding['path'], binding['sha256'])
    require(len(raw) == binding['bytes'], 'published byte count differs: ' + binding['path'])
    return raw


def source_manifest(s, commit, selected):
    selected = selection(selected)
    raw = pinned(commit, MANIFEST, MANIFEST_SHA)
    manifest = json.loads(raw)
    require(manifest['schema'] == 'p15_current_corrections_source_and_reuse_manifest_v1' and
            manifest['project'] == str(PROJECT) and manifest['source_anchor_commit'] == SOURCE_ANCHOR and
            manifest['targets'] == TARGETS and manifest['target_count'] == 21 and
            manifest['project_module_count'] == 360, 'fixed correction source scope differs')
    rows = manifest['project_sources']
    require(len(rows) == 360, 'full published source inventory differs')
    graph, sources = {}, {}
    for module, row in rows.items():
        require(MODULE.fullmatch(module) and row['path'] == s.h.module_path(module) and
                SHA256.fullmatch(row['sha256']) and all(dep in rows for dep in row['imports']),
                'invalid published source row: ' + module)
        payload = git_file(commit, row['path'])
        require(payload == git_file(SOURCE_ANCHOR, row['path']) and
                len(payload) == row['bytes'] and s.api.sha(payload) == row['sha256'] and
                hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest() == row['git_blob'] and
                s.h.imports(payload) == row['all_imports'] and
                [dep for dep in row['all_imports'] if dep.startswith('ImbalancedChen.')] == row['imports'],
                'committed source/import identity differs: ' + module)
        graph[module], sources[module] = row['imports'], row['sha256']
    require(set(graph) == s.h.closure(graph, TARGETS), 'published graph is not the exact 21-root closure')
    supplier, fixed = manifest['accepted_suppliers'], manifest['fixed_dependencies']
    blocked = set(manifest['unaccepted_p3_dependencies'])
    parts = [set(TARGETS), set(supplier), set(fixed), blocked]
    require([len(part) for part in parts] == [21, 17, 303, 19] and
            set.union(*parts) == set(graph) and sum(map(len, parts)) == len(graph),
            'owner/supplier/fixed/unaccepted partition differs')
    groups = manifest['accepted_supplier_groups']
    require(set(groups) == set(SUPPLIER_IDENTITIES), 'supplier group whitelist differs')
    for name, (source_commit, count, root) in SUPPLIER_IDENTITIES.items():
        group = groups[name]
        require((group['source_commit'], group['published_source_count'], group['evidence_root']) ==
                (source_commit, count, root) and group['run'] == 'runs/attempt-00000' and
                set(group['owners']) == {m for m in supplier if supplier[m]['group'] == name},
                'original acceptance identity differs: ' + name)
    previous = manifest['previously_accepted_targets']
    require(previous == PREVIOUSLY_ACCEPTED_TARGETS and
            set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE, CUTOFF_K_MODULE, LICENSED_M_MODULE, PERGROUP_O_MODULE},
            'fixed previous-target acceptance identity differs')
    for module, prior in previous.items():
        if module == PERGROUP_O_MODULE:
            require(module in TARGETS and module not in supplier and prior['group'] not in groups,
                    'PerGroup@O previous target classification differs')
            pergroup_o_source_binding(s, graph, sources, prior)
            continue
        if module == LICENSED_M_MODULE:
            require(module in TARGETS and module not in supplier and prior['group'] not in groups,
                    'Licensed@M previous target classification differs')
            licensed_m_source_binding(s, graph, sources, prior)
            continue
        if module == CUTOFF_K_MODULE:
            require(module in TARGETS and module not in supplier and prior['group'] not in groups,
                    'Cutoff@K previous target classification differs')
            cutoff_k_source_binding(s, graph, sources, prior)
            continue
        if module == HB_F_MODULE:
            require(module in TARGETS and module not in supplier and prior['group'] not in groups,
                    'HB@F previous target classification differs')
            hb_f_source_binding(s, graph, sources, prior)
            continue
        require(module in TARGETS and module not in supplier and
                prior['source_sha256'] == sources[module] and
                len(s.h.closure(graph, [module])) == prior['live_source_closure_count'] == 109,
                'previous target source/closure differs')
        require(prior['group'] not in groups and
                prior['historical_group']['source_commit'] == prior['source_commit'] and
                prior['historical_group']['owners'] == [module] and
                prior['historical_group']['published_source_count'] == 360,
                'previous target historical group differs')
        prior_group, public_binding = prior['historical_group'], prior['historical_group']['public_evidence']
        require(re.fullmatch('job_[0-9a-f]{32}', prior_group['compiler_job'] or '') and
                public_binding['commit'] == '545566753bae9464560a871bea87ea663f90aa53' and
                isinstance(public_binding['path'], str) and public_binding['path'] and
                valid_fingerprint({key: public_binding[key] for key in ('bytes', 'sha256')}),
                'Support@B collection or C publication binding is still unbound')
    require(set(manifest['target_source_origins']) == set(TARGETS), 'per-owner source origins incomplete')
    for module, origin in manifest['target_source_origins'].items():
        require(published_binding(origin['canonical_source']) == git_file(commit, rows[module]['path']),
                'original canonical source provenance differs: ' + module)
        for review in origin['source_reviews']:
            published_binding(review)
    observation = manifest['object_observation_binding']
    require(observation['path'] == OBSERVATIONS and observation['sha256'] == OBSERVATIONS_SHA,
            'fixed object observation binding differs')
    observed_raw = pinned(commit, OBSERVATIONS, OBSERVATIONS_SHA)
    require(len(observed_raw) == observation['bytes'], 'fixed observation byte count differs')
    observed = json.loads(observed_raw)
    require(observed['schema'] == 'p15_current_corrections_retained_object_observations_v1' and
            observed['project'] == str(PROJECT) and len(observed['modules']) == 8 and
            observed['new_cloud_probe_performed'] is False, 'fixed object observation scope differs')
    for module, policy in fixed.items():
        require(policy['required_extensions'] == ['.olean', '.trace'], 'dependency pin scope differs')
        if policy['kind'] == 'retained_accepted_normal_dependency_context':
            witness = policy['witness_owner']
            require(witness in supplier and module in s.h.closure(graph, [witness]) - {witness},
                    'invalid retained normal context witness: ' + module)
        else:
            require(policy['kind'] == 'retained_object_observation' and policy['observation_key'] == module and
                    module in observed['modules'], 'unknown fixed dependency provenance: ' + module)
            record = observed['modules'][module]
            require(record['module'] == module and record['project'] == str(PROJECT) and
                    record['source'] == {'bytes': rows[module]['bytes'], 'sha256': rows[module]['sha256']} and
                    all(valid_fingerprint(record['outputs'].get(ext)) for ext in ('.olean', '.trace')),
                    'recorded fixed object source or pin differs: ' + module)
    active = s.h.closure(graph, selected)
    binding = {'source_commit': commit, 'source_anchor_commit': SOURCE_ANCHOR,
        'manifest': {'path': MANIFEST, 'bytes': len(raw), 'sha256': s.api.sha(raw)},
        'observations': observation, 'full_published_source_count': len(graph),
        'selected_live_source_count': len(active), 'selected_targets': selected,
        'full_published_graph_claimed_equal_to_current_live_graph': False}
    return manifest, graph, sources, observed, binding


def retained_read(s, spec, path, expected=None):
    require(path.is_file() and path.resolve() == path, 'missing/nonregular retained evidence: ' + str(path))
    raw = path.read_bytes()
    fp = {'bytes': len(raw), 'sha256': s.api.sha(raw)}
    if expected is not None:
        require(all(fp.get(k) == v for k, v in expected.items()), 'retained evidence pin differs: ' + str(path))
    require(str(path) not in spec.retained_inputs or spec.retained_inputs[str(path)] == fp,
            'retained evidence changed during reading: ' + str(path))
    spec.retained_inputs[str(path)] = fp
    return raw


def historical_group(s, spec, name):
    if name in spec.historical_groups:
        return spec.historical_groups[name]
    fixed = spec.manifest['accepted_supplier_groups'][name]
    commit = fixed['source_commit']
    manifest = json.loads(published_binding(fixed['source_graph']))
    rows = manifest['project_sources']
    require(len(rows) == fixed['published_source_count'], 'historical graph count differs')
    graph, sources = {}, {}
    for module, row in rows.items():
        require(MODULE.fullmatch(module) and row['path'] == s.h.module_path(module) and
                all(dep in rows for dep in row['imports']), 'historical graph row differs')
        raw = git_file(commit, row['path'])
        require(s.api.sha(raw) == row['sha256'] and
                [dep for dep in s.h.imports(raw) if dep.startswith('ImbalancedChen.')] == row['imports'],
                'historical committed graph/source differs: ' + module)
        graph[module], sources[module] = row['imports'], row['sha256']
    public = json.loads(published_binding(fixed['public_evidence']))
    base = Path(fixed['evidence_root']) / commit
    run = base / fixed['run']
    code = published_binding(fixed['driver'])
    require(retained_read(s, spec, run / 'executed-driver.py') == code,
            'retained executed supplier driver differs')
    if name == 'mellin':
        require(public['source_commit'] == commit and public['platform']['job_id'] == fixed['compiler_job'] and
                public['platform']['exit_code'] == 0 and public['new_acceptance_scope'] == fixed['owners'],
                'fixed Mellin terminal identity differs')
        original = json.loads(retained_read(s, spec, run / 'RESULT.json'))
        require(original == {k: v for k, v in public['result'].items() if k not in ('batch6', 'path')},
                'Mellin retained result differs from published terminal observation')
        audit_rows = [row for row in public['normal_and_audit'] if row.get('name') == 'audit-lane-0']
        require(len(audit_rows) == 1 and audit_rows[0].get('batch6') == 'END' and
                audit_rows[0].get('exit_code') == 0 and audit_rows[0].get('built') == [] and
                audit_rows[0].get('failed') == [], 'Mellin published audit-lane success identity differs')
        retained_read(s, spec, run / fixed['owners'][0] / 'audit-lane-0.log',
                      {'sha256': audit_rows[0]['log_sha256']})
    else:
        require(public['source_commit'] == commit and public['compiler_job'] == fixed['compiler_job'] and
                set(public['owners']) == set(fixed['owners']), 'historical public acceptance scope differs')
        expected = ({'sha256': public['original_result_sha256']} if name == 'initial4'
                    else public['original_result'])
        original = json.loads(retained_read(s, spec, run / 'RESULT.json', expected))
    require(original['source_commit'] == commit and set(fixed['owners']) <= set(original['accepted_owners']) and
            not set(fixed['owners']).intersection(original['failures']) and
            not any(k in original for k in ('context_error', 'final_context_error', 'git_error')),
            'supplier original run does not retain these accepted owners')
    for stem in ('CONTEXT', 'GIT'):
        require(retained_read(s, spec, run / (stem + '_BEFORE.json')) ==
                retained_read(s, spec, run / (stem + '_AFTER.json')),
                'retained supplier compile context changed')
    result = SimpleNamespace(fixed=fixed, commit=commit, base=base, graph=graph, sources=sources,
                             public=public, original=original)
    spec.historical_groups[name] = result
    return result


def retained_owner(s, spec, module, validate_live=False):
    if module not in spec.historical_owners:
        supplier = spec.manifest['accepted_suppliers'][module]
        group = historical_group(s, spec, supplier['group'])
        own_closure = s.h.closure(group.graph, [module])
        require(own_closure == s.h.closure(spec.graph, [module]) and
                all(group.sources[m] == spec.sources[m] for m in own_closure),
                'supplier current source closure differs from its original acceptance: ' + module)
        folder = group.base / module
        expected = None if supplier['group'] == 'mellin' else group.public['owners'][module]['receipt_bindings']['normal']
        path = folder / 'normal' / module / 'NORMAL_PASS.json'
        normal = json.loads(retained_read(s, spec, path, expected))
        binding = normal['dependency_context']
        expected_objects = {'.lake/build/lib/lean/' + m.replace('.', '/') + ext
                            for m in own_closure - {module} for ext in ('.olean', '.trace')}
        require(normal['module'] == module and normal['source_commit'] == group.commit and
                normal['status'] == 'NORMAL_PASS_AUDIT_PENDING' and binding['source_commit'] == group.commit and
                binding['project_sources'] == {m: group.sources[m] for m in sorted(own_closure)} and
                set(binding['dependency_objects_and_traces']) == expected_objects and
                all(valid_fingerprint(v) for v in binding['dependency_objects_and_traces'].values()) and
                binding['configuration'] == spec.review['runtime_configuration_bindings'] and
                binding['existing_runtime'] == spec.review['existing_runtime_bindings'],
                'historical normal context is incomplete or misbound: ' + module)
        if supplier['group'] == 'mellin':
            recorded = [row for row in group.public['normal_and_audit'] if row.get('name') == 'normal']
            require(len(recorded) == 1 and recorded[0]['exit_code'] == 0 and recorded[0]['built'] == [module] and
                    normal['normal_command']['log_sha256'] == recorded[0]['log_sha256'],
                    'Mellin original normal log identity differs')
        spec.historical_owners[module] = SimpleNamespace(group=group, normal=normal, normal_path=path,
            folder=folder, live_validated=False)
    owner = spec.historical_owners[module]
    if validate_live and not owner.live_validated:
        group = owner.group
        require(s.h.closure(group.graph, [module]) <= spec.active, 'supplier validation exceeds selected live closure')
        audits = sorted((owner.folder / 'audits').glob('*'))
        require(len(audits) == 1 and audits[0].is_dir() and not audits[0].is_symlink() and
                re.fullmatch('[0-9a-f]{20}', audits[0].name), 'ambiguous or missing retained supplier audit')
        audit, public_bindings = audits[0], {}
        if spec.manifest['accepted_suppliers'][module]['group'] != 'mellin':
            public_bindings = group.public['owners'][module]['receipt_bindings']
        refs = {'audit_plan': audit / 'AUDIT_PLAN.json',
                'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
                'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
                'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
                'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
        for key, path in refs.items():
            retained_read(s, spec, path, public_bindings.get(key))
        plan = s.api.read_json(refs['audit_plan'])
        require(s.api.audit_valid(group.commit, PROJECT, audit, plan, {module: owner.normal},
                group.graph, group.sources, s.h, s.d) == {module}, 'original supplier full audit differs')
        result = s.api.read_json(refs['audit_result'])
        owner.live_validated = True
        spec.supplier_evidence[module] = {'source_commit': group.commit,
            'compiler_job': group.fixed['compiler_job'], 'source_sha256': group.sources[module],
            'published_source_count': group.fixed['published_source_count'],
            'selected_supplier_live_closure_count': len(s.h.closure(group.graph, [module])),
            'normal': {'path': str(owner.normal_path), **spec.retained_inputs[str(owner.normal_path)]},
            'audit_plan': {'path': str(refs['audit_plan']), **spec.retained_inputs[str(refs['audit_plan'])]},
            'audit_result': {'path': str(refs['audit_result']), **spec.retained_inputs[str(refs['audit_result'])]},
            'owned_count': result['total_owned_exports'], 'public_count': result['total_public_exports'],
            'original_group_worker_exit_code': group.original['worker_exit_code'],
            'original_full_audit_revalidated_without_execution': True,
            'receipt_rebound_to_current_commit': False, 'Lean_or_kernel_executed_for_supplier': False}
    return owner


def retained_previous_target(s, spec, module):
    # This is an actual dependency only. It never enlarges the selected closure.
    require(module == 'ImbalancedChen.P1OriginalSingletonSupportData' and
            module in spec.active and module not in spec.selected,
            'previous-target reuse is outside the actual dependency scope')
    prior = spec.manifest['previously_accepted_targets'][module]
    require(prior == PREVIOUSLY_ACCEPTED_TARGETS[module] and
            prior['source_sha256'] == spec.sources[module] and
            module not in spec.manifest['accepted_suppliers'] and
            prior['group'] not in spec.manifest['accepted_supplier_groups'],
            'fixed Support@B overlay differs')
    fixed = prior['historical_group']
    public = json.loads(published_binding(fixed['public_evidence']))
    require(public['source_commit'] == prior['source_commit'] and
            public['compiler_job'] == fixed['compiler_job'] and set(public['owners']) == {module},
            'fixed Support@B public evidence identity differs')
    owner = public['owners'][module]
    require(owner['source_commit'] == prior['source_commit'] and
            owner['source_sha256'] == prior['source_sha256'] and
            valid_fingerprint(public['original_result']) and
            all(valid_fingerprint(owner['receipt_bindings'].get(key)) for key in
                ('normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence')),
            'Support@B bounded public receipt bindings incomplete')
    # All state maps and active remain the very same objects. Only the temporary
    # manifest view exposes the already accepted target to the old supplier API.
    shadow = SimpleNamespace(**spec.__dict__)
    shadow.manifest = {**spec.manifest,
        'accepted_suppliers': {**spec.manifest['accepted_suppliers'], module: {
            'group': prior['group'], 'source_commit': prior['source_commit'],
            'source_sha256': prior['source_sha256']}},
        'accepted_supplier_groups': {**spec.manifest['accepted_supplier_groups'], prior['group']: fixed}}
    result = retained_owner(s, shadow, module, validate_live=True)
    spec.dependency_pins[module] = module_artifacts(s, module)
    return result


def hb_f_source_binding(s, graph, sources, prior):
    require(prior == HB_F_PREVIOUSLY_ACCEPTED_TARGET and
            prior['source_sha256'] == sources[HB_F_MODULE] and
            len(s.h.closure(graph, [HB_F_MODULE])) == prior['live_source_closure_count'] == 67,
            'fixed HB@F source/67-module closure differs')
    fixed, public = prior['historical_group'], prior['historical_group']['public_evidence']
    require(fixed['source_commit'] == prior['source_commit'] and fixed['owners'] == [HB_F_MODULE] and
            fixed['published_source_count'] == 360 and fixed['run'] == 'runs/attempt-00000' and
            re.fullmatch('job_[0-9a-f]{32}', fixed['compiler_job'] or '') and
            re.fullmatch('[0-9a-f]{40}', public['commit'] or '') and
            public['path'] == 'docs/p1/20261125/p15-current-public-acceptance/HB_F_PUBLIC_ACCEPTANCE.json' and
            valid_fingerprint({key: public[key] for key in ('bytes', 'sha256')}),
            'HB@F public collection/publication binding is still unbound')


def require_hb_f_public_scope(prior, public):
    fixed = prior['historical_group']
    require(public['schema'] == 'p15_hb_F_original_public_acceptance_v1' and
            public['status'] == 'ORIGINAL_HB_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION' and
            public['source_commit'] == prior['source_commit'] and
            public['compiler_job'] == fixed['compiler_job'] and
            public['driver'] == fixed['driver'] and public['source_manifest'] == fixed['source_graph'] and
            public['source_anchor_commit'] == HB_F_SOURCE_ANCHOR and
            public['published_source_count'] == 360 and public['selected_owner_live_closure_count'] == 67 and
            public['selected_owners_revalidated'] == [HB_F_MODULE] and set(public['owners']) == {HB_F_MODULE} and
            public['original_group_worker_exit_code'] == 1 and
            public['original_group_all_selected_owners_accepted'] is False and
            public['original_group_accepted_owners'] == [HB_F_MODULE] and
            public['original_group_failed_modules'] == [HB_F_CUTOFF] and
            public['original_group_dispatch_error'] == 'serialized worker exited 1' and
            public['source_runtime_and_original_receipts_unchanged'] is True and
            type(public['normal_or_kernel_commands_executed']) is int and
            public['normal_or_kernel_commands_executed'] == 0 and
            valid_fingerprint(public['original_result']) and valid_fingerprint(public['original_worker_result']),
            'fixed HB@F bounded public identity differs')
    owner = public['owners'][HB_F_MODULE]
    require(owner['source_commit'] == prior['source_commit'] and
            owner['source_sha256'] == prior['source_sha256'] and
            re.fullmatch('[0-9a-f]{20}', owner['audit_id'] or '') and
            type(owner['owned_count']) is int and type(owner['public_count']) is int and
            0 <= owner['public_count'] <= owner['owned_count'] and
            (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
                (prior['owned_count'], prior['public_count'], prior['audit_id']) and
            owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
            owner['receipt_rebound_to_current_commit'] is False and
            all(valid_fingerprint(owner['receipt_bindings'].get(key)) for key in
                ('normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence')) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and
                valid_fingerprint(pair['before']) and pair['before'] == pair['after']
                for pair in public['original_context_pairs'].values()),
            'HB@F complete public receipt/count/context pins differ')


def require_hb_f_run_scope(public, original, worker):
    for record in (original, worker):
        require(record['source_commit'] == public['source_commit'] and
                record['accepted_owners'] == [HB_F_MODULE] and
                len(record['targets']) == 2 and set(record['targets']) == {HB_F_MODULE, HB_F_CUTOFF} and
                set(record['failures']) == {HB_F_CUTOFF} and
                set(record['acceptance_bindings']) == {HB_F_MODULE} and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error')),
                'HB@F original pair scope differs')
    require(original['worker_exit_code'] == 1 and original['all_selected_owners_accepted'] is False and
            original.get('dispatch_error') == 'serialized worker exited 1' and
            'dispatch_error' not in worker and original['failures'] == worker['failures'] and
            original['acceptance_bindings'] == worker['acceptance_bindings'],
            'HB@F original partial-result/worker identity differs')
    binding = original['acceptance_bindings'][HB_F_MODULE]
    receipts = public['owners'][HB_F_MODULE]['receipt_bindings']
    require(binding['module'] == HB_F_MODULE and len(binding['audits']) == 1 and
            {key: binding['normal_receipt'][key] for key in ('bytes', 'sha256')} == receipts['normal'] and
            all({key: binding['audits'][0][name][key] for key in ('bytes', 'sha256')} == receipts[kind]
                for kind, name in (('audit_plan', 'plan'), ('audit_result', 'result'))) ,
            'HB@F public receipts differ from original accepted binding')


def retained_hb_f_target(s, spec, module):
    require(module == HB_F_MODULE and module in spec.active and module not in spec.selected,
            'HB@F reuse is outside the actual dependency scope')
    prior = spec.manifest['previously_accepted_targets'][module]
    hb_f_source_binding(s, spec.graph, spec.sources, prior)
    require(module not in spec.manifest['accepted_suppliers'] and
            prior['group'] not in spec.manifest['accepted_supplier_groups'], 'HB@F overlay group collides')
    fixed = prior['historical_group']
    public = json.loads(published_binding(fixed['public_evidence']))
    require_hb_f_public_scope(prior, public)
    run = Path(fixed['evidence_root']) / prior['source_commit'] / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', public['original_result']))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', public['original_worker_result']))
    require_hb_f_run_scope(public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'HB@F original context/Git differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'HB@F live source/full21 artifacts differ from original accepted binding')
    # Keep the same state maps and active set. Only the manifest view exposes
    # HB@F to the unmodified historical normal/full-owned readers.
    shadow = SimpleNamespace(**spec.__dict__)
    shadow.manifest = {**spec.manifest,
        'accepted_suppliers': {**spec.manifest['accepted_suppliers'], module: {
            'group': prior['group'], 'source_commit': prior['source_commit'],
            'source_sha256': prior['source_sha256']}},
        'accepted_supplier_groups': {**spec.manifest['accepted_supplier_groups'], prior['group']: fixed}}
    owner = retained_owner(s, shadow, module, validate_live=True)
    evidence, published_owner = spec.supplier_evidence[module], public['owners'][module]
    require(evidence['source_commit'] == prior['source_commit'] and
            evidence['selected_supplier_live_closure_count'] == 67 and
            evidence['owned_count'] == published_owner['owned_count'] and
            evidence['public_count'] == published_owner['public_count'] and
            Path(evidence['audit_plan']['path']).parent.name == published_owner['audit_id'] and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'HB@F full audit/count/source/full21 post-validation differs')
    spec.dependency_pins[module] = expected
    return owner


def cutoff_k_source_binding(s, graph, sources, prior):
    require(prior == CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET and
            prior['source_sha256'] == sources[CUTOFF_K_MODULE] and
            len(s.h.closure(graph, [CUTOFF_K_MODULE])) == prior['live_source_closure_count'] == 68,
            'fixed Cutoff@K source/68-module closure differs')
    fixed, public = prior['historical_group'], prior['historical_group']['public_evidence']
    require(fixed['source_commit'] == prior['source_commit'] and fixed['owners'] == [CUTOFF_K_MODULE] and
            fixed['published_source_count'] == 360 and fixed['run'] == 'runs/attempt-00000' and
            re.fullmatch('job_[0-9a-f]{32}', fixed['compiler_job'] or '') and
            re.fullmatch('[0-9a-f]{40}', public['commit'] or '') and
            public['path'] == 'docs/p1/20261125/p15-current-public-acceptance/CUTOFF_K_PUBLIC_ACCEPTANCE.json' and
            valid_fingerprint({key: public[key] for key in ('bytes', 'sha256')}),
            'Cutoff@K original run or public publication binding is still unbound')


def require_cutoff_k_public_scope(prior, public):
    fixed = prior['historical_group']
    require(public['schema'] == 'p15_cutoff_K_original_public_acceptance_v1' and
            public['status'] == 'ORIGINAL_CUTOFF_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION' and
            public['source_commit'] == prior['source_commit'] and
            public['compiler_job'] == fixed['compiler_job'] and
            public['driver'] == fixed['driver'] and public['source_manifest'] == fixed['source_graph'] and
            public['source_anchor_commit'] == CUTOFF_K_SOURCE_ANCHOR and
            public['published_source_count'] == 360 and public['selected_owner_live_closure_count'] == 68 and
            public['selected_owners_revalidated'] == [CUTOFF_K_MODULE] and
            set(public['owners']) == {CUTOFF_K_MODULE} and
            public['original_group_worker_exit_code'] == 0 and
            public['original_group_all_selected_owners_accepted'] is True and
            public['original_group_accepted_owners'] == [CUTOFF_K_MODULE] and
            public['original_group_failed_modules'] == [] and
            public['source_runtime_and_original_receipts_unchanged'] is True and
            type(public['normal_or_kernel_commands_executed']) is int and
            public['normal_or_kernel_commands_executed'] == 0 and
            valid_fingerprint(public['original_result']) and valid_fingerprint(public['original_worker_result']),
            'fixed Cutoff@K single-owner bounded public identity differs')
    owner = public['owners'][CUTOFF_K_MODULE]
    require(owner['source_commit'] == prior['source_commit'] and
            owner['source_sha256'] == prior['source_sha256'] and
            type(owner['owned_count']) is int and type(owner['public_count']) is int and
            (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
                (prior['owned_count'], prior['public_count'], prior['audit_id']) and
            owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
            owner['all_21_artifacts_bound_to_original_result'] is True and
            owner['receipt_rebound_to_current_commit'] is False and
            all(valid_fingerprint(owner['receipt_bindings'].get(key)) for key in
                ('normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence')) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and
                valid_fingerprint(pair['before']) and pair['before'] == pair['after']
                for pair in public['original_context_pairs'].values()),
            'Cutoff@K complete receipt/16-owned/8-public/context pins differ')
    stock = public['original_final_stock_readiness']
    require(stock['exit_code'] == 0 and stock['built'] == [] and stock['failed'] == [] and
            stock['executed_again_by_collector'] is False and valid_fingerprint(stock['log_fingerprint']),
            'Cutoff@K final no-build public evidence differs')


def require_cutoff_k_run_scope(public, original, worker):
    for record in (original, worker):
        require(record['source_commit'] == public['source_commit'] and
                record['targets'] == [CUTOFF_K_MODULE] and record['accepted_owners'] == [CUTOFF_K_MODULE] and
                record['failures'] == {} and set(record['acceptance_bindings']) == {CUTOFF_K_MODULE} and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == 68 and
                record['accepted_supplier_recompile_requested'] is False and
                record['dependency_rebuild_requested'] is False and record['old_receipts_rebound'] is False and
                record['old_P3_REUSE_changed'] is False and record['reused_complete_selected_owners'] == [] and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error', 'dispatch_error')),
                'Cutoff@K original single-owner run differs from the later failed batch')
    require(original['worker_exit_code'] == 0 and original['all_selected_owners_accepted'] is True and
            all(original[key] == worker[key] for key in
                ('failures', 'acceptance_bindings', 'direct_import_readiness', 'final_stock_readiness',
                 'original_supplier_acceptance_bindings')),
            'Cutoff@K original successful RESULT/WORKER identity differs')
    ready, stock = original['direct_import_readiness'][CUTOFF_K_MODULE], original['final_stock_readiness']
    require(all(record['exit_code'] == 0 and record['actual_built_modules'] == [] and
                record['actual_failed_modules'] == [] for record in (ready, stock)),
            'Cutoff@K original stock readiness is not successful and build-free')
    owner = public['owners'][CUTOFF_K_MODULE]
    base = ROOT / public['source_commit'] / CUTOFF_K_MODULE
    audit = base / 'audits' / owner['audit_id']
    receipts, binding = owner['receipt_bindings'], original['acceptance_bindings'][CUTOFF_K_MODULE]
    require(binding['module'] == CUTOFF_K_MODULE and
            binding['normal_receipt'] == {
                'path': str(base / 'normal' / CUTOFF_K_MODULE / 'NORMAL_PASS.json'), **receipts['normal']} and
            binding['audits'] == [{
                'plan': {'path': str(audit / 'AUDIT_PLAN.json'), **receipts['audit_plan']},
                'result': {'path': str(audit / 'lane-0/VALIDATION_RESULTS.json'), **receipts['audit_result']}}],
            'Cutoff@K public receipt paths/pins differ from original acceptance')


def retained_cutoff_k_target(s, spec, module):
    require(module == CUTOFF_K_MODULE and module in spec.active and module not in spec.selected,
            'Cutoff@K reuse is outside the actual dependency scope')
    prior = spec.manifest['previously_accepted_targets'][module]
    cutoff_k_source_binding(s, spec.graph, spec.sources, prior)
    require(module not in spec.manifest['accepted_suppliers'] and
            prior['group'] not in spec.manifest['accepted_supplier_groups'], 'Cutoff@K overlay group collides')
    fixed = prior['historical_group']
    public = json.loads(published_binding(fixed['public_evidence']))
    require_cutoff_k_public_scope(prior, public)
    run = Path(fixed['evidence_root']) / prior['source_commit'] / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', public['original_result']))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', public['original_worker_result']))
    require_cutoff_k_run_scope(public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'Cutoff@K original context/Git differs')
    stock, stock_log = original['final_stock_readiness'], run / 'final-stock-readiness.log'
    require(stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + module + ':olean']) and
            stock['cwd'] == str(PROJECT) and stock['log'] == str(stock_log) and
            {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']} ==
                public['original_final_stock_readiness']['log_fingerprint'],
            'Cutoff@K original guarded final stock command/log binding differs')
    retained_read(s, spec, stock_log, public['original_final_stock_readiness']['log_fingerprint'])
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Cutoff@K live source/full21 artifacts differ from original accepted binding')
    # Share all state maps and the exact active set; only expose this fixed
    # accepted target through the unchanged historical normal/full-owned API.
    shadow = SimpleNamespace(**spec.__dict__)
    shadow.manifest = {**spec.manifest,
        'accepted_suppliers': {**spec.manifest['accepted_suppliers'], module: {
            'group': prior['group'], 'source_commit': prior['source_commit'],
            'source_sha256': prior['source_sha256']}},
        'accepted_supplier_groups': {**spec.manifest['accepted_supplier_groups'], prior['group']: fixed}}
    owner = retained_owner(s, shadow, module, validate_live=True)
    evidence, published_owner = spec.supplier_evidence[module], public['owners'][module]
    require(evidence['source_commit'] == prior['source_commit'] and
            evidence['selected_supplier_live_closure_count'] == 68 and
            evidence['owned_count'] == published_owner['owned_count'] and
            evidence['public_count'] == published_owner['public_count'] and
            Path(evidence['audit_plan']['path']).parent.name == published_owner['audit_id'] and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Cutoff@K full audit/count/source/full21 post-validation differs')
    spec.dependency_pins[module] = expected
    return owner


def fixed_dependency_pins(s, spec, module):
    policy = spec.manifest['fixed_dependencies'][module]
    stem = '.lake/build/lib/lean/' + module.replace('.', '/')
    if policy['kind'] == 'retained_accepted_normal_dependency_context':
        owner = retained_owner(s, spec, policy['witness_owner'])
        context = owner.normal['dependency_context']
        require(context['project_sources'].get(module) == spec.sources[module],
                'retained dependency source identity differs')
        return {stem + ext: context['dependency_objects_and_traces'][stem + ext] for ext in ('.olean', '.trace')}
    record = spec.observed['modules'][module]
    require(set(record['outputs']) <= {'.olean', '.trace', '.ilean', '.olean.private', '.olean.server'},
            'unexpected observed artifact extension')
    return {stem + ext: value for ext, value in record['outputs'].items()}


def environment(s, review):
    configuration = {p: regular_fingerprint(s, PROJECT / p) for p in review['runtime_configuration_bindings']}
    require(configuration == review['runtime_configuration_bindings'] and
            not os.path.lexists(PROJECT / 'lakefile.lean'), 'runtime configuration differs')
    runtime = s.d.runtime_binding(s.h)
    require(runtime == review['existing_runtime_bindings'], 'existing runtime binding differs')
    protected = {m: file_binding(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    require(protected == s.h.FOUR_ROOTS, 'protected original roots differ')
    return {'configuration': configuration, 'runtime': runtime, 'protected_roots': protected}


def snapshot(s, spec):
    result = environment(s, spec.review)
    sources = {m: file_binding(PROJECT / s.h.module_path(m)) for m in sorted(spec.active)}
    require(sources == {m: spec.sources[m] for m in sorted(spec.active)}, 'selected live source context differs')
    dependencies = {}
    for module, expected in sorted(spec.dependency_pins.items()):
        actual = module_artifacts(s, module)
        require(all(actual.get(path) == value for path, value in expected.items()),
                'PRESERVED_DEPENDENCY_PIN_DIFFERS: ' + module)
        dependencies[module] = actual
    retained = {path: regular_fingerprint(s, Path(path)) for path in spec.retained_inputs}
    require(retained == spec.retained_inputs, 'original retained acceptance evidence changed')
    result.update(selected_live_sources=sources, preserved_dependency_artifacts=dependencies,
                  retained_original_evidence=retained, committed_inputs=spec.input_bindings)
    return result


def preflight(s, commit, selected):
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source-commit must name a commit')
    executed = Path(__file__).read_bytes()
    require(executed == git_file(commit, RUNNER), 'executed runner differs from committed source')
    manifest, graph, sources, observed, inputs = source_manifest(s, commit, selected)
    active = s.h.closure(graph, selected)
    blocked = sorted(active & set(manifest['unaccepted_p3_dependencies']))
    require(not blocked, 'UNACCEPTED_P3_SUPPLIERS_REQUIRE_SEPARATE_ACCEPTANCE: ' + ', '.join(blocked))
    review_raw = pinned(commit, REVIEW, REVIEW_SHA)
    review = json.loads(review_raw)
    for path, expected in review['source_configuration_bindings'].items():
        raw = git_file(commit, path)
        require({'bytes': len(raw), 'sha256': s.api.sha(raw)} == expected, 'published configuration differs: ' + path)
    actual_graph, actual = s.h.project_graph(PROJECT, selected)
    require(actual_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in actual.items()} == {m: sources[m] for m in active},
            'selected installed source graph differs; source installation is separate')
    spec = SimpleNamespace(manifest=manifest, graph=graph, sources=sources, observed=observed,
        review=review, active=active, selected=set(selected), order=s.d.compile_order([], selected, graph),
        input_bindings={**inputs, 'runtime_review': {'path': REVIEW, 'bytes': len(review_raw), 'sha256': s.api.sha(review_raw)},
                        'runner': {'path': RUNNER, 'bytes': len(executed), 'sha256': s.api.sha(executed)}},
        retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})
    environment(s, review)
    for module in sorted(active & set(manifest['previously_accepted_targets'])):
        if module == PERGROUP_O_MODULE:
            retained_pergroup_o_target(s, spec, module)
        elif module == HB_F_MODULE:
            retained_hb_f_target(s, spec, module)
        elif module == LICENSED_M_MODULE:
            retained_licensed_m_target(s, spec, module)
        elif module == CUTOFF_K_MODULE:
            retained_cutoff_k_target(s, spec, module)
        else:
            retained_previous_target(s, spec, module)
    for module in sorted(active & set(manifest['accepted_suppliers'])):
        retained_owner(s, spec, module, validate_live=True)
        spec.dependency_pins[module] = module_artifacts(s, module)
    for module in sorted(active & set(manifest['fixed_dependencies'])):
        spec.dependency_pins[module] = fixed_dependency_pins(s, spec, module)
    active_targets = (active & set(TARGETS)) - set(manifest['previously_accepted_targets'])
    spec.initial_owners = {m: existing_owner(s, commit, spec, m) for m in sorted(active_targets)}
    for module in sorted(active_targets - set(selected)):
        require_completed_existing_owner(s, commit, spec, module, spec.initial_owners[module])
        spec.dependency_pins[module] = module_artifacts(s, module)
    require(set(spec.dependency_pins) == active - set(selected), 'selected dependency readiness inventory incomplete')
    spec.baseline = snapshot(s, spec)
    return spec


def worker(s, commit, selected, run):
    s.d.verify_lane(s.h)
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [], 'failures': {},
              'acceptance_bindings': {}, 'direct_import_readiness': {}, 'reused_complete_selected_owners': [],
              'whole_P1_complete': False, 'whole_P1_5_complete': False,
              'acceptance_class': 'SELECTED_CURRENT_P1_BRIDGES_AND_ORIGINAL_PROVIDERS',
              'accepted_supplier_recompile_requested': False, 'dependency_rebuild_requested': False,
              'old_receipts_rebound': False, 'old_P3_REUSE_changed': False}
    spec = None
    try:
        spec = preflight(s, commit, selected)
        result['targets'] = spec.order
        result['original_supplier_acceptance_bindings'] = spec.supplier_evidence
        result['published_source_count'] = len(spec.graph)
        result['selected_live_source_count'] = len(spec.active)
        s.d.save(run / 'CONTEXT_BEFORE.json', spec.baseline)
        s.d.save(run / 'COMMITTED_INPUT_BINDINGS.json', spec.input_bindings)
        for module in spec.order:
            require(snapshot(s, spec) == spec.baseline, 'source/runtime/preserved evidence context changed')
            other_owners = {m: module_artifacts(s, m) for m in TARGETS if m != module}
            try:
                state = spec.initial_owners[module]
                complete = (ROOT / commit / module / 'audits').is_dir() and any(
                    (ROOT / commit / module / 'audits').glob('*/lane-0/VALIDATION_RESULTS.json'))
                if complete:
                    require_completed_existing_owner(s, commit, spec, module, state)
                    result['reused_complete_selected_owners'].append(module)
                else:
                    result['direct_import_readiness'][module] = direct_import_readiness(s, spec, module, run)
                    require(snapshot(s, spec) == spec.baseline and
                            {m: module_artifacts(s, m) for m in other_owners} == other_owners,
                            'preserved dependency/other target changed during import readiness')
                    run_owner(s, commit, ROOT / commit, run, module, spec.graph, spec.sources)
                require(snapshot(s, spec) == spec.baseline and
                        {m: module_artifacts(s, m) for m in other_owners} == other_owners,
                        'preserved context or another owner changed during acceptance')
                result['acceptance_bindings'][module] = acceptance_binding(s, commit, module)
                result['accepted_owners'].append(module)
                s.ops.emit('CURRENT_CORRECTION_OWNER_ACCEPTED', module=module)
            except Exception as error:
                result['failures'][module] = str(error)
                s.ops.emit('CURRENT_CORRECTION_OWNER_HELD_OR_FAILED', module=module, reason=str(error))
                break
        if not result['failures']:
            before = {m: module_artifacts(s, m) for m in TARGETS}
            stock = s.ops.run(run, 'final-stock-readiness', s.h.guard(0, ['lake', '--no-build', 'build'] +
                             ['+' + m + ':olean' for m in spec.order]), cwd=PROJECT)
            require(stock['exit_code'] == 0 and stock['actual_built_modules'] == [] and
                    stock['actual_failed_modules'] == [], 'FINAL_STOCK_READINESS_FAILED_NO_REBUILD_ALLOWED')
            require({m: module_artifacts(s, m) for m in TARGETS} == before,
                    'target artifact changed during final stock readiness')
            result['final_stock_readiness'] = stock
    except Exception as error:
        result['context_error'] = str(error)
    finally:
        if spec is not None:
            try:
                after = snapshot(s, spec)
                s.d.save(run / 'CONTEXT_AFTER.json', after)
                require(after == spec.baseline, 'source/runtime/preserved evidence context changed')
            except Exception as error:
                result['final_context_error'] = str(error)
    s.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('context_error') or result.get('final_context_error')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--targets', nargs='+', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit, selected = args.source_commit, selection(args.targets)
    require(re.fullmatch('[0-9a-f]{40}', commit), 'source-commit requires a full lowercase SHA')
    s = helpers()
    if args.check:
        require(args.inside_lane is None, 'read-only check does not use a lane')
        spec = preflight(s, commit, selected)
        print(json.dumps({'status': 'PUBLISHED_SOURCES_AND_SELECTED_EXISTING_ACCEPTANCE_CONTEXT_VERIFIED',
            'source_commit': commit, 'targets': spec.order, 'published_source_count': len(spec.graph),
            'selected_live_source_count': len(spec.active), 'preserved_dependency_count': len(spec.dependency_pins),
            'original_supplier_acceptance_bindings': spec.supplier_evidence,
            'stock_readiness_performed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}))
        return 0
    base = ROOT / commit
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                'invalid correction worker directory')
        return worker(s, commit, selected, run)
    preflight(s, commit, selected)
    run = s.d.attempt(base / 'runs')
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [], 'failures': {},
              'whole_P1_complete': False, 'whole_P1_5_complete': False}
    try:
        s.d.save(run / 'GIT_BEFORE.json', s.d.original_git_state(REPO))
        executed = run / 'executed-driver.py'
        s.d.write_frozen(executed, Path(__file__).read_bytes())
        child = ['python3', '-B', str(executed), '--source-commit', commit, '--targets', *selected,
                 '--run', '--inside-lane', str(run)]
        command = s.ops.run(run, 'serialized-worker',
                           s.h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        if (run / 'WORKER_RESULT.json').is_file():
            result.update(s.api.read_json(run / 'WORKER_RESULT.json'))
        result['worker_exit_code'] = command['exit_code']
        require(command['exit_code'] == 0, 'serialized worker exited ' + str(command['exit_code']))
    except Exception as error:
        result['dispatch_error'] = str(error)
    finally:
        try:
            after = s.d.original_git_state(REPO)
            s.d.save(run / 'GIT_AFTER.json', after)
            require(after == s.api.read_json(run / 'GIT_BEFORE.json'), 'original dirty Git state changed')
        except Exception as error:
            result['git_error'] = str(error)
    success = (set(result['accepted_owners']) == set(selected) and not result['failures'] and
               not any(key in result for key in ('context_error', 'final_context_error', 'dispatch_error', 'git_error')))
    result['all_selected_owners_accepted'] = success
    s.d.save(run / 'RESULT.json', result)
    s.ops.emit('P15_CURRENT_CORRECTIONS_RESULT', path=str(run / 'RESULT.json'), **result)
    return int(not success)


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    raise SystemExit(main())
