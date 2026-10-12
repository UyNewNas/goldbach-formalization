#!/usr/bin/env python3
"""Rebuild P0 round-3 intake ledger by reading fixed evidence; never runs Lean/CI.

Inputs are parameterized. A local Git repository is used only for `git show`
and `git diff` of the already fetched immutable commits. Existing receipts are
copied or linked; this program performs no new proof verification.
"""
from __future__ import annotations

import argparse
import collections
import copy
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


BASE = '1a80c1bcce67886f699d097fc37fd245cd3620bf'
MANUSCRIPT = 'ba6ec11d800eccc54406490631895e174de85766'
PREVIOUS_P0 = '80aca6710c83b5160f4c5fdd05d180e507990e95'
CCE = 'cce2334906f068fda2f58c400646366f2aa2d417'
ALLOWLIST = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--round-root', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--previous-ledger', type=Path)
    parser.add_argument('--git-repo', type=Path)
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    root = args.round_root.resolve()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    previous = (args.previous_ledger or root / 'previous-ledger/ledger-delivery/module-ledger.json').resolve()
    repo = (args.git_repo or root.parent / 'goldbach-formalization').resolve()
    generated = dt.datetime.now(dt.timezone.utc).isoformat()
    inputs = {}

    publication_ledger = repo / 'verification/parts/p0/round3/ledger'
    publication_root = publication_ledger.parent
    publication_map = {}

    def published_path(path):
        path = Path(path).resolve()
        if path.is_relative_to(out):
            return publication_ledger / path.relative_to(out)
        if path.is_relative_to(previous.parent):
            return publication_ledger / 'history/round2/ledger-delivery' / path.relative_to(previous.parent)
        cce_source = root / 'context/cce-artifact'
        if path.is_relative_to(cce_source):
            return publication_root / 'prior-ci/cce-core' / path.relative_to(cce_source)
        for source_dir in ['p2-p4-intake/p2/fixed', 'p3-intake/fixed', 'p1-intake/fixed-source']:
            source_root = root / source_dir
            if path.is_relative_to(source_root / 'verification'):
                destination = repo / path.relative_to(source_root)
                if path.is_file() and destination.is_file() and digest(path.read_bytes()) != digest(destination.read_bytes()):
                    # Keep raw producer evidence separate from P0's published
                    # derivative; never overwrite a different target receipt.
                    return publication_root / 'intake' / path.relative_to(root)
                return destination
        for intake in ['p1-intake', 'p2-p4-intake', 'p3-intake', 'p5-intake']:
            source_root = root / intake
            if path.is_relative_to(source_root):
                return publication_root / 'intake' / intake / path.relative_to(source_root)
        return publication_root / path.relative_to(root)

    def published_rel(path):
        return os.path.relpath(published_path(path), publication_ledger)

    def ref(path):
        path = Path(path).resolve()
        target = published_path(path)
        if not path.is_relative_to(out):
            publication_map[str(target)] = str(path)
        return {'path': published_rel(path), 'sha256': digest(path.read_bytes()), 'bytes': path.stat().st_size}

    def input_json(rel):
        path = root / rel
        value = read_json(path)
        inputs[rel] = ref(path)
        return value

    def fixed_git(commit, path):
        return subprocess.run(['git', '-C', str(repo), 'show', f'{commit}:{path}'],
                              capture_output=True, check=True).stdout

    def snapshot(data, path, expected_sha, expected_blob=None, prefix='snapshot-sources'):
        assert digest(data) == expected_sha, (path, digest(data), expected_sha)
        if expected_blob:
            assert blob(data) == expected_blob, (path, blob(data), expected_blob)
        target = out / prefix / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        return ref(target)

    old = read_json(previous)
    inputs['previous_ledger'] = ref(previous)
    assert old['proof_baseline'] == BASE and old['manuscript_baseline'] == MANUSCRIPT
    assert len(old['modules']) == 28
    p1 = input_json('p1-intake/P1_RECEIPT_REUSE.json')
    p24 = input_json('p2-p4-intake/INTAKE.json')
    p2, p4 = copy.deepcopy(p24['p2']), copy.deepcopy(p24['p4'])
    p2['dedicated_ci']['raw_log'] = published_rel(root / 'p2-p4-intake' / p2['dedicated_ci']['raw_log'])
    p3 = input_json('p3-intake/P3_RECEIPT_REUSE.json')
    p5 = input_json('p5-intake/p5-fixed-intake.json')
    live = input_json('p1-intake/LIVE_FIFTH_CANDIDATES.json')
    p1_diagnostics = input_json('p1-intake/FIRST_DIAGNOSTICS.json')
    p1_types = input_json('p1-intake/compiler-pretty-types.json')
    p5_types = input_json('p5-intake/key-compiler-types.json')
    p1_manifest = input_json('p1-intake/fixed-source-manifest.json')
    p5_manifest = input_json('p5-intake/fixed-source-manifest.json')
    prefix = root / 'p2-p4-intake/p2/fixed/verification/part2/round2/prefix4'
    p2_receipt = input_json(str((prefix / 'receipt.json').relative_to(root)))
    p2_types = input_json(str((prefix / 'compiler-types.json').relative_to(root)))
    old_types = read_json(previous.parent / 'compiler-declarations.json')
    inputs['previous_compiler_declarations'] = ref(previous.parent / 'compiler-declarations.json')

    # Preserve the previous ledger AND its companion evidence byte-for-byte.
    history_root = out / 'history/round2/ledger-delivery'
    shutil.copytree(previous.parent, history_root, dirs_exist_ok=True)
    assert (history_root / previous.name).read_bytes() == previous.read_bytes()
    preserved_history = ref(history_root / previous.name)

    def old_log_ref(attempt):
        item = attempt.get('log_snapshot') or {}
        rel = item.get('snapshot_path')
        if rel:
            path = out / 'history/round2' / rel
            if path.is_file():
                result = ref(path)
                assert result['sha256'] == item['sha256']
                return result
        return None

    def old_gate(gate, status):
        attempts = gate.get('completed_matching_attempts', [])
        summaries = []
        for a in attempts:
            summary = {k: a[k] for k in (
                'action', 'module', 'returncode', 'elapsed_seconds', 'started_utc',
                'source_sha256_before', 'source_sha256_after', 'olean_sha256',
                'target_olean_sha256_before', 'trustLevel', 'strict', 'metadata_adapter',
                'stable_source_and_recorded_imports', 'first_real_diagnostic',
                'first_real_diagnostic_block') if k in a}
            summary['raw_log'] = old_log_ref(a)
            summaries.append(summary)
        return {'status': status, 'record_kind': 'REUSED_PREVIOUS_VERSION_EVIDENCE',
                'matching_attempts': summaries, 'receipt': preserved_history}

    def owned_types(records, module, explicit):
        selected = [copy.deepcopy(x) for x in records if x['module'] == module]
        for x in selected:
            assert set(x.get('axioms', [])) <= ALLOWLIST, (module, x['name'], x.get('axioms'))
            x['compiler_confirmation'] = 'REUSED_COMPILER_RECORD'
            x['display_kind'] = 'PP_ALL' if explicit else 'DEFAULT_PRETTY'
            x['contains_omission_marker'] = any(s in x['type'] for s in ('⋯', '…'))
            if explicit:
                assert not x['contains_omission_marker'], x['name']
        return selected

    compiler_inventory = []
    modules = []
    by_module = {}
    old_by_module = {m['module']: m for m in old['modules']}
    latest = {'p1': p1['source_commit'], 'p2': p2['handoff_commit'],
              'p3': p3['fixed_submission'], 'p4': p4['latest_fixed_commit'],
              'p5': p5['fixed_handoff'], 'P0': CCE, 'p0': CCE}

    # The 28 old entries stay in their original order; source-history records
    # retain old compile failures even when current sources are changed.
    for om in old['modules']:
        cm = om['current_source']
        src = previous.parent.parent / cm['snapshot']['snapshot_path']
        if not src.is_file():
            src = previous.parent / 'snapshot-sources' / om['source_part'] / om['path']
        data = src.read_bytes()
        accepted = bool(om['integration_acceptance']['accepted'])
        object_hash = None
        for a in om['validation']['compile'].get('completed_matching_attempts', []):
            if a.get('returncode') == 0:
                object_hash = a.get('olean_sha256') or object_hash
        ts = owned_types(old_types, om['module'], True) if accepted else []
        m = {
            'module': om['module'], 'repository_path': om['path'],
            'part_owner': om['part_owner'], 'source_part': om['source_part'],
            'source': {'fixed_commit': cm['source_fixed_commit'],
                       'latest_fixed_handoff': latest[om['source_part']],
                       'sha256': cm['source_sha256'], 'git_blob_sha1': cm['git_blob_sha1'],
                       'snapshot': snapshot(data, om['path'], cm['source_sha256'], cm['git_blob_sha1'])},
            'compiled_object_sha256': object_hash,
            'validation': {
                'compile': old_gate(om['validation']['compile'], om['validation']['compile']['status']),
                'kernel_replay': old_gate(om['validation']['kernel_replay'], om['validation']['kernel_replay']['status']),
                'axiom_audit': {'status': om['validation']['axioms']['status'],
                                'receipt': preserved_history,
                                'owned_declaration_count': len(ts) if accepted else None}},
            'component_acceptance': {'accepted': accepted,
                                     'status': 'PREVIOUSLY_ACCEPTED_EXACT_SOURCE' if accepted else 'CANDIDATE',
                                     'accepted_in_previous_P0_production': accepted,
                                     'previous_acceptance_commit': om['integration_acceptance'].get('commit'),
                                     'new_integration_commit': None,
                                     'new_integration_root_validation': 'PENDING'},
            'declarations': {'owned_audited': len(ts) if accepted else None,
                             'compiler_pp_all': len(ts), 'compiler_default_pretty': 0,
                             'default_pretty_without_omission_marker': 0,
                             'default_pretty_with_omission_marker': 0,
                             'source_extracted_theorem_heads': om['types']['source_extracted_count'],
                             'inventory': 'compiler-declarations.json' if accepted else None},
            'direct_imports': om.get('direct_imports', []),
            'receiving_parts': om.get('receiving_parts', []),
            'unclosed_real_inputs': copy.deepcopy(om.get('unclosed_inputs', [])),
            'outstanding_validation_gates': copy.deepcopy(om.get('outstanding_validation_gates', [])),
            'version_history': [{
                'fixed_commit': cm['source_fixed_commit'], 'source_sha256': cm['source_sha256'],
                'compile_status_at_previous_snapshot': om['validation']['compile']['status'],
                'replay_status_at_previous_snapshot': om['validation']['kernel_replay']['status'],
                'audit_status_at_previous_snapshot': om['validation']['axioms']['status'],
                'original_module_record': {'receipt': preserved_history, 'module_key': om['module']},
                'all_prior_attempts_and_failures_preserved': True}],
            'receipt_links': [preserved_history],
        }
        for x in ts:
            x['production_source_sha256'] = cm['source_sha256']
            x['source_fixed_commit'] = cm['source_fixed_commit']
        compiler_inventory.extend(ts)
        modules.append(m)
        by_module[m['module']] = m

    # P1 four production modules: audit owns 140; the 10 probe declarations
    # belong to a verification module and never enter production totals.
    p1_audit = next(m for m in p1['modules'] if m['role'] == 'audit execution')
    p1_modules = [m for m in p1['modules'] if m['module'].startswith('ImbalancedChen.')]
    assert len(p1_modules) == 4
    p1_open = [
        '采用的 cell/cap/mask 字典、真实积分数值证书与 row 绑定尚待供应。',
        '每 cell 的整盒许可、完整覆盖和不重计尚待与实际采用表接合。',
        '同一 boxed physical rho 的身份、支持、因式分解、分布及 compiler 误差尚未闭合。',
        '完整历史第五/第六/第八积分、截断误差和全局 K 尚待提供。',
        '完整十一项采用均值、真实 c、hLower、hUpper 尚无实际供应者。',
    ]
    for pm in p1_modules:
        assert pm['strict_compile_exit_code'] == pm['original_replay_exit_code'] == 0
        m = by_module[pm['module']]
        data = (root / 'p1-intake/fixed-source' / pm['repository_path']).read_bytes()
        m['source'] = {'fixed_commit': p1['source_commit'],
                       'latest_fixed_handoff': '7f894bfb57b7aa561360e335c6d610b7c30614e0',
                       'sha256': pm['source_sha256'], 'git_blob_sha1': pm['source_git_blob_sha1'],
                       'snapshot': snapshot(data, pm['repository_path'], pm['source_sha256'], pm['source_git_blob_sha1'])}
        m['compiled_object_sha256'] = pm['main_olean_sha256']
        common = {'receipt': ref(root / 'p1-intake/P1_RECEIPT_REUSE.json'),
                  'record_kind': 'REUSED_PRODUCER_RAW_RECORD_EXACT_SOURCE_AND_OBJECT',
                  'source_sha256': pm['source_sha256'], 'object_sha256': pm['main_olean_sha256']}
        m['validation'] = {
            'compile': dict(common, status='PASS_STRICT_TRUST0', exit_code=0,
                            elapsed_seconds=pm['strict_compile_elapsed_seconds'],
                            raw_log_sha256=pm['compile_log_sha256']),
            'kernel_replay': dict(common, status='PASS_ORIGINAL_LEANCHECKER', exit_code=0,
                                  elapsed_seconds=pm['original_replay_elapsed_seconds'],
                                  raw_log_sha256=pm['replay_log_sha256']),
            'axiom_audit': dict(common, status='PASS_EXACT_OBJECT_ALL_OWNED_DECLARATIONS',
                                exit_code=p1_audit['strict_compile_exit_code'],
                                elapsed_seconds=p1_audit['strict_compile_elapsed_seconds'],
                                audit_module=p1_audit['module'],
                                audit_object_sha256=p1_audit['main_olean_sha256'],
                                raw_log_sha256=p1_audit['compile_log_sha256'],
                                import_binding_verified=p1['audit_declaring_modules_and_objects_bound'],
                                audit_module_replay_exit_code=p1_audit['original_replay_exit_code'],
                                owned_declaration_count=pm['audited_defining_module_declarations'])}
        ts = owned_types(p1_types, pm['module'], False)
        elided = sum(x['contains_omission_marker'] for x in ts)
        assert len(ts) == pm['audited_defining_module_declarations']
        m['declarations'].update(owned_audited=len(ts), compiler_pp_all=0,
                                 compiler_default_pretty=len(ts),
                                 default_pretty_without_omission_marker=len(ts)-elided,
                                 default_pretty_with_omission_marker=elided,
                                 inventory='compiler-declarations.json',
                                 explicit_complete_type_supplement='PENDING_NEW_P0_FIXED_SHA_CI')
        m['component_acceptance'].update(accepted=True, status='RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA')
        m['outstanding_validation_gates'] = []
        m['unclosed_real_inputs'] = p1_open
        m['receipt_links'].append(common['receipt'])
        for x in ts:
            x['source_fixed_commit'] = p1['source_commit']
            x['production_source_sha256'] = pm['source_sha256']
        compiler_inventory.extend(ts)

    # P3: all seven fixed source blobs match the previous source bytes;
    # only LongSlotNormalization gains three gates in this intake.
    for m in modules:
        if m['source_part'] == 'p3':
            data = fixed_git(p3['fixed_submission'], m['repository_path'])
            assert digest(data) == m['source']['sha256']
            m['source']['latest_fixed_handoff_byte_identity_checked'] = True
            m['source']['snapshot'] = snapshot(data, m['repository_path'], m['source']['sha256'])
    m = by_module[p3['target']]
    m['source']['fixed_commit'] = p3['fixed_submission']
    m['compiled_object_sha256'] = p3['object_sha256']
    m['validation'] = {}
    for gate, name in [('compile','compile'), ('replay','kernel_replay'), ('audit','axiom_audit')]:
        g = copy.deepcopy(p3['gates'][gate])
        assert g['returncode'] == 0 and g['source_and_target_match']
        g.update(status='PASS_REUSED_EXACT_SOURCE_AND_OBJECT',
                 receipt=ref(root / 'p3-intake/P3_RECEIPT_REUSE.json'),
                 source_sha256=p3['source_sha256'], object_sha256=p3['object_sha256'])
        m['validation'][name] = g
    m['validation']['axiom_audit']['owned_declaration_count'] = 2
    ts = owned_types(p3['compiler_declarations'], m['module'], True)
    assert len(ts) == 2
    m['declarations'].update(owned_audited=2, compiler_pp_all=2, inventory='compiler-declarations.json')
    m['component_acceptance'].update(accepted=True, status='RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA')
    m['outstanding_validation_gates'] = []
    m['unclosed_real_inputs'] = [
        '归一化转移仍需其真实前提；物理 MD ≤ N^theta 不是本模块的新结论。',
        'rough-prime / long-slot 分布、长区间、Brun–Mellin 及 medium/two-long 的全部算术供应尚待闭合。',
        '本模块不供应同一实际 rho 的 K 密度界或 hUpper/hLower。']
    m['receipt_links'].append(ref(root / 'p3-intake/P3_RECEIPT_REUSE.json'))
    m['version_history'].append({'source_unchanged_from_old_7d': p3['old_7d_source_unchanged'],
                                 'producer_prior_attempts': p3['prior_actual_attempts']})
    for x in ts:
        x.update(source_fixed_commit=p3['fixed_submission'], production_source_sha256=p3['source_sha256'])
    compiler_inventory.extend(ts)

    # Existing P2 modules preserve their accepted object lineage. The current
    # fixed P2 sources and dedicated nine-module CI provide additional evidence.
    for same in p2['previously_accepted_source_comparison']:
        m = by_module[same['module']]
        data = (root / 'p2-p4-intake/p2/fixed' / m['repository_path']).read_bytes()
        assert same['source_sha256'] == m['source']['sha256'] == digest(data)
        m['source']['latest_fixed_handoff_byte_identity_checked'] = True
        m['additional_same_source_verification'] = p2['dedicated_ci']
        m['unclosed_real_inputs'] = copy.deepcopy(p2['open_inputs'])
        m['receipt_links'].append(ref(root / 'p2-p4-intake/INTAKE.json'))
    for pm in p2['new_ready_modules']:
        assert pm['recommended_acceptance']
        data = (root / 'p2-p4-intake/p2/fixed' / pm['source']).read_bytes()
        ts = owned_types(p2_types, pm['module'], True)
        assert len(ts) == pm['owned_declarations']
        val = {}
        for gate, name in [('compile','compile'), ('replay','kernel_replay')]:
            g = copy.deepcopy(pm['gates'][gate])
            assert g['exit_code'] == 0
            g['receipt'] = ref(root / 'p2-p4-intake' / g['receipt'])
            g['raw_log'] = ref(root / 'p2-p4-intake' / g.pop('log'))
            g.update(source_sha256=pm['source_sha256'], object_sha256=pm['olean_sha256'])
            val[name] = g
        audit = copy.deepcopy(p2_receipt['audit']['compile'])
        audit['receipt'] = ref(prefix / audit['receipt'])
        audit['raw_log'] = ref(prefix / audit.pop('log'))
        audit.update(status=pm['audit_status'], audit_module=p2_receipt['audit']['module'],
                     audit_object_sha256=p2_receipt['audit']['object_sha256'],
                     owned_declaration_count=len(ts), object_sha256=pm['olean_sha256'],
                     source_sha256=pm['source_sha256'], all_private_and_generated=True)
        val['axiom_audit'] = audit
        m = {
            'module': pm['module'], 'repository_path': pm['source'], 'part_owner': 'P2', 'source_part': 'p2',
            'source': {'fixed_commit': p2['proof_commit'], 'latest_fixed_handoff': p2['handoff_commit'],
                       'sha256': pm['source_sha256'], 'git_blob_sha1': pm['git_blob_sha1'],
                       'snapshot': snapshot(data, pm['source'], pm['source_sha256'], pm['git_blob_sha1'])},
            'compiled_object_sha256': pm['olean_sha256'], 'validation': val,
            'component_acceptance': {'accepted': True, 'status': 'RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA',
                                     'accepted_in_previous_P0_production': False, 'previous_acceptance_commit': None,
                                     'new_integration_commit': None, 'new_integration_root_validation': 'PENDING'},
            'declarations': {'owned_audited': len(ts), 'compiler_pp_all': len(ts), 'compiler_default_pretty': 0,
                             'default_pretty_without_omission_marker': 0, 'default_pretty_with_omission_marker': 0,
                             'source_extracted_theorem_heads': None, 'inventory': 'compiler-declarations.json'},
            'direct_imports': re.findall(r'^import\s+(\S+)', data.decode(), re.M),
            'receiving_parts': pm['receivers'], 'unclosed_real_inputs': copy.deepcopy(p2['open_inputs']),
            'outstanding_validation_gates': [],
            'version_history': [{'producer_repair_attempts': published_rel(prefix / 'attempts'),
                                 'past_failed_attempts_are_not_current_source_failures': True}],
            'receipt_links': [ref(root / 'p2-p4-intake/INTAKE.json'), ref(prefix / 'receipt.json')],
            'additional_same_source_verification': copy.deepcopy(p2['dedicated_ci']),
            'certified_scope': copy.deepcopy(p2['scope']),
        }
        modules.append(m)
        by_module[m['module']] = m
        for x in ts:
            x.update(source_fixed_commit=p2['proof_commit'], production_source_sha256=pm['source_sha256'])
        compiler_inventory.extend(ts)

    # P4 targets were never reached. Preserve timeout distinctly from Lean errors.
    for m in modules:
        if m['source_part'] == 'p4':
            data = (root / 'p2-p4-intake/p4/fixed' / m['repository_path']).read_bytes()
            assert digest(data) == m['source']['sha256']
            m['source']['latest_fixed_handoff_byte_identity_checked'] = True
            m['ci_receipt'] = p4['ci_receipt']
            m['unclosed_real_inputs'] = copy.deepcopy(p4['open_inputs'])
            m['outstanding_validation_gates'] = ['explicit_production_compile', 'strict_trust0_compile',
                                                  'original_kernel_replay', 'all_owned_axiom_audit']
            for name in ['compile', 'kernel_replay', 'axiom_audit']:
                m['validation'][name] = {'status': 'NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT',
                                        'target_completion_count': 0,
                                        'first_real_lean_diagnostic': None,
                                        'receipt': ref(root / 'p2-p4-intake/INTAKE.json')}
            m['receipt_links'].append(ref(root / 'p2-p4-intake/INTAKE.json'))

    # Fixed P5 repair: new source owns its producer successes; old failure remains
    # in immutable history. Missing legacy import binding prevents acceptance.
    for same in p5['previously_accepted_production_unchanged']:
        m = next(m for m in modules if m['repository_path'] == same['path'])
        assert m['source']['sha256'] == same['sha256']
        m['source']['latest_fixed_handoff_byte_identity_checked'] = True
        m['unclosed_real_inputs'] = copy.deepcopy(p5['remaining_inputs'])
        m['receipt_links'].append(ref(root / 'p5-intake/p5-fixed-intake.json'))
    p5_source = {x['path']: x for x in p5_manifest}
    initial = p5['initial_source']
    for name, accepted_status in [('ImbalancedChen.CurrentChenInitialSource','CANDIDATE_LEGACY_AUDIT_IMPORT_BINDING_PENDING'),
                                  ('ImbalancedChen.CurrentChenInitialMean','SOURCE_CANDIDATE_NOT_LEAN_VERIFIED')]:
        m = by_module[name]
        ident = p5_source[m['repository_path']]
        data = (root / 'p5-intake/fixed-source' / p5['fixed_handoff'] / m['repository_path']).read_bytes()
        m['source'] = {'fixed_commit': p5['fixed_handoff'], 'latest_fixed_handoff': p5['fixed_handoff'],
                       'sha256': ident['sha256'], 'git_blob_sha1': ident['git_blob_sha1'],
                       'snapshot': snapshot(data, m['repository_path'], ident['sha256'], ident['git_blob_sha1'])}
        m['component_acceptance']['status'] = accepted_status
        m['receipt_links'].append(ref(root / 'p5-intake/p5-fixed-intake.json'))
        m['unclosed_real_inputs'] = copy.deepcopy(p5['remaining_inputs'])
        if name.endswith('InitialSource'):
            m['source']['first_fixed_source_commit'] = initial['source_identity']['fixed_source_first_commit']
            m['compiled_object_sha256'] = initial['source_identity']['current_object']['expected_sha256']
            m['validation'] = {}
            for g in initial['gates']:
                name2 = {'compilation':'compile','kernel_replay':'kernel_replay','axiom_audit':'axiom_audit'}[g['gate']]
                current = copy.deepcopy(g)
                assert current['returncode'] == 0
                current.update(status='PRODUCER_PASS_LEGACY_BINDING_INCOMPLETE',
                               receipt=ref(root / 'p5-intake/p5-fixed-intake.json'))
                m['validation'][name2] = current
            m['validation']['axiom_audit']['owned_declaration_count'] = 8
            m['declarations'].update(owned_audited=8, compiler_default_pretty=8,
                                     default_pretty_without_omission_marker=8,
                                     inventory='candidate-compiler-declarations.json')
            m['outstanding_validation_gates'] = ['P0_exact_import_bound_owned_audit',
                                                  'full_replay_target_lineage_binding_for_legacy_schema']
            m['unclosed_real_inputs'].insert(0, initial['gap'])
            m['version_history'].append({'fixed_source_first_commit': initial['source_identity']['fixed_source_first_commit'],
                                         'old_source_sha256': old_by_module[m['module']]['current_source']['source_sha256'],
                                         'old_first_real_lean_diagnostic': initial['first_diagnostic'],
                                         'current_source_producer_all_three_pass': True,
                                         'public_theorem_headers_changed': False})
        else:
            m['compiled_object_sha256'] = None
            m['validation'] = {x: {'status': 'NOT_RECORDED_CURRENT_FIXED_SOURCE',
                                   'receipt': ref(root / 'p5-intake/p5-fixed-intake.json')}
                               for x in ['compile','kernel_replay','axiom_audit']}
            m['outstanding_validation_gates'] = ['compile_supplier_closure', 'strict_trust0_compile',
                                                  'original_kernel_replay', 'all_owned_axiom_audit']
            m['source_extracted_key_type'] = p5['initial_mean']['declaration']
            m['source_extracted_key_type_compiler_confirmed'] = False
            m['source_supplier'] = p5['initial_mean']['supplier']
            m['unclosed_real_inputs'].insert(0, '固定 S1BetaFixedNormalizedLower 供应链及当前 InitialMean 源尚无完成的匹配验证。')

    # Capture the actual first frontend diagnostics. The upstream intake JSON
    # mistakenly truncated each to '/'; keep that original field unchanged in
    # its receipt and record the extraction correction only here.
    corrections = []
    for entry in p1_diagnostics['first_diagnostics']:
        path = root / 'p1-intake' / entry['raw_log']
        data = path.read_bytes()
        assert digest(data) == entry['raw_log_sha256']
        lines = data.decode().splitlines()
        ix = next(i for i,l in enumerate(lines) if re.search(r'\.lean:\d+:\d+: error:', l))
        end = next((j for j in range(ix+1, len(lines))
                    if re.search(r'\.lean:\d+:\d+: (?:error|warning):|^FRONTEND_', lines[j])), len(lines))
        block = '\n'.join(lines[ix:end]).rstrip()
        corrections.append({'module': entry['module'], 'attempt': entry['attempt'],
                            'source_sha256': entry['source_sha256'], 'exit_code': entry['exit_code'],
                            'original_mistruncated_field': entry['diagnostic'],
                            'original_field_source': ref(root / 'p1-intake/FIRST_DIAGNOSTICS.json'),
                            'raw_log': ref(path), 'correct_first_diagnostic_line': lines[ix],
                            'correct_first_diagnostic_block': block,
                            'interpretation': 'INTAKE_EXTRACTION_CORRECTION_OF_HISTORICAL_FAILURE;_NO_NEW_PRODUCTION_PROOF_FAILURE',
                            'new_Lean_execution': False})
    write_json(out / 'CORRECTED_INTAKE_DIAGNOSTICS.json',
               {'schema': 'chen-p0-round3-corrected-intake-diagnostics-v1', 'recorded_utc': generated,
                'source_receipt_unchanged': True, 'corrections': corrections})

    # Separate upstream S1Carrier and unfixed fifth-layer work, never in 31/19.
    upstream = copy.deepcopy(p5['s1carrier'])
    upstream.update(counted_in_fixed_production_modules=False, counted_in_accepted_owned_declarations=False,
                    verification_reuse_status='UPSTREAM_COMPONENT_THREE_GATES_REUSED',
                    receipt=ref(root / 'p5-intake/p5-fixed-intake.json'),
                    compiler_types='upstream-S1Carrier-types.json',
                    first_interruption=copy.deepcopy(p5['prior_s1carrier_interruption']))
    write_json(out / 'upstream-S1Carrier-types.json',
               {'source_identity': upstream['source_identity'], 'owned_default': p5_types['s1carrier_owned_default'],
                'public_pp_all_and_expr': p5_types['s1carrier_public_explicit'],
                'owned_audited_count': 36, 'complete_public_types_count': 17,
                'all_36_full_explicit_types_claimed': False})
    candidate_types = owned_types(p5_types['initial_source'], 'ImbalancedChen.CurrentChenInitialSource', False)
    write_json(out / 'candidate-compiler-declarations.json', candidate_types)
    fifth = copy.deepcopy(live)
    fifth['counted_in_fixed_production_modules'] = False
    fifth['counted_in_accepted_owned_declarations'] = False
    fifth['receipt'] = ref(root / 'p1-intake/LIVE_FIFTH_CANDIDATES.json')
    for entry in fifth['files']:
        copied = root / 'p1-intake/live-candidates/20261012T120742Z' / entry['path']
        entry['ledger_source_snapshot'] = snapshot(copied.read_bytes(), entry['path'],
                                                   entry['source_sha256'], prefix='unfixed-candidate-sources')
    assert len(fifth['files']) == 2

    # Exact existing CCE root evidence, not the future integration root.
    cce_dir = root / 'context/cce-artifact'
    provenance = (cce_dir / 'provenance.log').read_text()
    outcomes = (cce_dir / 'outcomes.log').read_text()
    build_log = (cce_dir / 'build.log').read_text()
    audit_log = (cce_dir / 'axiom-audit.log').read_text()
    assert f'project_commit={CCE}' in provenance
    assert all(x+'=success' in outcomes for x in ['build','leanchecker','axiom-audit'])
    assert 'Build completed successfully (9790 jobs).' in build_log
    assert "audited 5260 declaration(s) under 'ImbalancedChen'" in audit_log
    diff = subprocess.run(['git', '-C', str(repo), 'diff', '--name-only', PREVIOUS_P0, CCE],
                          capture_output=True, check=True, text=True).stdout.splitlines()
    assert diff == ['.github/workflows/lean.yml'], diff
    workflow_diff = subprocess.run(['git', '-C', str(repo), 'diff', PREVIOUS_P0, CCE, '--', '.github/workflows/lean.yml'],
                                   capture_output=True, check=True, text=True).stdout
    assert '+    timeout-minutes: 150' in workflow_diff and '+        timeout-minutes: 90' in workflow_diff
    old_root = {
        'exact_integration_commit': CCE, 'same_production_as': PREVIOUS_P0,
        'only_changed_path': diff[0], 'CI_job_timeout_minutes': 150, 'CI_build_timeout_minutes': 90,
        'run_id': 38227766990, 'attempt': 1,
        'full_build': {'status':'PASS', 'jobs':9790, 'elapsed_seconds':3226},
        'root_kernel_replay': {'status':'PASS', 'elapsed_seconds':506},
        'root_axiom_audit': {'status':'PASS', 'owned_namespace_declarations':5260,
                             'elapsed_seconds':31, 'allowlist':sorted(ALLOWLIST)},
        'raw_artifact_files': {p.name:ref(p) for p in sorted(cce_dir.iterdir()) if p.is_file()},
        'scope': 'Existing CCE root and its imported closure only; not the eight newly accepted leaves or future integration SHA.',
        'must_not_transfer_to_new_integration_SHA': True,
    }

    # Pin verification is source reading of CCE files, with no toolchain launch.
    protected = []
    for entry in old['toolchain']['config_files']:
        data = fixed_git(CCE, entry['path'])
        assert digest(data) == entry['sha256']
        protected.append({'path':entry['path'], 'sha256':entry['sha256'],
                          'git_blob_sha1':blob(data), 'checked_fixed_commit':CCE,
                          'snapshot':snapshot(data, entry['path'], entry['sha256'], prefix='protected-config')})
    toolchain = {'pin':old['toolchain']['pin'], 'githash':old['toolchain']['githash'],
                 'dependency_pins':old['toolchain']['dependency_pins'], 'protected_config':protected,
                 'all_pins_unchanged':True, 'historical_runtime_details_in_preserved_ledger':preserved_history}

    accepted = [m for m in modules if m['component_acceptance']['accepted']]
    new_accepted = [m for m in accepted if not m['component_acceptance']['accepted_in_previous_P0_production']]
    counts = {
        'fixed_production_modules':len(modules), 'component_accepted_modules':len(accepted),
        'not_fully_accepted_modules':len(modules)-len(accepted), 'previously_accepted_modules':len(accepted)-len(new_accepted),
        'new_component_accepted_modules':len(new_accepted),
        'new_component_owned_audited_declarations':sum(m['declarations']['owned_audited'] for m in new_accepted),
        'accepted_owned_audited_declarations':sum(m['declarations']['owned_audited'] for m in accepted),
        'accepted_complete_explicit_pp_all_declarations':sum(m['declarations']['compiler_pp_all'] for m in accepted),
        'accepted_default_pretty_declarations':sum(m['declarations']['compiler_default_pretty'] for m in accepted),
        'accepted_default_pretty_without_omission_marker':sum(m['declarations']['default_pretty_without_omission_marker'] for m in accepted),
        'accepted_default_pretty_with_omission_marker':sum(m['declarations']['default_pretty_with_omission_marker'] for m in accepted),
        'P1_new_owned_audited':140, 'P1_pp_all_executed':0,
        'P2_new_owned_audited':56, 'P3_new_owned_audited':2,
        'separate_upstream_modules':1, 'separate_upstream_owned_audited':36,
        'separate_upstream_complete_public_types':17, 'separate_unfixed_fifth_candidates':2,
        'separate_initial_source_candidate_owned_audited':8,
    }
    expected = {'fixed_production_modules':31,'component_accepted_modules':19,'not_fully_accepted_modules':12,
                'previously_accepted_modules':11,'new_component_accepted_modules':8,
                'new_component_owned_audited_declarations':198,'accepted_owned_audited_declarations':591,
                'accepted_complete_explicit_pp_all_declarations':451,'accepted_default_pretty_declarations':140,
                'accepted_default_pretty_without_omission_marker':133,'accepted_default_pretty_with_omission_marker':7}
    assert all(counts[k] == v for k,v in expected.items()), counts
    assert len(compiler_inventory) == 591
    assert len({(x['module'],x['name']) for x in compiler_inventory}) == 591
    assert sum(x['display_kind'] == 'PP_ALL' for x in compiler_inventory) == 451
    for m in modules:
        assert len(m['source']['fixed_commit']) == 40
        assert len(m['source']['sha256']) == 64
        assert m['source']['snapshot']['sha256'] == m['source']['sha256']
    compiler_inventory.sort(key=lambda x:(x['module'], x['name']))
    write_json(out / 'compiler-declarations.json', compiler_inventory)

    certificate = copy.deepcopy(old['certificate_version'])
    certificate['current_round3_scope'] = copy.deepcopy(p2['scope'])
    certificate['current_round3_actual_certificate'] = {
        'proof_commit':p2['proof_commit'], 'handoff_commit':p2['handoff_commit'],
        'adopted_corpus_source_sha256':p2['adopted_data']['source_sha256'],
        'original_zero_based_ordinals':[0,1,2,3], 'group':'E0',
        'finite_integral_sum_lower':p2['scope']['lower'], 'finite_integral_sum_upper':p2['scope']['upper'],
        'full_17572_rows_and_E1_and_error_ledger_certified':False,
        'K_over_80_already_contains_gain':True,
        'K_over_80_identity':'(1 / 20) * (K / 4) = K / 80; do not apply a second gain.'}
    certificate['previous_certificate_description_is_historical'] = True
    ledger = {
        'schema':'chen-p0-round3-component-ledger-candidate-v1', 'generated_utc':generated,
        'scope':'READ_ONLY_FIXED_RECEIPT_REUSE_AND_COMPILATION_OF_LEDGER;_NO_NEW_LEAN_CI_EXECUTION',
        'proof_baseline':BASE, 'manuscript_baseline':MANUSCRIPT,
        'source_branch':'codex/variable-envelope-boxes', 'integration_branch':'chatgpt/chen-p0-integration',
        'first_P0_document_commit':'9fe1d6b8b68a97cad3a122410ad7fde1701eed35',
        'previous_P0_user_handoff':PREVIOUS_P0, 'actual_existing_P0_fixed_source':CCE,
        'new_integration':{'fixed_commit':None,'status':'PENDING_AT_LEDGER_WRITE_TIME',
                           'status_as_of':generated,
                           'update_authority':'Actions artifact bound to the next actual immutable integration SHA; pending is not a permanent state.',
                           'root_full_build':'PENDING','root_kernel_replay':'PENDING','root_axiom_audit':'PENDING',
                           'new_198_declarations_complete_types':'PENDING',
                           'main_conditional_bridge_complete_compiler_type':'PENDING',
                           'hLower_hUpper_free_main_theorem':'NOT_AVAILABLE'},
        'counts':counts, 'toolchain':toolchain, 'certificate':certificate,
        'existing_CCE_root_validation':old_root, 'modules':modules,
        'separate_upstream_S1Carrier':upstream, 'separate_unfixed_P1_fifth_candidates':fifth,
        'corrected_intake_diagnostics':ref(out / 'CORRECTED_INTAKE_DIAGNOSTICS.json'),
        'compiler_inventory':ref(out / 'compiler-declarations.json'),
        'type_display_interpretation':{
            'pp_all_complete_accepted_count':451,
            'P1_default_pretty_count':140,'P1_default_pretty_without_omission_marker':133,
            'P1_default_pretty_with_omission_marker':7,
            'absence_of_ellipsis_is_not_claimed_as_pp_all':True,
            'P1_generated_or_private_type_coverage_audit_and_display_are_separate':True},
        'cross_part_inputs':[
            {'from':'P5','to':'P2','interface':'Buchstab refinement / CurrentPairedBuchstabBridge',
             'status':'PREVIOUSLY_ACCEPTED_COMPONENTS_REUSED'},
            {'from':'P1','to':['P2','P4-A','P5'],'interface':'Actual construction, support, parent legality, genuine integrals',
             'status':'FOUR_LOCAL_COMPONENTS_ACCEPTED;_FULL_ADOPTED_CONSTRUCTION_OPEN'},
            {'from':'P3','to':['P4-A','P4-B','P5'],'interface':'Physical arithmetic distribution and normalized errors',
             'status':'LONGSLOT_AND_NORMALIZATION_ACCEPTED;_OTHER_ACTUAL_DISTRIBUTION_INPUTS_OPEN'},
            {'from':'P4-A','to':'P5','interface':'Same actual rho K density bound',
             'status':'OPEN','does_not_wait_for_P4_B':True},
            {'from':'P4-B','to':'P0','interface':'Actual hUpper','status':'OPEN'},
            {'from':'P5','to':'P0','interface':'Complete eleven-term mean, true c, hLower','status':'OPEN'}],
        'final_mathematical_inputs':[
            'Actual weights, counts, normalization and real parameter ranges must match the fixed manuscript.',
            'Actual K for the same rho needs its analytic proof; existing local certificate slices are insufficient.',
            'Complete eleven-term Chen mean and analytic c still need suppliers.',
            'Actual hLower and hUpper remain explicit open inputs; no new structure or typeclass closes them.',
            'Keep the valid conditional bridge; add the complete main entry only after genuine suppliers are proved.'],
        'prior_version_history':preserved_history,'input_inventory':inputs,
        'local_actions':{'new_Lean':0,'new_Lake':0,'new_leanchecker':0,'new_CI':0,'new_Codex_tasks':0,
                         'signals_sent':0,'other_part_sources_modified':False,'integration_worktree_modified':False,
                         'read_only_source_hash_checks':31},
    }
    write_json(out / 'module-ledger.json', ledger)

    lines = [
        '# Part 0 第三批组件台账候选', '',
        f'生成：{generated}。本文件由 `build_ledger.py` 从固定源码和已有原始回执编目；本次没有执行 Lean、Lake、内核重放或 CI。', '',
        '**31 个固定生产模块中，19 个达到组件接收条件，12 个仍未全接收。新增 8 个组件有 198 个所属声明，累计 591 个。台账写入时新集成 SHA 尚未生成，整根构建、根重放、根公理检查及新增完整类型输出均为 pending；后续以该实际 SHA 的 Actions artifact 更新机器结果。**', '',
        '机器台账见 [module-ledger.json](module-ledger.json)，全部 591 条接受组件声明的编译器记录见 [compiler-declarations.json](compiler-declarations.json)。该清单逐项标明 `PP_ALL` 或 `DEFAULT_PRETTY`；不能把两者混称完整显式输出。', '',
        '## 固定版本与口径', '',
        '| 对象 | 完整 SHA / 状态 |', '| --- | --- |',
        f'| 共同证明基线 | `{BASE}` |', f'| 手稿基线 | `{MANUSCRIPT}` |',
        f'| 首轮 P0 文档 | `{ledger["first_P0_document_commit"]}` |',
        f'| 上轮 P0 交付 | `{PREVIOUS_P0}` |', f'| 当前实有 P0 固定来源 | `{CCE}` |',
        '| 新集成 SHA | **pending；本候选不自行生成集成提交** |',
        f'| P1 证明 / 后续文档 | `{p1["source_commit"]}` / `7f894bfb57b7aa561360e335c6d610b7c30614e0` |',
        f'| P2 证明 / 交接 | `{p2["proof_commit"]}` / `{p2["handoff_commit"]}` |',
        f'| P3 固定交接 | `{p3["fixed_submission"]}` |',
        f'| P4 生产 / 最新交接 | `{p4["fixed_production_source_checkpoint"]}` / `{p4["latest_fixed_commit"]}` |',
        f'| P5 最新固定交接 | `{p5["fixed_handoff"]}` |', '',
        '这里的“组件接收”表示固定源和既有编译、原装重放、公理审计回执已对应；新增 8 个叶模块仍需由 P0 写入公共根并绑定新集成 SHA。旧 11 个组件已在此前 P0 生产树。', '',
        '## 已执行验证的边界', '',
        f'CCE 的原始 artifact 绑定 `{CCE}`：完整 `lake build` 成功 **9790 jobs / 3226 秒**，根 `leanchecker` 成功 **506 秒**，根公理检查成功 **5260 个 ImbalancedChen 声明 / 31 秒**。',
        f'回执：[provenance]({published_rel(cce_dir / "provenance.log")})、[outcomes]({published_rel(cce_dir / "outcomes.log")})、[build]({published_rel(cce_dir / "build.log")})、[replay]({published_rel(cce_dir / "leanchecker.log")})、[axioms]({published_rel(cce_dir / "axiom-audit.log")})。', '',
        '已读取本地固定 Git diff：CCE 相对 80aca 仅改 `.github/workflows/lean.yml`，job timeout 为 150 分钟、build timeout 为 90 分钟，生产源码不变。**这些通过只属于 CCE 旧根；不能套到新增根或未被旧根导入的模块。**', '',
        '新增组件复用已有同版本成功记录：P1 四模块 strict/replay/所属声明审计；P3 Normalization 三门及 4957 模块导入身份；P2 Geometry/Prefix4Data/Prefix4 三门、完整声明审计以及已完成的专用 CI。没有重启同版本健康任务。', '',
        '## 声明数与完整类型', '',
        '| 来源 | 所属声明审计 | 完整显式 pp.all | 默认 pretty 无 `⋯`/`…` | 默认 pretty 有省略 |',
        '| --- | ---: | ---: | ---: | ---: |',
        '| 上轮已接收 11 模块 | 393 | 393 | 0 | 0 |',
        '| 本轮 P1 四模块 | 140 | **0** | 133 | 7 |',
        '| 本轮 P3 Normalization | 2 | 2 | 0 | 0 |',
        '| 本轮 P2 三模块 | 56 | 56 | 0 | 0 |',
        '| 接受组件合计 | **591** | **451** | **133** | **7** |', '',
        'P1 的 7 项省略均在 HistoricalPrefixCertificate；133 项没有省略标记仍不等于 pp.all。P1 的 probe 另有 10 声明，未混入生产 140。P0 正在准备新固定 SHA 下的 198 新声明和主条件桥完整类型输出，本候选只记录 pending。', '',
        '## 模块清单', '',
        '表中三门依次为严格编译 / 原装生产重放 / 全所属声明公理审计；“未达”指依赖超时，目标没有完成，“legacy+”指 producer 确实返回 0 但 P0 要求的导入对象绑定仍缺失。每项源码哈希与固定 SHA 在后面的明细中完整打印。', '',
        '| 模块 | 归属 | 三门 | 所属声明 | 接收 |', '| --- | --- | --- | ---: | --- |',
    ]
    for m in modules:
        is_acc = m['component_acceptance']['accepted']
        if is_acc: gates='通过 / 通过 / 通过'
        elif m['source_part']=='p4':gates='未达 / 未达 / 未达'
        elif m['module'].endswith('InitialSource'):gates='legacy+ / legacy+ / legacy+'
        else:gates='待验证 / 待验证 / 待验证'
        short = m['module'].removeprefix('ImbalancedChen.')
        count = m['declarations']['owned_audited']
        lines.append(f'| `{short}` | {m["part_owner"]} | {gates} | {count if count is not None else "—"} | {"组件接收" if is_acc else "候选"} |')
    lines.extend(['', '## 逐模块固定身份、回执与未闭合输入', ''])
    for m in modules:
        s=m['source'];lines.extend([f'### {m["module"]}', '',
            f'- 文件：[{m["repository_path"]}]({s["snapshot"]["path"]})；归属 **{m["part_owner"]}**；接收方：{", ".join(m["receiving_parts"])}。',
            f'- 当前证明源固定 SHA：`{s["fixed_commit"]}`；最新固定交接：`{s["latest_fixed_handoff"]}`。',
            f'- 源码 SHA256：`{s["sha256"]}`；Git blob：`{s["git_blob_sha1"]}`。',
            f'- 对象 SHA256：`{m["compiled_object_sha256"]}`。' if m['compiled_object_sha256'] else '- 当前源未记录匹配已编译对象。',
            f'- 组件状态：`{m["component_acceptance"]["status"]}`；新增根固定 SHA：pending。'])
        for key,label in [('compile','编译'),('kernel_replay','生产重放'),('axiom_audit','公理审计')]:
            g=m['validation'][key];r=g.get('receipt',preserved_history)
            sec=g.get('elapsed_seconds');ec=g.get('exit_code',g.get('returncode'))
            detail=f'，exit={ec}，{sec} 秒' if sec is not None else ''
            lines.append(f'- {label}：`{g["status"]}`{detail}；[回执]({r["path"]})。')
        d=m['declarations']
        lines.append(f'- 声明：所属审计 {d["owned_audited"] if d["owned_audited"] is not None else "未确认"}；pp.all {d["compiler_pp_all"]}；默认 pretty {d["compiler_default_pretty"]}（有省略 {d["default_pretty_with_omission_marker"]}）。')
        lines.append('- 未闭合输入：'+'；'.join(m['unclosed_real_inputs'])+'。')
        if m['outstanding_validation_gates']:lines.append('- 待补验证：'+', '.join(m['outstanding_validation_gates'])+'。')
        lines.append('')
    lines.extend([
        '## 采用证书与接口边界', '',
        'P2 Prefix4 只覆盖采用 v2 corpus 的原始零基编号 **0–3，E0**，包含此前首格。结果是四个已绑定实际格积分的有限和区间；没有把全部 17572 行、E1、全历史许可、全局并集积分或误差账本标为已证。', '',
        f'四格有限积分和：`{p2["scope"]["lower"]}` ≤ sum ≤ `{p2["scope"]["upper"]}`。采用 corpus SHA256：`{p2["adopted_data"]["source_sha256"]}`。原 Q160 区间没有成为未经证明的前提。', '',
        '`K / 80` 已含 `(1 / 20) * (K / 4)` 的增益；不能再乘一次增益。固定常数、实际权、计数、归一化、实数参数及量词保持原定义；有限局部通过不等于实际 K 或 c 的完整解析证明。', '',
        '| 供应关系 | 本批状态 |', '| --- | --- |',
        '| P5 → P2 Buchstab | 已接收 Buchstab refinement 与 P0 配对桥，继续复用 |',
        '| P1 → P2 / P4-A / P5 实际构造 | 四个局部生产模块接收；完整采用历史、合法性/支持、真实全局积分仍未闭合 |',
        '| P3 → P4 / P5 分布 | LongSlot 与 Normalization 接收；其余实际分布及误差供应仍缺 |',
        '| P4-A → P5 同一实际 rho 的 K | 尚待真实供应；**P5 不必等 P4-B** |',
        '| P4-B → P0 hUpper | 尚待真实供应 |',
        '| P5 → P0 十一项均值、c、hLower | 尚待真实供应 |', '',
        '## 单列的上游与候选', '',
        f'S1Carrier 属于固定 goldbach 依赖 `{p5["s1carrier"]["source_identity"]["fixed_dependency_commit"]}`，源码 SHA256 `{p5["s1carrier"]["source_identity"]["sha256"]}`。已有真实 strict/replay/audit，36 个所属声明审计与 17 个完整 public pp.all/Expr 类型可复用。两条 generated 默认类型有省略，不能称 36 条完整类型。该上游模块不计入 31 / 19 / 591。见 [上游类型](upstream-S1Carrier-types.json)。', '',
        'P5 InitialSource 的旧 `2573e5…` 源真实失败保留；当前 `4b11a6…` 修复已固定且 producer 三门确实成功。旧 schema 缺 audit 导入对象前后绑定，故暂不列为组件接收。InitialMean 当前 `5358e4…` 固定源仍待供应链及模块验证；类型只按源码提取。其 S1 局部下界尚不等于采用 L1、完整十一项均值、c 或 hLower。', '',
        'P1 取得以下两份未提交 joint-cell 第五层候选，固定 commit 都为 null，当前没有匹配对象回执；两份均独立保存源码身份。它们尚未与用户先前报告的“独立全局第五层积分仅单模块编译”候选建立身份对应。保留已取得成果，同时保留原候选的定位缺口。', '',
        '| 候选源码 | SHA256 | 固定提交 / 编译器确认 |', '| --- | --- | --- |',
    ])
    for f in fifth['files']:
        lines.append(f'| [{f["path"]}]({f["ledger_source_snapshot"]["path"]}) | `{f["source_sha256"]}` | null / 无 |')
    lines.extend(['', '## 首诊断与历史不可改写', '',
        '原 P1 接收器把两个首诊断误截成 `/`。本候选从其原始日志恢复完整行和完整诊断块：[CORRECTED_INTAKE_DIAGNOSTICS.json](CORRECTED_INTAKE_DIAGNOSTICS.json)。这是一项接收器提取字段修正，**不是新生产证明失败**。', '',
        '- attempt-01：Part1HistoryAudit 首个错误为缺少 LevelCheckProbe.olean。',
        '- attempt-02：LevelCheckProbe 首个错误为 `decide` 无法归约 `increasing.levelCheck = true`。',
        '- P5 原 S1Carrier exit 130 按中断保存，不改写成 Lean 证明失败；其后成功是另一条实际记录。',
        '- P4 专用 CI 在依赖构建处超时，五目标完成数为 0；不伪造第一处 Lean 诊断。', '',
        f'上轮完整 28 模块记录及配套文件逐字节保存在 [历史台账]({preserved_history["path"]})，历史文件 SHA256 `{preserved_history["sha256"]}`。原编译失败不随当前源升格而删除，也不把旧失败迁移到新源。', '',
        '## 复建', '',
        '以下命令只读取现有固定源码、Git 对象和已下载回执，写新台账；不调用 Lean、Lake、CI 或 Codex。路径可替换。', '',
        '```bash',
        'python build_ledger.py \\',
        '  --round-root /workspace/scratch/535d89efd063/p0-round3 \\',
        '  --previous-ledger /workspace/scratch/535d89efd063/p0-round3/previous-ledger/ledger-delivery/module-ledger.json \\',
        '  --git-repo /workspace/scratch/535d89efd063/goldbach-formalization \\',
        '  --output-dir /workspace/scratch/535d89efd063/p0-round3/ledger-candidate',
        '```', '',
        '此候选的角色是可追溯组件接收台账。完整最终入口仍须调用真正已证的上下界，最终类型不得携带 hLower、hUpper 或等价未证包装；新固定集成 SHA 的构建、内核及公理门保持待办。', '',
    ])
    (out / 'MODULE_LEDGER.md').write_text('\n'.join(lines))
    summary = f'''# Part 0 第三批台账摘要

- **31 个固定生产模块：19 组件接收、12 未全接收。**新增 8 个 = P1 四个 + P3 Normalization 一个 + P2 三个；新增所属声明 **198**，累计 **591**。
- 已保存全部 31 份当前源码快照，并核对 SHA256/Git blob；旧 28 项完整历史及原失败逐字节保留。固定版本、对象哈希、三门状态、声明数、原回执链接、接收方与未闭合输入逐模块记录。
- 类型统计：旧 393 + P2 新 56 + P3 新 2 = **451 条完整显式 pp.all**。P1 140 条是默认 pretty，其中 **133 无省略标记、7 有省略**，pp.all 为 **0**；不虚称其全部完整。新 P0 的 198 声明与主条件桥完整输出待新固定 SHA CI。
- **台账写入时新集成 SHA 与新根三门均 pending；机器结果将由该实际 SHA 的 Actions artifact 更新。**已有 `{CCE}` 的真实原始 artifact 证明 9790 jobs 构建、根重放及 5260 根声明公理检查成功；它与 `{PREVIOUS_P0}` 的生产源相同，仅 CI timeout 为 job 150 / build 90。旧根通过不迁移到新增根。
- P2 Prefix4 是原始零基行 **0–3 / E0**，包含首格；不是 17572 行，也不供应全局并集身份、历史合法性或完整 K/c。`K / 80` 已包含增益。
- P5 S1Carrier 上游 **36 审计 / 17 完整 public 类型**单列，不入19；InitialSource 固定修复的 producer 三门可复用，但旧 schema 导入绑定仍待补；InitialMean 固定 `5358e4…` 仍候选。
- P1 两份新取得但未提交的第五层 joint-cell 源单列，不冒认为原报告独立全局第五候选。没有把“尚未定位原候选”解释为无成果。
- P1 `FIRST_DIAGNOSTICS.json` 的 `/` 是接收器字段提取错误。本候选单独保存完整原始首诊断及原日志哈希；不是新生产证明失败。P5 exit130 保留为中断；P4 依赖超时保留为目标未达。
- 全十一项均值、实际 c、同一实际 rho 的 K、hLower、hUpper 仍需真实供应；**P5 只等 P4-A，不等 P4-B**。
- 本次编目没有执行 Lean/Lake/leanchecker/CI/Codex，没有改其他 Part 源码或集成工作树，也没有发信号。

交付：[`MODULE_LEDGER.md`](MODULE_LEDGER.md)、[`module-ledger.json`](module-ledger.json)、[`compiler-declarations.json`](compiler-declarations.json)、[`CORRECTED_INTAKE_DIAGNOSTICS.json`](CORRECTED_INTAKE_DIAGNOSTICS.json)、[`build_ledger.py`](build_ledger.py)。
'''
    (out / 'SUMMARY.md').write_text(summary)
    missing = []
    existing = []
    for target_text, source_text in sorted(publication_map.items()):
        target, source = Path(target_text), Path(source_text)
        if target.is_relative_to(publication_ledger):
            # This subtree is supplied by copying the complete ledger-candidate.
            continue
        item = {'source_path': str(source), 'destination_repository_path': str(target.relative_to(repo)),
                'ledger_link': os.path.relpath(target, publication_ledger),
                'sha256': digest(source.read_bytes()), 'bytes': source.stat().st_size}
        if target.is_file():
            item['already_copied_sha256_matches'] = digest(target.read_bytes()) == item['sha256']
            assert item['already_copied_sha256_matches'], item
            existing.append(item)
        else:
            missing.append(item)
    write_json(out / 'COPY_MISSING_FILES.json', {
        'schema': 'chen-p0-round3-ledger-publication-copy-list-v1',
        'publication_ledger_repository_path': 'verification/parts/p0/round3/ledger',
        'all_internal_ledger_files_supplied_by_copying_whole_candidate_directory': True,
        'source_files_read_only': True, 'copies_performed_by_this_script': False,
        'missing_referenced_files': missing, 'already_copied_referenced_file_count': len(existing),
        'already_copied_referenced_files': existing})
    copy_lines = ['# 发布路径与待复制原始日志', '',
        '台账最终位置：`verification/parts/p0/round3/ledger/`。', '',
        '各 intake 证据链接使用 `../intake/<原 intake 目录>/`；CCE 原始 artifact 使用 `../prior-ci/cce-core/`。P2 已在生产验证目录的 gate/log/type 文件直接引用 `verification/part2/round2/prefix4/`，不重复复制。', '',
        f'已核对 {len(existing)} 个外部引用文件在发布树中存在且哈希一致；另有 {len(missing)} 个直接引用文件需要复制，清单如下。此清单不修改源分支或发布树。', '',
        '| 原始文件 | 发布仓库目标 | SHA256 |', '| --- | --- | --- |']
    for item in missing:
        copy_lines.append(f'| `{item["source_path"]}` | `{item["destination_repository_path"]}` | `{item["sha256"]}` |')
    copy_lines += ['', '机器可执行复制清单见 [COPY_MISSING_FILES.json](COPY_MISSING_FILES.json)。完整复制 ledger-candidate 目录即提供所有内部源码、历史台账与历史日志；不要省略其 history/ 子目录。', '']
    (out / 'PUBLICATION_PATHS.md').write_text('\n'.join(copy_lines))
    manifest = {str(p.relative_to(out)): {'sha256':digest(p.read_bytes()), 'bytes':p.stat().st_size}
                for p in sorted(out.rglob('*')) if p.is_file() and p.name != 'MANIFEST.json'}
    write_json(out / 'MANIFEST.json', {'schema':'chen-p0-round3-ledger-file-manifest-v1',
                                      'generated_utc':generated,'files':manifest,'counts':counts})
    print(json.dumps({'output_dir':str(out),'counts':counts,'module_ledger_sha256':digest((out/'module-ledger.json').read_bytes()),
                      'history_ledger_sha256':preserved_history['sha256'],
                      'proof_executions':0,'files':len(manifest)},ensure_ascii=False,indent=2))


if __name__ == '__main__':
    main()
