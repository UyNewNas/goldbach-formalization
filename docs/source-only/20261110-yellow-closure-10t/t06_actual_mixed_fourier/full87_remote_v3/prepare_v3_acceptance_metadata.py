"""Assemble the separate paid-I87 installation proposal from pinned metadata.

No Lean, Lake, guard, finite decision, numerical replay or object restore.
"""
from __future__ import annotations
import copy
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent


def raw(path):
    return Path('\\\\?\\' + str(path.resolve())).read_bytes()


def descriptor(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def load(path):
    return json.loads(raw(path))


def write(name, value):
    (HERE / name).write_bytes((json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode())


def main():
    d = load(HERE / 'SOURCE_CLOSURE_DISCOVERY.json')
    old = load(BASE / 'full87_remote_v2/EXACT_INSTALL_MANIFEST.json')
    selected = {r['module']: r for r in d['full_selected_files']}
    active = set(d['active_module_names'])
    primary = d['primary_module']
    theorem_names = [
        primary + '.original_signed_density_and_count',
        'ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_ordinary_source',
        'ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_ordinary_saved',
        'ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_positive_source',
        'ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_positive_saved',
        'ImbalancedChen.P4AOriginalR17SameCutoffPresieve.original_source',
        'ImbalancedChen.P4AOriginalR17SameCutoffPresieve.original_saved',
        'ImbalancedChen.P4AOrderedThirdCommonSchedule.common_schedule',
        'ImbalancedChen.P4AOrderedThirdRectanglePayment.paid',
        'ImbalancedChen.P4AOrderedThirdSameCoefficient.joined',
        'ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.count',
        'ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.upper_majorant',
        'ImbalancedChen.P4AOriginalR17EighthSignedTransport.coefficient_difference',
        'ImbalancedChen.P4AOriginalR17EighthSignedTransport.raw_difference',
        'ImbalancedChen.P4AOriginalR17EighthParent.seventeenth_tent',
        'ImbalancedChen.P4AOriginalR17EighthParent.pair17_on_overlap',
        'ImbalancedChen.P4AOrderedThirdRectanglePayment.fixed_rate',
        'ImbalancedChen.P4AOrderedThirdRectanglePayment.rough_ratio']
    definitions = [
        primary + '.integralUpper',
        'ImbalancedChen.P4AOriginalR17EighthParent.orderedSixth',
        'ImbalancedChen.P4AOriginalR17EighthParent.orderedEighth',
        'ImbalancedChen.P4AOriginalR17EighthParent.parent',
        'ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.Ordinary',
        'ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.PositivePresieve',
        'ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.coefficient',
        'ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.keep',
        'ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.alignedWidth',
        'ImbalancedChen.P4AOriginalOrderedThirdFullPolicy.policy',
        'ImbalancedChen.P4AOrderedThirdArithmeticOccurrence.fresh',
        'ImbalancedChen.P4AUpperTaggedBetaAttachment.rho',
        'ImbalancedChen.P4AUpperTaggedParityCompiler.coefficient',
        'ImbalancedChen.P4AOriginalFull87CompiledCounting.moduli',
        'ImbalancedChen.P4AOriginalFull87SourcePrimeTests.cellIntegral',
        'ImbalancedChen.P4AOriginalFull87SourceDictionary.Cell',
        'ImbalancedChen.P4AOriginalNewFifthUnion.data',
        'ImbalancedChen.P4AFull87PhysicalReserveFromRate.Paid',
        'ImbalancedChen.P4AFull87PhysicalReserveFromRate.WallRate',
        'ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger.raw',
        'ImbalancedChen.P5OriginalCommonPositivePresieve.normalize']
    # Cell is the actual original87 inductive carrier. Preserve its kind;
    # do not misidentify it as an alias or a definitional wrapper.
    audit_roots = sorted(set(d['new_scope_roots']) | {n.rsplit('.', 1)[0] for n in theorem_names + definitions})
    if not set(audit_roots) <= active:
        raise ValueError('An audit root was not in the actual selected closure')
    targets = {
        'schema': 'full87-paid-I87-complete-type-audit-v3', 'source_commit': d['source_commit'],
        'primary_terminal': theorem_names[0], 'root_modules': audit_roots,
        'theorems': [{'name': n, 'defining_module': n.rsplit('.', 1)[0],
                      'source_sha256': selected[n.rsplit('.', 1)[0]]['sha256']} for n in theorem_names],
        'definition_prints': [{'name': n, 'kind': ('inductive' if n.endswith('SourceDictionary.Cell') else 'definition'),
                               'defining_module': n.rsplit('.', 1)[0],
                               'source_sha256': selected[n.rsplit('.', 1)[0]]['sha256']} for n in definitions],
        'retained_legacy_print_targets': {'path': 'LEGACY_PRINT_TARGETS.json',
                                         **descriptor(raw(BASE / 'full87_remote/PRINT_TARGETS.json'))},
        'retained_legacy_theorem_count': 27, 'retained_original_floor_theorem_count': 9,
        'expected_record_markers': {'theorems': 'FULL87_PAID_DECL', 'theorem_count': 'FULL87_PAID_COUNT',
                                    'definitions': 'FULL87_PAID_DEF', 'definition_count': 'FULL87_PAID_DEF_COUNT'},
        'allowed_standard_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'scope_boundaries': [
            'I87 is the exact finite sum of the original87 cellIntegral; it is not all22 savings.',
            'Same actual corrected coefficient/keep, Q, rho and one beta schedule occur in density/payment/count.',
            'The actual same-Q/rho realPhysicalDistributionError, ceil(z) and T+1 remain explicit.',
            'The earlier full87 archived numerical and old27 types are retained in a separate unchanged audit.',
            'No full signed PP error estimate, factor-group licence, whole all22 hdensity or final hUpper is supplied.']}
    write('PRINT_TARGETS.json', targets)
    (HERE / 'LEGACY_PRINT_TARGETS.json').write_bytes(raw(BASE / 'full87_remote/PRINT_TARGETS.json'))

    legacy_audit = raw(BASE / 'full87_remote/Full87RemoteAudit.lean')
    (HERE / 'Full87RemoteAudit.lean').write_bytes(legacy_audit)
    old_source = legacy_audit.decode('utf-8')
    start = old_source.index('open Lean Elab Command in\nrun_cmd do')
    end = old_source.index('\n#print axioms ')
    collector = old_source[start:end]
    array_start = collector.index('  let names : Array Name := #[')
    array_end = collector.index('\n  let allowed := ', array_start)
    array = '  let names : Array Name := #[\n' + ',\n'.join('    `' + n for n in theorem_names) + ']'
    collector = collector[:array_start] + array + collector[array_end:]
    collector = collector.replace('FULL87_DECL', 'FULL87_PAID_DECL').replace('FULL87_COUNT', 'FULL87_PAID_COUNT')
    defs_collector = collector.replace(array, '  let names : Array Name := #[\n' + ',\n'.join('    `' + n for n in definitions) + ']')
    defs_collector = defs_collector.replace('let .thmInfo _ := info | throwError "Target is not a theorem: {name}"',
        'let kind ← match info with\n'
        '      | .defnInfo _ => pure "definition"\n'
        '      | .inductInfo _ =>\n'
        '        if name == `ImbalancedChen.P4AOriginalFull87SourceDictionary.Cell then pure "inductive"\n'
        '        else throwError "Unexpected inductive target: {name}"\n'
        '      | _ => throwError "Target is not a physical definition or original Cell carrier: {name}"')
    defs_collector = defs_collector.replace('toJson "theorem"', 'toJson kind')
    defs_collector = defs_collector.replace('FULL87_PAID_DECL', 'FULL87_PAID_DEF').replace('FULL87_PAID_COUNT', 'FULL87_PAID_DEF_COUNT')
    header = '\n'.join('import ' + n for n in audit_roots) + '\nimport Lean.Util.CollectAxioms\n\n'
    options = old_source[old_source.index('set_option pp.all true'):start]
    audit = header + '/-! Actual R17 paid-I87 full types, axioms and physical definitions. Remote only. -/\n\n'
    audit += options + collector + '\n\n' + defs_collector + '\n\n'
    audit += '\n'.join('#print axioms ' + n for n in theorem_names + definitions) + '\n\n'
    audit += '\n'.join('#print ' + n for n in definitions) + '\n'
    (HERE / 'Full87R17PaidAudit.lean').write_bytes(audit.encode())

    edges = [(r['module'], imp) for r in selected.values() for imp in r['imports']]
    reverse = {}
    for caller, imported in edges:
        reverse.setdefault(imported, set()).add(caller)
    def cone(seeds, active_only=True):
        seen, todo = set(seeds), list(seeds)
        while todo:
            for caller in reverse.get(todo.pop(), set()):
                if caller not in seen:
                    seen.add(caller); todo.append(caller)
        return sorted(seen & (active if active_only else set(selected)))
    r17_seeds = [r['module'] for r in old['semantic_selection']['selections']]
    api_seeds = ['ImbalancedChen.P4AOriginalOrderedThirdFullPolicy']
    r17_cone, api_cone = cone(r17_seeds), cone(api_seeds)
    r17_inventory_cone = sorted(set(cone(r17_seeds, False)) - active)
    forbidden = sorted(set(r17_cone) | set(api_cone))
    original729 = set(old['potential_v3_source_matches_only_not_accepted_objects'])
    candidates = sorted((original729 & active) - set(forbidden))
    invalidation = {
        'schema': 'full87-paid-I87-selected-source-invalidation-v3', 'source_commit': d['source_commit'],
        'compiled': False, 'kernel_verified': False, 'atomic_R17_all_four': True,
        'semantic_selections': old['semantic_selection']['selections'],
        'R17_seeds': r17_seeds, 'R17_actual_active_reverse_import_cone': r17_cone,
        'R17_inventory_only_reverse_import_cone': r17_inventory_cone,
        'API_patch_seeds': api_seeds, 'API_patch_active_reverse_import_cone': api_cone,
        'forbidden_old_object_modules': forbidden,
        'old729_source_candidate_intersection_with_forbidden': sorted(original729 & set(forbidden)),
        'unaffected_source_candidates_only': candidates, 'accepted_objects': [],
        'rule': 'Each actual predecessor/facet change propagates. No old-semantics object is accepted for any affected dependant, even if its own source bytes match.'}
    write('SEMANTIC_AND_API_INVALIDATION.json', invalidation)

    manifest = copy.deepcopy(old)
    manifest['schema'] = 'full87-exact-install-manifest-v3-actual-R17-paid-I87'
    manifest['status'] = 'SOURCE_ONLY_FUTURE_ACTUAL_PAID_I87_INSTALLATION_PENDING_ROOT_REVIEW_REAL_OBJECT_REBIND_AND_REMOTE_GATES'
    manifest['frozen_source_parent'] = d['source_commit']
    manifest['supersedes_source_environment_manifest_sha256'] = descriptor(raw(BASE / 'full87_remote_v2/EXACT_INSTALL_MANIFEST.json'))['sha256']
    manifest['historical_environment_preserved_unmodified'] = True
    manifest['files'] = sorted(selected.values(), key=lambda r: r['module'])
    manifest['counts'].pop('unchanged_original_core_selections', None)
    for key in ['selected_published_supplement_additions', 'new_scope_extension']:
        manifest['counts']['historical_v2_' + key] = manifest['counts'].pop(key)
    manifest['counts'].update({'original_core_selection_names_retained': 1046,
        'original_core_source_bytes_same_as_authority': 1021, 'original_core_source_bytes_changed_from_authority': 25,
        'installed_mathematical_modules': len(selected), 'active_mathematical_modules': len(active),
        'inventory_only_modules': len(set(selected) - active), 'additional_v3_source_inventory': len(d['additional_source_records']),
        'additional_v3_active_modules': len(d['new_active_module_names']), 'actual_paid_terminal_closure': len(d['actual_paid_terminal_closure']),
        'complete_fresh_kernel_modules': len(d['fresh_kernel_modules'])})
    witness = raw(BASE.parent / 't05_all22_actual_density/G6_ORIGINAL_WITNESS.json')
    witness_desc = descriptor(witness)
    if witness_desc['sha256'] != '0401062c690c7993fd34722dca97d3c504f3e72f83d87659f597d135490d50a5':
        raise ValueError('Original G6 witness differs')
    manifest['data_inputs'].append({'install_path': 'ImbalancedChen/G6_ORIGINAL_WITNESS.json', **witness_desc,
        'consuming_module': 'ImbalancedChen.P4AOriginalThirdFallbackArchive',
        'origin': {'kind': 'release_member',
                   'member': 'chen-numerical-evidence-20261010-renewal-v2/goldbach-research/third-prefix-fallback-pair-20261009.witness.json'}})
    manifest['counts']['installed_data_inputs'] = len(manifest['data_inputs'])
    manifest['counts']['original_release_json_retained'] = 144
    manifest['counts']['release_json'] = 145
    manifest['legacy_audit_source'] = old['audit_source']
    manifest['audit_source'] = {'module': 'ImbalancedChen.Full87R17PaidAudit',
        'install_path': 'ImbalancedChen/Full87R17PaidAudit.lean', **descriptor(audit.encode())}
    manifest['targets'] = [{
        'id': 'actual_R17_paid_original87_integral_density_and_same_coefficient_count',
        'modules': audit_roots, 'primary_module': primary, 'declarations': theorem_names,
        'definition_prints': definitions, 'closure_modules': sorted(active),
        'primary_terminal_closure_modules': d['actual_paid_terminal_closure'],
        'external_imports': sorted({imp for caller, imp in edges if caller in active and not imp.startswith('ImbalancedChen.')}),
        'unresolved_modules': d['unresolved'], 'whole_yellow_scope_complete': False,
        'eligible_for_green': False, 'remaining_mathematical_premises': targets['scope_boundaries'],
        'source_identity_sha256': identity([(n, selected[n]['sha256']) for n in sorted(active)])}]
    manifest['retained_legacy_target'] = old['targets'][0]
    manifest['mandatory_legacy_kernel_modules'] = d['mandatory_legacy_kernel_modules']
    manifest['fresh_kernel_modules'] = d['fresh_kernel_modules']
    manifest['mandatory_legacy_kernel_module_set_sha256'] = identity(sorted(d['mandatory_legacy_kernel_modules']))
    manifest['fresh_kernel_module_set_sha256'] = identity(sorted(d['fresh_kernel_modules']))
    manifest['inventory_only_modules'] = sorted(set(selected) - active)
    manifest['inventory_only_unexpanded_imports'] = {
        r['module']: [n for n in r['imports'] if n.startswith('ImbalancedChen.') and n not in selected]
        for r in selected.values() if r['module'] not in active
        and any(n.startswith('ImbalancedChen.') and n not in selected for n in r['imports'])}
    manifest['active_external_direct_imports'] = manifest['targets'][0]['external_imports']
    manifest['external_imports'] = sorted({imp for _, imp in edges if not imp.startswith('ImbalancedChen.')})
    manifest['edges'] = edges
    manifest['new_scope_sources'] = d['additional_source_records']
    manifest['unresolved'] = d['unresolved']
    manifest['source_owner_registries'] = d['owner_registries']
    manifest['mandatory_FullPolicy_patch'] = d['mandatory_FullPolicy_patch']
    current_selections = [
        {**r, 'post': {**{k: selected[r['module']][k] for k in ['bytes', 'sha256', 'git_blob_sha1', 'origin']}}}
        for r in old['semantic_selection']['selections']]
    manifest['semantic_selection'] = {
        'schema': 'full87-actual-paid-I87-R17-semantic-selection-v3',
        'status': 'ATOMIC_R17_CORRECT_SEMANTICS_WITH_ACTUAL_PAID_CONSUMERS_SELECTED_UNCOMPILED',
        'T05_registry': old['semantic_selection']['T05_registry'],
        'T05_broad_import_impact': old['semantic_selection']['T05_broad_import_impact'],
        'selections': current_selections, 'atomic_all_four': True,
        'semantic_reason': old['semantic_selection']['semantic_reason'],
        'seeds': r17_seeds, 'affected_active_modules': r17_cone,
        'affected_inventory_only_modules': r17_inventory_cone,
        'affected_prior_v3_source_matches': sorted(original729 & set(r17_cone)),
        'additional_R17_comparison_parent_modules_adopted': [
            'ImbalancedChen.P4AOriginalNonsingletonComparison',
            'ImbalancedChen.P4AOriginalNonsingletonEighthParent'],
        'mandatory_API_patch_reverse_cone': api_cone,
        'actual_paid_primary': primary,
        'old_object_restore_for_affected_modules': 'FORBIDDEN',
        'fresh_consumer_elaboration_and_semantic_review_required': True,
        'old_R0_environment_claims_not_promoted': True}
    manifest['semantic_forbidden_old_object_modules'] = forbidden
    manifest['semantic_eligible_v3_source_matches_only_not_accepted_objects'] = candidates
    manifest['potential_v3_source_matches_only_not_accepted_objects'] = candidates
    manifest['active_modules_requiring_fresh_or_unmatched_source_build'] = sorted(active - set(candidates))
    manifest['active_sources_absent_or_changed_from_v3'] = sorted(active - original729)
    manifest['accepted_reuse_objects'] = []
    manifest['historical_v2_extension_module_names'] = manifest.pop('extension_modules')
    manifest['additional_v3_extension_module_names'] = sorted(r['module'] for r in d['additional_source_records'])
    manifest['historical_v2_published_candidates_not_needed'] = manifest.pop('published_candidates_not_needed_by_selected_scope')
    manifest['native_research_overlay']['source_gate_script'] = 'stage_native_research_overlay_v3.py'
    manifest['native_research_overlay']['actual_guarded_compile_setup_import_gate'] = 'MANDATORY_FUTURE_ROOT_ADAPTER_NOT_IMPLEMENTED_BY_SOURCE_INSTALLER'
    manifest['required_unpublished_frozen_suppliers'] = []
    manifest['original_29_published_helpers'] = copy.deepcopy(old['required_unpublished_frozen_suppliers'])
    for helper in manifest['original_29_published_helpers']:
        helper.pop('review_and_root_publication_pending', None)
        helper['published_unchanged_raw_bytes'] = True
        helper['selected_origin'] = selected[helper['module']]['origin']
        helper['active_in_complete_scope'] = helper['module'] in active
    manifest['counts']['original_29_helpers_retained'] = len(manifest['original_29_published_helpers'])
    manifest['build_authorized'] = False
    manifest['pending_remote_integration'] = [
        'Root review/publication of this separate source-only proposal and exact complete type/closure/resource map.',
        'Await sole existing CDC v3 real coherent object artifact; immutable artifact ID/digest plus per-module rebind before use.',
        'Implement and independently review T01 dependency/object/type/guard-input adapters and exact restore against real artifact; no competing cold729 build.',
        'Run source installer, pre-source receipt, native43 install receipt and actual source/runtime/setup/import/ABI gate.',
        'Build only actual absent/invalidated modules and audits; run actual guarded compilation with exact source flags.',
        'Postcompile source verification must bind pre receipt/census, not repair any source; fresh complete1664 kernel gate and complete types/axioms remain mandatory.']
    support_names = ['stage_project_full87_v3.py', 'verify_staged_sources_v3.py', 'stage_native_research_overlay_v3.py',
        'PRINT_TARGETS.json', 'REUSE_PLAN.json', 'INHERITED_TOOL_ADAPTATIONS.json', 'NATIVE_RESEARCH_OVERLAY.json',
        'NATIVE_ACCEPTANCE_REQUIREMENTS.json', 'SEMANTIC_AND_API_INVALIDATION.json', 'HISTORICAL_METADATA_FIELD_ERRATUM.json',
        'SOURCE_GATE_V3_STATIC_CHANGE_NOTE.md', 'SOURCE_VARIANTS_AND_RESOURCES.json',
        'G6_RELEASE_MEMBER_RECEIPT.json', 'RUNTIME_SETUP_IMPORT_ACCEPTANCE_MAP.json', 'CORE_SELECTION_BYTE_COMPARISON.json',
        'SOURCE_SELECTION_ROLE_MAP.json', 'LEGACY_PRINT_TARGETS.json', 'TOPOLOGICAL_BUILD_PLAN.json', 'EXECUTION_ORDER.md']
    manifest['support_files'] = [{'path': p, **descriptor(raw(HERE / p))} for p in support_names]
    write('EXACT_INSTALL_MANIFEST.json', manifest)
    print(json.dumps({'counts': manifest['counts'], 'R17_active_cone': len(r17_cone),
                      'API_active_cone': len(api_cone), 'source_candidates_only': len(candidates),
                      'accepted_objects': 0, 'type_theorems': len(theorem_names), 'definition_types': len(definitions)}))


if __name__ == '__main__':
    main()
