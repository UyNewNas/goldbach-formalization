from pathlib import Path
import datetime
import difflib
import hashlib
import json
import re
import subprocess

ROOT = Path('/workspace/blue-reindex-build-evidence')
PUB = ROOT / 'publication-lite'
ISO = ROOT / 'verified-isolated-closure'
BUILD = Path('/workspace/blue-reindex-build')
REPO = Path('/workspace/goldbach-formalization')
OUT = ROOT / 'independent-source-review'
OUT.mkdir(exist_ok=True)


def read(p):
    return json.loads(p.read_bytes())


def digest(b):
    return hashlib.sha256(b).hexdigest()


def identity(p):
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': digest(b)}


def bound(p, expected):
    got = identity(p)
    assert got['bytes'] == expected['bytes'], (p, 'bytes')
    assert got['sha256'] == expected['sha256'], (p, 'sha256')
    return got


def blob(sha):
    return subprocess.check_output(['git', 'cat-file', 'blob', sha], cwd=REPO)


inputs = [PUB / 'PUBLICATION_FILES.json', PUB / 'SOURCE_INSTALL.json',
          ISO / 'INSTALL_SELECTION.json', ROOT / 'FINAL_TRIAL_RECEIPT.json',
          ROOT / 'coverage-addendum/COVERAGE_ADDENDUM.json',
          ROOT / 'PUBLIC_EXPORTS.json', ROOT / 'PUBLIC_AUDIT_RECEIPT.json',
          ROOT / 'KERNEL_REPLAY_RECEIPT.json', ROOT / 'BUILD_RECEIPT.json']
initial_inputs = [identity(p) for p in inputs]
files = read(inputs[0])
source = read(inputs[1])
install = read(inputs[2])
final = read(inputs[3])
coverage = read(inputs[4])
api = read(PUB / 'verification/API_IDENTITY.json')
candidates = read(PUB / 'verification/INTEGRATION_CANDIDATES.json')
assert len(files['files']) == 92
publication_checks = [bound(PUB / x['path'], x) for x in files['files']]
assert sum(x['bytes'] for x in publication_checks) == files['total_bytes_excluding_this_manifest']
assert source['project_source_count'] == install['project_source_count'] == 70
assert source['native_source_count'] == install['native_source_count'] == 456
assert len(source['native_canonical_materialization']) == 456
assert source['native_pin'] == '09b97db5764ade1246bfb77206baa1b124760958'
im = {x['module']: x for x in install['project_sources']}
sm = {x['module']: x for x in source['project_sources']}
changed_names = {x['module'] for x in candidates['verified_changed_or_new_source_files']}
assert len(im) == len(sm) == 70 and set(im) == set(sm)
assert len(changed_names) == 19

# These scans inspect source tokens only; no Lean elaboration or audit is run.
decl = re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                  r'(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|instance|'
                  r'namespace|section|end|variable|set_option|open|local notation)\b')
heads_pat = re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+([^\s({:]+)')


def theorem_headers(s):
    return [(m.group(1), s[m.start():s.index(':=', m.end()) + 2]) for m in heads_pat.finditer(s)]


def outside_proofs(s):
    starts = list(decl.finditer(s))
    out, pos = [], 0
    for i, z in enumerate(starts):
        if z.group('kind') not in ('theorem', 'lemma'):
            continue
        end = starts[i+1].start() if i+1 < len(starts) else len(s)
        cut = s.find(':=', z.end(), end)
        assert cut >= 0, s[z.start():z.start()+100]
        out += [s[pos:cut+2], '\n<PROOF_IMPLEMENTATION>\n']
        pos = end
    out.append(s[pos:])
    return ''.join(out)


def imports(s):
    return re.findall(r'(?m)^import\s+([^\n\r]+)', s)


def normalize_decl_exceptions(s, module):
    s = re.sub(r'(?m)^import[^\n]*\n', '', s)
    if module.endswith('P5ActualMultiGroupHBChartScale'):
        s = s.replace('  (R z y : ℝ)', '  R z y : ℝ').replace('  (j n : ℕ)', '  j n : ℕ')
    if module.endswith('P5ActualLabelledPrimeSmoothCharts'):
        s = s.replace('local notation "R" => ExactOriginalSmoothDyadicPartition.R\n', '')
    return s


repair_records = {}
for x in api['dependency_proof_body_compatibility_repairs']:
    repair_records.setdefault(x['module'], []).append(x)
for key in ['declaration_syntax_compatibility_repairs', 'elaboration_context_compatibility_repairs',
            'target_proof_body_compatibility_repairs']:
    for x in api[key]:
        repair_records.setdefault(x['module'], []).append(x)

rows, diffs, reconstructed = [], [], []
for module, entry in sm.items():
    post = (PUB / entry['postimage']).read_bytes()
    bound(PUB / entry['postimage'], entry)
    bound(BUILD / entry['isolated_project_install_path'], entry)
    bound(ISO / im[module]['packet_postimage'], entry)
    assert im[module]['identity']['sha256'] == entry['sha256']
    assert imports(post.decode()) == im[module]['imports']
    pre_id = entry['registered_preimage']
    new_leaf = module == 'ImbalancedChen.P5HBCompleteProduct'
    # A new relocated leaf has a computed Git blob identity, not an existing
    # historical object. Its real mathematical preimage is checked in parent.
    pre = post if new_leaf else blob(pre_id['git_blob_sha1'])
    assert len(pre) == pre_id['bytes'] and digest(pre) == pre_id['sha256']
    assert hashlib.sha1(b'blob ' + str(len(pre)).encode() + b'\0' + pre).hexdigest() == pre_id['git_blob_sha1']
    is_delta = pre != post or new_leaf
    assert is_delta == (module in changed_names), module
    if entry['registered_source_locator']:
        committed = subprocess.check_output(['git', 'show', source['registered_project_repository_commit']
                                            + ':' + entry['registered_source_locator']], cwd=REPO)
        assert committed == pre, (module, 'registered commit/preimage')
    row = {'module': module, 'bytes': len(post), 'sha256': digest(post),
           'packet_and_actual_install_and_original_packet_identical': True,
           'registered_preimage_sha256': digest(pre), 'new_relocated_leaf': new_leaf,
           'changed_or_new': is_delta, 'imports': imports(post.decode())}
    if is_delta and not new_leaf:
        ps, qs = pre.decode(), post.decode()
        assert theorem_headers(ps) == theorem_headers(qs), (module, 'headers')
        assert outside_proofs(normalize_decl_exceptions(ps, module)) == outside_proofs(
            normalize_decl_exceptions(qs, module)), (module, 'nonproof stream')
        replay = ps
        occurrences = 0
        for rec in repair_records[module]:
            blocks = (rec.get('proof_blocks', []) + rec.get('syntax_blocks', [])
                      + rec.get('context_blocks', []))
            if 'before' in rec and 'after' in rec:
                blocks.append({'before': rec['before'], 'after': rec['after']})
            for block in blocks:
                count = replay.count(block['before'])
                assert count > 0, (module, block['before'])
                occurrences += count
                replay = replay.replace(block['before'], block['after'])
        # Target alone changes one import route to the narrow relocation leaf.
        if module.endswith('P5OrderedFactorTupleRectangleReindex'):
            old_imports, new_imports = imports(replay), imports(qs)
            assert old_imports != new_imports
            replay = re.sub(r'(?m)^import[^\n]*\n', '', replay)
            qs_no_import = re.sub(r'(?m)^import[^\n]*\n', '', qs)
            assert replay == qs_no_import, (module, 'replay beyond import')
        else:
            assert replay == qs, (module, 'replay')
        row.update(all_public_private_theorem_headers_exact=True,
                   all_definitions_constants_hypotheses_exact_except_recorded_syntax=True,
                   exact_authorized_block_replay=True, replacement_occurrences=occurrences)
        diffs += difflib.unified_diff(ps.splitlines(True), qs.splitlines(True),
                                     fromfile=module + '.registered', tofile=module + '.verified')
        reconstructed.append({'module': module, 'replacement_occurrences': occurrences})
    rows.append(row)

assert sum(x['changed_or_new'] for x in rows) == 19
assert sum(x['new_relocated_leaf'] for x in rows) == 1
target_row = next(x for x in rows if x['module'] == source['target'])
assert target_row['replacement_occurrences'] == 6

leaf = (PUB / 'postimages/ImbalancedChen/P5HBCompleteProduct.lean').read_text()
parent = blob(source['relocated_existing_definition']['origin']['git_blob_sha1']).decode()
definition = 'def completeProduct (n : Fin m → ℕ) : ℕ := ∏ a, n a'
assert definition in parent and definition in leaf
assert 'namespace ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff' in leaf
definition_locations = [m for m, e in sm.items()
                        if re.search(r'(?m)^def completeProduct\b', (PUB / e['postimage']).read_text())]
assert definition_locations == ['ImbalancedChen.P5HBCompleteProduct']
old_parent_name = 'ImbalancedChen.P5ActualHBPostModulusLogCutoff'
assert old_parent_name not in sm
assert all(old_parent_name not in x['imports'] for x in rows)
assert source['old_broad_cutoff_parent_included'] is False
assert candidates['old_broad_parent']['compiled'] is False
assert candidates['old_broad_parent']['included_in_verified_install_selection'] is False
assert candidates['old_broad_parent']['apply_to_main_canonical_library'] is False

exports = read(ROOT / 'PUBLIC_EXPORTS.json')
canonical = read(Path(coverage['canonical_names_file']['path']))
bound(Path(coverage['canonical_names_file']['path']), coverage['canonical_names_file'])
name_owner_a = {(x['name'], x['module']) for x in exports['declarations']}
name_owner_b = {(x['name'], x['module']) for x in canonical['declarations']}
assert name_owner_a == name_owner_b and len(name_owner_a) == 1742
name_digest = digest(('\n'.join(sorted(n for n, _ in name_owner_a)) + '\n').encode())
assert name_digest == coverage['original_name_set_sha256'] == coverage['canonical_name_set_sha256']
assert set(canonical['modules']) == set(sm)
assert coverage['name_sets_equal'] and coverage['canonical_owner_bindings_equal']
assert not coverage['missing_names'] and not coverage['extra_names'] and not coverage['owner_changes']
for field in ['canonical_names_file', 'set_differences', 'raw_log', 'guarded_commands']:
    bound(Path(coverage[field]['path']), coverage[field])
for field in ['public_export_inventory', 'public_declaration_audit_receipt',
              'named_module_kernel_replay_receipt', 'full_target_build_receipt']:
    bound(Path(final[field]['path']), final[field])
build = read(ROOT / 'BUILD_RECEIPT.json')
audit = read(ROOT / 'PUBLIC_AUDIT_RECEIPT.json')
kernel = read(ROOT / 'KERNEL_REPLAY_RECEIPT.json')
assert build['exit_code'] == audit['exit_code'] == coverage['exit_code'] == 0
assert len(kernel['results']) == 19 and all(x['exit_code'] == 0 for x in kernel['results'])
assert set(kernel['exact_module_targets']) == changed_names
assert audit['checked_declaration_count'] == audit['axiom_report_count'] == 1742
assert not audit['unexpected_axioms'] and not audit['owned_axiom_declarations'] and not audit['contains_sorryAx']
assert source['source_selection_full_evidence_sha256'] == install['source_selection_sha256'] == build['source_selection_sha256'] == audit['source_selection_sha256'] == kernel['source_selection_sha256']
assert final == read(PUB / 'verification/FINAL_TRIAL_RECEIPT.json')
assert final == read(ISO / 'verification/FINAL_TRIAL_RECEIPT.json')
assert identity(ISO / 'INSTALL_SELECTION.json')['sha256'] == source['verified_source_install_selection_sha256']
assert identity(ROOT / 'coverage-addendum/COVERAGE_ADDENDUM.json')['sha256'] == read(PUB / 'VERIFICATION_SUMMARY.json')['coverage_addendum_sha256']

(OUT / 'SOURCE_DIFFS.patch').write_text(''.join(diffs))
for p, before in zip(inputs, initial_inputs):
    assert identity(p) == before, (p, 'input changed')
for item, checked in zip(files['files'], publication_checks):
    assert identity(PUB / item['path']) == checked, (item['path'], 'packet changed')

report = {
    'schema': 'independent_readonly_reindex_source_review_v1',
    'reviewed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'reviewer': '/root/retained_reuse',
    'status': 'PASS_STATIC_SOURCE_AND_EXISTING_EVIDENCE_REVIEW_ISOLATED_SCOPE_ONLY',
    'source_implementation_authorship': 'Reviewer did not implement or modify any reviewed source.',
    'Lean_kernel_type_axiom_invocations_in_this_review': 0,
    'live_main_frozen_and_original_packet_mutations': 0,
    'checked_inputs': initial_inputs,
    'publication_manifest': {'files_checked': 92, 'total_bytes': sum(x['bytes'] for x in publication_checks),
                             'all_recorded_sha256_and_sizes_match': True,
                             'all_original_publication_files_unchanged_after_review': True},
    'project_source_selection': {'source_count': 70, 'actual_install_root': str(BUILD),
                                'all70_match_publication_and_original_verified_packet': True,
                                'registered_commit': source['registered_project_repository_commit'],
                                'registered_source_locators_matching_exact_commit_preimages': sum(bool(x['registered_source_locator']) for x in sm.values()),
                                'unchanged_existing_blob_without_commit_path': 'ImbalancedChen.P5SmoothChartHBDyadicPartition',
                                'changed_or_new': 19, 'existing_changed': 18, 'new_relocated_leaf': 1,
                                'native_count': 456, 'native_pin': source['native_pin'],
                                'native_sources_recompiled_or_broad_cache_audit_repeated': False,
                                'modules': rows},
    'proof_and_API_review': {'all18_existing_changed_public_private_theorem_headers_exact': True,
                            'all18_exact_authorized_block_replay': True,
                            'all_definitions_constants_and_hypotheses_preserved_outside_explicit_syntax_exceptions': True,
                            'target_proof_replacement_blocks': 6,
                            'target_proof_API_adjustment_effects': 7,
                            'target_changes': ['2 List.length_eq_zero_iff API substitutions',
                                               '1 explicit Nat.lt_of_succ_lt_succ inference',
                                               '2 named List.length_ofFn (f := n) calls',
                                               '1 explicit prod_ofFn normalization',
                                               '1 Nat.succ_le_of_lt positive-to-at-least-one conversion'],
                            'new_mathematical_assumptions_or_quantifier_changes_found': False,
                            'replay_counts': reconstructed},
    'explicit_exceptions': [
        {'module': 'ImbalancedChen.P5ActualMultiGroupHBChartScale',
         'classification': 'GROUPED_RECORD_FIELD_PARSER_EXCEPTION',
         'change': 'R z y : Real -> (R z y : Real); j n : Nat -> (j n : Nat).',
         'intended_five_fields': ['R:Real', 'z:Real', 'y:Real', 'j:Nat', 'n:Nat'],
         'all_original_constraints_unchanged': ['positive', 'rough_nonneg', 'hb_nonneg', 'hb_cube',
                                                 'lower_support', 'upper_support', 'order', 'active'],
         'review': 'Whole Group block checked. Only these2 parentheses pairs differ. Consumers already use all5 projections independently; no constraint or numeric change.',
         'old_elaborated_type_equality_claimed': False},
        {'module': 'ImbalancedChen.P5ActualLabelledPrimeSmoothCharts',
         'classification': 'EXISTING_DYADIC_R_NAME_RESOLUTION_EXCEPTION',
         'change': 'Section-local notation R resolves ExactOriginalSmoothDyadicPartition.R.',
         'existing_definition': 'R(j:Nat):Real := (2:Real)^j',
         'review': 'All6 listed bare-R source lines use dyadic chart indices, tupleProfile, psi_left/right and R_pos from same supplier; no new alias/environment declaration. Root PNT error-function R is unintended.',
         'header_tokens_unchanged': True,
         'old_acceptable_unambiguous_elaborated_type_available': False,
         'old_new_elaborated_type_equality_claimed': False}],
    'completeProduct': {'name': source['relocated_existing_definition']['fully_qualified_name'],
                        'definition': definition, 'token_text_matches_existing_parent': True,
                        'unique_selected_definition_module': definition_locations,
                        'new_theorem_added': False,
                        'old_broad_parent_selected_or_directly_imported': False,
                        'old_parent_reexport_variant_compiled': False,
                        'old_parent_reexport_variant_accepted': False,
                        'main_integration_constraint': 'Do not coinstall the leaf with the original broad parent: duplicate completeProduct. The separate reexport proposal is uncompiled and excluded; this review authorizes only isolated packet publication.'},
    'existing_validation_receipts_reviewed_not_reexecuted': {
        'normal_build_exit_code': build['exit_code'], 'public_audit_exit_code': audit['exit_code'],
        'public_type_axiom_count': 1742, 'unexpected_or_owned_axioms': [], 'contains_sorryAx': False,
        'named_kernel_module_count': 19, 'named_kernel_all_exit0': True,
        'coverage_existing_exit_code': coverage['exit_code'], 'canonical_name_owner_pair_count': 1742,
        'independently_compared_existing_name_owner_pairs': True, 'name_set_sha256': name_digest,
        'missing_extra_owner_changes': [0, 0, 0],
        'all_receipt_selection_hashes_bound': True,
        'fresh_all_dependency_kernel_or_external_verifier_claimed': False},
    'limitations': ['Static source/evidence review only; no new compilation, kernel, type or axiom audit.',
                    'Scope is isolated70-project/456-native Reindex closure; not Retained, seven missing suppliers or all board nodes.',
                    'No main canonical integration accepted; old broad-parent collision remains a separate integration prerequisite.'],
    'review_artifacts': [identity(OUT / 'SOURCE_DIFFS.patch'), identity(Path(__file__))],
}
(ROOT / 'INDEPENDENT_SOURCE_REVIEW.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
addition = {'schema': 'independent_reindex_review_separate_addition_manifest_v1',
            'base_publication_manifest_unchanged': identity(PUB / 'PUBLICATION_FILES.json'),
            'does_not_rewrite_original_packet_or_receipts': True,
            'files_to_add_separately': [identity(ROOT / 'INDEPENDENT_SOURCE_REVIEW.json'),
                                      identity(OUT / 'SOURCE_DIFFS.patch'), identity(Path(__file__))],
            'git_staging_or_source_install_performed': False}
(ROOT / 'INDEPENDENT_SOURCE_REVIEW_FILES.json').write_text(json.dumps(addition, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'report': identity(ROOT / 'INDEPENDENT_SOURCE_REVIEW.json'),
                  'addition_manifest': identity(ROOT / 'INDEPENDENT_SOURCE_REVIEW_FILES.json'),
                  'source_count': 70, 'changed_or_new': 19, 'canonical_names': 1742,
                  'target_proof_compatibility_blocks': 6,
                  'target_proof_API_adjustment_effects': 7}, ensure_ascii=False, indent=2))
