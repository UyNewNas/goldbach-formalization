from pathlib import Path
import collections
import datetime
import hashlib
import json
import re
import shlex
import subprocess

ROOT = Path('/workspace/blue-member-repair-batch9')
BUILD = Path('/workspace/blue-member-build')
MAIN = Path('/workspace/goldbach-formalization')


def read(p):
    return json.loads(p.read_bytes())


def sha(b):
    return hashlib.sha256(b).hexdigest()


def ident(p):
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': sha(b)}


def bound(p, expect):
    got = ident(p)
    assert got['bytes'] == expect['bytes'] and got['sha256'] == expect['sha256'], p
    return got


release = read(ROOT / 'FINAL_RELEASE.json')
manifest = read(ROOT / 'PUBLICATION_FILES.json')
validation = read(ROOT / 'VALIDATION_RESULTS.json')
selection = read(ROOT / 'SOURCE_SELECTION.json')
initial_core = [ident(ROOT / x) for x in ['FINAL_RELEASE.json', 'PUBLICATION_FILES.json',
                                         'VALIDATION_RESULTS.json', 'SOURCE_SELECTION.json']]
assert release['validation_results_sha256'] == sha((ROOT / 'VALIDATION_RESULTS.json').read_bytes())
assert release['publication_files_sha256'] == sha((ROOT / 'PUBLICATION_FILES.json').read_bytes())
assert len(manifest['files']) == 64
initial_packet = [bound(ROOT / f['path'], f) for f in manifest['files']]

pat = re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                 r'(?P<kind>theorem|lemma|def|abbrev|namespace|section|end|open|variable)\b')


def declarations(s):
    starts = list(pat.finditer(s))
    result = []
    for i, m in enumerate(starts):
        if m.group('kind') not in ['theorem', 'lemma', 'def', 'abbrev']:
            continue
        end = starts[i+1].start() if i+1 < len(starts) else len(s)
        cut = s.index(':=', m.end(), end) + 2
        name = s[m.end():].lstrip().split()[0]
        result.append({'name': name, 'kind': m.group('kind'),
                       'header': s[m.start():cut], 'full': s[m.start():end]})
    return result


def nonproof_stream(s):
    starts = list(pat.finditer(s))
    result, pos = [], 0
    for i, m in enumerate(starts):
        if m.group('kind') not in ['theorem', 'lemma']:
            continue
        end = starts[i+1].start() if i+1 < len(starts) else len(s)
        cut = s.index(':=', m.end(), end) + 2
        result += [s[pos:cut], '\n<PROOF_IMPLEMENTATION>\n']
        pos = end
    result.append(s[pos:])
    return ''.join(result)


neutral_old = 'SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.'
neutral_new = 'Verification records: docs/verification/20261123-blue-compilation.'
rows, outputs = [], []
for module, chosen in selection.items():
    short = module.split('.')[-1]
    base = (ROOT / short / 'baseline.lean').read_bytes()
    post = (ROOT / short / 'candidate.lean').read_bytes()
    assert sha(base) == chosen['preimage_sha256']
    assert sha(post) == chosen['postimage_sha256'] == validation['modules'][module]
    b, p = base.decode(), post.decode()
    bd, pd = declarations(b), declarations(p)
    assert [(x['name'], x['kind'], x['header']) for x in bd] == [
        (x['name'], x['kind'], x['header']) for x in pd], (module, 'headers')
    changed_defs = [a['name'] for a, z in zip(bd, pd)
                    if a['kind'] in ['def', 'abbrev'] and a['full'] != z['full']]
    normalized = p
    if short == 'P1FourthNearOneKernel':
        normalized = normalized.replace(neutral_new, neutral_old)
        assert changed_defs == []
    elif short == 'P1CoarseFirstCubeFallbackMargin':
        assert changed_defs == []
    else:
        assert changed_defs == ['wallForm']
        normalized = normalized.replace('import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral\n', '')
        for a, z in zip(bd, pd):
            if a['name'] == 'wallForm':
                normalized = normalized.replace(z['full'], a['full'])
        old_form = next(x for x in bd if x['name'] == 'wallForm')['full']
        new_form = next(x for x in pd if x['name'] == 'wallForm')['full']
        for i in range(4):
            assert new_form.count(f'(ContinuousLinearMap.proj {i} : (Fin 4 → ℝ) →L[ℝ] ℝ)') == 1
        assert '(2 : ℝ) •' in old_form and '(2 : ℝ) •' in new_form
    assert nonproof_stream(b) == nonproof_stream(normalized), (module, 'nonproof')
    source_path = Path('ImbalancedChen') / (short + '.lean')
    assert (BUILD / source_path).read_bytes() == post
    main = (MAIN / source_path).read_bytes()
    assert sha(main) == release['actual_source_readback'][module]['main_source_sha256']
    if short == 'P1FourthNearOneKernel':
        assert sha(main) == '83fc7aa451aa3a40d9112f511b3d869045117a79eb7d4ba3f6c6626d96c1f19d'
        assert main != base and main != post
    else:
        assert main == post
    for rel, exp in validation['source_plus_five_outputs'][module].items():
        outputs.append(bound(BUILD / rel, exp))
    rows.append({'module': module, 'baseline_sha256': sha(base), 'accepted_Member_sha256': sha(post),
                 'current_main_sha256': sha(main), 'main_equals_accepted_Member': main == post,
                 'full_public_private_headers_byte_exact': True,
                 'all_nonproof_bytes_exact_after_recorded_comment_import_and_wallForm_exceptions': True,
                 'changed_definitions': changed_defs,
                 'before_CRLF': base.count(b'\r\n'), 'after_CRLF': post.count(b'\r\n'),
                 'declarations': [{'name': x['name'], 'kind': x['kind'], 'header': x['header'],
                                   'header_sha256': sha(x['header'].encode()),
                                   'full_definition': x['full'] if x['kind'] in ['def', 'abbrev'] else None}
                                  for x in pd]})
assert len(outputs) == 18

# Exact existing published code reuse: source snapshots are bound directly to
# immutable commits, not inferred from workflow success metadata.
near_published = subprocess.check_output(['git', 'show',
    'c1eb228f281d93e03a6fc231e0086baa9f589036:verification/parts/p0/p1-near-one-api/candidate.lean'], cwd=MAIN)
assert near_published == (ROOT / 'P1FourthNearOneKernel/published_or_static_candidate.lean').read_bytes()
assert near_published.decode().replace(neutral_old, neutral_new).encode() == (
    ROOT / 'P1FourthNearOneKernel/candidate.lean').read_bytes()
fallback_published = subprocess.check_output(['git', 'show',
    '3c94ec71e13d038ae661138dac1037116615a20f:ImbalancedChen/P1CoarseFirstCubeFallbackMargin.lean'], cwd=MAIN)
assert fallback_published == (ROOT / 'P1CoarseFirstCubeFallbackMargin/candidate.lean').read_bytes()
supplier = BUILD / 'ImbalancedChen/ActualPrimeBoxInitialSavingIntegral.lean'
assert sha(supplier.read_bytes()) == '71dcac6ff550921467241071fbd86a5e90025ca27bd0292cb2f6f5b6ceda25e0'
assert 'theorem actualPrimeTupleLog_sum_prod' in supplier.read_text()
supplier_decl = next(x for x in declarations(supplier.read_text()) if x['name'] == 'actualPrimeTupleLog_sum_prod')
assert '(hp : ∀ i, 0 < p i)' in supplier_decl['header']

# Check original raw failure slices against their exact immutable byte spans.
failure_checks = []
for module, rec in read(ROOT / 'BEFORE_LOG_SLICES.json').items():
    raw = Path(rec['original_running_log']).read_bytes()[rec['raw_byte_start']:rec['raw_byte_end_exclusive']]
    assert raw == (ROOT / rec['slice']).read_bytes() and sha(raw) == rec['slice_sha256']
    assert b'error:' in raw
    failure_checks.append({'module': module, 'raw_slice': ident(ROOT / rec['slice']),
                           'matches_original_log_byte_span': True})
failed = read(ROOT / 'P1OriginalCoarseFourthArithmeticWall/attempt-1/FAILED_STAGE.json')
assert failed['record']['exit_code'] == 1
fail_path = ROOT / 'P1OriginalCoarseFourthArithmeticWall/attempt-1' / failed['record']['log']
assert sha(fail_path.read_bytes()) == failed['record']['log_sha256']
assert b'Fin.mk' in fail_path.read_bytes() or '⟨↑0'.encode() in fail_path.read_bytes()
assert sha((ROOT / 'P1OriginalCoarseFourthArithmeticWall/attempt-1/candidate.lean').read_bytes()) == 'd0572c3de790072433921c023dd92c813bc60c5d532ab074e54e398c26093485'

commands = validation['normal_commands'] + validation['kernel_commands'] + [validation['audit_command']]
assert len(commands) == 7 and all(x['exit_code'] == 0 for x in commands)
for rec in commands:
    assert sha((ROOT / rec['log']).read_bytes()) == rec['log_sha256']
    assert rec['cwd'] == str(BUILD)
    assert rec['argv'][:4] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
                               '/workspace/blue-build-tools/runtime-evidence/state.json']
runtime = read(ROOT / 'ACTUAL_RUNTIME_COMMANDS.json')
assert len(runtime['actual_compiler_commands']) == 4
for path, event in runtime['actual_compiler_commands'].items():
    assert event['cwd'] == str(BUILD) and event['tool'] == 'lean'
    assert event['command'][:4] == ['/workspace/blue-build-tools/runtime/p0-ci-shadow-toolchain/bin/lean-runtime',
                                     '-t0', '-j2', '-M12288']
    assert event['sysroot'] == '/workspace/blue-build-tools/runtime/p0-ci-shadow-toolchain'
    assert '-DmaxRecDepth=100000' in event['input_args'] and '-DmaxHeartbeats=4000000' in event['input_args']
    assert path in event['input_args']
    if path == str(ROOT / 'PublicAudit.lean'):
        assert event['input_args'] == validation['audit_command']['argv'][7:]
        continue
    short = Path(path).stem
    current_trace = read(BUILD / ('.lake/build/lib/lean/ImbalancedChen/' + short + '.trace'))
    trace_lines = [x['message'] for x in current_trace['log']
                   if x['message'].startswith('.> LEAN_PATH=') and path in x['message']]
    assert len(trace_lines) == 1
    tokens = shlex.split(trace_lines[0][len('.> '):])
    idx = tokens.index('/workspace/blue-build-tools/runtime/p0-ci-shadow-toolchain/bin/lean')
    assert tokens[idx+1:] == event['input_args']

exports = read(ROOT / 'PUBLIC_EXPORTS.json')
auditlog = (ROOT / 'types-axioms.log').read_text()
records = [json.loads(line.split('AUDIT_RECORD ', 1)[1]) for line in auditlog.splitlines()
           if 'AUDIT_RECORD ' in line]
assert records == [{k: v for k, v in x.items() if k != 'transitive_axioms'} for x in exports]
assert len(exports) == 118
counts = dict(collections.Counter(x['module'] for x in exports))
assert counts == validation['public_export_counts'] == release['environment_public_export_counts']
assert len({x['name'] for x in exports}) == 118
assert all(not x['is_axiom_declaration'] for x in exports)
assert all('...' not in x['type_expression'] and 'sorryAx' not in x['type_expression'] for x in exports)
axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", auditlog, re.S)
no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", auditlog)
assert len(axioms) + len(no_axioms) == 118
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
def axiom_names(a):
    return {re.sub(r'\.\{[^}]*\}$', '', s.strip()) for s in a.split(',')}
assert all(axiom_names(a).issubset(allowed) for _, a in axioms)
assert {n for n, _ in axioms} | set(no_axioms) == {x['name'] for x in exports}
parsed_axioms = {n: axiom_names(a) for n, a in axioms}
parsed_axioms.update({n: set() for n in no_axioms})
assert all(set(x['transitive_axioms']) == parsed_axioms[x['name']] for x in exports)
assert 'AUDIT_FINISHED 118' in auditlog
audit_source = (ROOT / 'PublicAudit.lean').read_text()
assert 'env.constants.fold' in audit_source and 'env.getModuleIdxFor? name' in audit_source
assert '!isPrivateName name' in audit_source and 'set_option pp.all true' in audit_source

for check in initial_packet:
    assert ident(Path(check['path'])) == check
for check in initial_core:
    assert ident(Path(check['path'])) == check
for check in outputs:
    assert ident(Path(check['path'])) == check

report = {
    'schema': 'independent_member_batch9_P1_static_review_v1',
    'reviewer': '/root/retained_reuse', 'reviewed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status': 'PASS_INDEPENDENT_SOURCE_AND_EXISTING_VALIDATION_EVIDENCE_REVIEW',
    'reviewer_authored_or_modified_reviewed_sources': False,
    'Lean_kernel_type_axiom_audit_invocations_in_this_review': 0,
    'live_main_P6_frozen_original_manifest_mutations': 0,
    'core_inputs': initial_core,
    'publication_manifest_files_checked': 64,
    'all_manifest_sizes_and_sha256_match_and_remain_unchanged': True,
    'source_plus_five_current_outputs_checked': outputs,
    'source_plus_five_current_outputs_stable_during_review': True,
    'source_declaration_review': rows,
    'existing_source_reuse': [
        {'module': 'ImbalancedChen.P1FourthNearOneKernel',
         'commit': 'c1eb228f281d93e03a6fc231e0086baa9f589036',
         'path': 'verification/parts/p0/p1-near-one-api/candidate.lean',
         'published_sha256': sha(near_published),
         'accepted_member_differs_from_published_only_by_neutral_status_comment': True,
         'repairs': ['Use original suzukiLayer_one_two_odd_nonneg at its actual namespace.',
                     'Specialize original upper_eq_inv at s=2, preserving variable-s left side.'],
         'main_83fc_source_preserved_and_not_validated_as5697_by_this_batch': True},
        {'module': 'ImbalancedChen.P1CoarseFirstCubeFallbackMargin',
         'commit': '3c94ec71e13d038ae661138dac1037116615a20f',
         'path': 'ImbalancedChen/P1CoarseFirstCubeFallbackMargin.lean',
         'published_sha256': sha(fallback_published), 'entire_accepted_source_byte_identical': True,
         'repair': 'Expose log(first actual prime)/log N using existing rank-independent reverse-history index0; no length or positivity premise added.'}],
    'wall_exception_review': {
        'definition': 'wallForm', 'outer_definition_type_unchanged': '(Fin4->Real)->L[Real]Real',
        'four_existing_projection_types_made_explicit': True, 'same_coordinate_weights': [1, 1, 1, 2],
        'raw_definition_body_identical_claimed': False,
        'old_definition_elaborated_successfully': False,
        'old_new_kernel_type_equality_claimed': False,
        'existing_same_typed_projection_pattern': 'P1OriginalCoarseFourthJointGeometry.gateForms, local e(i:Fin4)',
        'added_supplier': ident(supplier), 'supplier_header': supplier_decl['header'],
        'same_exact_actual_log_product_identity_reused_not_reproved': True,
        'Fin_castLE_fix': 'Existing prefix3 projections at0,1,2 normalized explicitly; all new words remain in original admitted-gap proof.',
        'original_domain_and_quantifiers': 'True original initial/fallback or selected Gamma exponent; original firstStop, natural product denominator, reciprocal-prime signed mass. delta0/N0 chosen before all N/cap and omega/smaller delta, with original positive last-prime cutoff.',
        'added_or_strengthened_mathematical_assumption_found': False,
        'original_failed_definition_placeholder_not_treated_as_a_valid_old_proof': True},
    'failed_attempt_evidence': {'aggregate_failures': failure_checks,
                                'wall_attempt1_exit_code': 1, 'wall_attempt1_log': ident(fail_path),
                                'wall_attempt1_candidate_sha256': 'd0572c3de790072433921c023dd92c813bc60c5d532ab074e54e398c26093485',
                                'original_errors_and_failed_candidate_retained_verbatim': True},
    'existing_validation_evidence_not_reexecuted': {
        'normal_exit_codes': [x['exit_code'] for x in validation['normal_commands']],
        'kernel_exit_codes': [x['exit_code'] for x in validation['kernel_commands']],
        'audit_exit_code': validation['audit_command']['exit_code'],
        'actual_source_guard_commands_bound_to_hash_checked_current_trace_argv': True,
        'actual_resource_policy': 'Lean -t0 -j2 -M12288, project maxRecDepth100000/maxHeartbeats4000000',
        'canonical_actual_public_enumeration': True, 'public_export_counts': counts, 'public_total': 118,
        'raw_audit_records_equal_published_export_inventory': True,
        'full_type_expression_elisions_or_sorryAx': False,
        'axiom_report_count': 118, 'only_standard_transitive_axioms': True, 'owned_axiom_declarations': 0},
    'manuscript1106': {
        'directory': '/workspace/chen-imbalanced-semiprimes/paper/release-20261106/en',
        'anchors': ['sieve-appendix.tex41-49 odd cube tests and retained earlier decisions',
                    'sieve-appendix.tex116-126 rank4 upper residual density and F/(2 exp gamma)',
                    'coefficient-appendix.tex20-45 original full/selected squares, admitted cube pays next square',
                    'coefficient-appendix.tex118-126 original coarse margin and fixed-policy strict reserves',
                    'numerical-appendix.tex213 cap19/96 and256-257 second/third fallback entries'],
        'scope': 'Compatibility of already selected manuscript modules; no residual-mean supplier, new cap replacement, weight or arithmetic filter added.'},
    'findings': [],
    'limits': ['Independent static source and existing-record review only, no verification rerun.',
               'NearOne5697 acceptance belongs to selected Member source; distinct canonical main83fc remains preserved and receives no acceptance from this batch.',
               'Wall explicit definition elaboration exception is required; raw old/new definition identity or old elaborated-type equality is not claimed.'],
    'late_addendum_handoff': 'Owner should add this new report and its independent file manifest as a late addendum; do not rewrite original FINAL_RELEASE/PUBLICATION_FILES/VALIDATION_RESULTS or raw logs.',
}
(ROOT / 'INDEPENDENT_REVIEW.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
addition = {'schema': 'member_batch9_independent_review_late_addendum_v1',
            'base_publication_manifest': ident(ROOT / 'PUBLICATION_FILES.json'),
            'base_final_release': ident(ROOT / 'FINAL_RELEASE.json'),
            'files_to_add_separately': [ident(ROOT / 'INDEPENDENT_REVIEW.json'), ident(Path(__file__))],
            'old_manifest_or_raw_records_rewritten': False}
(ROOT / 'INDEPENDENT_REVIEW_FILES.json').write_text(json.dumps(addition, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'report': ident(ROOT / 'INDEPENDENT_REVIEW.json'),
                  'late_addendum': ident(ROOT / 'INDEPENDENT_REVIEW_FILES.json'),
                  'public_exports': 118, 'current_source_plus5_output_files': len(outputs)}, indent=2))
