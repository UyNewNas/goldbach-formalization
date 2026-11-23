from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys
sys.path.insert(0, '/workspace/blue-source-review-utils')
from comment_decls import mask_comments_and_strings

ROOT = Path('/workspace/blue-member-repair-batch21')
BUILD = Path('/workspace/blue-member-build')
MAIN = Path('/workspace/goldbach-formalization')


def sha(b):
    return hashlib.sha256(b).hexdigest()


def identity(p):
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': sha(b)}


def read(p):
    return json.loads(p.read_bytes())


def assignment(masked, start, end):
    stack, pairs = [], {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    i = start
    while i < end:
        c = masked[i]
        if c in '([{⟨':
            stack.append(c)
        elif c in pairs:
            assert stack and stack.pop() == pairs[c]
        elif not stack and masked.startswith(':=', i):
            # There are no top-level let-valued theorem statements in these
            # three files; nested binder/default lets are skipped by depth.
            return i
        i += 1
    raise ValueError('assignment not found')


def declarations(s):
    masked = mask_comments_and_strings(s)
    pattern = re.compile(r'(?m)^(?P<private>private\s+)?'
                         r'(?P<kind>theorem|lemma|def|abbrev|namespace|section|end|open|variable)\b')
    starts = list(pattern.finditer(masked))
    out = []
    for i, m in enumerate(starts):
        if m.group('kind') not in ['theorem', 'lemma', 'def', 'abbrev']:
            continue
        end = starts[i+1].start() if i+1 < len(starts) else len(s)
        cut = assignment(masked, m.end(), end)
        assert not re.search(r'\blet\b', masked[m.end():cut]), 'unexpected header let: inspect explicitly'
        out.append({'name': masked[m.end():].lstrip().split()[0],
                    'kind': m.group('kind'), 'private': bool(m.group('private')),
                    'header': s[m.start():cut+2], 'full': s[m.start():end],
                    'assignment': cut, 'end': end})
    return out


def body(s, name):
    d = next(x for x in declarations(s) if x['name'] == name)
    start, end = d['assignment'], d['end']
    comment = re.search(r'(?m)^/--', s[start:end])
    if comment:
        end = start + comment.start()
    text = s[start:end].rstrip('\r\n') + '\n'
    return start, start + len(text), text


selection = read(ROOT / 'SOURCE_SELECTION.json')
assert set(selection) == {'ImbalancedChen.P4BOuterRampBoundaryUnion',
                          'ImbalancedChen.P1ActualUpperClosedParameterUniformity',
                          'ImbalancedChen.P1HistoricalFourthFullCellIntegral'}
input_paths = [ROOT / 'SOURCE_SELECTION.json', ROOT / 'BEFORE_LOG_SLICES.json',
               ROOT / 'STAGING_CONFIGURATION.json', ROOT / 'EXPECTED_SOURCES.json']
initial = [identity(p) for p in input_paths]
published = subprocess.check_output(['git', 'show',
    '48db3d603d632bc60037e149a55717832e4c04be:ImbalancedChen/P4BOuterRampBoundaryUnion.lean'], cwd=MAIN)
assert sha(published) == 'aed450cac730845f55f48042265b8bb7e95e82332f69940a71313d39bc251fe4'
assert subprocess.check_output(['git', 'cat-file', 'blob', '430e605a85c22f0eea65a59c5c8728d6592c4089'], cwd=MAIN) == published
provenance = read(ROOT / 'P4BOuterRampBoundaryUnion/static-provenance/PROVENANCE.json')
assert (Path('/workspace/blue-member-static-boundary-union/published-reference/ImbalancedChen/P4BOuterRampBoundaryUnion.lean').read_bytes()) == published

local_repairs = {
    'P1ActualUpperClosedParameterUniformity': [
        ('exists_p1_actualSmallRosserPlusDensity_closed_residual_compact_normalized_threshold',
         'exact ⟨hu, hu.trans_le hub, by linarith [hp.2]⟩',
         'exact ⟨hu, hu.trans_le hub, by linarith [show p.1 ≤ 2 * p.2 from hp.2]⟩'),
        ('exists_p1_actualSmallRosserPlusDensity_closed_residual_compact_normalized_threshold',
         'exact ⟨hu, by linarith [hp.2]⟩',
         'exact ⟨hu, by linarith [show 2 * p.2 ≤ p.1 from hp.2]⟩')],
    'P1HistoricalFourthFullCellIntegral': [
        ('integrableOn_fullCellIntegrand',
         'simpa only [extendedWeightedProfile, sub_mul] using',
         'simpa only [Pi.sub_def, extendedWeightedProfile, sub_mul] using'),
        ('fullCellIntegral_eq_raw_single', '  intro t ht\n  rw [extendedProfile_eq_raw_on_joint',
         '  intro t ht\n  dsimp only\n  rw [extendedProfile_eq_raw_on_joint')]}
rows, snapshots, boundary_proofs = [], [], []
for module, chosen in selection.items():
    name = module.split('.')[-1]
    base_path, post_path = ROOT / name / 'baseline.lean', ROOT / name / 'candidate.lean'
    base, post = base_path.read_bytes(), post_path.read_bytes()
    assert sha(base) == chosen['preimage_sha256']
    assert sha(post) == chosen['postimage_sha256']
    bs, ps = base.decode(), post.decode()
    bd, pd = declarations(bs), declarations(ps)
    assert [(x['name'], x['kind'], x['header']) for x in bd] == [
        (x['name'], x['kind'], x['header']) for x in pd]
    assert all(x['full'] == y['full'] for x, y in zip(bd, pd) if x['kind'] in ['def', 'abbrev'])
    if name == 'P4BOuterRampBoundaryUnion':
        replay = bs
        operations = []
        for entry in provenance['extraction']:
            thm = entry['theorem']
            a, z, old_body = body(bs, thm)
            ca, cz, current_body = body(ps, thm)
            pa, pz, pub_body = body(published.decode(), thm)
            assert current_body == pub_body
            pbytes = published[len(published.decode()[:pa].encode()):len(published.decode()[:pz].encode())]
            cbytes = post[len(ps[:ca].encode()):len(ps[:cz].encode())]
            assert pbytes == cbytes
            assert sha(pbytes) == entry['published_body_sha256'] == entry['candidate_body_sha256']
            assert [len(published.decode()[:pa].encode()), len(published.decode()[:pz].encode())] == entry['published_body_byte_range_half_open']
            assert [len(ps[:ca].encode()), len(ps[:cz].encode())] == entry['candidate_body_byte_range_half_open']
            operations.append((a, z, pub_body))
            boundary_proofs.append({'theorem': thm, 'body_sha256': sha(pbytes),
                                     'independently_derived_source_byte_ranges_equal_provenance': True,
                                     'entire_proof_body_byte_exact_to_48db_430e': True})
        for a, z, replacement in sorted(operations, reverse=True):
            replay = replay[:a] + replacement + replay[z:]
        assert replay == ps
        assert re.findall(r'(?m)^import .*', bs) == re.findall(r'(?m)^import .*', ps) == [
            'import ImbalancedChen.ActualUpperCountingInputs', 'import ImbalancedChen.P4BLogGateOuterRamp']
        assert re.findall(r'(?m)^import .*', published.decode()) != re.findall(r'(?m)^import .*', ps)
        assert len([x for x in bd if x['kind'] in ['theorem', 'lemma']]) == 10
    else:
        replay = bs
        for thm, before, after in local_repairs[name]:
            assert replay.count(before) == 1
            d = next(x for x in declarations(replay) if x['name'] == thm)
            offset = replay.index(before)
            assert d['assignment'] < offset < offset + len(before) < d['end']
            replay = replay.replace(before, after, 1)
        assert replay == ps
    member, main = BUILD / ('ImbalancedChen/' + name + '.lean'), MAIN / ('ImbalancedChen/' + name + '.lean')
    assert member.read_bytes() == post and main.read_bytes() == post
    snapshots += [identity(base_path), identity(post_path), identity(member), identity(main),
                  identity(ROOT / name / 'SOURCE_COMPARISON.json')]
    rows.append({'module': module, 'baseline_sha256': sha(base), 'candidate_sha256': sha(post),
                 'current_main_Member_exact_postimage': True,
                 'all_complete_public_private_headers_byte_exact': True,
                 'all_local_raw_definitions_byte_exact': True,
                 'exact_replay_proves_all_other_raw_bytes_unchanged': True,
                 'imports_constants_domains_carriers_hypotheses_quantifiers_unchanged': True,
                 'headers': [{'name': x['name'], 'private': x['private'], 'header': x['header'],
                              'sha256': sha(x['header'].encode())}
                             for x in bd if x['kind'] in ['theorem', 'lemma']],
                 'definitions': [{'name': x['name'], 'raw': x['full'], 'sha256': sha(x['full'].encode())}
                                 for x in bd if x['kind'] in ['def', 'abbrev']]})

failures = []
for module, entry in read(ROOT / 'BEFORE_LOG_SLICES.json').items():
    raw = Path(entry['original_running_log']).read_bytes()[entry['raw_byte_start']:entry['raw_byte_end_exclusive']]
    assert raw == (ROOT / entry['slice']).read_bytes() and sha(raw) == entry['raw_sha256']
    assert b'error:' in raw
    failures.append({'module': module, 'slice': identity(ROOT / entry['slice']),
                     'matches_original_aggregate2_raw_byte_span': True})
for item in initial + snapshots:
    assert identity(Path(item['path'])) == item
pending = [n for n in ['VALIDATION_RESULTS.json', 'FINAL_RELEASE.json', 'PUBLICATION_FILES.json'] if not (ROOT / n).exists()]
report = {
    'schema': 'independent_batch21_three_module_source_only_prepared_review_v1',
    'status': 'PREPARED_SOURCE_REVIEW_ONLY_PENDING_OWNER_VALIDATION_AND_FINAL_CHAIN',
    'reviewer': '/root/retained_reuse', 'reviewed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'reviewer_source_authorship': False, 'Lean_kernel_type_axiom_invocations': 0,
    'live_main_P6_frozen_source_or_old_record_mutations': 0,
    'request_path_correction': 'Actual batch20 is OrderedReciprocal; this review covers actual batch21 BoundaryUnion and its2P1 companions only. No batch20 acceptance or14public count is reused.',
    'source_inputs': initial, 'immutable_source_snapshots_for_future_hash_only_binding': snapshots,
    'modules': rows,
    'complete_theorem_headers': sum(len(x['headers']) for x in rows),
    'raw_definition_count': sum(len(x['definitions']) for x in rows),
    'boundary_existing_work': {'published_commit': '48db3d603d632bc60037e149a55717832e4c04be',
                               'published_blob': '430e605a85c22f0eea65a59c5c8728d6592c4089',
                               'published_whole_sha256': sha(published),
                               'whole_source_not_installed_due_import_difference': True,
                               'four_proofs': boundary_proofs,
                               'source_family_ActualUpperCountingInputs_retained': True},
    'mathematical_review': {
        'BoundaryUnion': 'Same strict gates0<G; literal arithmetic strips -width<G<=0 include zero walls and strict lower edge. Finite natural carrier, empty gate case, ramp laws[0,1], unchanged ActualUpperCountingInputs source family/cutoff; hpaid remains actual strip-cardinality premise. No null-volume or asymptotic payment substituted. Original forall delta>0 before eventuallyN/evenN kept, and arbitrary width generic statements retain their exact hypotheses.',
        'UpperClosedParameterUniformity': 'Only expose the existing membership inequalities p1<=2p2 and2p2<=p1 to linarith. Same closed residual u<=beta, exact cube cutoff/density normalization, compact T, threshold N0 before all targets/parameters/caps, actual quotient N^lambda/P and same singular series. No positive margin above residual1 added.',
        'HistoricalFourthFullCellIntegral': 'Only pointwise function subtraction and beta reduction. Same actual common historical T3 joint cell, Ico mesh, old4/cap4 levels, original levelCheck premise, signed profile difference and reciprocal weight. Max-one extension used off admitted set only; original gates prove strict legality on joint cell. No whole-box margin or cap replacement added.',
        'new_mathematical_estimates_assumptions_or_quantifier_changes_found': False,
        'declaration_definition_exception_found': False},
    'manuscript1106': {'directory': '/workspace/chen-imbalanced-semiprimes/paper/release-20261106/en',
        'anchors': ['argument.tex601-625 smooth endpoint with absolute arithmetic boundary/exact-coprime payment',
                    'sieve-appendix.tex41-49 original odd cube tests and retained ancestor decisions',
                    'sieve-appendix.tex116-126 rank4 old/new normalized upper residual density',
                    'coefficient-appendix.tex108-126 retain equality chambers and freeze finite causal decisions before children'],
        'scope': 'Existing finite boundary payment and source-implemented closed-parameter/full-cell identities, not a new analytic supplier or full-board acceptance.'},
    'raw_failures': failures,
    'validation_status': {'normal': 'PENDING_OWNER_RESULT', 'kernel': 'PENDING_OWNER_RESULT',
                          'actual_public_type_axiom_enumeration': 'PENDING_OWNER_RESULT',
                          'current_source5outputs_expected_hash_binding': 'PENDING_VALIDATION_RECEIPT',
                          'missing_release_files_at_capture': pending,
                          'accepted_public_declaration_count_claimed': None,
                          'no_verification_success_assertion_from_source_review': True},
    'findings': [],
    'next_step': 'After owner completion, preserve this prepared source review, compare recorded source SHA only, and add a final validation/hash/log-chain binding. If a source changes, inspect only the real delta before accepting it. No normal/kernel/audit rerun.'}
path = ROOT / 'INDEPENDENT_REVIEW.PREPARED.json'
assert not path.exists(), 'prepared snapshot already exists; preserve it'
path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'prepared': identity(path), 'headers': report['complete_theorem_headers'],
                  'raw_definitions': report['raw_definition_count'], 'pending': pending}, indent=2))
