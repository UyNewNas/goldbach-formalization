from pathlib import Path
import collections
import datetime
import hashlib
import json
import re
import shlex
import subprocess
import sys
sys.path.insert(0, str(Path(__file__).parent))
from comment_decls import mask_comments_and_strings
from comment_decls_v2 import proof_assignment

R = Path('/workspace/blue-member-repair-batch17')
B = Path('/workspace/blue-member-build')
M = Path('/workspace/goldbach-formalization')
NAME = 'P2HistoricQ80OrdinaryEstimatorSoundness'
MODULE = 'ImbalancedChen.' + NAME
REL = 'ImbalancedChen/' + NAME + '.lean'


def read(p):
    return json.loads(p.read_bytes())


def sha(b):
    return hashlib.sha256(b).hexdigest()


def identity(p):
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': sha(b)}


def bind(p, expected):
    got = identity(p)
    assert got['bytes'] == expected['bytes'] and got['sha256'] == expected['sha256'], p
    return got


core = [identity(R / n) for n in ['FINAL_RELEASE.json', 'PUBLICATION_FILES.json',
                                'VALIDATION_RESULTS.json', 'SOURCE_SELECTION.json']]
release, manifest, val, sel = [read(Path(x['path'])) for x in core]
assert release['publication_files_sha256'] == core[1]['sha256']
assert release['validation_results_sha256'] == core[2]['sha256']
assert len(manifest['files']) == 28
packet_files = [bind(R / x['path'], x) for x in manifest['files']]
sel = sel[MODULE]
base = (R / NAME / 'baseline.lean').read_bytes()
post = (R / NAME / 'candidate.lean').read_bytes()
assert sha(base) == sel['preimage_sha256']
assert sha(post) == sel['postimage_sha256'] == val['modules'][MODULE]
assert sha(post) == '7d941caf8eca9a5647b7c7e9221c8fa63e614ef37bef170f9d1bf211b95f3d43'
assert (B / REL).read_bytes() == (M / REL).read_bytes() == post
published_base = subprocess.check_output(['git', 'cat-file', 'blob',
                                        '1cfac7c07af49e5f0b645a2f5c6fe620acb7abaa'], cwd=M)
assert published_base == base

command_pattern = re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)?'
                             r'(?P<private>private\s+)?'
                             r'(?P<kind>theorem|lemma|def|abbrev|namespace|section|end|open|variable)\b')


def declarations(s):
    masked = mask_comments_and_strings(s)
    commands = list(command_pattern.finditer(masked))
    result = []
    for i, match in enumerate(commands):
        if match.group('kind') not in ['theorem', 'lemma', 'def', 'abbrev']:
            continue
        end = commands[i+1].start() if i+1 < len(commands) else len(s)
        name = masked[match.end():].lstrip().split()[0]
        kind = match.group('kind')
        cut = (proof_assignment(s, match.end(), end) if kind in ['theorem', 'lemma']
               else masked.index(':=', match.end(), end))
        header = s[match.start():cut+2]
        result.append({'name': name, 'kind': kind, 'private': bool(match.group('private')),
                       'start': match.start(), 'assignment': cut, 'end': end,
                       'header': header, 'full': s[match.start():end]})
    return result


bs, ps = base.decode(), post.decode()
bd, pd = declarations(bs), declarations(ps)
assert [(x['name'], x['kind'], x['header']) for x in bd] == [
    (x['name'], x['kind'], x['header']) for x in pd]
theorems = [x for x in bd if x['kind'] in ['theorem', 'lemma']]
assert len(theorems) == 23 and sum(x['private'] for x in theorems) == 6
definitions = [x for x in bd if x['kind'] in ['def', 'abbrev']]
assert len(definitions) == 7
for left, right in zip(bd, pd):
    if left['kind'] in ['def', 'abbrev']:
        assert left['full'] == right['full'], left['name']

repairs = read(R / NAME / 'static-provenance/STATIC_RECEIPT.json')['changes']
assert len(repairs) == 5 and len({x['theorem'] for x in repairs}) == 4
replayed = bs
for change in repairs:
    assert replayed.count(change['old']) == 1
    d = next(x for x in declarations(replayed) if x['name'] == change['theorem'])
    at = replayed.index(change['old'])
    assert d['assignment'] < at and at + len(change['old']) < d['end']
    replayed = replayed.replace(change['old'], change['new'], 1)
assert replayed.encode() == (R / NAME / 'static-candidate-before-owner-comment.lean').read_bytes()
for change in sel['neutral_status_text_replacements']:
    assert replayed.count(change['before']) == change['count']
    replayed = replayed.replace(change['before'], change['after'])
assert replayed == ps
assert re.findall(r'(?m)^import .*', bs) == re.findall(r'(?m)^import .*', ps)

outputs = [bind(B / path, exp) for path, exp in val['source_plus_five_outputs'][MODULE].items()]
assert len(outputs) == 6
failure_info = read(R / 'BEFORE_LOG_SLICES.json')[MODULE]
raw = Path(failure_info['original_running_log']).read_bytes()[
    failure_info['raw_byte_start']:failure_info['raw_byte_end_exclusive']]
assert raw == (R / failure_info['slice']).read_bytes()
assert sha(raw) == failure_info['raw_sha256'] and b'(155s)' in raw
assert len(re.findall(rb'(?m)^error: ImbalancedChen/', raw)) == 5
commands = val['normal_commands'] + val['kernel_commands'] + [val['audit_command']]
assert len(commands) == 3 and all(x['exit_code'] == 0 for x in commands)
for cmd in commands:
    assert sha((R / cmd['log']).read_bytes()) == cmd['log_sha256']
    assert cmd['cwd'] == str(B)
    assert cmd['argv'][:4] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
                              '/workspace/blue-build-tools/runtime-evidence/state.json']
runtime = read(R / 'ACTUAL_RUNTIME_COMMANDS.json')
assert len(runtime['actual_compiler_commands']) == 2
for path, event in runtime['actual_compiler_commands'].items():
    assert event['cwd'] == str(B) and event['tool'] == 'lean'
    assert event['sysroot'] == '/workspace/blue-build-tools/runtime/p0-ci-shadow-toolchain'
    assert event['command'][:4] == [event['sysroot'] + '/bin/lean-runtime', '-t0', '-j2', '-M12288']
    assert path in event['input_args']
    assert '-DmaxRecDepth=100000' in event['input_args'] and '-DmaxHeartbeats=4000000' in event['input_args']
    if path == str(R / 'PublicAudit.lean'):
        assert event['input_args'] == val['audit_command']['argv'][7:]
    else:
        assert path == str(B / REL)
        trace = read(B / ('.lake/build/lib/lean/ImbalancedChen/' + NAME + '.trace'))
        lines = [x['message'] for x in trace['log'] if x['message'].startswith('.> LEAN_PATH=')]
        assert len(lines) == 1
        tokens = shlex.split(lines[0][3:])
        index = tokens.index(event['sysroot'] + '/bin/lean')
        assert tokens[index+1:] == event['input_args']

exports = read(R / 'PUBLIC_EXPORTS.json')
log = (R / 'types-axioms.log').read_text()
records = [json.loads(line.split('AUDIT_RECORD ', 1)[1]) for line in log.splitlines()
           if 'AUDIT_RECORD ' in line]
assert len(exports) == len(records) == 54
assert records == [{k: v for k, v in x.items() if k != 'transitive_axioms'} for x in exports]
assert len({x['name'] for x in exports}) == 54
assert dict(collections.Counter(x['module'] for x in exports)) == {MODULE: 54}
assert all(not x['is_axiom_declaration'] for x in exports)
assert all('...' not in x['type_expression'] and 'sorryAx' not in x['type_expression'] for x in exports)
ax = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
noax = re.findall(r"'([^']+)' does not depend on any axioms", log)
assert len(ax) + len(noax) == 54
am = {n: {re.sub(r'\.\{[^}]*\}$', '', x.strip()) for x in a.split(',')} for n, a in ax}
am.update({n: set() for n in noax})
assert all(set(x['transitive_axioms']) == am[x['name']] for x in exports)
assert all(a <= {'propext', 'Classical.choice', 'Quot.sound'} for a in am.values())
audit = (R / 'PublicAudit.lean').read_text()
assert 'env.constants.fold' in audit and 'env.getModuleIdxFor? name' in audit
assert '!isPrivateName name' in audit and 'set_option pp.all true' in audit
assert 'AUDIT_FINISHED 54' in log

for item in core + packet_files + outputs:
    assert identity(Path(item['path'])) == item

report = {
    'schema': 'independent_batch17_ordinary_estimator_review_v1',
    'reviewer': '/root/retained_reuse', 'reviewed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status': 'PASS_INDEPENDENT_STATIC_SOURCE_AND_EXISTING_VALIDATION_REVIEW',
    'reviewer_was_source_author': False,
    'Lean_kernel_type_axiom_invocations_in_this_review': 0,
    'actual_sources_or_original_packet_manifest_raw_records_edited': False,
    'core_inputs': core, 'publication_manifest_files_checked': 28,
    'all_manifest_and_current_source_plus5_output_sha256_sizes_match': True,
    'original_records_and6_actual_source_outputs_stable_during_review': True,
    'current_source_outputs': outputs,
    'source': {'module': MODULE, 'baseline_sha256': sha(base), 'accepted_sha256': sha(post),
               'Member_and_main_current_match_accepted': True,
               'baseline_is_exact_existing_git_blob': '1cfac7c07af49e5f0b645a2f5c6fe620acb7abaa',
               'theorem_header_count': 23, 'public': 17, 'private': 6,
               'all23_complete_headers_byte_exact': True, 'all7_raw_definitions_byte_exact': True,
               'five_exact_API_replacements_within4_original_proofs': True,
               'all_other_raw_bytes_unchanged_except_registered_neutral_comment': True,
               'all_import_routes_and_current_R03_I80_core_owner_retained': True,
               'no_data_row_banks_cutoffs_numeric_constants_changed': True,
               'headers': [{'name': x['name'], 'private': x['private'], 'header': x['header'],
                            'sha256': sha(x['header'].encode())} for x in theorems],
               'definitions': [{'name': x['name'], 'private': x['private'], 'raw': x['full'],
                                'sha256': sha(x['full'].encode())} for x in definitions],
               'header_method': 'Nested-comment/string aware offsets; balanced delimiters; top-level tactic proof := by, not first nested :=. No Lean elaboration.',
               'before_CRLF': base.count(b'\r\n'), 'after_CRLF': post.count(b'\r\n')},
    'repair_review': [
        {'theorem': 'affineRange_real_enclosure', 'API_changes': 2,
         'result': 'Universal add_le_add fixes requested addition side; same p.c, signed affine edges and closed-rectangle bounds.'},
        {'theorem': 'weightedIntegral_affine', 'API_changes': 1,
         'result': 'Beta reduction only before existing exact logarithmic inner-integral identity.'},
        {'theorems': ['ordinary_base_real_sound', 'ordinary_chord_real_sound'], 'API_changes': 2,
         'result': 'Existing ordinaryA_pos explicitly proves unchanged multiplier4/ordinaryA nonnegative; no new premise.'}],
    'mathematical_scope_review': {
        'integral_measure': 'Exact dt du/(t*u), realMass=log(tr/tl)*log(ur/ul); no area substitution.',
        'base_and_chord': 'Same monotone lower-factor base; true concavity only above2; plane minorant, range, positive span/divisor and both lower endpoint licences retained.',
        'saved_estimator': 'Same max of monotone base and legal concave chords, never sum of chords. High branch25/128, ordinaryA/source a and Q80 decode retained.',
        'actual_h_licence': 'Original delta/domain, local hlow<=actual h(endpoint), and actual h-composition inner/outer integrability premises remain; no licence inferred from numeric bank replay.',
        'query_licences': 'Original sf/logI enclosure hypotheses and chordEligible conditional positive I80 denominator guards remain exact.',
        'quantifiers': 'All original quantifiers and any inherited thresholds unchanged; no added N0/cap/family/positivity assumptions.',
        'new_estimate_or_substantive_proof_gap_found': False,
        'declaration_or_definition_syntax_exception_needed': False},
    'manuscript1106': {'directory': '/workspace/chen-imbalanced-semiprimes/paper/release-20261106/en',
        'anchors': ['numerical-appendix.tex94-102 directed arithmetic',
                    'numerical-appendix.tex103-176 exact log interval series, ordinary lower numerator concavity and positive logarithmic chord weights',
                    'numerical-appendix.tex841-886 residual R, logarithmic M/M_R, ordinary base/chord max and separately licensed finite-h lower estimator',
                    'argument.tex708-730 closed-cell choices/common refinement']},
    'original_failure': {'raw_slice': identity(R / failure_info['slice']),
                         'matches_original_aggregate2_exact_byte_span': True,
                         'elapsed_label': '155s', 'actual_error_count': 5,
                         'failure_kinds': ['2addition-side API mismatches', '1integrand beta rewrite', '2nonnegativity tactic inference'],
                         'original_failure_retained_verbatim': True},
    'existing_validation_not_reexecuted': {
        'normal_exit_code': 0, 'kernel_exit_code': 0, 'public_audit_exit_code': 0,
        'all3_log_hashes_match': True,
        'actual_normal_guard_argv_matches_current_hash_checked_trace': True,
        'actual_audit_guard_argv_matches_audit_command': True,
        'actual_resource_policy': 'Lean-t0/-j2/-M12288; project maxRecDepth100000/maxHeartbeats4000000',
        'canonical_environment_owner_enumeration': True, 'full_type_AST_records': 54,
        'all_raw_type_AST_and_axiom_records_match_published_export_inventory': True,
        'unexpected_axioms_or_owned_axiom_declarations_or_sorryAx': False,
        'only_standard_transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound']},
    'findings': [],
    'late_addendum_handoff': 'Add this new independent review separately; do not rewrite original FINAL_RELEASE/PUBLICATION_FILES/VALIDATION_RESULTS or raw logs. No successful test rerun was requested or performed.'}
(R / 'INDEPENDENT_REVIEW.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
files = [identity(R / 'INDEPENDENT_REVIEW.json'), identity(Path(__file__)),
         identity(Path(__file__).parent / 'comment_decls.py'),
         identity(Path(__file__).parent / 'comment_decls_v2.py')]
addendum = {'schema': 'batch17_independent_review_late_addendum_v1',
            'original_final_release': core[0], 'original_publication_manifest': core[1],
            'new_files_to_add_separately': files, 'original_records_changed': False}
(R / 'INDEPENDENT_REVIEW_FILES.json').write_text(json.dumps(addendum, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'report': identity(R / 'INDEPENDENT_REVIEW.json'),
                  'late_addendum': identity(R / 'INDEPENDENT_REVIEW_FILES.json'),
                  'complete_headers': 23, 'raw_definitions': 7, 'public_AST': 54}, indent=2))
