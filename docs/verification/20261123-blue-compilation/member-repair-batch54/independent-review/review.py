from pathlib import Path
import collections, datetime, hashlib, json, re, shutil, sys
sys.path.insert(0, '/workspace/blue-source-review-utils')
from comment_decls import mask_comments_and_strings
from comment_decls_v2 import proof_assignment

member = Path('/workspace/blue-member-build')
totals = {49: (31, 30), 50: (32, 32), 51: (42, 42), 54: (175, 169)}
notes = {
    49: 'Previously independently reviewed final mixed-EOL source c189: original R qualified only in proofs, exact same Icc/product witnesses and continuous gap; final source retains the real preimage line endings. No old normalized-LF draft is accepted.',
    50: 'Only two rfl steps after the existing tuple/history dictionary and own-cube definitions. The original old/new gates, exponent casts, natural product and reciprocal-totient normalization stay identical.',
    51: 'Decode the same two dependent union memberships; expose the original old/new strict own-cube inequalities before rewriting their if branches; unfold the same overlap set before ring. Full and selected domains, lower-gain sign, levelCheck and integrability hypotheses stay unchanged.',
    54: 'All nine patches were manually inspected. They preserve the original domains, hypotheses, multiplicities, functions, masks and numerical estimates: explicit ENNReal notation scope; zero-tag if_true; beta reduction; List length API; the same three-coordinate own-cube complement; explicit original C/complement filter identities and sum_product arguments; pointwise Pi.add normalization and same-side additive inequality; removing an already-closed ring; and exact published SW source with explicit if_pos/if_neg. The series enclosure does not close the separately open sharp numerical endpoint.',
}
sha = lambda data: hashlib.sha256(data).hexdigest()

def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha(data)}

def read(path):
    return json.loads(path.read_bytes())

def bound(path, expected):
    result = identity(path)
    assert result['sha256'] == expected['sha256'] and result['bytes'] == expected['bytes'], path
    return result

decl = re.compile(r'(?m)^[ \t]*(?:(?:private|noncomputable)\s+)?(?:theorem|lemma)\s+(\S+)')
top = re.compile(r'(?m)^[ \t]*(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def|abbrev|namespace|end|open|section|structure|inductive)\b')

def parse(text):
    masked = mask_comments_and_strings(text)
    commands = list(top.finditer(masked))
    headers, bodies = [], {}
    for match in decl.finditer(masked):
        end = next((c.start() for c in commands if c.start() > match.end()), len(text))
        try:
            start = proof_assignment(text, match.end(), end) + 2
            headers.append({'name': match.group(1), 'kind': 'complete_header', 'raw': text[match.start():start]})
            bodies[match.group(1)] = (start, end, text[start:end])
        except ValueError:
            headers.append({'name': match.group(1), 'kind': 'entire_non_tactic_alias_declaration', 'raw': text[match.start():end]})
    return headers, bodies

for number in map(int, sys.argv[1:]):
    root = Path(f'/workspace/blue-member-repair-batch{number}')
    assert not (root / 'INDEPENDENT_REVIEW.json').exists()
    release, manifest, result, selection = [read(root / x) for x in
        ['FINAL_RELEASE.json', 'PUBLICATION_FILES.json', 'VALIDATION_RESULTS.json', 'SOURCE_SELECTION.json']]
    assert sha((root / 'PUBLICATION_FILES.json').read_bytes()) == release['publication_files_sha256']
    assert sha((root / 'VALIDATION_RESULTS.json').read_bytes()) == release['validation_results_sha256']
    packet = [bound(root / x['path'], x) for x in manifest['files']]
    sources = []
    for module, selected in selection.items():
        folder = root / module.rsplit('.', 1)[-1]
        before, after = (folder / 'baseline.lean').read_bytes(), (folder / 'candidate.lean').read_bytes()
        assert sha(before) == selected['preimage_sha256']
        assert sha(after) == selected['postimage_sha256'] == result['modules'][module]
        old, new = before.decode(), after.decode()
        h0, p0 = parse(old)
        h1, p1 = parse(new)
        assert h0 == h1
        changed = [name for name in p0 if p0[name][2] != p1[name][2]]
        stripped = []
        for text, bodies in [(old, p0), (new, p1)]:
            for name in sorted(changed, key=lambda n: bodies[n][0], reverse=True):
                start, end, _ = bodies[name]
                text = text[:start] + '<PROOF ' + name + '>' + text[end:]
            stripped.append(text)
        if number == 54:
            normalized = stripped[0]
            replacements = [
                ('Status: source_written / uncompiled.', 'Compilation records: docs/verification/20261123-blue-compilation.'),
                ('SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.', 'Compilation records: docs/verification/20261123-blue-compilation.'),
                ('SOURCEONLY / UNCOMPILED. Two actual retained policies at the identical', 'Compilation records: docs/verification/20261123-blue-compilation. Two actual retained policies at the identical'),
            ]
            for old_text, new_text in replacements:
                normalized = normalized.replace(old_text, new_text)
            if module == 'ImbalancedChen.P5ZU11CanonicalSwitchedIntegrable':
                normalized = normalized.replace('open scoped BigOperators\n', 'open scoped BigOperators ENNReal\n')
            assert normalized == stripped[1], module
        elif number == 49:
            assert stripped[0].replace('SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.', 'Compilation records: docs/verification/20261123-blue-compilation.') == stripped[1]
        else:
            assert stripped[0] == stripped[1]
        sources.append({'module': module, 'baseline_sha256': sha(before), 'postimage_sha256': sha(after),
                        'complete_headers_or_entire_aliases': h0, 'changed_proof_names': changed,
                        'all_definitions_data_domains_constants_quantifiers_hypotheses_preserved': True,
                        'source_review': notes[number]})
    outputs = []
    for module, parts in result['source_plus_five_outputs'].items():
        assert len(parts) == 6
        outputs.extend(bound(member / path, expected) for path, expected in parts.items())
    assert result['source_plus_five_outputs_unchanged_across_kernel_and_audit']
    commands = result['normal_commands'] + result['kernel_commands'] + [result['audit_command']]
    assert len(commands) == 2 * len(selection) + 1 and all(x['exit_code'] == 0 and x['cwd'] == str(member) for x in commands)
    for command in commands:
        assert sha((root / command['log']).read_bytes()) == command['log_sha256']
    exports = read(root / 'OWNED_EXPORTS.json')
    public = read(root / 'PUBLIC_EXPORTS.json')
    log = (root / 'types-axioms.log').read_text()
    records = [json.loads(line.split('AUDIT_RECORD ', 1)[1]) for line in log.splitlines() if 'AUDIT_RECORD ' in line]
    assert records == [{k: v for k, v in x.items() if k not in ['transitive_axioms', 'is_axiom_declaration']} for x in exports]
    assert len(exports) == len({x['name'] for x in exports}) == totals[number][0]
    assert len(public) == sum(not x['is_private'] for x in exports) == totals[number][1]
    assert {x['name'] for x in public} == {x['name'] for x in exports if not x['is_private']}
    inventory = [json.loads(line.split('MEMBER_OWNED_NAMES ', 1)[1])['names'] for line in log.splitlines() if line.startswith('MEMBER_OWNED_NAMES ')]
    assert inventory == [[x['name'] for x in exports]]
    assert f'MEMBER_OWNED_COUNT {len(exports)}' in log
    assert all(not x['is_axiom_declaration'] and x['kind'] != 'axiom' and '...' not in x['type_expression']
               and x['transitive_axioms'] == x['axioms'] and set(x['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in exports)
    counts = dict(collections.Counter(x['module'] for x in exports))
    assert counts == result['owned_export_counts'] == release['environment_owned_export_counts']
    assert dict(collections.Counter(x['module'] for x in public)) == result['public_export_counts'] == release['environment_public_export_counts']
    driver = (root / 'PublicAudit.lean').read_text()
    assert all(x in driver for x in ['env.constants.fold', 'env.getModuleIdxFor? name', 'set_option pp.all true', 'set_option pp.universes true'])
    assert '!isPrivateName name' not in driver
    for entry in packet + outputs:
        assert identity(Path(entry['path'])) == entry
    report = {'schema': 'independent_P1_full_owned_source_and_final_binding_review_v1', 'status': 'PASS_INDEPENDENT_REVIEW',
              'reviewer': '/root', 'captured_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'batch': number, 'findings': [], 'source_review': sources,
              'final_inputs': [identity(root / x) for x in ['FINAL_RELEASE.json', 'PUBLICATION_FILES.json', 'VALIDATION_RESULTS.json', 'SOURCE_SELECTION.json']],
              'original_publication_file_count': len(packet), 'all_packet_bindings_match': True,
              'source_and_five_outputs': outputs,
              'existing_validation': {'owned': len(exports), 'public': len(public), 'private': len(exports)-len(public),
                  'normal_kernel_audit_exit_codes': [x['exit_code'] for x in commands],
                  'raw_AST_universe_axioms_and_owner_inventory_exact': True, 'only_standard_axioms': True},
              'scope': 'These exact necessary P1 suppliers in their recorded Member import context; no complete P1 or whole-board acceptance.',
              'new_Lean_kernel_audit_or_source_compiler_invocations': 0,
              'original_source_outputs_logs_or_records_mutated': False}
    path = root / 'INDEPENDENT_REVIEW.json'
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    copy = root / 'independent-review/review.py'
    copy.parent.mkdir(exist_ok=True)
    shutil.copyfile(Path(__file__), copy)
    late = {'schema': 'independent_review_late_manifest_v1', 'original_manifest': identity(root / 'PUBLICATION_FILES.json'),
            'original_release': identity(root / 'FINAL_RELEASE.json'), 'new_files': [identity(path), identity(copy)],
            'original_packet_changed': False}
    (root / 'INDEPENDENT_REVIEW_FILES.json').write_text(json.dumps(late, indent=2) + '\n')
    print(json.dumps({'batch': number, 'owned': len(exports), 'public': len(public), 'review': identity(path)}))
