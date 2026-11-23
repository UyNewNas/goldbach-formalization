from pathlib import Path
import collections, datetime, hashlib, json, re, sys
sys.path.insert(0, '/workspace/blue-source-review-utils')
from comment_decls import mask_comments_and_strings
from comment_decls_v2 import proof_assignment

member = Path('/workspace/blue-member-build')
main = Path('/workspace/goldbach-formalization')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
totals = {30: 22, 31: 97, 32: 47, 33: 21, 36: 24}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha(data)}

def read(path):
    return json.loads(path.read_bytes())

def bind(path, expected):
    result = identity(path)
    assert result['sha256'] == expected['sha256'] and result['bytes'] == expected['bytes'], path
    return result

top = re.compile(r'(?m)^(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def|abbrev|namespace|end|open|section|noncomputable section)\b')
theorems = re.compile(r'(?m)^(?P<private>private\s+)?(?:theorem|lemma)\s+(?P<name>[^\s({:]+)')

def parse(text):
    masked = mask_comments_and_strings(text)
    commands = list(top.finditer(masked))
    headers, bodies = [], {}
    for match in theorems.finditer(masked):
        start = proof_assignment(text, match.end(), len(text)) + 2
        end = next((c.start() for c in commands if c.start() > start), len(text))
        header = text[match.start():start]
        headers.append({'name': match.group('name'), 'private': bool(match.group('private')),
                        'header': header, 'sha256': sha(header.encode())})
        bodies[match.group('name')] = (start, end, text[start:end])
    return headers, bodies

def strip_bodies(text, bodies, names):
    for name in sorted(names, key=lambda n: bodies[n][0], reverse=True):
        start, end, _ = bodies[name]
        text = text[:start] + '<TACTIC-BODY ' + name + '>\n' + text[end:]
    return text

for number in map(int, sys.argv[1:]):
    root = Path(f'/workspace/blue-member-repair-batch{number}')
    assert not (root / 'INDEPENDENT_REVIEW.json').exists()
    release, manifest, results, selection = [read(root / n) for n in
        ['FINAL_RELEASE.json', 'PUBLICATION_FILES.json', 'VALIDATION_RESULTS.json', 'SOURCE_SELECTION.json']]
    assert sha((root / 'PUBLICATION_FILES.json').read_bytes()) == release['publication_files_sha256']
    assert sha((root / 'VALIDATION_RESULTS.json').read_bytes()) == release['validation_results_sha256']
    packet = [bind(root / x['path'], x) for x in manifest['files']]
    sources, current_outputs = [], []
    for module, source in selection.items():
        folder = root / module.rsplit('.', 1)[-1]
        baseline, candidate = (folder / 'baseline.lean').read_bytes(), (folder / 'candidate.lean').read_bytes()
        assert sha(baseline) == source['preimage_sha256']
        assert sha(candidate) == source['postimage_sha256'] == results['modules'][module]
        before, after = baseline.decode(), candidate.decode()
        headers0, bodies0 = parse(before)
        headers1, bodies1 = parse(after)
        assert headers0 == headers1, module
        changed = [name for name in bodies0 if bodies0[name][2] != bodies1[name][2]]
        assert strip_bodies(before, bodies0, changed) == strip_bodies(after, bodies1, changed), module
        definitions = []
        commands = list(top.finditer(mask_comments_and_strings(before)))
        for i, command in enumerate(commands):
            if re.match(r'(?:noncomputable\s+)?(?:def|abbrev)\b', before[command.start():]):
                end = commands[i+1].start() if i+1 < len(commands) else len(before)
                definitions.append({'raw': before[command.start():end], 'sha256': sha(before[command.start():end].encode())})
        live = [identity(tree / (module.replace('.', '/') + '.lean')) for tree in [member, main]]
        assert all(x['sha256'] == sha(candidate) for x in live)
        sources.append({'module': module, 'preimage_sha256': sha(baseline), 'postimage_sha256': sha(candidate),
                        'complete_headers': headers0, 'raw_definitions': definitions, 'changed_proof_names': changed,
                        'all_bytes_outside_changed_proof_bodies_exact': True, 'current_source_bindings': live,
                        'new_assumptions_or_semantic_definition_changes': False,
                        'review_basis': 'All patch hunks were manually inspected; changes only expose existing arguments, definitions, algebra or nonnegativity for the current API.'})
    for module, parts in results['source_plus_five_outputs'].items():
        assert len(parts) == 6
        current_outputs.extend(bind(member / p, e) for p, e in parts.items())
    assert results['source_plus_five_outputs_unchanged_across_kernel_and_audit']
    commands = results['normal_commands'] + results['kernel_commands'] + [results['audit_command']]
    assert len(commands) == 2*len(selection)+1 and all(x['exit_code'] == 0 for x in commands)
    for command in commands:
        assert command['cwd'] == str(member)
        assert sha((root / command['log']).read_bytes()) == command['log_sha256']
    exports = read(root / 'PUBLIC_EXPORTS.json')
    log = (root / 'types-axioms.log').read_text()
    records = [json.loads(line.split('AUDIT_RECORD ', 1)[1]) for line in log.splitlines() if 'AUDIT_RECORD ' in line]
    assert records == [{k: v for k, v in x.items() if k != 'transitive_axioms'} for x in exports]
    assert len(exports) == len({x['name'] for x in exports}) == totals[number]
    counts = dict(collections.Counter(x['module'] for x in exports))
    assert counts == results['public_export_counts'] == release['environment_public_export_counts']
    axioms = {name: {re.sub(r'\.\{[^}]*\}$', '', value.strip()) for value in values.split(',')}
              for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)}
    axioms.update({name: set() for name in re.findall(r"'([^']+)' does not depend on any axioms", log)})
    assert set(axioms) == {x['name'] for x in exports}
    assert all(not x['is_axiom_declaration'] and '...' not in x['type_expression']
               and set(x['transitive_axioms']) == axioms[x['name']] <= allowed for x in exports)
    driver = (root / 'PublicAudit.lean').read_text()
    assert all(s in driver for s in ['env.constants.fold', 'env.getModuleIdxFor? name', '!isPrivateName name', 'set_option pp.all true'])
    assert f'AUDIT_FINISHED {len(exports)}' in log
    for entry in packet + current_outputs:
        assert identity(Path(entry['path'])) == entry
    report = {'schema': 'independent_p1_shared_prerequisite_review_v1', 'status': 'PASS_INDEPENDENT_REVIEW',
              'reviewer': '/root', 'reviewed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'batch': number, 'source_review': sources, 'findings': [],
              'release_and_manifest': [identity(root / n) for n in ['FINAL_RELEASE.json', 'PUBLICATION_FILES.json', 'VALIDATION_RESULTS.json', 'SOURCE_SELECTION.json']],
              'original_packet_file_count': len(packet), 'all_manifest_size_sha256_bindings_match': True,
              'source_plus_five_outputs': current_outputs,
              'existing_validation': {'public_export_counts': counts, 'total_public_exports': len(exports),
                  'normal_kernel_audit_exit_codes': [x['exit_code'] for x in commands],
                  'all_command_log_hashes_match': True, 'full_AST_equals_raw_log': True,
                  'transitive_axioms_equal_raw_log': True, 'only_standard_axioms': True},
              'scope': 'Exact accepted Member prerequisites also used by the selected modern P1 source closure; no complete-P1 or whole-board claim.',
              'reviewer_Lean_kernel_audit_stock_or_compiler_invocations': 0,
              'original_source_log_trace_or_validation_record_edits': 0}
    output = root / 'INDEPENDENT_REVIEW.json'
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    addition = {'schema': 'independent_review_publication_addendum_v1', 'batch': number,
                'original_release': identity(root / 'FINAL_RELEASE.json'),
                'original_manifest': identity(root / 'PUBLICATION_FILES.json'),
                'new_files': [identity(output), identity(Path(__file__))], 'original_packet_changed': False}
    (root / 'INDEPENDENT_REVIEW_FILES.json').write_text(json.dumps(addition, indent=2) + '\n')
    print(json.dumps({'batch': number, 'public_exports': len(exports), 'review': identity(output),
                      'changed_proof_names': {x['module']: x['changed_proof_names'] for x in sources}}))
