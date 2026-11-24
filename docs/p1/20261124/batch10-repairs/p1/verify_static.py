from pathlib import Path
import re, json, hashlib, subprocess, os
ROOT = Path('/workspace/scratch/638a86a3af73')
REPO = ROOT / 'goldbach-p1'
OUT = Path(__file__).resolve().parent
SOURCE_COMMIT = 'e44e941df0a4cdf126fc0a0c41df3abd7637d1e8'
RX = re.compile(r'^(?:(?:private|protected|noncomputable|unsafe)\s+)*(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|structure|inductive|instance)\s+(?P<name>[^\s(:]+)', re.M)
COMMAND = re.compile(r'^(?:import\b|namespace\b|end(?:\s|$)|open\b|section\b|noncomputable section\b|variable\b|attribute\b|set_option\b)', re.M)
def inspect(source):
    decls = list(RX.finditer(source))
    cuts = sorted(set([m.start() for m in decls] + [m.start() for m in COMMAND.finditer(source)] + [len(source)]))
    headers, definitions, proofs, names = {}, {}, [], []
    for decl in decls:
        end = next(x for x in cuts if x > decl.start())
        segment = source[decl.start():end]
        kind, name = decl['kind'], decl['name']
        names.append((kind, name))
        if kind in ('theorem', 'lemma'):
            assert ':=' in segment, (name, 'missing assignment')
            offset = segment.index(':=') + 2
            headers[name] = segment[:offset]
            proofs.append((decl.start() + offset, end, name))
        else:
            definitions[name] = segment
    parts, cursor = [], 0
    for start, end, name in proofs:
        parts.extend([source[cursor:start], '<PROOF:' + name + '>'])
        cursor = end
    parts.append(source[cursor:])
    return names, headers, definitions, ''.join(parts), proofs

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\x00' + data).hexdigest()

checks = []
for row in json.loads((OUT / 'EDIT_OPERATIONS.json').read_text()):
    original = subprocess.check_output(['git', 'show', SOURCE_COMMIT + ':' + row['relative_path']], cwd=REPO)
    before = (REPO / row['relative_path']).read_bytes()
    after = (OUT / row['relative_path']).read_bytes()
    assert before == original, (row['module'], 'canonical preimage changed')
    assert hashlib.sha256(before).hexdigest() == row['before_sha256']
    assert hashlib.sha256(after).hexdigest() == row['after_sha256']
    old, new = inspect(before.decode()), inspect(after.decode())
    assert old[:4] == new[:4], (row['module'], 'contract/definition/outside-proof mismatch')
    rebuilt = before.decode()
    for op in row['operations']:
        assert rebuilt.count(op['before']) == op['count']
        rebuilt = rebuilt.replace(op['before'], op['after'])
        prefix = len(os.path.commonprefix([op['before'], op['after']]))
        suffix = len(os.path.commonprefix([op['before'][prefix:][::-1], op['after'][prefix:][::-1]]))
        for match in re.finditer(re.escape(op['before']), before.decode()):
            changed_start = match.start() + prefix
            changed_end = match.end() - suffix
            assert any(start <= changed_start <= changed_end <= end for start, end, _ in old[4]), (row['module'], 'change outside proof')
    assert rebuilt.encode() == after
    additions = '\n'.join(op['after'] for op in row['operations'])
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option|autoImplicit', additions)
    log_path = ROOT / 'context-recovery/batch9-module-errors' / (row['module'].split('.')[-1] + '.log')
    log = log_path.read_bytes()
    assert hashlib.sha256(log).hexdigest() == row['error_log_sha256']
    record = {k:v for k,v in row.items() if k != 'operations'}
    record.update({
        'before_git_blob_sha1': blob(before), 'after_git_blob_sha1': blob(after),
        'actual_error_count': len(re.findall(rb'^error: ImbalancedChen/', log, re.M)),
        'declaration_order_unchanged': True, 'theorem_header_count': len(old[1]),
        'definition_count': len(old[2]), 'all_theorem_headers_byte_identical': True,
        'all_definition_blocks_byte_identical': True, 'outside_theorem_proof_bodies_byte_identical': True,
        'before_CRLF_count': before.count(b'\r\n'), 'after_CRLF_count': after.count(b'\r\n'),
        'imports_unchanged': True, 'proof_only_changes': True,
        'lean_validation': 'NOT_RUN_PENDING_ROOT_NORMAL'})
    checks.append(record)
    print(row['module'], 'headers', len(old[1]), 'definitions', len(old[2]), 'errors', record['actual_error_count'], 'proof-only OK')
result = {'schema': 'p1-batch10-six-candidates-contract-check-v1', 'source_commit': SOURCE_COMMIT,
          'checks': checks, 'static_checks_only': True, 'lean_or_cloud_executed': False,
          'canonical_modified': False}
(OUT / 'CONTRACT_CHECK.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
