#!/usr/bin/env python3
"""Verify only source identity, extraction boundaries, and overlay scope."""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(value, message):
    if not value:
        raise AssertionError(message)


def code_only(text):
    """Remove nested Lean comments and string contents for token scanning."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    require(not depth and not string, 'unterminated comment/string')
    return ''.join(out)


def main():
    path = ROOT / 'OVERLAY_MANIFEST.json'
    require(path.is_file(), 'candidate manifest missing; extraction not generated')
    manifest = json.loads(path.read_text())
    require(manifest['status'] == 'UNCOMPILED_STATIC_CANDIDATE', 'incorrect status')
    require(len(manifest['overlay']) == 2, 'scope exceeds extension + consumer')
    ext = ROOT / manifest['extension']['candidate_path']
    data = ext.read_bytes()
    require(sha(data) == manifest['extension']['sha256'], 'extension SHA mismatch')
    require(len(manifest['declarations']) == 18, 'expected 18 declarations')
    public = [r for r in manifest['declarations'] if r['visibility'] == 'public']
    private = [r for r in manifest['declarations'] if r['visibility'] == 'private']
    require(len(public) == 11 and len(private) == 7, 'public/private count mismatch')
    require(sum(r['role'] == 'existing_private_helper' for r in private) == 6,
            'six existing private helpers required')
    names = [r['name'] for r in manifest['declarations']]
    require(len(set(names)) == len(names), 'duplicate declaration')
    source_checks = {}
    for row in manifest['declarations']:
        source_path = ROOT / row['source_snapshot']
        source = source_path.read_bytes()
        require(sha(source) == row['source_file_sha256'], 'source snapshot changed')
        start, end = row['source_byte_range_half_open']
        original = source[start:end]
        cstart, cend = row['candidate_byte_range_half_open']
        copied = data[cstart:cend]
        require(copied == original, row['name'] + ': declaration bytes changed')
        require(sha(original) == row['declaration_sha256'], 'declaration SHA mismatch')
        split = original.index(b':=') + 2
        require(sha(original[:split]) == row['header_sha256'], 'header SHA mismatch')
        require(sha(original[split:]) == row['proof_body_sha256'], 'body SHA mismatch')
        start_line = source[:start].count(b'\n') + 1
        end_line = source[:end].count(b'\n')
        require([start_line, end_line] == row['source_lines_inclusive'],
                'source line range mismatch')
        require(row['source_public_commit'] == manifest['published_commit'],
                'declaration has unexpected public commit')
        source_checks[row['name']] = {'declaration_sha256': sha(original),
                                     'byte_exact': True}
    code = code_only(data.decode())
    actual = re.findall(r'(?m)^(?:(private) )?theorem\s+(\w+)', code)
    require([name for _, name in actual] == names, 'untracked declaration/code')
    require(sum(not flag for flag, _ in actual) == 11, 'public declarations mismatch')
    forbidden = re.findall(r'\b(?:axiom|sorry|admit|native_decide|unsafe|extern|'
                           r'implemented_by|run_tac|elab|macro)\b|#(?:eval|reduce)', code)
    require(not forbidden, 'forbidden proof shortcut: ' + repr(forbidden))
    require(not re.search(r'(?m)^(?:noncomputable )?def\b', code),
            'extension unexpectedly defines mathematical data')
    # Every copied private helper used by another copied proof is declared first.
    private_names = {r['name'] for r in private}
    seen = set()
    for row in manifest['declarations']:
        a, b = row['candidate_byte_range_half_open']
        body = code_only(data[a:b].decode()).split(':=', 1)[1]
        refs = {n for n in private_names if re.search(r'\b' + n + r'\b', body)}
        require(refs <= seen, row['name'] + ': private helper unavailable at use')
        seen.add(row['name'])
    baseline = (ROOT / manifest['consumer']['baseline_snapshot']).read_bytes()
    consumer = (ROOT / manifest['consumer']['candidate_path']).read_bytes()
    prefix = manifest['consumer']['new_import_prefix'].encode()
    require(len(baseline) == 4333, 'unexpected consumer baseline length')
    require(consumer == prefix + baseline, 'consumer change exceeds import prefix')
    require(sha(baseline) == manifest['consumer']['baseline_sha256'],
            'consumer baseline SHA mismatch')
    require(sha(consumer) == manifest['consumer']['candidate_sha256'],
            'consumer candidate SHA mismatch')
    boundary_checks = {}
    for row in manifest['unchanged_boundaries']:
        snapshot = (ROOT / row['snapshot']).read_bytes()
        require(sha(snapshot) == row['sha256'], 'unchanged snapshot SHA mismatch')
        live = Path(row['live_path'])
        require(live.read_bytes() == snapshot, 'live boundary changed: ' + str(live))
        boundary_checks[row['label']] = row['sha256']
    old_names = set(manifest['legacy_provider_public_names'])
    require(not (old_names & {r['name'] for r in public}),
            'extension shadows existing public declaration')
    require(manifest['extension']['imports'] ==
            ['MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform'],
            'extension import scope changed')
    require(manifest['overlay'][0]['operation'] == 'create_missing_only',
            'extension would overwrite another source')
    require(manifest['overlay'][1]['operation'] == 'replace_exact_baseline_only',
            'consumer overwrite lacks exact baseline gate')
    # The one omitted new public theorem is not a dependency of any copied block.
    # Check against all additions in the full published supplier snapshots.
    all_additions = set()
    for source_path in sorted({r['source_snapshot'] for r in manifest['declarations']}):
        published = (ROOT / source_path).read_text()
        relative = source_path.split('research/wu2008/src/', 1)[1]
        old = (ROOT / 'baseline' / relative).read_text()
        decl_pattern = r'(?m)^(?:private )?theorem\s+(\w+)'
        all_additions.update(set(re.findall(decl_pattern, published)) -
                             set(re.findall(decl_pattern, old)))
    missing_additions = all_additions - set(names)
    require(missing_additions == {'buchstabPrimeKernel_abel_unrestricted'},
            'unexpected omitted published declaration')
    for row in manifest['declarations']:
        a, b = row['candidate_byte_range_half_open']
        body = code_only(data[a:b].decode()).split(':=', 1)[1]
        require(not any(re.search(r'\b' + n + r'\b', body) for n in missing_additions),
                row['name'] + ': missing dependency on omitted published declaration')
    value = {'status': 'STATIC_IDENTITY_CHECKS_PASS_UNCOMPILED',
             'manifest_sha256': sha(path.read_bytes()),
             'extension_sha256': sha(data),
             'public_declarations': 11, 'private_declarations': 7,
             'existing_private_helpers_included_in_private_count': 6,
             'declarations_bound_byte_exact_to_public_sources': source_checks,
             'consumer_original_4333_bytes_retained': True,
             'unchanged_live_boundary_sha256': boundary_checks,
             'forbidden_code_tokens': forbidden,
             'omitted_published_new_declarations_not_referenced': sorted(missing_additions),
             'compiler_or_kernel_invoked': False,
             'compiler_acceptance_claimed': False}
    (ROOT / 'STATIC_VERIFICATION.json').write_text(json.dumps(value, indent=2) + '\n')
    print(json.dumps({k: v for k, v in value.items() if k not in
                      ['declarations_bound_byte_exact_to_public_sources',
                       'unchanged_live_boundary_sha256']}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (AssertionError, OSError, ValueError, KeyError) as exc:
        print('STATIC CHECK FAILED: ' + str(exc), file=sys.stderr)
        raise SystemExit(1)
