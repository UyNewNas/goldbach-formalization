#!/usr/bin/env python3
"""Check exact source reuse and declaration separation; not a Lean acceptance."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(name):
    return json.loads((HERE / name).read_bytes())


def blob(digest):
    return subprocess.check_output(['git', 'cat-file', 'blob', digest], cwd=ROOT)


def repaired_source_preimages():
    """Verify exact reported repairs, then expose the frozen extraction originals."""
    repair = read('FIRST_COMPILE_REPAIRS.json')
    need(repair['failed_source_commit'] == '1a259e113c0977c8cb2814492ff3bd6ab7cdc475',
         'failed-source anchor differs')
    expected_paths = {
        'ImbalancedChen/P1OriginalSingletonPointwiseData.lean',
        'ImbalancedChen/P1Full87TrueDPolicyDelta.lean',
    }
    need({r['path'] for r in repair['files']} == expected_paths and
         len(repair['files']) == 2, 'repair selection differs')
    originals = {}
    for row in repair['files']:
        original = blob(repair['failed_source_commit'] + ':' + row['path'])
        need(sha(original) == row['before']['sha256'] and
             len(original) == row['before']['bytes'], 'repair preimage differs')
        parts, previous = [], 0
        for splice in row['exact_byte_splices']:
            start, end = splice['pre_start_byte'], splice['pre_end_byte']
            need(previous <= start < end <= len(original) and
                 original[start:end] == splice['old_utf8'].encode(), 'repair splice differs')
            parts.extend([original[previous:start], splice['new_utf8'].encode()])
            previous = end
        parts.append(original[previous:])
        after = b''.join(parts)
        need(sha(after) == row['after']['sha256'] and len(after) == row['after']['bytes'] and
             (ROOT / row['path']).read_bytes() == after, 'repair postimage differs')
        originals[row['path']] = original
    return originals


def extraction(source, target, postimage, common_import):
    raw = blob(source['git_blob'])
    need(sha(raw) == source['sha256'] and len(raw) == source['bytes'], 'origin differs')
    remaining = raw
    for row in source['declarations']:
        body = raw[row['source_start_byte']:row['source_end_byte']]
        need(len(body) == row['bytes'] and sha(body) == row['sha256'], 'declaration bytes differ')
        need(target.count(body) == 1, 'separated declaration not unique: ' + row['name'])
    for row in sorted(source['declarations'], key=lambda x: x['source_start_byte'], reverse=True):
        remaining = remaining[:row['source_start_byte']] + remaining[row['source_end_byte']:]
    post = (common_import + '\n').encode() + remaining
    need((ROOT / postimage['path']).read_bytes() == post, 'complementary provider differs')
    need(sha(post) == postimage['sha256'] and len(post) == postimage['bytes'], 'postimage binding differs')


def main():
    original_sources = repaired_source_preimages()
    reuse = read('P3_REUSE.json')
    need(reuse['counts']['new_canonical_paths'] == 19, 'P3 selection differs')
    for row in reuse['canonical_additions']:
        raw = blob(row['git_blob'])
        need(sha(raw) == row['sha256'], 'P3 source pin differs')
        need((ROOT / row['path']).read_bytes() == raw, 'P3 adopted source differs')

    pointwise = read('POINTWISE_EXTRACTION.json')
    target = original_sources[pointwise['destination']]
    need(sha(target) == pointwise['destination_sha256'], 'pointwise destination differs')
    for source in pointwise['sources']:
        extraction(source, target, source['provider_postimage'],
                   'import ImbalancedChen.P1OriginalSingletonPointwiseData')
    need(sum(len(x['declarations']) for x in pointwise['sources']) == 18, 'pointwise selection differs')

    historical = read('HISTORICAL_POINTWISE_EXTRACTION.json')
    target = (ROOT / historical['destination']).read_bytes()
    need(sha(target) == historical['destination_sha256'], 'historical destination differs')
    extraction({'git_blob': historical['origin_git_blob'], 'sha256': historical['origin_sha256'],
                'bytes': historical['origin_bytes'], 'declarations': historical['declarations']},
               target, historical['provider_postimage'],
               'import ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData')
    need(len(historical['declarations']) == 3, 'historical selection differs')

    for row in read('TRUE_D_ADOPTION.json')['sources']:
        raw = blob(row['origin_git_blob'])
        need(sha(raw) == row['origin_sha256'] and len(raw) == row['origin_bytes'], 'TrueD origin differs')
        expected = raw
        if row['module'] == 'ImbalancedChen.P1Full87TrueDUnitBound':
            old = b'import ImbalancedChen.P1Full87TrueDThreeBookNetInvoice\n'
            need(raw.startswith(old), 'TrueD original header differs')
            expected = b'import ImbalancedChen.P1Full87TrueDPolicyDelta\n' + raw[len(old):]
        installed = original_sources.get(row['installed_path'])
        if installed is None:
            installed = (ROOT / row['installed_path']).read_bytes()
        need(installed == expected and sha(installed) == row['installed_sha256'] and
             len(installed) == row['installed_bytes'], 'TrueD installed source differs')

    closure = read('SOURCE_CLOSURE.json')
    need(not closure['missing'], 'project source missing')
    for module, row in closure['project_sources'].items():
        need(row['path'] == module.replace('.', '/') + '.lean', 'source path differs')
        raw = (ROOT / row['path']).read_bytes()
        need(sha(raw) == row['sha256'], 'closure source differs: ' + module)
        imports = [x for line in re.findall(r'^import\s+([^\n\r]+)', raw.decode(), re.M)
                   for x in line.split() if x.startswith('ImbalancedChen.')]
        need(imports == row['imports'], 'closure imports differ: ' + module)
        need(set(imports) <= closure['project_sources'].keys(), 'closure is incomplete')
    reached = set()
    def visit(module):
        if module in reached:
            return
        reached.add(module)
        for child in closure['project_sources'][module]['imports']:
            visit(child)
    for module in closure['targets']:
        visit(module)
        raw = (ROOT / closure['project_sources'][module]['path']).read_text()
        need(not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^axiom\b', raw, re.M),
             'forbidden declaration/tactic token in selected source')
    need(reached == set(closure['project_sources']), 'closure contains unrelated project sources')
    print(json.dumps({'status': 'SOURCE_REUSE_AND_EXTRACTION_VERIFIED_NOT_LEAN_ACCEPTANCE',
                      'p3_reused_sources': 19, 'original_extracted_declarations_verified': 21,
                      'current_unchanged_extracted_declarations': 20,
                      'expression_repaired_extracted_declarations': 1,
                      'redundant_tactic_removals_in_existing_true_d_provider': 2,
                      'selected_owners': len(closure['targets']), 'project_sources': len(reached)}))


if __name__ == '__main__':
    main()
