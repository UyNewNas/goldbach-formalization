"""Read-only advisory import-header census, independent of runtime v1.

Follows the pinned Lean 4.33 header grammar (module, prelude, public/meta
import, import all), including implicit Init imports. An unqualified import
in a module is private unless public; private import is also recognized as
an unsupported explicit spelling and reported, not silently certified valid.
This is a source walk, not recorded-object import inspection or kernel replay.
No Lean process, compiler, cache installation, or PASS cache mutation occurs.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import json
import re
import subprocess

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]
STD = Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux')
PROVIDERS = Path('/home/slava/codex-lean-ve/native-packages')


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def uncomment(text):
    """Header-only lexer: retain whitespace while removing nested comments."""
    code, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
            code.append(' ')
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
            code.append(' ')
        elif depth:
            if text[i] == '\n':
                code.append('\n')
            i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            if end == -1:
                break
            i = end
        else:
            code.append(text[i])
            i += 1
    return ''.join(code)


def header_imports(text):
    tokens = uncomment(text).lstrip('\ufeff').split()
    i, is_module, prelude, result, flags = 0, False, False, [], []
    if i < len(tokens) and tokens[i] == 'module':
        is_module = True
        i += 1
    if i < len(tokens) and tokens[i] == 'prelude':
        prelude = True
        i += 1
    while i < len(tokens):
        start, visibility, meta = i, None, False
        if tokens[i] in ('public', 'private'):
            visibility = tokens[i]
            i += 1
        if i < len(tokens) and tokens[i] == 'meta':
            meta = True
            i += 1
        if i >= len(tokens) or tokens[i] != 'import':
            i = start
            break
        i += 1
        all_data = i < len(tokens) and tokens[i] == 'all'
        if all_data:
            i += 1
        if i >= len(tokens):
            raise ValueError('Unterminated import')
        name = tokens[i]
        if not re.fullmatch(r'[^\W\d][\w\u00b7\u2080-\u2089\u2070-\u2079\u1d62\u1d63\u2090-\u209c\u03b1-\u03c9.\u00ab\u00bb\u0027]*', name):
            raise ValueError('Unsupported module identifier: ' + repr(name))
        i += 1
        result.append({'module': name, 'is_meta': meta, 'import_all': all_data,
                       'is_exported': visibility == 'public' or not is_module,
                       'explicit_visibility': visibility, 'implicit': False})
        if visibility == 'private':
            flags.append('Explicit private import is not in pinned Lean grammar')
        if not is_module and (visibility is not None or meta or all_data):
            flags.append('New module import modifier without module header')
    if not prelude:
        result = [{'module': 'Init', 'is_meta': False, 'import_all': False,
                   'is_exported': False, 'explicit_visibility': None, 'implicit': True},
                  {'module': 'Init', 'is_meta': True, 'import_all': False,
                   'is_exported': False, 'explicit_visibility': None, 'implicit': True}] + result
    return {'module_header': is_module, 'prelude': prelude, 'imports': result,
            'parser_findings': flags}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--target', action='append', default=[])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    report = {'status': 'READ_ONLY_ADVISORY_SOURCE_HEADER_CENSUS',
              'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'script_sha256': digest(Path(__file__)),
              'scope': 'Source header walk including module/public/meta/import-all and implicit Init; not recorded-object graph or kernel replay',
              'no_compiler_invoked': True, 'no_cache_mutated': True,
              'cache_upgrade_authorized': False,
              'pinned_header_grammar': {str(p.relative_to(STD)): digest(p) for p in [
                  STD / 'src/lean/Lean/Parser/Module/Syntax.lean',
                  STD / 'src/lean/Lean/Elab/Import.lean']},
              'providers': [], 'project_direct_comparison': [], 'walks': []}
    for package in packages:
        directory = PROVIDERS / package['name']
        rev = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        tracked = subprocess.run(['git', '-C', str(directory), 'diff', '--quiet', 'HEAD', '--']).returncode
        untracked = subprocess.check_output(['git', '-C', str(directory), 'ls-files', '--others', '--exclude-standard', '*.lean'], text=True).splitlines()
        report['providers'].append({'name': package['name'], 'pinned_rev': package['rev'],
            'actual_rev': rev, 'head_matches_pin': rev == package['rev'],
            'tracked_tree_clean': tracked == 0, 'untracked_lean_files': untracked})
    spec = importlib.util.spec_from_file_location('frozen_runtime_v1', STATE / 'runtime.py')
    old = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(old)
    report['runtime_v1_sha256'] = digest(STATE / 'runtime.py')
    results, paths = {}, {}
    def locate(name):
        if name not in paths:
            rel = Path(name.replace('.', '/')).with_suffix('.lean')
            if name == 'ImbalancedChen' or name.startswith('ImbalancedChen.'):
                candidate = ROOT / rel
            else:
                candidate = next((PROVIDERS / p['name'] / rel for p in packages
                                  if (PROVIDERS / p['name'] / rel).is_file()), STD / 'src/lean' / rel)
            paths[name] = candidate if candidate.is_file() else None
        return paths[name]
    def read(name):
        if name not in results:
            path = locate(name)
            results[name] = header_imports(path.read_text()) if path else None
        return results[name]
    for path in sorted((ROOT / 'ImbalancedChen').rglob('*.lean')):
        name = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        head = read(name)
        old_deps = old.imports(path)
        explicit = list(dict.fromkeys(x['module'] for x in head['imports'] if not x['implicit']))
        missed = sorted(set(explicit) - set(old_deps))
        spurious = sorted(set(old_deps) - set(explicit))
        cache = STATE / 'cache' / (name + '.json')
        if missed or spurious or head['module_header'] or head['parser_findings']:
            report['project_direct_comparison'].append({'module': name, 'source_sha256': digest(path),
                'v1_direct_imports': old_deps, 'v2_explicit_imports': explicit,
                'v1_missed_explicit_imports': missed, 'v1_spurious_imports': spurious,
                'header': head, 'has_development_cache_record': cache.exists()})
    for target in args.target:
        seen, unresolved, findings, nodes, public_count = set(), [], [], [], 0
        def visit(name):
            nonlocal public_count
            if name in seen:
                return
            seen.add(name)
            head = read(name)
            if head is None:
                unresolved.append(name)
                return
            if head['parser_findings']:
                findings.append({'module': name, 'findings': head['parser_findings']})
            public_count += sum(x['explicit_visibility'] == 'public' for x in head['imports'])
            for entry in head['imports']:
                visit(entry['module'])
            nodes.append({'module': name, 'source': str(locate(name)),
                          'source_sha256': digest(locate(name)), 'header': head})
        visit(target)
        report['walks'].append({'target': target, 'resolved_source_nodes': len(nodes),
            'public_import_edges': public_count, 'unresolved_modules': unresolved,
            'parser_findings': findings, 'nodes': nodes})
    report['all_provider_heads_and_tracked_sources_pin_clean'] = all(
        x['head_matches_pin'] and x['tracked_tree_clean'] for x in report['providers'])
    report['project_explicit_dependency_mismatches'] = [x['module'] for x in report['project_direct_comparison']
        if x['v1_missed_explicit_imports'] or x['v1_spurious_imports']]
    report['cache_scope_correction'] = (
        'v1 recursively missed public/meta/import-all and implicit Init provider edges. '
        'Provider pins and tracked-source cleanliness are reported separately; no complete recursive object alignment is claimed. '
        'Existing inherited objects remain development cache only and are not upgraded by this census. '
        'Actual source compilation, stock owned replay, and full owned type/axiom results are separate evidence.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(args.output), 'project_mismatches': report['project_explicit_dependency_mismatches'],
                     'providers_pin_clean': report['all_provider_heads_and_tracked_sources_pin_clean'],
                     'walk_counts': {x['target']: x['resolved_source_nodes'] for x in report['walks']}}))


if __name__ == '__main__':
    main()
