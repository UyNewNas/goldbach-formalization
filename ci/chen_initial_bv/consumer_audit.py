#!/usr/bin/env python3
"""Owned static/source/artifact gates. This file never fetches or runs Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

HERE = Path(__file__).resolve().parent
PLAN = json.loads((HERE / 'owned-closure.json').read_text())
FOREIGN = json.loads((HERE.parent / 'external_bv/closure.json').read_text())


def need(ok, message):
    if not ok:
        raise SystemExit(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blob(path):
    raw = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def scrub(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\' and i+1 < len(text): out.extend('  '); i += 2
            elif text[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i); end = len(text) if end < 0 else end
            out.extend(' ' * (end-i)); i = end
        elif text[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(text[i]); i += 1
    need(depth == 0 and not string, 'Unterminated source comment/string')
    return ''.join(out)


def imports(text):
    result = []
    for line in scrub(text).splitlines():
        if re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\b', line):
            match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_. ]+)\s*', line)
            need(match is not None, f'Unsupported import syntax: {line}')
            result.extend(match.group(1).split())
    return result


def validate_sources(consumer):
    need(len(FOREIGN['modules']) == 270 and len(FOREIGN['architectModules']) == 9,
         'Wrong existing foreign closure counts')
    need(sha256(HERE.parent / 'external_bv/closure.json') == PLAN['foreignClosureSha256'],
         'Foreign reviewed closure bytes changed')
    for rel, expected in PLAN['coreConfigBlobs'].items():
        need(blob(consumer / rel) == expected, f'Pinned core config changed: {rel}')
    for row in PLAN['sources']:
        path = consumer / row['source']
        need(path.is_file() and not path.is_symlink(), f'Missing regular source: {path}')
        need(sha256(path) == row['sha256'], f'Owned source changed: {path}')
        need(blob(path) == row['gitBlob'], f'Owned source blob changed: {path}')
        need(imports(path.read_text()) == row['imports'], f'Owned imports changed: {path}')
        if row['kind'] != 'audit-tool':
            code = scrub(path.read_text())
            need(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC|#eval|\brun_cmd\b|\brun_elab\b|\binitialize\b|IO\.(?:Process|FS)', code),
                 f'Unreviewed proof escape/runtime token: {path}')
    known = {row['module'] for row in PLAN['sources']}
    edges = {row['module']: row['imports'] for row in PLAN['sources']}
    visited, foreign_refs, boundary = set(), set(), set()
    def visit(module):
        if module in visited: return
        visited.add(module)
        for dep in edges[module]:
            if dep in known: visit(dep)
            elif dep in FOREIGN['modules']: foreign_refs.add(dep)
            else:
                need(dep.startswith(('Mathlib.', 'Lean.', 'Init.', 'Std.')),
                     f'Unapproved additional import: {dep}')
                boundary.add(dep)
    visit('ChenInitialBVProbe')
    need(visited == known, 'Extra/missing owned module in closure')
    need(foreign_refs == {FOREIGN['supplierModule']}, 'Changed foreign entry roots')
    need(sorted(boundary) == PLAN['boundaryImports'], 'Changed trusted dependency boundary')


def stage(consumer, root, out):
    validate_sources(consumer)
    for row in PLAN['sources']:
        dst = root / row['destination']
        need(not dst.exists() and not dst.is_symlink(), f'Stage collision: {dst}')
    for row in PLAN['sources']:
        dst = root / row['destination']; dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(consumer / row['source'], dst)
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(HERE / 'owned-closure.json', out / 'owned-closure.json')
    (out / 'owned-build-modules.txt').write_text('\n'.join(PLAN['topologicalOrder']) + '\n')
    print(f"STAGED_OWNED_CORE={PLAN['coreModuleCount']} ADAPTER=1 AUDIT_PROBE=1")


def after(consumer, root, out):
    validate_sources(consumer)
    gate = json.loads((out / 'cold-gate.json').read_text())
    built = []
    for row in PLAN['sources']:
        need(sha256(root / row['destination']) == row['sha256'], 'Staged source changed')
        p = root / '.lake/build/lib/lean' / (row['module'].replace('.', '/') + '.olean')
        need(p.is_file() and not p.is_symlink(), f'Missing compiled owned module: {p}')
        need(p.stat().st_mtime_ns >= gate['time_ns'], f'Artifact predates cold gate: {p}')
        built.append({'module':row['module'],'sha256':sha256(p),'bytes':p.stat().st_size})
    replay = list(FOREIGN['modules']) + [r['module'] for r in FOREIGN['architectModules']]
    replay += ['ColdBVProbe'] + PLAN['topologicalOrder']
    need(len(replay) == len(set(replay)) == PLAN['replayModuleCount'], 'Replay count mismatch')
    main_oleans = root / '.lake/build/lib/lean'
    main_seen = {str(p.relative_to(main_oleans))[:-6].replace('/', '.') for p in main_oleans.rglob('*.olean')}
    need(main_seen == set(FOREIGN['modules']) | {'ColdBVProbe'} | set(PLAN['topologicalOrder']),
         'Unexpected/missing root-project compiled module')
    arch_oleans = root / '.lake/packages/LeanArchitect/.lake/build/lib/lean'
    arch_seen = {str(p.relative_to(arch_oleans))[:-6].replace('/', '.') for p in arch_oleans.rglob('*.olean')}
    need(arch_seen == {r['module'] for r in FOREIGN['architectModules']},
         'Unexpected/missing Architect compiled module')
    (out / 'replay-modules.txt').write_text('\n'.join(replay)+'\n')
    (out / 'owned-built-artifacts.json').write_text(json.dumps(built,indent=2)+'\n')
    log = (out / 'chen-initial-bv-build.log').read_text()
    module_lines = re.findall(r'\bBV_IMPORTED_MODULE (\S+)$', log, re.M)
    seen = set(module_lines)
    for row in PLAN['sources']:
        if row['module'] != 'ChenInitialBVProbe':
            need(row['module'] in seen, f'Owned module missing from loaded environment: {row["module"]}')
    actual_foreign = {m for m in seen if m.split('.')[0] in {'MathlibNt','AnalyticNumberTheory','PrimeNumberTheoremAnd','Architect'}}
    expected_foreign = set(FOREIGN['modules']) | {r['module'] for r in FOREIGN['architectModules']}
    need(actual_foreign == expected_foreign, 'Loaded foreign closure is not exactly 270+9')
    need(re.search(r'\bBV_OWNED_AXIOM_AUDIT_PASS declarations=[1-9][0-9]* modules=39$',log,re.M),
         'Missing nonempty successful full owned/transitive axiom audit')
    need('sorryAx' not in log, 'sorryAx in consumer audit output')
    (out / 'loaded-imports.json').write_text(json.dumps(sorted(seen),indent=2)+'\n')
    print(f"PASS: unchanged 279 foreign modules; {len(built)} newly compiled owned modules; {len(replay)} replay roots")


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('mode',choices=['stage','after'])
    parser.add_argument('consumer',type=Path);parser.add_argument('root',type=Path);parser.add_argument('out',type=Path)
    a=parser.parse_args(); {'stage':stage,'after':after}[a.mode](a.consumer,a.root,a.out)
