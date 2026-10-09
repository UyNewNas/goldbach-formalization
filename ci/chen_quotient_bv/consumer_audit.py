#!/usr/bin/env python3
"""Owned read/source/artifact/log gates. Never fetch or run Lean, Lake or foreign code."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

HERE = Path(__file__).resolve().parent
PLAN = json.loads((HERE / 'owned-closure.json').read_text())
FOREIGN = json.loads((HERE.parent / 'external_bv/closure.json').read_text())
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
TRUSTED_PREFIXES = {'Mathlib', 'Lean', 'Lake', 'Init', 'Std', 'Batteries', 'Aesop', 'Qq',
                    'ProofWidgets', 'Plausible', 'ImportGraph', 'Cli', 'LeanSearchClient'}


def need(ok, message):
    if not ok:
        raise SystemExit(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blob(path):
    raw = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def write(out, name, value):
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_text(json.dumps(value, indent=2) + '\n')


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


def regular(path, boundary):
    need(path.is_file() and not path.is_symlink(), f'Missing regular file: {path}')
    need(boundary == path or boundary in path.parents, f'Outside boundary: {path}')
    need(not any(p.is_symlink() for p in [boundary, *path.parents] if p == boundary or boundary in p.parents),
         f'Symlink parent: {path}')


def validate_sources(consumer):
    need(len(FOREIGN['modules']) == 270 and len(FOREIGN['architectModules']) == 9,
         'Wrong existing foreign closure counts')
    need(sha256(HERE.parent / 'external_bv/closure.json') == PLAN['foreignClosureSha256'],
         'Foreign reviewed closure bytes changed')
    for rel, expected in PLAN['preservedCoreBlobs'].items():
        p = consumer / rel; regular(p, consumer)
        need(blob(p) == expected, f'Base root/core workflow/config changed: {rel}')
    license = consumer / PLAN['license']['source']; regular(license, consumer)
    need(blob(license) == PLAN['license']['gitBlob'] and sha256(license) == PLAN['license']['sha256'], 'Missing/changed adjacent upstream license')
    for rel, row in PLAN['unchangedAuditSupport'].items():
        p = consumer / rel; regular(p, consumer)
        need(blob(p) == row['gitBlob'] and sha256(p) == row['sha256'], f'Unchanged audit support changed: {rel}')
    need(len(PLAN['sources']) == PLAN['ownedBuildModuleCount'] == 47, 'Wrong owned build count')
    need(len(PLAN['auditedModules']) == PLAN['ownedProofModuleCount'] == 46, 'Wrong owned audit count')
    for row in PLAN['sources']:
        for key in ('source', 'destination'):
            path = Path(row[key]); need(not path.is_absolute() and '..' not in path.parts, 'Unsafe manifest path')
        p = consumer / row['source']; regular(p, consumer)
        need(sha256(p) == row['sha256'] and blob(p) == row['gitBlob'], f'Owned source changed: {p}')
        need(imports(p.read_text()) == row['imports'], f'Owned imports changed: {p}')
        if row['kind'] != 'audit-tool':
            need(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC|#eval|\brun_cmd\b|\brun_elab\b|\binitialize\b|IO\.(?:Process|FS)', scrub(p.read_text())),
                 f'Unreviewed proof escape/runtime token: {p}')
    known = {row['module'] for row in PLAN['sources']}
    need(len(known) == len(PLAN['sources']), 'Duplicate owned module')
    edges = {row['module']: row['imports'] for row in PLAN['sources']}
    visited, active, foreign_refs, boundary, order = set(), set(), set(), set(), []
    def visit(module):
        need(module not in active, 'Cyclic owned imports')
        if module in visited: return
        active.add(module)
        for dep in edges[module]:
            if dep in known: visit(dep)
            elif dep in FOREIGN['modules']: foreign_refs.add(dep)
            else:
                need(dep.startswith(('Mathlib.', 'Lean.', 'Init.', 'Std.')), f'Unapproved additional import: {dep}')
                boundary.add(dep)
        active.remove(module); visited.add(module); order.append(module)
    visit(PLAN['probeModule'])
    need(visited == known and order == PLAN['topologicalOrder'], 'Extra/missing/unordered owned closure')
    need(PLAN['auditedModules'] == order[:-1] and order[-2] == PLAN['rootModule'], 'Wrong audited root/probe')
    need(foreign_refs == {FOREIGN['supplierModule']}, 'Changed foreign entry roots')
    need(sorted(boundary) == PLAN['boundaryImports'], 'Changed trusted dependency boundary')
    need(replay_targets() == PLAN['replayTargets'], 'Changed ordered replay manifest')


def replay_targets():
    targets = list(FOREIGN['modules']) + [r['module'] for r in FOREIGN['architectModules']]
    targets += ['ColdBVProbe'] + PLAN['topologicalOrder']
    need(len(targets) == len(set(targets)) == PLAN['replayModuleCount'] == 327, 'Replay count mismatch')
    need(PLAN['rootModule'] in targets and PLAN['probeModule'] in targets, 'Missing actual root/probe target')
    return targets


def stage(consumer, root, out):
    validate_sources(consumer)
    for row in PLAN['sources']:
        dst = root / row['destination']
        need(not dst.exists() and not dst.is_symlink(), f'Stage collision: {dst}')
        need(not any(p.is_symlink() for p in dst.parents if p == root or root in p.parents), f'Symlink stage parent: {dst}')
    for row in PLAN['sources']:
        dst = root / row['destination']; dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(consumer / row['source'], dst)
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(HERE / 'owned-closure.json', out / 'owned-closure.json')
    (out / 'owned-build-modules.txt').write_text('\n'.join(PLAN['topologicalOrder']) + '\n')
    print('STAGED_OWNED_CORE=44 ADAPTERS=2 AUDIT_PROBE=1')


def compiled_set(directory):
    paths = list(directory.rglob('*.olean')) if directory.exists() else []
    for p in paths: regular(p, directory)
    return {str(p.relative_to(directory))[:-6].replace('/', '.') for p in paths}


def axiom_gate(out):
    log = (out / 'chen-quotient-bv-build.log').read_text()
    need('sorryAx' not in log, 'sorryAx in consumer audit output')
    module_lines = re.findall(r'^QUOTIENT_BV_IMPORTED_MODULE (\S+)$', log, re.M)
    need(len(module_lines) == len(set(module_lines)), 'Duplicate loaded-module report')
    seen = set(module_lines)
    proof = set(PLAN['auditedModules'])
    expected_foreign = set(FOREIGN['modules']) | {r['module'] for r in FOREIGN['architectModules']}
    # Fail closed on any unexpected custom namespace, including root names without dots.
    custom = {m for m in seen if m.split('.')[0] not in TRUSTED_PREFIXES}
    need(custom == proof | expected_foreign, 'Loaded custom closure is not exactly 46 owned + 270+9 foreign')
    need(PLAN['rootModule'] in seen, 'Actual quotient consumer root was not loaded')
    rows = re.findall(r'^QUOTIENT_BV_OWNED_MODULE_AUDIT (\S+) declarations=([1-9][0-9]*)$', log, re.M)
    need(len(rows) == len(proof) and {m for m, _ in rows} == proof, 'Missing/duplicate module-origin axiom coverage')
    counts = {m: int(n) for m, n in rows}
    success = re.findall(r'^QUOTIENT_BV_OWNED_AXIOM_AUDIT_PASS declarations=([1-9][0-9]*) modules=46$', log, re.M)
    need(len(success) == 1 and int(success[0]) == sum(counts.values()), 'Missing/inconsistent full owned/transitive axiom audit')
    named = {}
    for name in PLAN['namedAxiomReports']:
        reports = re.findall(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]", log)
        empty = re.findall(r"'"+re.escape(name)+r"' does not depend on any axioms", log)
        need(len(reports)+len(empty) == 1, f'Missing/duplicate named axiom report: {name}')
        axioms = {v.strip() for v in reports[0].split(',') if v.strip()} if reports else set()
        need(axioms <= ALLOWED_AXIOMS, f'Forbidden named axioms: {name}')
        named[name] = sorted(axioms)
    write(out, 'loaded-imports.json', sorted(seen))
    write(out, 'module-origin-axiom-audit.json', {'counts': counts, 'total': sum(counts.values()), 'named': named})


def after(consumer, root, out):
    validate_sources(consumer)
    gate = json.loads((out / 'cold-gate.json').read_text())
    main = root / '.lake/build/lib/lean'
    arch = root / '.lake/packages/LeanArchitect/.lake/build/lib/lean'
    architect = {r['module'] for r in FOREIGN['architectModules']}
    targets = replay_targets()
    need(compiled_set(main) == set(targets) - architect, 'Unexpected/missing root-project compiled module')
    need(compiled_set(arch) == architect, 'Unexpected/missing Architect compiled module')
    for row in PLAN['sources']:
        p = root / row['destination']; regular(p, root)
        need(sha256(p) == row['sha256'], 'Staged source changed')
    built = []
    for module in targets:
        p = (arch if module in architect else main) / (module.replace('.', '/') + '.olean')
        regular(p, arch if module in architect else main)
        need(p.stat().st_mtime_ns >= gate['time_ns'], f'Artifact predates cold gate: {p}')
        built.append({'module': module, 'sha256': sha256(p), 'bytes': p.stat().st_size, 'mtime_ns': p.stat().st_mtime_ns})
    axiom_gate(out)
    (out / 'replay-modules.txt').write_text('\n'.join(targets)+'\n')
    write(out, 'all-built-artifacts.json', built)
    print('PASS: exact 270+9 foreign closure; 46 owned proof origins audited; 327 fresh replay targets')


def replay_gate(out):
    targets = replay_targets()
    need((out / 'replay-modules.txt').read_text().splitlines() == targets, 'Replay file differs from exact ordered targets')
    batches = [targets[i:i+12] for i in range(0, len(targets), 12)]
    need((out / 'replay-batches.txt').read_text().splitlines() == [' '.join(b) for b in batches], 'Batch input missing/reordered/duplicated')
    log = (out / 'kernel-replay.log').read_text()
    starts = list(re.finditer(r'^QUOTIENT_REPLAY_BEGIN ([1-9][0-9]*) (.+)$', log, re.M))
    ends = list(re.finditer(r'^QUOTIENT_REPLAY_END ([1-9][0-9]*) exit=([0-9]+)$', log, re.M))
    need(len(starts) == len(ends) == len(batches) == 28, 'Incomplete/duplicate replay batch framing')
    explicit_all, records = set(), []
    for index, (start, end, batch) in enumerate(zip(starts, ends, batches), 1):
        need(int(start[1]) == int(end[1]) == index and end[2] == '0', 'Batch numbering/failure mismatch')
        need(start[2].split() == batch, 'Batch requested targets do not match exact ordered manifest')
        need(start.end() < end.start(), 'Misordered replay markers')
        need(index == len(batches) or end.end() < starts[index].start(), 'Overlapping replay batches')
        chunk = log[start.end():end.start()]
        commands = re.findall(r'^\s*Command being timed: "(.+)"$', chunk, re.M)
        need(commands == ['lake env leanchecker --verbose '+' '.join(batch)], 'Missing/changed per-batch checker command')
        need(re.findall(r'^\s*Exit status: ([0-9]+)$', chunk, re.M) == ['0'], 'Missing/failed checker exit status')
        explicit = re.findall(r'^replaying (\S+)$', chunk, re.M)
        need(set(batch) <= set(explicit), 'Requested target lacks explicit kernel replay')
        need(set(explicit) <= set(targets), 'Unexpected explicit replay module')
        explicit_all.update(explicit)
        records.append({'index': index, 'requested': batch, 'explicit': explicit, 'exit': 0})
    need(explicit_all == set(targets), 'Missing exact root or other replay target')
    # No unframed replay/command/status evidence can silently stand in for a complete batch.
    outside = log
    for start, end in reversed(list(zip(starts, ends))): outside = outside[:start.start()] + outside[end.end():]
    need(not re.search(r'^replaying |Command being timed:|Exit status:|QUOTIENT_REPLAY_', outside, re.M), 'Unframed replay evidence')
    write(out, 'verified-replay-batches.json', records)
    write(out, 'replay-verification.json', {'targets': len(targets), 'batches': len(batches),
          'exactOrderedRequestedTargets': True, 'everyBatchExit0': True,
          'everyBatchCommandMatches': True, 'everyTargetExplicitlyReplayed': True,
          'requiredRoot': PLAN['rootModule'], 'rootExplicitlyReplayed': PLAN['rootModule'] in explicit_all,
          'fullLogSha256': sha256(out / 'kernel-replay.log')})
    print('PASS: all 28 complete batches; all 327 exact ordered targets explicitly kernel-replayed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['sources', 'stage', 'after', 'replay'])
    parser.add_argument('consumer', type=Path); parser.add_argument('root', type=Path); parser.add_argument('out', type=Path)
    a = parser.parse_args()
    if a.mode == 'sources': validate_sources(a.consumer)
    elif a.mode == 'replay': replay_gate(a.out)
    else: {'stage': stage, 'after': after}[a.mode](a.consumer, a.root, a.out)
