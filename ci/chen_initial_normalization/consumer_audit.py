#!/usr/bin/env python3
"""Review-owned subset and consumer gates. Never fetch or invoke foreign code/Lean."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil

HERE = Path(__file__).resolve().parent
PLAN = json.loads((HERE / 'closure.json').read_text())
BASE_PATH = HERE.parent / 'external_bv'
for name, expected in PLAN['baseAuditFileSha256'].items():
    if hashlib.sha256((BASE_PATH / name).read_bytes()).hexdigest() != expected:
        raise SystemExit(f'Byte-preserved baseline file changed: {name}')
SPEC = importlib.util.spec_from_file_location('base_source_audit', BASE_PATH / 'cold_source_audit.py')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
FOREIGN = BASE.REVIEW
need, blob, scrub, imports = BASE.need, BASE.blob, BASE.scrub, BASE.imports
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
TRUSTED_PREFIXES = {'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop', 'Qq',
                    'Plausible', 'ProofWidgets', 'LeanSearchClient', 'ImportGraph', 'Cli', 'Lake'}
RUNTIME = re.compile(r'#eval|\brun_cmd\b|\brun_elab\b|\binitialize\b|\bbuiltin_initialize\b|IO\.(?:Process|FS)')
ESCAPES = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC')


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(out, name, obj):
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_text(json.dumps(obj, indent=2) + '\n')


def module_set(kind):
    return {r['module'] for r in PLAN['sources'] if r['kind'] == kind}


def check_file(path, row):
    need(path.is_file() and not path.is_symlink(), f'Missing regular source: {path}')
    need(sha256(path) == row['sha256'] and blob(path) == row['gitBlob'], f'Pinned source changed: {path}')
    need(path.stat().st_size == row['bytes'], f'Source byte count changed: {path}')
    need(imports(path.read_text()) == row['imports'], f'Import edges changed: {path}')


def validate_graph():
    need(len(FOREIGN['modules']) == 270 and len(FOREIGN['architectModules']) == 9,
         'Wrong ordinary270 baseline counts')
    need(sha256(BASE_PATH / 'closure.json') == PLAN['foreignClosureSha256'], 'Ordinary270 bytes changed')
    expected = {'owned-core': 42, 'supplier': 32, 'architect': 9, 'consumer': 1, 'audit-tool': 1}
    for kind, count in expected.items():
        need(len(module_set(kind)) == count, f'Wrong {kind} source count')
    known = {r['module']: r for r in PLAN['sources']}
    need(len(known) == len(PLAN['sources']) == 85, 'Duplicate or wrong total source count')
    arch = {r['module']: r['sha'] for r in FOREIGN['architectModules']}
    for row in PLAN['sources']:
        module = row['module']
        if row['kind'] == 'supplier':
            need(module in FOREIGN['modules'] and row['gitBlob'] == FOREIGN['gitBlobs'][module],
                 f'Supplier is outside the exact approved ordinary270: {module}')
            need(row['imports'] == FOREIGN['imports'][module], f'Changed supplier imports: {module}')
        if row['kind'] == 'architect':
            need(arch.get(module) == row['gitBlob'], f'Changed Architect pin: {module}')
    visited, boundary, topo, visiting = set(), set(), [], set()
    def visit(module):
        if module in visited:
            return
        need(module not in visiting, f'Import cycle: {module}')
        visiting.add(module)
        for dep in known[module]['imports']:
            if dep in known:
                visit(dep)
            else:
                need(dep.split('.')[0] in TRUSTED_PREFIXES, f'Unapproved import: {dep}')
                boundary.add(dep)
        visiting.remove(module)
        visited.add(module)
        topo.append(module)
    visit('ChenInitialNormalizationProbe')
    need(visited == set(known), 'Extra/missing module in complete selected closure')
    need(topo == PLAN['topologicalOrder'], 'Changed build/replay topological order')
    need(sorted(boundary) == PLAN['boundaryImports'], 'Changed trusted dependency boundary')
    need(PLAN['auditedModules'] == topo[:-1] and len(topo[:-1]) == 84, 'Incomplete origin audit scope')
    need(PLAN['allowEmptyDeclarationModules'] == ['Architect'], 'Changed empty-module exception')
    need(PLAN['ownedBuildOrder'] == [m for m in topo if known[m]['kind'] in {'owned-core', 'consumer', 'audit-tool'}],
         'Wrong owned build order')
    need(known['ChenInitialNormalizationAdapter']['imports'] ==
         ['ImbalancedChen.CenterEulerTail'] + PLAN['supplierRoots'], 'Changed consumer roots')
    need(PLAN['supplierRoots'] == ['AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem',
                                  'AnalyticNumberTheory.Mertens.Theorems'], 'Wrong supplier roots')


def validate_owned(consumer):
    validate_graph()
    for rel, expected in PLAN['coreConfigBlobs'].items():
        need(blob(consumer / rel) == expected, f'Pinned core config changed: {rel}')
    for row in PLAN['sources']:
        if 'source' not in row:
            continue
        path = consumer / row['source']
        check_file(path, row)
        if row['kind'] != 'audit-tool':
            code = scrub(path.read_text())
            need(not ESCAPES.search(code) and not RUNTIME.search(code), f'Unreviewed owned proof/runtime token: {path}')


def source_gate(consumer, root, out):
    validate_owned(consumer)
    runtime, arch_tokens, hashes = [], [], {}
    for row in PLAN['sources']:
        if row['kind'] not in {'supplier', 'architect'}:
            continue
        path = root / row['destination']
        check_file(path, row)
        hashes[row['module']] = row['gitBlob']
        code = scrub(path.read_text())
        if row['kind'] == 'supplier':
            need(not ESCAPES.search(code), f'Forbidden supplier proof token: {row["module"]}')
        else:
            arch_tokens.extend({'module': row['module'], 'token': m.group(),
                                'line': code[:m.start()].count('\n') + 1} for m in ESCAPES.finditer(code))
        runtime.extend({'module': row['module'], 'token': m.group(),
                        'line': code[:m.start()].count('\n') + 1} for m in RUNTIME.finditer(code))
    need(runtime == PLAN['runtimeEntries'], 'Changed reviewed runtime entries')
    need(arch_tokens == PLAN['architectReviewedTokens'], 'Changed reviewed Architect tooling tokens')
    write(out, 'normalization-source-audit.json', {'supplier_count': 32, 'architect_count': 9,
          'ordinary270_subset': True, 'git_blobs': hashes, 'runtime_entries': runtime,
          'architect_reviewed_tokens': arch_tokens, 'issues': []})
    print('PASS: exact 32 ordinary270 supplier sources + unchanged 9 Architect; 42 core + consumer + probe source pins')


def stage(consumer, root, out):
    source_gate(consumer, root, out)
    selected = [r for r in PLAN['sources'] if 'source' in r]
    for row in selected:
        destination = root / row['destination']
        need(not destination.exists() and not destination.is_symlink(), f'Stage collision: {destination}')
    for row in selected:
        destination = root / row['destination']
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(consumer / row['source'], destination)
    shutil.copyfile(HERE / 'closure.json', out / 'normalization-closure.json')
    (out / 'owned-build-modules.txt').write_text('\n'.join(PLAN['ownedBuildOrder']) + '\n')
    print('STAGED: 42 core + 1 consumer + 1 audit probe; no Lake configuration changes')


def compiled_set(directory):
    files = list(directory.rglob('*.olean')) if directory.exists() else []
    need(all(p.is_file() and not p.is_symlink() for p in files), f'Nonregular olean under {directory}')
    return {str(p.relative_to(directory))[:-6].replace('/', '.') for p in files}


def artifact_gate(root, out, owned):
    gate = json.loads((out / 'cold-gate.json').read_text())
    root_expected = module_set('supplier')
    kinds = {'supplier', 'architect'}
    if owned:
        root_expected |= module_set('owned-core') | module_set('consumer') | module_set('audit-tool')
        kinds |= {'owned-core', 'consumer', 'audit-tool'}
    main = root / '.lake/build/lib/lean'
    architect = root / '.lake/packages/LeanArchitect/.lake/build/lib/lean'
    need(compiled_set(main) == root_expected, 'Unexpected/missing root-project compiled module')
    need(compiled_set(architect) == module_set('architect'), 'Unexpected/missing Architect compiled module')
    rows = []
    for row in PLAN['sources']:
        if row['kind'] not in kinds:
            continue
        directory = architect if row['kind'] == 'architect' else main
        p = directory / (row['module'].replace('.', '/') + '.olean')
        need(p.is_file() and not p.is_symlink(), f'Missing regular compiled module: {p}')
        need(p.stat().st_mtime_ns >= gate['time_ns'], f'Artifact predates cold gate: {p}')
        rows.append({'module': row['module'], 'sha256': sha256(p), 'bytes': p.stat().st_size,
                     'mtime_ns': p.stat().st_mtime_ns})
    write(out, 'normalization-built-artifacts.json' if owned else 'supplier-built-artifacts.json', rows)


def after_supplier(consumer, root, out):
    source_gate(consumer, root, out)
    artifact_gate(root, out, False)
    print('PASS: all 32+9 selected foreign modules built cold; no extra project/Architect olean')


def axiom_gate(out):
    text = (out / 'chen-initial-normalization-build.log').read_text()
    need('sorryAx' not in text, 'sorryAx in consumer audit output')
    loaded_rows = re.findall(r'\bNORMALIZATION_IMPORTED_MODULE (\S+)$', text, re.M)
    need(len(loaded_rows) == len(set(loaded_rows)), 'Duplicate loaded-module report')
    loaded = set(loaded_rows)
    audited = set(PLAN['auditedModules'])
    custom = {m for m in loaded if m.split('.')[0] not in TRUSTED_PREFIXES}
    need(custom == audited, 'Loaded custom closure is not exactly 32+9+42+1')
    rows = re.findall(r'\bNORMALIZATION_MODULE_AUDIT (\S+) declarations=([0-9]+)$', text, re.M)
    need(len(rows) == len({r[0] for r in rows}) == len(audited) and {r[0] for r in rows} == audited,
         'Incomplete/duplicate module-origin axiom coverage')
    counts = {name: int(n) for name, n in rows}
    for module, count in counts.items():
        need(count > 0 or module in PLAN['allowEmptyDeclarationModules'], f'Empty declaration coverage: {module}')
    successes = re.findall(r'\bNORMALIZATION_AXIOM_AUDIT_PASS declarations=([1-9][0-9]*) modules=84$', text, re.M)
    need(len(successes) == 1 and int(successes[0]) == sum(counts.values()), 'Missing/inconsistent full axiom audit')
    named = {}
    for name in PLAN['namedAxiomReports']:
        pattern = r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]"
        found = re.findall(pattern, text)
        empty = re.findall(r"'" + re.escape(name) + r"' does not depend on any axioms", text)
        need(len(found) + len(empty) == 1, f'Missing/duplicate named axiom report: {name}')
        axioms = {v.strip() for v in found[0].split(',') if v.strip()} if found else set()
        need(axioms <= ALLOWED_AXIOMS, f'Forbidden named axioms: {name}: {axioms}')
        named[name] = sorted(axioms)
    write(out, 'loaded-imports.json', sorted(loaded))
    write(out, 'module-origin-axiom-audit.json', {'declarations_by_module': counts,
          'total_declarations': sum(counts.values()), 'named_reports': named,
          'allowed_axioms': sorted(ALLOWED_AXIOMS)})


def after(consumer, root, out):
    source_gate(consumer, root, out)
    for row in PLAN['sources']:
        if 'source' in row:
            check_file(root / row['destination'], row)
    artifact_gate(root, out, True)
    axiom_gate(out)
    replay = PLAN['topologicalOrder']
    need(len(replay) == len(set(replay)) == PLAN['replayModuleCount'] == 85, 'Wrong replay target count')
    (out / 'replay-modules.txt').write_text('\n'.join(replay) + '\n')
    print('PASS: all 84 selected custom modules origin-audited; 85 fresh exact replay targets including audit probe')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['sources', 'stage', 'after-supplier', 'after'])
    parser.add_argument('consumer', type=Path)
    parser.add_argument('root', type=Path)
    parser.add_argument('out', type=Path)
    args = parser.parse_args()
    {'sources': source_gate, 'stage': stage, 'after-supplier': after_supplier, 'after': after}[args.mode](
        args.consumer, args.root, args.out)
