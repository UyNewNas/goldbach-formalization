#!/usr/bin/env python3
"""Review-owned static/CI gates. Never execute fetched Python or shell."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
REVIEW = json.loads((HERE / 'closure.json').read_text())
MANIFEST = json.loads((HERE / 'upstream-manifest.json').read_text())
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def need(ok, message):
    if not ok:
        raise SystemExit(message)


def blob(path):
    raw = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def scrub(text):
    """Mask nested Lean comments and strings, preserving offsets/newlines."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2
            elif pair == '-/':
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                out.extend('  '); i += 2
            elif text[i] == '"':
                string = False; out.append(' '); i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-':
            depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i)); i = end
        elif text[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    need(depth == 0 and not string, 'Unclosed comment/string')
    return ''.join(out)


def imports(text):
    result = []
    for line in scrub(text).splitlines():
        match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*', line)
        if match:
            names = match.group(1).split()
            need(all(re.fullmatch(r'[A-Za-z0-9_.]+', name) for name in names),
                 f'Unsupported import syntax: {line}')
            result.extend(names)
    return result


def write(out, name, data):
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_text(json.dumps(data, indent=2) + '\n')


def source_gate(root, out):
    edges, runtime, hashes = {}, [], {}
    bad = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC')
    io = re.compile(r'#eval|\brun_cmd\b|\brun_elab\b|\binitialize\b|IO\.(?:Process|FS)')
    for module in REVIEW['modules']:
        path = root / (module.replace('.', '/') + '.lean')
        need(path.is_file() and not path.is_symlink(), f'Missing/nonregular source: {path}')
        hashes[module] = blob(path)
        need(hashes[module] == REVIEW['gitBlobs'][module], f'Source changed: {module}')
        content = path.read_text()
        code = scrub(content)
        need(not bad.search(code), f'Forbidden proof-source token: {module}')
        for match in io.finditer(code):
            runtime.append({'module': module, 'token': match.group(),
                            'line': code[:match.start()].count('\n') + 1})
        edges[module] = imports(content)
    need(edges == REVIEW['imports'], 'Source import graph differs from reviewed graph')
    visited, boundary = set(), set()
    def visit(module):
        if module in visited:
            return
        visited.add(module)
        for dep in edges[module]:
            if dep in edges:
                visit(dep)
            else:
                boundary.add(dep)
    visit(REVIEW['supplierModule'])
    need(visited == set(REVIEW['modules']), 'Extra/missing supplier closure modules')
    need(sorted(boundary) == REVIEW['boundaryImports'], 'Changed dependency boundary')
    need(runtime == [{'module': 'PrimeNumberTheoremAnd.Consequences',
                      'token': 'run_cmd', 'line': 436}], 'Unreviewed runtime entry point')
    write(out, 'source-audit.json', {'source_modules': len(visited), 'git_blob_hashes': hashes,
          'boundary_imports': sorted(boundary), 'runtime_entries': runtime, 'issues': []})
    print(f'Source audit passed: {len(visited)} pinned proof modules; runtime entry reviewed.')


def root_gate(root, out):
    need(blob(root / 'lakefile.toml') == REVIEW['rootConfig']['sha'], 'Root Lake config changed')
    need(json.loads((root / 'lake-manifest.json').read_text()) == MANIFEST,
         'Pinned root dependency manifest changed')
    need((root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0-rc1',
         'Root Lean toolchain changed')
    sha = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    need(sha == REVIEW['commit'], 'Wrong external project revision')
    subprocess.run(['git', '-C', str(root), 'diff', '--quiet', 'HEAD', '--'], check=True)
    write(out, 'root-audit.json', {'commit': sha, 'rootConfig': REVIEW['rootConfig'],
                                 'dependency_manifest': MANIFEST})
    print('Root source/config/toolchain pins passed before dependency execution.')


def dependencies(root, out):
    root_gate(root, out)
    rows = []
    for config in REVIEW['dependencyConfigs']:
        path = root / '.lake/packages' / config['name']
        sha = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        need(sha == config['rev'], f'Wrong dependency revision: {config["name"]}')
        subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD', '--'], check=True)
        need(blob(path / config['path']) == config['sha'], f'Lake config changed: {config["name"]}')
        rows.append(config)
    for item in REVIEW['architectModules']:
        path = root / '.lake/packages/LeanArchitect' / (item['module'].replace('.', '/') + '.lean')
        need(blob(path) == item['sha'], f'Architect source changed: {item["module"]}')
    write(out, 'dependency-audit.json', {'packages': rows, 'architect': REVIEW['architectModules']})
    print(f'Dependency audit passed: {len(rows)} pinned packages; 9 Architect source modules.')


def build_roots(root):
    return [root / '.lake/build', root / '.lake/packages/LeanArchitect/.lake/build']


def prebuild(root, out):
    artifacts = [str(p) for directory in build_roots(root) if directory.exists()
                 for p in directory.rglob('*') if p.is_file()]
    need(not artifacts, f'Cold gate failed, external build outputs already exist: {artifacts[:10]}')
    write(out, 'cold-gate.json', {'time_ns': time.time_ns(), 'external_artifacts_before': artifacts,
          'claim': 'External project and Architect source-cold; Mathlib and its dependencies cached.'})
    print('Cold gate passed: zero external project/Architect build artifacts.')


def postbuild(root, out):
    gate = json.loads((out / 'cold-gate.json').read_text())
    rows = []
    modules = [(m, root / '.lake/build/lib/lean') for m in REVIEW['modules']]
    modules += [(m['module'], root / '.lake/packages/LeanArchitect/.lake/build/lib/lean')
                for m in REVIEW['architectModules']]
    for module, directory in modules:
        path = directory / (module.replace('.', '/') + '.olean')
        need(path.is_file() and not path.is_symlink(), f'Unbuilt external module: {module}')
        need(path.stat().st_mtime_ns >= gate['time_ns'], f'Artifact predates cold gate: {module}')
        rows.append({'module': module, 'path': str(path.relative_to(root)),
                     'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                     'bytes': path.stat().st_size, 'mtime_ns': path.stat().st_mtime_ns})
    write(out, 'built-artifacts.json', rows)
    (out / 'replay-modules.txt').write_text('\n'.join(m for m, _ in modules) + '\nColdBVProbe\n')
    source_gate(root, out)
    dependencies(root, out)
    print(f'Fresh artifact coverage passed: {len(rows)} external modules.')


def axiom_gate(log, out):
    text = log.read_text()
    names = [REVIEW['supplierConstant'], 'IndependentBV.standard_bv']
    rows = {}
    for name in names:
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", text)
        need(match is not None, f'Missing named axiom report: {name}')
        values = {value.strip() for value in match.group(1).split(',') if value.strip()}
        need(values <= ALLOWED_AXIOMS, f'Unexpected axioms for {name}: {values}')
        rows[name] = sorted(values)
    need('sorryAx' not in text, 'sorryAx in probe output')
    write(out, 'axiom-audit.json', rows)
    print('Named supplier and literal-consumer axiom reports passed.')


def selftest(root, out):
    need('axiom' not in scrub('/- outer /- nested -/ axiom x -/'), 'Nested comments broken')
    need('sorry' not in scrub('"sorry" -- sorry\n'), 'String/comment masking broken')
    need(imports('public meta import A.B\nimport C D\n') == ['A.B', 'C', 'D'], 'Import parsing broken')
    source_gate(root, out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['roots', 'sources', 'dependencies', 'prebuild', 'postbuild', 'axioms', 'selftest'])
    parser.add_argument('root', type=Path)
    parser.add_argument('out', type=Path)
    args = parser.parse_args()
    {'roots': root_gate, 'sources': source_gate, 'dependencies': dependencies, 'prebuild': prebuild,
     'postbuild': postbuild, 'axioms': axiom_gate, 'selftest': selftest}[args.mode](args.root, args.out)
