"""Read-only exact current-input preflight using the frozen proper header lexer."""
from pathlib import Path
import argparse
import datetime
import importlib.util
import json

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

p = argparse.ArgumentParser()
p.add_argument('target')
p.add_argument('source_sha256')
p.add_argument('--include-target', action='store_true')
a = p.parse_args()
runtime = load('oct20_frozen_runtime', STATE / 'runtime.py')
walker = load('oct20_frozen_walker', STATE / 'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py')
assert runtime.sha(STATE / 'runtime.py') == '81635b52f3b62dfe477a8184bff5ef6dc8de3daee334c6cfd4547cccefe3b9be'
assert runtime.sha(STATE / 'audit_owned.py') == '267d59bfc37e5d5a742b619390f5b42155bb5ab33d923684487acb6b8a7e19e6'
assert runtime.sha(Path(walker.__file__)) == 'e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914'
rt = runtime.Runtime(ROOT)
assert runtime.sha(rt.paths(a.target)[0]) == a.source_sha256
seen, project, foreign, missing, findings, foreign_roots = set(), [], [], [], [], set()
def visit(name):
    if name in seen:
        return
    seen.add(name)
    source, obj = rt.paths(name)
    if source is None:
        rel = Path(name.replace('.', '/')).with_suffix('.lean')
        source = next((q for q in [runtime.BIN.parent / 'src/lean' / rel,
            runtime.BIN.parent / 'src/lean/lake' / rel] if q.is_file()), None)
    head = walker.header_imports(source.read_text()) if source else None
    if head:
        if head['parser_findings']:
            findings.append({'module': name, 'findings': head['parser_findings']})
        for dep in dict.fromkeys(x['module'] for x in head['imports']):
            visit(dep)
    if rt.project(name):
        foreign_roots.update(x['module'] for x in head['imports'] if not rt.project(x['module']))
        explicit = list(dict.fromkeys(x['module'] for x in head['imports'] if not x['implicit']))
        assert runtime.imports(source) == explicit, ('runtime_parser_mismatch', name)
        if name != a.target or a.include_target:
            cache_path = STATE / 'cache' / (name + '.json')
            cache = json.loads(cache_path.read_text())
            deps = {d: runtime.sha(rt.paths(d)[1]) for d in explicit}
            binding = rt.binding(name, deps)
            assert cache['status'] == 'PASS' and cache['binding'] == binding, ('cache_binding', name)
            assert cache['object_parts'] == rt.parts(obj), ('object_parts', name)
            project.append({'module': name, 'source_sha256': runtime.sha(source),
                'object_sha256': runtime.sha(obj), 'cache_sha256': runtime.sha(cache_path),
                'object_parts': rt.parts(obj), 'header': head, 'exact': True})
    else:
        if not obj.is_file():
            missing.append(name)
        foreign.append({'module': name, 'source_sha256': runtime.sha(source) if source else None,
            'object_sha256': runtime.sha(obj) if obj.is_file() else None,
            'object_path': str(obj)})
visit(a.target)
assert not findings and not missing, (findings, missing)
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
out = STATE / 'preflights' / (stamp + '-exact-current-' + a.target + '.json')
report = {'status': 'READONLY_PROPER_GRAPH_EXISTING_RECURSIVE_CACHES_EXACT',
    'target': a.target, 'target_sha256': a.source_sha256,
    'target_cache_included': a.include_target,
    'proper_project_count': sum(rt.project(n) for n in seen),
    'checked_project_cache_count': len(project), 'project_parents': project,
    'foreign_nodes': foreign, 'foreign_node_count': len(foreign),
    'foreign_header_roots_including_Init': sorted(foreign_roots),
    'foreign_header_root_count': len(foreign_roots),
    'missing_external': missing, 'parser_findings': findings,
    'pins': rt.pins(), 'runtime_sha256': runtime.sha(STATE / 'runtime.py'),
    'import_walker_sha256': runtime.sha(Path(walker.__file__)),
    'no_compilation': True, 'no_cache_mutated': True,
    'full_foreign_replay_claimed': False}
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in ('project_parents', 'foreign_nodes')} | {'report': str(out)}))
