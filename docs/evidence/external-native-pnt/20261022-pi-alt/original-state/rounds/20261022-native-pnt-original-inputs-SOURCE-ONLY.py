"""Unexecuted native Consequences input collector, before/after only.

No Lean/checker/audit invocation, locks, ownership, gate or producer claim.
Original Runtime initialization performs its original provider cleanliness checks.
Root separately schedules soleheavy/physical-idle/quota and singleton audit.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import traceback

STATE = Path(__file__).resolve().parent.parent
ROOT = STATE.parents[1]
TARGET = 'PrimeNumberTheoremAnd.Consequences'
SOURCE_SHA = '03f9980b261eebef3e773e67d891287ed1c165c2f02305211d96df335f653a9b'
OBJECT_SHA = '3de498061c2d9c574fb5989f93d2914d3e80c316903ac9b69a60353c2f85bdb6'
PROPER = 'preflights/20261022T021630789741Z-exact-current-PrimeNumberTheoremAnd.Consequences.json'
PROPER_SHA = '0e4659de701fa14fb9b55c9809f83065cbb550939ca9fca7c3c6c86d4683651f'
PARTS = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')
PROTECTED = {
    'runtime.py': '81635b52f3b62dfe477a8184bff5ef6dc8de3daee334c6cfd4547cccefe3b9be',
    'audit_owned.py': '267d59bfc37e5d5a742b619390f5b42155bb5ab33d923684487acb6b8a7e19e6',
    'preflight_current_oct20.py': 'e5c11c36e35582e4f864fa8582e49800027e91cbfab85d71f3456da83abb1947',
    'import_walker_v2.py': 'e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914',
    'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py': 'e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914',
    '../../verification/parts/p0/queue/AuditTemplate.lean': 'df79aecf54317dbdc193e9b68ec8e833f6d4d09a92f369ac6985d23d974ff822',
    '../../../goldbach-integration/verification/parts/takeover-p0/checker_memory_guard.py': 'a506fcc8bd2a2f1731c1ae32d845be21bc3a35548ce25774aa8bf8b4cb6f7ab7',
    '/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux/src/lean/LeanChecker.lean': 'eb5dee411837629f09c5c18d63cc833d30335a46048bc586642742e90aa65d5f',
    '/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux/src/lean/Lean/Util/CollectAxioms.lean': '64f340d42f18c51ee83527f03fa69cc26415dd71dcf7fe71031b7760be90007d',
}
PINS = {
    'lean-toolchain': '62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef',
    'lakefile.toml': 'b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254',
    'lake-manifest.json': '35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849',
}
BINS = {'lean': '98ae075329cac5c48823aff15c364b8da4fa76b1ddcd14c801dc891032614ab9',
    'lean.real': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    'leanchecker': 'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def path(value):
    value = str(value).replace('\\', '/')
    if os.name == 'nt' and value.startswith('/mnt/') and len(value) > 7:
        value = value[5].upper() + ':/' + value[7:]
    elif os.name != 'nt' and len(value) >= 3 and value[0].isascii() and value[0].isalpha() and value[1:3] == ':/':
        value = '/mnt/' + value[0].lower() + '/' + value[3:]
    p = Path(value)
    if p.is_absolute():
        return p
    return (ROOT if value.startswith('.lake/') else STATE) / p


def sha(value):
    with path(value).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(value):
    return json.loads(path(value).read_text(encoding='utf-8'))


def reference(value):
    return {'path': str(path(value).resolve()), 'sha256': sha(value)}


def write_new(value, data):
    with path(value).open('x', encoding='utf-8', newline='\n') as stream:
        stream.write(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
    return reference(value)


def load(name, value):
    spec = importlib.util.spec_from_file_location(name, path(value))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_protected():
    for name, digest in PROTECTED.items():
        require(sha(name) == digest, 'Protected API changed: ' + name)
    require(sha(PROPER) == PROPER_SHA, 'Original proper hash differs')


def project_freeze():
    files = sorted((ROOT / 'ImbalancedChen').rglob('*.lean'))
    require(len(files) == 562, 'Actual source inventory differs')
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in files}


def artifact_freeze():
    files = list((STATE / 'cache').glob('*.json'))
    files += [p for p in (STATE / 'lib/lean').rglob('*') if p.is_file()]
    return {p.relative_to(STATE).as_posix(): sha(p) for p in sorted(files)}


def collect():
    """Measure ALL original foreign rows using original native resolution APIs."""
    check_protected()
    proper = read(PROPER)
    require(proper['status'] == 'READONLY_PROPER_GRAPH_EXISTING_RECURSIVE_CACHES_EXACT', 'Proper status')
    require(proper['target'] == TARGET and proper['target_sha256'] == SOURCE_SHA, 'Proper target')
    require(proper['target_cache_included'] is False, 'Proper target mode')
    require(proper['proper_project_count'] == proper['checked_project_cache_count'] == 0, 'Unexpected project inputs')
    require(proper['project_parents'] == proper['missing_external'] == proper['parser_findings'] == [], 'Proper findings')
    require(proper['no_compilation'] and proper['no_cache_mutated'], 'Wrong proper scope')
    rows = {row['module']: row for row in proper['foreign_nodes']}
    require(len(rows) == len(proper['foreign_nodes']) == proper['foreign_node_count'], 'Proper duplicate/count')
    require(TARGET in rows, 'Native target absent')
    before_sources, before_artifacts = project_freeze(), artifact_freeze()
    runtime = load('native_pnt_original_runtime', STATE / 'runtime.py')
    walker = load('native_pnt_frozen_walker', STATE / 'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py')
    rt = runtime.Runtime(ROOT)
    require(rt.pins() == PINS == proper['pins'], 'Fixed native pins differ')
    bins = {name: sha(runtime.BIN / name) for name in BINS}
    require(bins == BINS, 'Native compiler/checker hashes differ')
    nodes = {}
    for name, original in rows.items():
        require(not rt.project(name), 'Native graph contains project module')
        source, obj = rt.paths(name)
        if source is None:
            rel = Path(name.replace('.', '/')).with_suffix('.lean')
            source = next((q for q in [runtime.BIN.parent / 'src/lean' / rel,
                runtime.BIN.parent / 'src/lean/lake' / rel] if q.is_file()), None)
        source_sha = sha(source) if source else None
        require(source_sha == original['source_sha256'], 'Native source differs: ' + name)
        require(str(obj) == original['object_path'] and obj.is_file(), 'Native object resolution/missing: ' + name)
        present = rt.parts(obj)
        require(set(present) <= set(PARTS), 'Unknown object slot')
        slots = {suffix: present.get(suffix) for suffix in PARTS}
        require(slots['.olean'] == original['object_sha256'], 'Native main object differs: ' + name)
        head = walker.header_imports(source.read_text()) if source else None
        require(not head or not head['parser_findings'], 'Native header findings: ' + name)
        imports = list(dict.fromkeys(item['module'] for item in head['imports'])) if head else []
        require(set(imports) <= set(rows), 'Native header edge outside original proper graph')
        nodes[name] = {'source_path': str(source) if source else None, 'source_sha256': source_sha,
            'object_path': str(obj), 'all_five_slots': slots, 'header': head, 'imports': imports}
    reached, pending = set(), [TARGET]
    while pending:
        name = pending.pop()
        if name not in reached:
            reached.add(name)
            pending.extend(nodes[name]['imports'])
    require(reached == set(nodes), 'Measured native graph not exact target closure')
    require(nodes[TARGET]['source_sha256'] == SOURCE_SHA and nodes[TARGET]['all_five_slots']['.olean'] == OBJECT_SHA, 'Target source/object binding')
    require(project_freeze() == before_sources and artifact_freeze() == before_artifacts, 'Project source/cache/object changed during collection')
    require(rt.pins() == PINS, 'Pins changed during collection')
    check_protected()
    return {'target': TARGET, 'source_sha256': SOURCE_SHA, 'main_olean_sha256': OBJECT_SHA,
        'original_proper': reference(PROPER), 'native_nodes': nodes, 'native_node_count': len(nodes),
        'native_bins': bins, 'pins': PINS, 'provider_revisions': {p['name']: p['rev'] for p in rt.packages},
        'protected_apis': PROTECTED, 'project_sources562': before_sources, 'STATE_cache_and_lib_map': before_artifacts,
        'collector': reference(__file__)}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--phase', choices=('before', 'after'), required=True)
    p.add_argument('--directory', required=True)
    p.add_argument('--before')
    p.add_argument('--before-sha256')
    a = p.parse_args()
    directory = path(a.directory).resolve()
    require(directory.parent == (STATE / 'rounds').resolve() and directory.name.startswith('native-pnt-inputs-'), 'New native inputs directory required')
    directory.mkdir(exist_ok=True)
    try:
        require(not (directory / 'HOLD.json').exists(), 'First failure already HOLD')
        require(not (directory / (a.phase + '-started.json')).exists(), 'No stage retry permitted')
        if a.phase == 'before':
            require(a.before is None and a.before_sha256 is None, 'Before phase cannot consume prior map')
            require(not (directory / 'after.json').exists(), 'Phase order')
            prior = None
        else:
            require(a.before and a.before_sha256, 'After needs root-designated actual before path+SHA')
            require(sha(a.before) == a.before_sha256, 'Before input-map hash differs')
            prior = read(a.before)
            require(prior['status'] == 'ORIGINAL_NATIVE_INPUT_MAP_ONLY' and prior['phase'] == 'before', 'Before input-map scope')
            require(prior['inputs']['collector']['sha256'] == sha(__file__), 'Before collector changed')
        write_new(directory / (a.phase + '-started.json'), {'phase': a.phase,
            'before': reference(a.before) if a.before else None, 'status': 'RUNNING_NO_RETRY'})
        first = collect()
        second = collect()
        require(first == second, 'Inputs changed across complete double measurement')
        if prior is not None:
            require(first == prior['inputs'], 'Native/project inputs before-after not deep exact')
        output = write_new(directory / (a.phase + '.json'), {'status': 'ORIGINAL_NATIVE_INPUT_MAP_ONLY',
            'phase': a.phase, 'inputs': first, 'deep_exact_against_before': prior is not None,
            'before': reference(a.before) if a.before else None,
            'scope': 'Existing singleton native selected-module stock plus ALL qualification inputs only; no strict producer or nine-module fresh closure replay claim',
            'no_compilation_or_audit': True, 'unconditional_main_proved': False})
        print(json.dumps({'phase': a.phase, 'output': output, 'status': 'READONLY_INPUT_MAP_COMPLETE'}))
    except BaseException as error:
        if not (directory / 'HOLD.json').exists():
            write_new(directory / 'HOLD.json', {'status': 'FIRSTFAIL_HOLD_NO_RETRY_REPAIR',
                'phase': a.phase, 'error': str(error), 'traceback': traceback.format_exc()})
        raise


if __name__ == '__main__':
    main()
