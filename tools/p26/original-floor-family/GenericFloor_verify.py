#!/usr/bin/env python3
"""Verify one frozen generic floor owner using the exact accepted P1 cache."""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import io
import json
import os
import re
import sys
import tarfile
import uuid

sys.dont_write_bytecode = True
TARGET = 'ImbalancedChen.P2OriginalSaving19OriginalFloorTransport'
SOURCE_SHA = '9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574'
AUDIT_SHA = '4fa2d4bc9272505e76c14088e08ff309df9ba21981532016f4ff5ba6b89c7680'
MODES = ('normal', 'kernel', 'owned')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/original-floor-family/generic-v1')


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def fp(path):
    path = Path(path)
    digest, size = hashlib.sha256(), 0
    with path.open('rb') as source:
        for part in iter(lambda: source.read(1024 * 1024), b''):
            digest.update(part)
            size += len(part)
    return {'path': str(path), 'bytes': size, 'sha256': digest.hexdigest()}


def same(a, b):
    return isinstance(a, dict) and isinstance(b, dict) and all(
        key in a and key in b and a[key] == b[key] for key in ('bytes', 'sha256'))


def read(path):
    return json.loads(Path(path).read_text())


def canonical(path):
    path = Path(path).absolute()
    need('..' not in path.parts and not path.is_symlink() and path.resolve() == path,
         f'Noncanonical or symlinked path: {path}')
    return path


def within(root, path):
    root, path = canonical(root), canonical(path)
    need(path.is_relative_to(root), f'Path escapes root: {path} / {root}')
    return path


def disjoint(a, b):
    a, b = canonical(a), canonical(b)
    need(not a.is_relative_to(b) and not b.is_relative_to(a),
         f'Stage/input roots overlap: {a} / {b}')


def mkdir(stage, path, exist_ok=True):
    path = within(stage, path)
    path.mkdir(parents=True, exist_ok=exist_ok)
    within(stage, path)


def write_json(stage, path, value):
    path = within(stage, path)
    mkdir(stage, path.parent)
    within(stage, path)
    with path.open('x') as output:
        output.write(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def keep_json(stage, path, value):
    path = within(stage, path)
    if path.exists():
        need(read(path) == value, f'Frozen stage context changed: {path}')
    else:
        write_json(stage, path, value)
    return fp(path)


def pinned(path, expected):
    path = canonical(path)
    need(path.is_file() and same(fp(path), expected), f'Missing or changed pinned file: {path}')
    return fp(path)


def install_link(stage, source, destination, expected):
    """No cross-device fallback: old supplier object bytes are never copied."""
    source, destination = canonical(source), within(stage, destination)
    pinned(source, expected)
    mkdir(stage, destination.parent)
    within(stage, destination)
    if destination.exists():
        pinned(destination, expected)
    else:
        os.link(source, destination)
    return pinned(destination, expected)


def module_relative(module, suffix='.olean'):
    need(re.fullmatch(r'ImbalancedChen(?:\.[A-Za-z0-9_]+)+', module), 'Invalid project module')
    return Path(module.replace('.', '/') + suffix)


def sidecar_paths(obj):
    return (Path(str(obj) + '.server'), Path(str(obj) + '.private'), obj.with_suffix('.ir'))


def object_state(stage, obj):
    obj = within(stage, obj)
    sidecars = [fp(within(stage, p)) for p in sidecar_paths(obj) if p.exists() or p.is_symlink()]
    return {'object': fp(obj) if obj.exists() else None, 'sidecars': sidecars}


def check_object(stage, obj, expected, sidecars):
    need(expected is not None, 'Success receipt has no fixed object; restore its complete evidence')
    actual = object_state(stage, obj)
    need(actual['object'] == expected and actual['sidecars'] == sidecars,
         'RESTORE_EXACT_ACCEPTED_OBJECT: accepted normal object/sidecars are missing or changed')


def tree_signature(root):
    """Freeze every file of a runtime root without copying the runtime tree."""
    root = canonical(root)
    need(root.is_dir(), f'Missing runtime root: {root}')
    digest, count, size = hashlib.sha256(), 0, 0
    for parent, directories, files in os.walk(root, followlinks=False):
        directories.sort()
        files.sort()
        for name in directories:
            need(not (Path(parent) / name).is_symlink(), f'Symlinked runtime directory: {parent}/{name}')
        for name in files:
            path = Path(parent) / name
            link = os.readlink(path) if path.is_symlink() else None
            actual = path.resolve() if link is not None else canonical(path)
            need(actual.is_file(), f'Broken runtime file: {path}')
            pin = fp(actual)
            item = [str(path.relative_to(root)), link, str(actual), pin['bytes'], pin['sha256']]
            encoded = json.dumps(item, separators=(',', ':'), ensure_ascii=False).encode()
            digest.update(len(encoded).to_bytes(8, 'big'))
            digest.update(encoded)
            count += 1
            size += pin['bytes']
    need(count > 0, f'Empty runtime root: {root}')
    return {'root': str(root), 'files': count, 'file_bytes': size, 'sha256': digest.hexdigest()}


class Frozen:
    def __init__(self):
        self.files = {}

    def add(self, path, expected=None):
        path = canonical(path)
        actual = pinned(path, expected) if expected is not None else fp(path)
        old = self.files.setdefault(str(path), actual)
        need(old == actual, f'Conflicting frozen file: {path}')
        return actual

    def check(self):
        for path, pin in self.files.items():
            pinned(path, pin)


def load_helper(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def expected_argv(mode, run):
    if mode == 'kernel':
        return [run['checker'], '--verbose', TARGET]
    flags = ['-j1', f"-M{run['rss_gib'] * 1024}", '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    if mode == 'normal':
        return [run['lean'], *flags, '-o', run['object_path'],
                str(Path(run['source']['path']).relative_to(run['project']))]
    need(mode == 'owned', 'Unexpected proof mode')
    return [run['lean'], *flags, run['audit']['path']]


def parsed_imports(text, expected_projects):
    marker = 'P26_GEOMETRY01_AUDIT_IMPORTS '
    lines = [json.loads(line[len(marker):]) for line in text.splitlines() if line.startswith(marker)]
    need(len(lines) == 1 and len(lines[0]) == len(set(lines[0])), 'Missing/duplicate module inventory')
    names = lines[0]
    need({n for n in names if n.startswith('ImbalancedChen.')} == set(expected_projects),
         'Audit imported a different project module boundary')
    return names


def module_byte_context(names, roots):
    rows = []
    for name in sorted(names):
        need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*', name), 'Bad module name')
        relative = Path(name.replace('.', '/') + '.olean')
        namespace = name.split('.')[0]
        candidates = [Path(root) for root in roots
                      if (Path(root) / namespace).is_dir() or
                         (Path(root) / (namespace + '.olean')).is_file()]
        need(candidates, f'No fixed provider for imported module: {name}')
        path = canonical(candidates[0] / relative)
        need(path.is_file(), f'Missing module in first namespace provider: {name}')
        rows.append({'module': name, 'object': fp(path),
                     'sidecars': [fp(canonical(p)) for p in sidecar_paths(path) if p.exists()]})
    return rows


def validate_step(seal_path, stage, context_pin, source, audit, obj, owned_helper):
    """A success with broken evidence is an error, never a cache miss."""
    seal_path = within(stage, seal_path)
    seal = read(seal_path)
    mode = seal.get('mode')
    need(seal.get('module') == TARGET and mode in MODES and seal.get('status') == 'succeeded',
         f'Invalid accepted seal: {seal_path}')
    need(seal['source'] == source and seal['audit'] == audit and seal['context'] == context_pin,
         'Accepted source/audit/same-stage context differs')
    check_object(stage, obj, seal['object'], seal['object_sidecars'])
    for key in ('run', 'command', 'command_result', 'log', 'before', 'after'):
        ref = seal[key]
        pinned(within(stage, ref['path']), ref)
    run = read(seal['run']['path'])
    need(run['stage_context'] == context_pin and run['stage'] == str(stage) and
         run['module'] == TARGET and run['source'] == source and run['audit'] == audit and
         run['object_path'] == str(obj), 'Accepted run context differs')
    context = read(context_pin['path'])
    need(run['inputs'] == context['inputs'] and run['LEAN_PATH'] == context['LEAN_PATH'] and
         run['project'] == context['project'] and run['lean'] == context['lean_binary']['path'] and
         run['checker'] == context['leanchecker_binary']['path'], 'Accepted runtime differs')
    need(isinstance(run['rss_gib'], int) and 1 <= run['rss_gib'] <= 24 and
         isinstance(run['wall_seconds'], int) and 0 < run['wall_seconds'] <= 3300,
         'Invalid recorded command limits')
    command, result = read(seal['command']['path']), read(seal['command_result']['path'])
    need(result['status'] == 'succeeded' and result['exit_code'] == 0 and
         result['error'] is None and not result['timed_out'], 'Accepted command failed')
    need(result['command'] == seal['command'] and result['log'] == seal['log'],
         'Broken command/log/result chain')
    need(all(result.get(key) == value for key, value in command.items()), 'Command/result mismatch')
    need(command['module'] == TARGET and command['mode'] == mode and
         command['run'] == seal['run'] and command['source'] == source and
         command['audit'] == audit and command['context'] == context_pin and
         command['input_fingerprints'] == context['inputs'], 'Wrong command provenance')
    need(command['argv'] == expected_argv(mode, run) and
         command['cwd'] == run['project'] and command['LEAN_PATH'] == run['LEAN_PATH'] and
         command['wall_limit_seconds'] == run['wall_seconds'], 'Wrong required proof command')
    need(command['object_before'] is None if mode == 'normal'
         else command['object_before'] == seal['object'], 'Wrong prior object state')
    for key in ('before', 'after'):
        check = read(seal[key]['path'])
        need(check['status'] == 'ALL_FROZEN_BYTES_UNCHANGED' and
             check['context'] == context_pin and check['inputs'] == context['inputs'] and
             check['runtime_trees'] == context['runtime_trees'], 'Incomplete byte recheck')
    text = Path(seal['log']['path']).read_text()
    if mode == 'normal':
        axioms = {a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                  for a in group.split(',') if a.strip()}
        need(axioms <= ALLOWED and sorted(axioms) == seal['printed_axioms'],
             'Unexpected normal axioms')
    if mode == 'owned':
        for key in ('owned_declarations', 'module_byte_context'):
            pinned(within(stage, seal[key]['path']), seal[key])
        owned = owned_helper.parse_owned(text, TARGET)
        need(owned == read(seal['owned_declarations']['path']) and
             owned['owned_declaration_count'] == seal['owned_declaration_count'],
             'Owned inventory/type/axiom evidence differs')
        names = parsed_imports(text, context['project_modules'])
        need(module_byte_context(names, context['module_search_roots']) ==
             read(seal['module_byte_context']['path']), 'Imported module byte context changed')
    return seal


def scan_history(stage, context_pin, source, audit, obj, owned_helper):
    for name in ('accepted', 'attempts', 'objects', 'project', 'evidence', 'audit'):
        within(stage, stage / name)
    accepted = {}
    for anchor in sorted((stage / 'accepted').glob('*.json')):
        data = read(within(stage, anchor))
        need(data['mode'] in MODES, 'Unknown accepted anchor')
        pinned(within(stage, data['receipt']['path']), data['receipt'])
        seal = validate_step(data['receipt']['path'], stage, context_pin, source, audit, obj, owned_helper)
        need(seal['mode'] == data['mode'], 'Accepted anchor mode mismatch')
        accepted[data['mode']] = data['receipt']
    for attempt in sorted((stage / 'attempts').glob('*')):
        canonical(attempt)
        need(attempt.is_dir(), 'Unexpected attempt entry')
        for mode in MODES:
            folder = within(stage, attempt / 'steps' / mode)
            seal_path = within(stage, folder / 'ACCEPTED_STEP.json')
            result_path = within(stage, folder / 'result.json')
            if seal_path.exists() or seal_path.is_symlink():
                seal = validate_step(seal_path, stage, context_pin, source, audit, obj, owned_helper)
                need(seal['mode'] == mode, 'Step directory/mode differs')
                ref = fp(seal_path)
                need(mode not in accepted or accepted[mode] == ref, 'Multiple conflicting successful steps')
                accepted[mode] = ref
            elif result_path.exists() or result_path.is_symlink():
                result = read(within(stage, result_path))
                if result.get('status') == 'succeeded' or (
                    result.get('exit_code') == 0 and result.get('error') is None and
                    not result.get('timed_out')):
                    raise RuntimeError('RESTORE_SUCCESS_EVIDENCE_CHAIN: successful result has no accepted seal')
        final = within(stage, attempt / 'RESULT.json')
        if final.exists():
            value = read(within(stage, final))
            if value.get('status') == 'PASS_GENERIC_ORIGINAL_FLOOR_TRANSPORT':
                need(value['context'] == context_pin and value['source'] == source,
                     'Old successful attempt has another context')
                for record in value['records']:
                    pinned(within(stage, record['receipt']['path']), record['receipt'])
                    seal = validate_step(record['receipt']['path'], stage, context_pin, source, audit, obj, owned_helper)
                    need(seal['mode'] == record['mode'], 'Old success record mismatch')
                need([r['mode'] for r in value['records']] == list(MODES), 'Incomplete successful attempt')
    need(not accepted or 'normal' in accepted, 'Kernel/owned accepted without accepted normal')
    need('owned' not in accepted or 'kernel' in accepted, 'Owned accepted without accepted kernel')
    live = object_state(stage, obj)
    if 'normal' not in accepted:
        need(live['object'] is None and not live['sidecars'],
             'UNRECEIPTED_OBJECT: restore evidence; refusing normal overwrite/recompile')
    for mode, ref in accepted.items():
        keep_json(stage, stage / 'accepted' / (mode + '.json'), {'mode': mode, 'receipt': ref})
    return accepted


def load_package(package):
    package = canonical(package)
    manifest_path = package / 'PACKAGE_MANIFEST.json'
    manifest = read(manifest_path)
    frozen = Frozen()
    frozen.add(manifest_path)
    for row in manifest['files']:
        relative = Path(row['member'])
        need(not relative.is_absolute() and '..' not in relative.parts, 'Unsafe package member')
        frozen.add(within(package, package / relative), row)
    need(any(row['member'] == 'GenericFloor_verify.py' and same(fp(__file__), row)
             for row in manifest['files']), 'Unfrozen driver')
    registry = read(package / 'REGISTRY.json')
    need(registry['target'] == TARGET and registry['source']['sha256'] == SOURCE_SHA and
         registry['audit']['sha256'] == AUDIT_SHA and len(registry['suppliers']) == 233,
         'Wrong single-owner source or supplier boundary')
    shared = load_helper('p26_generic_shared', package / 'Cell00OriginalFloor_continue.py')
    owned = load_helper('p26_generic_owned', package / 'export_cell01_row000.py')
    return manifest, registry, frozen, shared, owned


def preflight(stage, package, registry, frozen, owned):
    disjoint(stage, package)
    origin = registry['origin']
    disjoint(stage, origin['attempt'])
    for pin in origin['pinned_files']:
        frozen.add(pin['path'], pin)
    old_run, old_inputs, old_result = (read(origin[key]['path']) for key in ('run', 'inputs', 'result'))
    need(old_run == registry['accepted_runtime'] and old_run['inputs'] == origin['inputs'] and
         len(old_inputs['canonical_modules']) == 1111 and old_result['status'] ==
         'PASS_CELL01_ROW000_ORIGINAL_FLOOR', 'Accepted P1 supplier context differs')
    need(old_result['context'] == origin['run'] and
         [r['mode'] for r in old_result['records']] == list(MODES), 'Incomplete origin acceptance')
    for record in old_result['records']:
        frozen.add(record['receipt']['path'], record['receipt'])
        seal = read(record['receipt']['path'])
        need(seal['module'] == old_run['target'] and seal['mode'] == record['mode'] and
             seal['status'] == 'succeeded' and seal['context'] == origin['run'] and
             seal['source'] == old_result['source'] and seal['object'] == old_result['object'] and
             seal['all_frozen_inputs_unchanged'] is True, 'Bad origin seal')
        for key in ('source', 'object', 'command_result', 'log'):
            frozen.add(seal[key]['path'], seal[key])
        result = read(seal['command_result']['path'])
        frozen.add(result['command']['path'], result['command'])
        command = read(result['command']['path'])
        need(result['status'] == 'succeeded' and result['exit_code'] == 0 and
             result['error'] is None and not result['timed_out'] and
             result['log'] == seal['log'] and
             all(result.get(k) == v for k, v in command.items()), 'Bad origin command chain')
        if record['mode'] == 'kernel':
            need(result['argv'] == [old_run['leanchecker_binary']['path'], '--verbose', old_run['target']],
                 'Origin did not use exact stock kernel replay')
        if record['mode'] == 'owned':
            for key in ('audit_source', 'owned_declarations'):
                frozen.add(seal[key]['path'], seal[key])
            need(owned.parse_owned(Path(seal['log']['path']).read_text(), old_run['target']) ==
                 read(seal['owned_declarations']['path']), 'Origin full owned inventory differs')
    project, objects = within(stage, stage / 'project'), within(stage, stage / 'objects')
    mkdir(stage, project)
    mkdir(stage, objects)
    modules, installations = set(), []
    for row in registry['suppliers']:
        module = row['module']
        need(module not in modules and module != TARGET, 'Duplicate/target supplier')
        modules.add(module)
        old = old_inputs['canonical_modules'][module]
        need(old == row['canonical'], f'Accepted canonical supplier changed: {module}')
        for kind, suffix, destination_root in [('source', '.lean', project), ('object', '.olean', objects)]:
            pin = row[kind]
            relative = module_relative(module, suffix)
            provider = Path(pin['path']).parents[len(relative.parts) - 1]
            disjoint(stage, provider)
            frozen.add(pin['path'], pin)
            destination = destination_root / relative
            installations.append(install_link(stage, pin['path'], destination, pin))
            frozen.add(destination, pin)
        for side in row['sidecars']:
            source = Path(side['path'])
            suffix = source.name[len(Path(row['object']['path']).stem):]
            need(suffix in ('.olean.server', '.olean.private', '.ir'), 'Unknown supplier sidecar')
            destination = objects / module_relative(module, suffix)
            frozen.add(source, side)
            installations.append(install_link(stage, source, destination, side))
            frozen.add(destination, side)
    need(len(modules) == 233, 'Wrong supplier count')
    for row in registry['suppliers']:
        imports = re.findall(r'^import\s+(ImbalancedChen\.[A-Za-z0-9_.]+)',
                             Path(row['source']['path']).read_text(), re.M)
        need(set(imports) <= modules, f'Supplier source closure is incomplete: {row["module"]}')
    for ext in registry['external_modules']:
        need(ext in old_inputs['external_modules'], 'External byte context differs from accepted P1 input')
        for pin in [ext['source'], ext['object'], *ext['sidecars']]:
            frozen.add(pin['path'], pin)
    source = project / module_relative(TARGET, '.lean')
    audit = stage / 'audit' / (TARGET.split('.')[-1] + '.lean')
    for origin_path, destination, pin in [
            (package / registry['source_member'], source, registry['source']),
            (package / registry['audit_member'], audit, registry['audit'])]:
        frozen.add(origin_path, pin)
        install_link(stage, origin_path, destination, pin)
        frozen.add(destination, pin)
    need(set(re.findall(r'^import\s+(ImbalancedChen\.[A-Za-z0-9_.]+)', source.read_text(), re.M))
         <= modules, 'Missing new-owner import')
    need({p for p in project.rglob('*') if p.is_file() or p.is_symlink()} ==
         {project / module_relative(name, '.lean') for name in modules | {TARGET}},
         'Unpinned source in isolated namespace')
    runtime_roots = [canonical(p) for p in old_run['LEAN_PATH'].split(os.pathsep)[1:]]
    for root in runtime_roots:
        disjoint(stage, root)
        need(not (root / 'ImbalancedChen').exists(), 'Runtime root contains project namespace fallback')
    for key in ('lean_binary', 'leanchecker_binary'):
        frozen.add(old_run[key]['path'], old_run[key])
    toolchain_lib = canonical(Path(old_run['lean_binary']['path']).parent.parent / 'lib')
    disjoint(stage, toolchain_lib)
    roots = list(dict.fromkeys([*runtime_roots, toolchain_lib]))
    signatures = [tree_signature(root) for root in roots]
    obj = within(stage, objects / module_relative(TARGET))
    allowed = {objects / module_relative(row['module']) for row in registry['suppliers']}
    allowed |= {objects / module_relative(row['module'], Path(side['path']).name[
        len(Path(row['object']['path']).stem):]) for row in registry['suppliers'] for side in row['sidecars']}
    allowed |= {obj, *sidecar_paths(obj)}
    need({p for p in objects.rglob('*') if p.is_file() or p.is_symlink()} <= allowed,
         'Unpinned object in isolated namespace')
    inputs = {'files': [frozen.files[k] for k in sorted(frozen.files)],
              'supplier_modules': sorted(modules), 'installed_files': installations,
              'runtime_trees': signatures, 'source_generation': False, 'supplier_recompiled': False}
    input_pin = keep_json(stage, stage / 'INPUT_FINGERPRINTS.json', inputs)
    context = {'schema': 'p26_single_generic_floor_context_v1', 'module': TARGET, 'stage': str(stage),
        'project': str(project), 'objects': str(objects), 'source': fp(source), 'audit': fp(audit),
        'inputs': input_pin, 'registry': fp(package / 'REGISTRY.json'),
        'package_manifest': fp(package / 'PACKAGE_MANIFEST.json'),
        'lean_binary': old_run['lean_binary'], 'leanchecker_binary': old_run['leanchecker_binary'],
        'accepted_lean_version': old_run['lean_version'], 'package_revisions': old_run['package_revisions'],
        'runtime_trees': signatures, 'runtime_roots': list(map(str, roots)),
        'project_modules': sorted(modules | {TARGET}),
        'module_search_roots': list(map(str, [objects, *runtime_roots, toolchain_lib / 'lean'])),
        'LEAN_PATH': os.pathsep.join(map(str, [objects, *runtime_roots])),
        'accepted_supplier_count': 233, 'old_supplier_commands': 0,
        'origin_context': origin['run'], 'old_evidence_bodies_copied': False,
        'cloud_Lean_source_generation': False, 'new_concrete_row_claim': False}
    context_pin = keep_json(stage, stage / 'CONTEXT.json', context)
    frozen.add(input_pin['path'], input_pin)
    frozen.add(context_pin['path'], context_pin)
    return context, context_pin, frozen, source, audit, obj


def recheck(stage, path, context, context_pin, frozen):
    frozen.check()
    project, objects = Path(context['project']), Path(context['objects'])
    need({p for p in project.rglob('*') if p.is_file() or p.is_symlink()} ==
         {project / module_relative(name, '.lean') for name in context['project_modules']},
         'Project source namespace changed')
    inputs = read(context['inputs']['path'])
    fixed_objects = {Path(pin['path']) for pin in inputs['installed_files']
                     if Path(pin['path']).is_relative_to(objects)}
    obj = objects / module_relative(TARGET)
    need({p for p in objects.rglob('*') if p.is_file() or p.is_symlink()} <=
         fixed_objects | {obj, *sidecar_paths(obj)}, 'Project object namespace changed')
    actual = [tree_signature(root) for root in context['runtime_roots']]
    need(actual == context['runtime_trees'], 'Runtime module byte context changed')
    value = {'status': 'ALL_FROZEN_BYTES_UNCHANGED', 'context': context_pin,
             'inputs': context['inputs'], 'file_count': len(frozen.files), 'runtime_trees': actual}
    write_json(stage, path, value)
    return fp(path)


def archive_success(stage, package, attempt, context_pin, source, audit, obj):
    paths = {}
    def add(path, member):
        path = canonical(path)
        need(path.is_file() and member not in paths and not Path(member).is_absolute() and
             '..' not in Path(member).parts, 'Unsafe/duplicate evidence member')
        paths[member] = path
    add(source, str(source.relative_to(stage)))
    add(audit, str(audit.relative_to(stage)))
    for path in [obj, *[p for p in sidecar_paths(obj) if p.exists()]]:
        add(path, str(path.relative_to(stage)))
    for name in ('INPUT_FINGERPRINTS.json', 'CONTEXT.json'):
        add(stage / name, name)
    for root in (stage / 'attempts', stage / 'accepted'):
        for path in sorted(root.rglob('*')):
            need(not path.is_symlink(), 'Symlinked history in export')
            if path.is_file():
                need(path.suffix in ('.json', '.log'), 'Unexpected history body in evidence export')
                add(path, str(path.relative_to(stage)))
    for row in read(package / 'PACKAGE_MANIFEST.json')['files']:
        path = within(package, package / row['member'])
        pinned(path, row)
        add(path, 'frozen-package/' + row['member'])
    add(package / 'PACKAGE_MANIFEST.json', 'frozen-package/PACKAGE_MANIFEST.json')
    target_objects = {obj, *sidecar_paths(obj)}
    need(all(not ('.olean' in Path(name).suffixes or Path(name).suffix == '.ir') or
             path in target_objects for name, path in paths.items()),
         'Supplier object body entered evidence')
    entries = [{'member': name, **fp(path)} for name, path in sorted(paths.items())]
    manifest = {'schema': 'p26_single_generic_floor_evidence_v1', 'target': TARGET, 'context': context_pin,
                'files': entries, 'supplier_object_bodies_included': False,
                'old_supplier_evidence_bodies_included': False, 'cloud_in_place_only': True}
    data = (json.dumps(manifest, indent=2) + '\n').encode()
    output = within(stage, stage / 'evidence' / (attempt.name + '.tar.xz'))
    mkdir(stage, output.parent)
    within(stage, output)
    with output.open('xb') as raw, tarfile.open(fileobj=raw, mode='w:xz', format=tarfile.PAX_FORMAT) as tar:
        for name, path in sorted(paths.items()):
            pin = next(item for item in entries if item['member'] == name)
            pinned(path, pin)
            info = tarfile.TarInfo(name); info.size = pin['bytes']; info.mode = 0o644
            with path.open('rb') as incoming:
                tar.addfile(info, incoming)
        info = tarfile.TarInfo('MANIFEST.json'); info.size = len(data); info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
    result = {'archive': fp(output), 'members': len(entries) + 1, 'context': context_pin,
              'supplier_object_bodies_included': False, 'retrieval_requested': False}
    manifest_path = output.with_suffix('.manifest.json')
    write_json(stage, manifest_path, {**manifest, **result})
    return {**result, 'manifest': fp(manifest_path)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    parser.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime(
        '%Y%m%dT%H%M%S%fZ') + '-' + uuid.uuid4().hex[:8])
    parser.add_argument('--rss-gib', type=int, default=6)
    parser.add_argument('--wall-seconds', type=int, default=900)
    args = parser.parse_args()
    need(re.fullmatch(r'[A-Za-z0-9_-]+', args.attempt), 'Unsafe attempt name')
    need(1 <= args.rss_gib <= 24 and 0 < args.wall_seconds <= 3300, 'Invalid limits')
    stage, package = canonical(args.stage), canonical(Path(__file__).parent)
    disjoint(stage, package)
    manifest, registry, frozen, shared, owned = load_package(package)
    # Reject stage nesting before any write, including every selected provider.
    disjoint(stage, registry['accepted_runtime']['stage'])
    for name in ('accepted', 'attempts', 'objects', 'project', 'evidence', 'audit'):
        within(stage, stage / name)
    for row in registry['suppliers']:
        for kind, suffix in [('source', '.lean'), ('object', '.olean')]:
            relative = module_relative(row['module'], suffix)
            disjoint(stage, Path(row[kind]['path']).parents[len(relative.parts) - 1])
    for root in registry['accepted_runtime']['LEAN_PATH'].split(os.pathsep)[1:]:
        disjoint(stage, root)
    for ext in registry['external_modules']:
        for kind, suffix in [('source', '.lean'), ('object', '.olean')]:
            relative = Path(ext['module'].replace('.', '/') + suffix)
            disjoint(stage, Path(ext[kind]['path']).parents[len(relative.parts) - 1])
    for key in ('lean_binary', 'leanchecker_binary'):
        disjoint(stage, Path(registry['accepted_runtime'][key]['path']).parent.parent)
    context, context_pin, frozen, source, audit, obj = preflight(stage, package, registry, frozen, owned)
    accepted = scan_history(stage, context_pin, fp(source), fp(audit), obj, owned)
    if 'normal' in accepted:
        for pin in [fp(obj), *object_state(stage, obj)['sidecars']]:
            frozen.add(pin['path'], pin)
    attempt = within(stage, stage / 'attempts' / args.attempt)
    mkdir(stage, attempt, exist_ok=False)
    run = {'schema': 'p26_single_generic_floor_attempt_v1', 'stage': str(stage), 'module': TARGET,
           'stage_context': context_pin, 'inputs': context['inputs'], 'attempt': args.attempt,
           'project': context['project'], 'LEAN_PATH': context['LEAN_PATH'],
           'source': fp(source), 'audit': fp(audit), 'object_path': str(obj),
           'lean': context['lean_binary']['path'], 'checker': context['leanchecker_binary']['path'],
           'rss_gib': args.rss_gib, 'wall_seconds': args.wall_seconds}
    write_json(stage, attempt / 'RUN.json', run)
    run_pin = fp(attempt / 'RUN.json')
    frozen.add(run_pin['path'], run_pin)
    env = os.environ.copy()
    env.pop('LEAN_SRC_PATH', None); env.pop('LEAN_SYSROOT', None)
    env['PATH'] = str(Path(run['lean']).parent) + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = run['LEAN_PATH']
    env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
    records, commands = [], 0
    try:
        for mode in MODES:
            if mode in accepted:
                validate_step(accepted[mode]['path'], stage, context_pin, fp(source), fp(audit), obj, owned)
                records.append({'mode': mode, 'receipt': accepted[mode], 'reused': True})
                continue
            folder = within(stage, attempt / 'steps' / mode)
            need(not folder.exists(), 'Refusing step-directory overwrite')
            mkdir(stage, folder.parent)
            for child in ('command.json', 'result.json', 'output.log', 'ACCEPTED_STEP.json'):
                within(stage, folder / child)
            before = recheck(stage, attempt / 'checks' / (mode + '-before.json'), context, context_pin, frozen)
            live = object_state(stage, obj)
            if mode == 'normal':
                need(live['object'] is None and not live['sidecars'], 'UNRECEIPTED_OBJECT')
            else:
                need('normal' in accepted, 'Missing accepted normal step')
                normal = read(accepted['normal']['path'])
                check_object(stage, obj, normal['object'], normal['object_sidecars'])
            within(stage, obj); within(stage, folder)
            argv = expected_argv(mode, run)
            metadata = {'module': TARGET, 'mode': mode, 'run': run_pin, 'context': context_pin,
                        'source': fp(source), 'audit': fp(audit), 'object_before': live['object'],
                        'input_fingerprints': context['inputs']}
            print(json.dumps({'mode': mode, 'running': True, 'supplier_commands': 0}), flush=True)
            commands += 1
            result = shared.run_command(argv, run['project'], env, folder, args.wall_seconds, metadata)
            after = recheck(stage, attempt / 'checks' / (mode + '-after.json'), context, context_pin, frozen)
            state = object_state(stage, obj)
            need(state['object'] is not None, 'Proof command produced no target object')
            if mode != 'normal':
                need(state == live, 'Target object changed during checking')
            for pin in [state['object'], *state['sidecars']]:
                frozen.add(pin['path'], pin)
            seal = {'status': 'succeeded', 'module': TARGET, 'mode': mode,
                    'source': fp(source), 'audit': fp(audit), 'object': state['object'],
                    'object_sidecars': state['sidecars'], 'run': run_pin, 'context': context_pin,
                    'command': fp(folder / 'command.json'), 'command_result': fp(folder / 'result.json'),
                    'log': result['log'], 'before': before, 'after': after}
            text = Path(result['log']['path']).read_text()
            if mode == 'normal':
                axioms = {a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                          for a in group.split(',') if a.strip()}
                need(axioms <= ALLOWED, 'Forbidden normal transitive axiom')
                seal['printed_axioms'] = sorted(axioms)
            if mode == 'owned':
                inventory = owned.parse_owned(text, TARGET)
                names = parsed_imports(text, context['project_modules'])
                byte_context = module_byte_context(names, context['module_search_roots'])
                write_json(stage, folder / 'owned-declarations.json', inventory)
                write_json(stage, folder / 'module-byte-context.json', byte_context)
                seal.update({'owned_declarations': fp(folder / 'owned-declarations.json'),
                             'module_byte_context': fp(folder / 'module-byte-context.json'),
                             'owned_declaration_count': inventory['owned_declaration_count']})
            write_json(stage, folder / 'ACCEPTED_STEP.json', seal)
            seal_path = folder / 'ACCEPTED_STEP.json'
            validate_step(seal_path, stage, context_pin, fp(source), fp(audit), obj, owned)
            ref = fp(seal_path)
            keep_json(stage, stage / 'accepted' / (mode + '.json'), {'mode': mode, 'receipt': ref})
            accepted[mode] = ref
            records.append({'mode': mode, 'receipt': ref, 'reused': False})
        recheck(stage, attempt / 'checks' / 'final.json', context, context_pin, frozen)
        result = {'status': 'PASS_GENERIC_ORIGINAL_FLOOR_TRANSPORT', 'module': TARGET,
                  'context': context_pin, 'source': fp(source), 'object': fp(obj), 'records': records,
                  'new_proof_commands': commands, 'supplier_proof_commands': 0,
                  'new_concrete_row_claim': False, 'P2_6_complete_claimed': False}
        write_json(stage, attempt / 'RESULT.json', result)
        evidence = archive_success(stage, package, attempt, context_pin, source, audit, obj)
        print(json.dumps({'status': result['status'], 'attempt': str(attempt),
                          'new_proof_commands': commands, 'evidence': evidence}), flush=True)
        return 0
    except Exception as error:
        failure = {'status': 'FAILED_STOPPED', 'error': f'{type(error).__name__}: {error}',
                   'context': context_pin, 'records': records, 'new_proof_commands': commands,
                   'supplier_proof_commands': 0}
        if not (attempt / 'RESULT.json').exists():
            write_json(stage, attempt / 'RESULT.json', failure)
        print(json.dumps(failure), file=sys.stderr, flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
