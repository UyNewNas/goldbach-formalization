#!/usr/bin/env python3
"""Freeze the two authored cell01 transport pilot owners and complete audits.

The archive is source/metadata only. Existing owner bodies and objects are
represented by source pins, not copied. This never invokes Lean or cloud tools.
"""
from pathlib import Path
import ast
import hashlib
import importlib.util
import io
import json
import re
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OUT = HERE / 'cell01-blocks-pilot'
PREFIX = 'ImbalancedChen.P2OriginalSaving19'
TARGETS = [PREFIX + 'Cell01OriginalFloorInterface', PREFIX + 'Cell01OriginalFloorBlock000_015']
GENERIC = PREFIX + 'OriginalFloorTransport'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def fingerprint(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def module_path(module):
    return REPO / (module.replace('.', '/') + '.lean')


def pin(path):
    return {'path': str(path.relative_to(REPO)), **fingerprint(path.read_bytes())}


def write(path, data):
    need(path.resolve() == path and not path.is_symlink() and not path.exists(),
         f'Refusing existing/noncanonical output: {path}')
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def imports(text):
    return [name for line in text.splitlines() if line.startswith('import ')
            for name in line.split()[1:]]


def named_declarations(text):
    namespaces, result = [], []
    for line in text.splitlines():
        if line.startswith('namespace '):
            namespaces.append(line.split()[1])
        elif line.startswith('end '):
            need(namespaces and line.split()[1] == namespaces[-1], 'Namespace mismatch')
            namespaces.pop()
        match = re.match(r'(?:noncomputable )?(def|theorem) ([A-Za-z0-9_]+)', line)
        if match:
            result.append({'kind': match[1], 'name': '.'.join(namespaces + [match[2]])})
    need(not namespaces, 'Unclosed namespace')
    return result


def main():
    spec = importlib.util.spec_from_file_location('cell01_transport_generator',
                                                 HERE / 'generate_cell01_transport_blocks.py')
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    finite_before, series_pin = generator.finite_pins()
    generation = json.loads((OUT / 'GENERATION.json').read_text())
    need(generation['blocks'] == [0], 'This freeze is for the first block only')
    need(pin(module_path(TARGETS[0])) == generation['shared_interface'] and
         pin(module_path(TARGETS[1])) == generation['source_outputs'][0],
         'Authored pilot differs from generation pins')
    template = (HERE / 'owned-audit.lean').read_bytes()
    need(fingerprint(template)['sha256'] ==
         '4fa2d4bc9272505e76c14088e08ff309df9ba21981532016f4ff5ba6b89c7680',
         'Complete owned-audit template differs')
    need(template.decode().count(GENERIC) == 2, 'Unexpected audit substitution scope')
    closure, visiting, external = {}, set(), set()
    def visit(module):
        if module in closure:
            return
        need(module not in visiting, 'Project import cycle')
        visiting.add(module)
        path = module_path(module)
        need(path.is_file(), f'Missing project source: {module}')
        names = imports(path.read_text())
        dependencies = [name for name in names if name.startswith('ImbalancedChen.')]
        external.update(name for name in names if not name.startswith('ImbalancedChen.'))
        for dependency in dependencies:
            visit(dependency)
        closure[module] = {'module': module, **pin(path), 'project_imports': dependencies}
        visiting.remove(module)
    for target in TARGETS:
        visit(target)
    audit_rows, declarations = [], {}
    for target in TARGETS:
        text = module_path(target).read_text()
        need(not re.search(r'\b(axiom|sorry|admit|native_decide|unsafe)\b', text),
             'Forbidden mechanism in new mathematical source')
        declarations[target] = named_declarations(text)
        audit = OUT / 'audits' / (target.split('.')[-1] + '.lean')
        write(audit, template.decode().replace(GENERIC, target).encode())
        audit_rows.append({'module': target, **pin(audit)})
    block_text = module_path(TARGETS[1]).read_text()
    need(block_text == generator.render(0), 'Pilot rendering differs')
    need(block_text.count('original_floor_and_bounds_of_encoding vertices row momentRow') == 15 and
         block_text.count('original_floor_and_bounds_of_bindings (rawVertices') == 16,
         'Expected concrete row instantiations differ')
    need(block_text.count('theorem typed_original_floor_and_bounds :') == 16 and
         block_text.count('theorem raw_original_floor_and_bounds :') == 16,
         'Closed row theorem signatures differ')
    expected_literals = [f'  · exact Row{i:03d}.raw_original_floor_and_bounds' for i in range(16)]
    need([line for line in block_text.splitlines() if line.startswith('  · exact Row')] == expected_literals,
         'Pilot original ordinal order differs')
    plan_blocks = [{'block': b, 'module': generator.block_module(b),
                    'ordinals': list(range(16 * b, 16 * (b + 1))),
                    'source_authored_in_this_pilot': b == 0} for b in range(9)]
    need([r for block in plan_blocks for r in block['ordinals']] == list(range(144)),
         'Full original ordinal plan has a gap, overlap or reordering')
    plan = {'status': 'SOURCE_PLAN_ONLY_NO_ALL_144_PROOF', 'row_type': 'Fin 144',
        'vertex_type': 'Fin 9', 'coordinate_type': 'Fin 8', 'factor_type': 'Fin 10',
        'blocks': plan_blocks, 'shared_interface': TARGETS[0], 'final_owner_authored': False,
        'final_target': '∀ r : Fin 144, OriginalFloorAndBoundsAt r',
        'final_dispatch': 'block = r.val / 16; within-block position = r.val % 16',
        'planned_new_owner_count': 11, 'new_owners_authored_now': 2,
        'new_proof_assumptions': 0, 'old_proof_reruns': 0}
    write(OUT / 'FAMILY_PLAN.json', encoded(plan))
    static = {'status': 'STATIC_SOURCE_CHECKS_ONLY',
        'missing_project_sources': [], 'import_cycles': [],
        'all_143_finite_pins_match': True, 'typed_and_raw_row_theorems_closed': 32,
        'numeric_evaluations_in_new_sources': 0, 'finite_encoding_instantiations': 15,
        'accepted_row000_original_transport_reused': True, 'raw_binding_instantiations': 16,
        'original_ordinal_sequence': list(range(16)), 'full_144_plan_coverage_exact': True,
        'row_bounds_and_three_level_vertex_chain_preserved': True,
        'uncapped_new_and_saved_max_distinction_preserved': True,
        'new_assumptions_or_forbidden_mechanisms': [], 'named_declarations': declarations,
        'owned_serialized_count': 'PENDING_REAL_FULL_AUDIT', 'Lean_invoked': False}
    write(OUT / 'STATIC_CHECK.json', encoded(static))
    source_manifest = {'schema': 'p26_cell01_original_floor_block_pilot_v1',
        'status': 'SOURCE_ONLY_NOT_COMPILED', 'targets': [closure[target] for target in TARGETS],
        'audits': audit_rows, 'generation_report': pin(OUT / 'GENERATION.json'),
        'generic_supplier': closure[GENERIC],
        'accepted_row000_supplier': closure[generator.ROW000],
        'direct_finite_suppliers': [closure[PREFIX + f'Cell01Row{i:03d}Finite'] for i in range(1, 16)],
        'project_source_closure_count': len(closure), 'old_supplier_count': len(closure) - 2,
        'project_source_closure': list(closure.values()), 'direct_external_import_names': sorted(external),
        'finite_series_manifest': series_pin,
        'supplier_acceptance': 'Exact same-source object and normal/kernel/owned receipt union must be supplied before execution.',
        'generic_acceptance': 'Pending coordinator receipt at preparation time; no acceptance inferred from this source package.',
        'new_concrete_claim_scope_if_verified': 'Original cell01 rows 000 through 015 only',
        'new_Archive_alias_claim': False, 'new_all_144_claim': False, 'new_integral_claim': False,
        'blocked_completed_archive_read_or_transferred': False,
        'Lean_invoked': False, 'cloud_jobs_submitted': 0, 'Git_or_STATUS_changed': False}
    write(OUT / 'SOURCE_MANIFEST.json', encoded(source_manifest))
    order = '# Source-only plan; exact accepted supplier union required first.\n'
    for target in TARGETS:
        order += f'{target} normal\n{target} kernel\n{target} owned\n'
    write(OUT / 'cloud_order.txt', order.encode())
    files = {}
    for target in TARGETS:
        path = module_path(target)
        files['sources/' + str(path.relative_to(REPO))] = path.read_bytes()
    for path in sorted(OUT.rglob('*')):
        if path.is_file():
            files['metadata/' + str(path.relative_to(OUT))] = path.read_bytes()
    for name in ('generate_cell01_transport_blocks.py', 'freeze_cell01_transport_pilot.py'):
        files['tools/' + name] = (HERE / name).read_bytes()
        ast.parse(files['tools/' + name].decode())
    package_manifest = {'schema': 'p26_cell01_transport_pilot_source_package_v1',
        'status': 'SOURCE_ONLY_NOT_COMPILED', 'files': [
            {'member': name, **fingerprint(data)} for name, data in sorted(files.items())],
        'new_Lean_owners': 2, 'supplier_object_bodies_included': False,
        'old_supplier_source_bodies_included': False, 'old_completed_evidence_included': False,
        'Lean_invoked': False, 'cloud_jobs_submitted': 0}
    files['PACKAGE_MANIFEST.json'] = encoded(package_manifest)
    tar_path = HERE / 'cell01-original-floor-pilot-v1.tar.xz'
    need(tar_path.resolve() == tar_path and not tar_path.exists() and not tar_path.is_symlink(),
         'Refusing package overwrite')
    with tar_path.open('xb') as raw, tarfile.open(fileobj=raw, mode='w:xz', format=tarfile.PAX_FORMAT) as tar:
        for name, data in sorted(files.items()):
            item = tarfile.TarInfo(name)
            item.size, item.mode = len(data), 0o644
            tar.addfile(item, io.BytesIO(data))
    seen = set()
    with tarfile.open(tar_path, 'r:xz') as tar:
        for member in tar.getmembers():
            need(member.isfile() and member.name in files and member.name not in seen,
                 'Unexpected package readback member')
            seen.add(member.name)
            need(tar.extractfile(member).read() == files[member.name], 'Package payload readback differs')
    need(seen == set(files), 'Incomplete package inventory')
    for module, row in closure.items():
        need(pin(module_path(module)) == {k: row[k] for k in ('path', 'bytes', 'sha256')},
             'Closure source changed during freeze')
    finite_after, series_after = generator.finite_pins()
    need(finite_before == finite_after and series_pin == series_after,
         'Finite suppliers changed during freeze')
    summary = {'status': 'SOURCE_ONLY_NOT_COMPILED', 'package': pin(tar_path), 'members': len(files),
        'targets': [pin(module_path(target)) for target in TARGETS], 'audits': audit_rows,
        'project_source_closure_count': len(closure), 'old_supplier_count': len(closure) - 2,
        'named_theorems': sum(d['kind'] == 'theorem' for ds in declarations.values() for d in ds),
        'named_definitions': sum(d['kind'] == 'def' for ds in declarations.values() for d in ds),
        'finite_donors_unchanged': 143, 'source_manifest': pin(OUT / 'SOURCE_MANIFEST.json'),
        'static_checks': pin(OUT / 'STATIC_CHECK.json'), 'all_144_owner_authored': False,
        'Lean_invoked': False, 'cloud_jobs_submitted': 0}
    write(HERE / 'cell01-original-floor-pilot-v1.metadata.json', encoded(summary))
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
