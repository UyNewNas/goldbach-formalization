#!/usr/bin/env python3
"""Author or freeze the original 144-row transport family locally.

The --author step writes only the new final aggregation owner. The --freeze
step requires all eleven unchanged authored sources and writes source-only
evidence. Neither mode invokes Lean, a cloud command, Git, or a proof runner.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import importlib.util
import io
import json
import re
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OUT = HERE / 'cell01-family'
PREFIX = 'ImbalancedChen.P2OriginalSaving19'
INTERFACE = PREFIX + 'Cell01OriginalFloorInterface'
FINAL = PREFIX + 'Cell01AllOriginalFloorBridge'
GENERIC = PREFIX + 'OriginalFloorTransport'
PILOT_INTERFACE_SHA = 'dcfebb22ceae165a75e78fbc612a4b0d46ef3381e81cf637f71d6d45c8d5d504'
PILOT_BLOCK_SHA = '78c649f07f8000949d807a800162eaa1c8025cd335b0a4370144510456346b66'
PILOT_PACKAGE_SHA = 'e41581d10a25f95d59ddd1b679b69dc55efd06fa79ce4346ba8c0f4b5fb45f65'
GENERIC_SHA = '9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def module_path(module):
    return REPO / (module.replace('.', '/') + '.lean')


def fingerprint(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


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


def render_endpoint(generator):
    text = '\n'.join('import ' + generator.block_module(b) for b in range(9))
    text += '\nimport Mathlib.Tactic.FinCases\n'
    text += f'''
/-!
SOURCE CANDIDATE / NOT COMPILED. The original cell01 Fin 144 aggregation.
Every branch uses one closed 16-row block theorem at the original ordinal.
No floor target, arithmetic condition, moment identity, or integral bound is
assumed. No assertion of kernel acceptance follows from this candidate source.
-/
namespace {FINAL}

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ALL_ORIGINAL_FLOOR_before_144_branches"
  err.flush

/-- All original rows, without a smaller subset guard or a floor premise. -/
theorem all_original_floor_and_bounds :
    ∀ r : Fin 144, OriginalFloorAndBoundsAt r := by
  intro r
  fin_cases r
'''
    for ordinal in range(144):
        block, position = divmod(ordinal, 16)
        name = generator.block_module(block).removeprefix('ImbalancedChen.')
        text += f'  · exact {name}.all_original_floor_and_bounds ({position} : Fin 16)\n'
    text += '''
theorem all_original_floor_formula (r : Fin 144) :
    OriginalFloorChecksFor (rawGeometryRow r) (rawMomentRow r) (rawOriginalMoments r) :=
  (all_original_floor_and_bounds r).1

theorem all_original_Q80_bounds (r : Fin 144) :
    OriginalQ80BoundsFor (rawMomentRow r) (rawOriginalMoments r) :=
  (all_original_floor_and_bounds r).2

#print axioms all_original_floor_and_bounds
#print axioms all_original_floor_formula
#print axioms all_original_Q80_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ALL_ORIGINAL_FLOOR_144_branches_complete"
  err.flush
'''
    return text + '\nend ' + FINAL + '\n'


def verify_authored_inputs(generator):
    finite, finite_series = generator.finite_pins()
    need(pin(module_path(INTERFACE))['sha256'] == PILOT_INTERFACE_SHA, 'Pilot interface changed')
    need(pin(module_path(generator.block_module(0)))['sha256'] == PILOT_BLOCK_SHA, 'Pilot block changed')
    need(pin(HERE / 'cell01-original-floor-pilot-v1.tar.xz')['sha256'] == PILOT_PACKAGE_SHA,
         'Frozen pilot package changed')
    need(pin(module_path(GENERIC))['sha256'] == GENERIC_SHA, 'Generic source changed')
    need(pin(module_path(generator.ROW000))['sha256'] == generator.ROW000_SHA,
         'Accepted row000 original bridge changed')
    for block in range(9):
        need(module_path(generator.block_module(block)).read_text() == generator.render(block),
             f'Block {block} differs from unchanged generator rendering')
    return finite, finite_series


def author(generator):
    before, series = verify_authored_inputs(generator)
    text = render_endpoint(generator)
    need(not re.search(r'\b(axiom|sorry|admit|native_decide|unsafe)\b', text),
         'Forbidden mechanism in final owner')
    path = module_path(FINAL)
    write(path, text.encode())
    after, after_series = verify_authored_inputs(generator)
    need(before == after and series == after_series, 'Original suppliers changed during authoring')
    report = {'status': 'SOURCE_ONLY_NOT_COMPILED', 'module': FINAL, 'source': pin(path),
        'block_sources': [pin(module_path(generator.block_module(b))) for b in range(9)],
        'original_ordinals': list(range(144)), 'branch_count': 144,
        'block_position_pairs': [[r // 16, r % 16] for r in range(144)],
        'target': '∀ r : Fin 144, OriginalFloorAndBoundsAt r',
        'proof_premises': [], 'all_143_finite_sources_unchanged': True,
        'pilot_sources_and_package_unchanged': True, 'generic_source_unchanged': True,
        'numeric_calculations': 0, 'Lean_invoked': False, 'cloud_jobs_submitted': 0,
        'Git_or_STATUS_changed': False}
    write(OUT / 'ENDPOINT_GENERATION.json', encoded(report))
    print(json.dumps({'source': pin(path), 'report': pin(OUT / 'ENDPOINT_GENERATION.json'),
                      'status': report['status']}, indent=2))


def freeze(generator):
    before, series = verify_authored_inputs(generator)
    need(module_path(FINAL).read_text() == render_endpoint(generator), 'Final source rendering differs')
    review_path = HERE / 'cell01-blocks-pilot/INDEPENDENT_MATH_REVIEW.json'
    review_bytes = review_path.read_bytes()
    need(fingerprint(review_bytes)['sha256'] ==
         'd4915ee4954581ee5107f0c27c0636d3860dbc30558ec1ee804cd52eccd996cd',
         'Independent pilot/endpoint source review differs')
    review = json.loads(review_bytes)
    need(review['status'] == 'PASS_STATIC_MATHEMATICAL_AND_ORIGINAL_DATA_REVIEW_NOT_LEAN_ACCEPTANCE'
         and not review['blocking_findings'], 'Independent source review has an unresolved blocker')
    delta_path = OUT / 'SUPPLIER_DELTA.json'
    delta = json.loads(delta_path.read_text())
    need(delta['supplier_count'] == 791 and delta['exact_canonical_source_matches'] == 646 and
         not delta['same_module_source_conflicts'] and
         delta['other_unclassified_or_unverified_owner_count'] == 0,
         'Unresolved P1 supplier source-pin delta')
    helper = load('cell01_pilot_freeze_helpers', HERE / 'freeze_cell01_transport_pilot.py')
    targets = [INTERFACE] + [generator.block_module(b) for b in range(9)] + [FINAL]
    template = (HERE / 'owned-audit.lean').read_bytes()
    need(fingerprint(template)['sha256'] ==
         '4fa2d4bc9272505e76c14088e08ff309df9ba21981532016f4ff5ba6b89c7680' and
         template.decode().count(GENERIC) == 2, 'Full owned audit template changed')
    closure, visiting, external = {}, set(), set()
    def visit(module):
        if module in closure:
            return
        need(module not in visiting, 'Project import cycle')
        visiting.add(module)
        path = module_path(module)
        need(path.is_file(), f'Missing project source: {module}')
        names = helper.imports(path.read_text())
        dependencies = [name for name in names if name.startswith('ImbalancedChen.')]
        external.update(name for name in names if not name.startswith('ImbalancedChen.'))
        for dependency in dependencies:
            visit(dependency)
        closure[module] = {'module': module, **pin(path), 'project_imports': dependencies}
        visiting.remove(module)
    for target in targets:
        visit(target)
    compared = {row['module']: row['family_source'] for row in delta['matched_canonical_suppliers']}
    compared.update({row['module']: row for row in delta['additional_suppliers']})
    need(set(compared) == set(closure) - set(targets), 'Supplier comparison does not cover the exact closure')
    for module, row in compared.items():
        need(all(row[key] == closure[module][key] for key in ('path', 'bytes', 'sha256')),
             'Supplier delta source pin drifted')
    write(OUT / 'INDEPENDENT_PILOT_AND_ENDPOINT_REVIEW.json', review_bytes)
    declarations, audits = {}, []
    for target in targets:
        text = module_path(target).read_text()
        need(not re.search(r'\b(axiom|sorry|admit|native_decide|unsafe)\b', text),
             'Forbidden mechanism in new mathematical owner')
        declarations[target] = helper.named_declarations(text)
        audit = OUT / 'audits' / (target.split('.')[-1] + '.lean')
        write(audit, template.decode().replace(GENERIC, target).encode())
        audits.append({'module': target, **pin(audit)})
    for row in audits[:2]:
        old = HERE / 'cell01-blocks-pilot/audits' / Path(row['path']).name
        need(old.read_bytes() == (REPO / row['path']).read_bytes(), 'Pilot full audit changed')
    counts = {'finite_encoding_instantiations': 0, 'raw_binding_instantiations': 0,
              'closed_typed_row_theorems': 0, 'closed_raw_row_theorems': 0}
    covered = []
    for block in range(9):
        text = module_path(generator.block_module(block)).read_text()
        counts['finite_encoding_instantiations'] += text.count(
            'original_floor_and_bounds_of_encoding vertices row momentRow')
        counts['raw_binding_instantiations'] += text.count(
            'original_floor_and_bounds_of_bindings (rawVertices')
        counts['closed_typed_row_theorems'] += text.count('theorem typed_original_floor_and_bounds :')
        counts['closed_raw_row_theorems'] += text.count('theorem raw_original_floor_and_bounds :')
        expected = [f'  · exact Row{r:03d}.raw_original_floor_and_bounds'
                    for r in range(16 * block, 16 * (block + 1))]
        need([line for line in text.splitlines() if line.startswith('  · exact Row')] == expected,
             'Block ordinal order differs')
        covered.extend(range(16 * block, 16 * (block + 1)))
    need(covered == list(range(144)) and counts == {
        'finite_encoding_instantiations': 143, 'raw_binding_instantiations': 144,
        'closed_typed_row_theorems': 144, 'closed_raw_row_theorems': 144}, 'Full row instantiations differ')
    final_text = module_path(FINAL).read_text()
    expected_branches = [
        f'  · exact {generator.block_module(r // 16).removeprefix("ImbalancedChen.")}'
        f'.all_original_floor_and_bounds ({r % 16} : Fin 16)' for r in range(144)]
    need([line for line in final_text.splitlines() if line.startswith('  · exact ')] == expected_branches,
         'Final original ordinal dispatch differs')
    static = {'status': 'STATIC_SOURCE_CHECKS_ONLY', **counts,
        'original_ordinal_sequence': covered, 'final_branch_count': len(expected_branches),
        'final_guard': '∀ r : Fin 144', 'all_143_finite_pins_match': True,
        'pilot_sources_audits_and_package_unchanged': True, 'generic_source_unchanged': True,
        'accepted_row000_transport_reused': True, 'new_numeric_evaluations': 0,
        'raw_row_vertex_coordinate_bounds_preserved': True,
        'uncapped_new_and_saved_max_preserved': True, 'new_target_hypotheses': [],
        'missing_project_sources': [], 'import_cycles': [], 'named_declarations': declarations,
        'complete_owned_counts': 'PENDING_REAL_SERIALIZED_ENVIRONMENT_AUDITS',
        'independent_source_review_scope': review['scope'],
        'Lean_invoked': False, 'cloud_jobs_submitted': 0}
    write(OUT / 'STATIC_CHECK.json', encoded(static))
    source_manifest = {'schema': 'p26_cell01_all144_original_floor_family_v1',
        'status': 'SOURCE_ONLY_NOT_COMPILED', 'targets': [closure[t] for t in targets],
        'full_owned_audits': audits, 'source_closure_count': len(closure),
        'old_supplier_count': len(closure) - len(targets), 'project_source_closure': list(closure.values()),
        'direct_external_import_names': sorted(external), 'finite_series_manifest': series,
        'generic_supplier': closure[GENERIC], 'accepted_row000_supplier': closure[generator.ROW000],
        'P1_canonical1111_supplier_delta': pin(delta_path),
        'independent_pilot_and_endpoint_review': pin(OUT / 'INDEPENDENT_PILOT_AND_ENDPOINT_REVIEW.json'),
        'independent_source_review_scope': review['scope'],
        'prior_pilot_package': pin(HERE / 'cell01-original-floor-pilot-v1.tar.xz'),
        'prior_pilot_sources': [closure[INTERFACE], closure[generator.block_module(0)]],
        'new_owners': 11, 'additional_owners_since_pilot': 9,
        'source_conclusion_if_verified': 'All original cell01 Fin 144 rows: rationalMoment five floor clauses and ten Q80 double bounds.',
        'supplier_acceptance_required': 'All exact same-source objects and complete normal/kernel/owned chains; no acceptance inferred from source.',
        'generic_acceptance_required': 'Coordinator receipt required; this package does not grant acceptance.',
        'new_Archive_alias_claim': False, 'new_integral_claim': False, 'P2_6_complete_claimed': False,
        'blocked_completed_archive_accessed': False, 'Lean_invoked': False,
        'cloud_jobs_submitted': 0, 'Git_or_STATUS_changed': False}
    write(OUT / 'SOURCE_MANIFEST.json', encoded(source_manifest))
    order = '# Source-only order; exact accepted suppliers and generic required first.\n'
    for target in targets:
        for mode in ('normal', 'kernel', 'owned'):
            order += f'{target} {mode}\n'
    write(OUT / 'cloud_order.txt', order.encode())
    files = {'sources/' + str(module_path(t).relative_to(REPO)): module_path(t).read_bytes()
             for t in targets}
    for path in sorted(OUT.rglob('*')):
        if path.is_file():
            files['metadata/' + str(path.relative_to(OUT))] = path.read_bytes()
    for name in ('generate_cell01_transport_blocks.py', 'freeze_cell01_transport_pilot.py',
                 'prepare_cell01_transport_family.py', 'compare_cell01_family_suppliers.py'):
        files['tools/' + name] = (HERE / name).read_bytes()
        ast.parse(files['tools/' + name].decode())
    manifest = {'schema': 'p26_cell01_original_floor_family_source_package_v1',
        'status': 'SOURCE_ONLY_NOT_COMPILED', 'new_Lean_owners': 11,
        'files': [{'member': name, **fingerprint(data)} for name, data in sorted(files.items())],
        'supplier_object_bodies_included': False, 'old_supplier_source_bodies_included': False,
        'old_completed_evidence_included': False, 'Lean_invoked': False, 'cloud_jobs_submitted': 0}
    files['PACKAGE_MANIFEST.json'] = encoded(manifest)
    tar_path = HERE / 'cell01-original-floor-family-v1.tar.xz'
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
                 'Invalid family package readback inventory')
            seen.add(member.name)
            need(tar.extractfile(member).read() == files[member.name], 'Family payload readback differs')
    need(seen == set(files), 'Incomplete family package inventory')
    for module, row in closure.items():
        need(pin(module_path(module)) == {k: row[k] for k in ('path', 'bytes', 'sha256')},
             'Closure source changed while freezing family')
    after, after_series = verify_authored_inputs(generator)
    need(before == after and series == after_series, 'Original finite inputs changed during freeze')
    result = {'status': 'SOURCE_ONLY_NOT_COMPILED', 'package': pin(tar_path), 'members': len(files),
        'new_owners': len(targets), 'additional_owners_since_pilot': 9,
        'targets': [pin(module_path(t)) for t in targets], 'source_closure_count': len(closure),
        'old_supplier_count': len(closure) - len(targets),
        'named_theorems': sum(d['kind'] == 'theorem' for ds in declarations.values() for d in ds),
        'named_definitions': sum(d['kind'] == 'def' for ds in declarations.values() for d in ds),
        'original_row_count': 144, 'full_owned_audits': len(audits),
        'source_manifest': pin(OUT / 'SOURCE_MANIFEST.json'), 'static_checks': pin(OUT / 'STATIC_CHECK.json'),
        'P1_supplier_delta': pin(delta_path),
        'P1_source_pin_matches': 646, 'source_pin_conflicts': 0,
        'known_accepted_suppliers_including_coordinator_reports': 754,
        'pending_finite_suppliers_at_coordinator_snapshot': list(range(107, 144)),
        'other_unclassified_or_unverified_suppliers': 0,
        'independent_source_review_scope': review['scope'],
        'pilot_and_generic_bytes_unchanged': True, 'Lean_invoked': False, 'cloud_jobs_submitted': 0}
    write(HERE / 'cell01-original-floor-family-v1.metadata.json', encoded(result))
    print(json.dumps(result, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--author', action='store_true')
    mode.add_argument('--freeze', action='store_true')
    args = parser.parse_args()
    generator = load('cell01_family_generator', HERE / 'generate_cell01_transport_blocks.py')
    (author if args.author else freeze)(generator)


if __name__ == '__main__':
    main()
