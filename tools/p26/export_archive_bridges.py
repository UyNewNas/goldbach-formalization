#!/usr/bin/env python3
"""Audit and export accepted Archive bridges; never invoke Lean or rewrite proof evidence."""
import ast
import datetime
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import sys
import tarfile
import types
sys.dont_write_bytecode = True
STAGE = Path('/workspace/p26-continuation-59264dd64286/archive-bridges')
ATTEMPT = STAGE / 'attempts/20261126-geometry01-transparent-v4'
PRIOR = STAGE / 'attempts/20261126T040431856651Z-b965fcb0'
OUT = Path(__file__).parent
GEOM = 'ImbalancedChen.P2OriginalSaving19Geometry01ArchiveBridge'
CELL = 'ImbalancedChen.P2OriginalSaving19Cell00ArchiveBridge'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}
EXPECTED_RESULT = '79328a828a252a88d6c62541b6f15c06a2847e9919271c321ed86ae557912590'
EXPECTED_RECEIPTS = {
('ImbalancedChen.P2OriginalSaving19ArchivePackedInputs', 'kernel_compatibility'): '22c515e4dbad410008364683e35096b29ca4eb432125eb978f65b1f08ff8e9ec',
('ImbalancedChen.P2OriginalSaving19ArchiveCore', 'kernel_compatibility'): 'f653ebd11ca652ab64ca3e7aaf1e177da53c0b0a08b35c5f7a9f479991319acf',
(CELL, 'normal'): 'b849730bf405fa66a11dd0780586470628b56eb4c16b898a63ef3ae2ea188753',
(CELL, 'kernel'): 'f6b3f60afcf2c9b4eec86ca6e77a74a363db7859f6933f4801f51920538e0bc1',
(CELL, 'owned'): '1424ba4cb68604f4a8b36158ef12656654180b1b469cdd46ea13645bd5d6752d',
(GEOM, 'normal'): 'cdb837d4561413eff0c8bb72bad73398589e1ddfa4b35c1e85228f1500fdff2b',
(GEOM, 'kernel'): 'af687c9c4d569be69e0eef28c055ece46ea141c00000b1eeb71be327aa2b3c01',
(GEOM, 'owned'): 'fc333cfa9bdf1418789552f6adf0474b35e194ca0fde3038add888ef9c412a82'}
EXPECTED_OWNERS = {
CELL: {'source': ('027587bac1cd4ebf390281aa36680a70b1a2c09e4be85061bdef8d970af6744f', 5838),
       'object': ('2806531a2fb42c16d36d8e0c52cc6b12786d716a8a25cb695449f8d2749540cc', 64976), 'owned_count': 22},
GEOM: {'source': ('045fd132023f85aa74c6d37813430b152cc40d6539856c2e3556a5407e01b6b1', 6069),
       'object': ('71e3071c9deb9680289e79e800e66a93482cf72363b7f86cc15f59d91a49f144', 53680), 'owned_count': 19}}
checked, members, remaps, declarations = {}, {}, [], {}
def need(ok, message):
    if not ok: raise RuntimeError(message)
def raw_fp(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'Missing file or leaf symlink: ' + str(path))
    need(path.resolve().is_relative_to(Path('/workspace')), 'Outside workspace: ' + str(path))
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''): h.update(b)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': h.hexdigest()}
def identity(row):
    return row['sha256'], row['bytes']
def read(path):
    return json.loads(Path(path).read_text())
def pin(path, expected=None):
    p = str(Path(path).absolute())
    got = checked.get(p)
    if got is None:
        got = raw_fp(p)
        checked[p] = got
    if expected:
        need(got['sha256'] == expected['sha256'], 'SHA mismatch: ' + p)
        if 'bytes' in expected: need(got['bytes'] == expected['bytes'], 'Size mismatch: ' + p)
    return got
def remember(path, expected=None, root=None):
    if root: need(Path(path).resolve().is_relative_to(Path(root).resolve()), 'Root mismatch: ' + str(path))
    return pin(path, expected)
def write(path, data):
    with Path(path).open('x') as f: json.dump(data, f, ensure_ascii=False, indent=2); f.write('\n')
def add(path, name, expected=None, role='evidence'):
    actual = pin(path, expected)
    need(not Path(name).is_absolute() and '..' not in Path(name).parts, 'Unsafe archive member')
    entry = {**actual, 'archive_path': name, 'role': role}
    if name in members:
        existing = members[name]
        need(existing['path'] == entry['path'] and identity(existing) == identity(entry), 'Conflicting archive member: ' + name)
        existing['roles'] = sorted(set(existing.get('roles', [existing['role']])) | {role})
    else:
        members[name] = {**entry, 'roles': [role]}
    return actual
def add_original(path, expected=None, role='evidence'):
    path = Path(path).absolute()
    return add(path, 'original/' + str(path).lstrip('/'), expected, role)
def module_path(module, suffix):
    return Path(*module.split('.')).with_suffix(suffix)
def object_body(path):
    return str(path).endswith(('.olean', '.olean.server', '.olean.private', '.ir'))
def load_module(path, expected, name):
    pin(path, expected)
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(Path(path).read_text(), str(path), 'exec'), module.__dict__)
    return module

def main():
    result_pin = add_original(ATTEMPT / 'RESULT.json', {'sha256': EXPECTED_RESULT}, 'accepted_result')
    result = read(result_pin['path'])
    need(result['status'] == 'PASS_ARCHIVE_BRIDGES', 'Final result not accepted')
    need(result['new_proof_commands_executed'] == 3 and result['P2_6_complete_claimed'] is False,
         'Wrong claim boundary')
    need(len(result['records']) == 8 and {(r['module'], r['mode']) for r in result['records']} == set(EXPECTED_RECEIPTS),
         'Expected exactly eight proof chains')
    run_pin = add_original(result['context']['path'], result['context'], 'runtime_context')
    run = read(run_pin['path'])
    input_pin = add_original(run['inputs']['path'], run['inputs'], 'input_fingerprints')
    inputs = read(input_pin['path'])
    reg_pin = add_original(run['registry']['path'], run['registry'], 'registry')
    registry = read(reg_pin['path'])
    need(run['driver']['sha256'] == '8f419abeab658a6abd4f58a5ca9694dc0b5cd2dbb81c4dfe3bead78bf93ad680', 'Driver differs')
    need(reg_pin['sha256'] == '6e3d50751328d8924e96c317d1bbf6d4259a7ac0f5d587cc8babb59d0e838ba1', 'Registry differs')
    driver = load_module(run['driver']['path'], run['driver'], 'p26_archive_verifier_export')
    shared = load_module(run['shared_driver']['path'], run['shared_driver'], 'p26_shared_export')
    add_original(run['driver']['path'], run['driver'], 'verification_driver')
    add_original(run['shared_driver']['path'], run['shared_driver'], 'verification_helper')
    need(len(inputs['canonical_modules']) == run['canonical_project_modules'] == 1034, 'Wrong supplier count')
    need(len(inputs['external_modules']) == 515 and len(inputs['mixed_object_context']) == 5, 'Wrong external/mixed context')
    need(run['historical_core_context_identical_claimed'] is False, 'Historical Core context overclaim')
    need(run['previous_attempt_state'] == 'cancelled_partial' and run['previous_attempt'] == str(PRIOR), 'Historical boundary differs')
    need(run['new_context_compatibility_kernel_count'] == 0 and run['compatibility_receipts_reused'] == 2, 'Compatibility replay boundary differs')

    old_run_pin = add_original(PRIOR / 'RUN.json', role='historical_runtime_context')
    old_run = read(old_run_pin['path'])
    old_input_pin = add_original(old_run['inputs']['path'], old_run['inputs'], 'historical_input_fingerprints')
    old_inputs = read(old_input_pin['path'])
    reuse_pin = add_original(result['reused_steps']['path'], result['reused_steps'], 'reused_chains')
    reuse = driver.reuse_partial_attempt(shared, PRIOR, run, inputs, registry, remember)
    need(reuse == read(reuse_pin['path']), 'Five-chain revalidation differs from accepted reuse record')
    need(driver.logical_context_signature(inputs) == driver.logical_context_signature(old_inputs), 'Context join differs')
    context_signature = driver.logical_context_signature(inputs)
    context_hash = hashlib.sha256(json.dumps(context_signature, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

    # Mutable staging paths in historical metadata are resolved only to exact
    # preserved bytes; retain both recorded and resolved paths in the export.
    candidates = {}
    candidate_paths = [x for x in (STAGE / 'revisions').rglob('*') if x.is_file()]
    for base in [PRIOR / 'project', PRIOR / 'audits', ATTEMPT / 'project', ATTEMPT / 'audits']:
        candidate_paths += [x for x in base.rglob('*') if x.is_file() and x.suffix == '.lean']
    for p in candidate_paths:
        f = pin(p)
        candidates.setdefault(identity(f), []).append(p)
    def resolve_ref(row):
        p = Path(row['path'])
        actual = pin(p) if p.is_file() and not p.is_symlink() else None
        if actual and identity(actual) == identity(row): return p
        matches = candidates.get(identity(row), [])
        need(matches, 'Historical bytes not preserved: ' + str(p))
        selected = sorted(matches, key=str)[0]
        remap = {'recorded': row, 'preserved': pin(selected), 'reason': 'recorded_staging_path_replaced_after_historical_attempt'}
        if remap not in remaps: remaps.append(remap)
        return selected

    for key in ['driver', 'registry', 'shared_driver']:
        historical_file = resolve_ref(old_run[key])
        add_original(historical_file, old_run[key], 'historical_verification_code')

    snapshot_counts = []
    for label, snapshot in [('current', inputs), ('historical', old_inputs)]:
        for row in snapshot['files']:
            p = resolve_ref(row)
            pin(p, row)
            if p.suffix in {'.lean', '.json', '.log', '.md', '.txt', '.py'}:
                add_original(p, row, 'frozen_source_or_evidence')
        for module, row in snapshot['canonical_modules'].items():
            need(module == row['module'], 'Canonical module key differs')
            for key in ['source', 'object']: pin(row[key]['path'], row[key])
        for row in snapshot['project_object_union']:
            pin(row['path'], row)
            need(row['module'] in snapshot['canonical_modules'], 'Unlisted project object')
            if str(row['path']).endswith('.olean'):
                need(identity(row) == identity(snapshot['canonical_modules'][row['module']]['object']), 'Union differs from selected supplier')
        for row in snapshot['external_modules']:
            for part in [row['source'], row['object'], *row.get('sidecars', [])]: pin(part['path'], part)
        snapshot_counts.append({'context': label, 'files': len(snapshot['files']),
            'canonical_modules': len(snapshot['canonical_modules']), 'project_object_files': len(snapshot['project_object_union']),
            'external_modules': len(snapshot['external_modules'])})
    for variant in inputs['mixed_object_context']:
        need(variant['module'] in inputs['canonical_modules'], 'Unknown mixed module')
        need(variant['canonical'] == inputs['canonical_modules'][variant['module']], 'Mixed canonical selection differs')
        a, original_b = variant['canonical'], variant['historical_alternative']
        if 'source' in original_b:
            b = original_b
        else:
            need(original_b['module'] == variant['module'] and original_b['already_supplied_source_identical']
                and original_b['object_sha256_identical'] is False
                and identity(original_b['already_supplied_object']) == identity(a['object']), 'Flat mixed-context record differs')
            b = {'source': {'path': original_b['original_source'], 'sha256': original_b['source_sha256'], 'bytes': original_b['source_bytes']},
                 'object': {'path': original_b['originalpath'], 'sha256': original_b['object_sha256'], 'bytes': original_b['bytes']}}
        need(identity(a['source']) == identity(b['source']) and a['source']['sha256'] == variant['source_sha256'], 'Mixed source identity differs')
        need(identity(a['object']) != identity(b['object']), 'Expected distinct mixed objects')
        for side in [a, b]:
            for key in ['source', 'object']: pin(side[key]['path'], side[key])
    print(json.dumps({'export_phase':'supplier_snapshots_and_context_join_verified','project_modules':1034,'external_modules':515}), flush=True)

    # Recheck runtime receipts without executing their commands.
    runtime_summary = []
    for base, ctx in [(PRIOR, old_run), (ATTEMPT, run)]:
        for key in ['lean_binary', 'leanchecker_binary']: pin(ctx[key]['path'], ctx[key])
        for name in ['lean', 'mathlib', 'goldbach', 'LeanArchitect']:
            folder = base / 'runtime' / name
            rp = add_original(folder / 'result.json', role='runtime_result')
            rr = read(rp['path'])
            need(rr['status'] == 'succeeded' and rr['exit_code'] == 0 and not rr['timed_out'] and rr['error'] is None, 'Runtime command failed')
            cp = add_original(rr['command']['path'], rr['command'], 'runtime_command')
            cc = read(cp['path'])
            need(all(rr[k] == v for k, v in cc.items()), 'Runtime command/result mismatch')
            lp = add_original(rr['log']['path'], rr['log'], 'runtime_log')
            need(rr['cwd'] == ctx['project'] and rr['LEAN_PATH'] == ctx['LEAN_PATH'], 'Runtime environment mismatch')
            text = Path(lp['path']).read_text().strip()
            if name == 'lean':
                need(rr['argv'] == [ctx['lean_binary']['path'], '--version'] and text == ctx['lean_version'], 'Lean version receipt differs')
            else:
                need(len(rr['argv']) == 5 and rr['argv'][:2] == ['git', '-C'] and rr['argv'][3:] == ['rev-parse', 'HEAD'], 'Package command differs')
                need(text == ctx['package_revisions'][name], 'Package pin output differs')
            runtime_summary.append({'attempt': str(base), 'name': name, 'result': rp, 'command': cp, 'log': lp})
        external_roots = ctx['LEAN_PATH'].split(os.pathsep)[1:]
        need(len(external_roots) >= 9 and all(Path(p).is_dir() for p in external_roots), 'Runtime object root missing')
        need(str(Path(ctx['LEAN_PATH'].split(os.pathsep)[0])) == str(base / 'objects'), 'Not a single project namespace')
        need('/workspace/blue-member-build/.lake/build/lib/lean' not in external_roots, 'Unexpected mutable blue project fallback')

    chains, owner_phases, imported_project_counts = [], {}, {}
    for record in result['records']:
        module, mode = record['module'], record['mode']
        receipt_pin = add_original(record['receipt']['path'], record['receipt'], 'accepted_step')
        need(receipt_pin['sha256'] == EXPECTED_RECEIPTS[(module, mode)], 'Unexpected accepted receipt SHA')
        receipt = read(receipt_pin['path'])
        base = ATTEMPT if module == GEOM else PRIOR
        ctx = run if module == GEOM else old_run
        ctxpin = run_pin if module == GEOM else old_run_pin
        inpin = input_pin if module == GEOM else old_input_pin
        need(receipt['status'] == 'succeeded' and receipt['module'] == module and receipt['mode'] == mode
            and receipt['all_frozen_inputs_unchanged'] is True and receipt['context'] == ctxpin, 'Accepted step binding failed')
        need(Path(receipt_pin['path']).is_relative_to(base), 'Accepted step in wrong attempt')
        for key in ['source', 'object', 'command_result', 'log']: pin(receipt[key]['path'], receipt[key])
        for side in receipt.get('object_sidecars', []): pin(side['path'], side)
        rrpin = add_original(receipt['command_result']['path'], receipt['command_result'], 'proof_result')
        rr = read(rrpin['path'])
        need(rr['status'] == 'succeeded' and rr['exit_code'] == 0 and not rr['timed_out'] and rr['error'] is None, 'Proof command failed')
        cpin = add_original(rr['command']['path'], rr['command'], 'proof_command')
        command = read(cpin['path'])
        need(all(rr[k] == v for k, v in command.items()), 'Proof command/result differs')
        lpin = add_original(receipt['log']['path'], receipt['log'], 'proof_log')
        need(rr['source'] == receipt['source'] and rr['log'] == lpin and rr['input_fingerprints'] == inpin
            and rr['cwd'] == ctx['project'] and rr['LEAN_PATH'] == ctx['LEAN_PATH']
            and rr['module'] == module and rr['mode'] == mode, 'Proof exact environment binding failed')
        flags = ['-j1', '-M14336', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
        if mode in ['kernel', 'kernel_compatibility']:
            need(rr['argv'] == [ctx['leanchecker_binary']['path'], '--verbose', module]
                and rr['object_before'] == receipt['object'], 'Not the independent kernel command')
        elif mode == 'normal':
            need(rr['argv'] == [ctx['lean_binary']['path'], *flags, '-o', receipt['object']['path'],
                str(module_path(module, '.lean'))] and rr['object_before'] is None, 'Normal argv/output differs')
        else:
            audit = add_original(receipt['audit_source']['path'], receipt['audit_source'], 'owned_audit_source')
            target = next(t for t in registry['targets'] if t['module'] == module)
            need(identity(audit) == identity(target['audit']) and rr['audit_source'] == audit
                and rr['object_before'] == receipt['object'] and rr['argv'] == [ctx['lean_binary']['path'], *flags, audit['path']], 'Owned argv/source differs')
            text = Path(lpin['path']).read_text()
            normalized = '\n'.join('P26_CELL00_AUDIT_' + line[len('P26_ARCHIVE_AUDIT_'):]
                if line.startswith('P26_ARCHIVE_AUDIT_') else line for line in text.splitlines())
            owned = shared.parse_owned(normalized, module)
            need(owned == receipt['owned'], 'Full owned record differs')
            need(owned['count'] == EXPECTED_OWNERS[module]['owned_count'], 'Owned count differs')
            need(set(owned['axioms_union']) <= ALLOWED, 'Forbidden transitive axiom')
            imports = [json.loads(line[len('P26_ARCHIVE_AUDIT_IMPORTS '):]) for line in text.splitlines()
                if line.startswith('P26_ARCHIVE_AUDIT_IMPORTS ')]
            need(len(imports) == 1 and module in imports[0], 'Owned import inventory missing')
            project_imports = [m for m in imports[0] if m.startswith('ImbalancedChen.')]
            need(set(project_imports) <= set(inputs['canonical_modules']) | set(EXPECTED_OWNERS), 'Import outside frozen project boundary')
            imported_project_counts[module] = len(project_imports)
            declarations[module] = {**owned, 'imports': imports[0], 'audit': audit, 'log': lpin,
                'type_basis': 'all_environment_owned_constants_with_full_types',
                'axiom_basis': 'Lean.collectAxioms_for_each_owned_declaration'}
        if module in EXPECTED_OWNERS:
            for key in ['source', 'object']:
                need(identity(receipt[key]) == EXPECTED_OWNERS[module][key], 'Owner exact ' + key + ' differs')
            owner_phases.setdefault(module, []).append(receipt)
        chains.append({'module': module, 'mode': mode, 'reused': module != GEOM,
            'receipt': receipt_pin, 'source': receipt['source'], 'object': receipt['object'],
            'command': cpin, 'result': rrpin, 'log': lpin,
            'wall_seconds': rr['finished_unix'] - rr['started_unix']})
    print(json.dumps({'export_phase':'all_eight_proof_chains_verified','owned_count':sum(d['count'] for d in declarations.values())}), flush=True)
    for module, phases in owner_phases.items():
        need(len(phases) == 3 and all(r['source'] == phases[0]['source'] and r['object'] == phases[0]['object'] for r in phases), 'Owner phases do not bind identical bytes')
        need(all(r.get('object_sidecars', []) == phases[0].get('object_sidecars', []) for r in phases), 'Owner sidecar phases differ')
        row = phases[0]
        add(row['source']['path'], 'sources/' + str(module_path(module, '.lean')), row['source'], 'accepted_owner_source')
        add(row['object']['path'], 'objects/' + str(module_path(module, '.olean')), row['object'], 'accepted_owner_object')
        for side in row.get('object_sidecars', []):
            add(side['path'], 'objects/ImbalancedChen/' + Path(side['path']).name, side, 'accepted_owner_sidecar')
        owned_path = OUT / (module.split('.')[-1] + '_OWNED.json')
        write(owned_path, declarations[module])
        add(owned_path, 'owned/' + owned_path.name, role='full_owned_types_transitive_axioms')

    # Historical retries remain cancelled, with no accepted Geometry step.
    observations = read(OUT / 'MCP_TASK_OBSERVATIONS.json')
    need(observations['successful_task']['status'] == 'succeeded'
         and observations['successful_task']['exit_code'] == 0
         and observations['successful_task']['task_id'] == 'job_34bfba6b1c94464c880cd79e0eac7a7e', 'MCP task differs')
    need(all(x['status'] == 'cancelled' and x['cancel_requested'] for x in observations['cancelled_tasks']), 'Cancelled task history differs')
    historical_attempts = []
    expected_previous_sources = {'7a8c898069a99389fda403792d4e28a9c71b9d1aab92536d20611e196bba15c1',
        '0f6aa7e3d1ae1cef8b162847d01aaf9e9183699f33cc2f57f7305ba62d45b78c',
        'ed455c02e55a25f2622effb3f189dbc5c55c3abbcb3ff3b04e3851467ddb764b'}
    for folder in sorted((STAGE / 'attempts').iterdir()):
        source = folder / 'project' / module_path(GEOM, '.lean')
        if folder == ATTEMPT or not source.is_file(): continue
        sp = pin(source)
        if sp['sha256'] not in expected_previous_sources: continue
        need(not any((folder / 'steps' / GEOM.split('.')[-1] / mode / 'ACCEPTED_STEP.json').exists()
            for mode in ['normal', 'kernel', 'owned']), 'Historical Geometry attempt became accepted')
        marker_path = folder / 'steps' / GEOM.split('.')[-1] / 'normal/output.log'
        markers = []
        if marker_path.exists():
            add_original(marker_path, role='cancelled_normal_log')
            markers = [line for line in marker_path.read_text().splitlines() if line.startswith('P26_GEOMETRY01_ARCHIVE ')]
        for name in ['RUN.json', 'INPUT_FINGERPRINTS.json', 'RESULT.json', 'REUSED_ACCEPTED_STEPS.json']:
            p = folder / name
            if p.is_file(): add_original(p, role='cancelled_attempt_context')
        for p in (folder / 'steps' / GEOM.split('.')[-1] / 'normal').glob('*.json'):
            add_original(p, role='cancelled_unaccepted_command')
        add_original(source, sp, 'cancelled_geometry_source')
        normal_command_path = folder / 'steps' / GEOM.split('.')[-1] / 'normal/command.json'
        need(normal_command_path.is_file(), 'Historical normal command absent')
        started = read(normal_command_path)['started_unix']
        matching_jobs = [t for t in observations['cancelled_tasks'] if t['started_at'] <= started <= t['finished_at']]
        need(len(matching_jobs) == 1, 'Historical attempt cannot be bound to cancelled MCP task')
        historical_attempts.append({'attempt': str(folder), 'state': 'cancelled_partial', 'MCP_job': matching_jobs[0]['task_id'],
            'geometry_normal_accepted': False, 'source': sp, 'markers': markers,
            'overall_result_present': (folder / 'RESULT.json').is_file()})
    need(expected_previous_sources <= {h['source']['sha256'] for h in historical_attempts}, 'Missing preserved cancelled candidate history')
    for p in (STAGE / 'revisions').rglob('*'):
        if p.is_file(): add_original(p, role='preserved_revision')
    for name in ['PACKAGE_MANIFEST.json', 'TRANSPARENT_VERTEX_SOURCE_CHECK.json', 'ArchiveBridges_README.md']:
        p = STAGE / name
        if p.is_file(): add_original(p, role='preparation_evidence')
    for base in [PRIOR, ATTEMPT]:
        for p in (base / 'owners').glob('*.json'): add_original(p, role='owner_result')
    add(Path(__file__), 'exporter.py', role='exporter_source')
    add(OUT / 'MCP_TASK_OBSERVATIONS.json', 'MCP_TASK_OBSERVATIONS.json', role='MCP_task_observations')

    # No historical supplier object bodies; all source identities and pins stay.
    for name, row in list(members.items()):
        if object_body(row['path']):
            need(name.startswith('objects/') and row['role'] in ['accepted_owner_object', 'accepted_owner_sidecar'], 'Supplier object body in export')
    object_members = [n for n,r in members.items() if r['role'] == 'accepted_owner_object']
    need(len(object_members) == 2, 'Expected exactly two bridge objects')
    literal_rows = {r['path']: r for r in inputs['files'] if 'original-inputs' in Path(r['path']).parts}
    need(len(literal_rows) >= 26, 'Raw literal input boundary missing')
    audit = {
        'schema': 'p26_archive_bridges_strict_export_audit_v1', 'status': 'PASS_EIGHT_CHAINS_AND_CONTEXT_JOIN',
        'attempt': str(ATTEMPT), 'result': result_pin, 'proof_chains': chains,
        'new_proof_chains': 3, 'historical_accepted_chains_reused': 5,
        'compatibility_kernel_chains_reused': 2, 'new_Lean_commands_executed_by_exporter': 0,
        'owner_summaries': {m: {'source_sha256': EXPECTED_OWNERS[m]['source'][0],
            'object_sha256': EXPECTED_OWNERS[m]['object'][0], 'owned_count': declarations[m]['count'],
            'axioms_union': declarations[m]['axioms_union'], 'imported_project_modules': imported_project_counts[m]}
            for m in EXPECTED_OWNERS},
        'owned_total': 41, 'all_owned_types_and_transitive_axioms_in_archive': True,
        'owned_basis': 'complete_environment_owned_inventory_with_full_types_and_Lean.collectAxioms',
        'context_join': {'same_logical_supplier_source_object_runtime_literal_context': True,
            'signature_sha256': context_hash, 'original_partial_attempt': str(PRIOR),
            'original_partial_attempt_state': 'cancelled_partial', 'original_overall_success_claimed': False,
            'historical_core_context_identical_claimed': False, 'mixed_object_variants': inputs['mixed_object_context']},
        'snapshot_counts': snapshot_counts, 'raw_literal_input_count': len(literal_rows),
        'runtime': {'lean_version': run['lean_version'], 'lean_binary': run['lean_binary'],
            'leanchecker_binary': run['leanchecker_binary'], 'package_revisions': run['package_revisions'],
            'current_LEAN_PATH': run['LEAN_PATH'], 'original_LEAN_PATH': old_run['LEAN_PATH'], 'records': runtime_summary},
        'historical_attempts': historical_attempts, 'historical_path_resolutions': remaps,
        'MCP_metrics': {k:v for k,v in observations['successful_task'].items() if k != 'command'},
        'supplier_object_bodies_in_archive': 0, 'accepted_bridge_object_bodies_in_archive': 2,
        'original_files_modified': False, 'P2_6_complete_claimed': False}
    audit_path = OUT / 'AUDIT_DETAILS.json'
    write(audit_path, audit)
    add(audit_path, 'AUDIT_DETAILS.json', role='strict_export_audit')
    manifest = {'schema': 'p26_archive_bridges_completed_export_v1',
        'status': 'PASS_EIGHT_CHAINS_AND_CONTEXT_JOIN', 'attempt': str(ATTEMPT),
        'source_result': result_pin, 'script': pin(__file__), 'files': sorted(members.values(), key=lambda r:r['archive_path']),
        'verified_input_files': len(checked), 'excluded_supplier_object_bodies': True,
        'new_Lean_commands_executed': 0}
    manifest_path = OUT / 'EXPORT_MANIFEST.json'
    write(manifest_path, manifest)
    manifest_pin = pin(manifest_path)
    archive = OUT / 'archive-bridges-completed-evidence.tar.xz'
    need(not archive.exists(), 'Refusing archive overwrite')
    print(json.dumps({'export_phase':'packing_verified_evidence','file_members':len(manifest['files']),'uncompressed_bytes':sum(r['bytes'] for r in manifest['files'])}), flush=True)
    with tarfile.open(archive, 'w:xz', preset=4) as tf:
        for row in manifest['files']:
            need(identity(raw_fp(row['path'])) == identity(row), 'Member changed before packing')
            info = tf.gettarinfo(row['path'], arcname=row['archive_path'])
            info.uid = info.gid = 0
            info.uname = info.gname = ''
            info.mtime = 0
            with open(row['path'], 'rb') as f: tf.addfile(info, f)
        info = tf.gettarinfo(manifest_path, arcname='EXPORT_MANIFEST.json')
        info.uid = info.gid = 0; info.uname = info.gname = ''; info.mtime = 0
        with manifest_path.open('rb') as f: tf.addfile(info, f)
    expected = {r['archive_path']:r for r in manifest['files']}
    expected['EXPORT_MANIFEST.json'] = manifest_pin
    with tarfile.open(archive, 'r:xz') as tf:
        actual_names = []
        for item in tf:
            need(item.isfile() and item.name in expected and item.name not in actual_names, 'Invalid/duplicate tar member')
            need(not Path(item.name).is_absolute() and '..' not in Path(item.name).parts, 'Unsafe tar member')
            actual_names.append(item.name)
            h = hashlib.sha256()
            with tf.extractfile(item) as f:
                for b in iter(lambda:f.read(1048576), b''): h.update(b)
            row = expected[item.name]
            need(item.size == row['bytes'] and h.hexdigest() == row['sha256'], 'Tar member readback mismatch')
        need(set(actual_names) == set(expected), 'Missing tar member')
    for path, before in checked.items():
        need(identity(raw_fp(path)) == identity(before), 'Read-only input changed during export: ' + path)
    summary = {'schema': 'p26_archive_bridges_export_summary_v1',
        'status': 'PASS_STRICT_EXPORT_AND_READBACK', 'script': pin(__file__), 'archive': raw_fp(archive),
        'manifest': manifest_pin, 'audit_details': pin(audit_path), 'archive_members': len(expected),
        'all_member_hashes_readback_verified': True, 'all_input_hashes_rechecked_after_export': True,
        'checked_unique_files': len(checked), 'source_result': result_pin,
        'proof_chain_count': 8, 'new_geometry_chains': 3, 'reused_cell00_chains': 3,
        'reused_compatibility_kernel_chains': 2, 'owned_total': 41,
        'owners': audit['owner_summaries'], 'supplier_contexts': snapshot_counts,
        'raw_literal_inputs': len(literal_rows), 'mixed_object_variants': 5,
        'same_logical_supplier_source_object_runtime_literal_context': True,
        'context_signature_sha256': context_hash,
        'historical_attempts': [{k:v for k,v in h.items() if k not in ['markers']} for h in historical_attempts],
        'historical_path_resolution_count': len(remaps), 'original_overall_success_claimed': False,
        'supplier_object_bodies_archived': 0, 'bridge_object_bodies_archived': 2,
        'new_Lean_commands': 0, 'original_files_modified': False, 'P2_6_complete_claimed': False,
        'MCP_metrics': audit['MCP_metrics'], 'issues': []}
    summary_path = OUT / 'AUDIT_SUMMARY.json'
    write(summary_path, summary)
    print(json.dumps({'summary': raw_fp(summary_path), **summary}, ensure_ascii=False))
if __name__ == '__main__':
    try: main()
    except Exception as e:
        failure = {'status':'FAILED_STOPPED_EXPORT', 'error':type(e).__name__ + ': ' + str(e),
            'script':raw_fp(__file__), 'Lean_commands_executed':0, 'original_files_modified':False}
        write(OUT / 'EXPORT_FAILURE.json', failure)
        print(json.dumps(failure), flush=True)
        raise
