#!/usr/bin/env python3
"""Accept unchanged Cell03 Simplex05/10/18 on P2 using sixteen accepted objects.

--plan validates the existing evidence without invoking Lean. --inventory also
finds exact existing objects. Only the explicitly selected missing owners
can be compiled; dependencies are never compiled. Actual P2 commands and paths
remain distinct from the original local SIGKILL records.
"""
import argparse
import ast
import base64
import datetime
import functools
import hashlib
import importlib
import json
import lzma
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PLAN_SHA = '21c54c94f6a7be85f284983f38e03f95c227c4cb2d4b192fed0ea4df8bbbe38f'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
LOG_KEYS = {'NORMAL': 'normal_log_sha256', 'REPLAY': 'stock_replay_log_sha256',
            'AUDIT': 'complete_owned_audit_log_sha256'}
PACKAGE = 'docs/source-only/20261127-p2-5-cell03-finite'
TEMPLATE = 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean'
APPENDIX = 'docs/source-only/20261126-p2-5-cell00-field-split/PRIVATE_SCOPED_SIMP_AUDIT_APPENDIX.lean'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(p):
    with Path(p).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def jsig(value):
    return digest(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def read(p):
    return json.loads(Path(p).read_bytes())


def write(p, value):
    temporary = p.with_suffix(p.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(p)


def checked(p, expected):
    require(p.is_file() and sha(p) == expected, 'Missing or changed pinned file: ' + str(p))
    return p


def standalone(p):
    require(not any(Path(str(p) + s).exists() for s in ('.private', '.server')),
            'Unqualified project companion: ' + str(p))


def marks(raw):
    result = {}
    for line in raw.decode().splitlines():
        if line.startswith(('P0_QUEUE_', 'P25_PRIVATE_SCOPED_SIMP_INTERFACE ')):
            key, body = line.split(' ', 1)
            result.setdefault(key, []).append(json.loads(body))
    return result


def old_inventory(raw, module, members, external_names, required):
    """Recheck captured complete inventories, including the import-only owner."""
    data = marks(raw)
    require(len(data.get('P0_QUEUE_INVENTORY', [])) == len(data.get('P0_QUEUE_IMPORTS', [])) == 1,
            'Missing or duplicate prior inventories: ' + module)
    inventory, = data['P0_QUEUE_INVENTORY']
    imports, = data['P0_QUEUE_IMPORTS']
    declarations = data.get('P0_QUEUE_DECL', [])
    names = [d['name'] for d in declarations]
    require(inventory['module'] == module and len(names) == len(set(names)) and
            sorted(names) == sorted(inventory['serialized']) == sorted(inventory['environment']),
            'Prior serialized/environment inventory differs: ' + module)
    require((not names) == (module == 'ImbalancedChen.P2Saving16Cell03ScalarDecode'),
            'Unexpected empty prior inventory: ' + module)
    require(len(imports) == len(set(imports)) and
            {m for m in imports if m.startswith('ImbalancedChen.')} == members and
            set(imports) - members == external_names and set(required) <= set(names),
            'Prior imports/public declarations differ: ' + module)
    for d in declarations:
        require(d['module'] == module and all(d.get(k) is False for k in ('unsafe', 'partial', 'axiom')) and
                isinstance(d.get('type'), str) and d['type'] and '⋯' not in d['type'] and
                isinstance(d.get('axioms'), list) and set(d['axioms']) <= AXIOMS,
                'Prior declaration failed complete audit: ' + d['name'])
    return data, declarations


def inspect_objects(dependencies, owners, roots):
    """Read only; discover duplicates before any new compile or archive unpack."""
    stems = {m.split('.')[-1] + '.olean': m for m in [*dependencies, *owners]}
    paths = {m: [] for m in stems.values()}
    rg = shutil.which('rg')
    if rg:
        argv = [rg, '--files', '--hidden', '--no-ignore', '--glob', '*.olean', '--', *map(str, roots)]
        process = subprocess.run(argv, capture_output=True, text=True)
        require(process.returncode in (0, 1), 'Object inventory failed: ' + process.stderr)
        enumerator = {'kind': 'rg', 'executable': rg, 'follow_directory_symlinks': False}
        for line in process.stdout.splitlines():
            p = Path(line)
            if p.name in stems:
                paths[stems[p.name]].append(p)
    else:
        argv = None
        enumerator = {'kind': 'os.walk', 'followlinks': False}

        def walk_error(error):
            raise error

        for root in roots:
            for directory, _, filenames in os.walk(root, followlinks=False, onerror=walk_error):
                for filename in filenames:
                    if filename.endswith('.olean') and filename in stems:
                        paths[stems[filename]].append(Path(directory) / filename)
    suppliers, rejected = {}, {}
    for m, row in dependencies.items():
        for p in sorted(set(paths[m])):
            if not p.is_file() or p.stat().st_size != row['bytes']:
                rejected.setdefault(m, []).append({'path': str(p), 'reason': 'size'})
                continue
            actual = sha(p)
            if actual != row['sha256']:
                rejected.setdefault(m, []).append({'path': str(p), 'sha256': actual})
                continue
            if any(Path(str(p) + s).exists() for s in ('.private', '.server')):
                rejected.setdefault(m, []).append({'path': str(p), 'reason': 'companions'})
                continue
            suppliers[m] = str(p.resolve(strict=True))
            break
    return {'schema': 'p25-cell03-object-inventory-v1', 'search_roots': list(map(str, roots)),
            'search_argv': argv, 'enumerator': enumerator, 'accepted_suppliers': suppliers,
            'missing': {m: row for m, row in dependencies.items() if m not in suppliers},
            'rejected_candidates': rejected,
            'existing_target_objects': {m: list(map(str, paths[m])) for m in owners if paths[m]},
            'compile_credit': False, 'P2_5_proved': False}


def main():
    require(__debug__, 'The original reused runner requires Python assertions')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--evidence-capsule', type=Path, required=True)
    ap.add_argument('--new-deps-archive', type=Path)
    ap.add_argument('--only', nargs='+', choices=['05', '10', '18'], default=['05'])
    ap.add_argument('--plan', action='store_true')
    ap.add_argument('--inventory', action='store_true')
    ap.add_argument('--search-root', type=Path, action='append')
    ap.add_argument('--work', type=Path)
    ap.add_argument('--stage-limit', type=int, default=900)
    args = ap.parse_args()
    require(not (args.plan and args.inventory), 'Choose one read-only mode')
    repo = args.repo.resolve(strict=True)
    plan_path = checked(HERE / 'PLAN.json', PLAN_SHA)
    plan = read(plan_path)
    controls = {plan_path: PLAN_SHA, Path(__file__).resolve(): sha(Path(__file__).resolve())}
    for section in ('package_manifest', 'public_expectations', 'historical_checkpoint', 'reuse_driver', 'finite_runtime'):
        row = plan[section]
        controls[checked(repo / row['path'], row['sha256'])] = row['sha256']
    for p, h in plan['repo_helpers'].items():
        controls[checked(repo / p, h)] = h
    transfer_path = HERE / plan['transfer_manifest']['path']
    controls[checked(transfer_path, plan['transfer_manifest']['sha256'])] = plan['transfer_manifest']['sha256']
    transfer = read(transfer_path)
    capsule_path = args.evidence_capsule.resolve(strict=True)
    controls[checked(capsule_path, plan['local_evidence_capsule']['sha256'])] = plan['local_evidence_capsule']['sha256']
    capsule = json.loads(lzma.decompress(capsule_path.read_bytes()))
    require(capsule['file_count'] == len(capsule['files']) == 625, 'Wrong original checkpoint evidence capsule')
    captured = {}
    for p, q in capsule['files'].items():
        raw = base64.b64decode(q['base64'], validate=True)
        require(len(raw) == q['bytes'] and digest(raw) == q['sha256'], 'Corrupt captured evidence: ' + p)
        captured[p] = raw
    def cj(p):
        return json.loads(captured[p])
    inputs = cj('INPUTS.json')
    local_root = Path(capsule['execution_root'])
    local_package = Path('/workspace/scratch/ffd83d72c265/goldbach-formalization') / PACKAGE
    dependencies, owners = plan['project_dependencies'], plan['owners']
    nodes = {**dependencies, **owners}
    selected = ['ImbalancedChen.P2Saving16Cell03Simplex' + n + 'Decode' for n in dict.fromkeys(args.only)]
    source_manifest = read(repo / plan['package_manifest']['path'])
    manifest_rows = {q['module']: q for q in source_manifest['local_topological_order']}
    expectations = read(repo / plan['public_expectations']['path'])['modules']
    historical = read(repo / plan['historical_checkpoint']['path'])['project_objects']
    require(set(dependencies) == set(transfer['project_dependencies']) and len(dependencies) == 16,
            'Dependency transfer scope differs')
    for m, q in nodes.items():
        p = (repo / q['source']).resolve(strict=True)
        require(p.is_relative_to(repo), 'Source escapes selected repository')
        checked(p, q['source_sha256'])
        require(re.findall(r'^import (ImbalancedChen\.[\w.]+)', p.read_text(), re.M) == q['imports'],
                'Source graph changed: ' + m)
        if m in dependencies:
            original = transfer['project_dependencies'][m]
            require(all(q[k] == v for k, v in original.items()), 'Transfer pin changed: ' + m)
            if q['kind'] == 'reuse_existing_historical_object':
                require(all(q[k] == historical[m][k] for k in ('bytes', 'sha256', 'source_sha256')) and
                        all(inputs['historical_project_objects'][m][k] == historical[m][k]
                            for k in historical[m]), 'Historical accepted lineage differs: ' + m)
        if m in manifest_rows:
            r = manifest_rows[m]
            require(r['sha256'] == q['source_sha256'] and r['direct_project_imports'] == q['imports'] and
                    (repo / PACKAGE / r['path']).resolve() == p and p.stat().st_size == r['bytes'],
                    'Original Cell03 manifest differs: ' + m)
        if m in owners:
            require(owners[m]['required_declarations'] == expectations[m] and len(expectations[m]) == 11,
                    'Original public expectation list differs: ' + m)

    @functools.cache
    def closure(m):
        return frozenset({m}.union(*(closure(d) for d in nodes[m]['imports'])))

    require(all(closure(m) - {m} == set(dependencies) for m in owners),
            'Targets do not share the exact sixteen-object closure')
    compatibility_path = repo / plan['finite_runtime']['path']
    compatibility = json.loads(lzma.decompress(compatibility_path.read_bytes()))
    runtime = inputs['runtime_hashes']
    require(inputs['manifest_sha256'] == plan['package_manifest']['sha256'] and
            inputs['historical_checkpoint_sha256'] == plan['historical_checkpoint']['sha256'] and
            len(runtime) == inputs['external_files'] == 15940 and
            jsig(runtime) == inputs['external_map_sha256'] and
            inputs['external_origin_sha256'] == compatibility['historical_context_sha256'] and
            compatibility['external_snapshot_sha256'] == plan['external_snapshot']['sha256'],
            'Original finite runtime provenance differs')
    projected = {}
    for p, h in runtime.items():
        if '.olean' in p:
            stem, suffix = p.split('.olean', 1)
            name = stem.split('/lib/lean/', 1)[1].replace('/', '.')
            target = compatibility['modules'][name] + suffix
        elif p.startswith('/mathlib/'):
            target = '/workspace/compile-deps/mathlib/' + p.removeprefix('/mathlib/')
        else:
            target = p
        require(target not in projected, 'Runtime projection is not injective')
        projected[target] = h
    require(projected == compatibility['runtime'] and len(compatibility['modules']) == 5312,
            'Cell03 finite runtime is not byte-identical to the qualified P2 projection')
    external_names = set(compatibility['modules'])
    template = (repo / TEMPLATE).read_text()
    require(inputs['audit_template_sha256'] == sha(repo / TEMPLATE), 'Original template pin differs')

    def local_commands(m):
        name = m.split('.')[-1]
        return {'NORMAL': [inputs['compiler'], *plan['strict_flags'], '--root=' + str(local_package), '-o',
                           str(local_root / 'objects' / (m.replace('.', '/') + '.olean')),
                           str(local_package / 'ImbalancedChen' / (name + '.lean'))],
                'REPLAY': [inputs['stock_checker'], '-v', m],
                'AUDIT': [inputs['compiler'], *plan['strict_flags'], '--root=' + str(local_root / 'audits'),
                          str(local_root / 'audits' / (name + '.lean'))]}

    provenance = {}
    for m, q in dependencies.items():
        if q['kind'] != 'new_Cell03_accepted_object':
            continue
        name = m.split('.')[-1]
        folder = 'evidence/' + name + '/'
        require(digest(captured[q['receipt_path']]) == q['receipt_sha256'], 'Prior accepted receipt differs: ' + m)
        receipt = cj(q['receipt_path'])
        require(receipt.get('accepted') is True and receipt['module'] == m and
                receipt['source_sha256'] == q['source_sha256'] and receipt['object_sha256'] == q['sha256'] and
                receipt['object_bytes'] == q['bytes'] and receipt['manifest_sha256'] == inputs['manifest_sha256'],
                'Prior source/object acceptance differs: ' + m)
        program = template.replace('P2Saving16Cell00TypedPayload', name)
        if name == 'P2Saving16Cell03ScalarDecode':
            program = program.replace('names.size > 0', 'names.size == 0')
        private_names = []
        if name == 'P2Saving16Cell03FieldSimp':
            appendix = (repo / APPENDIX).read_text().replace('Cell00', 'Cell03')
            private_names = re.findall(r'^private theorem (\w+)', (repo / q['source']).read_text(), re.M)
            expected = ',\n    '.join(json.dumps('ImbalancedChen.P2Saving16Cell03FieldDecode.' + n) for n in private_names)
            appendix = re.sub(r'(let expected : Array String := #\[).*?(\]\n  let simpTheorems)',
                              lambda z: z[1] + expected + z[2], appendix, count=1, flags=re.S)
            program += '\n' + appendix
        require(captured['audits/' + name + '.lean'] == program.encode() and
                digest(program.encode()) == receipt['audit_sha256'], 'Prior complete audit program differs: ' + m)
        stages = cj(folder + 'STAGES.json')
        require(stages == receipt['stages'] and [s['stage'] for s in stages] == list(LOG_KEYS),
                'Prior stage sequence differs: ' + m)
        for stage in stages:
            label = stage['stage']
            require(stage['exit_code'] == 0 and stage['argv'] == local_commands(m)[label] and
                    digest(captured[folder + label + '.log']) == stage['log_sha256'] == receipt[LOG_KEYS[label]],
                    'Prior commands/logs failed: ' + m + '/' + label)
            for phase in ('BEFORE', 'AFTER'):
                c = cj(folder + label + '_' + phase + '_CONTEXT.json')
                require(c['external_files'] == 15940 and c['external_map_sha256'] == inputs['external_map_sha256'] and
                        c['source_sha256'] == q['source_sha256'] and c['manifest_sha256'] == inputs['manifest_sha256'] and
                        c['project_dependencies'] == {d: dependencies[d]['sha256'] for d in closure(m) - {m}},
                        'Prior frozen dependency/runtime context differs: ' + m)
                require(c.get('owner_object_sha256') == (None if (label, phase) == ('NORMAL', 'BEFORE') else q['sha256']),
                        'Prior owner object changed during acceptance: ' + m)
        parsed, declarations = old_inventory(captured[folder + 'AUDIT.log'], m, set(closure(m)),
                                              external_names, expectations[m])
        require(cj(folder + 'DECLARATIONS.json') == declarations and len(declarations) == receipt['owned_count'] and
                receipt['imports_count'] == len(parsed['P0_QUEUE_IMPORTS'][0]) and
                receipt['external_modules'] == len(external_names) and
                set(receipt['project_imports']) == closure(m) and
                receipt['transitive_axioms'] == sorted({a for d in declarations for a in d['axioms']}),
                'Prior declaration artifact differs: ' + m)
        if private_names:
            scope, = parsed['P25_PRIVATE_SCOPED_SIMP_INTERFACE']
            require(scope['required_count'] == scope['matched_count'] == len(private_names) == 576,
                    'Prior FieldSimp private scoped interface differs')
        provenance[m] = {'receipt_member': q['receipt_path'], 'receipt_sha256': q['receipt_sha256'],
                         'object_sha256': q['sha256'], 'owned_count': len(declarations)}
    require(len(provenance) == 7, 'Not all seven new dependencies have complete acceptance')
    failures = {}
    for m in selected:
        rows = plan['local_failures'][m]
        raw = {}
        for filename, q in rows.items():
            p = HERE / q['path']
            controls[checked(p, q['sha256'])] = q['sha256']
            raw[filename] = p.read_bytes()
        stages = json.loads(raw['STAGES.json'])
        require(len(stages) == 1 and stages[0]['stage'] == 'NORMAL' and stages[0]['exit_code'] == -9 and
                stages[0]['argv'] == local_commands(m)['NORMAL'] and raw['NORMAL.log'] == b'' and
                stages[0]['log_sha256'] == digest(b'') and json.loads(raw['FAILURE.json'])['stages'] == stages,
                'Requested owner is not the captured local SIGKILL: ' + m)
        same_closure = plan.get('same_closure_records', {}).get(m)
        if same_closure is not None:
            p = HERE / same_closure['path']
            controls[checked(p, same_closure['sha256'])] = same_closure['sha256']
            record = read(p)
            require(record['module'] == m and record['dependency_map_identical_to_Simplex05'] is True and
                    record['source']['path'] == owners[m]['source'] and
                    record['source']['sha256'] == owners[m]['source_sha256'] and
                    record['source']['bytes'] == owners[m]['source_bytes'] and
                    record['source']['direct_project_imports'] == owners[m]['imports'] and
                    record['object_archive_sha256'] == plan['new_dependency_archive']['sha256'] and
                    record['failed_stage'] == stages[0], 'Supplemental same-closure failure record differs: ' + m)
        for phase in ('BEFORE', 'AFTER'):
            c = json.loads(raw['NORMAL_' + phase + '_CONTEXT.json'])
            require(c['source_sha256'] == owners[m]['source_sha256'] and
                    c['manifest_sha256'] == inputs['manifest_sha256'] and c['external_files'] == 15940 and
                    c['external_map_sha256'] == inputs['external_map_sha256'] and not c.get('owner_object_sha256') and
                    c['project_dependencies'] == {d: q['sha256'] for d, q in dependencies.items()},
                    'Local failed attempt had different inputs or produced an object: ' + m)
        failures[m] = rows
    prepared = {'status': 'PLAN_VALIDATED_NO_FORMAL_CREDIT', 'owners': selected,
                'source_manifest_sha256': inputs['manifest_sha256'], 'plan_sha256': PLAN_SHA,
                'exact_project_dependencies': 16, 'historical_dependencies': 9, 'new_accepted_dependencies': provenance,
                'local_evidence_capsule_sha256': plan['local_evidence_capsule']['sha256'],
                'projected_finite_runtime_files': len(projected), 'finite_external_modules': len(external_names),
                'local_external_map_sha256': inputs['external_map_sha256'],
                'p2_runtime_projection_sha256': jsig(projected), 'P2_5_proved': False}
    if args.plan:
        print(json.dumps(prepared, indent=2))
        return 0

    roots = [p.resolve(strict=True) for p in (args.search_root or [Path('/workspace')])]
    inventory = inspect_objects(dependencies, {m: owners[m] for m in selected}, roots)
    if args.inventory:
        print(json.dumps(inventory, indent=2))
        return 0
    require(args.work is not None, 'An actual run requires a fresh --work directory')
    work = args.work.resolve()
    require(not work.exists(), 'Preserve prior attempts/results; select a fresh --work directory')
    require(not inventory['existing_target_objects'],
            'Existing target objects require receipt review before further work: ' + json.dumps(inventory['existing_target_objects']))
    work.mkdir(parents=True)
    write(work / 'OBJECT_INVENTORY.json', inventory)
    old_missing = {m: q for m, q in inventory['missing'].items() if q['kind'] != 'new_Cell03_accepted_object'}
    require(not old_missing, 'Missing exact historical objects; see OBJECT_INVENTORY.json (no dependency rebuild)')
    suppliers = dict(inventory['accepted_suppliers'])
    missing_new = set(inventory['missing'])
    if missing_new:
        require(args.new_deps_archive is not None, 'Missing new dependencies; provide the existing seven-object archive')
        archive = checked(args.new_deps_archive.resolve(strict=True), plan['new_dependency_archive']['sha256'])
        require(archive.stat().st_size == plan['new_dependency_archive']['bytes'], 'Wrong existing object archive size')
        controls[archive] = plan['new_dependency_archive']['sha256']
        allowed = {q['path']: (m, q) for m, q in dependencies.items() if q['kind'] == 'new_Cell03_accepted_object'}
        with tarfile.open(archive, 'r:xz') as tar:
            members = tar.getmembers()
            require(len(members) == 7 and {m.name for m in members} == set(allowed) and all(m.isfile() for m in members),
                    'Existing seven-object archive scope differs')
            for member in members:
                m, row = allowed[member.name]
                require(member.size == row['bytes'], 'Archive member size differs: ' + m)
                stream = tar.extractfile(member)
                raw = stream.read()
                require(digest(raw) == row['sha256'], 'Archive object hash differs: ' + m)
                if m in missing_new:
                    destination = work / 'transferred-dependencies' / member.name
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_bytes(raw)
                    suppliers[m] = str(destination)
    require(set(suppliers) == set(dependencies), 'Incomplete accepted-object assembly')
    objects, package = work / 'objects', work / 'sources'
    for directory in (objects / 'ImbalancedChen', package / 'ImbalancedChen', work / 'evidence', work / 'audits'):
        directory.mkdir(parents=True, exist_ok=True)
    for m, q in dependencies.items():
        source = checked(Path(suppliers[m]), q['sha256'])
        standalone(source)
        target = objects / (m.replace('.', '/') + '.olean')
        target.symlink_to(source)
    for m in selected:
        shutil.copyfile(repo / owners[m]['source'], package / (m.replace('.', '/') + '.lean'))

    sys.path.insert(0, str(repo / 'verification/part2'))
    A = importlib.import_module('run_winner9_private_audit')
    E = importlib.import_module('winner9_external_snapshot')
    C = importlib.import_module('run_winner9_private_checks')
    snapshot_path = checked(Path(plan['external_snapshot']['path']), plan['external_snapshot']['sha256'])
    external = E.ExternalSnapshot(snapshot_path, lean=plan['lean'], mathlib_pin=C.PIN, project_lib=objects)
    binding = external.binding()
    for name, target in compatibility['modules'].items():
        require(external.value['resolutions'].get(name, target) == target, 'P2 finite module resolution differs: ' + name)
    for p, h in projected.items():
        if p in external.files:
            require(external.files[p]['sha256'] == h, 'Qualified finite runtime bytes differ: ' + p)
        else:
            require(compatibility['supplements'][p]['sha256'] == h, 'Unqualified finite runtime supplement: ' + p)
        checked(Path(p), h)
    def verify_supplemental_resolutions():
        for name in external_names - set(external.value['resolutions']):
            found = None
            for root in external.search_path:
                candidate = root / (name.replace('.', '/') + '.olean')
                if candidate.is_file():
                    found = candidate.resolve(strict=True)
                    break
                require(not (root / name.split('.', 1)[0]).is_dir(),
                        'Earlier incomplete package shadows supplemental module: ' + name)
            require(found == Path(compatibility['modules'][name]).resolve(strict=True),
                    'Finite supplemental module resolution changed: ' + name)

    verify_supplemental_resolutions()
    env = external.environment(os.environ)
    env['PATH'] = str(Path(plan['lean']).parent) + os.pathsep + env.get('PATH', '')
    os.environ.clear()
    os.environ.update(env)
    require(Path(shutil.which('lean')).resolve() == Path(plan['lean']).resolve() and
            Path(shutil.which('leanchecker')).resolve() == Path(plan['lean']).with_name('leanchecker').resolve(),
            'PATH does not resolve pinned stock tools')
    os.chdir(work)
    driver_path = repo / plan['reuse_driver']['path']
    tree = ast.parse(driver_path.read_bytes())
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    require({n.name: digest(ast.dump(n).encode()) for n in functions} == plan['reuse_driver']['functions'],
            'Original four owner-driver functions changed')
    extracted = ast.Module(body=[n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))] + functions,
                           type_ignores=[])
    r = types.ModuleType('existing_cell03_simplex_p2_runner')
    exec(compile(extracted, str(driver_path), 'exec'), r.__dict__)
    r.root, r.repo, r.package, r.work, r.objects = HERE, repo, package, work, objects
    r.strict, r.template = plan['strict_flags'], template
    r.aggregate, r.support, r.typed = 'P2Saving16Cell01ScalarDecode', 'P2Saving16Cell01FieldSimp', 'P2Saving16Cell01TypedPayload'
    r.hashes = {m.split('.')[-1]: q['source_sha256'] for m, q in owners.items()}
    original_audit_results = r.audit_results
    hashes = E.PhysicalHashes()
    p2_provenance = {**prepared, 'schema': 'p25-cell03-p2-provenance-v1', 'status': 'P2_EXECUTION_INPUTS_FROZEN',
                     'execution_environment': 'P2 cloud-compile-private-8e1da5a7',
                     'execution_root': str(work), 'repository': str(repo),
                     'source_publication': plan['source_publication'], 'external': binding,
                     'evidence_publication': plan['evidence_publication'],
                     'published_evidence_directory': plan['published_evidence_directory'],
                     'finite_runtime_sha256': plan['finite_runtime']['sha256'],
                     'prior_local_failures': failures, 'dependency_suppliers': suppliers,
                     'path_mapping': {'original_local_root': str(local_root), 'P2_root': str(work),
                                      'original_local_package': str(local_package), 'P2_selected_sources': str(package),
                                      'original_local_compiler': inputs['compiler'], 'P2_compiler': plan['lean'],
                                      'original_local_checker': inputs['stock_checker'],
                                      'P2_checker': str(Path(plan['lean']).with_name('leanchecker'))},
                     'actual_environment': {k: os.environ[k] for k in ('LEAN_PATH', 'LEAN_SYSROOT', 'PATH')},
                     'original_local_receipts_preserved': True, 'physical_geometry_proved': False}
    write(work / 'P2_PROVENANCE.json', p2_provenance)
    controls[work / 'P2_PROVENANCE.json'] = sha(work / 'P2_PROVENANCE.json')
    controls[work / 'OBJECT_INVENTORY.json'] = sha(work / 'OBJECT_INVENTORY.json')
    baseline = {'plan_sha256': PLAN_SHA, 'source_manifest_sha256': inputs['manifest_sha256'],
                'project_dependencies': {m: q['sha256'] for m, q in dependencies.items()},
                'source_sha256': {m: q['source_sha256'] for m, q in nodes.items()},
                'external': binding, 'finite_runtime_sha256': plan['finite_runtime']['sha256'],
                'original_local_external_map_sha256': inputs['external_map_sha256'],
                'p2_finite_runtime_map_sha256': jsig(projected),
                'local_evidence_capsule_sha256': plan['local_evidence_capsule']['sha256'],
                'p2_provenance_sha256': controls[work / 'P2_PROVENANCE.json']}
    context_signature = jsig(baseline)
    current_owner_hash = None
    accepted = {}

    def snapshot(name, label, phase, stage):
        nonlocal current_owner_hash
        m = 'ImbalancedChen.' + name
        for p, h in controls.items():
            require(hashes.digest(p) == h, 'Control/evidence changed during stage: ' + str(p))
        require(external.verify() == binding, 'Qualified P2 external context changed')
        verify_supplemental_resolutions()
        for p, q in compatibility['supplements'].items():
            require(hashes.digest(Path(p)) == q['sha256'], 'Finite supplemental runtime changed: ' + p)
        for d, q in nodes.items():
            require(hashes.digest(repo / q['source']) == q['source_sha256'], 'Pinned source changed: ' + d)
        for d, q in dependencies.items():
            p = objects / (d.replace('.', '/') + '.olean')
            standalone(p)
            standalone(p.resolve(strict=True))
            require(hashes.digest(p) == q['sha256'], 'Accepted dependency object changed: ' + d)
        for d, q in accepted.items():
            p = objects / (d.replace('.', '/') + '.olean')
            standalone(p)
            require(hashes.digest(p) == q['object_sha256'], 'Earlier accepted owner changed: ' + d)
            require(hashes.digest(Path(q['receipt'])) == q['receipt_sha256'], 'Earlier P2 receipt changed: ' + d)
        require(hashes.digest(package / (m.replace('.', '/') + '.lean')) == owners[m]['source_sha256'],
                'Selected P2 source copy changed')
        audit = work / 'audits' / (name + '.lean')
        require(audit.read_text() == template.replace('P2Saving16Cell00TypedPayload', name),
                'Full original audit program changed')
        obj = objects / (m.replace('.', '/') + '.olean')
        standalone(obj)
        actual = hashes.digest(obj) if obj.is_file() else None
        if current_owner_hash is None and actual is not None:
            require((label, phase) == ('NORMAL', 'after'), 'Owner object appeared before normal compile')
            current_owner_hash = actual
        if current_owner_hash is not None:
            require(actual == current_owner_hash, 'Compiled owner bytes changed during replay/audit')
        write(stage / f'{label}_{phase.upper()}_CONTEXT.json',
              {**baseline, 'context_signature': context_signature,
               'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'owner': m,
               'owner_object_sha256': actual, 'audit_source_sha256': sha(audit),
               'control_file_sha256': {str(p): h for p, h in controls.items()}})

    def audit_results(name, src, stage):
        m = 'ImbalancedChen.' + name
        result = original_audit_results(name, src, stage)
        parsed = A.parse_audit(stage / 'AUDIT.log', m, set(closure(m)))
        require(set(parsed['imports']) - closure(m) == external_names,
                'P2 owner does not use the exact original finite external module closure')
        names = {d['name'] for d in parsed['declarations']}
        require(set(expectations[m]) <= names and result['object_sha256'] == current_owner_hash,
                'Missing public declarations or changed owner object')
        stages = read(stage / 'STAGES.json')
        require([(s['stage'], s['exit_code']) for s in stages] == [(label, 0) for label in LOG_KEYS],
                'Missing successful normal/replay/audit stage')
        for s in stages:
            label = s['stage']
            s['log_sha256'] = sha(stage / (label + '.log'))
            s['resolved_executable'] = shutil.which(s['argv'][0])
            s['subprocess_argv'] = ['timeout', str(args.stage_limit) + 's', *s['argv']]
            for phase in ('BEFORE', 'AFTER'):
                c = read(stage / f'{label}_{phase}_CONTEXT.json')
                require(c['context_signature'] == context_signature and all(c[k] == v for k, v in baseline.items()),
                        'P2 stage input binding differs')
                require(c['owner_object_sha256'] == (None if (label, phase) == ('NORMAL', 'BEFORE') else current_owner_hash),
                        'P2 stage owner object differs')
        write(stage / 'STAGES.json', stages)
        write(stage / 'DECLARATIONS.json', parsed['declarations'])
        write(stage / 'declarations.json', parsed)
        (stage / 'types.txt').write_text('\n\n'.join(d['name'] + '\n' + d['type'] for d in parsed['declarations']) + '\n')
        artifacts = {p.name: sha(p) for p in stage.iterdir() if p.is_file() and p.name != 'RESULT.json'}
        result.update({'schema': 'p25-cell03-p2-scoped-acceptance-v1', 'accepted': True,
                       'execution_environment': p2_provenance['execution_environment'],
                       'manifest_sha256': inputs['manifest_sha256'], 'plan_sha256': PLAN_SHA,
                       'context_signature': context_signature, 'p2_provenance_sha256': controls[work / 'P2_PROVENANCE.json'],
                       'required_declarations': expectations[m], 'public_expectations_matched': len(expectations[m]),
                       'neighbor_inventory_reference_count': 17, 'reference_count_is_acceptance_gate': False,
                       'external_modules': len(set(parsed['imports']) - closure(m)), 'stages': stages, 'artifacts': artifacts,
                       'source_and_external_context_checked_before_after_every_stage': True,
                       'P2_5_proved': False, 'physical_geometry_proved': False})
        return result

    r.audit_results = audit_results
    for m in selected:
        name = m.split('.')[-1]
        current_owner_hash = None
        try:
            r.run_owner(name, stage_limit=args.stage_limit, snapshot=snapshot)
            receipt_path = work / 'evidence' / name / 'RESULT.json'
            receipt = read(receipt_path)
            accepted[m] = {'receipt': str(receipt_path), 'receipt_sha256': sha(receipt_path),
                           'object_sha256': receipt['object_sha256'], 'owned_count': receipt['owned_count']}
        except Exception as error:
            write(work / 'SUMMARY.json', {'accepted': accepted, 'failed': m, 'error': str(error), 'P2_5_proved': False})
            raise
    write(work / 'SUMMARY.json', {'schema': 'p25-cell03-p2-summary-v1', 'accepted': accepted,
                                 'all_requested_accepted': len(accepted) == len(selected), 'requested': selected,
                                 'dependencies_compiled': 0, 'P2_5_proved': False})
    print(json.dumps({'all_requested_accepted': True, 'owners': accepted, 'P2_5_proved': False}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
