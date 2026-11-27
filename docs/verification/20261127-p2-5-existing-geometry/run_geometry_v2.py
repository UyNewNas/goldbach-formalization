#!/usr/bin/env python3
"""Run existing geometry owners against accepted P2 and finite-cache objects.

No dependency is compiled. The original four run_new_owners functions and
complete owned-declaration audit/parser are reused with their byte hashes pinned.
--plan is read-only and claims no formal credit. Real runs require a terminal P2
receipt, its exact source graph, and accepted row-owner normal/replay/audit records.
"""
import argparse
import ast
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
import sys
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
MANIFEST_SHA = '268d0a2cea5a852594ae7b50b965c118ddf91916c8352c79a462ce0929fdb00d'
LEAN = '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean'
POSTFLIGHT = ('baseline_after_matches', 'external_after_matches', 'gate_after_matches',
              'head_after_matches', 'history_after_matches', 'prior_normal_reuse_after_matches',
              'prior_owned_reuse_after_matches', 'runner_after_matches', 'source_after_matches')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(p):
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def read(p):
    return json.loads(p.read_bytes())


def jsig(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def write(p, value):
    temporary = p.with_suffix(p.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(p)


def checked(p, expected):
    require(p.is_file() and sha(p) == expected, 'Missing or changed pinned file: ' + str(p))
    return p


def standalone(p):
    require(not any(Path(str(p) + suffix).exists() for suffix in ('.private', '.server')),
            'Unqualified project companion beside standalone object: ' + str(p))


def source_path(repo, relative):
    p = (repo / relative).resolve(strict=True)
    require(p.is_relative_to(repo), 'Source outside selected repository: ' + str(p))
    return p


def main():
    require(__debug__, 'Python optimization disables assertions in the reused original runner')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--only', nargs='+', default=['Cell00TypedGeometry'])
    ap.add_argument('--plan', action='store_true')
    ap.add_argument('--source-closure', type=Path)
    ap.add_argument('--source-closure-sha256')
    ap.add_argument('--run-result', type=Path)
    ap.add_argument('--run-result-sha256')
    ap.add_argument('--finite-objects', type=Path, action='append', default=[],
                    help='Existing accepted .olean roots, searched in order; may be repeated')
    ap.add_argument('--work', type=Path)
    ap.add_argument('--stage-limit', type=int, default=900)
    args = ap.parse_args()
    repo = args.repo.resolve(strict=True)
    manifest_path = checked(HERE / 'MANIFEST.json', MANIFEST_SHA)
    manifest = read(manifest_path)
    for p, h in manifest['repo_helpers'].items():
        checked(repo / p, h)
    cache_path = checked(HERE / manifest['cache_manifest']['path'], manifest['cache_manifest']['sha256'])
    cached = read(cache_path)['project_objects']
    driver_path = checked(HERE / manifest['reuse_driver']['path'], manifest['reuse_driver']['sha256'])
    compatibility_path = checked(HERE / manifest['finite_runtime']['path'], manifest['finite_runtime']['sha256'])
    compatibility = json.loads(lzma.decompress(compatibility_path.read_bytes()))
    owners = manifest['owners']
    selected = set()
    for name in args.only:
        full = name if name.startswith('ImbalancedChen.') else 'ImbalancedChen.' + (
            name if name.startswith('P2Saving16') else 'P2Saving16' + name)
        require(full in owners, 'Unknown existing geometry owner: ' + name)
        selected.add(full)
    if args.plan:
        graph_path = args.source_closure or HERE / 'PLANNED_ANALYTIC_SOURCE_CLOSURE.json'
    else:
        require(all([args.source_closure, args.source_closure_sha256, args.run_result,
                     args.run_result_sha256, args.work]), 'A real run requires exact terminal receipt/graph pins and --work')
        graph_path = checked(args.source_closure, args.source_closure_sha256)
    graph_path = graph_path.resolve(strict=True)
    graph = read(graph_path)['modules']
    nodes = {}
    visiting = set()

    def visit(m):
        require(m not in visiting, 'Project import cycle: ' + m)
        if m in nodes:
            return
        visiting.add(m)
        if m in owners:
            row = dict(owners[m], kind='new')
        elif m in manifest['finite']:
            row = dict(manifest['finite'][m], kind='finite')
            old = cached[m]
            require(all(row[k] == old[k] for k in ('path', 'source_sha256', 'sha256', 'bytes', 'basis')),
                    'Finite-cache provenance differs: ' + m)
        else:
            row = dict(graph[m], kind='analytic', source_sha256=graph[m]['sha256'])
        if row['kind'] != 'analytic' or not args.plan:
            p = source_path(repo, row['source'])
            checked(p, row['source_sha256'])
            require(re.findall(r'^import (ImbalancedChen\.[\w.]+)', p.read_text(), re.M) == row['imports'],
                    'Selected source import list changed: ' + m)
        for dep in row['imports']:
            visit(dep)
        visiting.remove(m)
        nodes[m] = row

    for m in sorted(selected):
        visit(m)
    ordered_owners = [m for m, q in nodes.items() if q['kind'] == 'new']
    rows = sorted({owners[m]['row_owner'] for m in ordered_owners})
    counts = {kind: sum(q['kind'] == kind for q in nodes.values()) for kind in ('finite', 'analytic', 'new')}
    if args.plan:
        print(json.dumps({'status': 'PLAN_ONLY_NO_FORMAL_CREDIT', 'owners_in_dependency_order': ordered_owners,
                          'required_accepted_row_owners': rows, 'counts': counts,
                          'finite_objects': {m: {'path': q['path'], 'sha256': q['sha256'], 'bytes': q['bytes']}
                                             for m, q in nodes.items() if q['kind'] == 'finite'}}, indent=2))
        return 0

    terminal_path = checked(args.run_result, args.run_result_sha256).resolve(strict=True)
    terminal = read(terminal_path)
    require(all(terminal.get(k) is True for k in POSTFLIGHT), 'P2 terminal source/context/reuse postflight failed')
    require(terminal.get('project_modules') == len(graph), 'Terminal receipt/source graph size differs')
    require(terminal['external_before'] == terminal['external_after'], 'P2 external context changed')
    blocked = set(terminal['compile_summary']['failed_or_blocked']) | set(terminal['compile_summary']['pending'])
    analytic_names = {m for m, q in nodes.items() if q['kind'] == 'analytic'}
    require(not analytic_names & blocked, 'Selected analytic prerequisites failed or remain pending')
    for m in rows:
        require(terminal['audit_summary']['modules'][m]['accepted'] is True,
                'Required row owner lacks terminal owned acceptance: ' + m)

    sys.path.insert(0, str(repo / 'verification/part2'))
    A = importlib.import_module('run_winner9_private_audit')
    E = importlib.import_module('winner9_external_snapshot')
    C = importlib.import_module('run_winner9_private_checks')
    analytic_lib = repo / '.lake/p2-private/lib'
    snapshot_path = Path(terminal['external_after']['snapshot'])
    checked(snapshot_path, manifest['external_snapshot_sha256'])
    original_external = E.ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=C.PIN, project_lib=analytic_lib)
    require(original_external.binding() == terminal['external_after'], 'Current P2 external binding differs from terminal')
    records_path = repo / '.lake/p2-private/records.json'
    records = read(records_path)
    analytic_objects = {}
    prerequisite_receipts = {}
    observed_analytic = set()
    for target in rows:
        row_nodes = A.project_nodes(repo, target)
        require(set(row_nodes) <= analytic_names, 'Analytic row closure escaped selected geometry source graph')
        observed_analytic.update(row_nodes)
        receipt_path = repo / '.lake/p2-private/audit' / target / 'latest.json'
        receipt = read(receipt_path)
        require(receipt.get('accepted') is True and receipt.get('module') == target,
                'No accepted normal/replay/owned receipt: ' + target)
        E.mark_project_nodes(row_nodes, set(original_external.modules))
        frozen = A.snapshot(repo, analytic_lib, row_nodes, receipt['input_snapshot']['toolchain'], original_external)
        A.verify_compilation(records, row_nodes, frozen)
        require(receipt['input_snapshot'] == frozen and A.artifacts_valid(repo, receipt['artifacts']),
                'Row receipt does not match current source/object/context/artifact bytes: ' + target)
        require(receipt['input_sha256'] == C.json_digest(frozen) and
                receipt['compile_closure_signature'] == records[target]['closure_signature'],
                'Row receipt signature differs from normal compilation: ' + target)
        for label in ('replay', 'audit'):
            require(receipt[label]['exit_code'] == 0 and receipt[label]['inputs_unchanged'] is True,
                    'Unaccepted row stage: ' + target + '/' + label)
        A.parse_audit(repo / receipt['audit']['log'], target, set(row_nodes))
        for m, q in frozen['project'].items():
            require(q['source_sha256'] == nodes[m]['source_sha256'], 'Row source differs from selected graph: ' + m)
            analytic_objects[m] = {'path': q['object'], 'sha256': q['object_sha256']}
        prerequisite_receipts[target] = {'path': str(receipt_path), 'sha256': sha(receipt_path),
                                        'input_sha256': receipt['input_sha256'],
                                        'compile_closure_signature': receipt['compile_closure_signature']}
    require(observed_analytic == analytic_names, 'A selected analytic dependency lacks an accepted row closure')

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    objects = work / 'objects'
    package = work / 'sources'
    for d in (objects / 'ImbalancedChen', package / 'ImbalancedChen', work / 'evidence', work / 'audits'):
        d.mkdir(parents=True, exist_ok=True)
    object_hashes = {}
    suppliers = {}
    roots = [p.resolve(strict=True) for p in args.finite_objects]
    for m, q in nodes.items():
        if q['kind'] == 'new':
            source = source_path(repo, q['source'])
            dest = package / (m.replace('.', '/') + '.lean')
            if dest.exists():
                checked(dest, q['source_sha256'])
            else:
                shutil.copyfile(source, dest)
            continue
        if q['kind'] == 'finite':
            possible = [p / q['path'] for p in roots]
            # Existing P2 finite objects are preferred when their accepted bytes match.
            possible.insert(0, analytic_lib / q['path'])
            supplier = next((p for p in possible if p.is_file() and sha(p) == q['sha256']), None)
            require(supplier is not None, 'Missing accepted finite object: ' + m)
            h = q['sha256']
        else:
            supplier = Path(analytic_objects[m]['path'])
            h = analytic_objects[m]['sha256']
        target = objects / (m.replace('.', '/') + '.olean')
        standalone(target)
        if target.exists() or target.is_symlink():
            checked(target, h)
        else:
            target.symlink_to(supplier)
        object_hashes[m] = h
        suppliers[m] = str(supplier)

    external = E.ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=C.PIN, project_lib=objects)
    external_binding = external.binding()
    require(compatibility['external_snapshot_sha256'] == manifest['external_snapshot_sha256'],
            'Finite-runtime compatibility binds a different qualified environment')
    for name, target in compatibility['modules'].items():
        wanted = external.value['resolutions'].get(name, target)
        require(wanted == target, 'Finite-runtime resolution mismatch: ' + name)
    for p, h in compatibility['runtime'].items():
        if p in external.files:
            require(external.files[p]['sha256'] == h, 'Finite-runtime byte mismatch: ' + p)
        else:
            require(compatibility['supplements'][p]['sha256'] == h, 'Unbound finite supplemental input: ' + p)
        checked(Path(p), h)
    external_names = set(external.value['resolutions']) | set(compatibility['modules'])
    env = external.environment(os.environ)
    env['PATH'] = str(Path(LEAN).parent) + os.pathsep + env.get('PATH', '')
    os.environ.clear()
    os.environ.update(env)
    require(Path(shutil.which('lean')).resolve() == Path(LEAN).resolve() and
            Path(shutil.which('leanchecker')).resolve() == Path(LEAN).with_name('leanchecker').resolve(),
            'PATH does not select pinned stock tools')
    os.chdir(work)

    original_tree = ast.parse(driver_path.read_bytes())
    functions = [n for n in original_tree.body if isinstance(n, ast.FunctionDef)]
    require({n.name: hashlib.sha256(ast.dump(n).encode()).hexdigest() for n in functions} ==
            manifest['reuse_driver']['functions'], 'Reused owner driver functions changed')
    extracted = ast.Module(body=[n for n in original_tree.body if isinstance(n, (ast.Import, ast.ImportFrom))] + functions,
                           type_ignores=[])
    r = types.ModuleType('existing_geometry_owner_runner')
    exec(compile(extracted, str(driver_path), 'exec'), r.__dict__)
    r.root, r.repo, r.package, r.work, r.objects = HERE, repo, package, work, objects
    r.strict = manifest['strict_flags']
    r.template = (repo / 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean').read_text()
    r.aggregate, r.support, r.typed = 'P2Saving16Cell01ScalarDecode', 'P2Saving16Cell01FieldSimp', 'P2Saving16Cell01TypedPayload'
    r.hashes = {m.split('.')[-1]: q['source_sha256'] for m, q in owners.items()}
    original_audit_results = r.audit_results
    hashes = E.PhysicalHashes()
    file_pins = {manifest_path: MANIFEST_SHA, cache_path: manifest['cache_manifest']['sha256'],
                 compatibility_path: manifest['finite_runtime']['sha256'],
                 driver_path: manifest['reuse_driver']['sha256'],
                 graph_path.resolve(): args.source_closure_sha256, terminal_path.resolve(): args.run_result_sha256,
                 Path(__file__).resolve(): sha(Path(__file__).resolve())}
    file_pins.update({repo / p: h for p, h in manifest['repo_helpers'].items()})
    file_pins.update({Path(q['path']): q['sha256'] for q in prerequisite_receipts.values()})

    @functools.cache
    def closure(m):
        return {m}.union(*(closure(dep) for dep in nodes[m]['imports']))

    def context_signature(m):
        deps = closure(m) - {m}
        return jsig({'manifest_sha256': MANIFEST_SHA,
                     'project_sources': {d: nodes[d]['source_sha256'] for d in sorted(closure(m))},
                     'dependency_objects': {d: object_hashes[d] for d in sorted(deps)},
                     'external': external_binding, 'finite_runtime': manifest['finite_runtime']['sha256']})

    current_owner_hash = None

    def snapshot(name, label, phase, stage):
        nonlocal current_owner_hash
        m = 'ImbalancedChen.' + name
        for p, h in file_pins.items():
            require(hashes.digest(p) == h, 'Control/receipt changed during stage: ' + str(p))
        require(external.verify() == external_binding, 'Qualified external context changed during stage')
        for p, q in compatibility['supplements'].items():
            require(hashes.digest(Path(p)) == q['sha256'], 'Supplemental external bytes changed: ' + p)
        selected_sources, dependency_objects = {}, {}
        for d in sorted(closure(m)):
            src = source_path(repo, nodes[d]['source'])
            checked(src, nodes[d]['source_sha256'])
            selected_sources[d] = {'path': str(src), 'sha256': nodes[d]['source_sha256']}
            standalone(objects / (d.replace('.', '/') + '.olean'))
            if d != m:
                p = objects / (d.replace('.', '/') + '.olean')
                require(hashes.digest(p) == object_hashes[d], 'Dependency object changed: ' + d)
                dependency_objects[d] = {'path': str(p), 'sha256': object_hashes[d]}
        checked(package / (m.replace('.', '/') + '.lean'), owners[m]['source_sha256'])
        audit = work / 'audits' / (name + '.lean')
        require(audit.read_text() == r.template.replace('P2Saving16Cell00TypedPayload', name),
                'Audit source changed during stage')
        obj = objects / (m.replace('.', '/') + '.olean')
        standalone(obj)
        actual = hashes.digest(obj) if obj.is_file() else None
        if current_owner_hash is None and actual is not None:
            require(label == 'NORMAL' and phase == 'after', 'Owner object existed before normal compile')
            current_owner_hash = actual
        if current_owner_hash is not None:
            require(actual == current_owner_hash, 'Compiled owner object changed before replay/audit completed')
        record = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'manifest_sha256': MANIFEST_SHA, 'context_signature': context_signature(m),
                  'project_sources': selected_sources, 'dependency_objects': dependency_objects,
                  'owner_object_sha256': actual, 'external': external_binding,
                  'finite_runtime_sha256': manifest['finite_runtime']['sha256'], 'audit_source_sha256': sha(audit),
                  'p2_terminal_sha256': args.run_result_sha256, 'prerequisite_receipts': prerequisite_receipts}
        write(stage / f'{label}_{phase.upper()}_CONTEXT.json', record)

    def audit_results(name, src, stage):
        m = 'ImbalancedChen.' + name
        result = original_audit_results(name, src, stage)
        parsed = A.parse_audit(stage / 'AUDIT.log', m, closure(m))
        require(set(parsed['imports']) - closure(m) <= external_names, 'Loaded unqualified external module')
        names = {q['name'] for q in parsed['declarations']}
        require(set(owners[m]['required_declarations']) <= names, 'Missing original public theorem')
        require(result['object_sha256'] == current_owner_hash, 'Audited owner object differs')
        stages = read(stage / 'STAGES.json')
        require([(q['stage'], q['exit_code']) for q in stages] == [('NORMAL', 0), ('REPLAY', 0), ('AUDIT', 0)],
                'Missing successful normal/replay/audit stage')
        for label in ('NORMAL', 'REPLAY', 'AUDIT'):
            for phase in ('BEFORE', 'AFTER'):
                state = read(stage / f'{label}_{phase}_CONTEXT.json')
                require(state['context_signature'] == context_signature(m), 'Stage dependency context differs')
                if (label, phase) != ('NORMAL', 'BEFORE'):
                    require(state['owner_object_sha256'] == current_owner_hash, 'Stage owner object differs')
        write(stage / 'declarations.json', parsed)
        (stage / 'types.txt').write_text('\n\n'.join(q['name'] + '\n' + q['type'] for q in parsed['declarations']) + '\n')
        artifacts = {p.name: sha(p) for p in stage.iterdir() if p.is_file() and p.name != 'RESULT.json'}
        result.update({'accepted': True, 'schema': 'p25-existing-geometry-scoped-acceptance-v1',
                       'manifest_sha256': MANIFEST_SHA, 'context_signature': context_signature(m),
                       'prerequisite_receipts': prerequisite_receipts, 'p2_terminal_sha256': args.run_result_sha256,
                       'required_declarations': owners[m]['required_declarations'],
                       'artifacts': artifacts, 'P2_5_proved': False})
        return result

    r.audit_results = audit_results
    accepted = {}
    for m in ordered_owners:
        name = m.split('.')[-1]
        stage = work / 'evidence' / name
        obj = objects / (m.replace('.', '/') + '.olean')
        standalone(obj)
        if (stage / 'RESULT.json').exists():
            prior = read(stage / 'RESULT.json')
            require(prior.get('accepted') is True and prior.get('manifest_sha256') == MANIFEST_SHA and
                    prior['source_sha256'] == owners[m]['source_sha256'] and
                    prior['context_signature'] == context_signature(m), 'Existing geometry receipt cannot be reused: ' + m)
            checked(obj, prior['object_sha256'])
            for p, h in prior['artifacts'].items():
                checked(stage / p, h)
            A.parse_audit(stage / 'AUDIT.log', m, closure(m))
            object_hashes[m] = prior['object_sha256']
            accepted[m] = {'accepted': True, 'reused': True, 'object_sha256': prior['object_sha256']}
            print('REUSE_GEOMETRY', m, flush=True)
            continue
        require(not obj.exists() and not stage.exists(), 'Unaccepted prior geometry attempt preserved; select a fresh --work')
        current_owner_hash = None
        try:
            r.run_owner(name, stage_limit=args.stage_limit, snapshot=snapshot)
            receipt = read(stage / 'RESULT.json')
            object_hashes[m] = receipt['object_sha256']
            accepted[m] = {'accepted': True, 'reused': False, 'object_sha256': receipt['object_sha256'],
                           'owned_count': receipt['owned_count']}
        except Exception as error:
            write(work / 'SUMMARY.json', {'accepted': accepted, 'failed': m, 'error': str(error), 'P2_5_proved': False})
            raise
    write(work / 'SUMMARY.json', {'accepted': accepted, 'requested': ordered_owners,
                                 'all_requested_accepted': len(accepted) == len(ordered_owners),
                                 'dependency_counts': counts, 'suppliers': suppliers, 'P2_5_proved': False})
    print(json.dumps({'all_requested_accepted': True, 'owners': accepted, 'P2_5_proved': False}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
