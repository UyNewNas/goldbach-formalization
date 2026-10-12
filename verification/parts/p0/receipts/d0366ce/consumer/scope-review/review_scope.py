#!/usr/bin/env python3
"""Independent static/raw-artifact review, not execution of either consumer.

Reads two consumer ASTs, their exact diff, fixed Git source, original CI ZIP and
the already-written consumer outputs. Executes only read-only git show commands;
does not import either consumer or run Lean, CI, or build/environment commands.
"""
from pathlib import Path
import ast
from collections import Counter
import copy
import csv
import difflib
from functools import lru_cache
import hashlib
import io
import json
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
PREP = OUT.parent
REPO = PREP.parents[1] / 'goldbach-formalization'
NEW = PREP / 'consume_core_artifact.py'
OLD = PREP / 'consumer-corrections/before-actual-core-import-scope-fix/consume_core_artifact.py'
PATCH = PREP / 'consumer-corrections/ACTUAL_IMPORT_SCOPE_FIX.patch'
ATTEMPT = PREP / 'actual-d0366-consumed-attempt2'
FIRST = PREP / 'actual-d0366-consumed'
SHA = 'd0366ce64272e81faf6166a8a90050f56b328d38'
OLD_HASH = '925ebb6e12e1693635ca56dfbf58fc548e5ee350897079a95b0bf11b63b6ed63'
NEW_HASH = '5d697e55919c1e8a35053fbfb662605839ddba9319266b3ed97bc9a497c20e18'
ZIP_HASH = '4d7499fd526651d70f73fb7cbbf98769ffc51d8a406e1bc80f96ad5dc0d20df8'
THREE = {'ImbalancedChen.Certificates.PairedCertificateChecker',
         'ImbalancedChen.Certificates.PairedFibreIntegral',
         'ImbalancedChen.Certificates.RationalLogCertificate'}
STAGES = ['build', 'round4-targets', 'leanchecker', 'axiom-audit', 'round3-types', 'round4-types']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEDGER = 'verification/parts/p0/round4/ledger'
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def jread(path):
    return json.loads(path.read_text())


def write(name, obj):
    (OUT / name).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')


def ck(name, valid, detail=None):
    checks.append({'check': name, 'status': 'PASS' if valid else 'FAIL', 'detail': detail})
    if not valid:
        write('REVIEW_CHECKS.json', {'status': 'STATIC_REVIEW_MISMATCH_NOT_LEAN_DIAGNOSTIC', 'checks': checks})
        raise AssertionError(name)


@lru_cache(maxsize=None)
def fixed(path):
    return subprocess.check_output(['git', 'show', SHA + ':' + path], cwd=REPO)


def defs(tree):
    result = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            result[node.name] = node
        if isinstance(node, ast.ClassDef):
            for member in node.body:
                if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    result[node.name + '.' + member.name] = member
    return result


def literal(tree, name):
    return ast.literal_eval(next(n.value for n in tree.body if isinstance(n, ast.Assign)
                           and any(isinstance(t, ast.Name) and t.id == name for t in n.targets)))


def import_names(data):
    # Independent length-preserving masker for nested Lean comments and strings.
    src = data.decode(); chars = list(src); i = 0; depth = 0; string = False
    while i < len(src):
        if depth:
            if src.startswith('/-', i):
                chars[i:i+2] = [' ', ' ']; depth += 1; i += 2; continue
            if src.startswith('-/', i):
                chars[i:i+2] = [' ', ' ']; depth -= 1; i += 2; continue
            if src[i] != '\n': chars[i] = ' '
            i += 1; continue
        if string:
            if src[i] == '\\' and i + 1 < len(src):
                chars[i] = ' '; chars[i+1] = '\n' if src[i+1] == '\n' else ' '; i += 2; continue
            if src[i] == '"': string = False
            if src[i] != '\n': chars[i] = ' '
            i += 1; continue
        if src.startswith('/-', i):
            chars[i:i+2] = [' ', ' ']; depth = 1; i += 2; continue
        if src.startswith('--', i):
            while i < len(src) and src[i] != '\n': chars[i] = ' '; i += 1
            continue
        if src[i] == '"': string = True; chars[i] = ' '
        i += 1
    return {name for match in re.finditer(r'^\s*import[ \t]+([^\n]+)', ''.join(chars), re.M)
            for name in match.group(1).split()}


def main():
    old_bytes = OLD.read_bytes(); new_bytes = NEW.read_bytes()
    ck('consumer source identities', sha(old_bytes) == OLD_HASH and sha(new_bytes) == NEW_HASH)
    exact_diff = ''.join(difflib.unified_diff(old_bytes.decode().splitlines(keepends=True),
        new_bytes.decode().splitlines(keepends=True),
        fromfile='consumer-before-actual-scope-fix.py', tofile='consumer-after-actual-scope-fix.py'))
    ck('published patch equals full actual consumer difference', exact_diff == PATCH.read_text())
    old_ast = ast.parse(old_bytes); new_ast = ast.parse(new_bytes)
    od, nd = defs(old_ast), defs(new_ast)
    changed = sorted(n for n in od if ast.dump(od[n], include_attributes=False) != ast.dump(nd[n], include_attributes=False))
    ck('only two reviewed methods changed', set(od) == set(nd) and len(od) == 28
       and changed == ['Consumer.check_root_and_fixed_inputs', 'Consumer.merge_and_write'])
    for tree in (old_ast, new_ast):
        for node in defs(tree).values():
            if node.name in ('check_root_and_fixed_inputs', 'merge_and_write'):
                node.body = [ast.Pass()]
    ck('all code outside these two bodies is AST-identical', ast.dump(old_ast, include_attributes=False) == ast.dump(new_ast, include_attributes=False))
    old_ast = ast.parse(old_bytes); new_ast = ast.parse(new_bytes)
    def reqs(tree):
        return Counter(ast.dump(n, include_attributes=False) for n in ast.walk(tree) if isinstance(n, ast.Call)
            and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name)
            and n.func.value.id == 'self' and n.func.attr == 'require')
    removed, added = reqs(old_ast) - reqs(new_ast), reqs(new_ast) - reqs(old_ast)
    ck('only one old requirement removed', sum(removed.values()) == 1 and
       'Accepted production module is explicitly imported by the root:' in next(iter(removed)))
    ck('four requirements added', sum(added.values()) == 4)
    write('AST_SCOPE.json', {'old_sha256': OLD_HASH, 'new_sha256': NEW_HASH,
        'changed_methods': changed, 'unchanged_methods': sorted(set(od) - set(changed)),
        'removed_require_calls': list(removed.elements()), 'added_require_calls': list(added.elements()),
        'all_other_code_ast_identical': True, 'patch_sha256': sha(PATCH.read_bytes())})
    expected = literal(new_ast, 'ROUND_MODULES')
    frozen = literal(new_ast, 'FROZEN')
    ck('fixed module counts are 198 and 414', sum(expected[3].values()) == 198 and sum(expected[4].values()) == 414)

    artifact_path = ATTEMPT / 'original-metadata/core-artifact.zip'
    raw_zip = artifact_path.read_bytes()
    ck('actual artifact identical across first failed and successful consumption',
       raw_zip == (FIRST / 'original-metadata/core-artifact.zip').read_bytes() and sha(raw_zip) == ZIP_HASH)
    for filename in ['run.json', 'jobs.json', 'artifacts.json']:
        ck('original actual metadata preserved ' + filename,
           (ATTEMPT / 'original-metadata' / filename).read_bytes() == (FIRST / 'original-metadata' / filename).read_bytes())
    run = jread(ATTEMPT / 'original-metadata/run.json')
    jobs = jread(ATTEMPT / 'original-metadata/jobs.json')
    artifacts = jread(ATTEMPT / 'original-metadata/artifacts.json')
    job = next(j for j in jobs['jobs'] if j['id'] == 114946653833)
    art = next(a for a in artifacts['artifacts'] if a['id'] == 11767708658)
    ck('actual run/job/source and metadata result', run['id'] == 38289734671 and run['head_sha'] == SHA
       and run['run_attempt'] == 1 and run['status'] == job['status'] == 'completed'
       and run['conclusion'] == job['conclusion'] == 'success')
    ck('artifact digest and exact run binding', art['digest'] == 'sha256:' + ZIP_HASH
       and art['size_in_bytes'] == len(raw_zip) == 543994 and art['workflow_run']['head_sha'] == SHA
       and art['workflow_run']['id'] == run['id'])
    consumed = jread(ATTEMPT / 'CORE_RECEIPT.json')
    first = jread(FIRST / 'CORE_RECEIPT.json')
    ck('original failure is an evidence-consumer error', first['status'] == 'FAILED_EVIDENCE_CONSUMPTION'
       and first['consumer_exit_code'] == 1 and first['checks_failed'] == 1
       and first['first_real_lean_diagnostics_preserved'] == 0
       and first['error'].endswith('Accepted production module is explicitly imported by the root: ImbalancedChen.Certificates.PairedCertificateChecker'))
    ck('actual attempt2 output reports scoped success', consumed['status'] == 'PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE'
       and consumed['consumer_exit_code'] == 0 and consumed['checks_failed'] == 0
       and consumed['main_theorem_is_conditional'] is True and consumed['hLower_hUpper_discharged'] is False)

    ledger = json.loads(fixed(LEDGER + '/MODULE_LEDGER_CANDIDATE.json'))
    accepted = {r['module']: r for r in ledger['modules'] if r['component_evidence_accepted']}
    new_ledger = jread(ATTEMPT / 'MODULE_LEDGER_VERIFIED.json')
    new_rows = {r['module']: r for r in new_ledger['modules']}
    source_paths = {'ImbalancedChen': ['ImbalancedChen']}; queue = ['ImbalancedChen']
    while queue:
        current = queue.pop(0)
        for imported in sorted(import_names(fixed(current.replace('.', '/') + '.lean'))):
            if imported.startswith('ImbalancedChen.') and imported not in source_paths:
                source_paths[imported] = source_paths[current] + [imported]; queue.append(imported)
    direct = import_names(fixed('ImbalancedChen.lean'))
    ck('23 accepted modules are genuinely reachable in fixed root source', len(source_paths) == 276
       and len(accepted) == 23 and set(accepted) <= set(source_paths))
    ck('three affected historical modules are not root direct imports', not (THREE & direct))
    ck('all reported root paths match independently walked fixed graph',
       consumed['observed']['accepted_module_root_import_paths'] == {m: source_paths[m] for m in accepted})
    ck('all four new modules remain root direct imports', len(expected[4]) == 4 and set(expected[4]) <= direct)
    workflow = fixed('.github/workflows/lean.yml').decode()
    target_block = workflow.split('- name: Check the four explicit round 4 production targets', 1)[1].split('- name:', 1)[0]
    explicit_targets = re.findall(r'(?m)^\s+(ImbalancedChen\.\S+?)(?:\s*\\)?$', target_block)
    ck('fixed workflow actual target command lists exactly four new modules',
       'round4-targets lake build' in target_block and explicit_targets == list(expected[4]))

    stage_rows, export_info, export_receipts, declarations = [], {}, {}, {}
    with zipfile.ZipFile(io.BytesIO(raw_zip)) as archive:
        names = archive.namelist()
        logs = {s: archive.read('_temp/lean-verification-logs/' + s + '.log').decode() for s in STAGES}
        outcomes = dict(line.split('=', 1) for line in archive.read('_temp/lean-verification-logs/outcomes.log').decode().splitlines())
        ck('all six raw required outcomes are success', outcomes == {s: 'success' for s in STAGES})
        for stage in STAGES:
            timing = list(csv.DictReader(io.StringIO(archive.read('_temp/lean-verification-logs/' + stage + '.timing.tsv').decode()), delimiter='\t'))
            ck('actual timing success ' + stage, len(timing) == 1 and timing[0]['stage'] == stage
               and timing[0]['exit_code'] == '0' and int(timing[0]['elapsed_seconds']) >= 0)
            ck('consumed original raw log identity ' + stage,
               logs[stage].encode() == (ATTEMPT / 'actual-logs' / (stage + '.log')).read_bytes())
            step = next(row for row in consumed['observed']['required_job_steps'] if row['stage'] == stage)
            actual_step = next(row for row in job['steps'] if row['number'] == step['number'])
            ck('actual job step completed ' + stage, actual_step['name'] == step['name']
               and actual_step['status'] == 'completed' and actual_step['conclusion'] == 'success')
            stage_rows.append({**timing[0], 'log_sha256': sha(logs[stage].encode()), 'outcome': outcomes[stage]})
        replay = logs['leanchecker'].splitlines()
        ck('actual root and all 23 accepted module replay markers exist', 'replaying ImbalancedChen' in replay
           and all('replaying ' + m in replay for m in accepted))
        root_audit = re.findall(r"axiom-audit: audited (\d+) declaration\(s\) under 'ImbalancedChen'; all within the allowlist \[([^\]]+)\]\.", logs['axiom-audit'])
        ck('actual full root audit census and unchanged allowlist', len(root_audit) == 1
           and root_audit[0][0] == '5872' and {s.strip() for s in root_audit[0][1].split(',')} == ALLOWED
           and 'axiom-audit completed successfully' in logs['axiom-audit'].splitlines())
        for n in [3, 4]:
            receipt_name = next(name for name in names if '/.lake/part0-round' + str(n) + '-types/' in name and name.endswith('/receipt.json'))
            prefix = receipt_name.rsplit('/', 1)[0]
            receipt = json.loads(archive.read(receipt_name)); export_receipts[n] = receipt
            ck('actual Round export SHA/gate/strict scope ' + str(n), receipt['source_commit'] == receipt['source_commit_after'] == SHA
               and receipt['status'] == 'PASS' and receipt['lean_exit_code'] == receipt['pin_check_exit_code'] == 0
               and receipt['command'][1:5] == ['env', 'lean', '-DwarningAsError=true', '-o']
               and receipt['expected_defining_module_counts'] == expected[n]
               and receipt['full_types_untruncated'] is True and receipt['unsafe_and_new_axiom_checks'] == 'PASS_IN_LEAN')
            ck('entire per-round before/after input snapshots equal ' + str(n), receipt['inputs_before'] == receipt['inputs_after'])
            source_map = receipt['inputs_before']['source_sha256']; objects = receipt['inputs_before']['production_olean_parts']
            ck('actual snapshot counts and source bytes ' + str(n), len(source_map) == 274 and len(objects) == 267
               and all(sha(fixed(path)) == digest for path, digest in source_map.items()))
            seed = set(expected[n]) | {'ImbalancedChen', 'ImbalancedChen.CurrentMainTheorem'}
            scope = set(seed)
            for module in seed:
                scope |= {x for x in import_names(fixed(module.replace('.', '/') + '.lean'))
                          if x == 'ImbalancedChen' or x.startswith('ImbalancedChen.')}
            ck('object scope matches fixed exporter one-hop seed scope ' + str(n), set(objects) == scope)
            raw_decl = archive.read(prefix + '/declarations.json'); records = json.loads(raw_decl); declarations[n] = records
            stdout = archive.read(prefix + '/stdout.log').decode()
            marker = 'P0_ROUND' + str(n) + '_DECL '
            raw_records = [json.loads(line[len(marker):]) for line in stdout.splitlines() if line.startswith(marker)]
            ck('actual complete 198/414 declarations match raw compiler records ' + str(n), records == raw_records
               and len(records) == len({r['name'] for r in records}) == sum(expected[n].values())
               and Counter(r['module'] for r in records) == Counter(expected[n]))
            ck('actual declaration type/axiom checks ' + str(n), all(r['kind'] != 'axiom'
               and set(r['axioms']) <= ALLOWED and isinstance(r['type'], str) and r['type'].strip()
               and not any(s in r['type'] for s in ['⋯', '…', '<proof>']) for r in records))
            ck('actual payload and stdout hashes are receipt-bound ' + str(n),
               sha(raw_decl) == receipt['compiler_output_files_sha256']['declarations.json']
               and sha(stdout.encode()) == receipt['stdout_sha256'] and stdout in logs['round' + str(n) + '-types'])
            ck('actual pp.all audit retains unsafe/new-axiom guards ' + str(n), all(token in fixed('verification/parts/p0/Round' + str(n) + 'Audit.lean').decode()
               for token in ['set_option pp.all true', 'if info.isUnsafe then', 'if info.isAxiom then', 'collectAxioms name', 'env.getModuleIdxFor? name']))
            bridge = json.loads(archive.read(prefix + '/final-bridge.json'))
            ck('actual final bridge remains visibly conditional ' + str(n), 'hLower' in bridge['type'] and 'hUpper' in bridge['type']
               and receipt['final_bridge_is_conditional'] is True and receipt['hLower_hUpper_discharged'] is False)
            export_info[n] = {'receipt_member': receipt_name, 'receipt_sha256': sha(archive.read(receipt_name)),
                'source_count': len(source_map), 'object_module_count': len(objects), 'declarations': len(records),
                'declarations_sha256': sha(raw_decl), 'compiler_seconds': receipt['elapsed_seconds']}

    r3 = export_receipts[3]['inputs_before']; r4 = export_receipts[4]['inputs_before']
    ck('cross-round production object maps equal', r3['production_olean_parts'] == r4['production_olean_parts'])
    a, b = r3['source_sha256'], r4['source_sha256']
    ck('cross-round sources differ only in round-specific exporter files',
       set(a)-set(b) == {'verification/parts/p0/Round3Audit.lean', 'verification/parts/p0/check_round3_types.py'}
       and set(b)-set(a) == {'verification/parts/p0/Round4Audit.lean', 'verification/parts/p0/check_round4_types.py'}
       and all(a[k] == b[k] for k in set(a) & set(b)))
    objects = r4['production_olean_parts']
    ck('exactly the three affected accepted modules lack new object capture', set(accepted) - set(objects) == THREE)
    ck('all freshly exported 612 declarations have captured objects', (set(expected[3]) | set(expected[4])) <= set(objects))
    inherited = json.loads(fixed(LEDGER + '/INHERITED_TYPES_591.json'))
    original_types = {r['name']: r for r in inherited}
    merged = jread(ATTEMPT / 'COMPLETE_TYPES_1005.json')
    ck('final format census retains five default Buchstab types', len(merged) == len({r['name'] for r in merged}) == 1005
       and Counter(r['actual_type_format'] for r in merged) == {'PP_ALL_COMPLETE': 1000, 'DEFAULT_META_PPEXPR_COMPLETE': 5}
       and all(r['module'] == 'ImbalancedChen.CurrentChenBuchstabRefinement' for r in merged if r['actual_type_format'] == 'DEFAULT_META_PPEXPR_COMPLETE'))
    old_records = [r for r in merged if r['provenance']['kind'] == 'REUSED_OLD393_COMPLETE_COMPILER_RECORD_WITH_CURRENT_ROOT_REPLAY']
    ck('393 old type records retain actual old types/provenance', len(old_records) == 393
       and all(r['type'] == original_types[r['name']]['type']
               and r['inherited_provenance'] == original_types[r['name']]['provenance']
               and r['production_source_sha256'] == original_types[r['name']]['production_source_sha256']
               and r['provenance']['current_type_print_rerun'] is False for r in old_records))
    current = {r['name']: r for r in merged if r not in old_records}
    ck('all 612 fresh raw records preserved unchanged in merged types', len(current) == 612 and all(
       all(current[raw['name']][key] == value for key, value in raw.items()) for n in [3, 4] for raw in declarations[n]))
    three_rows = []
    for module in sorted(THREE):
        before, after = accepted[module], new_rows[module]
        records = [r for r in merged if r['module'] == module]
        ck('current null plus original supplier bindings retained ' + module,
           after['current_integration_production_olean_parts'] is None
           and after['current_integration_object_capture_status'] == 'NOT_IN_FIXED_EXPORTER_SNAPSHOT_SCOPE'
           and after['source'] == before['source'] and after['validation'] == before['validation']
           and after['compiled_object_sha256'] == before['compiled_object_sha256']
           and all(r['current_root_verification']['production_olean_parts'] is None
                   and r['current_root_verification']['object_capture_status'] == 'NOT_IN_FIXED_EXPORTER_SNAPSHOT_SCOPE'
                   and r['current_root_verification']['kernel_replay_marker'] == 'replaying ' + module for r in records))
        three_rows.append({'module': module, 'fixed_root_import_path': source_paths[module],
            'current_snapshot_object_parts': None, 'current_snapshot_source_present': before['repository_path'] in a,
            'retained_supplier_source_sha256': before['source']['sha256'],
            'retained_supplier_object_sha256': before['compiled_object_sha256'],
            'retained_complete_type_records': len(records), 'actual_root_replay_marker': 'replaying ' + module})
    sources_excluded = sorted(set(source_paths) - set(objects))
    write('ROOT_REACHABILITY_AND_NULL_SCOPE.json', {
        'fixed_source_sha': SHA, 'project_source_root_reachable_modules': len(source_paths),
        'root_import_paths_for_accepted_modules': {m: source_paths[m] for m in accepted},
        'captured_object_modules': len(objects), 'accepted_modules_with_captured_objects': 20,
        'all_project_reachable_modules_outside_exporter_object_scope': sources_excluded,
        'affected_accepted_modules': three_rows,
        'cross_export_sources': {'round3': 274, 'round4': 274, 'shared_equal': len(set(a)&set(b)),
            'only_round3': sorted(set(a)-set(b)), 'only_round4': sorted(set(b)-set(a))},
        'cross_export_object_maps_equal': True,
        'all_input_source_maps_equal_across_rounds': False,
        'full_dependency_object_hash_coverage': False,
    })
    review = {'schema': 'p0.consumer-import-scope-independent-review.v1',
        'status': 'NO_BLOCKING_GATE_OR_TRUTHFULNESS_DEFECT_FOUND_WITH_SCOPE_NOTES',
        'scope': 'STATIC_CONSUMER_DIFF_AND_ORIGINAL_ACTUAL_ARTIFACT_REVIEW_NOT_CONSUMER_RERUN',
        'source_sha': SHA, 'old_consumer_sha256': OLD_HASH, 'new_consumer_sha256': NEW_HASH,
        'patch_sha256': sha(PATCH.read_bytes()), 'actual_artifact_sha256': ZIP_HASH,
        'run_id': 38289734671, 'job_id': 114946653833, 'attempt': 1,
        'changed_methods': changed, 'protected_methods_unchanged': 26,
        'actual_required_gates': stage_rows, 'actual_exports': export_info,
        'root_replay_accepted_module_markers': 23, 'root_axiom_declarations': 5872,
        'object_capture_scope': {'captured_modules': 267, 'project_reachable_modules': 276,
            'captured_accepted_modules': 20, 'uncaptured_accepted_modules': sorted(THREE)},
        'scope_notes': [
            'Root membership is transitive. The old direct-import requirement for all 23 historical accepted modules was not a project proof gate. All four new modules still require root direct imports and the fixed explicit lake build target command.',
            'The three null fields correctly state no newly captured object hash; all original supplier source/object/validation fields and inherited compiler provenance remain present. Root replay markers do not carry per-module hashes.',
            '267 modules are the fixed exporter seed-plus-direct-import object scope, not the full 276-module project source closure or all external dependencies. The three named modules are only the missing subset among the 23 accepted components.',
            'SOURCE_OBJECT_BINDINGS equality_checked_within_and_between_exports must be read with scope: each full input snapshot is equal before/after its own export; only object maps are equal across exports. The two 274-source maps have 272 shared-equal files and different round-specific audit/script paths.',
            'The concise RECEIPT.md does not explicitly list the three uncaptured historical modules; release prose should include the 20-of-23 current-object snapshot boundary already explicit in the JSON outputs.',
            'The final bridge still requires hLower/hUpper; the consumer success does not close K/c analytic suppliers or the final theorem.',
        ],
        'consumer_scripts_executed': False, 'lean_or_ci_executed': False,
        'network_access': False, 'existing_files_modified': False,
        'assertion_count': len(checks)}
    write('REVIEW_RECEIPT.json', review)
    write('REVIEW_CHECKS.json', {'status': 'PASS_INDEPENDENT_SCOPE_REVIEW', 'script_sha256': sha(Path(__file__).read_bytes()),
        'scope': review['scope'], 'assertion_count': len(checks), 'checks': checks})
    print(json.dumps({'status': review['status'], 'checks': len(checks),
        'changed_methods': changed, 'artifact_sha256': ZIP_HASH,
        'uncaptured_project_modules': len(sources_excluded), 'uncaptured_accepted_modules': len(THREE)}))


if __name__ == '__main__':
    main()
