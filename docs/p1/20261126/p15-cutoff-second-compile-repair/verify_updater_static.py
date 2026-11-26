#!/usr/bin/env python3
"""Only inspect local source/Git/AST and exercise the pure exact-splice reader.

This never imports or calls a driver, updater main, API, archive, installer,
preflight, Lean, kernel, cloud connector, or subprocess other than git show.
"""
import ast
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
REPO = Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')
F = '080d4178711ae042235104f7f4768649f51da2ab'
H = 'f6fdd7fffe17803c60914bf28b39b55715d34464'
I = 'f21a8601d99ea33ec572223f5267415ca4ead8db'
J = '7c59a3d125d99010a501c14f1ecc60710483f918'
PREFIX = 'docs/p1/20261126/p15-cutoff-second-compile-repair/'
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
HB = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
SUPPORT = 'ImbalancedChen.P1OriginalSingletonSupportData'
checks = []

def check(value, label):
    if not value:
        raise AssertionError(label)
    checks.append(label)

def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}

def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)

def functions(raw):
    text = raw.decode()
    return {node.name: (node, ast.get_source_segment(text, node))
            for node in ast.parse(text).body if isinstance(node, ast.FunctionDef)}

def closure(graph, roots):
    result = set()
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module not in result:
            result.add(module)
            stack.extend(graph[module])
    return result

raw = (HERE / 'apply_source_repair.py').read_bytes()
base_raw = git(I, 'docs/p1/20261126/p15-cutoff-first-compile-repair/apply_source_repair.py')
manifest_raw = (HERE / 'REPAIR_MANIFEST.json').read_bytes()
m = json.loads(manifest_raw)
tree = ast.parse(raw)
func = functions(raw)
base = functions(base_raw)
constants = {}
for node in tree.body:
    if isinstance(node, ast.Assign):
        try:
            value = ast.literal_eval(node.value)
        except (TypeError, ValueError):
            continue
        for target in node.targets:
            if isinstance(target, ast.Name):
                constants[target.id] = value
check(constants['MANIFEST_SHA'] == fp(manifest_raw)['sha256'] and
      constants['SOURCE_ANCHOR'] == m['source_anchor_commit'] == J and
      constants['FAILED'] == m['failed_source_commit'] == I and constants['HB_SOURCE'] == F,
      'actual script/manifest/J/failed-I/accepted-F pins match')
check(base_raw == git(I, m['original_updater']['path']) and fp(base_raw) ==
      {k: m['original_updater'][k] for k in ('bytes', 'sha256')}, 'published I updater base exact')
unchanged = ['require', 'sha', 'git_file', 'check_bytes', 'payloads', 'source_watch',
             'support_evidence_files', 'original_support', 'unchanged_support',
             'prior_archive', 'fsync_directory', 'archive_binding', 'preserve_failed_setup', 'unchanged_hb']
for name in unchanged:
    check(func[name][1] == base[name][1], 'original I updater function bytes: ' + name)
for binding in m['historical_I_inputs'] + m['unchanged_shared_inputs']:
    check(binding['commit'] == I and fp(git(I, binding['path'])) ==
          {k: binding[k] for k in ('bytes', 'sha256')}, 'original I input pin: ' + binding['path'])
for binding in m['historical_F_HB_inputs']:
    check(binding['commit'] == F and fp(git(F, binding['path'])) ==
          {k: binding[k] for k in ('bytes', 'sha256')}, 'original F HB input pin: ' + binding['path'])
for binding in m['unchanged_shared_inputs']:
    check(git(I, binding['path']) == git(J, binding['path']), 'shared I/J input bytes: ' + binding['path'])
for binding in (m['actual_bounded_metadata'], m['candidate_provenance']):
    check(binding['commit'] == J and fp(git(J, binding['path'])) ==
          {k: binding[k] for k in ('bytes', 'sha256')}, 'published J evidence pin: ' + binding['path'])
binding = m['accepted_HB']['public_summary']
check(binding['commit'] == H and fp(git(H, binding['path'])) ==
      {k: binding[k] for k in ('bytes', 'sha256')}, 'original H public pin for accepted HB@F')
# Directly run only the real pure payload reader, with local read-only Git.
namespace = {'hashlib': hashlib, 'require': None, 'git_file': git,
             'FAILED': I, 'TARGET': CUTOFF, 'PUBLISHED_REPAIRS': [CUTOFF],
             'BEFORE_SHA': constants['BEFORE_SHA'], 'AFTER_SHA': constants['AFTER_SHA']}
selected = [func[name][0] for name in ('require', 'sha', 'check_bytes', 'payloads')]
exec(compile(ast.Module(body=selected, type_ignores=[]), '<pure-payload-static>', 'exec'), namespace)
before, after = namespace['payloads'](J, m)
check(fp(after[CUTOFF]) == {'bytes': 12744, 'sha256': constants['AFTER_SHA']} and
      before[CUTOFF] != after[CUTOFF], 'real single-splice forward reconstruction equals J')
check(after[CUTOFF] == (REPO / (CUTOFF.replace('.', '/') + '.lean')).read_bytes(),
      'frozen local canonical source equals J')
for kind in ('pre_start_byte', 'old_utf8', 'new_utf8'):
    bad = copy.deepcopy(m)
    splice = bad['repairs'][0]['exact_byte_splices'][0]
    splice[kind] = splice[kind] + (1 if kind == 'pre_start_byte' else 'x')
    try:
        namespace['payloads'](J, bad)
    except ValueError:
        checks.append('exact reader rejects corrupted ' + kind)
    else:
        raise AssertionError('corrupted splice accepted: ' + kind)
imanifest = json.loads(git(I, 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'))
rows = imanifest['project_sources']
graph = {module: row['imports'] for module, row in rows.items()}
changed = []
for module, row in rows.items():
    old, current = git(I, row['path']), git(J, row['path'])
    check(fp(old) == {k: row[k] for k in ('bytes', 'sha256')}, 'I source pin: ' + module)
    check(current == (after[module] if module in after else old), 'J exact source delta: ' + module)
    if current != old:
        changed.append(module)
    literal_imports = [token for line in current.decode().splitlines() if line.startswith('import ')
                       for token in line[len('import '):].split()]
    check(literal_imports == row['all_imports'], 'unchanged source imports: ' + module)
hb, cutoff, support = (closure(graph, [module]) for module in (HB, CUTOFF, SUPPORT))
watch = cutoff | support | set(imanifest['targets'])
check(len(rows) == 360 and changed == [CUTOFF], 'one changed J source and 359 unchanged sources')
check(len(hb) == 67 and len(cutoff) == 68 and cutoff == hb | {CUTOFF} and
      len(support) == 109 and len(cutoff | support) == 130 and len(watch) == 148,
      'actual I closure cardinalities 67/68/109/130/148')
check(CUTOFF not in support and all(CUTOFF not in closure(graph, [module])
      for module in imanifest['accepted_suppliers']), 'repair outside all accepted supplier and Support closures')
md = json.loads(git(J, m['actual_bounded_metadata']['path']))
public = json.loads(git(H, m['accepted_HB']['public_summary']['path']))
check(md['failed_evidence'] == m['failed_evidence'] and len(md['failed_evidence']) == 18,
      'actual eighteen failure evidence pins')
check(len(md['artifacts']) == 21 and [p for p, value in md['artifacts'].items() if value is not None] ==
      [constants['SETUP']] and md['artifacts'][constants['SETUP']] == constants['SETUP_FP'],
      'actual sole failed Cutoff setup and twenty absent artifact slots')
check(md['accepted_companion_artifacts'] == m['accepted_HB']['all_observed_target_artifacts'] and
      len(md['accepted_companion_artifacts']) == 21 and
      public['owners'][HB]['receipt_bindings'] == m['accepted_HB']['receipt_bindings'] and
      len(m['accepted_HB']['receipt_bindings']) == 6 and
      public['owners'][HB]['owned_count'] == public['owners'][HB]['public_count'] == 7,
      'actual HB twenty-one artifacts and six receipts, seven owned/public')
check(md['normal_pass_present'] is False and md['accepted_companion_normal_pass_present'] is True and
      public['original_group_all_selected_owners_accepted'] is False and
      public['original_group_accepted_owners'] == [HB] and
      public['original_group_failed_modules'] == [CUTOFF] and
      md['source_commit'] == I and md['accepted_companion_original_source_commit'] == F and
      md['failure_summary']['accepted_owners'] == [] and md['failure_summary']['failed_modules'] == [CUTOFF],
      'real I failure and separate original F partial success preserved')
body = func['apply_repair'][1]
check(body.index('preserve_failed_setup(') < body.index('driver.preflight(s, FAILED, [TARGET])') <
      body.index('s.h.install_sources('), 'original full I fresh gate after archive and before source write')
preflights = [ast.unparse(node) for node in ast.walk(tree) if isinstance(node, ast.Call) and
              isinstance(node.func, ast.Attribute) and node.func.attr == 'preflight']
check(preflights == ['driver.preflight(s, FAILED, [TARGET])'] and
      'driver.retained_hb_f_target(s, spec, ACCEPTED)' in func['original_I_readonly_context'][1] and
      'driver.retained_owner(s, spec, module, validate_live=True)' in func['original_I_readonly_context'][1] and
      'driver.fixed_dependency_pins(s, spec, module)' in func['original_I_readonly_context'][1],
      'only full I Cutoff preflight; HB uses original F adapter plus full original supplier prefix')
check('driver.require_fresh_owner(ACCEPTED' not in raw.decode() and
      'set(fresh.initial_owners) == {TARGET}' in body and
      "fresh.supplier_evidence[ACCEPTED]['source_commit'] == HB_SOURCE" in body,
      'HB never selected/fresh or fabricated as an I accepted owner')
check('hb_spec.sources = dict(spec.sources)' in func['original_I_readonly_context'][1] and
      'hb_spec.retained_inputs = dict(spec.retained_inputs)' in func['original_I_readonly_context'][1] and
      'copy.deepcopy(spec.dependency_pins[m])' in func['original_I_readonly_context'][1],
      'HB preservation view does not alias repaired source/evidence state')
check('driver.acceptance_binding(s, HB_SOURCE, ACCEPTED) == binding' in func['bind_hb_evidence'][1] and
      "binding['all_observed_target_artifacts'] == fixed['all_observed_target_artifacts']" in func['bind_hb_evidence'][1] and
      'driver.module_artifacts(s, ACCEPTED) == state.artifacts[ACCEPTED]' in func['unchanged_hb'][1],
      'HB original F result to initial full21 and final full21 preservation connection')
check("run = OLD_ROOT / HB_SOURCE / 'runs/attempt-00000'" in func['bind_hb_evidence'][1] and
      'driver.require_hb_f_run_scope(public, original, worker)' in func['bind_hb_evidence'][1] and
      "record['accepted_owners'] == []" in func['bind_failed_evidence'][1] and
      "record['acceptance_bindings'] == {}" in func['bind_failed_evidence'][1],
      'I failed current RESULT and F accepted historical RESULT/WORKER bound separately')
forbidden_calls = {'normal_one', 'audit', 'run_owner', 'worker', 'direct_import_readiness', 'dependency_readiness'}
called = {node.func.attr for node in ast.walk(tree) if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)}
check(not called.intersection(forbidden_calls), 'no normal/kernel/build/owner execution call')
mutation_calls = [(node.func.attr, node.lineno) for node in ast.walk(tree) if isinstance(node, ast.Call)
                  and isinstance(node.func, ast.Attribute) and node.func.attr in {'unlink', 'install_sources'}]
check([name for name, _ in mutation_calls].count('unlink') == 1 and
      [name for name, _ in mutation_calls].count('install_sources') == 1,
      'one reviewed exact setup unlink and one immutable source installer call')
check("s.h.serialize(0, run / 'SOURCE_REPAIR_LANE.json'" in func['main'][1] and
      's.d.verify_lane(s.h)' in body and
      "s.h.guard(0, ['lake', 'build', '+' + TARGET + ':olean'])" in func['bind_failed_evidence'][1],
      'original lane zero serializer/verification and diagnostic command guard')
candidate = m['candidate_provenance']
check((REPO / candidate['path']).read_bytes() == git(J, candidate['path']), 'J candidate record untouched')
receipt = {'schema': 'p15_single_cutoff_updater_local_static_verification_v1',
           'status': 'PASS', 'updater': fp(raw), 'manifest': fp(manifest_raw),
           'source_anchor_commit': J, 'historical_failed_source_commit': I, 'accepted_HB_source_commit': F,
           'checks_passed': len(checks),
           'source_scope_checks': {'exact_I_source_pins': 360, 'exact_J_source_delta': 360,
                                   'unchanged_literal_imports': 360},
           'other_checks': [label for label in checks if not label.startswith(
               ('I source pin: ', 'J exact source delta: ', 'unchanged source imports: '))],
           'fixed_inputs': {'I_source_modules': 360, 'J_source_delta_modules': changed,
                            'unchanged_sources': 359, 'Cutoff_source_closure': 68,
                            'HB_source_closure': 67, 'Cutoff_preserved_dependencies': 67,
                            'Support_source_closure': 109, 'watched_modules': 148},
           'pure_exact_splice_negative_cases': 3,
           'original_archive_algorithm': 'EXACT_PUBLISHED_I_UPDATER_BYTES',
           'driver_or_updater_entrypoint_executed': False, 'cloud_calls': 0,
           'Lean_or_kernel_commands': 0, 'source_or_cache_mutations': 0,
           'future_K_publication_not_yet_available': True,
           'live_runtime_validation': 'DEFERRED_TO_ORIGINAL_PINNED_READERS_AT_AUTHORIZED_APPLY',
           'new_Lean_acceptance': False}
(HERE / 'STATIC_VERIFICATION.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({key: receipt[key] for key in ('status', 'checks_passed', 'updater', 'manifest', 'fixed_inputs')}))
