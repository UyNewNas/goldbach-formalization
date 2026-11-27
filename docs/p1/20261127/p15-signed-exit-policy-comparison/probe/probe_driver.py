"""UNBOUND draft: probe the original PolicyComparison source only.

This template is not a formal acceptance adapter.  It must remain UNBOUND until
the real Partition formal PASS and independent readonly JSON are downloaded,
reviewed and pinned.  PARTITION_BINDING requires exactly two rows, formal_pass
and readonly_receipt, each containing its real absolute path, bytes and sha256.
The readonly receipt must contain the unwrapped return value of the original
Partition check API.  No owned/public count is supplied by this template.

The original Partition adapter checks its own acceptance.  Its forty old
dependencies, Dictionary, Variation, runtime and Git protections are reused.
This probe only elaborates PolicyComparison, with no object output or build.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
PARTITION_BINDING = {'formal_pass': {'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/7296a9659fbf34773ec03f437860c14073b3a638/signed-exit-partition-operation/PASS.json',
                 'bytes': 6154,
                 'sha256': '423497a297bd3f9eb74decf2322d4a7f9701f23f78c4bab68c60410a07b9a979'},
 'readonly_receipt': {'path': '/workspace/p1-complete-proof/20261127-p15-partition-readonly-v1/7296a9659fbf34773ec03f437860c14073b3a638/attempt-00000/READONLY_RESULT.json',
                      'bytes': 4222,
                      'sha256': 'a7433f2da6075d06f26af89fe6cb2e80b91fe7aa2b619153e93d1dd59a3c0be2'}}
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ACCEPTANCE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PARTITION_COMMIT = '7296a9659fbf34773ec03f437860c14073b3a638'
PARTITION = 'ImbalancedChen.P1SignedExitPartition'
PARTITION_SOURCE_SHA = '19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c'
PARTITION_ADAPTER = ACCEPTANCE_ROOT / PARTITION_COMMIT / 'published-entrypoints/run_partition.py'
PARTITION_ADAPTER_PIN = {'bytes': 31065, 'sha256': '208fca4558eca8021837b3a2ca992eb6c071a4c9c33893f98a9f93a183582c57'}
SOURCE_COMMIT = '040d46058821746c69c5183b3f6c22792287c4ba'
TARGET = 'ImbalancedChen.P1SignedExitPolicyComparison'
NAME = 'P1SignedExitPolicyComparison.lean'
SOURCE_PATH = 'ImbalancedChen/' + NAME
SOURCE_PIN = {'bytes': 17805, 'sha256': 'c60992855b519d9767e66f31c9007dd18f2292e326e28539fc2a39d1d831b57f'}
IMPORTS = [PARTITION]
RUN = (Path('/workspace/p1-complete-proof/20261127-p15-signed-exit-policy-probe-v1') /
       SOURCE_PIN['sha256'] / 'attempt-00000')


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def validate_binding():
    # Must precede any project filesystem, Git, helper, lane or compiler call.
    need(isinstance(PARTITION_BINDING, dict),
         'UNBOUND: real Partition formal PASS and independent readonly receipt required')
    need(set(PARTITION_BINDING) == {'formal_pass', 'readonly_receipt'},
         'only complete real Partition formal/readonly bindings are permitted')
    for name, row in PARTITION_BINDING.items():
        need(isinstance(row, dict) and set(row) == {'path', 'bytes', 'sha256'} and
             isinstance(row['path'], str) and Path(row['path']).is_absolute() and
             type(row['bytes']) is int and row['bytes'] > 0 and
             isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']),
             'incomplete actual parent receipt binding: ' + name)


def regular(path):
    need(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return path.read_bytes()


def receipt(row):
    path = Path(row['path'])
    need(path.resolve() == path, 'unexpected receipt route')
    raw = regular(path)
    need(fingerprint(raw) == {k: row[k] for k in ('bytes', 'sha256')},
         'original Partition receipt changed: ' + str(path))
    return json.loads(raw)


def load():
    validate_binding()
    raw = regular(PARTITION_ADAPTER)
    need(fingerprint(raw) == PARTITION_ADAPTER_PIN, 'published Partition adapter differs')
    parent = ModuleType('original_partition_acceptance')
    parent.__file__ = str(PARTITION_ADAPTER)
    exec(compile(raw, str(PARTITION_ADAPTER), 'exec'), parent.__dict__)
    need((parent.REPO, parent.PROJECT, parent.ROOT, parent.TARGET) ==
         (REPO, PROJECT, ACCEPTANCE_ROOT, PARTITION), 'parent fixed environment differs')
    c = parent.load(PARTITION_COMMIT)
    readonly = parent.check(c)
    need(readonly['status'] == 'REVALIDATED' and
         readonly['normal_or_kernel_commands_executed'] == 0 and
         readonly['identity'] == c.ident and c.ident['module'] == PARTITION and
         c.ident['commit'] == PARTITION_COMMIT and
         c.ident['new_source_sha256'] == PARTITION_SOURCE_SHA,
         'Partition is not the actual complete original acceptance')
    need(Path(PARTITION_BINDING['formal_pass']['path']) == c.run / 'PASS.json' and
         receipt(PARTITION_BINDING['formal_pass'])['identity'] == c.ident and
         receipt(PARTITION_BINDING['readonly_receipt']) == readonly,
         'formal/independent readonly identities do not match original Partition')
    source = parent.git(SOURCE_COMMIT, SOURCE_PATH)
    need(fingerprint(source) == SOURCE_PIN and c.s.h.imports(source) == IMPORTS,
         'original complete PolicyComparison source/import bytes differ')
    graph, sources = c.s.h.project_graph(PROJECT, IMPORTS)
    need(graph == c.spec.graph and
         {m: row['sha256'] for m, row in sources.items()} == c.spec.sources and
         len(graph) == 41 and TARGET not in graph and
         c.s.h.closure(graph, IMPORTS) == set(graph),
         'PolicyComparison inputs are not exactly original forty plus accepted Partition')
    need(c.spec.sources[PARTITION] == PARTITION_SOURCE_SHA and
         fingerprint(regular(PROJECT / c.s.h.module_path(PARTITION))) ==
         fingerprint(c.new), 'accepted Partition source changed')
    return SimpleNamespace(parent=parent, c=c, source=source, readonly=readonly)


def fresh(x):
    c = x.c
    roots = [p / TARGET for p in ACCEPTANCE_ROOT.iterdir()
             if p.is_dir() and re.fullmatch('[0-9a-f]{40}', p.name) and os.path.lexists(p / TARGET)]
    need(not roots, 'prior/partial PolicyComparison owner found; preserve and inspect without rerun')
    artifacts = c.g.module_artifacts(c.s, TARGET)
    c.g.require_fresh_owner(TARGET, artifacts)
    path = PROJECT / SOURCE_PATH
    source = regular(path) if os.path.lexists(path) else None
    need(source is None or source == x.source, 'foreign installed PolicyComparison source')
    stem = PROJECT / '.lake/build/lib/lean' / TARGET.replace('.', '/')
    need(all(not os.path.lexists(Path(str(stem) + ext)) for ext in ('.trace.nobuild', '.ir.sig.hash')),
         'partial extra PolicyComparison artifact')
    return {'source': None if source is None else fingerprint(source), 'artifacts': artifacts}


def fixed(x):
    c = x.c
    parent_owner = x.parent.accepted(c)
    need(c.g.module_artifacts(c.s, PARTITION) == parent_owner['binding']['all_observed_target_artifacts'],
         'accepted Partition artifact inputs differ')
    need(c.g.file_binding(PROJECT / c.s.h.module_path(PARTITION)) == PARTITION_SOURCE_SHA,
         'accepted Partition source input differs')
    stem = PROJECT / '.lake/build/lib/lean' / PARTITION.replace('.', '/')
    return {'original_inputs': x.parent.fixed(c), 'original_partition_owner': parent_owner,
            'partition_extra_metadata': {ext: c.support.metadata(Path(str(stem) + ext))
                                         for ext in ('.trace.nobuild', '.ir.sig.hash')},
            'parent_receipts': {k: receipt(v) for k, v in PARTITION_BINDING.items()},
            'new_target': fresh(x)}


def worker(x):
    c = x.c
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__) == RUN / 'probe_driver.py' and RUN.resolve() == RUN, 'unexpected worker route')
    need(c.s.api.read_json(RUN / 'GIT_BEFORE.json') == c.s.d.original_git_state(REPO),
         'checkout changed before probe worker')
    need(regular(RUN / NAME) == x.source, 'frozen original PolicyComparison source differs')
    before = fixed(x)
    c.s.d.save(RUN / 'PRESERVED_BEFORE.json', before)
    result = {'schema': 'p15_policy_comparison_no_output_probe_v1', 'target': TARGET,
              'source_commit': SOURCE_COMMIT, 'source_path': SOURCE_PATH, 'source': SOURCE_PIN,
              'original_source_unchanged': True, 'partition_original_identity': x.readonly,
              'partition_original_receipt_bindings': PARTITION_BINDING,
              'project_dependency_count': len(c.spec.graph), 'direct_imports': IMPORTS,
              'direct_import_readiness': None, 'command': None, 'exit_code': 3,
              'probe_passed': False, 'preservation_passed': False,
              'output_object_requested': False, 'new_owner_accepted': False,
              'new_formal_credit': 0, 'whole_P1_5_complete': False}
    try:
        ready = SimpleNamespace(manifest={'project_sources': {TARGET: {'all_imports': IMPORTS}}})
        result['direct_import_readiness'] = c.g.direct_import_readiness(c.s, ready, TARGET, RUN)
        need(fixed(x) == before, 'no-build readiness changed protected inputs')
        cmd = c.s.ops.run(RUN, 'probe',
            c.s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(RUN / NAME)]),
            cwd=PROJECT, relay=True)
        result['command'] = cmd
        need(not cmd['actual_built_modules'] and not cmd['actual_failed_modules'],
             'probe attempted a build')
        result['exit_code'] = cmd['exit_code']
    except Exception as error:
        result['probe_error'] = str(error)
    finally:
        try:
            after = fixed(x)
            c.s.d.save(RUN / 'PRESERVED_AFTER.json', after)
            need(before == after, 'probe changed original dependencies, owners or receipts')
            need(all(not list(RUN.glob(pattern)) for pattern in
                     ('*.olean*', '*.ilean*', '*.c', '*.o', '*.bc', '*.ir', '*.trace*')),
                 'no-output probe produced an object')
            result['preservation_passed'] = True
        except Exception as error:
            result['preservation_error'] = str(error)
    result['probe_passed'] = (result['exit_code'] == 0 and result['preservation_passed'] and
                              not result.get('probe_error') and not result.get('preservation_error'))
    if not result['probe_passed'] and result['exit_code'] == 0:
        result['exit_code'] = 3
    c.s.d.save(RUN / 'PROBE_RESULT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)
    return result['exit_code']


def relay_original_log_tail():
    # Preserve the complete original log and its hash; print a bounded view.
    for name in ('probe.log', 'serialized-probe.log'):
        path = RUN / name
        if os.path.lexists(path):
            tail = regular(path).decode('utf-8', errors='replace')[-24000:]
            print('ORIGINAL_LOG_TAIL_BEGIN ' + name, flush=True)
            print(tail, end='' if tail.endswith('\n') else '\n', flush=True)
            print('ORIGINAL_LOG_TAIL_END ' + name, flush=True)
            return


def main():
    validate_binding()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker', action='store_true')
    args = parser.parse_args()
    x = load()
    if args.worker:
        return worker(x)
    fresh(x)
    need(RUN.resolve() == RUN, 'unexpected new probe route')
    RUN.mkdir(parents=True, exist_ok=False)
    x.c.s.d.write_frozen(RUN / 'probe_driver.py', regular(Path(__file__)))
    x.c.s.d.write_frozen(RUN / NAME, x.source)
    before = x.c.s.d.original_git_state(REPO)
    x.c.s.d.save(RUN / 'GIT_BEFORE.json', before)
    try:
        outer = x.c.s.ops.run(RUN, 'serialized-probe',
            x.c.s.h.serialize(0, RUN / 'LANE.json',
                ['python3', '-B', str(RUN / 'probe_driver.py'), '--worker']),
            cwd=PROJECT, relay=True)
    finally:
        after = x.c.s.d.original_git_state(REPO)
        x.c.s.d.save(RUN / 'GIT_AFTER.json', after)
        relay_original_log_tail()
        need(before == after, 'original Git state changed')
    result = x.c.s.api.read_json(RUN / 'PROBE_RESULT.json')
    need(not outer['actual_built_modules'] and not outer['actual_failed_modules'] and
         result['exit_code'] == outer['exit_code'], 'outer probe scope/status differs')
    print(json.dumps({'target': TARGET, 'exit_code': outer['exit_code'],
                      'probe_passed': result['probe_passed'], 'result': fingerprint(regular(RUN / 'PROBE_RESULT.json')),
                      'new_formal_credit': 0, 'whole_P1_5_complete': False}, sort_keys=True), flush=True)
    return outer['exit_code']


if __name__ == '__main__':
    raise SystemExit(main())
