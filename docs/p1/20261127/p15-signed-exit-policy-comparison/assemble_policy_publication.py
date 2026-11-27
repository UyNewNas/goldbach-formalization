"""Bind actual probe inputs only and assemble local Policy source publication."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import pprint

HERE = Path(__file__).resolve().parent
UNBOUND = HERE / 'formal-unbound'
OUT = HERE / 'formal-publication'
PUBLICATION = OUT / 'publication'
PACKET = 'docs/p1/20261127/p15-signed-exit-policy-comparison'
PARENT = '19f493948737f6f5f7bc5e858d5266b41f976b22'
NAME = 'P1SignedExitPolicyComparison.lean'
SOURCE_SHA = 'c60992855b519d9767e66f31c9007dd18f2292e326e28539fc2a39d1d831b57f'


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.is_file() and not path.is_symlink() and path.read_bytes() == data, path
    else:
        with path.open('xb') as stream:
            stream.write(data)


def main():
    runner = (UNBOUND / 'run_policy.py').read_bytes()
    assert fp(runner) == {'bytes': 23571, 'sha256': 'fda19f6f88e99a2f5077fe48cd40cdf98649d4eda04ff01b43796e5edb7a806e'}
    review_raw = (UNBOUND / 'INDEPENDENT_REVIEW.json').read_bytes()
    assert fp(review_raw) == {'bytes': 5019, 'sha256': '0acc0742981577fc53c5e307b0038722f6effa258d0a39ab94028b7b064c3fb9'}
    review = json.loads(review_raw)
    assert review['reviewed_adapter']['sha256'] == fp(runner)['sha256']
    assert not review['important_or_blocking_findings'] and review['adapter_inputs_bound'] is False
    inputs_raw = (UNBOUND / 'ACTUAL_PROBE_INPUTS.json').read_bytes()
    inputs = json.loads(inputs_raw)
    needle = b'INPUTS = None\n'
    replacement = ('INPUTS = ' + pprint.pformat(inputs, width=110, sort_dicts=False) + '\n').encode()
    assert runner.count(needle) == 1
    bound = runner.replace(needle, replacement, 1)
    assert bound.replace(replacement, needle, 1) == runner
    ast.parse(bound)
    scope = {'__name__': 'local_policy_actual_binding_check', '__file__': str(OUT / 'run_policy.py')}
    exec(compile(bound, str(OUT / 'run_policy.py'), 'exec'), scope)
    assert scope['INPUTS'] == inputs
    scope['validate_inputs']()
    source = (HERE.parent / 'reference' / NAME).read_bytes()
    assert fp(source) == {'bytes': 17805, 'sha256': SOURCE_SHA}
    scope['verify_source'](source)
    helper = (HERE / 'probe_policy_bound.py').read_bytes()
    assert fp(helper) == {'bytes': 12998, 'sha256': '1b0915e36b854e8f4e92c46e1bb9d9578013c8d74ace08331dc925c24af3e167'}
    raw_root = HERE / 'exact-probe-evidence/policy' / SOURCE_SHA / 'attempt-00000'
    exported = json.loads((HERE / 'EXACT_PROBE_FILES.json').read_bytes())
    raw_files = {}
    for row in exported:
        data = Path(row['local']).read_bytes()
        assert fp(data) == {k: row[k] for k in ('bytes', 'sha256')}
        rel = str(Path(row['local']).relative_to(raw_root))
        assert row['remote'] == inputs['probe']['directory'] + '/' + rel
        assert inputs['probe']['files'][rel] == fp(data)
        raw_files[rel] = data
    assert set(raw_files) == set(scope['PROBE_FILES']) and len(raw_files) == 17
    assert sum(len(raw) for raw in raw_files.values()) == 3085351
    assert raw_files[NAME] == source and raw_files['probe_driver.py'] == helper
    files = {}
    def add(repo_path, data):
        assert not repo_path.startswith('/') and '..' not in Path(repo_path).parts and repo_path not in files
        files[repo_path] = data
    add('ImbalancedChen/' + NAME, source)
    add(PACKET + '/' + NAME, source)
    add(PACKET + '/run_policy.py', bound)
    add(PACKET + '/support/probe_policy_v1.py', helper)
    add(PACKET + '/INPUTS.json', inputs_raw)
    add(PACKET + '/README.md', (HERE / 'POLICY_PUBLICATION_README_DRAFT.md').read_bytes())
    for name in ('POLICY_PUBLICATION_SCOPE_PINS.json', 'POLICY_ORIGINAL_INTERFACE.json', 'PARTITION_BINDING.json'):
        add(PACKET + '/' + name, (HERE / name).read_bytes())
    for name in ('run_policy.py', 'test_policy_boundaries.py', 'LOCAL_CHECKS.json', 'INDEPENDENT_REVIEW.json', 'README.md'):
        add(PACKET + '/reviewed-unbound/' + name, (UNBOUND / name).read_bytes())
    for rel, data in raw_files.items():
        add(PACKET + '/probe/' + rel, data)
    add(PACKET + '/probe/EXACT_PROBE_FILES.json', (HERE / 'EXACT_PROBE_FILES.json').read_bytes())
    for name in ('probe-task-output.log', 'probe-task-output.json', 'policy-probe-export-raw.json',
                 'stage_probe_policy.py', 'export_policy_probe.py', 'BOUND_PROBE_SUMMARY.json'):
        add(PACKET + '/transport/' + name, (HERE / name).read_bytes())
    diff = ''.join(difflib.unified_diff(runner.decode().splitlines(True), bound.decode().splitlines(True),
        fromfile='reviewed-unbound/run_policy.py', tofile='run_policy.py'))
    add(PACKET + '/BINDING_ONLY.diff', diff.encode())
    summary = {'schema': 'p15_policy_formal_source_publication_binding_v1',
        'status': 'ACTUAL_PROBE_INPUTS_BOUND_FORMAL_EXECUTION_PENDING', 'publication_parent': PARENT,
        'packet': PACKET, 'canonical_source': {'path': 'ImbalancedChen/' + NAME, **fp(source)},
        'canonical_source_byte_change': False, 'only_new_formal_owner': scope['TARGET'],
        'bound_adapter': fp(bound), 'reviewed_unbound_adapter': fp(runner),
        'only_inputs_assignment_changed': True, 'independent_review': fp(review_raw),
        'original_probe': {'job_id': inputs['probe']['job_id'], 'files': 17, 'bytes': 3085351,
                           'result': fp(raw_files['PROBE_RESULT.json'])},
        'frozen_probe_helper': fp(helper), 'actual_project_dependencies': 41, 'formal_graph_sources': 42,
        'partition_original_acceptance_commit': scope['PARTITION_COMMIT'],
        'new_formal_owned_count': None, 'new_formal_public_count': None,
        'new_formal_acceptance_executed': False, 'cloud_calls': 0, 'git_commands': 0,
        'lean_commands': 0, 'kernel_commands': 0, 'whole_P1_5_complete': False}
    summary_raw = (json.dumps(summary, indent=2, sort_keys=True) + '\n').encode()
    add(PACKET + '/BINDING_SUMMARY.json', summary_raw)
    add(PACKET + '/assemble_policy_publication.py', Path(__file__).read_bytes())
    assert [p for p in files if p.startswith('ImbalancedChen/')] == ['ImbalancedChen/' + NAME]
    index = []
    for repo_path, data in sorted(files.items()):
        local = PUBLICATION / repo_path
        put(local, data)
        assert local.read_bytes() == data
        index.append({'local': str(local), 'path': repo_path, **fp(data)})
    put(OUT / 'FILE_INDEX.json', (json.dumps(index, indent=2) + '\n').encode())
    put(OUT / 'BINDING_SUMMARY.json', summary_raw)
    put(OUT / 'run_policy.py', bound)
    put(OUT / 'BINDING_ONLY.diff', diff.encode())
    assert (UNBOUND / 'run_policy.py').read_bytes() == runner
    assert (HERE.parent / 'reference' / NAME).read_bytes() == source
    print(json.dumps({'parent': PARENT, 'files': len(index), 'bytes': sum(r['bytes'] for r in index),
        'index': {'path': str(OUT / 'FILE_INDEX.json'), **fp((OUT / 'FILE_INDEX.json').read_bytes())},
        'bound_adapter': {'path': str(OUT / 'run_policy.py'), **fp(bound)},
        'binding_summary': {'path': str(OUT / 'BINDING_SUMMARY.json'), **fp(summary_raw)}}, indent=2))


if __name__ == '__main__':
    main()
