"""Materialize only the independently reviewed, undeployed Y18 Git proposal."""
import json
from publication_util import ROOT, read, write, identity, git

base = ROOT / 'output/resume-20261112'
allow = base / 't16-empty-review/y18-driver-binding/ALLOWLIST.json'
assert identity(read(allow))['sha256'] == '7a98e5c64aa0caf9af5a6ce964866558a5f1a096ea14ad09b7bdb8d9be37a1a7'
a = json.loads(read(allow))
out = base / 'y18-open-driver-publication'
assert not (out / 'PREPARED.json').exists(), 'Frozen proposal already exists; do not recreate.'
assert a['required_parent'] == '356c3782e9428098a2fcbfb18c689bef264d84fa'
assert a['branch'] == 'ci/y18-empty-mother-20261112'
assert a['selected_proposal_deployment_authorized'] is False
assert git('rev-parse', a['required_parent'] + '^{tree}').decode().strip() == a['base_tree']
rows = []
for x in a['proposal_changed_paths']:
    source = ROOT / x['local_frozen_input']
    data = read(source)
    ident = identity(data)
    assert ident == {'bytes': x['bytes'], 'sha256': x['sha256'], 'git_blob': x['git_blob_sha1']}, x['path']
    assert x['mode'] == '100644'
    write(out / 'payload' / x['path'], data)
    rows.append({'path': x['path'], 'source': str(source), **ident})
assert len(rows) == len({r['path'] for r in rows}) == 49
external = next(r for r in rows if r['path'] == 'verification/parts/p0/Y18_EMPTY_MOTHER_DRIVER_SELECTION.json')
selection = json.loads(read(external['source']))
assert selection['deployment_authorized'] is False
git('read-tree', a['required_parent'])
for start in range(0, len(rows), 20):
    chunk = rows[start:start+20]
    assert git('hash-object', '-w', '--no-filters', '--', *[str(out / 'payload' / r['path']) for r in chunk]).decode().splitlines() == [r['git_blob'] for r in chunk]
git('update-index', '--index-info', data=''.join('100644 ' + r['git_blob'] + '\t' + r['path'] + '\n' for r in rows).encode())
tree = git('write-tree').decode().strip()
commit = git('commit-tree', tree, '-p', a['required_parent'], data=b'ci: materialize reviewed Y18 OPEN driver proposal; do not deploy\n').decode().strip()
changes = git('diff-tree', '--no-commit-id', '--name-status', '-r', commit).decode().splitlines()
assert len(changes) == 49
assert {x[2:] for x in changes} == {r['path'] for r in rows}
assert [x for x in changes if x.startswith('M\t')] == ['M\t.github/workflows/variable-envelope.yml']
assert all(x.startswith(('M\t', 'A\t')) for x in changes)
workflows = a['actual_workflows_expected']
assert set(git('ls-tree', '-r', '--name-only', commit, '--', '.github/workflows').decode().splitlines()) == {r['path'] for r in workflows}
for r in workflows:
    b = git('show', commit + ':' + r['path'])
    assert identity(b) == {'bytes': r['bytes'], 'sha256': r['sha256'], 'git_blob': r['git_blob_sha1']}, r['path']
git('update-ref', 'refs/heads/y18-open-driver-20261112', commit)
record = {'status': 'PREPARED_NOT_PUSHED_ROOT_DECISION_OPEN', 'commit': commit, 'tree': tree,
    'parent': a['required_parent'], 'branch': a['branch'], 'files': 49,
    'lean': sum(r['path'].endswith('.lean') for r in rows), 'bytes': sum(r['bytes'] for r in rows),
    'deployment_authorized': False, 'root_decision': None, 'local_proof_execution': False,
    'new_ci_dispatched': False, 'default_branch_modified': False,
    'review_allowlist_sha256': identity(read(allow))['sha256'], 'rows': rows,
    'actual_workflows_expected': workflows,
    'shared_concurrency_group': 'goldbach-p0-heavy', 'cancel_in_progress': False}
write(out / 'PREPARED.json', (json.dumps(record, ensure_ascii=False, indent=2) + '\n').encode())
print(json.dumps({k:v for k,v in record.items() if k not in ['rows','actual_workflows_expected']}, indent=2))
