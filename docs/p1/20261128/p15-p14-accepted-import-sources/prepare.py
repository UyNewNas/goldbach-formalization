from pathlib import Path
import json, hashlib, subprocess, re, datetime
ROOT = Path(__file__).resolve().parent
RAW = Path('/workspace/p1-complete-proof/20261128-p14-archive-common-raw-mean')
P15 = Path('/workspace/p15-continue-20261127')
P14 = Path('/workspace/p14-continue-20261128')
MEMBER = Path('/workspace/blue-member-build')
BASE = '696e0ff40f883ef98cc824ecedfc148d6bb4c8e0'
P14HEAD = '92bee4656bc732902baf5a3944af545b0188256c'

def fp(p):
    p = Path(p)
    with p.open('rb') as f:
        h = hashlib.file_digest(f, 'sha256').hexdigest()
    return dict(path=str(p), bytes=p.stat().st_size, sha256=h)

def check(x):
    assert fp(x['path']) == x, x['path']

def git_sha(repo, commit, module):
    return hashlib.sha256(subprocess.check_output(['git', '-C', str(repo), 'show',
        commit + ':' + module.replace('.', '/') + '.lean'])).hexdigest()

assert subprocess.check_output(['git', '-C', str(P15), 'rev-parse', 'HEAD'], text=True).strip() == BASE
assert not subprocess.check_output(['git', '-C', str(P15), 'status', '--porcelain'], text=True)
contexts = json.loads((RAW / 'REUSED_CONTEXTS.json').read_text())
res = json.loads((RAW / 'formal-00001/VALIDATION_RESULTS.json').read_text())
contexts.append(dict(root=str(RAW), receipt=str(RAW / 'formal-00001/VALIDATION_RESULTS.json'),
    module=res['module'], source=res['source']))
group = {x['module'] for x in contexts}
inputs = {}
records = []
direct = set()
for context in contexts:
    receipt = Path(context['receipt'])
    result = json.loads(receipt.read_text())
    mod = result['module']
    assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED', mod
    assert result['source'] == context['source'], mod
    check(result['source'])
    assert git_sha(P14, P14HEAD, mod) == result['source']['sha256'], mod
    for stage in ['normal', 'kernel', 'audit']:
        assert result[stage]['exit_code'] == 0, mod
        check(result[stage]['log'])
    objects = json.loads((receipt.parent / 'OUTPUTS_AFTER_NORMAL.json').read_text())
    for x in objects:
        check(x)
    coupled_path = receipt.parent / 'COUPLED_IMPORT_VALIDATION.json'
    coupled = json.loads(coupled_path.read_text())
    assert coupled['status'] == 'PASS' and coupled['accepted_import_normal_or_kernel_commands'] == 0, mod
    for x in coupled['inputs']:
        if x['path'] in inputs:
            assert inputs[x['path']] == x, x['path']
        inputs[x['path']] = x
    review_root = Path(context.get('review_root', context['root']))
    review_path = review_root / 'INDEPENDENT_REVIEW.json'
    review = json.loads(review_path.read_text())
    assert review['blocking_findings'] == [] and review['source_sha256'] == result['source']['sha256'], mod
    metadata_path = review_root / 'ARCHIVE.json'
    metadata = json.loads(metadata_path.read_text())
    archive = review_root / metadata['archive']
    assert fp(archive)['sha256'] == metadata['sha256'], mod
    before = git_sha(P15, BASE, mod)
    records.append(dict(module=mod, source=result['source'], objects=objects,
        original_receipt=fp(receipt), normal=result['normal'], kernel=result['kernel'], audit=result['audit'],
        owned=result['owned'], private=result['private'], coupled_receipt=fp(coupled_path),
        review=fp(review_path), archive_metadata=fp(metadata_path), archive=fp(archive),
        p14_source_commit=P14HEAD, p15_before_source_sha256=before,
        source_adoption_required=before != result['source']['sha256'], new_proof_commands=0))
    direct.update(re.findall(r'^import (ImbalancedChen[.][A-Za-z0-9_.]+)',
        Path(result['source']['path']).read_text(), re.M))
external = direct - group
assert len(external) == 11, sorted(external)
closure = set(group)
setup_records = []
for mod in sorted(external):
    setup = MEMBER / '.lake/build/ir' / (mod.replace('.', '/') + '.setup.json')
    obj = MEMBER / '.lake/build/lib/lean' / (mod.replace('.', '/') + '.olean')
    for p in [setup, obj]:
        assert str(p) in inputs, str(p)
        check(inputs[str(p)])
    closure.add(mod)
    closure.update(m for m in json.loads(setup.read_text())['importArts'] if m.startswith('ImbalancedChen.'))
    setup_records.append(dict(module=mod, setup=inputs[str(setup)], object=inputs[str(obj)]))
assert len(closure) == 560, len(closure)
sources = {}
for x in list(inputs.values()) + [res['source']]:
    if '/ImbalancedChen/' in x['path'] and x['path'].endswith('.lean'):
        mod = 'ImbalancedChen.' + x['path'].split('/ImbalancedChen/', 1)[1].removesuffix('.lean').replace('/', '.')
        if mod in sources:
            assert sources[mod]['sha256'] == x['sha256'], mod
        sources[mod] = x
assert len(sources) == 166, len(sources)
assert set(sources) - closure == {'ImbalancedChen.P5OldFifthPointwiseQ'}
pins = []
for mod, x in sorted(sources.items()):
    check(x)
    pins.append(dict(module=mod, source=x, p15_before_source_sha256=git_sha(P15, BASE, mod),
        actual_import_closure=mod in closure))
ordinary = []
for mod in sorted(closure - group):
    x = fp(MEMBER / (mod.replace('.', '/') + '.lean'))
    assert git_sha(P15, BASE, mod) == x['sha256'], mod
    ordinary.append(dict(module=mod, source=x, p15_git_sha256=x['sha256']))
assert len(ordinary) == 549
assert sum(x['source_adoption_required'] for x in records) == 8
j = dict(status='PREPARED_ONLY_NOT_ADOPTED', utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    base_commit=BASE, p14_source_commit=P14HEAD, accepted_owners=records,
    coupled_project_source_pins=pins, pinned_project_source_count=166,
    group_external_actual_setup=setup_records, actual_project_import_closure_count=560,
    actual_group_external_project_sources=ordinary, actual_group_external_source_count=549,
    historical_extra_pin=dict(module='ImbalancedChen.P5OldFifthPointwiseQ',
        reason='Historical PointwiseQ receipt provenance explicitly pinned by Index18 and CommonPolicy2 drivers; not an actual imported module of this group.',
        source_sha256=sources['ImbalancedChen.P5OldFifthPointwiseQ']['sha256'],
        p15_git_sha256=git_sha(P15, BASE, 'ImbalancedChen.P5OldFifthPointwiseQ'),
        p15_source_adoption_required=False, p15_variant_formal_credit=0),
    coupled_unique_paths=len(inputs), all_expected_repeat_fingerprints_consistent=True,
    owner_count=11, changed_source_count=8, identical_owner_sources=3,
    only_exact_previously_accepted_sources=True, fresh_import_closure_acceptance_claimed=False,
    new_proof_commands=0, whole_P1_4_complete=False, whole_P1_5_complete=False)
(ROOT / 'PROVENANCE.json').write_text(json.dumps(j, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(dict(status='PREPARED_ONLY', owners=11, changes=8, sources=166,
    actual_import_closure=560, historical_unused_pin=1, unique_coupled_paths=len(inputs))))
