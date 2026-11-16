"""Stage frozen T01 v3 with exact target API corrections and canonical owner import."""
import hashlib, json, os, pathlib, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
T01 = pathlib.Path('docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel')

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    if os.environ.get('GITHUB_ACTIONS') != 'true':
        raise SystemExit('GitHub Actions only; no local proof execution')
    source = pathlib.Path(os.environ['GITHUB_WORKSPACE']) / 'candidate'
    project = pathlib.Path(os.environ['PROJECT'])
    logs = pathlib.Path(os.environ['LOGS'])
    raw = (HERE / 'candidate-manifest.json').read_bytes()
    assert digest(raw) == os.environ['EXPECTED_MANIFEST'], 'Candidate manifest changed'
    m = json.loads(raw)
    assert subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() == m['base_commit'] == os.environ['SOURCE_COMMIT']
    original = source / T01
    full_raw = (original / 'EXACT_INSTALL_MANIFEST-v3.json').read_bytes()
    assert digest(full_raw) == m['original_full_manifest_sha256']
    assert digest((original / 'stage_project_v3.py').read_bytes()) == m['original_installer_sha256']
    full = json.loads(full_raw)
    assert len(full['targets'][0]['declarations']) == 9
    assert len(full['files']) == 729
    # The original installer validates all frozen729 sources,15 primary proofs,
    # review inputs, binary data and the original487-byte project profile.
    subprocess.run([sys.executable, str(original / 'stage_project_v3.py'), '--dest', str(project), '--purpose', 'source_validation'], check=True)
    target = project / 'ImbalancedChen/P1FourthNearOneKernel.lean'
    before = target.read_bytes()
    assert digest(before) == m['original_target_sha256']
    replacement = m['replacement']
    assert before.count(replacement['old'].encode()) == replacement['count'] == 1
    after = before.replace(replacement['old'].encode(), replacement['new'].encode())
    instantiation = m['rewrite_instantiation']
    assert after.count(instantiation['old'].encode()) == instantiation['count'] == 1
    after = after.replace(instantiation['old'].encode(), instantiation['new'].encode())
    assert digest(after) == m['candidate_target_sha256']
    assert after == (HERE / 'candidate.lean').read_bytes()
    target.write_bytes(after)
    owner = m['import_owner_repair']
    owner_path = project / owner['install_path']
    owner_before = owner_path.read_bytes()
    assert digest(owner_before) == owner['original_sha256']
    assert owner_before.count(owner['old'].encode()) == owner['count'] == 1
    owner_after = owner_before.replace(owner['old'].encode(), owner['new'].encode())
    assert digest(owner_after) == owner['candidate_sha256']
    assert owner_after == (HERE / owner['source_file']).read_bytes()
    owner_path.write_bytes(owner_after)
    assert len((project / 'lakefile.toml').read_bytes()) == 487
    assert digest((project / 'lakefile.toml').read_bytes()) == '26a6b01a52446ad6aae63d5201330b902ec94a1171fb1f0baf9fc61016098491'
    for row in m['closure_source_records']:
        expected = {m['target']: m['candidate_target_sha256'], owner['module']: owner['candidate_sha256']}.get(row['module'], row['sha256'])
        assert digest((project / row['install_path']).read_bytes()) == expected, row['module']
    logs.mkdir(parents=True, exist_ok=True)
    receipt = {'status': 'MATERIALIZED_UNCOMPILED', 'source_commit': m['base_commit'], 'manifest_sha256': digest(raw), 'target': m['target'], 'closure_modules': m['closure_modules'], 'two_target_API_corrections_and_one_canonical_owner_import_only': True, 'whole_t01_accepted': False, 'original_full_t01_requirements_unchanged': True}
    (logs / 'P1_STAGE_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (logs / 'ORIGINAL_T01_PROVENANCE.json').write_bytes((project / 'T01_PROVENANCE.json').read_bytes())
    print(json.dumps(receipt))

if __name__ == '__main__':
    main()
