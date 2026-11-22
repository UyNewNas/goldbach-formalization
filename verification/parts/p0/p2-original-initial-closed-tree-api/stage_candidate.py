"""Stage exact frozen T01 v3 and hash-bound accepted-source/API overlays; GitHub CI only."""
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
    assert digest(raw) == os.environ['EXPECTED_MANIFEST']
    m = json.loads(raw)
    assert subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() == m['base_commit'] == os.environ['SOURCE_COMMIT']
    original = source / T01
    full_raw = (original / 'EXACT_INSTALL_MANIFEST-v3.json').read_bytes()
    assert digest(full_raw) == m['original_full_manifest_sha256']
    assert digest((original / 'stage_project_v3.py').read_bytes()) == m['original_installer_sha256']
    full = json.loads(full_raw)
    assert len(full['targets'][0]['declarations']) == 9
    assert len(full['files']) == 729
    subprocess.run([sys.executable, str(original / 'stage_project_v3.py'), '--dest', str(project), '--purpose', 'source_validation'], check=True)
    # Append only the five exact checkout sources absent from frozen T01.
    expected_supplemental = {'ImbalancedChen.Part4ActualThirdOriginalCompactDomain': ('ImbalancedChen/Part4ActualThirdOriginalCompactDomain.lean', 'cb8f346cdd5a2c47decece40dcff875123ba99ee', '94afd7ce9718f7c00fe43800ad657e1aa00cb32229bbfd9db1968180724db11f', 4323), 'ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation': ('ImbalancedChen/Part4ActualThirdOriginalClosedSplitAggregation.lean', '4004e371fefad826cc4427afeff0d28127919d47', '27c9daffb5b47294f4f73b954f2512c12a77102655488d6b300726d581749a98', 8221), 'ImbalancedChen.P4AClosedTreeCoordinatePropagation': ('ImbalancedChen/P4AClosedTreeCoordinatePropagation.lean', '6001168a68966f5c847d915e168ae6bd3b48e675', 'f800db085c2040fc741a31809a85305683673a788d067855b44cca1426443276', 11042), 'ImbalancedChen.P4AOriginalInitialSeedInventory': ('ImbalancedChen/P4AOriginalInitialSeedInventory.lean', '6bf6688c29a6286657ac511f9eb391f1ad5a167d', 'aceb10f1a15bf9e58dd676ed13be79cfffaa99a90fdb475ae4271215a87f85dc', 6690), 'ImbalancedChen.P2OriginalInitialClosedTree': ('ImbalancedChen/P2OriginalInitialClosedTree.lean', '910b3ce75c5c29423dde981191c480819c7d57ed', '020bcb30a18a5a718e6982fd88b2902efba4c97c346b0bb967a815b1445d16fd', 6473)}
    ext_sources = m['supplemental_checkout_sources']
    assert len(ext_sources) == len(expected_supplemental)
    assert {x['module'] for x in ext_sources} == set(expected_supplemental)
    assert m['target'] == 'ImbalancedChen.P2OriginalInitialClosedTree'
    for ext in ext_sources:
        target_path, expected_blob, expected_hash, expected_len = expected_supplemental[ext['module']]
        assert ext['install_path'] == ext['repository_path'] == target_path
        assert [row for row in m['closure_source_records'] if row['module'] == ext['module']] == [ext]
        blob = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD:' + target_path], text=True).strip()
        assert blob == ext['git_blob_sha1'] == expected_blob
        content = subprocess.check_output(['git', '-C', str(source), 'cat-file', 'blob', blob])
        assert len(content) == ext['bytes'] == expected_len
        assert digest(content) == ext['sha256'] == expected_hash
        destination = project / ext['install_path']
        assert not destination.exists(), 'Supplemental target unexpectedly part of original T01'
        destination.write_bytes(content)
    expected_overlays = {}
    for row in m['candidate_overlays']:
        path = project / row['install_path']
        assert digest(path.read_bytes()) == row['original_sha256'], row['module']
        content = (HERE / row['source_file']).read_bytes()
        assert digest(content) == row['candidate_sha256'], row['module']
        path.write_bytes(content)
        assert row['module'] not in expected_overlays
        expected_overlays[row['module']] = row['candidate_sha256']
    assert len((project / 'lakefile.toml').read_bytes()) == 487
    assert digest((project / 'lakefile.toml').read_bytes()) == '26a6b01a52446ad6aae63d5201330b902ec94a1171fb1f0baf9fc61016098491'
    assert set(expected_overlays) <= set(m['closure_modules'])
    for row in m['closure_source_records']:
        assert digest((project / row['install_path']).read_bytes()) == expected_overlays.get(row['module'], row['sha256']), row['module']
    logs.mkdir(parents=True, exist_ok=True)
    receipt = {'status': 'MATERIALIZED_UNCOMPILED', 'source_commit': m['base_commit'], 'manifest_sha256': digest(raw), 'target': m['target'], 'closure_modules': m['closure_modules'], 'overlays': expected_overlays, 'whole_t01_accepted': False, 'original_full_t01_requirements_unchanged': True}
    (logs / 'P1_STAGE_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (logs / 'ORIGINAL_T01_PROVENANCE.json').write_bytes((project / 'T01_PROVENANCE.json').read_bytes())
    print(json.dumps(receipt))
if __name__ == '__main__':
    main()
