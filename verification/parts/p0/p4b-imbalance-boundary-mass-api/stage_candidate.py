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
    # Append only only these exact checkout sources absent from frozen T01.
    expected_supplemental = {'ImbalancedChen.RealHalfProductSieveBridge': ('ImbalancedChen/RealHalfProductSieveBridge.lean', 'ImbalancedChen/RealHalfProductSieveBridge.lean', '4b338348a830dcba08b8d4b4e4406605c13f104b', '36f16ed6d0f7aa95227a7d3b3783186b3e9bb041255ee6ae24e1ac9e1f147a2e', 8636), 'ImbalancedChen.ActualOptimizedSieveBound': ('ImbalancedChen/ActualOptimizedSieveBound.lean', 'ImbalancedChen/ActualOptimizedSieveBound.lean', '7f08574eef174c60f4498bf2fed86544033fc3f4', '90c85946fb0ac2289abf21a628242bf4efce66875070e2a0c83fbab039e4cc0a', 6021), 'ImbalancedChen.ActualSelbergMain': ('ImbalancedChen/ActualSelbergMain.lean', 'ImbalancedChen/ActualSelbergMain.lean', '2619c743e3a7ef3d3d217c45861246f34c341ee0', '0965470e4fde84b4d497978d4b040fca34fa8c1bac9993f68fcbf7c8da03f0cd', 12453), 'ImbalancedChen.ActualSelbergCoefficients': ('ImbalancedChen/ActualSelbergCoefficients.lean', 'ImbalancedChen/ActualSelbergCoefficients.lean', 'fc6039caf0b319e0d0f2d1576838497352df04d7', '81d8a37b5bb14295fe35d79f876e16e7e331eabc4f110f6c1f2e5b22f6aead2e', 12628), 'ImbalancedChen.WeightedSieveLogBudget': ('ImbalancedChen/WeightedSieveLogBudget.lean', 'ImbalancedChen/WeightedSieveLogBudget.lean', '4def45618e5f21fd75cbf398b4225cb64d4193bf', '5eb67bec621dbeccf5216cd79246f0c59ffdf0d83cf269198a5b6706196bcd13', 6865), 'ImbalancedChen.WeightedSieveError': ('ImbalancedChen/WeightedSieveError.lean', 'ImbalancedChen/WeightedSieveError.lean', '5a9bd03fde7c1e8c5a88556b80d3011c9c9f92ed', '92df6afcf67a3545df50f354b8f676465e5533374117cdff3589c0b41c805a68', 14690), 'ImbalancedChen.TruncatedSieveLevel': ('ImbalancedChen/TruncatedSieveLevel.lean', 'ImbalancedChen/TruncatedSieveLevel.lean', '4eed2c57ede792f8aa089a0e8b7e1d27e62155fd', '38b4be7a4ceaa2e9b7d8374861b44a160c162fdb3ece70f35eef0573bf2c626d', 8362), 'ImbalancedChen.DivisorMomentBudget': ('ImbalancedChen/DivisorMomentBudget.lean', 'ImbalancedChen/DivisorMomentBudget.lean', '0ebeac3a0f8a4ca6f608e28e0fbc24b13b1e928a', '6bf631795ed2e7af99894c8c984bb2e4171029f089c17492e9cbcce22083a9cd', 8678), 'ImbalancedChen.P4BRealBParameterMonotonicity': ('ImbalancedChen/P4BRealBParameterMonotonicity.lean', 'ImbalancedChen/P4BRealBParameterMonotonicity.lean', '3b0e45cac65b9db04b5ef8645133fcb00cac2afb', 'c627d4af7bf7318f166c125f18add18b086f65c7ca642993c7e911621730992b', 9398), 'ImbalancedChen.P4BImbalanceBoundaryMass': ('ImbalancedChen/P4BImbalanceBoundaryMass.lean', 'ImbalancedChen/P4BImbalanceBoundaryMass.lean', '68e28f9e261c577310b20e1dddfb8675300d34f1', 'aba22f49a64c13eff5a6071105befab698577670c324744a025e52d263c263f9', 7333)}
    ext_sources = m['supplemental_checkout_sources']
    assert len(ext_sources) == len(expected_supplemental)
    assert {x['module'] for x in ext_sources} == set(expected_supplemental)
    assert m['target'] == 'ImbalancedChen.P4BImbalanceBoundaryMass'
    for ext in ext_sources:
        install_path, source_path, expected_blob, expected_hash, expected_len = expected_supplemental[ext['module']]
        assert ext['install_path'] == install_path and ext['repository_path'] == ext['source'] == source_path
        assert [row for row in m['closure_source_records'] if row['module'] == ext['module']] == [ext]
        blob = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD:' + source_path], text=True).strip()
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
