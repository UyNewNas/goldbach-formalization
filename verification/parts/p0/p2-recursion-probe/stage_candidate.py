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
    expected_overlays = {}
    assert m['candidate_overlays'] == []
    for row in m['probe_sources']:
        path = project / row['install_path']
        assert not path.exists(), 'Probe must never replace existing project source'
        content = (HERE / row['source_file']).read_bytes()
        assert digest(content) == row['sha256'], row['module']
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
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
