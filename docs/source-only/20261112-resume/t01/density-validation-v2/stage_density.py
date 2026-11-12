"""Remote-only actual paid-I87 exact-byte installer derived from T01 v3.

No Lean/Lake/guard invocation, Git fetch/write, numerical evaluation, object
restore or CI dispatch. A new isolated project is materialized without proof
credit. Object reuse requires a separate, reviewed binding of real v3 artifacts.
"""
from __future__ import annotations
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_bytes(data: bytes, record: dict, label: str) -> bytes:
    if len(data) != record['bytes'] or digest(data) != record['sha256']:
        raise ValueError('Exact input changed: ' + label)
    if record.get('git_blob_sha1'):
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != record['git_blob_sha1']:
            raise ValueError('Git blob differs: ' + label)
    return data


def write_new(path: Path, data: bytes) -> None:
    if path.exists():
        raise ValueError('Destination already exists: ' + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def main() -> None:
    if os.getenv('GITHUB_ACTIONS') != 'true':
        raise SystemExit('Run only in root-authorized GitHub Actions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dest', type=Path, required=True)
    parser.add_argument('--repo', type=Path, default=ROOT)
    parser.add_argument('--release-asset', type=Path, required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--purpose', choices=['source_validation'], required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    manifest_bytes = (HERE / 'DENSITY_MANIFEST.json').read_bytes()
    if digest(manifest_bytes) != args.manifest_sha256:
        raise ValueError('Independently approved manifest SHA256 differs')
    manifest = json.loads(manifest_bytes)
    for record in manifest['support_files']:
        checked_bytes((HERE / record['path']).read_bytes(), record, record['path'])
    semantic = manifest['semantic_selection']
    selected = {r['module']: r for r in manifest['files'] if r.get('semantic_group')}
    if not semantic['atomic_all_four'] or len(semantic['selections']) != 4 or len(selected) != 4:
        raise ValueError('The R17 semantic source environment must select all four replacements')
    for replacement in semantic['selections']:
        if selected[replacement['module']]['sha256'] != replacement['post']['sha256']:
            raise ValueError('Mixed R17 semantic source versions')
    if (manifest['unresolved'] or manifest['targets'][0]['unresolved_modules']
            or manifest['targets'][0]['primary_module'] != 'ImbalancedChen.P4AOriginalFiniteAll22FineDensity'):
        raise ValueError('Unresolved full87 installation sources')
    if [r['module'] for r in manifest['files']] != manifest['project_modules'] or len(set(manifest['project_modules'])) != 1808:
        raise ValueError('Exact FineDensity module census differs')
    if args.dest.exists():
        raise ValueError('A new isolated destination is required')
    source_commit = os.environ['SOURCE_COMMIT']
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if head != source_commit:
        raise ValueError('Checkout is not the immutable driver source commit')
    t01_rel = manifest['inherited_T01']['repository_directory']
    v3_commit = manifest['inherited_T01']['publication_commit']

    def v3_input(relative: str) -> bytes:
        return subprocess.check_output(['git', '-C', str(repo), 'show',
                                        v3_commit + ':' + t01_rel + '/' + relative])

    v3_bytes = v3_input(manifest['inherited_T01']['manifest_path'])
    if digest(v3_bytes) != manifest['inherited_T01']['manifest_sha256']:
        raise ValueError('Inherited T01 v3 manifest changed')
    v3 = json.loads(v3_bytes)
    for r in manifest['configuration']:
        checked_bytes((repo / r['repository_path']).read_bytes(), r, r['repository_path'])
    for r in manifest['inherited_T01']['support_files']:
        checked_bytes(v3_input(r['path']), r, r['path'])
    lakefile = checked_bytes(v3_input('project-lakefile-v3.toml'),
                             manifest['inherited_T01']['project_lakefile'], 'original v3 lakefile')
    old_audit = checked_bytes(v3_input('T01Audit-v3.lean'),
                              manifest['inherited_T01']['audit_source'], 'original v3 floor audit')
    toolchain = (repo / 'lean-toolchain').read_bytes()
    lock = (repo / 'lake-manifest.json').read_bytes()
    if toolchain.decode().strip() != manifest['toolchain']:
        raise ValueError('Wrong Lean toolchain')
    revs = {x['name']: x['rev'] for x in json.loads(lock)['packages']}
    if revs['mathlib'] != manifest['mathlib_rev'] or revs['goldbach'] != manifest['native_rev']:
        raise ValueError('Wrong dependency revisions')
    required_flags = ['-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000']
    if manifest['source_elaboration_resource_options']['moreLeanArgs'] != required_flags:
        raise ValueError('Full87 must use the identical v3 source elaboration flags')
    asset_record = manifest['release_asset']
    with args.release_asset.open('rb') as stream:
        asset_hash = hashlib.file_digest(stream, 'sha256').hexdigest()
    if args.release_asset.stat().st_size != asset_record['bytes'] or asset_hash != asset_record['sha256']:
        raise ValueError('Wrong original official release asset')
    release = zipfile.ZipFile(args.release_asset)
    if len(release.namelist()) != len(set(release.namelist())):
        raise ValueError('Ambiguous duplicate outer archive member names')
    nested: dict[str, zipfile.ZipFile] = {}
    nested_receipts = {}

    def get_origin(origin: dict) -> bytes:
        kind = origin['kind']
        if kind == 'checkout':
            path = (repo / origin['path']).resolve()
            if not path.is_relative_to(repo):
                raise ValueError('Checkout input escaped the source checkout')
            return path.read_bytes()
        if kind == 'git':
            # Root prepares these exact commits beforehand. This script never fetches.
            if len(origin['commit']) != 40 or not all(c in '0123456789abcdef' for c in origin['commit']):
                raise ValueError('Git source is not fixed to an exact commit')
            return subprocess.check_output(['git', '-C', str(repo), 'show',
                                            origin['commit'] + ':' + origin['path']])
        if kind == 'release_member':
            return release.read(origin['member'])
        if kind == 'release_nested_member':
            member = origin['outer_member']
            if member not in nested:
                payload = release.read(member)
                if len(payload) != origin['outer_bytes'] or digest(payload) != origin['outer_sha256']:
                    raise ValueError('Original NPZ container differs: ' + member)
                archive = zipfile.ZipFile(io.BytesIO(payload))
                if len(archive.namelist()) != len(set(archive.namelist())):
                    raise ValueError('Ambiguous duplicate original NPZ member')
                nested[member] = archive
                nested_receipts[member] = {'bytes': len(payload), 'sha256': digest(payload)}
            return nested[member].read(origin['inner_member'])
        raise ValueError('Unknown exact source kind: ' + kind)

    def materialize_record(record: dict) -> bytes:
        pre = record.get('pre_input')
        if pre:
            checked_bytes(get_origin(pre['origin']), pre, record['install_path'] + ' original preimage')
        payload = get_origin(record['origin'])
        if record.get('transform'):
            if not pre:
                raise ValueError('An isolated patch requires its exact preimage')
            payload = checked_bytes(payload, pre, record['install_path'] + ' patch preimage')
            for edit in record['transform']:
                old, new = edit['old'].encode(), edit['new'].encode()
                if payload.count(old) != edit['count']:
                    raise ValueError('Literal patch-site count differs')
                payload = payload.replace(old, new)
        return checked_bytes(payload, record, record['install_path'])

    project = args.dest.resolve()
    external_data = project.parent / 'goldbach-research'
    full_final = project.parent / 'tmp/publication-20261010/verification-renewal-v2/_runs/full-final'
    declared_data = {r['install_path'] for r in manifest['data_inputs']}
    if len(manifest['full_final_paths']) != 22 or set(manifest['full_final_paths']) - declared_data:
        raise ValueError('Exact full-final input census differs')

    def destination(relative: str) -> Path:
        path = (project / relative).resolve()
        if path.is_relative_to(project):
            return path
        if relative.startswith('../goldbach-research/') and path.is_relative_to(external_data):
            return path
        if relative in manifest['full_final_paths'] and path.is_relative_to(full_final):
            return path
        raise ValueError('Unlisted destination outside the isolated project')

    project.mkdir(parents=True)
    write_new(project / 'lean-toolchain', toolchain)
    write_new(project / 'lake-manifest.json', lock)
    # Exactly v3 bytes: same package/library configuration and source flags.
    write_new(project / 'lakefile.toml', lakefile)
    source_receipts = {}
    for record in manifest['files']:
        payload = materialize_record(record)
        write_new(destination(record['install_path']), payload)
        source_receipts[record['module']] = {'bytes': len(payload), 'sha256': digest(payload), 'origin': record['origin'],
                                             'transform': record.get('transform', []),
                                             'pre_sha256': record.get('pre_input', {}).get('sha256')}
    for record in manifest['data_inputs']:
        write_new(destination(record['install_path']), materialize_record(record))
    write_new(project / 'T01Audit.lean', old_audit)
    legacy_audit = checked_bytes((HERE / 'CandidateAudit.lean').read_bytes(),
                                 manifest['legacy_audit_source'], 'retained unchanged original27 audit')
    write_new(destination(manifest['legacy_audit_source']['install_path']), legacy_audit)
    audit = checked_bytes((HERE / 'DensityAudit.lean').read_bytes(),
                           manifest['audit_source'], 'new original-scope type audit')
    write_new(destination(manifest['audit_source']['install_path']), audit)
    for archive in nested.values():
        archive.close()
    release.close()
    if len(nested_receipts) != 94:
        raise ValueError('Original 94 NPZ container inventory was reduced')
    provenance = {
        'status': 'MATERIALIZED_FINE_DENSITY_SOURCES_UNCOMPILED',
        'source_commit': source_commit, 'run_id': os.environ['GITHUB_RUN_ID'],
        'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'], 'manifest_sha256': digest(manifest_bytes),
        'source_identity_sha256': manifest['targets'][0]['source_identity_sha256'],
        'target': manifest['targets'][0],
        'source_count': len(manifest['files']), 'source_receipts': source_receipts,
        'data_inputs': manifest['data_inputs'], 'original_npz_receipts': nested_receipts,
        'audit_source_sha256': digest(audit), 'legacy_audit_source_sha256': digest(legacy_audit),
        'original_T01_audit_source_sha256': digest(old_audit), 'project_lakefile_sha256': digest(lakefile),
        'purpose': args.purpose, 'compiled': False, 'kernel_verified': False,
        'reused_objects': [], 'v2_object_claim': False,
        'semantic_selection': semantic,
        'forbidden_old_object_modules': manifest['semantic_forbidden_old_object_modules'],
        'semantic_consumer_elaboration_and_review_pending': True,
        'actual_paid_terminal': 'ImbalancedChen.P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity',
        'fresh_kernel_module_set_sha256': manifest['fresh_kernel_module_set_sha256'],
        'actual_compiler_flags_verified': False, 'actual_runtime_ABI_verified': False,
        'required_pre_and_post_source_gate': 'verify_density_sources.py',
        'reuse_requirement': 'Wait for actual T01 v3 coherent artifact; independently rebind each candidate before loading; no automatic cold duplicate 729 build.'}
    write_new(project / 'DENSITY_PROVENANCE.json', (json.dumps(provenance, indent=2) + '\n').encode())
    print(json.dumps({'status': provenance['status'], 'source_count': len(manifest['files']),
                      'data_count': len(manifest['data_inputs']), 'reused_objects': 0}))


if __name__ == '__main__':
    main()
