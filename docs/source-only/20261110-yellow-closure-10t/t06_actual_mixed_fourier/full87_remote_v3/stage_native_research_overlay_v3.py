"""Remote source-copy gate v3. No compiler, guard, kernel or Git write.

Checks actual canonical readback and the observed native source path set,
including ignored physical files. Actual guarded compile/setup/import binding
and fresh kernel replay remain mandatory separate root-owned gates.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
LOADABLE_SUFFIXES = {'.lean', '.olean', '.ilean', '.ir', '.so', '.dll', '.dylib', '.bc', '.o', '.a', '.c'}
LEGACY_KERNEL_SET_SHA256 = '7182083990021cce01c1e357f8de8148e636a4c24d7613c00be0b3328ec5f543'


def raw_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def descriptor(path: Path) -> dict:
    payload = path.read_bytes()
    return {'bytes': len(payload), 'sha256': hashlib.sha256(payload).hexdigest(),
            'raw_git_blob_sha1': raw_blob(payload)}


def json_identity(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def walk_error(error: OSError) -> None:
    raise error


def physical_untracked_census(package: Path, tracked: set[str]) -> dict:
    """Observed source tree, including ignored files; .git/.lake excluded.

    .lake dependency/build artifacts require the separate actual-import/ABI
    collector. This filesystem census is not mislabeled a compiler read trace.
    """
    files, links = {}, []
    for directory, dirs, names in os.walk(package, followlinks=False, onerror=walk_error):
        base = Path(directory)
        if base == package:
            dirs[:] = [d for d in dirs if d not in {'.git', '.lake'}]
        for child in list(dirs):
            path = base / child
            if path.is_symlink():
                links.append(path.relative_to(package).as_posix())
                dirs.remove(child)
        for name in names:
            path = base / name
            rel = path.relative_to(package).as_posix()
            if path.is_symlink():
                links.append(rel)
            elif path.is_file() and rel not in tracked:
                loadable = path.suffix in LOADABLE_SUFFIXES or any(
                    marker in path.name for marker in ['.olean.', '.ilean.', '.ir.', '.so.'])
                files[rel] = {**descriptor(path), 'source_or_loadable': loadable}
    return {'scope': 'physical native package source tree excluding .git and .lake',
            'ignored_files_included': True, 'untracked_files': files,
            'unfollowed_symlinks': sorted(links)}


def main() -> None:
    if os.getenv('GITHUB_ACTIONS') != 'true':
        raise SystemExit('Root-authorized remote staging only')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--plan-sha256', required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--mode', choices=['install', 'verify_existing'], default='install')
    parser.add_argument('--pre-install-receipt', type=Path)
    parser.add_argument('--pre-install-receipt-sha256')
    parser.add_argument('--acceptance-manifest', type=Path, required=True)
    parser.add_argument('--acceptance-manifest-sha256', required=True)
    args = parser.parse_args()
    plan_bytes = (HERE / 'NATIVE_RESEARCH_OVERLAY.json').read_bytes()
    if hashlib.sha256(plan_bytes).hexdigest() != args.plan_sha256:
        raise ValueError('Different independently reviewed native overlay plan')
    plan = json.loads(plan_bytes)
    acceptance_bytes = args.acceptance_manifest.read_bytes()
    acceptance_sha = hashlib.sha256(acceptance_bytes).hexdigest()
    if acceptance_sha != args.acceptance_manifest_sha256:
        raise ValueError('Different independently approved complete-scope acceptance manifest')
    acceptance = json.loads(acceptance_bytes)
    kernel_modules = acceptance['fresh_kernel_modules']
    legacy_modules = acceptance['mandatory_legacy_kernel_modules']
    native_modules = {r['module'] for r in plan['files']}
    if len(kernel_modules) != len(set(kernel_modules)) or len(kernel_modules) < 1607:
        raise ValueError('The mandatory fresh kernel gate was reduced or duplicated')
    if len(legacy_modules) != 1607 or json_identity(sorted(legacy_modules)) != LEGACY_KERNEL_SET_SHA256:
        raise ValueError('The reviewed legacy1607 module census was altered')
    if not set(legacy_modules) <= set(kernel_modules):
        raise ValueError('A mandatory legacy kernel module was dropped')
    if not native_modules <= set(kernel_modules):
        raise ValueError('The complete43 native kernel set is missing')
    gate_record = next((r for r in acceptance['support_files'] if r['path'] == Path(__file__).name), None)
    script_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if gate_record is None or gate_record['sha256'] != script_sha:
        raise ValueError('Source gate script is not the reviewed manifest input')
    if acceptance['native_research_overlay']['sha256'] != args.plan_sha256:
        raise ValueError('The source plan and complete-scope manifest are not bound')
    package = args.package.resolve()
    revision = plan['native_commit']
    git = ['git', '-C', str(package)]
    if subprocess.check_output(git + ['rev-parse', 'HEAD'], text=True).strip() != revision:
        raise ValueError('Wrong native dependency revision')
    if subprocess.check_output(git + ['status', '--porcelain', '--untracked-files=no']):
        raise ValueError('Native tracked sources already differ')
    if args.receipt.exists() or plan['failures']:
        raise ValueError('Existing receipt or incomplete source plan')
    expected = {r['install_path'] for r in plan['files']}
    if len(expected) != 43 or len(plan['files']) != 43:
        raise ValueError('The exact original43 native source set was changed')
    tracked = set(subprocess.check_output(git + ['ls-files', '-z']).decode().split('\0')) - {''}
    if tracked & expected:
        raise ValueError('A canonical destination is unexpectedly tracked at the native pin')
    before = physical_untracked_census(package, tracked)
    pre_binding = None
    if args.mode == 'verify_existing':
        if args.pre_install_receipt is None or args.pre_install_receipt_sha256 is None:
            raise ValueError('Post-compile verification requires the exact installation-period receipt and SHA256')
        pre_bytes = args.pre_install_receipt.read_bytes()
        pre_sha = hashlib.sha256(pre_bytes).hexdigest()
        if pre_sha != args.pre_install_receipt_sha256:
            raise ValueError('Installation-period receipt identity differs')
        pre = json.loads(pre_bytes)
        required_context = {
            'schema': 'full87-native-original-source-overlay-receipt-v3',
            'mode': 'install', 'source_commit': os.environ['SOURCE_COMMIT'],
            'run_id': os.environ['GITHUB_RUN_ID'], 'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'],
            'native_commit': revision, 'plan_sha256': args.plan_sha256,
            'acceptance_manifest_sha256': acceptance_sha, 'source_gate_script_sha256': script_sha}
        if any(pre.get(k) != v for k, v in required_context.items()):
            raise ValueError('Installation and verification receipts belong to different source/run/gate environments')
        pre_rows = {r['installed_relative_path']: r for r in pre['files']}
        pre_after = pre['after_source_tree_census']
        if len(pre['files']) != 43 or set(pre_rows) != expected or pre_after['unfollowed_symlinks']:
            raise ValueError('Installation receipt lacks the exact observed43 source set')
        if pre_after != before:
            raise ValueError('Post-compile source census differs from the installation-period observed census')
        for relative, row in pre_rows.items():
            observed = before['untracked_files'][relative]
            if (row['bytes'], row['sha256'], row['git_blob_sha1']) != (
                    observed['bytes'], observed['sha256'], observed['raw_git_blob_sha1']):
                raise ValueError('Installation row and actual post-compile canonical bytes differ')
            if row['installed_path'] != str(package / relative) or not row['canonical_readback_verified']:
                raise ValueError('Installation canonical path/readback is not bound to this verification')
        pre_binding = {'path': str(args.pre_install_receipt.resolve()), 'bytes': len(pre_bytes),
                       'sha256': pre_sha, 'observed_after_census_sha256': json_identity(pre_after),
                       'source_rows_sha256': json_identity(pre['files'])}
    elif args.pre_install_receipt is not None or args.pre_install_receipt_sha256 is not None:
        raise ValueError('Install mode does not accept a prior verification receipt')
    def reject_census(reason: str, after: dict | None = None) -> None:
        observed = after if after is not None else before
        observed_sources = {p for p, r in observed['untracked_files'].items() if r['source_or_loadable']}
        diagnostic = {'status': 'REJECT_UNDECLARED_OR_MUTATED_SOURCE_TREE_INPUTS',
                      'reason': reason, 'before': before, 'after': after,
                      'run_id': os.environ['GITHUB_RUN_ID'], 'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'],
                      'unexpected_source_paths': sorted(observed_sources - expected),
                      'missing_source_paths': sorted(expected - observed_sources),
                      'compiled': False, 'kernel_verified': False}
        failure = args.receipt.with_name(args.receipt.name + '.failure.json')
        if failure.exists():
            raise ValueError('Existing failure diagnostic')
        failure.parent.mkdir(parents=True, exist_ok=True)
        failure.write_text(json.dumps(diagnostic, indent=2) + '\n')
        raise ValueError(reason)
    unexpected = sorted(p for p, row in before['untracked_files'].items()
                        if row['source_or_loadable'] and p not in expected)
    if before['unfollowed_symlinks'] or unexpected:
        reject_census('Source/loadable file or symlink is outside the declared43')
    before_sources = {p for p, r in before['untracked_files'].items() if r['source_or_loadable']}
    if args.mode == 'verify_existing' and before_sources != expected:
        reject_census('Post-compile verification requires the existing exact43 sources without repair')
    rows = []
    for record in plan['files']:
        original = subprocess.check_output(git + ['show', revision + ':' + record['path']])
        if len(original) != record['bytes'] or raw_blob(original) != record['git_blob_sha1']:
            raise ValueError('Pinned research source differs: ' + record['module'])
        path = package / record['install_path']
        if not path.resolve().is_relative_to(package) or path.is_symlink():
            raise ValueError('Unsafe canonical native source destination')
        already_present = path.exists()
        if already_present and path.read_bytes() != original:
            raise ValueError('Refuse to overwrite a different native source')
        if not already_present:
            if args.mode == 'verify_existing':
                reject_census('Canonical source disappeared during verification')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(original)
        installed = path.read_bytes()
        if installed != original:
            raise ValueError('Canonical native source readback differs')
        rows.append({'module': record['module'], 'original_revision': revision,
                     'original_research_path': record['path'], 'installed_relative_path': record['install_path'],
                     'installed_path': str(path), 'bytes': len(installed),
                     'git_blob_sha1': raw_blob(installed), 'sha256': hashlib.sha256(installed).hexdigest(),
                     'canonical_readback_verified': True, 'preexisting_identical': already_present})
    after = physical_untracked_census(package, tracked)
    actual = {p for p, row in after['untracked_files'].items() if row['source_or_loadable']}
    if after['unfollowed_symlinks'] or actual != expected:
        reject_census('Observed post-overlay source set is not exactly the declared43', after)
    prior_other = {p: row for p, row in before['untracked_files'].items() if p not in expected}
    after_other = {p: row for p, row in after['untracked_files'].items() if p not in expected}
    if prior_other != after_other:
        reject_census('Undeclared physical files changed during native source staging', after)
    for row in rows:
        observed = after['untracked_files'][row['installed_relative_path']]
        if (observed['bytes'], observed['sha256'], observed['raw_git_blob_sha1']) != (
                row['bytes'], row['sha256'], row['git_blob_sha1']):
            reject_census('Final source census/readback identity differs', after)
    if subprocess.check_output(git + ['status', '--porcelain', '--untracked-files=no']):
        raise ValueError('Tracked native sources changed during source overlay')
    result = {'schema': 'full87-native-original-source-overlay-receipt-v3',
              'status': 'OBSERVED_EXACT43_SOURCE_SET_AND_READBACK_ONLY_UNCOMPILED',
              'source_commit': os.environ['SOURCE_COMMIT'], 'native_commit': revision,
              'run_id': os.environ['GITHUB_RUN_ID'], 'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'],
              'mode': args.mode,
              'acceptance_manifest_sha256': acceptance_sha, 'source_gate_script_sha256': script_sha,
              'fresh_kernel_module_set_sha256': json_identity(sorted(kernel_modules)),
              'pre_install_receipt_binding': pre_binding,
              'observed_before_census_sha256': json_identity(before),
              'observed_after_census_sha256': json_identity(after),
              'plan_sha256': hashlib.sha256(plan_bytes).hexdigest(), 'files': rows,
              'before_source_tree_census': before, 'after_source_tree_census': after,
              'observed_canonical_untracked_source_paths': sorted(actual),
              'unexpected_source_paths': sorted(actual - expected), 'missing_source_paths': sorted(expected - actual),
              'tracked_sources_unchanged': True, 'source_installer_did_not_modify_lakefile_or_flags': True,
              'actual_compiler_flags_verified': False, 'actual_runtime_ABI_verified': False,
              'compiled': False, 'kernel_verified': False,
              'actual_guarded_compile_setup_import_binding': 'MANDATORY_SEPARATE_GATE_NOT_RUN_HERE',
              'fresh_native_kernel_census_required': sorted(r['module'] for r in plan['files']),
              'fresh_complete_project_plus_audit_plus_native_kernel_count_required': len(kernel_modules)}
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': result['status'], 'observed_source_copies': len(rows)}))


if __name__ == '__main__':
    main()
