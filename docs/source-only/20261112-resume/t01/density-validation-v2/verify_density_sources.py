"""Remote pre/post source receipt, with no compiler/guard/kernel execution.

The post mode never repairs sources. Keep receipts outside the staged project.
Actual guarded source reads, setup/import objects, flags and runtime/ABI remain
separate mandatory root-owned gates.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def descriptor(payload):
    return {'bytes': len(payload), 'sha256': hashlib.sha256(payload).hexdigest()}


def walk_error(error):
    raise error


def main():
    if os.getenv('GITHUB_ACTIONS') != 'true':
        raise SystemExit('Root-authorized remote source verification only')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--mode', choices=['pre_compile', 'post_compile'], required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--pre-source-receipt', type=Path)
    parser.add_argument('--pre-source-receipt-sha256')
    args = parser.parse_args()
    manifest_bytes = args.manifest.read_bytes()
    if descriptor(manifest_bytes)['sha256'] != args.manifest_sha256:
        raise ValueError('Independently approved installation manifest differs')
    manifest = json.loads(manifest_bytes)
    script = descriptor(Path(__file__).read_bytes())
    record = next(r for r in manifest['support_files'] if r['path'] == Path(__file__).name)
    if any(script[k] != record[k] for k in script):
        raise ValueError('Source verifier is not the reviewed manifest input')
    project = args.project.resolve()
    if args.receipt.resolve().is_relative_to(project) or args.receipt.exists():
        raise ValueError('Use a new receipt outside the staged project')
    provenance_path = project / 'DENSITY_PROVENANCE.json'
    provenance_bytes = provenance_path.read_bytes()
    provenance = json.loads(provenance_bytes)
    context = {'source_commit': os.environ['SOURCE_COMMIT'], 'run_id': os.environ['GITHUB_RUN_ID'],
               'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'], 'manifest_sha256': args.manifest_sha256}
    if any(provenance.get(k) != v for k, v in context.items()):
        raise ValueError('Staging provenance belongs to another source/run/manifest')
    if provenance['source_identity_sha256'] != manifest['targets'][0]['source_identity_sha256']:
        raise ValueError('Actual full target source identity differs')
    if provenance['source_count'] != len(manifest['files']):
        raise ValueError('Installed mathematical source census is incomplete')
    expected = {r['install_path']: r for r in manifest['files']}
    expected.update({r['install_path']: r for r in manifest['data_inputs']})
    expected.update({r['install_path']: r for r in [manifest['audit_source'], manifest['legacy_audit_source']]})
    expected['T01Audit.lean'] = manifest['inherited_T01']['audit_source']
    expected['lakefile.toml'] = manifest['inherited_T01']['project_lakefile']
    expected.update({r['install_path']: r for r in manifest['configuration']})
    expected['DENSITY_PROVENANCE.json'] = descriptor(provenance_bytes)
    actual = {}
    for relative, r in expected.items():
        path = (project / relative).resolve()
        external = (relative.startswith('../goldbach-research/') and path.is_relative_to(project.parent / 'goldbach-research')) or (relative in manifest['full_final_paths'] and path.is_relative_to(project.parent / 'tmp/publication-20261010/verification-renewal-v2/_runs/full-final'))
        if not path.is_relative_to(project) and not external:
            raise ValueError('Undeclared source/data destination escape')
        if (project / relative).is_symlink() or not path.is_file():
            raise ValueError('Missing/symlinked actual source input: ' + relative)
        observed = descriptor(path.read_bytes())
        if any(observed[k] != r[k] for k in observed):
            raise ValueError('Actual source/data/config bytes differ: ' + relative)
        actual[relative] = {**observed, 'canonical_path': str(path)}
    # Physical census includes ignored files and fails closed on unreadable
    # directories. .lake objects require the actual import/runtime collector.
    physical = {}
    for directory, dirs, names in os.walk(project, followlinks=False, onerror=walk_error):
        base = Path(directory)
        if base == project:
            dirs[:] = [n for n in dirs if n not in {'.lake', '.git'}]
        for child in dirs:
            if (base / child).is_symlink():
                raise ValueError('Undeclared source-tree directory symlink')
        for name in names:
            path = base / name
            if path.is_symlink():
                raise ValueError('Undeclared source-tree file symlink')
            relative = path.relative_to(project).as_posix()
            physical[relative] = descriptor(path.read_bytes())
    expected_internal = {p for p in expected if not p.startswith('../')}
    if set(physical) != expected_internal:
        raise ValueError('Actual physical source tree has extra/missing paths: ' +
                         json.dumps({'extra': sorted(set(physical) - expected_internal),
                                     'missing': sorted(expected_internal - set(physical))}))
    external_census = {}
    for root in [project.parent / 'goldbach-research', project.parent / 'tmp/publication-20261010/verification-renewal-v2/_runs/full-final']:
        expected_paths = {str((project / p).resolve()) for p in expected if p.startswith('../') and (project / p).resolve().is_relative_to(root)}
        observed_paths = set()
        if root.exists():
            for directory, dirs, names in os.walk(root, followlinks=False, onerror=walk_error):
                for name in dirs + names:
                    path = Path(directory) / name
                    if path.is_symlink(): raise ValueError('External source/data symlink')
                    if path.is_file(): observed_paths.add(str(path.resolve()))
        if observed_paths != expected_paths:
            raise ValueError('External data root has extra/missing files')
        external_census[str(root)] = sorted(observed_paths)
    binding = None
    if args.mode == 'post_compile':
        if args.pre_source_receipt is None or args.pre_source_receipt_sha256 is None:
            raise ValueError('Postcompile verification requires independently bound precompile receipt')
        pre_bytes = args.pre_source_receipt.read_bytes()
        if descriptor(pre_bytes)['sha256'] != args.pre_source_receipt_sha256:
            raise ValueError('Different installation-period source receipt')
        pre = json.loads(pre_bytes)
        required = {**context, 'schema': 'fine-density-source-receipt-v2', 'mode': 'pre_compile',
                    'project': str(project), 'verifier_sha256': script['sha256'],
                    'provenance_sha256': descriptor(provenance_bytes)['sha256']}
        if any(pre.get(k) != v for k, v in required.items()):
            raise ValueError('Pre/post source receipt context differs')
        if pre['actual_inputs'] != actual or pre['physical_project_census'] != physical or pre['external_data_census'] != external_census:
            raise ValueError('Actual postcompile source identities differ; no repair is permitted')
        binding = {**descriptor(pre_bytes), 'path': str(args.pre_source_receipt.resolve()),
                   'pre_actual_input_identity_sha256': identity(pre['actual_inputs']),
                   'pre_physical_census_sha256': identity(pre['physical_project_census'])}
    elif args.pre_source_receipt is not None or args.pre_source_receipt_sha256 is not None:
        raise ValueError('Precompile mode does not take an earlier source receipt')
    receipt = {**context, 'schema': 'fine-density-source-receipt-v2', 'mode': args.mode,
               'status': 'SOURCE_BYTES_AND_CENSUS_ONLY_NOT_COMPILATION_OR_ABI_EVIDENCE', 'project': str(project),
               'verifier_sha256': script['sha256'], 'provenance_sha256': descriptor(provenance_bytes)['sha256'],
               'actual_inputs': actual, 'physical_project_census': physical, 'external_data_census': external_census,
               'actual_input_identity_sha256': identity(actual), 'physical_census_sha256': identity(physical),
               'pre_source_receipt_binding': binding, 'source_tree_exclusions': ['.lake', '.git'],
               'actual_guarded_read_import_flags_runtime_ABI_gate': 'MANDATORY_SEPARATE_GATE_NOT_RUN',
               'compiled': False, 'kernel_verified': False, 'source_repaired': False}
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': receipt['status'], 'mode': args.mode, 'inputs': len(actual)}))


if __name__ == '__main__':
    main()
