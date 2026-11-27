"""Bind a reviewed, retained Gaps archive to the next workflow; run no proof commands."""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile


HERE = Path(__file__).resolve().parent
GAPS = '/workspace/p26-cell05-all-row-gaps-20261127-v1'
ARITHMETIC = '/workspace/p26-cell05-all-row-arithmetic-20261127-v1'
TOOL = 'tools/p26/cell05-all-row-gaps-20261127'
GAPS_MODULE = 'ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps'
AUDIT = 'owned-audits/P2OriginalSaving19Cell05AllRowArithmetic.lean'
SOURCE_PIN = {'bytes': 6895, 'sha256': '8a271737e570b277b2f30a39ec193fe72480f8e685de5860e648b8477918c931'}
AUDIT_PIN = {'bytes': 2718, 'sha256': '27f18c413bc763a619daf32400e7f8d217acfbb32e892242e48f38679afc2e64'}
FASTDET_PIN = {'bytes': 9926, 'sha256': 'a7cd0646913fb7c485f328c0eb97a6e55e76b3a15d730ae628ce3f3ece54eee9'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def identity(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def output_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def configuration(archive_body, retained_body, retained_digest, workflow_digest):
    require(identity(retained_body)['sha256'] == retained_digest, 'Retained report digest differs')
    report = json.loads(retained_body)
    require(report['status'] == 'RETAINED_EVIDENCE_VERIFIED' and report['old_proof_commands'] == 0 and
            report['accepted_targets'] == 1 and report['accepted_steps'] == 3 and report['P2_6_complete'] is False,
            'Completed retained predecessor verification required')
    members = {'workflow': TOOL+'/WORKFLOW_MANIFEST.json', 'configuration': TOOL+'/CONFIG.json',
               'driver': TOOL+'/run_gaps.py', 'run': 'verification/RUN.json', 'success': 'verification/SUCCESS.json',
               'index': 'REUSE_INDEX.json', 'object': 'objects/ImbalancedChen/P2OriginalSaving19Cell05AllRowGaps.olean'}
    pins = {'stage': GAPS, 'archive': {'path': GAPS+'/exports/gaps-evidence.tar.xz', **identity(archive_body)}}
    require(report['archive'] == pins['archive'], 'Retained archive identity differs')
    with tarfile.open(fileobj=io.BytesIO(archive_body), mode='r:xz') as tar:
        rows = tar.getmembers()
        require(len({r.name for r in rows}) == len(rows), 'Duplicate archive member')
        require(all(r.isfile() and not PurePosixPath(r.name).is_absolute() and '..' not in PurePosixPath(r.name).parts
                    for r in rows), 'Invalid evidence archive member')
        def read(name):
            return tar.extractfile(tar.getmember(name)).read()
        for key, name in members.items():
            pins[key] = {'path': GAPS+'/'+name, **identity(read(name))}
        require(pins['workflow']['sha256'] == workflow_digest, 'Wrong independently supplied Gaps workflow')
        require(pins['success'] == report['success'] and pins['index'] == report['reuse_index'], 'Gaps summaries changed')
        manifest = json.loads(read(members['workflow']))
        files = manifest['files']
        names = {r['relative_path'] for r in files}
        require(manifest['schema'] == 'p26_cell05_all_row_gaps_workflow_v1' and len(names) == len(files) and
                {'CONFIG.json','run_gaps.py','owned-audits/P2OriginalSaving19Cell05AllRowGaps.lean'} <= names,
                'Incomplete predecessor workflow')
        for row in files:
            name = row['relative_path']
            require(identity(read(TOOL+'/'+name)) == {k: row[k] for k in ('bytes','sha256')}, 'Gaps workflow payload changed')
        run = json.loads(read(members['run']))
        success = json.loads(read(members['success']))
        require(run['stage'] == GAPS and run['schema'] == 'cell05_all_row_gaps_run_v1' and
                run['workflow_sha256'] == workflow_digest and len(run['dependencies']) == 128 and
                [x['module'] for x in run['targets']] == [GAPS_MODULE], 'Unexpected Gaps RUN')
        require(success['schema'] == 'cell05_all_row_gaps_success_v1' and success['status'] == 'succeeded' and
                success['run'] == pins['run'] and success['object'] == pins['object'] and pins['object']['bytes'] > 0 and
                [success[k] for k in ('accepted_targets','accepted_steps','old_supplier_count','project_closure_count')] == [1,3,128,129] and
                success['old_proof_commands'] == 0 and success['P2_6_complete'] is False and
                [(r['module'],r['mode']) for r in success['records']] == [(GAPS_MODULE,m) for m in ('normal','kernel','owned')],
                'Unexpected Gaps success or object binding')
    return {'schema':'p26_cell05_all_row_arithmetic_config_v1','stage':ARITHMETIC,'source':SOURCE_PIN,'audit':AUDIT_PIN,
            'fastdet_transport':FASTDET_PIN,'gaps':pins}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gaps-archive', type=Path, required=True)
    parser.add_argument('--retained-report', type=Path, required=True)
    parser.add_argument('--retained-sha256', required=True)
    parser.add_argument('--gaps-workflow-sha256', required=True)
    parser.add_argument('--package-dir', type=Path, required=True)
    args = parser.parse_args()
    config = configuration(args.gaps_archive.read_bytes(), args.retained_report.read_bytes(),
                           args.retained_sha256, args.gaps_workflow_sha256)
    tool = args.package_dir
    files = ['run_arithmetic.py', 'bind_config.py', 'test_run_arithmetic.py', 'DEPLOYMENT.md', AUDIT]
    require(tool.is_dir() and not tool.is_symlink() and all((tool/n).is_file() and not (tool/n).is_symlink() for n in files),
            'Prepare the reviewed package files first')
    require(identity((tool/AUDIT).read_bytes()) == AUDIT_PIN, 'Wrong arithmetic audit')
    config_body = output_bytes(config)
    manifest_rows = [{'relative_path':n, **identity((tool/n).read_bytes())} for n in files]
    manifest_rows.append({'relative_path':'CONFIG.json', **identity(config_body)})
    manifest_body = output_bytes({'schema':'p26_cell05_all_row_arithmetic_workflow_v1',
                                  'files':sorted(manifest_rows,key=lambda r:r['relative_path'])})
    outputs = [(tool/'CONFIG.json',config_body), (tool/'WORKFLOW_MANIFEST.json',manifest_body)]
    for path,body in outputs:
        if path.is_symlink() or (path.exists() and path.read_bytes() != body):
            raise ValueError('Conflicting existing binding: '+str(path))
    for path,body in outputs:
        if not path.exists():
            with path.open('xb') as stream:
                stream.write(body)
    print(json.dumps({'configuration':identity(config_body),'workflow_manifest':identity(manifest_body),
                      'gaps_run':config['gaps']['run'],'gaps_success':config['gaps']['success'],
                      'gaps_object':config['gaps']['object'],'new_Lean_commands':0}))


if __name__ == '__main__':
    main()
