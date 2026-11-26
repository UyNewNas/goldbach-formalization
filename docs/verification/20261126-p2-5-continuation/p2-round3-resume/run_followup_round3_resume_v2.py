#!/usr/bin/env python3
"""SOURCE ONLY: resume the failed-before-Lean P2 round from its current commit.

The published round2 source tables, verification drivers, resource flags, and
377/69 acceptance predicate are reused unchanged. This runner performs no Git
checkout/reset, sparse operation, cache deletion, or source repair. A separately
reviewed disk reclamation must leave at least the original 1 GiB free threshold.

Revision 2 reads the exact historical task STDOUT.log from its already-published
archive. The original round1 runner never created a separate COMPILE.log.
"""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import io
import json
import os
import posixpath
import shutil
import subprocess
import sys
import tarfile
import traceback
import types

ROOT = Path('/workspace/p2-saving16-20261125')
PUBLICATION = '6a4bfce285e1512b3ba31fb408812040b8aee368'
PREVIOUS_COMMIT = '59e552b5459f6c0b8852e02c037c00d34a86e32f'
PRIOR_RESULT_SHA = 'acc0adffc72fd90625da9821a6cd482ebbf26a69fa3ba04ab98a7118ae947e97'
FAILED_RESULT_SHA = '85b8cbef58b5db277de1770c80c907fb448fd342457feaa85911cefc1a13a507'
ROUND2_RUNNER = 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental/run_followup_round2.py'
ROUND2_RUNNER_SHA = 'bd3a0e94025c837897ec12d9c1350cb6f236c2902c09844517cab7a0a91b3591'
ROUND2_FOLDER = 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental'
OLD = 'docs/verification/20261125-p2-5-saving16'
PRIOR_OUT = ROOT / '.lake/p25-followup-repairs-attempt001'
FAILED_OUT = ROOT / '.lake/p25-followup-repairs-attempt002'
OUT = ROOT / '.lake/p25-followup-repairs-attempt003'
ORIGINAL_ARCHIVE = 'ImbalancedChen/P2OriginalSaving16OriginalArchive.lean'
ORIGINAL_ARCHIVE_SHA = 'f51c3fdc3507d8ddbb1ea9471b667a07326abf5c3ac68a696e9b475ae9c2aaf9'
REQUIRED_394_SHA = '07526edb33b2d93d6516946d4bde0fffde168b81ffca3fcdcd2c94c6d4493ed5'
MIN_FREE_BYTES = 1073741824
ROUND1_EVIDENCE_ARCHIVE = 'docs/verification/20261126-p2-5-continuation/p2_resumed_round1_evidence.tar.gz'
ROUND1_EVIDENCE_BLOB = '9ccaee18fa8ae24bb7cdf440b039fc2b429c9133'
ROUND1_EVIDENCE_SHA = 'fc24c4e1ad5662a94c3fa378179ebdacd02d1e8a9c1a59859aafb4f4aeb575f6'
ROUND1_TASK_ID = 'fe08c0b43c374c588302d0f5142c56e9'
ROUND1_STDOUT_BYTES = 634205
ROUND1_STDOUT_SHA = '13d976b0acb6d4b2c9c5a2170015a36a505c902daafa2c6bd24c742e084fb08f'
ROUND1_EXPORT_MANIFEST_SHA = 'b6ef2bf298cf36f10d8dca8d8e18502f5aa5b4415b6e8695f669a746a30323e9'
ROUND1_COMPILE_SUMMARY_SHA = '0c6353c6953fad27c4155eebf2825bea5b692d75a7f028499c35468c7747b489'
FAILED_FILE_SHA = {
    'RUN_RESULT.json': FAILED_RESULT_SHA,
    'PREVIOUS_RECORDS.json': 'd985d34e7a94dd8cd955226bae7e62d86854ade812755fc533ef994fbf95538e',
    'previous-records.json.gz': 'dfaa5c15443ea6c8b0271da8841c39b38264178964dd743b19c53c39e14a17e8',
    'PRIOR_RUN_RESULT.json': PRIOR_RESULT_SHA,
    'p25-unused-cache-reclamation-second-recovery.json': 'feaf028b54ee589bc605c0c04acc7c73f417b92b440b25b05058bc6c69171428',
    'p25-empty-baseline-setup.json': '6b7aaf695a39f01eb0e16d23390631c9b6f70f7d3115ee4791991e83dfd96baf',
}
ABSENT_BEFORE_LEAN_KEYS = {
    'input_preparation_exit', 'compile_command', 'compile_exit', 'compile_summary',
    'compile_log_sha256', 'audit_command', 'audit_exit', 'audit_summary',
    'audit_log_sha256', 'ended_utc',
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def output(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def canonical_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def save_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def directory_files(path):
    require(path.is_dir() and not path.is_symlink(), 'Missing or symlinked historical attempt: ' + str(path))
    found = {}
    for file in sorted(path.rglob('*')):
        require(not file.is_symlink(), 'Historical attempt contains a symlink: ' + str(file))
        if file.is_file():
            found[str(file.relative_to(path))] = {'bytes': file.stat().st_size, 'sha256': sha(file)}
    return found


def archived_round1_stdout(archive_raw, prior_raw, prior, round1_runner_sha):
    """Read original task bytes, without inventing or restoring a COMPILE.log."""
    require(hashlib.sha256(archive_raw).hexdigest()==ROUND1_EVIDENCE_SHA,
            'Published original round1 evidence archive differs.')
    with tarfile.open(fileobj=io.BytesIO(archive_raw),mode='r:gz') as archive:
        members=archive.getmembers()
        require(len({row.name for row in members})==len(members),'Duplicate original archive members.')

        def member(name):
            row=archive.getmember(name)
            require(row.isfile(),'Original evidence member is not a regular file: '+name)
            return archive.extractfile(row).read()

        stdout_raw=member('STDOUT.log')
        manifest_raw=member('EXPORT_MANIFEST.json')
        require(member('.lake/p25-followup-repairs-attempt001/RUN_RESULT.json')==prior_raw,
                'Archived original result differs from the preserved round1 result.')
    require(len(stdout_raw)==ROUND1_STDOUT_BYTES and hashlib.sha256(stdout_raw).hexdigest()==ROUND1_STDOUT_SHA,
            'Original complete task stdout differs.')
    require(hashlib.sha256(manifest_raw).hexdigest()==ROUND1_EXPORT_MANIFEST_SHA,
            'Original task export manifest differs.')
    manifest=json.loads(manifest_raw)
    require(manifest['source_commit']==PREVIOUS_COMMIT and manifest['task_id']==ROUND1_TASK_ID
            and manifest['stdout_bytes']==ROUND1_STDOUT_BYTES and manifest['stdout_sha256']==ROUND1_STDOUT_SHA,
            'Original export manifest source/task/stdout binding differs.')
    summaries=[]
    terminal=[]
    for line in stdout_raw.decode('utf-8').splitlines():
        if line.startswith('P25_FOLLOWUP_RESULT '):
            terminal.append(json.loads(line.split(' ',1)[1]))
        try:
            value=json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value,dict) and 'successful_closure' in value and 'total' in value:
            summaries.append(value)
    require(len(terminal)==1 and terminal[0]==prior,'Original stdout terminal result differs.')
    require(len(summaries)==1 and canonical_sha(summaries[0])==ROUND1_COMPILE_SUMMARY_SHA,
            'Original stdout does not contain the exact unique historical compile summary.')
    summary=summaries[0]
    require(summary['roots']==prior['compile_roots'] and summary['exit_code']==prior['compile_exit'],
            'Historical stdout compile summary is not bound to the original runner result.')
    provenance={
        'schema':'p25-original-round1-task-stdout-provenance-v1',
        'evidence_kind':'Original complete task stdout; not a separate compiler log or reconstructed log.',
        'original_task_id':ROUND1_TASK_ID,'original_source_commit':PREVIOUS_COMMIT,
        'archive_publication_commit':PUBLICATION,'archive_repository_path':ROUND1_EVIDENCE_ARCHIVE,
        'archive_git_blob':ROUND1_EVIDENCE_BLOB,'archive_sha256':ROUND1_EVIDENCE_SHA,
        'archive_member':'STDOUT.log','stdout_bytes':ROUND1_STDOUT_BYTES,'stdout_sha256':ROUND1_STDOUT_SHA,
        'export_manifest_member':'EXPORT_MANIFEST.json','export_manifest_sha256':ROUND1_EXPORT_MANIFEST_SHA,
        'original_runner_path':OLD+'/p2-followup-repairs/run_followup.py',
        'original_runner_sha256':round1_runner_sha,
        'original_compile_and_audit_logging':'subprocess.call(command, cwd=ROOT) inherited task stdout; no separate COMPILE.log or AUDIT.log was created.',
        'original_result_sha256':PRIOR_RESULT_SHA,'terminal_result_equals_preserved_result':True,
        'historical_compile_summary_canonical_sha256':ROUND1_COMPILE_SUMMARY_SHA,
        'new_evidence_copy_filename':'PRIOR_TASK_STDOUT.log','historical_files_rewritten':False,
        'historical_log_synthesized':False,
    }
    return stdout_raw,summary,provenance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication_commit')
    parser.add_argument('--failed-result-sha256', default=FAILED_RESULT_SHA,
                        help='Independently retained SHA256 of the failed-before-Lean attempt002 RUN_RESULT.json')
    parser.add_argument('--runner-sha256', required=True,
                        help='Independently reviewed SHA256 of this git-external resume runner')
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Run without Python -O; unchanged original gate assertions must remain active.')
    require(args.publication_commit == PUBLICATION, 'Resume only the exact already checked-out round2 publication.')
    require(args.failed_result_sha256 == FAILED_RESULT_SHA, 'Only the independently retained failed preflight is eligible.')
    for value in [args.failed_result_sha256, args.runner_sha256]:
        require(len(value) == 64 and all(c in '0123456789abcdef' for c in value), 'Require full lowercase SHA256 pins.')
    require(sha(__file__) == args.runner_sha256, 'Resume runner differs from the supplied review pin.')
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    sys.dont_write_bytecode = True
    require(output(['git','rev-parse','HEAD']) == PUBLICATION, 'Current HEAD must remain the completed checkout to 6a4bfce.')
    require(not output(['git','status','--porcelain','--untracked-files=no']), 'Tracked worktree is not clean.')
    require(not OUT.exists() and not OUT.is_symlink(), 'Preserve the existing attempt003; refuse to overwrite.')

    def published(commit, path):
        return subprocess.check_output(['git','show',commit + ':' + path], cwd=ROOT)

    trees = {}
    blobs = {}

    def published_source(commit, source_path):
        """Resolve tracked symlinks inside one immutable Git tree, without checkout."""
        if commit not in trees:
            tree = {}
            for item in subprocess.check_output(['git','ls-tree','-rz',commit], cwd=ROOT).split(b'\0'):
                if item:
                    metadata, name = item.split(b'\t',1)
                    mode, kind, object_id = metadata.decode().split()
                    tree[name.decode()] = (mode,kind,object_id)
            trees[commit] = tree
        tree = trees[commit]

        def blob(object_id):
            if object_id not in blobs:
                blobs[object_id] = subprocess.check_output(['git','cat-file','blob',object_id], cwd=ROOT)
            return blobs[object_id]

        path = source_path
        seen = set()
        chain = []
        while True:
            require(path not in seen and len(seen)<64, 'Published symlink cycle/depth at '+source_path)
            seen.add(path)
            row = tree.get(path)
            if row and row[0] in {'100644','100755'}:
                require(row[1]=='blob','Published source is not a file blob: '+path)
                return blob(row[2]), path, chain
            parts = path.split('/')
            link = None
            for count in range(1,len(parts)+1):
                prefix = '/'.join(parts[:count])
                candidate = tree.get(prefix)
                if candidate and candidate[0]=='120000':
                    link = (prefix,candidate,parts[count:])
                    break
            require(link is not None,'Published source or symlink target is missing: '+path)
            prefix,row,rest = link
            target = blob(row[2]).decode()
            require(not posixpath.isabs(target),'Published source symlink leaves repository: '+prefix)
            path = posixpath.normpath(posixpath.join(posixpath.dirname(prefix),target,*rest))
            require(path!='..' and not path.startswith('../'),'Published source symlink escapes repository: '+prefix)
            chain.append({'link_path':prefix,'blob_sha':row[2],'target':target,'resolved_path':path})

    round2_path = ROOT / ROUND2_RUNNER
    require(sha(round2_path) == ROUND2_RUNNER_SHA and round2_path.read_bytes() == published(PUBLICATION,ROUND2_RUNNER),
            'Original round2 runner is not the exact pinned published version.')
    # Load only the pinned original helper definitions. Its guarded main is not
    # called: it would require HEAD=59e and perform the already completed checkout.
    original = types.ModuleType('p25_original_round2_helpers')
    original.__file__ = str(round2_path)
    exec(compile(round2_path.read_bytes(), str(round2_path), 'exec'), original.__dict__)
    require(original.ROOT == ROOT and original.PREVIOUS_COMMIT == PREVIOUS_COMMIT
            and original.FOLDER == ROUND2_FOLDER and original.RUNNER == ROUND2_RUNNER,
            'Original helper constants differ.')
    for path, expected in original.PINS.items():
        require(sha(ROOT/path) == expected and hashlib.sha256(published(PUBLICATION,path)).hexdigest() == expected,
                'Published gate/source-table pin differs: ' + path)
    graph = json.loads((ROOT/ROUND2_FOLDER/'CONTINUATION_SOURCE_CLOSURE.json').read_text())
    old_graph = json.loads((ROOT/OLD/'CONTINUATION_SOURCE_CLOSURE.json').read_text())
    target_document = json.loads((ROOT/ROUND2_FOLDER/'CONTINUATION_AUDIT_TARGETS.json').read_text())
    targets = target_document['modules']
    old_targets = json.loads((ROOT/OLD/'CONTINUATION_AUDIT_TARGETS.json').read_text())['modules']
    selection = json.loads((ROOT/ROUND2_FOLDER/'SOURCE_SELECTION.json').read_text())
    require(graph['roots'] == old_graph['roots'] and len(graph['roots']) == 5
            and set(graph['modules']) == set(old_graph['modules'])
            and len(graph['modules']) == graph['project_modules'] == 377, 'Source graph scope changed.')
    require(len(targets) == len(set(targets)) == target_document['count'] == 69
            and len(old_targets) == 67 and len(selection['added_owned_targets']) == 2
            and set(targets) == set(old_targets) | set(selection['added_owned_targets'])
            and set(targets) <= set(graph['modules']), 'Owned audit scope changed.')
    sys.path.insert(0,str(ROOT/'verification/part2'))
    from inspect_winner9_owner_native import imports
    from winner9_external_snapshot import ExternalSnapshot

    def project_imports(text):
        return [name for name in imports(text) if name.startswith('ImbalancedChen.')]

    changes = []
    required = dict(original.PINS)
    required[ROUND2_RUNNER] = ROUND2_RUNNER_SHA
    required[ORIGINAL_ARCHIVE] = ORIGINAL_ARCHIVE_SHA
    for name, old_row in old_graph['modules'].items():
        row = graph['modules'][name]
        # Historical source provenance comes from the old Git object, never
        # from today's HEAD or today's six repaired source files.
        old_bytes, _, _ = published_source(PREVIOUS_COMMIT,old_row['source'])
        require(hashlib.sha256(old_bytes).hexdigest() == old_row['sha256']
                and project_imports(old_bytes.decode()) == old_row['imports'], 'Historical graph mismatch: ' + name)
        require(row['source'] == old_row['source'] and row['imports'] == old_row['imports'], 'Import graph changed: ' + name)
        current = (ROOT/row['source']).read_bytes()
        published_bytes, _, _ = published_source(PUBLICATION,row['source'])
        require(hashlib.sha256(current).hexdigest() == row['sha256'] and current == published_bytes
                and project_imports(current.decode()) == row['imports'], 'Current source mismatch: ' + name)
        required[row['source']] = row['sha256']
        if old_row['sha256'] != row['sha256']:
            changes.append({'module':name,'source':row['source'],'before_sha256':old_row['sha256'],'after_sha256':row['sha256']})
    require(changes == selection['changed_sources'] and len(changes) == 6, 'The six published repairs changed.')
    require(len(required) == 394 and canonical_sha(required) == REQUIRED_394_SHA, 'Required path/source table changed.')
    require(all((ROOT/path).is_file() and sha(ROOT/path)==expected for path,expected in required.items()),
            'A required retained path is missing or differs.')
    source_links = {}
    for path, expected in required.items():
        contents,resolved,chain = published_source(PUBLICATION,path)
        require(hashlib.sha256(contents).hexdigest()==expected,'Published dereferenced source differs: '+path)
        if chain:
            source_links[path] = {'resolved_repo_path':resolved,'chain':chain}

    def source_links_match():
        return all((ROOT/path).resolve()==(ROOT/row['resolved_repo_path']).resolve()
                   and all((ROOT/step['link_path']).is_symlink()
                           and os.readlink(ROOT/step['link_path'])==step['target'] for step in row['chain'])
                   for path,row in source_links.items())

    require(source_links_match(),'Current source symlink identities differ from the publication.')

    prior_path = PRIOR_OUT/'RUN_RESULT.json'
    prior_raw = prior_path.read_bytes()
    require(hashlib.sha256(prior_raw).hexdigest() == PRIOR_RESULT_SHA, 'Original round1 result changed.')
    prior = json.loads(prior_raw)
    require(prior['source_commit'] == PREVIOUS_COMMIT and prior.get('ended_utc') and 'audit_exit' in prior
            and prior['project_modules'] == 377 and prior['owned_targets'] == 67
            and prior['runner_sha256'] == original.PINS[OLD+'/p2-followup-repairs/run_followup.py'],
            'Original round1 source/result binding differs.')
    require(output(['git','rev-parse',PUBLICATION+':'+ROUND1_EVIDENCE_ARCHIVE])==ROUND1_EVIDENCE_BLOB,
            'Published original round1 archive Git blob differs.')
    round1_runner=OLD+'/p2-followup-repairs/run_followup.py'
    require(hashlib.sha256(published(PREVIOUS_COMMIT,round1_runner)).hexdigest()==original.PINS[round1_runner],
            'Original round1 runner logging provenance differs.')
    prior_stdout,prior_compiled,prior_stdout_provenance=archived_round1_stdout(
        published(PUBLICATION,ROUND1_EVIDENCE_ARCHIVE),prior_raw,prior,original.PINS[round1_runner])
    require(prior_compiled and prior_compiled['total']==377 and prior_compiled['successful_closure']==315,
            'Historical 315-module compile summary differs.')
    old_audit_summary_path = ROOT/'.lake/p2-private/audit/p25-followup-repairs-owned-audit.json'
    require(json.loads(old_audit_summary_path.read_text()) == prior['audit_summary']
            and prior['audit_summary']['requested']==67 and prior['audit_summary']['accepted']==31,
            'Historical 31-owner audit summary differs.')
    failed_files = directory_files(FAILED_OUT)
    require(set(failed_files)==set(FAILED_FILE_SHA) and
            all(failed_files[name]['sha256']==expected for name,expected in FAILED_FILE_SHA.items()),
            'Attempt002 file set or retained byte identities differ; before-Lean failure is not established.')
    failed_path = FAILED_OUT/'RUN_RESULT.json'
    require(sha(failed_path)==args.failed_result_sha256, 'Failed attempt002 result differs from supplied pin.')
    failed = json.loads(failed_path.read_text())
    require(failed['schema']=='p25-round2-pinned-compile-and-owned-audit-v1'
            and failed['source_commit']==PUBLICATION and failed['previous_commit']==PREVIOUS_COMMIT
            and failed['runner_sha256']==ROUND2_RUNNER_SHA and failed['prior_run_result_sha256']==PRIOR_RESULT_SHA
            and failed['project_modules']==377 and failed['owned_targets']==69
            and failed['compile_roots']==graph['roots'] and failed['source_and_gate_pins']==original.PINS
            and failed['external_snapshot_sha256']==original.SNAPSHOT_SHA and failed['accepted'] is False
            and failed['finite_guard_credit'] is False and failed['P2_5_proved'] is False
            and failed['disk_free_start'] < MIN_FREE_BYTES and not (ABSENT_BEFORE_LEAN_KEYS & set(failed)),
            'Attempt002 is not the exact failure at the unchanged disk preflight gate.')
    require((FAILED_OUT/'PRIOR_RUN_RESULT.json').read_bytes()==prior_raw, 'Archived original result differs.')
    previous = json.loads((FAILED_OUT/'PREVIOUS_RECORDS.json').read_text())
    packed_records = (FAILED_OUT/'previous-records.json.gz').read_bytes()
    archived_records = gzip.decompress(packed_records)
    records_path = ROOT/'.lake/p2-private/records.json'
    require(previous['source_commit']==PREVIOUS_COMMIT and len(archived_records)==previous['bytes']
            and hashlib.sha256(archived_records).hexdigest()==previous['sha256']
            and hashlib.sha256(packed_records).hexdigest()==previous['compressed_sha256']
            and records_path.read_bytes()==archived_records, 'Old cache records changed after the before-Lean failure.')
    json.loads(archived_records)
    for name in ['p25-unused-cache-reclamation-second-recovery.json','p25-empty-baseline-setup.json']:
        require((FAILED_OUT/name).read_bytes()==(ROOT/'.lake'/name).read_bytes(),'Original recovery/setup receipt changed: '+name)
    historical_files = {str(path):sha(path) for path in
                        [prior_path,old_audit_summary_path,
                         ROOT/'.lake/p25-unused-cache-reclamation-second-recovery.json',
                         ROOT/'.lake/p25-empty-baseline-setup.json']}
    original.baseline_checks()
    external = ExternalSnapshot(original.SNAPSHOT, lean=original.LEAN, mathlib_pin=original.MATHLIB_COMMIT,
                                project_lib=ROOT/'.lake/p2-private/lib')
    external_before = external.verify()
    require(external_before==failed['external_before'],'Qualified external environment changed since failed preflight.')
    require(failed['source_tree']==output(['git','rev-parse','HEAD^{tree}']), 'Current publication tree differs.')
    prior_file_map = directory_files(PRIOR_OUT)
    OUT.mkdir(parents=True,exist_ok=False)
    # Exact byte copies retain the historical 59e origin even though HEAD is 6a.
    for name in ['PREVIOUS_RECORDS.json','previous-records.json.gz','PRIOR_RUN_RESULT.json']:
        shutil.copyfile(FAILED_OUT/name,OUT/name)
    shutil.copyfile(failed_path,OUT/'FAILED_PREFLIGHT_RUN_RESULT.json')
    shutil.copyfile(__file__,OUT/'EXECUTED_RESUME_RUNNER.py')
    (OUT/'PRIOR_TASK_STDOUT.log').write_bytes(prior_stdout)
    save_json(OUT/'PRIOR_TASK_STDOUT_PROVENANCE.json',prior_stdout_provenance)
    require(original.compile_summary(OUT/'PRIOR_TASK_STDOUT.log')==prior_compiled,
            'Unchanged original summary parser disagrees with the preserved task stdout.')
    prior_evidence_files={str(path):sha(path) for path in
                          [OUT/'PRIOR_TASK_STDOUT.log',OUT/'PRIOR_TASK_STDOUT_PROVENANCE.json']}
    save_json(OUT/'PRESERVED_ATTEMPT002_FILES.json',failed_files)
    save_json(OUT/'REQUIRED_PATHS.json',required)
    save_json(OUT/'PUBLISHED_SOURCE_SYMLINKS.json',source_links)
    cache_origin = {'source_commit':PREVIOUS_COMMIT,'current_checkout_commit':PUBLICATION,
                    'records_sha256':previous['sha256'],'records_bytes':previous['bytes'],
                    'archived_from_attempt002_without_relabelling':True,
                    'prior_run_result_sha256':PRIOR_RESULT_SHA,'historical_successful_modules':315,
                    'historical_accepted_owned_targets':31,'current_new_Lean_stages_before_resume':0,
                    'reuse_requires_unchanged_original_driver_source_dependency_and_environment_validation':True}
    save_json(OUT/'CACHE_ORIGIN.json',cache_origin)
    state = {'schema':'p25-round3-resume-pinned-compile-and-owned-audit-v2','source_commit':PUBLICATION,
             'previous_commit':PREVIOUS_COMMIT,'source_tree':failed['source_tree'],
             'runner_sha256':args.runner_sha256,'original_round2_runner_sha256':ROUND2_RUNNER_SHA,
             'started_utc':now(),'prior_run_result_sha256':PRIOR_RESULT_SHA,
             'failed_preflight_result_sha256':args.failed_result_sha256,
             'prior_task_stdout_provenance':prior_stdout_provenance,
             'failed_attempt002_preserved_before':failed_files,'cache_origin':cache_origin,
             'required_path_count':394,'required_paths_canonical_sha256':REQUIRED_394_SHA,
             'published_source_symlinks':source_links,
             'baseline_root':str(original.BASELINE),'baseline_commit':original.BASELINE_COMMIT,
             'baseline_has_build_objects':False,'mathlib_commit':original.MATHLIB_COMMIT,
             'external_before':external_before,'project_modules':377,'owned_targets':69,
             'compile_roots':graph['roots'],'source_and_gate_pins':original.PINS,
             'external_snapshot_sha256':sha(original.SNAPSHOT),'disk_free_start':shutil.disk_usage(ROOT).free,
             'minimum_free_bytes':MIN_FREE_BYTES,'scope':selection['scope'],
             'accepted':False,'finite_guard_credit':False,'P2_5_proved':False,
             'git_checkout_or_reset_performed':False,'sparse_worktree_mutation_performed':False,
             'deleted_cached_objects':False,'historical_source_commit_relabelled':False}
    receipt=OUT/'RUN_RESULT.json'

    def save():
        save_json(receipt,state)

    def preserved_history():
        return (directory_files(FAILED_OUT)==failed_files and directory_files(PRIOR_OUT)==prior_file_map
                and all(sha(path)==expected for path,expected in historical_files.items())
                and all(sha(path)==expected for path,expected in prior_evidence_files.items()))

    try:
        save()
        require(state['disk_free_start']>=MIN_FREE_BYTES,'Original 1 GiB disk threshold not met; no Lean stage started.')
        require(preserved_history() and sha(records_path)==previous['sha256'],'Historical state changed before input preparation.')
        with (OUT/'INPUT_PREPARATION.log').open('w') as log:
            state['input_preparation_exit']=subprocess.call([sys.executable,str(ROOT/OLD/'prepare-q96-original-inputs.py')],
                cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        save()
        require(state['input_preparation_exit']==0,'Original input preparation failed.')
        require(preserved_history() and sha(records_path)==previous['sha256'],'Historical records changed before compilation.')
        command=[sys.executable,'verification/part2/run_winner9_private_checks.py',*graph['roots'],
                 '--baseline-root',str(original.BASELINE),'--workers','1','--threads','1','--memory-mb','11264',
                 '--external-snapshot',str(original.SNAPSHOT),'--time-budget-seconds','1400']
        state['compile_command']=command
        save()
        state['compile_exit']=original.logged_call(command,OUT/'COMPILE.log')
        state['compile_summary']=original.compile_summary(OUT/'COMPILE.log')
        state['compile_log_sha256']=sha(OUT/'COMPILE.log')
        save()
        original.baseline_checks()
        priority=[row['module'] for row in changes]
        ordered=priority+[name for name in targets if name not in priority]
        require(len(ordered)==69 and set(ordered)==set(targets),'Audit order/scope differs.')
        summary_name='p25-round3-repairs-owned-audit.json'
        summary=ROOT/'.lake/p2-private/audit'/summary_name
        require(not summary.exists(),'Preserve an existing round3 audit summary.')
        command=[sys.executable,'verification/part2/run_winner9_private_audit.py',*ordered,
                 '--summary-name',summary_name,'--memory-mb','11264','--external-snapshot',str(original.SNAPSHOT)]
        state['audit_command']=command
        save()
        state['audit_exit']=original.logged_call(command,OUT/'AUDIT.log')
        state['audit_summary']=json.loads(summary.read_text()) if summary.is_file() else None
        state['audit_log_sha256']=sha(OUT/'AUDIT.log')
        save()
        original.baseline_checks()
        state['external_after']=external.verify()
        state['source_after_matches']=all(sha(ROOT/row['source'])==row['sha256'] and
            project_imports((ROOT/row['source']).read_text())==row['imports'] for row in graph['modules'].values()) and source_links_match()
        state['gate_after_matches']=all(sha(ROOT/path)==expected for path,expected in required.items())
        state['resume_runner_after_matches']=sha(__file__)==args.runner_sha256 and sha(OUT/'EXECUTED_RESUME_RUNNER.py')==args.runner_sha256
        state['snapshot_after_matches']=sha(original.SNAPSHOT)==original.SNAPSHOT_SHA and state['external_after']==external_before
        state['head_after_matches']=output(['git','rev-parse','HEAD'])==PUBLICATION and not output(['git','status','--porcelain','--untracked-files=no'])
        state['historical_attempts_after_match']=preserved_history()
        state['baseline_after_matches']=True
        keys=['source_after_matches','gate_after_matches','resume_runner_after_matches','snapshot_after_matches',
              'head_after_matches','historical_attempts_after_match','baseline_after_matches']
        state['accepted']=original.accepted_summaries(state['compile_exit'],state['audit_exit'],state['compile_summary'],
            state['audit_summary'],graph['roots'],targets) and all(state[k] for k in keys)
        state['ended_utc']=now()
        state['disk_free_end']=shutil.disk_usage(ROOT).free
        save()
        print('P25_ROUND3_RESUME_RESULT '+json.dumps(state),flush=True)
        return 0 if state['accepted'] else 1
    except Exception as error:
        state.update(accepted=False,error=str(error),traceback=traceback.format_exc(),ended_utc=now(),
                     disk_free_end=shutil.disk_usage(ROOT).free)
        save()
        print('P25_ROUND3_RESUME_FAILED '+str(error),flush=True)
        return 1


if __name__=='__main__':
    sys.exit(main())
