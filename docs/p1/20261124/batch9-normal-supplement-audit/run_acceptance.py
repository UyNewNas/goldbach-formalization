#!/usr/bin/env python3
"""Run only the existing named-kernel/full-owned acceptance for Batch9 passes."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--commit', required=True)
args = parser.parse_args()
git = Path('/workspace/goldbach-formalization')
project = Path('/workspace/blue-member-build')
root = Path('/workspace/p1-complete-proof/20261124-resume/batch9-normal-audit-bootstrap')
root.mkdir(exist_ok=False)
plan_path = 'docs/p1/20261124/batch9-normal-supplement-audit/AUDIT_PLAN.json'
runner_path = 'docs/p1/20261124/normal-supplement-audit/run_parallel_acceptance_multibatch.py'
plan_sha = '0c9032290fa705820ca1d0d167b91fd0ef169394599efaab7afa2463c92050a5'
runner_sha = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def run(name, command, cwd):
    record = {'argv': command, 'cwd': str(cwd),
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    save(root / (name + '-started.json'), record)
    start = time.monotonic()
    log = root / (name + '.log')
    with log.open('xb') as stream:
        result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    record.update(exit_code=result.returncode, elapsed_seconds=time.monotonic() - start,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  log=str(log), log_bytes=log.stat().st_size, log_sha256=sha(log.read_bytes()))
    save(root / (name + '-command.json'), record)
    print(json.dumps({'stage': name, 'exit_code': result.returncode,
                      'seconds': record['elapsed_seconds']}), flush=True)
    return result.returncode


before_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=git)
before_status = subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=git)
(root / 'original-git-status-before.bin').write_bytes(before_status)
assert run('fetch-published-branch', ['git', 'fetch', 'origin',
           'codex/p1-final-acceptance-20261124'], git) == 0
assert run('published-ancestor', ['git', 'merge-base', '--is-ancestor',
           args.commit, 'FETCH_HEAD'], git) == 0
reads = []
for source, name, expected in [(plan_path, 'AUDIT_PLAN.json', plan_sha),
                               (runner_path, 'run_parallel_acceptance_multibatch.py', runner_sha)]:
    command = ['git', 'show', args.commit + ':' + source]
    raw = subprocess.check_output(command, cwd=git)
    assert sha(raw) == expected
    with (root / name).open('xb') as stream:
        stream.write(raw)
    reads.append({'argv': command, 'path': str(root / name), 'bytes': len(raw), 'sha256': sha(raw)})
save(root / 'GIT_SHOW_READS.json', reads)
plan = json.loads((root / 'AUDIT_PLAN.json').read_bytes())
assert plan['lanes'][0]['modules'] == [] and len(plan['lanes'][1]['modules']) == 12
receipt = Path(plan['receipt_root'])
runner = root / 'run_parallel_acceptance_multibatch.py'
assert run('prepare-only', ['python3', str(runner), '--plan',
           str(root / 'AUDIT_PLAN.json'), '--prepare-only'], project) == 0
command = ['python3', '/workspace/blue-build-tools/serialize_validation_lane.py',
           '--state', plan['runtime_states'][1], '--receipt', str(receipt / 'lane-1/VALIDATION_LANE.json'),
           'python3', str(runner), '--plan', str(receipt / 'AUDIT_PLAN.json'),
           '--receipt-root', str(receipt), '--lane', '1']
code = run('audit12-full', command, project)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=git) == before_head
assert subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=git) == before_status
result = {'commit': args.commit, 'exit_code': code, 'original_dirty_git_unchanged': True,
          'normal_compilation_not_repeated': True, 'plan_sha256': plan_sha,
          'runner_sha256': runner_sha, 'whole_P1_complete': False}
if code == 0:
    raw = (receipt / 'lane-1/VALIDATION_RESULTS.json').read_bytes()
    audit = json.loads(raw)
    assert audit['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
    assert len(audit['modules']) == 12 and audit['plan_sha256'] == plan_sha
    result.update(status=audit['status'], total_owned_exports=audit['total_owned_exports'],
                  total_public_exports=audit['total_public_exports'], receipt_sha256=sha(raw))
else:
    result['status'] = 'ACCEPTANCE_NOT_COMPLETE'
save(root / 'RESULT.json', result)
print('AUDIT12_RESULT ' + json.dumps(result), flush=True)
raise SystemExit(code)
