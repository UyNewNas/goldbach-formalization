from pathlib import Path
import hashlib
import json
import os

COMMIT = '6d9072f7b33332eaf5ecfff22876e0404cd6ab51'
MODULE = 'ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy'
PROJECT = Path('/workspace/blue-member-build')
BASE = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1') / COMMIT
INSTALL = Path('/workspace/p1-complete-proof/20261126-p15-trimlog-source-install-v1') / COMMIT


def fp(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    assert path.is_file() and not path.is_symlink(), str(path)
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


run = BASE / 'runs/attempt-00000'
result = json.loads((run / 'RESULT.json').read_bytes())
assert result['identity']['source_commit'] == COMMIT
out = {
    'source_commit': COMMIT,
    'module': MODULE,
    'source': fp(PROJECT / 'ImbalancedChen/P1OriginalSingletonAtlasTrimLogAccuracy.lean'),
    'run': {name: fp(run / name) for name in (
        'RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
        'GIT_BEFORE.json', 'GIT_AFTER.json', 'executed-trimlog.py',
        'serialized-trimlog-command.json', 'serialized-trimlog.log')},
    'installation': {name: fp(INSTALL / 'runs/attempt-00000' / name) for name in (
        'SOURCE_INSTALL_RESULT.json', 'WORKER_RESULT.json', 'OLD_CONTEXT_BEFORE.json',
        'OLD_CONTEXT_AFTER.json', 'GIT_BEFORE.json', 'GIT_AFTER.json',
        'executed-installer.py', 'serialized-trimlog-install-command.json',
        'serialized-trimlog-install.log')},
    'result_summary': {key: result.get(key) for key in (
        'targets', 'accepted_owners', 'failures', 'worker_exit_code', 'new_owner_accepted',
        'dispatch_error', 'preservation_error', 'git_error', 'whole_P1_5_complete')},
    'final_stock': result.get('final_stock_readiness'),
}
owner = result.get('owner')
if owner is not None:
    binding = owner['binding']
    normal_path = Path(binding['normal_receipt']['path'])
    audit_path = Path(binding['audits'][0]['result']['path'])
    normal = json.loads(normal_path.read_bytes())
    audit = json.loads(audit_path.read_bytes())
    out['owner'] = owner
    out['normal'] = fp(normal_path)
    out['audit_plan'] = fp(binding['audits'][0]['plan']['path'])
    out['audit_result'] = fp(audit_path)
    out['normal_command'] = normal['normal_command']
    out['normal_source_closure_count'] = len(normal['dependency_context']['project_sources'])
    out['audit_summary'] = {key: audit[key] for key in (
        'status', 'total_owned_exports', 'total_public_exports',
        'full_owned_including_private_generated', 'only_standard_axioms',
        'kernel_commands', 'audit_command', 'stock_readiness_before', 'stock_readiness_after')}
else:
    normal_dir = BASE / MODULE / 'normal' / MODULE / 'attempt-00000'
    command = normal_dir / 'normal-command.json'
    if command.is_file():
        row = json.loads(command.read_bytes())
        log = Path(row['log'])
        out['failed_normal'] = {'command': row, 'command_file': fp(command), 'log': fp(log),
            'error_tail': log.read_text()[-9000:]}
print(json.dumps(out, sort_keys=True))
