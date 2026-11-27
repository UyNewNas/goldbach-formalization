"""Stage the exact published GroupLog adapter, then run its one new owner."""
from pathlib import Path
from types import ModuleType
import hashlib, json, os, subprocess, sys

sys.dont_write_bytecode = True
os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                   'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
REPO = Path('/workspace/goldbach-formalization')
BASE = '040d46058821746c69c5183b3f6c22792287c4ba'
COMMIT = 'ce08ba304bafb7732c8fd9f27553822f87cfb7d0'
BOOTSTRAP = 'docs/p1/20261127/p15-historical-coefficient-dictionary/deploy_dictionary_formal.py'
ADAPTER = 'docs/p1/20261127/p15-group-log-abel/run_group_log.py'
raw = subprocess.check_output(['git', 'show', BASE + ':' + BOOTSTRAP], cwd=REPO)
assert hashlib.sha256(raw).hexdigest() == 'a73a6f6b8a0f641c0556d65e1aa6cf4092487da37a4e58d07b06e2537ea63f31'
h = ModuleType('original_staging_primitives')
h.__file__ = BOOTSTRAP
exec(compile(raw, BOOTSTRAP, 'exec'), h.__dict__)
before = h.gitstate()
fetch = subprocess.run(['git', '-c', 'maintenance.auto=false', 'fetch', '--quiet', '--no-tags',
                        '--no-write-fetch-head', 'origin', COMMIT], cwd=REPO, capture_output=True)
assert fetch.returncode == 0, 'Exact immutable source fetch failed; no checkout changed'
assert subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, COMMIT], cwd=REPO).returncode == 0
adapter = h.git('show', COMMIT + ':' + ADAPTER)
assert h.fp(adapter) == {'bytes': 21852, 'sha256': '9f618457ddd5dd25b251b153cf5f278bbf37ffead78247a034146efa95c49057'}
dest = h.ROOT / COMMIT / 'published-entrypoints/run_group_log.py'
h.put(dest, adapter)
after = h.gitstate()
assert before == after, 'Original Git state changed'
receipt = {'schema': 'p15_group_log_stage_v1', 'source_commit': COMMIT, 'adapter_path': str(dest),
           'adapter': h.fp(adapter), 'original_git_state_unchanged': True,
           'git_before': before, 'git_after': after, 'normal_or_kernel_commands_executed': 0,
           'new_owner_accepted': False, 'whole_P1_5_complete': False}
receipt_path = dest.parent / 'GROUPLOG_STAGE_RECEIPT.json'
h.put(receipt_path, (json.dumps(receipt, indent=2, sort_keys=True) + '\n').encode())
print(json.dumps({'stage_receipt': str(receipt_path), 'stage_receipt_binding': h.fp(receipt_path.read_bytes()),
                  'source_commit': COMMIT, 'adapter': h.fp(adapter), 'original_git_state_unchanged': True}), flush=True)
result = subprocess.run(['python3', '-B', str(dest), '--source-commit', COMMIT, '--run'],
                        cwd='/workspace/blue-member-build')
sys.exit(result.returncode)
