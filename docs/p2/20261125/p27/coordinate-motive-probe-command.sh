set -euo pipefail
python3 -B - <<'P27_COORDINATE_MOTIVE_PROBE'
from pathlib import Path
import hashlib, json, os, subprocess, time

root = Path.cwd()
assert root == Path('/workspace/p2-7-20261125')
out = root / '.lake/p27-coordinate-probe/attempt-001'
out.mkdir(parents=True, exist_ok=False)
compiler = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
mathlib = Path('/workspace/compile-deps/mathlib')
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib, text=True).strip()
assert revision == 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
compiler_sha = hashlib.sha256(compiler.read_bytes()).hexdigest()
assert compiler_sha == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(str(p) for p in [mathlib / '.lake/build/lib/lean', *sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))])
results = []
for stage in ('before', 'after'):
    source = root / 'docs/p2/20261125/p27' / f'coordinate-motive-probe-{stage}.lean'
    raw = source.read_bytes()
    local = out / f'{stage}.lean'
    local.write_bytes(raw)
    command = [str(compiler), '-t0', '-j1', '-M8192', '-DwarningAsError=true', str(local)]
    started = time.monotonic()
    run = subprocess.run(command, cwd=out, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    (out / f'{stage}.log').write_bytes(run.stdout)
    row = {'stage': stage, 'source_sha256': hashlib.sha256(raw).hexdigest(), 'source_bytes': len(raw), 'command': command, 'exit_code': run.returncode, 'elapsed_seconds': round(time.monotonic() - started, 3), 'log_bytes': len(run.stdout), 'log_sha256': hashlib.sha256(run.stdout).hexdigest()}
    results.append(row)
    print('P27_COORDINATE_PROBE_RESULT ' + json.dumps(row), flush=True)
    print('P27_COORDINATE_PROBE_LOG_BEGIN ' + stage, flush=True)
    print(run.stdout.decode('utf-8', errors='replace'), end='', flush=True)
    print('P27_COORDINATE_PROBE_LOG_END ' + stage, flush=True)
receipt = {'schema': 'p27-coordinate-motive-expression-probe-v1', 'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), 'compiler_sha256': compiler_sha, 'mathlib_revision': revision, 'results': results, 'project_modules_compiled': 0, 'module_acceptance': False, 'kernel_credit': False}
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('P27_COORDINATE_PROBE_RECEIPT ' + json.dumps(receipt), flush=True)
assert results[1]['exit_code'] == 0, 'The typed coordinate probe failed; project compilation was not started.'
P27_COORDINATE_MOTIVE_PROBE
