"""Pinned development environment and bounded direct Lean compiler.

This runner compiles current project sources and their project imports. It never
updates dependencies. Direct success is not aggregate, kernel, or axiom success.
"""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
STATE = ROOT / '.lake/takeover-p0'
BIN = Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux/bin')
PROVIDERS = Path('/home/slava/codex-lean-ve/native-packages')
BUILD = STATE / 'direct/lib/lean'
LOCKS = STATE / 'locks'
MEMO = {}
for directory in [STATE, BUILD, LOCKS]:
    directory.mkdir(parents=True, exist_ok=True)
if not (STATE / 'setup.json').exists() or json.loads((STATE / 'setup.json').read_text()).get('status') != 'PASS':
    raise RuntimeError('P0 environment setup has not finished successfully; no compiler started')

def source_and_object(module):
    relative = Path(module.replace('.', '/'))
    if module == 'ImbalancedChen' or module.startswith('ImbalancedChen.'):
        return ROOT / relative.with_suffix('.lean'), BUILD / relative.with_suffix('.olean')
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    for package in packages:
        provider = PROVIDERS / package['name']
        source = provider / relative.with_suffix('.lean')
        if source.is_file():
            return source, provider / '.lake/build/lib/lean' / relative.with_suffix('.olean')
    return None, None

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def environment():
    env = os.environ.copy()
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    env['LEAN_PATH'] = ':'.join(map(str, [BUILD, *[
        PROVIDERS / p['name'] / '.lake/build/lib/lean' for p in packages]]))
    env['PATH'] = str(STATE / 'bin') + ':' + str(BIN) + ':/usr/local/bin:/usr/bin:/bin'
    env['LEAN_NUM_THREADS'] = '2'
    env.pop('LEAN_SRC_PATH', None)
    return env

def imports(source):
    text = source.read_text()
    # Imports precede declarations here; nested block comments are masked.
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
    depth = 0
    code = []
    i = 0
    while i < len(text):
        if text[i:i+2] == '/-': depth += 1; i += 2
        elif depth and text[i:i+2] == '-/': depth -= 1; i += 2
        elif depth: i += 1
        elif text[i:i+2] == '--':
            i = text.find('\n', i)
            if i < 0: break
        else: code.append(text[i]); i += 1
    return [m for line in ''.join(code).splitlines()
            if line.strip().startswith('import ')
            for m in line.strip().split()[1:]
            if m and not m.startswith('--')]

def acquire_slot():
    while True:
        for index in range(2):
            lock = (LOCKS / f'compiler-{index}.lock').open('a+')
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return lock
            except BlockingIOError:
                lock.close()
        time.sleep(0.25)

def compile_module(module, force=False, strict=False):
    source, obj = source_and_object(module)
    if source is None:
        # Lean's own installed modules have no project source and are immutable.
        installed = BIN.parent / 'lib/lean' / (module.replace('.', '/') + '.olean')
        if installed.is_file(): return digest(installed)
        raise RuntimeError(f'Missing source/provider: {module}')
    external = not (module == 'ImbalancedChen' or module.startswith('ImbalancedChen.'))
    if external and obj.exists(): return digest(obj)
    if not source.is_file(): raise RuntimeError(f'Missing source: {source}')
    if not force and not strict and module in MEMO:
        return MEMO[module]
    module_lock = (LOCKS / (module + '.lock')).open('a+')
    with module_lock:
        fcntl.flock(module_lock, fcntl.LOCK_EX)
        deps = {dep: compile_module(dep) for dep in imports(source)}
        before = digest(source)
        cache = STATE / 'cache' / (module + '.json')
        if not force and cache.exists() and obj.exists():
            saved = json.loads(cache.read_text())
            if (saved.get('status') == 'PASS' and (not strict or saved.get('warnings_as_errors')) and saved['source_sha256'] == before
                    and saved['dependencies'] == deps and saved['object_sha256'] == digest(obj)):
                MEMO[module] = saved['object_sha256']
                return saved['object_sha256']
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        out = STATE / 'direct-runs' / (stamp + '-' + module)
        out.mkdir(parents=True)
        obj.parent.mkdir(parents=True, exist_ok=True)
        compile_root = source.parents[len(module.split('.'))-1] if external else ROOT
        source_arg = str(source.relative_to(compile_root))
        command = [str(BIN / 'lean'), '-t0', *(['-DwarningAsError=true'] if strict else []), '-o', str(obj), source_arg]
        record = {'status':'WAITING_FOR_COMPILER_SLOT','module':module,'runner_pid':os.getpid(),
                  'source_sha256':before,'dependencies':deps,'command':command,'cwd':str(compile_root),'warnings_as_errors':strict,
                  'scope':'direct current-source compilation (requested leaf warnings-as-errors; prerequisites ordinary Lake-style warnings); no aggregate/kernel/axiom claim'}
        receipt = out / 'receipt.json'
        receipt.write_text(json.dumps(record, indent=2)+'\n')
        slot = acquire_slot()
        with slot, (out / 'stdout.log').open('wb') as log:
            started = time.monotonic()
            proc = subprocess.Popen(command, cwd=compile_root, env=environment(), stdout=log, stderr=subprocess.STDOUT)
            record.update(status='RUNNING',child_pid=proc.pid)
            receipt.write_text(json.dumps(record, indent=2)+'\n')
            code = proc.wait()
        record.update(exit_code=code,seconds=round(time.monotonic()-started,3),source_sha256_after=digest(source))
        record['dependency_objects_after'] = {dep: digest(source_and_object(dep)[1])
            if source_and_object(dep)[1] is not None else value for dep, value in deps.items()}
        record['status'] = 'PASS' if code == 0 and record['source_sha256_after'] == before and record['dependency_objects_after'] == deps else 'FAILED'
        if record['status'] == 'PASS': record['object_sha256'] = digest(obj)
        receipt.write_text(json.dumps(record, indent=2)+'\n')
        print(json.dumps({'module':module,'status':record['status'],'seconds':record['seconds'],'receipt':str(receipt)}), flush=True)
        if record['status'] != 'PASS':
            print((out / 'stdout.log').read_text(), flush=True)
            raise RuntimeError(f'Compilation failed: {module}; {receipt}')
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_text(json.dumps(record, indent=2)+'\n')
        MEMO[module] = record['object_sha256']
        return record['object_sha256']

if __name__ == '__main__':
    if sys.argv[1:] == ['--environment']:
        print(json.dumps({k:v for k,v in environment().items() if k.startswith('LEAN') or k == 'PATH'},indent=2))
    else:
        name = sys.argv[1]
        if name.endswith('.lean'): name = name[:-5].replace('/', '.')
        if '.' not in name: name = 'ImbalancedChen.' + name
        compile_module(name, force='--force' in sys.argv[2:], strict=True)
