"""Local proof continuation: exact-source cache reuse and one bounded compiler.

No process starts unless --compile is supplied. This is development evidence,
not a kernel, type, axiom, or aggregate acceptance gate.
"""
from pathlib import Path
import argparse
import datetime
import fcntl
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

DEFAULT_ROOT = Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
OLD = Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-integration/.lake/takeover-p0')
BIN = Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux/bin')
PROVIDERS = Path('/home/slava/codex-lean-ve/native-packages')
PARTS = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def imports(path):
    text = path.read_text()
    depth = 0
    code = []
    i = 0
    while i < len(text):
        if text[i:i + 2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text[i:i + 2] == '--':
            i = text.find('\n', i)
            if i < 0:
                break
        else:
            code.append(text[i])
            i += 1
    return [m for line in ''.join(code).splitlines()
            if line.strip().startswith('import ')
            for m in line.strip().split()[1:]]


class Runtime:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.state = self.root / '.lake/proof-continuation'
        self.build = self.state / 'lib/lean'
        self.packages = json.loads((self.root / 'lake-manifest.json').read_text())['packages']
        self.memo = {}
        self.remote = []
        remote_index = self.state / 'verified-remote-producers.json'
        if remote_index.is_file():
            self.remote = json.loads(remote_index.read_text())['entries']
        for package in self.packages:
            provider = PROVIDERS / package['name']
            rev = subprocess.check_output(['git', '-C', str(provider), 'rev-parse', 'HEAD'], text=True).strip()
            if rev != package['rev']:
                raise RuntimeError(f'Provider revision mismatch: {package["name"]}')
            subprocess.run(['git', '-C', str(provider), 'diff', '--quiet', 'HEAD', '--'], check=True)

    def project(self, module):
        return module == 'ImbalancedChen' or module.startswith('ImbalancedChen.')

    def paths(self, module):
        rel = Path(module.replace('.', '/'))
        if self.project(module):
            return self.root / rel.with_suffix('.lean'), self.build / rel.with_suffix('.olean')
        for package in self.packages:
            source = PROVIDERS / package['name'] / rel.with_suffix('.lean')
            if source.is_file():
                return source, PROVIDERS / package['name'] / '.lake/build/lib/lean' / rel.with_suffix('.olean')
        return None, BIN.parent / 'lib/lean' / rel.with_suffix('.olean')

    def parts(self, obj):
        stem = str(obj)[:-len('.olean')]
        return {suffix: sha(Path(stem + suffix)) for suffix in PARTS if Path(stem + suffix).is_file()}

    def pins(self):
        return {name: sha(self.root / name) for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')}

    def binding(self, module, dependencies):
        src, _ = self.paths(module)
        return {'source_sha256': sha(src), 'direct_source_sha256': {
            d: sha(self.paths(d)[0]) if self.paths(d)[0] else None for d in dependencies},
            'dependencies': dependencies, 'pins': self.pins(),
            'dependency_parts': {d: self.parts(self.paths(d)[1]) for d in dependencies},
            'lean_wrapper_sha256': sha(BIN / 'lean'), 'lean_real_sha256': sha(BIN / 'lean.real')}

    def environment(self):
        env = os.environ.copy()
        env['LEAN_PATH'] = ':'.join(str(p) for p in [self.build, *[
            PROVIDERS / x['name'] / '.lake/build/lib/lean' for x in self.packages]])
        env['PATH'] = str(BIN) + ':/usr/local/bin:/usr/bin:/bin'
        env['LEAN_NUM_THREADS'] = '2'
        env.pop('LEAN_SRC_PATH', None)
        return env

    def plan(self, module):
        seen = set()
        nodes = []
        def visit(name):
            if name in seen:
                return
            seen.add(name)
            src, obj = self.paths(name)
            if src:
                for dep in imports(src):
                    visit(dep)
            old = OLD / 'cache' / (name + '.json')
            row = {'module': name, 'source': str(src) if src else None,
                   'source_sha256': sha(src) if src else None, 'object_exists': obj.exists()}
            if self.project(name) and old.exists():
                c = json.loads(old.read_text())
                row['old_source_exact'] = c.get('source_sha256') == row['source_sha256']
                row['old_cache_status'] = c.get('status')
            nodes.append(row)
        visit(module)
        return {'target': module, 'root': str(self.root), 'pins': self.pins(),
                'nodes': nodes, 'scope': 'read-only source/object plan; no compiler invoked'}

    def old_candidate(self, module, deps, strict):
        cp = OLD / 'cache' / (module + '.json')
        obj = OLD / 'direct/lib/lean' / Path(module.replace('.', '/')).with_suffix('.olean')
        if not cp.exists() or not obj.exists():
            return None
        c = json.loads(cp.read_text())
        src, _ = self.paths(module)
        if c.get('status') != 'PASS' or c.get('source_sha256') != sha(src):
            return None
        if strict and not c.get('warnings_as_errors'):
            return None
        if c.get('dependencies') != deps or c.get('object_sha256') != sha(obj):
            return None
        return obj, cp

    def remote_candidate(self, module, deps, strict):
        for candidate in self.remote:
            if candidate['module'] != module:
                continue
            entry = candidate['entry']
            inputs = entry['inputs']
            source, _ = self.paths(module)
            if inputs['source_sha256'] != sha(source) or inputs['pins'] != self.pins():
                continue
            if inputs['lean_sha256'] != sha(BIN / 'lean.real'):
                continue
            if strict and not candidate['warnings_as_errors']:
                continue
            if set(inputs['dependency_objects']) != set(deps):
                continue
            good = True
            for dep, objects in inputs['dependency_objects'].items():
                _, dep_obj = self.paths(dep)
                stem = dep.replace('.', '/')
                for original, expected in objects.items():
                    suffix = original.split(stem, 1)[-1]
                    if suffix not in PARTS:
                        continue  # Lake hash/trace metadata is not an imported Lean object.
                    local = Path(str(dep_obj)[:-6] + suffix)
                    if not local.is_file() or sha(local) != expected:
                        good = False
                        break
            if good:
                return candidate
        return None

    def compile(self, module, strict=True):
        if (self.state / 'stop-after-current').exists():
            raise RuntimeError('Controlled safe-boundary stop requested; no next Lean process started')
        if module in self.memo:
            return self.memo[module]
        source, obj = self.paths(module)
        if source is None:
            if not obj.exists():
                raise RuntimeError(f'Missing installed module {module}')
            self.memo[module] = sha(obj)
            return self.memo[module]
        # Existing pinned external objects remain trusted development inputs.
        # Their acceptance is never inferred from this cache presence.
        if not self.project(module) and obj.exists():
            self.memo[module] = sha(obj)
            return self.memo[module]
        deps = {d: self.compile(d, strict=False) for d in imports(source)}
        binding = self.binding(module, deps)
        cp = self.state / 'cache' / (module + '.json')
        if cp.exists() and obj.exists():
            saved = json.loads(cp.read_text())
            if saved.get('status') == 'PASS' and saved.get('binding') == binding and (
                    not strict or saved.get('warnings_as_errors')) and saved.get('object_parts') == self.parts(obj):
                self.memo[module] = sha(obj)
                return self.memo[module]
        remote = self.remote_candidate(module, deps, strict) if self.project(module) else None
        old = self.old_candidate(module, deps, strict) if self.project(module) else None
        if remote:
            obj.parent.mkdir(parents=True, exist_ok=True)
            for suffix in PARTS:
                dest = Path(str(obj)[:-6] + suffix)
                origin_info = remote['object_parts'].get(suffix)
                if origin_info:
                    origin = Path(origin_info['path'])
                    assert sha(origin) == origin_info['sha256']
                    shutil.copy2(origin, dest)
                    assert sha(dest) == origin_info['sha256']
                elif dest.exists():
                    dest.unlink()
            assert binding == self.binding(module, deps)
            record = {'status': 'PASS', 'module': module, 'binding': binding,
                      'warnings_as_errors': remote['warnings_as_errors'], 'object_parts': self.parts(obj),
                      'remote_producer': remote['provenance'],
                      'scope': ('Exact original producer compilation reused; no new replay or axiom audit claimed'
                                if remote['provenance']['original_stage_bound_in_this_artifact'] else
                                'Inherited development cache only; original producer stage absent from this artifact; final acceptance incomplete')}
        elif old:
            old_obj, old_receipt = old
            before = self.parts(old_obj)
            obj.parent.mkdir(parents=True, exist_ok=True)
            for suffix in PARTS:
                dest = Path(str(obj)[:-6] + suffix)
                origin = Path(str(old_obj)[:-6] + suffix)
                if origin.exists():
                    shutil.copy2(origin, dest)
                elif dest.exists():
                    dest.unlink()
            assert before == self.parts(obj) == self.parts(old_obj)
            assert binding == self.binding(module, deps)
            record = {'status': 'PASS', 'module': module, 'binding': binding,
                      'warnings_as_errors': json.loads(old_receipt.read_text()).get('warnings_as_errors'),
                      'object_parts': self.parts(obj), 'reused_receipt': str(old_receipt),
                      'reused_receipt_sha256': sha(old_receipt), 'scope': 'Exact-source/direct-object development reuse only'}
        else:
            stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
            run = self.state / 'runs' / (stamp + '-' + module)
            run.mkdir(parents=True)
            obj.parent.mkdir(parents=True, exist_ok=True)
            cwd = self.root if self.project(module) else source.parents[len(module.split('.')) - 1]
            command = [str(BIN / 'lean'), '-j2', '-M4096', *(['-DwarningAsError=true'] if strict else []),
                       '-o', str(obj), str(source.relative_to(cwd))]
            record = {'status': 'RUNNING', 'module': module, 'binding': binding,
                      'command': command, 'cwd': str(cwd), 'warnings_as_errors': strict,
                      'runtime_sha256': sha(__file__), 'shared_lock': str(OLD / 'locks/compiler-0.lock'),
                      'scope': 'Normal-trust development compilation only; no final acceptance claim'}
            receipt = run / 'receipt.json'
            receipt.write_text(json.dumps(record, indent=2) + '\n')
            started = time.monotonic()
            if (self.state / 'stop-after-current').exists():
                raise RuntimeError('Controlled safe-boundary stop requested; no next Lean process started')
            with (run / 'stdout.log').open('wb') as log:
                proc = subprocess.Popen(command, cwd=cwd, env=self.environment(), stdout=log, stderr=subprocess.STDOUT,
                                        pass_fds=(self.heavy_lock_fd,), start_new_session=True)
                record['child_pid'] = proc.pid
                receipt.write_text(json.dumps(record, indent=2) + '\n')
                _, wait_status, usage = os.wait4(proc.pid, 0)
                code = os.waitstatus_to_exitcode(wait_status)
                proc.returncode = code
            after = self.binding(module, {d: sha(self.paths(d)[1]) for d in deps})
            record.update(exit_code=code, seconds=round(time.monotonic() - started, 3), binding_after=after,
                          max_rss_kib=usage.ru_maxrss, user_cpu_seconds=usage.ru_utime,
                          system_cpu_seconds=usage.ru_stime,
                          status='PASS' if code == 0 and binding == after and obj.exists() else 'FAILED')
            if record['status'] == 'PASS':
                record['object_parts'] = self.parts(obj)
            receipt.write_text(json.dumps(record, indent=2) + '\n')
            print(json.dumps({'module': module, 'status': record['status'], 'receipt': str(receipt)}), flush=True)
            if record['status'] != 'PASS':
                raise RuntimeError(f'Leaf failed or changed inputs: {receipt}')
        cp.parent.mkdir(parents=True, exist_ok=True)
        cp.write_text(json.dumps(record, indent=2) + '\n')
        self.memo[module] = sha(obj)
        return self.memo[module]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('module')
    p.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    p.add_argument('--compile', action='store_true')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    rt = Runtime(a.root)
    if not a.compile:
        plan = rt.plan(a.module)
        text = json.dumps(plan, indent=2) + '\n'
        if a.output:
            a.output.parent.mkdir(parents=True, exist_ok=True)
            a.output.write_text(text)
            print(json.dumps({'plan': str(a.output), 'nodes': len(plan['nodes'])}))
        else:
            print(text)
        return
    lockpath = OLD / 'locks/compiler-0.lock'
    with lockpath.open('a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        rt.heavy_lock_fd = lock.fileno()
        # All dependency compilation and cache installation share this lock.
        print(json.dumps({'target': a.module, 'object_sha256': rt.compile(a.module)}), flush=True)


if __name__ == '__main__':
    main()
