"""Strict, resumable native compilation of the actual P3.4 Fourier-K closure.

This is an incremental build receipt, not an acceptance or full-library replay.
Each reuse is authenticated against this builder's previous successful command,
source, dependency objects, tool executable and external package commits.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
MATHLIB = Path('/tmp/workspace-compile-27f68009/deps/mathlib')
DEFAULT = ['Part3ActualRamanujanBesselNormalConvergence',
           'Part3ActualEisensteinCanonicalFourier',
           'Part3ActualComplexEisensteinCanonicalFourier']
FLAGS = ['-t0', '-j1', '-M12000', '-DwarningAsError=true']


def validate_package_pins(pins, locked):
    required = {
        str(MATHLIB): 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
        '/workspace/goldbach-p3/.lake/packages/goldbach': '09b97db5764ade1246bfb77206baa1b124760958',
        '/workspace/goldbach-p3/.lake/packages/LeanArchitect': '78dd66840d3efe8c824c699fc03381cec817c271',
    }
    for package in locked:
        required[str(MATHLIB / '.lake/packages' / package['name'])] = package['rev']
    for path, revision in required.items():
        if pins.get(path) != revision:
            raise ValueError('Required dependency revision differs: ' + path)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('targets', nargs='*', default=DEFAULT)
    args = parser.parse_args()
    out = ROOT / '.lake/p34-fourier-k'
    objects = out / 'objects'
    objects.mkdir(parents=True, exist_ok=True)
    stamp = str(time.time_ns())
    run = out / 'runs' / stamp
    run.mkdir(parents=True)
    lean = TOOLCHAIN / 'bin/lean'
    packages = [MATHLIB, *sorted((MATHLIB / '.lake/packages').iterdir()),
        Path('/workspace/goldbach-p3/.lake/packages/goldbach'),
        Path('/workspace/goldbach-p3/.lake/packages/LeanArchitect')]
    pins = {str(p): subprocess.check_output(['git', '-C', str(p), 'rev-parse', 'HEAD'],
                                          text=True).strip() for p in packages}
    locked = json.loads((MATHLIB / 'lake-manifest.json').read_text())['packages']
    validate_package_pins(pins, locked)
    fingerprint = {'lean': digest(lean), 'packages': pins}
    env = dict(os.environ)
    env['LEAN_PATH'] = ':'.join(map(str, [objects,
        *(p / '.lake/build/lib/lean' for p in packages), TOOLCHAIN / 'lib/lean']))
    env['LEAN_SYSROOT'] = str(TOOLCHAIN)
    modules = {}
    order = []

    def visit(module):
        if module in modules:
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        source = path.read_text(encoding='utf-8-sig')
        deps = re.findall(r'^import\s+(ImbalancedChen\.\S+)', source, re.M)
        modules[module] = {'path': path, 'deps': deps}
        for dep in deps:
            visit(dep)
        order.append(module)

    for module in args.targets:
        visit(module if module.startswith('ImbalancedChen.') else 'ImbalancedChen.' + module)
    report = {'status': 'RUNNING', 'head': subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'fingerprint': fingerprint, 'order': order, 'stages': [],
        'lean_path': env['LEAN_PATH'], 'run': str(run)}
    bindings = {}
    failed = False
    for module in order:
        item = modules[module]
        obj = objects / (module.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        lock = obj.with_suffix('.lock').open('a')
        fcntl.flock(lock, fcntl.LOCK_EX)
        state = obj.with_suffix('.receipt.json')
        # Older general-project dependencies are compiler checked verbatim.
        # Analytic suppliers and the intended endpoints additionally reject warnings.
        flags = FLAGS if module.startswith(('ImbalancedChen.Part3', 'ImbalancedChen.P0Ramanujan')) else FLAGS[:-1]
        binding = {'source_sha256': digest(item['path']), 'fingerprint': fingerprint, 'flags': flags,
                   'dependencies': {d: bindings[d] for d in item['deps']}}
        prior = json.loads(state.read_text()) if state.exists() else {}
        if obj.exists() and prior.get('binding') == binding and prior.get('exit_code') == 0 and \
                prior.get('object_sha256') == digest(obj):
            stage = {'module': module, 'status': 'REUSED', 'receipt': str(state),
                     'origin_log': prior['log'], 'object_sha256': digest(obj)}
        else:
            log = run / (module.split('.')[-1] + '.log')
            argv = [str(lean), *flags, '-o', str(obj), str(item['path'])]
            print('START', module, flush=True)
            start = time.monotonic()
            with log.open('w') as handle:
                handle.write('command=' + json.dumps(argv) + '\n')
                handle.flush()
                result = subprocess.run(argv, cwd=ROOT, env=env, stdout=handle,
                                        stderr=subprocess.STDOUT)
            stage = {'module': module, 'status': 'PASSED' if result.returncode == 0 else 'FAILED',
                     'exit_code': result.returncode, 'log': str(log),
                     'seconds': time.monotonic() - start}
            print(stage['status'], module, round(stage['seconds'], 3), flush=True)
            if result.returncode:
                print(log.read_text()[-12000:], flush=True)
                failed = True
            else:
                stage['object_sha256'] = digest(obj)
                state.write_text(json.dumps({'binding': binding, 'exit_code': 0,
                    'object_sha256': digest(obj), 'log': str(log)}, indent=2))
        report['stages'].append(stage)
        if not failed:
            bindings[module] = stage['object_sha256']
        (run / 'report.json').write_text(json.dumps(report, indent=2))
        lock.close()
        if failed:
            break
    report['status'] = 'FAILED' if failed else 'BUILD_PASSED'
    report['compiled_count'] = sum(s['status'] == 'PASSED' for s in report['stages'])
    report['reused_count'] = sum(s['status'] == 'REUSED' for s in report['stages'])
    (run / 'report.json').write_text(json.dumps(report, indent=2))
    print('REPORT', run / 'report.json', flush=True)
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
