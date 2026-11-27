"""Fresh diagnostic build of the existing higher-moment semantic closure.

No project objects are borrowed from an incompatible P2.5 checkout. External
native-cache inputs are recorded as provisional; normal build success alone
never grants formal acceptance to this stage.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-analytic-closure-20261127')
SYSROOT = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
MATHLIB = Path('/workspace/compile-deps/mathlib')
NATIVE = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib')
TARGET = 'ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix'


def pin(p):
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def main():
    STAGE.mkdir(exist_ok=True)
    objects = STAGE / 'objects'
    (objects / 'ImbalancedChen').mkdir(parents=True, exist_ok=True)
    (STAGE / 'logs').mkdir(exist_ok=True)
    order, nodes = [], {}

    def visit(module):
        if module in nodes:
            return
        source = ROOT / (module.replace('.', '/') + '.lean')
        imports = re.findall(r'^(?:public )?import ([\w.]+)', source.read_text(), re.M)
        nodes[module] = {'source': pin(source), 'imports': imports}
        for item in imports:
            if item.startswith('ImbalancedChen.'):
                visit(item)
        order.append(module)

    visit(TARGET)
    env = os.environ.copy()
    env['PATH'] = str(SYSROOT / 'bin') + ':' + env.get('PATH', '')
    packages = sorted((MATHLIB / '.lake/packages').glob('*/.lake/build/lib/lean'))
    env['LEAN_PATH'] = ':'.join(map(str, [objects, *packages, MATHLIB / '.lake/build/lib/lean', NATIVE]))
    env['LEAN_NUM_THREADS'] = '1'
    flags = ['--trust=0', '-DwarningAsError=true', '-j1', '-M12288',
             '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    run = {'schema': 'p26_fresh_analytic_closure_diagnostic_v1', 'target': TARGET,
           'cwd': str(ROOT), 'status': 'building', 'formal_acceptance': False,
           'external_cache_acceptance': False, 'P2_6_complete': False,
           'lean_path': env['LEAN_PATH'], 'runtime': pin(SYSROOT / 'bin/lean'),
           'builder_source': pin(Path(__file__)),
           'nodes': nodes, 'topological_order': order, 'commands': []}
    previous = STAGE / 'RUN.json'
    if previous.exists():
        old = json.loads(previous.read_text())
        if old['lean_path'] != run['lean_path'] or old['runtime'] != run['runtime']:
            raise SystemExit('Changed runtime or search path; preserve this stage and start a new one')
        for record in old['commands']:
            module = record['module']
            if record.get('exit_code') != 0:
                break
            if old['nodes'][module]['source'] != nodes[module]['source']:
                break
            obj = objects / (module.replace('.', '/') + '.olean')
            if not obj.is_file() or pin(obj) != record['object']:
                break
            run['commands'].append(record)

    def save():
        previous.write_text(json.dumps(run, indent=2) + '\n')

    save()
    for module in order[len(run['commands']):]:
        source = ROOT / (module.replace('.', '/') + '.lean')
        assert pin(source) == nodes[module]['source']
        obj = objects / (module.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        log = STAGE / 'logs' / (module + '.log')
        argv = [str(SYSROOT / 'bin/lean'), *flags, '-o', str(obj), str(source.relative_to(ROOT))]
        record = {'module': module, 'argv': argv, 'source': pin(source), 'started_at': time.time()}
        run['commands'].append(record)
        save()
        started = time.monotonic()
        with log.open('wb') as out:
            proc = subprocess.run(argv, cwd=ROOT, env=env, stdout=out,
                                  stderr=subprocess.STDOUT, timeout=900)
        record.update(exit_code=proc.returncode, seconds=time.monotonic() - started, log=pin(log))
        if proc.returncode:
            run['status'] = 'failed'
            save()
            print(module, 'FAILED', log.read_text()[-6000:], flush=True)
            raise SystemExit(proc.returncode)
        assert pin(source) == nodes[module]['source']
        record['object'] = pin(obj)
        save()
        print(f'{len(run["commands"])}/{len(order)} {module} exit=0', flush=True)
    run['status'] = 'normal_build_succeeded_not_formally_accepted'
    save()
    print(run['status'], flush=True)


if __name__ == '__main__':
    main()
