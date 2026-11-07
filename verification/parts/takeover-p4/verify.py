"""Replay the two new P4 modules and audit their actual declaration closure.

This is a leaf verification, not an aggregate build or an unconditional main
theorem certificate. Dependencies must already have been compiled by P0's
pinned current-source runner; this script never launches replacement builds.
"""
from pathlib import Path
import collections
import datetime
import importlib.util
import json
import os
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('p0_runtime', HERE.parent / 'takeover-p0/runtime.py')
rt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rt)
MODULES = ['ImbalancedChen.ActualUpperCountingInputs',
           'ImbalancedChen.ActualCompilerDensityReserve']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
OUT = HERE / 'runs' / stamp
OUT.mkdir(parents=True)
report = {'status': 'RUNNING', 'runner_pid': os.getpid(), 'modules': MODULES,
          'scope': 'Two P4 strict leaves; current-object kernel replay and defining-module transitive axiom inventory; no aggregate or unconditional main theorem claim',
          'stages': []}
REPORT = OUT / 'report.json'

def save():
    REPORT.write_text(json.dumps(report, indent=2) + '\n')

def provider_state():
    states = {}
    for name in report['pins']:
        path = rt.PROVIDERS / name
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
        tracked = subprocess.run(['git', 'diff', '--quiet'], cwd=path).returncode
        staged = subprocess.run(['git', 'diff', '--cached', '--quiet'], cwd=path).returncode
        states[name] = {'head': head, 'tracked_diff_exit': tracked, 'index_diff_exit': staged}
        assert head == report['pins'][name] and tracked == staged == 0, f'Provider changed: {name}'
    return states

def run(command, name):
    start = time.monotonic()
    slot = rt.acquire_slot()
    with slot, (OUT / name).open('w') as log:
        proc = subprocess.Popen(command, cwd=ROOT, env=rt.environment(),
                                stdout=log, stderr=subprocess.STDOUT)
        report['running_child_pid'] = proc.pid
        save()
        code = proc.wait()
    record = {'command': command, 'exit_code': code,
              'seconds': round(time.monotonic() - start, 3),
              'log': name, 'log_sha256': rt.digest(OUT / name)}
    report['stages'].append(record)
    save()
    if code:
        raise RuntimeError(f'{name} exited {code}; inspect {OUT / name}')
    print(json.dumps(record), flush=True)
    return (OUT / name).read_text()

try:
    frozen = {}
    for module in MODULES:
        source = ROOT / (module.replace('.', '/') + '.lean')
        obj = rt.BUILD / (module.replace('.', '/') + '.olean')
        cache = rt.STATE / 'cache' / (module + '.json')
        built = json.loads(cache.read_text())
        assert built['status'] == 'PASS' and built['warnings_as_errors']
        assert built['source_sha256'] == rt.digest(source)
        assert built['object_sha256'] == rt.digest(obj)
        for path in [source, obj, cache]:
            frozen[str(path)] = rt.digest(path)
    for path in [HERE / 'Audit.lean', Path(__file__), ROOT / 'lean-toolchain',
                 ROOT / 'lake-manifest.json', ROOT / 'lakefile.toml',
                 rt.BIN / 'lean.real', rt.BIN / 'leanchecker']:
        frozen[str(path)] = rt.digest(path)
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0-rc1'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    report['pins'] = {p['name']: p['rev'] for p in manifest['packages']}
    report['provider_state_before'] = provider_state()
    report['frozen'] = frozen
    save()
    version = run([str(rt.BIN / 'lean'), '--version'], 'lean-version.log').strip()
    assert '4.33.0-rc1' in version
    report['lean_version'] = version
    for module in MODULES:
        output = run([str(rt.BIN / 'leanchecker'), '--verbose', module],
                     module.rsplit('.', 1)[1] + '-kernel.log')
        assert 'replaying ' + module in output.splitlines()
    output = run([str(rt.BIN / 'lean'), '-DwarningAsError=true',
                  str((HERE / 'Audit.lean').relative_to(ROOT))], 'axioms.log')
    records = [json.loads(line.removeprefix('TAKEOVER_P4_AUDIT_DECL '))
               for line in output.splitlines() if line.startswith('TAKEOVER_P4_AUDIT_DECL ')]
    counts = [json.loads(line.removeprefix('TAKEOVER_P4_AUDIT_MODULE '))
              for line in output.splitlines() if line.startswith('TAKEOVER_P4_AUDIT_MODULE ')]
    totals = [int(line.removeprefix('TAKEOVER_P4_AUDIT_COUNT '))
              for line in output.splitlines() if line.startswith('TAKEOVER_P4_AUDIT_COUNT ')]
    assert records and totals == [len(records)]
    assert len({r['name'] for r in records}) == len(records)
    assert {c['module'] for c in counts} == set(MODULES)
    actual_counts = collections.Counter(r['module'] for r in records)
    for c in counts:
        assert c['count'] > 0 and c['count'] == actual_counts[c['module']]
    for r in records:
        assert set(r['axioms']) <= ALLOWED and r['type']
    for name, digest in frozen.items():
        assert rt.digest(Path(name)) == digest, f'Input changed during audit: {name}'
    report['provider_state_after'] = provider_state()
    assert report['provider_state_after'] == report['provider_state_before']
    (OUT / 'declarations.json').write_text(json.dumps(records, indent=2) + '\n')
    report.update(status='PASS', module_counts=counts,
                  declaration_count=len(records), allowed_transitive_axioms=sorted(ALLOWED))
    save()
    print('PASS_ALL', len(records), str(REPORT), flush=True)
except BaseException as error:
    report.update(status='FAILED', error=str(error))
    save()
    raise
