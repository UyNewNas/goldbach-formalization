"""Negative codegen/audit controls. No arbitrary failure counts as a pass."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

DIRECT = 'ImbalancedChen.Probes.DirectRecControl'
STRUCTURAL = 'ImbalancedChen.Probes.StructuralControl'
DIRECT_RECURSOR = DIRECT + '.Expr.rec'
PARTIAL_HELPER = STRUCTURAL + '.count._unsafe_rec'


def verdict(kind, returncode, output, timed_out=False):
    if timed_out or returncode <= 0:
        return False
    if kind == 'direct':
        needle = 'code generator does not support recursor `' + DIRECT_RECURSOR + '` yet'
    elif kind == 'structural':
        needle = 'Partial declaration in a P0 batch module: ' + PARTIAL_HELPER
    else:
        raise ValueError(kind)
    # Exact full declaration, not a prefix of another generated name.
    return any(needle in line and (kind == 'direct' or line.rstrip().endswith(needle))
               for line in output.splitlines())


def audit_source(template):
    audit = template[template.index('set_option pp.all'):]
    start = audit.index('  let modules := #[')
    end = audit.index('  let allowed :=', start)
    audit = audit[:start] + '  let modules := #[`' + STRUCTURAL + ']\n' + audit[end:]
    old = '  if names.contains finalBridge then\n    throwError "Final bridge must not be included in the owned-module census"\n'
    assert audit.count(old) == 1
    audit = audit.replace(old, '').replace('(names.push finalBridge).qsort', 'names.qsort')
    start = audit.index('    if name == finalBridge then')
    end = audit.index('  for (m, count) in counts do', start)
    audit = audit[:start] + '    liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"\n' + audit[end:]
    assert 'Partial declaration in a P0 batch module: {name}' in audit
    return 'import ' + STRUCTURAL + '\nimport Lean.Util.CollectAxioms\n' + audit


def command(argv, project, logs, label, timeout):
    started = time.monotonic()
    proc = subprocess.Popen(argv, cwd=project, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, start_new_session=True)
    timed_out = False
    try:
        data, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            data, _ = proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            data, _ = proc.communicate()
    (logs / (label + '.log')).write_bytes(data)
    result = {'argv': argv, 'cwd': str(project), 'returncode': proc.returncode,
              'timed_out': timed_out, 'timeout_seconds': timeout,
              'elapsed_seconds': time.monotonic() - started,
              'log_sha256': hashlib.sha256(data).hexdigest()}
    (logs / (label + '.json')).write_text(json.dumps(result, indent=2) + '\n')
    return result, data.decode('utf-8', errors='replace')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--project', type=Path, default=os.environ.get('PROJECT'))
    parser.add_argument('--logs', type=Path, default=os.environ.get('LOGS'))
    parser.add_argument('--template', type=Path, default=Path(__file__).with_name('Round6AuditTemplate.lean'))
    parser.add_argument('--timeout', type=int, default=300)
    args = parser.parse_args()
    if args.project is None or args.logs is None or not 1 <= args.timeout <= 900:
        parser.error('project/logs required; timeout must be 1..900 seconds')
    project, logs = args.project.resolve(), args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    receipt = {'status': 'FAIL', 'controls': {}}
    try:
        r, out = command(['lake', 'build', DIRECT], project, logs, 'negative-direct-build', args.timeout)
        assert verdict('direct', r['returncode'], out, r['timed_out']), 'Direct control failed to produce exact unsupported recursor diagnostic'
        receipt['controls']['direct'] = 'EXPECTED_CODEGEN_REJECTION'
        r, out = command(['lake', 'build', STRUCTURAL], project, logs, 'negative-structural-build', args.timeout)
        assert r['returncode'] == 0 and not r['timed_out'], 'Structural control must first compile successfully'
        raw = args.template.read_bytes()
        source = audit_source(raw.decode('utf-8'))
        audit = project / 'StructuralControlAudit.lean'
        audit.write_bytes(source.encode('utf-8'))
        (logs / 'StructuralControlAudit.lean').write_bytes(audit.read_bytes())
        receipt['template_sha256'] = hashlib.sha256(raw).hexdigest()
        receipt['audit_sha256'] = hashlib.sha256(audit.read_bytes()).hexdigest()
        r, out = command(['lake', 'env', 'lean', '-DwarningAsError=true', audit.name], project, logs, 'negative-structural-audit', args.timeout)
        assert verdict('structural', r['returncode'], out, r['timed_out']), 'Structural control failed to produce exact owned partial declaration rejection'
        receipt['controls']['structural'] = 'EXPECTED_STRICT_AUDIT_REJECTION'
        receipt['status'] = 'PASS_NEGATIVE_CONTROLS_ONLY'
    except Exception as exc:
        receipt['error'] = str(exc)
        raise
    finally:
        (logs / 'NEGATIVE_CONTROLS.json').write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
