"""Verify the existing all-level completed actual Eisenstein continuation.

Runs the strict/incremental build, real interface assertions, complete project
owner/type/axiom inventory, and bundled kernel replay. Imported external
libraries retain normal imported-environment trust, not full-library replay.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from build_p34_fourier_k import ROOT, TOOLCHAIN, FLAGS, digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.absolute()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env['PATH'] = str(TOOLCHAIN / 'bin') + os.pathsep + env.get('PATH', '')
    report = {'status': 'RUNNING', 'scope': 'All-level completed actual Eisenstein continuation; not full P3.4',
              'stages': [], 'trust': 'Normal external imported-environment trust; project replay only'}
    code_paths = ['verification/verify_p34_all_level.py', 'verification/build_p34_fourier_k.py',
                  'verification/P34FourierKEndpoints.lean', 'verification/P34AllLevelAudit.lean',
                  'verification/P34AllLevelEndpoints.lean',
                  'verification/P34PrimitiveAnalyticEndpoints.lean',
                  'verification/test_p34_fourier_k_pins.py',
                  'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
    report['verification_input_sha256'] = {p: digest(ROOT / p) for p in code_paths}

    def stream_digest(path):
        with path.open('rb') as handle:
            return hashlib.file_digest(handle, 'sha256').hexdigest()

    def save():
        (out / 'report.json').write_text(json.dumps(report, indent=2))

    def checked(label, argv):
        start = time.monotonic()
        log = out / (label + '.log')
        with log.open('w') as handle:
            handle.write('command=' + json.dumps(list(map(str, argv))) + '\n')
            handle.flush()
            result = subprocess.run(argv, cwd=ROOT, env=env, stdout=handle,
                                    stderr=subprocess.STDOUT)
        stage = {'name': label, 'exit_code': result.returncode,
                 'seconds': time.monotonic() - start, 'log_sha256': digest(log)}
        report['stages'].append(stage)
        save()
        print(label, result.returncode, round(stage['seconds'], 3), flush=True)
        if result.returncode:
            print(log.read_text()[-12000:], flush=True)
            raise RuntimeError(label + ' failed')
        return log.read_text()

    try:
        output = checked('build', [sys.executable, ROOT / 'verification/build_p34_fourier_k.py',
                                  'Part3AllLevelContinuedMaass'])
        path = Path(output.rsplit('REPORT ', 1)[1].strip())
        build = json.loads(path.read_text())
        if build['status'] != 'BUILD_PASSED' or len(build['stages']) != len(build['order']):
            raise ValueError('Incomplete build')
        env['LEAN_PATH'] = build['lean_path']
        env['LEAN_SYSROOT'] = str(TOOLCHAIN)
        report['build_receipt'] = str(path)
        report['build_receipt_sha256'] = digest(path)
        report['environment'] = build['fingerprint']
        modules = build['order']
        report['project_modules'] = modules
        bindings = {}
        for module in modules:
            source = ROOT / (module.replace('.', '/') + '.lean')
            obj = ROOT / '.lake/p34-fourier-k/objects' / (module.replace('.', '/') + '.olean')
            receipt = json.loads(obj.with_suffix('.receipt.json').read_text())
            if (receipt['exit_code'] != 0 or receipt['binding']['source_sha256'] != digest(source)
                    or receipt['binding']['fingerprint'] != build['fingerprint']
                    or receipt['object_sha256'] != digest(obj)):
                raise ValueError('Unbound object: ' + module)
            for dependency, sha in receipt['binding']['dependencies'].items():
                if sha != bindings[dependency]['object_sha256']:
                    raise ValueError('Stale dependency object: ' + module)
            origin = Path(receipt['log'])
            command = json.loads(origin.read_text().splitlines()[0].removeprefix('command='))
            expected = [str(TOOLCHAIN / 'bin/lean'), *receipt['binding']['flags'],
                        '-o', str(obj), str(source)]
            if command != expected:
                raise ValueError('Strict command differs: ' + module)
            bindings[module] = {'source_sha256': digest(source), 'object_sha256': digest(obj),
                               'strict_flags': receipt['binding']['flags'],
                               'origin_log': str(origin), 'origin_log_sha256': digest(origin)}
        report['bindings'] = bindings
        report['strict_module_count'] = sum(v['strict_flags'] == FLAGS for v in bindings.values())
        report['normal_warning_dependency_count'] = len(modules) - report['strict_module_count']
        for i, (package, pin) in enumerate(build['fingerprint']['packages'].items()):
            observed = checked('package-' + str(i), ['git', '-C', package, 'rev-parse', 'HEAD'])
            if observed.splitlines()[-1] != pin:
                raise ValueError('External package pin changed')
            checked('package-clean-' + str(i), ['git', '-C', package, 'diff', '--exit-code', 'HEAD'])
        version = checked('lean-version', [TOOLCHAIN / 'bin/lean', '--version']).splitlines()[-1]
        expected_version = ('Lean (version 4.33.0-rc1, x86_64-unknown-linux-gnu, '
                            'commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Release)')
        if version != expected_version:
            raise ValueError('Required Lean version differs')
        binaries = [TOOLCHAIN / 'bin/lean', TOOLCHAIN / 'bin/leanchecker',
                    *sorted((TOOLCHAIN / 'lib/lean').glob('libleanshared*.so'))]
        report['toolchain_binary_sha256'] = {str(p): stream_digest(p) for p in binaries}
        external = {}
        objroot = ROOT / '.lake/p34-fourier-k/objects'
        for module in modules:
            imported = checked('imports-' + module.split('.')[-1],
                [TOOLCHAIN / 'bin/lean', '--deps', ROOT / (module.replace('.', '/') + '.lean')])
            for line in imported.splitlines()[1:]:
                path = Path(line.strip())
                if path.suffix != '.olean' or not path.is_file():
                    raise ValueError('Unexpected compiler import path: ' + line)
                path = path.resolve()
                if path.is_relative_to(objroot):
                    continue
                for part in (path, path.with_suffix('.olean.private'), path.with_suffix('.olean.server')):
                    if part.exists():
                        external[str(part)] = stream_digest(part)
        report['direct_external_object_parts_sha256'] = external
        checked('python-suite', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                '-s', 'verification', '-p', 'test_*.py'])
        checked('prior-analytic-endpoints', [TOOLCHAIN / 'bin/lean', *FLAGS,
                                            ROOT / 'verification/P34PrimitiveAnalyticEndpoints.lean'])
        checked('fourier-k-endpoints', [TOOLCHAIN / 'bin/lean', *FLAGS,
                                       ROOT / 'verification/P34FourierKEndpoints.lean'])
        checked('all-level-endpoints', [TOOLCHAIN / 'bin/lean', *FLAGS,
                                       ROOT / 'verification/P34AllLevelEndpoints.lean'])
        audit = checked('owner-axiom-audit', [TOOLCHAIN / 'bin/lean', *FLAGS,
                                            ROOT / 'verification/P34AllLevelAudit.lean'])
        declarations = [json.loads(line.removeprefix('PART3_AUDIT_DECL '))
                        for line in audit.splitlines() if line.startswith('PART3_AUDIT_DECL ')]
        inventory = [json.loads(line.removeprefix('PART3_AUDIT_MODULE '))
                     for line in audit.splitlines() if line.startswith('PART3_AUDIT_MODULE ')]
        if (len({d['name'] for d in declarations}) != len(declarations)
                or {d['module'] for d in inventory} != set(modules)
                or sum(d['count'] for d in inventory) != len(declarations)
                or 'PART3_AUDIT_COUNT ' + str(len(declarations)) not in audit.splitlines()):
            raise ValueError('Compiler inventory differs from build closure')
        (out / 'declarations.json').write_text(json.dumps(declarations, ensure_ascii=False, indent=2))
        (out / 'theorem-types.txt').write_text('\n\n'.join(
            d['name'] + '\n' + d['type'] for d in declarations if d['kind'] == 'theorem'))
        report['inventory'] = inventory
        report['declaration_count'] = len(declarations)
        report['kinds'] = dict(Counter(d['kind'] for d in declarations))
        report['axiom_union'] = sorted({a for d in declarations for a in d['axioms']})
        for module in modules:
            checked('replay-' + module.split('.')[-1],
                    [TOOLCHAIN / 'bin/leanchecker', '--verbose', module])
        report['replayed_module_count'] = len(modules)
        for module, binding in bindings.items():
            source = ROOT / (module.replace('.', '/') + '.lean')
            obj = ROOT / '.lake/p34-fourier-k/objects' / (module.replace('.', '/') + '.olean')
            if digest(source) != binding['source_sha256'] or digest(obj) != binding['object_sha256']:
                raise ValueError('Source/object changed during verification: ' + module)
        for path, sha in {**external, **report['toolchain_binary_sha256']}.items():
            if stream_digest(Path(path)) != sha:
                raise ValueError('External artifact changed during verification: ' + path)
        for path, sha in report['verification_input_sha256'].items():
            if digest(ROOT / path) != sha:
                raise ValueError('Verification input changed during verification: ' + path)
        report['verifier_sha256'] = digest(Path(__file__))
        report['audit_sha256'] = digest(ROOT / 'verification/P34AllLevelAudit.lean')
        report['endpoints_sha256'] = digest(ROOT / 'verification/P34AllLevelEndpoints.lean')
        report['status'] = 'PASSED'
        save()
        return 0
    except Exception as error:
        report['status'] = 'FAILED'
        report['error'] = str(error)
        save()
        print(type(error).__name__ + ': ' + str(error), flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
