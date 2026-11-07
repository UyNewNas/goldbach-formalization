#!/usr/bin/env python3
"""Guard CI's fixed toolchain; never changes proof gates or dependency pins.

The shadow layout follows queue/bootstrap.py. Lake itself is a byte-identical
COPY: fixed Lake's findLakeLeanJointHome? uses IO.appPath, and Env.path puts
Lake's bin before Lean's bin. A symlink to real Lake would therefore make
`lake env lean` bypass the shadow. See Lean v4.33.0-rc1:
  src/lake/Lake/Config/{InstallPath,Env}.lean
Only metadata, wrapper copies and command logs are retained, never the shadow
sysroot (which links large libraries). The checker remains the native binary
with its supported LEAN_NUM_THREADS=2, without fictitious -M or OS caps.
"""
from __future__ import annotations
import argparse
import hashlib
import inspect
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

PIN = 'leanprover/lean4:v4.33.0-rc1'
ACTION_COMMIT = 'f061402b660e0c34644504b324e830f2991d4865'
ACTION_SHA256 = {
    'install_elan.sh': 'e59f4e4b7f719ee16e1ceb49d06fbcc200cc75e6928d050f3eccf4e4341c63a5',
    'config.sh': '22fe5bc8c381f61c2730c3a98c88c4ca2169aee6f31d2ae2efc956c803140b2e',
    'lake_build.sh': '953107e7e493fcf8052a55d2132a9f469b7ea884fbd30ca0ef3a1c962c32c03c',
    'run_leanchecker.sh': '90f634a5913b0e33b8547e90770f031f9f78bdd4167b3032689b62e3456d476f',
    'run_axiom_audit.sh': 'd1198185bf9171bf311cd88581a05050e69a63ae36474a2a652a05b407120748',
}
TOOLS = ('lean', 'leanir', 'clang', 'leanc', 'llvm-ar')
# No LEAN_CC override: that changes Lake's internal compiler/link flags.
AMBIGUOUS_ENV = ('LEAN_SYSROOT', 'LEAN', 'LEAN_AR', 'LEAN_CC', 'LAKE',
                 'LAKE_HOME', 'LAKE_OVERRIDE_LEAN', 'LEAN_PATH', 'LEAN_SRC_PATH',
                 'P0_CI_GUARD_STATE', 'P0_COMPILER_SLOT_HELD', 'P0_COMPILER_SLOT_FD', 'P0_COMPILER_SLOT_TOOL')

def normalize_lean_args(args):
    # Exact fixed-pin src/util/shell.cpp getopt spellings. -t is TRUST;
    # -T/--timeout is a different option and must remain unchanged.
    controlled = {'--trust', '--threads', '--memory'}
    long_required = {'--root', '--plugin', '--load-dynlib', '--setup', '--error',
                     '--incr-save', '--incr-load', '--incr-header-save', '--tstack', '--debug'}
    short_required = set('DoibcCtjRMTpEYZHs')
    short_noarg = set('PdqgvVh012rae')
    clean = []
    i = 0
    while i < len(args):
        a = args[i]
        require(a != '--run' and a != '-r', 'program execution is outside this build-only wrapper')
        if a == '--':
            clean.extend(args[i:]); break
        if a.startswith('--'):
            key, sep, value = a.partition('=')
            require(not (len(key) > 2 and '--run'.startswith(key)),
                    'program execution is outside this build-only wrapper')
            if key in controlled:
                if not sep:
                    i += 1
                    require(i < len(args), 'missing resource argument')
                    value = args[i]
                require(re.fullmatch(r'[0-9]+', value), 'bad resource argument')
            else:
                require(not (len(key) > 2 and any(n.startswith(key) for n in controlled)),
                        'abbreviated resource argument: ' + a)
                clean.append(a)
                if key in long_required and not sep:
                    i += 1
                    require(i < len(args), 'missing option argument')
                    clean.append(args[i])
        elif a.startswith('-') and a != '-':
            # Parse clusters too: getopt accepts -qj8 as -q -j8.
            j = 1
            while j < len(a):
                flag = a[j]
                require(flag != 'r', 'program execution is outside this build-only wrapper')
                require(flag in short_required or flag in short_noarg, 'unknown short option: ' + a)
                if flag in short_required:
                    value = a[j+1:]
                    if not value:
                        i += 1
                        require(i < len(args), 'missing option argument')
                        value = args[i]
                    if flag in 'tjM':
                        require(re.fullmatch(r'[0-9]+', value), 'bad resource argument')
                    else:
                        clean.extend(['-' + flag, value])
                    break
                clean.append('-' + flag)
                j += 1
        else:
            clean.append(a)
        i += 1
    return ['-t0', '-j2', '-M4096', *clean]


WRAPPER = r'''#!/usr/bin/env python3
import fcntl, json, os, pathlib, re, sys
C = __CONFIG__
def require(ok, message):
    if not ok: raise RuntimeError('CI runtime guard: ' + message)
__NORMALIZER__
for key, value in C['environment'].items():
    require(os.environ.get(key) == value, 'changed environment: ' + key)
for key, name in [('LEAN', 'lean'), ('LEAN_AR', 'llvm-ar')]:
    if key in os.environ:
        require(os.environ[key] == C['shadow'] + '/bin/' + name, 'bypassed ' + key)
require(not os.environ.get('LEAN_CC'), 'custom LEAN_CC bypasses bundled compiler')
name = pathlib.Path(sys.argv[0]).name
require(name in C['tools'], 'unknown compiler')
args = sys.argv[1:]
if name == 'lean':
    args = normalize_lean_args(args)
# One inherited flock across Lean and native compiler descendants. Never trust
# a naked HELD flag: require a live ancestor holding the exact lock descriptor.
held = os.environ.get('P0_COMPILER_SLOT_HELD')
if held:
    require(held.isdigit(), 'invalid slot owner')
    owner = int(held)
    # Permit only this direct, read-only metadata child from a Lean owner.
    cache_prefix_probe = (os.environ.get('P0_COMPILER_SLOT_TOOL') == 'lean'
                          and name == 'lean' and sys.argv[1:] == ['--print-prefix']
                          and os.getppid() == owner)
    # Keep the existing fixed Leanc.lean -> clang child and its inherited lock.
    # LeanIR emits C internally; no other nested compiler command is admitted.
    leanc_clang_child = (os.environ.get('P0_COMPILER_SLOT_TOOL') == 'leanc'
                         and name == 'clang' and os.getppid() == owner)
    require(cache_prefix_probe or leanc_clang_child,
            'unreviewed nested compiler chain')
    ancestor = os.getppid()
    while ancestor > 1 and ancestor != owner:
        ancestor = int(pathlib.Path('/proc', str(ancestor), 'stat').read_text().rsplit(')', 1)[1].split()[1])
    require(ancestor == owner, 'slot owner is not an ancestor')
    fdnum = os.environ.get('P0_COMPILER_SLOT_FD', '')
    require(fdnum.isdigit(), 'invalid slot descriptor')
    lockstat = os.stat(C['slot'])
    ownerstat = os.stat('/proc/' + held + '/fd/' + fdnum)
    require((lockstat.st_dev, lockstat.st_ino) == (ownerstat.st_dev, ownerstat.st_ino), 'slot descriptor mismatch')
else:
    fd = os.open(C['slot'], os.O_CREAT | os.O_WRONLY, 0o600)
    fcntl.flock(fd, fcntl.LOCK_EX)
    os.set_inheritable(fd, True)
    os.environ['P0_COMPILER_SLOT_HELD'] = str(os.getpid())
    os.environ['P0_COMPILER_SLOT_FD'] = str(fd)
    os.environ['P0_COMPILER_SLOT_TOOL'] = name
compiler = (C['shadow'] + '/bin/lean-runtime' if name == 'lean'
            else C['realbin'] + '/' + name)
cmd = [compiler, *args]
record = {'pid': os.getpid(), 'tool': name, 'command': cmd,
          'input_args': sys.argv[1:], 'slot_owner': os.environ['P0_COMPILER_SLOT_HELD'],
          'cwd': os.getcwd(), 'sysroot': os.environ['LEAN_SYSROOT']}
# One append under a separate short log lock, including nested children.
with open(C['log'], 'a') as log:
    fcntl.flock(log, fcntl.LOCK_EX)
    log.write(json.dumps(record) + '\n')
os.execv(cmd[0], cmd)
'''


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + '\n')


def capture(*command: str, env: dict | None = None) -> str:
    return subprocess.check_output(command, text=True, env=env).strip()


def resolve_pin() -> Path:
    # Elan `which` has no --toolchain option. Its documented environment
    # override selects the explicit pin without changing any Elan settings.
    pinned_env = dict(os.environ, ELAN_TOOLCHAIN=PIN)
    roots = [Path(capture('elan', 'which', name, env=pinned_env)).resolve().parent
             for name in ('lean', 'lake', 'leanchecker')]
    require(len(set(roots)) == 1, 'Elan executables disagree on toolchain root')
    require(all(Path(capture('elan', 'which', name)).resolve().parent == roots[0]
                for name in ('lean', 'lake', 'leanchecker')), 'Active Elan toolchain is not the fixed pin')
    return roots[0]


def prepare(root: Path, runner_temp: Path, evidence: Path, realbin: Path,
            action_dir: Path, verify_action: bool = True) -> dict:
    """Separated for deterministic fake-executable tests; CLI never skips pins."""
    root, runner_temp, realbin = root.resolve(), runner_temp.resolve(), realbin.resolve()
    require((root / 'lean-toolchain').read_text().strip() == PIN, 'Unexpected toolchain pin')
    require(not any(key in os.environ for key in AMBIGUOUS_ENV), 'Ambiguous existing runtime environment')
    require(os.environ.get('LEAN_NUM_THREADS') == '2', 'Native checker threads must be 2')
    require(os.environ.get('ELAN_TOOLCHAIN', PIN) == PIN, 'Unexpected Elan toolchain override')
    if verify_action:
        require(capture('git', '-C', str(action_dir), 'rev-parse', 'HEAD') == ACTION_COMMIT, 'Wrong lean-action commit')
        for name, expected in ACTION_SHA256.items():
            require(sha(action_dir / 'scripts' / name) == expected, 'Changed pinned action script: ' + name)
    shadow = runner_temp / 'p0-ci-shadow-toolchain'
    evidence = evidence.absolute()
    require(evidence != shadow and shadow not in evidence.parents and evidence not in shadow.parents,
            'Evidence and shadow must be separate')
    require(not shadow.exists() and not shadow.is_symlink(), 'Refusing an existing shadow root')
    require(not evidence.exists() and not evidence.is_symlink(), 'Refusing existing runtime evidence')
    realroot = realbin.parent
    require(realbin.name == 'bin' and (realroot / 'lib' / 'lean').is_dir(), 'Ambiguous real toolchain root')
    for name in (*TOOLS, 'lake', 'leanchecker'):
        path = realbin / name
        require(path.is_file() and os.access(path, os.X_OK), 'Missing pinned executable: ' + name)
        require(path.resolve().is_relative_to(realroot), 'Runtime escapes toolchain: ' + name)
    evidence.mkdir(parents=True)
    shadow.mkdir()
    (shadow / 'bin').mkdir()
    for path in realroot.iterdir():
        if path.name != 'bin':
            (shadow / path.name).symlink_to(path, target_is_directory=path.is_dir())
    for path in realbin.iterdir():
        if path.name not in (*TOOLS, 'lake'):
            (shadow / 'bin' / path.name).symlink_to(path, target_is_directory=path.is_dir())
    # See module docstring: a symlink is insufficient for IO.appPath.
    shutil.copy2(realbin / 'lake', shadow / 'bin' / 'lake')
    # Execute the exact pinned Lean bytes from the shadow bin directory.
    shadow_lean = shadow / 'bin' / 'lean-runtime'
    shutil.copy2(realbin / 'lean', shadow_lean)
    require(sha(realbin / 'lean') == sha(shadow_lean), 'Shadow Lean copy differs')
    real_leantar = realbin / 'leantar'
    shadow_leantar = shadow / 'bin' / 'leantar'
    leantar_setup = {
        'real_leantar_exists': real_leantar.is_file() and os.access(real_leantar, os.X_OK),
        'real_leantar_within_pin_root': real_leantar.is_file() and real_leantar.resolve().is_relative_to(realroot),
        'shadow_leantar_exists': shadow_leantar.is_file() and os.access(shadow_leantar, os.X_OK),
        'shadow_is_real_symlink': shadow_leantar.is_symlink() and shadow_leantar.resolve() == real_leantar.resolve(),
        'leantar_hashes_match': real_leantar.is_file() and shadow_leantar.is_file()
                                and sha(real_leantar) == sha(shadow_leantar),
    }
    print(json.dumps({'pinned_leantar_setup': leantar_setup}, sort_keys=True))
    require(all(leantar_setup.values()),
            'Pinned toolchain must expose its in-root leantar through the shadow sysroot')
    state_path = evidence / 'state.json'
    environment = {'LEAN_SYSROOT': str(shadow), 'LAKE_OVERRIDE_LEAN': 'true',
                   'LEAN_NUM_THREADS': '2', 'ELAN_TOOLCHAIN': PIN, 'P0_CI_GUARD_STATE': str(state_path)}
    config = {'environment': environment, 'shadow': str(shadow), 'realbin': str(realbin),
              'slot': str(evidence / 'compiler.lock'), 'log': str(evidence / 'compiler-commands.jsonl'),
              'tools': list(TOOLS)}
    runtime = {str(realbin / name): sha(realbin / name) for name in (*TOOLS, 'lake', 'leanchecker')}
    runtime[str(shadow / 'bin' / 'lake')] = sha(shadow / 'bin' / 'lake')
    runtime[str(shadow_lean)] = sha(shadow_lean)
    runtime[str(real_leantar)] = sha(real_leantar)
    runtime[str(shadow_leantar)] = sha(shadow_leantar)
    require(runtime[str(realbin / 'lean')] == runtime[str(shadow_lean)], 'Shadow Lean bytes differ from pin')
    require(runtime[str(real_leantar)] == runtime[str(shadow_leantar)], 'Shadow leantar bytes differ from pin')
    require(runtime[str(realbin / 'lake')] == runtime[str(shadow / 'bin' / 'lake')], 'Lake copy differs')
    for name in TOOLS:
        wrapper = shadow / 'bin' / name
        wrapper.write_text(WRAPPER.replace('__CONFIG__', repr(config)).replace(
            '__NORMALIZER__', inspect.getsource(normalize_lean_args)))
        wrapper.chmod(0o755)
        shutil.copy2(wrapper, evidence / (name + '-wrapper.py'))
        runtime[str(wrapper)] = sha(wrapper)
    Path(config['log']).touch()
    state = {'schema': 'p0-ci-runtime-v1', **config, 'root': str(root),
             'runtime_sha256': runtime,
             'input_sha256': {str(root / p): sha(root / p) for p in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')},
             'guard_sha256': sha(Path(__file__)),
             'action_commit': ACTION_COMMIT,
             'action_script_sha256': {str(action_dir / 'scripts' / n): h for n, h in ACTION_SHA256.items()} if verify_action else {},
             'policy': 'Lean -t0 -j2 -M4096; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2'}
    write_json(state_path, state)
    return state


def check_environment(state: dict) -> None:
    for key, value in state['environment'].items():
        require(os.environ.get(key) == value, 'Changed guard environment: ' + key)
    for name in (*TOOLS, 'lake', 'leanchecker'):
        require(shutil.which(name) == state['shadow'] + '/bin/' + name, 'PATH bypasses wrapper: ' + name)
    for key, name in [('LEAN', 'lean'), ('LEAN_AR', 'llvm-ar'), ('LAKE', 'lake')]:
        if key in os.environ:
            require(os.environ[key] == state['shadow'] + '/bin/' + name, 'Environment bypass: ' + key)
    if 'LAKE_HOME' in os.environ:
        require(os.environ['LAKE_HOME'] == state['shadow'], 'Wrong Lake home')
    require(not os.environ.get('LEAN_CC'), 'Custom compiler bypass')
    require(not os.environ.get('P0_COMPILER_SLOT_HELD'), 'Guard invoked inside a compiler')


def audit(state_path: Path, probe: bool = False, require_source: bool = False) -> dict:
    state = json.loads(state_path.read_text())
    check_environment(state)
    require(sha(Path(__file__)) == state['guard_sha256'], 'Runtime guard changed')
    require(not (Path(state['shadow']) / 'bin' / 'lake').is_symlink(), 'Lake must be a byte-identical copy')
    for mapping in ('runtime_sha256', 'input_sha256', 'action_script_sha256'):
        for path, expected in state[mapping].items():
            require(sha(Path(path)) == expected, 'Changed pinned runtime/input: ' + path)
    if probe:
        # Lake's own computed environment, including its PATH ordering, must
        # preserve the guard in the project AND outside the project tree.
        for cwd in (Path(state['root']), Path(state['shadow']).parent):
            subprocess.run([str(Path(state['shadow']) / 'bin' / 'lake'), 'env',
                            sys.executable, str(Path(__file__).resolve()), 'probe',
                            '--state', str(state_path)], cwd=cwd, check=True)
        before = len(Path(state['log']).read_text().splitlines())
        prefix = capture('lake', 'env', 'lean', '--print-prefix')
        realbin = Path(state['realbin'])
        realroot = realbin.parent.resolve()
        real_leantar = realbin / 'leantar'
        shadow_leantar = Path(state['shadow']) / 'bin' / 'leantar'
        diagnostics = {
            'prefix_matches_shadow': prefix == state['shadow'],
            'real_leantar_exists': real_leantar.is_file() and os.access(real_leantar, os.X_OK),
            'real_leantar_within_pin_root': real_leantar.is_file() and real_leantar.resolve().is_relative_to(realroot),
            'shadow_leantar_exists': shadow_leantar.is_file() and os.access(shadow_leantar, os.X_OK),
            'shadow_leantar_is_real_symlink': shadow_leantar.is_symlink()
                                             and shadow_leantar.resolve() == real_leantar.resolve(),
            'leantar_hashes_match': real_leantar.is_file() and shadow_leantar.is_file()
                                    and sha(real_leantar) == sha(shadow_leantar),
        }
        print(json.dumps({'pinned_sysroot_probe': diagnostics}, sort_keys=True))
        require(all(diagnostics.values()), 'Pinned Lean sysroot/leantar binding failed')
        require(len(Path(state['log']).read_text().splitlines()) > before, 'Lean probe bypassed wrapper')
    commands = [json.loads(line) for line in Path(state['log']).read_text().splitlines()]
    for record in commands:
        name = record['tool']
        expected_binary = (state['shadow'] + '/bin/lean-runtime' if name == 'lean'
                           else state['realbin'] + '/' + name)
        require(name in TOOLS and record['command'][0] == expected_binary, 'Unknown/bypassed compiler command')
        require(record['sysroot'] == state['shadow'], 'Compiler sysroot bypass')
        if name == 'lean':
            require(record['command'][1:] == normalize_lean_args(record['input_args']),
                    'Lean command differs from normalized input (possible flag override)')
        else:
            require(record['command'][1:] == record['input_args'], 'Native compiler flags changed')
    source_commands = sum(r['tool'] == 'lean' and any(a.endswith('.lean') for a in r['input_args']) for r in commands)
    require(not require_source or source_commands > 0, 'No guarded Lean source child was recorded')
    report = {'status': 'PASS_RUNTIME_GUARD_ONLY', 'compiler_commands': len(commands),
              'source_commands': source_commands, 'probe': probe,
              'command_log_sha256': sha(Path(state['log'])), 'state_sha256': sha(state_path)}
    write_json(state_path.parent / 'audit.json', report)
    return report


def cache_leantar_diagnostic() -> dict:
    """Log the pinned Mathlib Cache.IO bare-lean prefix lookup; never gate CI."""
    expected_sysroot = os.environ.get('LEAN_SYSROOT')
    resolved_lean = shutil.which('lean')
    result = {
        'kind': 'mathlib-cache-io-bare-lean-prefix-lookup',
        'command': ['lean', '--print-prefix'],
        'resolved_lean': resolved_lean,
        'expected_lean': (expected_sysroot + '/bin/lean') if expected_sysroot else None,
        'expected_sysroot': expected_sysroot,
        'timeout_seconds': 10,
    }
    def clipped(value):
        if value is None:
            return None
        if isinstance(value, bytes):
            value = value.decode('utf-8', errors='replace')
        return value[:4096]
    try:
        child = subprocess.run(['lean', '--print-prefix'], capture_output=True, text=True,
                               errors='replace', check=False, timeout=10)
        stdout = child.stdout
        # Match Lean's trimAscii before deriving <prefix>/bin/leantar.
        prefix = stdout.strip(' \t\n\v\f\r')
        candidate = Path(prefix) / 'bin' / 'leantar' if child.returncode == 0 and prefix else None
        result.update({
            'status': 'child-returned',
            'exit_code': child.returncode,
            'stdout': clipped(stdout),
            'stderr': clipped(child.stderr),
            'prefix': prefix if child.returncode == 0 else None,
            'prefix_matches_LEAN_SYSROOT': child.returncode == 0 and prefix == expected_sysroot,
            'candidate_leantar': str(candidate) if candidate is not None else None,
            # Cache.IO uses pathExists, not executable-bit or child-process checks.
            'candidate_leantar_path_exists': candidate.exists() if candidate is not None else False,
        })
    except subprocess.TimeoutExpired as error:
        result.update({'status': 'child-timeout', 'stdout': clipped(error.stdout), 'stderr': clipped(error.stderr)})
    except OSError as error:
        result.update({'status': 'child-launch-error', 'error_type': type(error).__name__, 'error': clipped(str(error))})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('setup', 'audit', 'probe', 'cache-leantar-diagnostic'))
    parser.add_argument('--evidence', type=Path)
    parser.add_argument('--state', type=Path)
    parser.add_argument('--probe', action='store_true')
    parser.add_argument('--require-source', action='store_true')
    args = parser.parse_args()
    if args.mode == 'setup':
        require(args.evidence is not None, '--evidence required')
        state = prepare(Path.cwd(), Path(os.environ['RUNNER_TEMP']), args.evidence,
                        resolve_pin(), Path(os.environ['LEAN_ACTION_DIR']))
        with open(os.environ['GITHUB_ENV'], 'a') as out:
            for key, value in state['environment'].items():
                require('\n' not in value and '\r' not in value, 'Invalid environment value')
                out.write(key + '=' + value + '\n')
        with open(os.environ['GITHUB_PATH'], 'a') as out:
            out.write(state['shadow'] + '/bin\n')
        print(json.dumps({'status': 'PREPARED_RUNTIME_GUARD', 'state': state['environment']['P0_CI_GUARD_STATE']}))
    elif args.mode == 'cache-leantar-diagnostic':
        # Informational only: the required Mathlib cache command below remains
        # the authoritative gate and is always attempted by the workflow.
        print(json.dumps(cache_leantar_diagnostic(), sort_keys=True))
    else:
        state_path = args.state or Path(os.environ['P0_CI_GUARD_STATE'])
        if args.mode == 'probe':
            check_environment(json.loads(state_path.read_text()))
        else:
            print(json.dumps(audit(state_path, args.probe, args.require_source)))

if __name__ == '__main__':
    main()
