"""Exact, default-deny compiler admission before the original guard log/exec."""
from pathlib import Path
import hashlib
import json
import os


def resolved(value, cwd):
    path = Path(value)
    return str((Path(cwd) / path).resolve() if not path.is_absolute() else path.resolve())


def canonical(argv, cwd, physical=True):
    def path(value):
        return resolved(value, cwd) if physical else os.path.abspath(os.path.join(str(cwd), value))
    return [path(a) if not a.startswith(('-', '@'))
            and ('/' in a or a.endswith(('.lean', '.c', '.olean', '.ilean', '.json')))
            else a for a in argv]


def clang_toolchain_paths(policy):
    # The original guard makes shadow/include a link into this exact official
    # root. Canonicalizing BOTH command sides must not bless a redirected link.
    realroot = Path(policy['toolchain_roots']['realroot'])
    shadow = Path(policy['toolchain_roots']['shadow'])
    for root in [realroot, shadow]:
        if not root.is_absolute() or root.resolve(strict=True) != root or not root.is_dir():
            raise RuntimeError('Compiler toolchain root changed or escaped its fixed identity')
    if not (shadow / 'include').is_symlink():
        raise RuntimeError('Original shadow include link is missing')
    for relative in ['include', 'include/clang']:
        official = realroot / relative
        target = official.resolve(strict=True)
        if (not official.is_dir() or not target.is_relative_to(realroot) or
                (shadow / relative).resolve(strict=True) != target):
            raise RuntimeError('Compiler include path escapes the fixed official toolchain')


def denied_path(argv, cwd, policy):
    roots = [Path(p).resolve() for p in policy['deny_roots']]
    exact = {Path(p).resolve() for p in policy['deny_exact_paths']}
    for arg in argv:
        candidates = [arg]
        if '=' in arg: candidates.append(arg.split('=', 1)[1])
        if arg.startswith('@'): candidates.append(arg[1:])
        if arg.startswith('-'):
            for index, character in enumerate(arg[1:], 1):
                if character in 'oibcIRC' and index + 1 < len(arg): candidates.append(arg[index + 1:])
        for value in candidates:
            if not value or value.startswith('-'): continue
            path = Path(resolved(value, cwd))
            if path in exact or any(path.is_relative_to(root) for root in roots): return path
    return None


def cache_response(path, policy):
    path = Path(path)
    if not path.is_file() or path.is_symlink() or path.stat().st_size > 1024 * 1024:
        raise RuntimeError('Nonregular/oversized Cache linker response')
    data = path.read_bytes(); original = policy['historical_cache_rsp']
    old, current = original['root'].encode(), policy['project'].encode()
    if b'@' in data or (old != current and old in data):
        raise RuntimeError('Nested response or unremapped historical project path')
    normalized = data.replace(current, old)
    if len(normalized) != original['bytes'] or hashlib.sha256(normalized).hexdigest() != original['sha256']:
        raise RuntimeError('Cache linker response differs from the authentic historical bytes after sole root mapping')
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'historical_normalized_sha256':original['sha256'], 'response_is_link_only': True}


def classify(tool, argv, cwd, policy, check_phase=True, raw_argv=None):
    protected = denied_path(argv, cwd, policy)
    if protected is not None: raise RuntimeError('Protected cache source/output: ' + str(protected))
    command = canonical(argv, cwd)
    lexical_command = canonical(argv, cwd, physical=False)
    if tool == 'lean' and command in [['-t0', '-j2', '-M12288', x] for x in ['--githash', '--print-prefix']]:
        if raw_argv not in [['--githash'], ['--print-prefix']]: raise RuntimeError('Metadata raw argv must be the exact singleton')
        if resolved(cwd, cwd) not in policy['metadata_cwds']: raise RuntimeError('Metadata cwd not admitted')
        return {'classification': 'EXACT_READ_ONLY_TOOLCHAIN_METADATA', 'physical_inputs': []}
    if resolved(cwd, cwd) != policy['project']: raise RuntimeError('Compiler cwd outside canonical project')
    for row in policy['admitted_commands']:
        if (row['tool'] == tool and command == canonical(row['argv'], cwd)
                and lexical_command == canonical(row['argv'], cwd, physical=False)):
            if row['phase'] == 'bootstrap' and policy.get('bootstrap_cache_reuse_only'):
                raise RuntimeError('Pinned bootstrap compiler call denied: authentic cache reuse only')
            if tool == 'clang': clang_toolchain_paths(policy)
            if row['phase'] == 'qualified-project' and check_phase:
                qualification = json.loads(Path(policy['qualification']).read_text())
                if (qualification['binding'] != policy['context'] or
                    qualification['status'] != 'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY'):
                    raise RuntimeError('Project compilation requires this run\'s cache qualification')
            physical = []
            if 'source' in row:
                path = Path(row['source']['path']); data = path.read_bytes()
                actual = {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
                for key in ['bytes', 'sha256']:
                    if key in row['source'] and actual[key] != row['source'][key]: raise RuntimeError('Admitted source changed')
                if row['phase'] == 'qualified-project' and check_phase:
                    admitted = json.loads(Path(policy['caller_inputs']).read_text())
                    if (admitted['binding'] != policy['context'] or admitted['sources'][str(path)] != actual or
                        admitted['qualification_sha256'] != hashlib.sha256(Path(policy['qualification']).read_bytes()).hexdigest()):
                        raise RuntimeError('Caller source/exporter changed after its one-time admission')
                physical.append(actual)
            return {'classification': row['classification'], 'physical_inputs': physical}
    if tool == 'clang' and command == ['-o', policy['cache_link_output'], '@' + policy['cache_link_response']]:
        if policy.get('bootstrap_cache_reuse_only'):
            raise RuntimeError('Cache link denied: authentic cache reuse only')
        return {'classification': 'EXACT_BOOTSTRAP_CACHE_LINK_RESPONSE',
                'physical_inputs': [cache_response(policy['cache_link_response'], policy)]}
    raise RuntimeError('Unknown compiler tool, mode, flags or input; default deny')


def enforce(tool, argv, cwd, policy_file, policy_sha, raw_argv=None):
    data = Path(policy_file).read_bytes()
    if hashlib.sha256(data).hexdigest() != policy_sha:
        raise RuntimeError('Cache compiler-denial policy changed')
    policy = json.loads(data)
    event = {'pid': os.getpid(), 'tool': tool, 'argv': argv, 'raw_argv':raw_argv,'cwd': str(cwd), 'context': policy['context']}
    try: event.update(classify(tool, argv, cwd, policy,raw_argv=raw_argv))
    except Exception as error:
        event.update(compiler_exec_permitted=False, classification='DENIED_BEFORE_COMPILER_EXEC', reason=str(error))
        with Path(policy['denial_log']).open('a', encoding='utf-8') as out:
            out.write(json.dumps(event) + '\n')
        raise RuntimeError('Cache compiler admission rejected before exec: ' + str(error)) from error
    event['compiler_exec_permitted'] = True
    with Path(policy['event_log']).open('a', encoding='utf-8') as out: out.write(json.dumps(event) + '\n')
