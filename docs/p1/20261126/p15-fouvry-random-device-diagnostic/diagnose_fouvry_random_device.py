#!/usr/bin/env python3
"""One guarded outer/inner device observation; no Lake, repair or cache transfer.

Loads the hash-bound original reader from its preserved executed attempt.
Reuses its sandbox_argv and namespace predicates without changing their code.
Only a new independent evidence attempt is writable; random bytes are discarded.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from types import ModuleType

sys.dont_write_bytecode = True
COMMIT = 'fd9634e90aad5a537337457e33cb538a1187038a'
READER = Path('/workspace/p1-complete-proof/20261126-p15-fouvry-existing-artifact-reuse-v1') / COMMIT / 'attempt-00000/executed-check-receiver.py'
READER_SHA = '788e505adf280069408975649b48a5ab8950f4603e35e3063f916a02e145c628'
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-fouvry-random-device-diagnostic-v1')

# Appended to the unchanged original probe prefix, before its marker write.
# That prefix computes run, protected, outside, readonly, own_rw and ok.
OBSERVE = r'''
import hashlib, stat, subprocess
phase = sys.argv[3]
check = {'schema':'p15_readonly_namespace_probe_v1',
    'protected_paths_readonly':bool(readonly),
    'all_writable_mounts_within_owned_run':not outside,
    'owned_tmp_writable':bool(own_rw), 'protected_path_count':len(protected), 'ok':bool(ok)}
result = {'schema':'p15_random_device_observation_v1', 'phase':phase, 'namespace_probe':check}
if phase == 'inner' and not ok:
    print(json.dumps(result))
    raise SystemExit(3)
def observe(fn):
    try:
        return {'ok':True, 'value':fn()}
    except Exception as e:
        return {'ok':False, 'error':type(e).__name__, 'errno':getattr(e,'errno',None)}
def small(path):
    with open(path,'rb') as f:
        data = f.read(4097)
    if len(data)>4096:
        raise ValueError('METADATA_TOO_LARGE')
    return data.decode(errors='replace').strip()
def acl(path):
    raw = os.getxattr(path,'system.posix_acl_access')
    return {'bytes':len(raw),'hex':raw[:516].hex(),'truncated':len(raw)>516}
def info(path):
    st = os.stat(path)
    flags = os.statvfs(path).f_flag
    return {'mode':oct(stat.S_IMODE(st.st_mode)), 'type':stat.S_IFMT(st.st_mode),
        'uid':st.st_uid, 'gid':st.st_gid, 'dev':st.st_dev, 'ino':st.st_ino,
        'rdev':[os.major(st.st_rdev),os.minor(st.st_rdev)],
        'symlink':os.path.islink(path), 'resolved':str(Path(path).resolve()),
        'readonly':bool(flags & os.ST_RDONLY), 'nodev':bool(flags & os.ST_NODEV),
        'access_acl':observe(lambda:acl(path))}
def mount_info():
    fd = os.open('/dev/urandom',os.O_PATH|os.O_CLOEXEC)
    try:
        mid = re.search(r'^mnt_id:\s*(\d+)$',small('/proc/self/fdinfo/'+str(fd)),re.M)[1]
        rows = []
        for line in Path('/proc/self/mountinfo').read_text().splitlines():
            f = line.split()
            if f[0] == mid:
                j = f.index('-')
                rows.append({'id':mid,'parent':f[1],'fs_dev':f[2],
                    'mountpoint':decode(f[4]),'vfs_options':f[5],'fstype':f[j+1],
                    'super_flags':[v for v in f[j+3].split(',') if v in ('ro','rw','nodev','nosuid','noexec')]})
        return rows
    finally:
        os.close(fd)
def read_device():
    stage,fd = 'identity',None
    try:
        st = os.stat('/dev/urandom')
        if not stat.S_ISCHR(st.st_mode) or (os.major(st.st_rdev),os.minor(st.st_rdev)) != (1,9):
            return {'ok':False,'stage':stage,'error':'UNEXPECTED_DEVICE'}
        stage = 'open'
        fd = os.open('/dev/urandom',os.O_RDONLY|os.O_CLOEXEC)
        got = os.fstat(fd)
        if (got.st_dev,got.st_ino,got.st_rdev) != (st.st_dev,st.st_ino,st.st_rdev):
            return {'ok':False,'stage':stage,'error':'DEVICE_CHANGED'}
        stage = 'read'
        count = len(os.read(fd,1))
        return {'ok':count == 1,'stage':stage,'read_bytes':count}
    except OSError as e:
        return {'ok':False,'stage':stage,'errno':e.errno}
    finally:
        if fd is not None:
            os.close(fd)
keys = 'Uid Gid Groups CapInh CapPrm CapEff CapBnd CapAmb NoNewPrivs Seccomp Seccomp_filters NSpid'.split()
result['process'] = {x.split(':',1)[0]:x.split(':',1)[1].strip()
    for x in small('/proc/self/status').splitlines() if x.split(':',1)[0] in keys}
result['maps'] = {n:observe(lambda n=n:small('/proc/self/'+n)) for n in ('uid_map','gid_map','setgroups')}
result['namespaces'] = {n:observe(lambda n=n:os.readlink('/proc/self/ns/'+n)) for n in ('user','mnt','pid','net','cgroup')}
result['lsm'] = observe(lambda:small('/proc/self/attr/current'))
result['cgroup_sha256'] = observe(lambda:hashlib.sha256(small('/proc/self/cgroup').encode()).hexdigest())
result['paths'] = {p:observe(lambda p=p:info(p)) for p in ('/','/dev','/dev/urandom')}
result['device_mount'] = observe(mount_info)
result['urandom_read'] = read_device()
if phase == 'outer':
    result['bwrap_version'] = observe(lambda:subprocess.check_output(
        ['/usr/bin/bwrap','--version'],stderr=subprocess.DEVNULL,timeout=5)[:512].decode())
print(json.dumps(result,sort_keys=True,separators=(',',':')))
'''


def require(ok, code):
    if not ok:
        raise ValueError(code)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load_reader():
    require(READER.resolve(strict=True) == READER and not READER.is_symlink(), 'READER_ROUTE_DIFFERS')
    raw = READER.read_bytes()
    require(len(raw) == 25582 and digest(raw) == READER_SHA, 'READER_PIN_DIFFERS')
    r = ModuleType('unchanged_fouvry_reader')
    r.__file__ = str(READER)
    exec(compile(raw, str(READER), 'exec'), r.__dict__)
    manifest, s, review, code, bindings = r.load_inputs(COMMIT)
    require(code == raw, 'ORIGINAL_COMMITTED_READER_DIFFERS')
    return r, manifest, s, review


def state(r, m, s, v):
    return {'context': r.snapshot(s, m, v), 'git': s.d.original_git_state(r.REPO)}


def collect(r, m, s, v, run, binary, binding, payload, rows):
    protected = sorted({str(r.PROJECT), str(r.PACKAGE), str(r.REPO),
        *m['receiver_configuration_pins'], *v['existing_runtime_bindings']})
    protected = sorted({str(Path(p) if Path(p).exists() else Path(p).parent) for p in protected})
    require(len(protected) == 14, 'PROTECTED_PATH_COUNT_DIFFERS')
    (run / 'tmp').mkdir(exist_ok=False)
    probe = run / 'observe-device.py'
    s.d.write_frozen(probe, payload)
    for phase in ('outer', 'inner'):
        require(r.namespace_tool_binding(binary) == binding, 'NAMESPACE_TOOL_CHANGED')
        cmd = ['python3','-B',str(probe),str(run),json.dumps(protected),phase]
        argv = r.sandbox_argv(binary, run, cmd) if phase == 'inner' else cmd
        rec = r.quiet_command(s, run, phase+'-device-observation', s.h.guard(0, argv))
        row = {'phase':phase, 'command':r.public_command(rec)}
        rows.append(row)
        require(rec['exit_code'] == 0 and not rec['actual_built_modules']
                and not rec['actual_failed_modules'], 'OBSERVER_FAILED')
        raw = r.bounded_bytes(Path(rec['log']), 65536)
        require(raw is not None and len(raw) == rec['log_bytes'] and digest(raw) == rec['log_sha256'],
                'OBSERVER_LOG_UNBOUND')
        require(not r.UNEXPECTED_LAKE_ACTION.search(r.ANSI.sub('', raw.decode())), 'UNEXPECTED_ACTION')
        lines = [x for x in raw.decode().splitlines() if x.startswith('{')]
        require(len(lines) == 1, 'OBSERVER_OUTPUT_AMBIGUOUS')
        obs = json.loads(lines[0])
        require(obs['schema'] == 'p15_random_device_observation_v1' and obs['phase'] == phase,
                'OBSERVER_OUTPUT_UNBOUND')
        row['observation'] = obs
        if phase == 'inner':
            require(obs['namespace_probe'] == {'schema':'p15_readonly_namespace_probe_v1',
                'protected_paths_readonly':True, 'all_writable_mounts_within_owned_run':True,
                'owned_tmp_writable':True, 'protected_path_count':14, 'ok':True}, 'NAMESPACE_CHECK_FAILED')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--script-sha256', required=True)
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    a = parser.parse_args()
    code = Path(__file__).read_bytes()
    require(re.fullmatch('[0-9a-f]{64}', a.script_sha256) and digest(code) == a.script_sha256,
            'DIAGNOSTIC_SOURCE_PIN_DIFFERS')
    r, m, s, v = load_reader()
    base = ROOT / a.script_sha256
    require(base.resolve() == base, 'EVIDENCE_ROUTE_DIFFERS')
    if a.inside_lane:
        run = a.inside_lane.resolve(strict=True)
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name)
                and Path(__file__).resolve() == run/'executed-diagnostic.py', 'WORKER_PATH_DIFFERS')
        s.d.verify_lane(s.h)
    before = state(r, m, s, v)
    binary = Path('/usr/bin/bwrap').resolve(strict=True)
    binding = r.namespace_tool_binding(binary)
    payload = (r.READONLY_PROBE.partition('if ok:\n')[0] + OBSERVE).encode()
    if not a.inside_lane:
        run = s.d.attempt(base)
        require(run.resolve() == run and not base.is_symlink(), 'EVIDENCE_ROUTE_DIFFERS')
        s.d.write_frozen(run/'executed-diagnostic.py', code)
    report = {'schema':'p15_random_device_diagnostic_v1', 'status':'HOLD',
        'reader_sha256':READER_SHA, 'script_sha256':a.script_sha256,
        'readonly_tool':{'path':str(binary), **binding}, 'sandbox_argv_reused_unchanged':True,
        'proof_compilation_requested':False, 'cache_transfer_requested':False,
        'trace_or_config_or_guard_changes_requested':False, 'new_lean_acceptance':False}
    try:
        if a.inside_lane:
            report['observations'] = []
            collect(r, m, s, v, run, binary, binding, payload, report['observations'])
            report['status'] = 'DEVICE_METADATA_OBSERVED'
        else:
            child = ['python3','-B',str(run/'executed-diagnostic.py'),
                     '--script-sha256',a.script_sha256,'--inside-lane',str(run)]
            rec = r.quiet_command(s, run, 'serialized-device-observation',
                s.h.serialize(0, run/'DIAGNOSTIC_LANE.json', child))
            raw = r.bounded_bytes(run/'PUBLIC_RESULT.json', 65536)
            require(raw is not None, 'WORKER_RESULT_MISSING')
            report = json.loads(raw)
            report['worker_exit_code'] = rec['exit_code']
            report['worker_failure_code'] = report.get('failure_code')
            require(rec['exit_code'] == 0, 'SERIALIZED_WORKER_FAILED')
    except Exception as exc:
        report.update(status='HOLD', failure_code=str(exc) if isinstance(exc, (ValueError, r.Hold)) else type(exc).__name__)
    finally:
        try:
            after = state(r, m, s, v)
            frozen = {READER:(25582,READER_SHA), Path(__file__):(len(code),digest(code)),
                run/'executed-diagnostic.py':(len(code),digest(code)),
                run/'observe-device.py':(len(payload),digest(payload))}
            stable = all(r.fingerprint(p) == {'bytes':n,'sha256':h} for p,(n,h) in frozen.items())
            checks = dict(before_state_sha256=digest(json.dumps(before,sort_keys=True).encode()),
                after_state_sha256=digest(json.dumps(after,sort_keys=True).encode()),
                source_artifact_configuration_runtime_unchanged=before['context'] == after['context'],
                repository_git_metadata_unchanged=before['git'] == after['git'],
                frozen_inputs_unchanged=stable, readonly_tool_unchanged=r.namespace_tool_binding(binary) == binding)
            if a.inside_lane:
                report.update(checks)
            else:
                report['dispatch_checks'] = checks
            require(before == after and stable and checks['readonly_tool_unchanged'], 'FINAL_INPUT_CHANGED')
        except Exception:
            report.update(status='HOLD', failure_code='FINAL_CONTEXT_CHECK_FAILED')
        out = run/('PUBLIC_RESULT.json' if a.inside_lane else 'PUBLIC_FINAL_RESULT.json')
        s.d.save(out, report)
        if not a.inside_lane:
            print(json.dumps({**report,'public_result':{'path':str(out),**r.fingerprint(out)}},sort_keys=True))
    return 0 if report.get('status') == 'DEVICE_METADATA_OBSERVED' else 3


if __name__ == '__main__':
    os.environ.update(GIT_OPTIONAL_LOCKS='0', GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(json.dumps({'status':'HOLD','failure_code':type(exc).__name__}),flush=True)
        raise SystemExit(3)
