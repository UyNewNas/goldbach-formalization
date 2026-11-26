"""Pin and budget one invocation of the unchanged two-root audit CLI.

Preflight performs no filesystem write and no source compilation. The exec'd
original driver owns all new checker/owned audit attempts and their receipts.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

ROOT = Path('/workspace/p2-saving16-20261125')
DRIVERS = Path('/workspace/p2-9-20261125/verification/part2')
TOOL_PINS = {
    'run_winner9_private_audit.py': '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'run_winner9_private_checks.py': '164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac',
    'inspect_winner9_owner_native.py': '9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d',
    'winner9_private_audit_template.lean': '2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
    'winner9_external_snapshot.py': 'a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf',
}
RUNTIME_PINS = {
    '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean':
        'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leanchecker':
        'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a',
}
RECORD_PINS = {
    'ImbalancedChen.ActualPrimePolyhedralTestFunctions':
        '8a420f88c97482a5949f51821e748a8fc219f4c135dc0dff91c530fd86fd9e95',
    'ImbalancedChen.AffinePrimeWallReserve':
        'f6978a7a65cc13f45d39ee81e5b9ce70ffc06873d346573ed87c3129a43d0899',
}
NORMAL_PROVENANCE = {
    'prior_reception_job': '0f6bf34cff044800a641002a1055dc0a',
    'original_archive_git_blob': '76f918e111c03dccb3069b8c75829fda443055be',
    'original_archive_bytes': 28112,
    'original_archive_sha256': 'c2e4ef91a7f029ab6a6c4a761931aac2f7b6ba1f3266351a15366c1e1701e413',
    'original_manifest_member': 'SELECTED_ORIGINAL_NORMAL_RECORDS.json',
    'original_member_bytes': 836362,
    'original_member_sha256': '88f5f492ccae8e0fa9ddee189559bb10d1c3cd1dea589486286a5eb6d2a8f78d',
    'record_map_member': 'RECORD_MAP.json',
    'record_map_sha256': '7abe7d6109098c5c283f4f216555cf40795a2c8fc23324825ed4283e07b97478',
    'canonical_record_encoding': 'json.dumps(row, sort_keys=True, separators=(",", ":")).encode()',
    'scope': 'Previously accepted original archive/member lineage; this launcher freshly matches only the two canonical rows below. Original CLI writes each root replay process, owned inventory/types, audit process and receipt.',
}
SNAPSHOT = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
SNAPSHOT_SHA = 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
MATHLIB = Path('/workspace/compile-deps/mathlib')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
MCP_MEMORY_MB, MCP_CPU_THREADS, MCP_TIMEOUT_SECONDS = 12800, 1, 3600
OBSERVED_MCP_MAX_MEMORY_MB = 13107
INNER_AUDIT_MEMORY_MB = 11264
DISK_FLOOR = 96 * 1024 * 1024
observed, checked = {}, []
resources_before = resources_after = None


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def stamp(path):
    info = path.stat()
    link = path.lstat()
    keys = ('st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns')
    return {'resolved': str(path.resolve(strict=True)),
            'stat': {k: getattr(info, k) for k in keys},
            'lstat': {k: getattr(link, k) for k in keys}}


def checked_hash(path, expected):
    before = stamp(path)
    with path.open('rb') as source:
        actual = hashlib.file_digest(source, 'sha256').hexdigest()
    require(stamp(path) == before, 'file changed during pin check: ' + str(path))
    require(actual == expected, 'pinned SHA mismatch: ' + str(path))
    observed[str(path)] = before
    checked.append({'path': str(path), 'bytes': before['stat']['st_size'], 'sha256': actual})


def bounded_text(path, maximum=1024 * 1024):
    with path.open('rb') as source:
        raw = source.read(maximum + 1)
    require(len(raw) <= maximum, 'resource metadata exceeds bound: ' + str(path))
    return raw.decode('utf-8')


def absolute_posix(text, label):
    value = PurePosixPath(text)
    require(text.startswith('/') and not text.startswith('//') and
            '..' not in value.parts and str(value) == text,
            'unsupported noncanonical ' + label + ': ' + text)
    return value


def bound_cgroup_v2():
    membership_text = bounded_text(Path('/proc/self/cgroup'), 65536)
    unified = [line for line in membership_text.splitlines() if line.startswith('0::')]
    require(len(unified) == 1, 'one unified cgroup2 membership is required')
    membership = absolute_posix(unified[0].split(':', 2)[2], 'cgroup membership')
    mount_text = bounded_text(Path('/proc/self/mountinfo'))
    candidates = []
    for line in mount_text.splitlines():
        left, separator, right = line.partition(' - ')
        if not separator or right.split()[0] != 'cgroup2':
            continue
        fields = left.split()
        require(len(fields) >= 6, 'invalid cgroup2 mountinfo')
        decode = lambda value: re.sub(r'\\([0-7]{3})',
                                      lambda match: chr(int(match.group(1), 8)), value)
        root = absolute_posix(decode(fields[3]), 'cgroup2 mount root')
        mount = Path(str(absolute_posix(decode(fields[4]), 'cgroup2 mount point')))
        # A subtree-only or namespace-misaligned mount cannot expose every
        # visible ancestor; stop unless a namespace-root mount is available.
        if root != PurePosixPath('/'):
            continue
        resolved_mount = mount.resolve(strict=True)
        group = mount.joinpath(*membership.relative_to(root).parts).resolve(strict=True)
        require(group.is_relative_to(resolved_mount), 'mapped cgroup escaped its mount')
        info = group.stat()
        require(str(os.major(info.st_dev)) + ':' + str(os.minor(info.st_dev)) == fields[2],
                'mapped cgroup device does not match mountinfo')
        candidates.append({'group': group, 'mount': resolved_mount, 'line': line,
                           'root': str(root), 'device': info.st_dev, 'inode': info.st_ino})
    require(candidates, 'no supported cgroup2 namespace-root mount maps this process')
    require(len({(item['device'], item['inode']) for item in candidates}) == 1,
            'cgroup2 mounts map this process to different groups')
    candidate = sorted(candidates, key=lambda item: (len(str(item['mount'])), str(item['mount'])))[0]
    group, mount = candidate['group'], candidate['mount']
    require(bounded_text(group / 'cgroup.type', 65536).strip() == 'domain',
            'only an ordinary cgroup2 domain is supported')
    procs = bounded_text(group / 'cgroup.procs')
    require(str(os.getpid()) in procs.split(),
            'mapped cgroup.procs does not contain the actual launcher PID')
    namespace = os.readlink('/proc/self/ns/cgroup')
    mount_stat = mount.stat()
    binding = {'proc_self_cgroup_text': membership_text,
               'unified_membership': str(membership),
               'cgroup_namespace': namespace, 'selected_mountinfo_line': candidate['line'],
               'mount_root': candidate['root'], 'resolved_mount_point': str(mount),
               'resolved_process_cgroup': str(group),
               'group_device': candidate['device'], 'group_inode': candidate['inode'],
               'mount_device': mount_stat.st_dev, 'mount_inode': mount_stat.st_ino,
               'self_pid': os.getpid(), 'self_pid_present_in_mapped_cgroup_procs': True,
               'ancestor_scope': 'All visible ancestors through this verified cgroup namespace root; no claim about hidden host ancestors.'}
    return group, mount, binding


def resources():
    group, mount, binding = bound_cgroup_v2()
    levels, finite_limits, adjusted_budgets, cpu_limits = [], [], [], []
    current_group = group
    while True:
        require(len(levels) < 128, 'cgroup hierarchy exceeds supported depth')
        row = {'path': str(current_group)}
        max_path = current_group / 'memory.max'
        if not max_path.exists():
            require(current_group == mount,
                    'memory controller is not exposed below the namespace-root mount')
            row['memory_limit_files'] = 'NOT_EXPOSED_AT_MOUNT_ROOT'
        else:
            maximum_text = bounded_text(max_path, 65536).strip()
            maximum = None if maximum_text == 'max' else int(maximum_text)
            current = int(bounded_text(current_group / 'memory.current', 65536).strip())
            memory_stat = {key: int(value) for key, value in
                           (line.split() for line in bounded_text(current_group / 'memory.stat').splitlines())}
            required = ('file', 'shmem', 'file_dirty', 'file_writeback', 'unevictable')
            require(all(key in memory_stat and memory_stat[key] >= 0 for key in required),
                    'required cache accounting fields are missing or negative')
            require(current >= 0 and (maximum is None or maximum > 0),
                    'invalid cgroup memory counters')
            excluded = sum(memory_stat[key] for key in required[1:])
            reclaimable = max(0, memory_stat['file'] - excluded)
            row.update({'memory_max_raw': maximum_text, 'memory_max_bytes': maximum,
                        'memory_current_bytes': current, 'memory_stat_raw': memory_stat,
                        'cache_deductions_bytes': {key: memory_stat[key] for key in required[1:]},
                        'cache_deductions_can_overlap_conservatively': True,
                        'estimated_regular_clean_evictable_file_cache_bytes': reclaimable})
            if maximum is not None:
                estimate = min(maximum, max(0, maximum - current + reclaimable))
                finite_limits.append(maximum)
                adjusted_budgets.append(estimate)
                row.update({'raw_headroom_bytes': max(0, maximum - current),
                            'reclaim_adjusted_budget_estimate_bytes': estimate})
        cpu_path = current_group / 'cpu.max'
        if cpu_path.exists():
            quota_text = bounded_text(cpu_path, 65536).strip()
            quota, period_text = quota_text.split()
            period = int(period_text)
            require(period > 0 and (quota == 'max' or int(quota) > 0), 'invalid cpu.max')
            row['cpu_max_raw'] = quota_text
            if quota != 'max':
                cpu_limits.append((int(quota), period))
        else:
            require(current_group == mount, 'cpu controller is not exposed below mount root')
            row['cpu_limit_files'] = 'NOT_EXPOSED_AT_MOUNT_ROOT'
        levels.append(row)
        if current_group == mount:
            break
        current_group = current_group.parent
        require(current_group.is_relative_to(mount), 'ancestor walk escaped cgroup2 mount')
    require(finite_limits, 'no finite visible cgroup memory maximum is exposed')
    meminfo = {line.split(':', 1)[0]: line.split(':', 1)[1].strip().split()
               for line in bounded_text(Path('/proc/meminfo')).splitlines()}
    require(meminfo['MemAvailable'][1] == 'kB', 'unsupported MemAvailable unit')
    host_available = int(meminfo['MemAvailable'][0]) * 1024
    effective_maximum = min(finite_limits)
    effective_budget = min([host_available, *adjusted_budgets])
    disk = os.statvfs(ROOT)
    free_disk = disk.f_bavail * disk.f_frsize
    result = {'cgroup_binding': binding, 'visible_cgroup_levels_leaf_to_root': levels,
              'visible_cgroup_effective_memory_max_bytes': effective_maximum,
              'host_MemAvailable_bytes': host_available,
              'reclaim_adjusted_process_budget_estimate_bytes': effective_budget,
              'reclaim_estimate_is_not_memory_reservation_or_guarantee': True,
              'resource_reads_are_live_samples_not_atomic_snapshots': True,
              'free_disk_bytes': free_disk, 'required_disk_floor_bytes': DISK_FLOOR,
              'cpu_affinity_count': len(os.sched_getaffinity(0)),
              'requested_MCP_limits': {'memory_mb': MCP_MEMORY_MB, 'cpu_threads': MCP_CPU_THREADS,
                                       'timeout_seconds': MCP_TIMEOUT_SECONDS},
              'observed_MCP_max_memory_mb': OBSERVED_MCP_MAX_MEMORY_MB,
              'inner_Lean_audit_memory_mb': INNER_AUDIT_MEMORY_MB}
    require(bounded_text(Path('/proc/self/cgroup'), 65536) == binding['proc_self_cgroup_text'] and
            os.readlink('/proc/self/ns/cgroup') == binding['cgroup_namespace'] and
            binding['selected_mountinfo_line'] in bounded_text(Path('/proc/self/mountinfo')).splitlines(),
            'cgroup membership, namespace or mount changed during resource check')
    require(MCP_MEMORY_MB <= OBSERVED_MCP_MAX_MEMORY_MB, 'request exceeds observed MCP per-job memory maximum')
    require(INNER_AUDIT_MEMORY_MB < MCP_MEMORY_MB, 'no process-wrapper memory margin')
    require(effective_maximum >= MCP_MEMORY_MB * 1024 * 1024, 'visible cgroup hard limit is below requested process budget')
    require(effective_budget >= MCP_MEMORY_MB * 1024 * 1024,
            'insufficient current host/cgroup reclaim-adjusted budget estimate: ' + json.dumps(result))
    require(free_disk >= DISK_FLOOR, 'insufficient current audit disk reserve: ' + json.dumps(result))
    require(result['cpu_affinity_count'] >= MCP_CPU_THREADS, 'insufficient CPU affinity')
    require(all(quota >= period * MCP_CPU_THREADS for quota, period in cpu_limits),
            'visible cgroup CPU quota is below requested thread allocation')
    return result


try:
    resources_before = resources()
    for name, expected in TOOL_PINS.items():
        checked_hash(DRIVERS / name, expected)
    for name, expected in RUNTIME_PINS.items():
        checked_hash(Path(name), expected)
    pin = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB, text=True).strip()
    require(pin == MATHLIB_PIN, 'Mathlib checkout pin differs')
    registry = ROOT / '.lake/p2-private/records.json'
    before_registry = stamp(registry)
    require(before_registry['stat']['st_size'] <= 64 * 1024 * 1024, 'registry exceeds bounded preflight size')
    raw = registry.read_bytes()
    require(stamp(registry) == before_registry, 'registry changed while reading')
    records = json.loads(raw)
    selected = {}
    for module, expected in RECORD_PINS.items():
        record = records[module]
        digest = hashlib.sha256(json.dumps(record, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        require(digest == expected, 'original normal record pin differs: ' + module)
        selected[module] = {'canonical_record_sha256': digest,
                            'source_sha256': record['source_sha256'],
                            'object_sha256': record['object_sha256'],
                            'closure_signature': record['closure_signature'],
                            'normal_exit_code': record['exit_code']}
    observed[str(registry)] = before_registry
    checked.append({'path': str(registry), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                    'selected_keys_only': list(RECORD_PINS)})
    del raw, records
    checked_hash(SNAPSHOT, SNAPSHOT_SHA)
    resources_after = resources()
    require(resources_before['cgroup_binding'] == resources_after['cgroup_binding'],
            'process cgroup binding changed between preflight resource checks')
    for name, original in observed.items():
        require(stamp(Path(name)) == original, 'pinned input changed before original CLI exec: ' + name)
    arguments = [sys.executable, '-B', str(DRIVERS / 'run_winner9_private_audit.py'),
                 '--memory-mb', str(INNER_AUDIT_MEMORY_MB), '--external-snapshot', str(SNAPSHOT),
                 '--summary-name', 'p29-polyhedral-affine-missing-owned-20261126.json', *RECORD_PINS]
    print('P29_TWO_ROOT_ORIGINAL_AUDIT_PREFLIGHT ' + json.dumps({
        'status': 'PINS_AND_RESOURCES_PASSED_BEFORE_AUDIT_WRITES',
        'launcher_sha256': hashlib.sha256(globals().get('SOURCE_TEXT', '').encode()).hexdigest(),
        'resources_before': resources_before, 'resources_after': resources_after,
        'checked_files': checked, 'selected_original_normal_records': selected,
        'selected_original_normal_record_lineage': NORMAL_PROVENANCE,
        'cwd': str(ROOT), 'original_cli_argv': arguments,
        'preflight_project_source_object_reads': 0,
        'preflight_Lean_invocations': 0, 'preflight_filesystem_writes': 0,
        'original_driver_freshness_checks_preserved': True,
        'original_driver_reuse_successes_preserved': True}), flush=True)
    os.chdir(ROOT)
    os.execv(sys.executable, arguments)
except Exception as exc:
    print('P29_TWO_ROOT_ORIGINAL_AUDIT_PREFLIGHT_STOP ' + json.dumps({
        'status': 'STOPPED_BEFORE_ORIGINAL_AUDIT_EXEC', 'error': type(exc).__name__ + ': ' + str(exc),
        'resources_before': resources_before, 'resources_after': resources_after,
        'completed_pin_checks': checked, 'original_audit_invoked': False,
        'preflight_filesystem_writes': 0}), flush=True)
    sys.exit(2)
