"""Pin and budget one invocation of the unchanged two-root audit CLI.

Preflight performs no filesystem write and no source compilation. The exec'd
original driver owns all new checker/owned audit attempts and their receipts.
"""
import hashlib
import json
import os
from pathlib import Path
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


def resources():
    group = Path('/sys/fs/cgroup')
    maximum_text = (group / 'memory.max').read_text().strip()
    require(maximum_text != 'max', 'finite cgroup memory maximum not exposed')
    maximum = int(maximum_text)
    current = int((group / 'memory.current').read_text())
    memory_stat = {key: int(value) for key, value in
                   (line.split() for line in (group / 'memory.stat').read_text().splitlines())}
    meminfo = {line.split(':', 1)[0]: line.split(':', 1)[1].strip().split()
               for line in Path('/proc/meminfo').read_text().splitlines()}
    host_available = int(meminfo['MemAvailable'][0]) * 1024
    regular_file_cache = max(0, memory_stat['file'] - memory_stat.get('shmem', 0))
    reclaim_adjusted = max(0, maximum - current + regular_file_cache)
    effective_budget = min(host_available, reclaim_adjusted)
    disk = os.statvfs(ROOT)
    free_disk = disk.f_bavail * disk.f_frsize
    result = {'cgroup_memory_max_bytes': maximum, 'cgroup_memory_current_bytes': current,
              'raw_cgroup_headroom_bytes': max(0, maximum - current),
              'regular_file_cache_bytes': regular_file_cache,
              'inactive_file_bytes': memory_stat.get('inactive_file'),
              'host_MemAvailable_bytes': host_available,
              'reclaim_adjusted_process_budget_bytes': effective_budget,
              'reclaim_adjustment_is_not_reserved_memory': True,
              'free_disk_bytes': free_disk, 'required_disk_floor_bytes': DISK_FLOOR,
              'cpu_affinity_count': len(os.sched_getaffinity(0)),
              'cgroup_cpu_max': (group / 'cpu.max').read_text().strip(),
              'requested_MCP_limits': {'memory_mb': MCP_MEMORY_MB, 'cpu_threads': MCP_CPU_THREADS,
                                       'timeout_seconds': MCP_TIMEOUT_SECONDS},
              'observed_MCP_max_memory_mb': OBSERVED_MCP_MAX_MEMORY_MB,
              'inner_Lean_audit_memory_mb': INNER_AUDIT_MEMORY_MB}
    require(MCP_MEMORY_MB <= OBSERVED_MCP_MAX_MEMORY_MB, 'request exceeds observed MCP per-job memory maximum')
    require(INNER_AUDIT_MEMORY_MB < MCP_MEMORY_MB, 'no process-wrapper memory margin')
    require(maximum >= MCP_MEMORY_MB * 1024 * 1024, 'cgroup hard limit is below requested process budget')
    require(effective_budget >= MCP_MEMORY_MB * 1024 * 1024,
            'insufficient current host/cgroup budget after regular-file-cache reclaim: ' + json.dumps(result))
    require(free_disk >= DISK_FLOOR, 'insufficient current audit disk reserve: ' + json.dumps(result))
    require(result['cpu_affinity_count'] >= MCP_CPU_THREADS, 'insufficient CPU affinity')
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
