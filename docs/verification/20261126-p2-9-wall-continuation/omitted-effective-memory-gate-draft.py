"""Readonly fragment for the future Omitted ready controller; never a launcher.

This fragment is intentionally not integrated into the fixed v2 controller.
Its inputs remain absent until the root has received the other authorities and
records a fresh P3 system_info result plus the exact planned MCP memory_mb.
No Lean, subprocess, cleanup, filesystem mutation, or capacity reservation.
"""

import datetime
import hashlib
import json
from pathlib import Path


def effective_memory_gate(capacity, launched_memory_mb):
    """Bound sampled remaining memory by host, cgroup and MCP task limits.

    launched_memory_mb must be injected by the final reviewed launcher from
    the same value sent to run_command. The original submission/get_task
    record must independently confirm it during final evidence acceptance.
    """
    assert capacity['status'] == 'ROOT_REVIEWED_MEASURED_NEW_OUTPUT_BUDGET'
    assert capacity['host'] == 'P3'
    snapshot = capacity['service_memory_snapshot']
    assert isinstance(snapshot, dict) and set(snapshot) == {'path', 'bytes', 'sha256'}
    path = Path(snapshot['path'])
    assert path.is_absolute() and path.is_relative_to('/workspace')
    assert not path.is_relative_to('/workspace/p29-omitted-prime-wall-20261126-ef40c77')
    before = path.stat()
    raw = path.read_bytes()
    after = path.stat()
    fields = lambda st: [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]
    assert fields(before) == fields(after)
    assert len(raw) == snapshot['bytes']
    assert hashlib.sha256(raw).hexdigest() == snapshot['sha256']
    info = json.loads(raw)
    assert info['service'] == 'Workspace Compile 27f68009'
    policy = info['environment']
    assert policy['memory_enforcement'] == 'sampled_process_tree_rss'
    assert policy['cgroup_write_available'] is False

    observed = datetime.datetime.fromisoformat(capacity['service_memory_snapshot_observed_utc'])
    assert observed.tzinfo is not None
    now = datetime.datetime.now(datetime.timezone.utc)
    age = (now - observed).total_seconds()
    max_age = capacity['service_memory_snapshot_max_age_seconds']
    assert isinstance(max_age, (int, float)) and 0 < max_age <= 120
    assert 0 <= age <= max_age, 'The original P3 capacity observation is missing or stale.'

    assert isinstance(launched_memory_mb, int) and not isinstance(launched_memory_mb, bool)
    assert launched_memory_mb == capacity['run_command_memory_mb']
    assert 0 < launched_memory_mb <= policy['max_memory_mb']
    task_limit = launched_memory_mb * 1024 * 1024
    cgroup_limit = policy['memory_limit_bytes']
    cgroup_used = policy['memory_current_bytes']
    assert isinstance(cgroup_limit, int) and cgroup_limit > 0
    assert isinstance(cgroup_used, int) and cgroup_used >= 0
    assert task_limit <= cgroup_limit

    meminfo = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    status = dict(line.split(':', 1) for line in Path('/proc/self/status').read_text().splitlines())
    assert meminfo['MemAvailable'].split()[1] == status['VmRSS'].split()[1] == 'kB'
    host_remaining = int(meminfo['MemAvailable'].split()[0]) * 1024
    controller_rss = int(status['VmRSS'].split()[0]) * 1024
    auxiliary_rss = capacity['task_auxiliary_process_rss_allowance_bytes']
    reserve = capacity['memory_safety_reserve_bytes']
    required = capacity['required_additional_memory_bytes']
    assert all(isinstance(n, int) and not isinstance(n, bool) and n > 0
               for n in [host_remaining, controller_rss, auxiliary_rss, reserve, required])

    # No reclaimable-file-cache or swap credit is assumed. Subtract this
    # controller and its reviewed auxiliary allowance from the pre-task
    # cgroup observation as well as from the task's sampled RSS budget.
    task_remaining = max(0, task_limit - controller_rss - auxiliary_rss)
    cgroup_remaining = max(0, cgroup_limit - cgroup_used - controller_rss - auxiliary_rss)
    effective = max(0, min(host_remaining, cgroup_remaining, task_remaining) - reserve)
    assert effective >= required, 'Insufficient effective host/cgroup/task memory; no target write or Lean is allowed.'
    return {
        'schema': 'p29_omitted_measured_host_cgroup_task_memory_gate_v1',
        'observed_utc': now.isoformat(),
        'service_memory_snapshot': snapshot,
        'service_memory_snapshot_stat': fields(before),
        'service_memory_snapshot_age_seconds': age,
        'host_MemAvailable_bytes': host_remaining,
        'cgroup_limit_bytes': cgroup_limit,
        'cgroup_current_bytes_in_original_P3_observation': cgroup_used,
        'cgroup_remaining_without_cache_credit_after_controller_allowance': cgroup_remaining,
        'declared_MCP_run_command_memory_mb': launched_memory_mb,
        'MCP_task_limit_bytes': task_limit,
        'MCP_task_memory_enforcement': policy['memory_enforcement'],
        'current_controller_rss_bytes': controller_rss,
        'task_auxiliary_process_rss_allowance_bytes': auxiliary_rss,
        'task_remaining_after_controller_allowance': task_remaining,
        'memory_safety_reserve_bytes': reserve,
        'effective_sampled_additional_memory_bytes': effective,
        'required_additional_memory_bytes': required,
        'reclaimable_cache_or_swap_credit': 0,
        'runtime_cgroup_remeasurement_claim': False,
        'MCP_submission_memory_mb_still_requires_original_tool_record_match': True,
        'memory_reservation_or_future_availability_guarantee': False,
    }
