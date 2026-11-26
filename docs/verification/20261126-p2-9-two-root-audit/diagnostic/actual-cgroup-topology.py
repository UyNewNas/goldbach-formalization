"""Read only the process cgroup topology needed after the v2 preflight stop."""
import hashlib
import json
import os
from pathlib import Path

def read(path, limit):
    with Path(path).open('rb') as handle:
        raw = handle.read(limit + 1)
    if len(raw) > limit:
        raise ValueError('bounded metadata exceeded: ' + path)
    return raw, raw.decode('utf-8')

membership_raw, membership = read('/proc/self/cgroup', 65536)
mount_raw, mountinfo = read('/proc/self/mountinfo', 1048576)
cgroup2 = [line for line in mountinfo.splitlines()
           if ' - cgroup2 ' in line]
if len(cgroup2) > 32:
    raise ValueError('too many cgroup2 mount rows')
result = {
    'schema': 'p29_actual_cgroup_topology_only_v1',
    'trigger_job': '3209b7df1fda47a9afc42de3119811ed',
    'self_pid': os.getpid(),
    'cgroup_namespace': os.readlink('/proc/self/ns/cgroup'),
    'pid_namespace': os.readlink('/proc/self/ns/pid'),
    'proc_self_cgroup_text': membership,
    'proc_self_cgroup_sha256': hashlib.sha256(membership_raw).hexdigest(),
    'mountinfo_total_bytes': len(mount_raw),
    'mountinfo_full_sha256': hashlib.sha256(mount_raw).hexdigest(),
    'cgroup2_mountinfo_rows': cgroup2,
    'non_cgroup2_mount_rows_not_output': True,
    'Lean_invocations': 0,
    'filesystem_writes': 0,
    'project_source_object_reads': 0,
}
print('P29_ACTUAL_CGROUP_TOPOLOGY ' + json.dumps(result), flush=True)
