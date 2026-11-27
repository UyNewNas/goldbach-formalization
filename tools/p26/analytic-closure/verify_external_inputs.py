"""Verify the recorded execution-relevant external inputs, not old credit.

Excluded archival/setup roles stay excluded explicitly. A successful result
does not relabel the incomplete original full-snapshot certificate.
"""
import hashlib
import json
from pathlib import Path
import time

PLAN = Path('/workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/halfopen-normal-001/EXECUTION_INPUT_PLAN.json')
OUT = Path('/workspace/p26-analytic-closure-20261127/EXTERNAL_INPUTS_READBACK.json')
ROLES = {'actual-imported-artifact', 'actual-imported-source',
         'batteries-donor-artifact', 'batteries-donor-source',
         'qualified-native-artifact', 'selected-native-source',
         'pinned-runtime', 'pinned-toolchain-shared-library-ABI'}


def main():
    started = time.monotonic()
    raw = PLAN.read_bytes()
    plan = json.loads(raw)
    seen, problems, counts, remapped = {}, [], {}, []
    for name, expected in plan['required_files'].items():
        if expected['role'] not in ROLES:
            continue
        role = expected['role']
        counts[role] = counts.get(role, 0) + 1
        path = Path(name)
        prefix = '/workspace/goldbach-p2/.lake/packages/'
        if not path.is_file() and name.startswith(prefix):
            relative = name[len(prefix):]
            alternate = Path('/workspace/compile-deps/mathlib/.lake/packages') / relative
            if alternate.is_file():
                path = alternate
                remapped.append({'original': name, 'current': str(path)})
        if not path.is_file():
            problems.append({'path': name, 'reason': 'missing'})
            continue
        resolved = str(path.resolve())
        stat = path.stat()
        key = (resolved, stat.st_size, stat.st_mtime_ns)
        if key not in seen:
            seen[key] = hashlib.sha256(path.read_bytes()).hexdigest()
        digest = seen[key]
        if stat.st_size != expected['bytes'] or digest != expected['sha256']:
            problems.append({'path': name, 'current': str(path), 'reason': 'mismatch',
                             'expected_sha256': expected['sha256'], 'actual_sha256': digest})
    result = {'schema': 'p26_external_runtime_input_readback_v1',
              'status': 'matched' if not problems else 'mismatched_or_missing',
              'formal_acceptance': False, 'original_full_snapshot_verified': False,
              'plan': {'path': str(PLAN), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()},
              'selected_roles': sorted(ROLES), 'role_counts': counts,
              'unique_physical_files_hashed': len(seen), 'remapped_aliases': remapped,
              'problems': problems, 'seconds': time.monotonic() - started}
    OUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'files': sum(counts.values()),
                      'problems': len(problems), 'seconds': result['seconds']}), flush=True)


if __name__ == '__main__':
    main()
