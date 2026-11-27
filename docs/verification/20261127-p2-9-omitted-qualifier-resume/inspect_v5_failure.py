import base64
import hashlib
import json
import os
from pathlib import Path
import stat
import zlib

BASE = Path('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')
OUT = BASE / 'verification-standard-package-resume-v5'
PROJECT = BASE / 'project'
TARGET = 'ImbalancedChen/P2FiniteMarkedGamma5OmittedPrimeWall'
MAX_BODY = 524288
MAX_JSON = 67108864
NAMES = [
    'driver.py', 'INPUT_CONTRACT.json', 'SERVICE_OBSERVATION.json', 'FAILURE.json',
    'runtime-evidence/state.json', 'batteries-composed-view-observation-process.json',
    'batteries-composed-view-observation.log', 'ACTUAL_FIRST_NAMESPACE_PATHS.json',
    'omitted-direct-imports-process.json', 'omitted-direct-imports.lean',
    'omitted-direct-imports.log', 'omitted-direct-imports-bindings.json',
    'CURRENT_INPUT_ORIGIN_BINDING.json', 'normal-build-process.json', 'normal-build.log',
    'ORIGINAL_V3_V4_GUARD_PREFIX.jsonl', 'BORROWED_OBJECTS.json',
    'COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json',
    'COMPLETE_SELECTED_BATTERIES_NAMESPACE_VIEW.json', 'REUSED_V4_PACKAGE_VIEW.json',
    'REUSED_ORIGINAL_QUALIFICATIONS.json',
]


def stamp(path):
    s = path.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def capture(path, force=False):
    if not path.exists() and not path.is_symlink():
        return {'path': str(path), 'exists': False}
    assert path.is_file() and not path.is_symlink()
    before = stamp(path)
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            digest.update(chunk)
    row = {'path': str(path), 'exists': True, 'bytes': before[2],
           'sha256': digest.hexdigest(), 'stat': before}
    if force or before[2] <= MAX_BODY:
        assert before[2] <= MAX_JSON
        raw = path.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == row['sha256']
        row['base64'] = base64.b64encode(raw).decode('ascii')
    elif path.suffix == '.json' and before[2] <= MAX_JSON:
        data = json.loads(path.read_bytes())
        row['semantic_summary'] = {'top_level_type': type(data).__name__}
        if isinstance(data, dict):
            row['semantic_summary']['keys'] = sorted(data)
            row['semantic_summary']['selected_scalars'] = {
                k: v for k, v in data.items()
                if k in {'schema', 'status', 'module_count', 'part_count', 'old_native_modules',
                         'received_native_modules', 'selected_native_modules', 'modules'}
                and isinstance(v, (str, int, bool))}
            row['semantic_summary']['sequence_counts'] = {k: len(v) for k, v in data.items()
                                                        if isinstance(v, (list, dict))}
    assert stamp(path) == before
    return row


assert OUT.is_dir() and not OUT.is_symlink()
report = {'schema': 'p29_v5_completed_failure_readonly_probe_v1',
          'v5_job_id': '1aadf7911aac4b80ab0a049f967aa3ba',
          'root': str(OUT), 'files': {name: capture(OUT / name) for name in NAMES},
          'all_v5_regular_file_inventory': {}, 'new_Lean_calls': 0,
          'writes_to_remote_workspace': 0, 'new_formal_credit': 0}
for path in sorted(OUT.rglob('*')):
    if path.is_file():
        assert not path.is_symlink()
        report['all_v5_regular_file_inventory'][path.relative_to(OUT).as_posix()] = {
            'bytes': path.stat().st_size, 'stat': stamp(path)}
state_raw = base64.b64decode(report['files']['runtime-evidence/state.json']['base64'])
state = json.loads(state_raw)
guard = Path(state['log'])
assert guard == BASE / 'verification-import-order-resume-v3/runtime-evidence/compiler-commands.jsonl'
report['live_guard_log'] = capture(guard, force=True)
source = PROJECT / (TARGET + '.lean')
report['old_target_source'] = capture(source, force=True)
assert report['old_target_source']['sha256'] == '4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c'
report['target_outputs'] = {suffix: {'path': str(PROJECT / '.lake/build/lib/lean' / (TARGET + suffix)),
    'exists': (PROJECT / '.lake/build/lib/lean' / (TARGET + suffix)).exists(),
    'is_symlink': (PROJECT / '.lake/build/lib/lean' / (TARGET + suffix)).is_symlink()}
    for suffix in ['.olean', '.ilean', '.trace', '.setup.json']}
assert all(not row['exists'] and not row['is_symlink'] for row in report['target_outputs'].values())
packages = PROJECT / '.lake/packages'
assert packages.is_symlink()
report['package_view'] = {'link': str(packages), 'link_target': os.readlink(packages),
                        'entries': {p.name: os.readlink(p) for p in sorted(packages.iterdir())}}
view_receipt = json.loads((OUT / 'REUSED_V4_PACKAGE_VIEW.json').read_bytes())
report['package_view']['matches_saved_selected_package_paths'] = (
    report['package_view']['entries'] == view_receipt['selected_package_paths'])
binding = json.loads((OUT / 'omitted-direct-imports-bindings.json').read_bytes())
part_mismatches = []
for row in binding['parts']:
    path = Path(row['identity']['path'])
    current = {'path': str(path.resolve(strict=True)), 'stat': stamp(path), 'is_file': path.is_file()}
    if (current['path'] != row['identity']['path'] or current['stat'] != row['stat_snapshot']
            or current['stat'][2] != row['identity']['bytes'] or not current['is_file']):
        part_mismatches.append({'module': row['module'], 'facet': row['facet'],
                                'expected': row, 'current': current})
report['actual_used_part_current_metadata'] = {'parts': len(binding['parts']),
    'module_count': binding['module_count'], 'part_count': binding['part_count'],
    'roots': binding.get('roots'), 'schema': binding.get('schema'),
    'mismatches': part_mismatches, 'fresh_part_hashes_claimed': False}
report['current_namespace_links'] = {}
for name in ['COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json', 'COMPLETE_SELECTED_BATTERIES_NAMESPACE_VIEW.json']:
    receipt = json.loads((OUT / name).read_bytes())
    mismatches = []
    for row in receipt['facets']:
        link = Path(row['requested_path'])
        if (not link.is_symlink() or os.readlink(link) != row['selected_path']
                or str(link.resolve(strict=True)) != str(Path(row['selected_path']).resolve(strict=True))):
            mismatches.append(row)
    report['current_namespace_links'][name] = {'facets_checked': len(receipt['facets']), 'mismatches': mismatches}
report['Batteries_view'] = {'path': str(BASE / 'batteries-native-cache-view-v5/lib'),
    'symlink_count': sum(p.is_symlink() for p in (BASE / 'batteries-native-cache-view-v5/lib').rglob('*'))}
assert report['Batteries_view']['symlink_count'] == 960
for row in [*report['files'].values(), report['live_guard_log'], report['old_target_source']]:
    if row['exists']:
        assert stamp(Path(row['path'])) == row['stat']
raw = (json.dumps(report, sort_keys=True, separators=(',', ':')) + '\n').encode()
compressed = zlib.compress(raw, 9)
assert len(compressed) <= 6 * 1024 * 1024
print('P29_V5_PROBE_META ' + json.dumps({'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                                     'compressed_bytes': len(compressed),
                                     'compressed_sha256': hashlib.sha256(compressed).hexdigest()}), flush=True)
print('P29_V5_PROBE_DATA ' + base64.b64encode(compressed).decode('ascii'), flush=True)
