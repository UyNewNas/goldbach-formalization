"""Read-only inspection of the original accepted frozen standard namespace."""
from pathlib import Path
import base64, hashlib, json, os, subprocess, zlib

BASE = Path('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')
V3 = BASE / 'verification-import-order-resume-v3'
STAGE = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169')
ACTIVE = STAGE / 'active/lib'

def stamp(p):
    s = p.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]

def inspect(p, include=False, limit=4000000):
    row = {'path': str(p), 'exists': p.is_file(), 'is_symlink': p.is_symlink(), 'resolved_path': str(p.resolve())}
    if not p.is_file():
        return row, None
    before = stamp(p)
    digest = hashlib.sha256()
    with p.open('rb') as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    row.update(bytes=before[2], sha256=digest.hexdigest(), stat=before)
    raw = None
    if include:
        assert before[2] <= limit
        raw = p.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == row['sha256']
        row['base64'] = base64.b64encode(raw).decode()
    assert stamp(p) == before
    return row, raw

report = {'schema': 'p29_frozen_batteries_original_cache_readonly_probe_v1', 'Lean_invocations': 0, 'filesystem_writes': 0, 'new_formal_credit': 0, 'records': {}}
receipt_path = STAGE / 'standard-input-overlays/batteries.json'
row, raw = inspect(receipt_path, True)
report['records']['batteries_receipt'] = row
assert raw is not None
receipt = json.loads(raw)
assert receipt['schema'] == 'p2-winner9-batteries-overlay-v1'
assert receipt['status'] == 'EXACT_ORIGINAL_INPUT_BYTES_RESTORED_NOT_QUALIFICATION'
for name in ['REQUEST.json', 'CHECKPOINT.json']:
    row, raw = inspect(STAGE / name, name == 'REQUEST.json')
    report['records'][name] = row
    if name == 'REQUEST.json' and raw is not None:
        document = json.loads(raw)
        report['request_keys'] = list(document)
        report['locked_packages'] = document.get('locked_packages')
producer = receipt.get('producer_script')
if isinstance(producer, str):
    report['records']['producer_script'] = inspect(Path(producer))[0]
report['source_roots'] = {}
for key in ['source_root', 'baseline_root', 'donor_root']:
    value = receipt.get(key)
    if not isinstance(value, str):
        continue
    p = Path(value)
    rec = {'path': str(p), 'resolved': str(p.resolve()), 'is_dir': p.is_dir(), 'git': {}}
    if p.is_dir():
        for label, args in [('HEAD', ['rev-parse', 'HEAD']), ('toplevel', ['rev-parse', '--show-toplevel']), ('tracked_diff', ['diff', '--quiet', 'HEAD', '--'])]:
            result = subprocess.run(['git', '-C', str(p), *args], capture_output=True, text=True, timeout=30, env=dict(os.environ, GIT_OPTIONAL_LOCKS='0'))
            rec['git'][label] = {'exit_code': result.returncode, 'stdout': result.stdout.strip(), 'stderr': result.stderr.strip()[:1000]}
    report['source_roots'][key] = rec
report['lemma_source_row'] = receipt.get('sources', {}).get('Batteries.Tactic.Lemma')
report['lemma_source_files'] = {}
def collect_source_paths(value):
    if isinstance(value, dict):
        for item in value.values():
            collect_source_paths(item)
    elif isinstance(value, list):
        for item in value:
            collect_source_paths(item)
    elif isinstance(value, str) and value.startswith('/') and value.endswith('.lean'):
        report['lemma_source_files'][value] = inspect(Path(value))[0]
collect_source_paths(report['lemma_source_row'])
shape_path = V3 / 'original-external-derived/SNAPSHOT_SHAPE.json'
shape_row, shape_raw = inspect(shape_path, True)
assert shape_row['bytes'] == 3445 and shape_row['sha256'] == 'b9892b552f36317dc29a9bb0b63cb0e7b5b1c664565483cbb908854bd723c221'
report['records']['SNAPSHOT_SHAPE.json'] = shape_row
shape = json.loads(shape_raw)
report['raw_snapshot_descriptor'] = shape.get('raw_source')
descriptor = shape.get('raw_source', {})
raw_path = descriptor.get('path')
report['original_snapshot_file_entries'] = {}
if isinstance(raw_path, str):
    snapshot_path = Path(raw_path)
    snap_row, snap_raw = inspect(snapshot_path, snapshot_path.is_file(), limit=25000000)
    report['raw_snapshot_current_identity'] = {k: v for k, v in snap_row.items() if k != 'base64'}
    if snap_raw is not None:
        assert snap_row['bytes'] == 20904189 and snap_row['sha256'] == 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
        snapshot = json.loads(snap_raw)
        report['raw_snapshot_root_keys'] = list(snapshot)
        frozen_files = snapshot.get('files', {})
        assert isinstance(frozen_files, dict)
        for rec in report['records'].values():
            p = rec['path']
            if p in frozen_files:
                report['original_snapshot_file_entries'][p] = frozen_files[p]
        del snapshot, snap_raw
table = V3 / 'original-external-derived/P2_DECLARED_FACETS.jsonl'
table_row, _ = inspect(table)
assert table_row['bytes'] == 23833463 and table_row['sha256'] == 'e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636'
report['original_derived_table'] = table_row
groups = {}
standard_rows = []
for line in table.read_bytes().splitlines():
    original = json.loads(line)
    p = Path(original['identity']['path'])
    if not p.is_relative_to(ACTIVE):
        continue
    prefix = original['module'].split('.')[0]
    group = groups.setdefault(prefix, {'facets': 0, 'modules': set(), 'present': 0, 'missing': [], 'size_mismatches': []})
    group['facets'] += 1
    group['modules'].add(original['module'])
    exists = p.is_file()
    if exists:
        group['present'] += 1
        current = stamp(p)
        if current[2] != original['identity']['bytes']:
            group['size_mismatches'].append(str(p))
    else:
        current = None
        group['missing'].append(str(p))
    if prefix not in ['MathlibNt', 'PrimeNumberTheoremAnd', 'Architect', 'ImbalancedChen']:
        rec = {'original': original, 'current': {'exists': exists, 'is_symlink': p.is_symlink(), 'resolved_path': str(p.resolve()), 'stat': current}}
        if original['module'] == 'Batteries.Tactic.Lemma':
            rec['current_exact_file'] = inspect(p)[0]
        standard_rows.append(rec)
for group in groups.values():
    group['modules'] = len(group['modules'])
report['active_namespace_groups'] = groups
report['accepted_cached_standard_facets'] = standard_rows
report['active_namespace_entries'] = [{'name': p.name, 'is_dir': p.is_dir(), 'is_symlink': p.is_symlink(), 'resolved': str(p.resolve())} for p in sorted(ACTIVE.iterdir())] if ACTIVE.is_dir() else []
report['interpretation'] = 'Original receipt and current observations only; no restoration, source compilation, qualification or substitution performed.'
raw = json.dumps(report, sort_keys=True, separators=(',', ':')).encode()
print('P29_FROZEN_BATTERIES_PROBE ' + base64.b64encode(zlib.compress(raw, 9)).decode())
