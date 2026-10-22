"""SOURCE ONLY: root must review before invoking any mode.
Read-only validate-source -> separately authorized exclusive EXPORT -> validate-archive.
No Git, Lean, compiler, collector, cache acceptance, canonical helper, or subprocess.
Any exception is FIRSTFAIL/HOLD. Never overwrite, retry, restore or clean a partial addon.
"""
from pathlib import Path, PurePosixPath
import argparse
import gzip
import hashlib
import io
import json
import os
import stat
import sys

PREFIX = 'docs/evidence/owned-frontiers/20261022-three-frontiers-193-v2'
STATE = '.lake/proof-continuation'
PLAN = STATE + '/source-reviews/20261022-three-frontiers193-v2-additive-publication-source-plan.json'
PLAN_SHA = '047b2f6a10a6ccaec575e4f6dea5d575d6fe0b7931bf04ec72f9f37b91feb48c'
ORIGINAL_ROWS_SHA = 'da4bbaea282eb5899827d3226a8c2afb8b16ffadd8ce4f3095a8e61bbe7fb501'
AUTH = STATE + '/publication-integrity/20261022-three-frontiers193-v2-root-export-authorization.json'
VALIDATION = STATE + '/publication-integrity/20261022-three-frontiers193-v2-source-validation.json'
BASE = 'verification/proof-continuation/2026-10-15'
BASE_SHA = '956c1a2bb2f15aada2d064b9b42587010ed4f2e34deb27f2aae89812860f13b2'
ACCEPT_SHA = '3b6455fb5b60033e064284d34803ee0c0ef5a310652b274bfa8c644e5d8b4062'
TARGETS = {'ImbalancedChen.Counting': '8651960368f560d7c931ef456cdd9bcc8a71477e9bbd5fb9c3add07dcc9206fa',
           'ImbalancedChen.NormalizationGrowth': 'c4a4544c29ae04cbcedc1f62261cb805bfa9e0f473aaf532c098b724624c9286',
           'ImbalancedChen.UniformPrimeTail': '786ed7d70f3f3e89161a9e025d2c8bb0b06db6cddae7200c3fc1c0ca009ebbbf'}
SCOPE = b'''Additive original evidence for the three accepted project frontiers.
Root local acceptance:193 modules /4371 per-module serialized records /141 receipts.
Delta: Counting32, NormalizationGrowth7, UniformPrimeTail5 =44 records /3 receipts.
Counting transfers retain analytic lower/upper assumptions. Normalization retains
its divergence or eventual-even positive lower comparison. Every UniformPrimeTail
prime-counting estimate retains the explicit real-PNT premise. Main1+1.75 OPEN.

The original190 canonical archive and42-file selected-native PNT addon are fixed
dependencies, not overwritten or copied as newly accepted evidence. Old190 files
are covered by exact manifest956c1a... and a reported published checkpoint24217fc...
whose Git membership is not reverified by this program. Native PNT addon is the
selected339-record qualification, not an owned project+339 or nine-closure replay.

Raw JSON/logs are complete byte copies or deterministic-mtime0 gzip payloads.
V2 compact p/<original-row-index>-<full-original-SHA>.raw/.gz names are mapped
back to every full original source path in source-plan.json. No trace is lost.
The first V1 EXPORT failed at a261-character Windows output path. Its partial
prefix, validation, authorization and logs remain preserved; V1 is never resumed.
This distinct V2 prefix requires new validation stdout and new root authorization.
Output paths are checked before writes: at most230 characters and100 per component.
Original absolute paths and historical SOURCE-ONLY/HOLD wording are preserved.
Capture paths referring to old/current caches or registries are historical hash
metadata: this exporter does not chase those paths or substitute today's cache.
Foreign sources/objects/binaries, runtime environment and registry remain external
fixed imported trust. Hash inventories do not make a self-contained proof replay.
No Git publication, external-closure replay, new kernel check or main theorem is
performed or claimed by any mode. Root separately verifies publication membership.

Root protocol: preserve the validate-source stdout as the fixed source-validation
JSON, create the separately reviewed root-export-authorization JSON binding its SHA,
this exact exporter SHA, plan SHA and prefix; then invoke EXPORT exactly once with
the explicit authorization SHA. Preserve any first error and partial directory.
No automatic retry/repair/restore/cleanup. All future measurements come from actual
validation/export output, never from predicted commit hashes or compressed sizes.
'''


def require(value, reason):
    if not value:
        raise ValueError(reason)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'Duplicate JSON key')
            result[key] = value
        return result
    return json.loads(data.decode('utf-8'), object_pairs_hook=unique)


def relative(value):
    require(isinstance(value, str) and value and '\\' not in value and ':' not in value, 'Nonportable path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and all(v not in ('', '.', '..') for v in value.split('/')), 'Unsafe path')
    return p


def under(root, value):
    p = root.joinpath(*relative(value).parts)
    require(p.resolve().is_relative_to(root.resolve()), 'Path escaped root')
    current = root
    for part in relative(value).parts:
        current = current / part
        if current.exists():
            info = current.lstat()
            require(not stat.S_ISLNK(info.st_mode), 'Symlink disallowed')
            require(not getattr(info, 'st_file_attributes', 0) & getattr(stat, 'FILE_ATTRIBUTE_REPARSE_POINT', 0),
                    'Reparse point disallowed')
    return p


def files(root):
    require(root.is_dir() and not root.is_symlink(), 'Missing/linked directory')
    result = {}
    folded = set()
    for p in root.rglob('*'):
        relative_name = p.relative_to(root).as_posix()
        under(root, relative_name)
        if p.is_file():
            require(relative_name.casefold() not in folded, 'Case-fold path collision')
            folded.add(relative_name.casefold())
            result[relative_name] = digest(p.read_bytes())
        else:
            require(p.is_dir(), 'Non-regular archive entry')
    return result


def archive_path_budget(root, plan):
    names = [row['archive_relative'] for row in plan['required_source_rows']] + [
        'source-plan.json', 'validate-addon.py', 'README.txt',
        'publication-authorization.json', 'source-validation.json', 'archive-manifest.json']
    for name in names:
        output = under(root, PREFIX + '/' + name)
        require(len(str(output)) <= 230, 'Output path exceeds230 characters')
        require(all(len(part) <= 100 for part in output.parts), 'Output component exceeds100 characters')


def check_plan(raw):
    require(digest(raw) == PLAN_SHA, 'Plan SHA changed')
    plan = load(raw)
    require(plan['destination'] == PREFIX and plan['root_acceptance_sha256'] == ACCEPT_SHA, 'Plan target/acceptance')
    require(plan['accepted_counts'] == [193, 4371, 141] and plan['delta_counts'] == [3, 44, 3], 'Plan scope')
    rows = plan['required_source_rows']
    require(len(rows) == plan['source_files_measured'] == 195, 'Fixed original inventory')
    require(len({r['archive_relative'].casefold() for r in rows}) == len(rows), 'Archive collisions')
    identity = [{key: row[key] for key in ('anchor', 'bytes', 'encoding', 'role', 'sha256', 'source_relative')}
                for row in rows]
    require(digest(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()) == ORIGINAL_ROWS_SHA,
            'Original195 row identity/order changed')
    for index, row in enumerate(rows):
        require(row['archive_row_index'] == index, 'Original row index changed')
        suffix = '.gz' if row['encoding'] == 'deterministic-gzip-mtime0' else '.raw'
        expected_archive = 'p/' + f'{index:03d}-' + row['sha256'] + suffix
        require(row['archive_relative'] == expected_archive, 'Compact content-addressed mapping changed')
        relative(row['source_relative'])
        relative(row['archive_relative'])
        require(row['anchor'] in ('repo', 'workspace'), 'Anchor')
        require(row['encoding'] in ('identity', 'deterministic-gzip-mtime0'), 'Encoding')
        require(type(row['bytes']) is int and row['bytes'] >= 0, 'Original size')
        if row['anchor'] == 'workspace':
            require(row['source_relative'] == 'goldbach-integration/verification/parts/takeover-p0/checker_memory_guard.py',
                    'Workspace source not allowlisted')
    actual = {r['source_relative']: r['sha256'] for r in rows if r['role'] == 'three-exact-actual-source'}
    require(actual == {n.replace('.', '/') + '.lean': h for n, h in TARGETS.items()}, 'Exact3 actual source identities')
    return plan


def protection(root, plan):
    raw = under(root, BASE + '/manifest.json').read_bytes()
    require(digest(raw) == BASE_SHA, 'Old190 manifest changed')
    old = load(raw)
    require(len(old['modules']) == 190 and old['declaration_count'] == 4327 and len(old['files']) == 3661,
            'Old190 archive schema/counts')
    expected = dict(old['files'])
    require('manifest.json' not in expected, 'Unexpected manifest self row')
    expected['manifest.json'] = BASE_SHA
    require(files(under(root, BASE)) == expected, 'Any old190 archive byte/path changed')
    pnt = plan['protected_pnt42']
    require(pnt['prefix'] == 'docs/evidence/external-native-pnt/20261022-pi-alt' and len(pnt['files']) == 42,
            'PNT42 fixed protection')
    require(files(under(root, pnt['prefix'])) == pnt['files'], 'Any PNT42 byte/path changed')
    return {'old190_manifest_sha256': BASE_SHA, 'old190_payload_files': 3661, 'old190_physical_files': 3662,
            'PNT42_map_sha256': digest(json.dumps(pnt['files'], sort_keys=True).encode()), 'PNT_files': 42}


def source_data(root, plan):
    data = {}
    for row in plan['required_source_rows']:
        anchor = root if row['anchor'] == 'repo' else root.parent
        p = under(anchor, row['source_relative'])
        require(p.is_file(), 'Missing original')
        raw = p.read_bytes()
        require(len(raw) == row['bytes'] and digest(raw) == row['sha256'], 'Original byte/SHA changed')
        data[row['archive_relative']] = raw
    return data


def semantics(plan, data):
    rows = {r['source_relative']: r for r in plan['required_source_rows']}
    def original(name):
        return data[rows[STATE + '/' + name]['archive_relative']]
    acceptance = load(original('source-reviews/20261022-root-three-frontiers-193-terminal-acceptance.json'))
    require(digest(original('source-reviews/20261022-root-three-frontiers-193-terminal-acceptance.json')) == ACCEPT_SHA,
            'Root acceptance identity')
    require(acceptance['status'] == 'ROOT_THREE_FRONTIERS_ACTUAL193_TERMINAL_ACCEPTED' and
            [acceptance['owned_modules'], acceptance['declarations'], acceptance['original_receipts']] == [193, 4371, 141],
            'Root accepted scope')
    require(not acceptance['unconditional_main_proved'] and not acceptance['external_closure_replayed'], 'Inflated scope')
    census = load(original('rounds/three-frontiers-run-20261022-current190-v2/candidate-census.json'))
    require(digest(original('rounds/three-frontiers-run-20261022-current190-v2/candidate-census.json')) ==
            acceptance['current_census_sha256'], 'Accepted census identity')
    before = load(original('source-reviews/20261022T013659602111Z-lcmpayment868a-v4-fresh-baseline189-runtime-fresh-current-terminal-owned-census.json'))
    require(set(census['modules']) - set(before['modules']) == set(TARGETS), 'Wrong additive target set')
    require(all(census['modules'][n] == v for n, v in before['modules'].items()), 'Old190 entries changed')
    require(sum(census['modules'][n]['complete_serialized_declarations'] for n in TARGETS) == 44, 'Actual new count')
    # All195 originals are pinned; no embedded current-cache or native paths are traversed.


def validate_source(root):
    require(not under(root, PREFIX).exists(), 'Addon already exists; no EXPORT retry')
    raw = under(root, PLAN).read_bytes()
    plan = check_plan(raw)
    archive_path_budget(root, plan)
    before = protection(root, plan)
    data = source_data(root, plan)
    semantics(plan, data)
    require(protection(root, plan) == before, 'Protected baseline changed while reading')
    return {'status': 'ADDITIVE193_SOURCE_VALIDATION_PASS_READONLY_NOT_EXPORTED',
            'plan_sha256': PLAN_SHA, 'exporter_sha256': digest(Path(__file__).read_bytes()), 'destination': PREFIX,
            'original_files_measured': len(data), 'raw_bytes_measured': sum(map(len, data.values())),
            'protected': before, 'input_map_sha256': digest(json.dumps(
                {n: digest(v) for n, v in data.items()}, sort_keys=True).encode()),
            'Git_publication_claimed': False, 'new_kernel_check_claimed': False}


def deterministic_gzip(raw):
    out = io.BytesIO()
    with gzip.GzipFile(filename='', mode='wb', compresslevel=9, mtime=0, fileobj=out) as stream:
        stream.write(raw)
    return out.getvalue()


def validate_archive(root):
    dest = under(root, PREFIX)
    plan = check_plan(under(dest, 'source-plan.json').read_bytes())
    archive_path_budget(root, plan)
    before = protection(root, plan)
    manifest = load(under(dest, 'archive-manifest.json').read_bytes())
    require(manifest['plan_sha256'] == PLAN_SHA and manifest['scope'] == 'ADDITIVE_ORIGINAL_EVIDENCE_ONLY', 'Archive scope')
    require(manifest['Git_commit'] is None and manifest['remote_publication'] is None and
            manifest['external_closure_replayed'] is False and manifest['unconditional_main_proved'] is False,
            'Predicted publication or inflated proof scope')
    actual = files(dest)
    require(set(actual) == set(manifest['files']) | {'archive-manifest.json'}, 'Archive exact file set')
    require({n: h for n, h in actual.items() if n != 'archive-manifest.json'} == manifest['files'], 'Archive file hashes')
    expected_paths = {r['archive_relative'] for r in plan['required_source_rows']} | {
        'source-plan.json', 'validate-addon.py', 'README.txt', 'publication-authorization.json', 'source-validation.json'}
    require(set(manifest['files']) == expected_paths, 'Unexpected/missing payload')
    require(under(dest, 'README.txt').read_bytes() == SCOPE, 'README scope changed')
    auth_raw = under(dest, 'publication-authorization.json').read_bytes()
    auth, validation = load(auth_raw), load(under(dest, 'source-validation.json').read_bytes())
    require(auth['status'] == 'ROOT_AUTHORIZED_THREE_FRONTIERS193_ADDITIVE_EXPORT' and auth['destination'] == PREFIX and
            auth['plan_sha256'] == PLAN_SHA and auth['exporter_sha256'] == actual['validate-addon.py'] and
            auth['source_validation_sha256'] == actual['source-validation.json'], 'Archived approval binding')
    require(validation['exporter_sha256'] == actual['validate-addon.py'] and validation['plan_sha256'] == PLAN_SHA and
            validation['protected'] == before, 'Archived source validation binding')
    require(validation['status'] == 'ADDITIVE193_SOURCE_VALIDATION_PASS_READONLY_NOT_EXPORTED' and
            validation['destination'] == PREFIX and actual['validate-addon.py'] == digest(Path(__file__).read_bytes()),
            'Wrong archived validator or source validation scope')
    raw_data = {}
    for row in plan['required_source_rows']:
        raw = under(dest, row['archive_relative']).read_bytes()
        if row['encoding'] == 'deterministic-gzip-mtime0':
            require(raw[:4] == b'\x1f\x8b\x08\x00' and raw[4:8] == b'\0\0\0\0', 'Noncanonical gzip header')
            raw = gzip.decompress(raw)
        require(len(raw) == row['bytes'] and digest(raw) == row['sha256'], 'Archived original reconstruction mismatch')
        raw_data[row['archive_relative']] = raw
    semantics(plan, raw_data)
    require(validation['original_files_measured'] == len(raw_data) and
            validation['raw_bytes_measured'] == sum(map(len, raw_data.values())) and
            validation['input_map_sha256'] == digest(json.dumps(
                {n: digest(v) for n, v in raw_data.items()}, sort_keys=True).encode()),
            'Archived originals differ from source validation measurement')
    require(protection(root, plan) == before, 'Protected baseline changed during archive validation')
    require(manifest['protected'] == before, 'Archive baseline protection binding')
    return {'status': 'ADDITIVE193_ARCHIVE_EXACT_PASS_NOT_GIT_PUBLICATION', 'destination': PREFIX,
            'actual_files': len(actual), 'archive_manifest_sha256': actual['archive-manifest.json'],
            'actual_archive_bytes': sum(under(dest, n).stat().st_size for n in actual),
            'raw_original_files': len(raw_data), 'accepted_reference_counts': [193, 4371, 141],
            'external_closure_replayed': False, 'unconditional_main_proved': False}


def export(root, authorization_sha):
    require(isinstance(authorization_sha, str) and len(authorization_sha) == 64 and
            all(c in '0123456789abcdef' for c in authorization_sha), 'Explicit root authorization SHA required')
    validation = validate_source(root)
    auth_raw = under(root, AUTH).read_bytes()
    require(digest(auth_raw) == authorization_sha, 'Authorization SHA mismatch')
    auth = load(auth_raw)
    validation_raw = under(root, VALIDATION).read_bytes()
    require(load(validation_raw) == validation, 'Source validation stale or unbound')
    require(auth['status'] == 'ROOT_AUTHORIZED_THREE_FRONTIERS193_ADDITIVE_EXPORT' and auth['destination'] == PREFIX and
            auth['mode'] == 'EXPORT_EXCLUSIVE' and auth['no_overwrite'] is True and
            auth['plan_sha256'] == PLAN_SHA and auth['exporter_sha256'] == validation['exporter_sha256'] and
            auth['source_validation_sha256'] == digest(validation_raw), 'Root authorization content')
    plan_raw = under(root, PLAN).read_bytes()
    plan = check_plan(plan_raw)
    data = source_data(root, plan)
    semantics(plan, data)
    before = protection(root, plan)
    require(before == validation['protected'], 'Protected archive changed before EXPORT')
    require(digest(json.dumps({n: digest(v) for n, v in data.items()}, sort_keys=True).encode()) ==
            validation['input_map_sha256'], 'Inputs changed after source validation')
    dest = under(root, PREFIX)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.mkdir(exist_ok=False)
    payload = {r['archive_relative']: deterministic_gzip(data[r['archive_relative']])
               if r['encoding'] == 'deterministic-gzip-mtime0' else data[r['archive_relative']]
               for r in plan['required_source_rows']}
    payload.update({'source-plan.json': plan_raw, 'validate-addon.py': Path(__file__).read_bytes(),
                    'README.txt': SCOPE, 'publication-authorization.json': auth_raw, 'source-validation.json': validation_raw})
    for name, raw in payload.items():
        p = under(dest, name)
        p.parent.mkdir(parents=True, exist_ok=True)
        with p.open('xb') as stream:
            stream.write(raw)
    manifest = {'schema': 'three-frontiers193-additive-archive-v2-compact-paths', 'scope': 'ADDITIVE_ORIGINAL_EVIDENCE_ONLY',
                'plan_sha256': PLAN_SHA, 'protected': before,
                'files': {n: digest(v) for n, v in sorted(payload.items())},
                'Git_commit': None, 'remote_publication': None, 'external_closure_replayed': False,
                'unconditional_main_proved': False}
    with under(dest, 'archive-manifest.json').open('xb') as stream:
        stream.write((json.dumps(manifest, indent=2) + '\n').encode())
    require(source_data(root, plan) == data, 'Original bytes changed across EXPORT')
    require(protection(root, plan) == before, 'Protected files changed across EXPORT')
    return validate_archive(root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['validate-source', 'EXPORT', 'validate-archive'])
    parser.add_argument('--root', required=True)
    parser.add_argument('--authorization-sha256')
    args = parser.parse_args()
    try:
        root = Path(args.root).resolve(strict=True)
        require(root.is_dir(), 'Root directory')
        if args.mode == 'validate-source':
            result = validate_source(root)
        elif args.mode == 'validate-archive':
            result = validate_archive(root)
        else:
            result = export(root, args.authorization_sha256)
        print(json.dumps(result, sort_keys=True))
    except Exception as error:
        print(json.dumps({'status': 'FIRSTFAIL_HOLD_NO_RETRY', 'mode': args.mode,
                          'error_type': type(error).__name__, 'error': str(error),
                          'partial_addon_preserved': True, 'originals_never_repaired': True}), file=sys.stderr)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
