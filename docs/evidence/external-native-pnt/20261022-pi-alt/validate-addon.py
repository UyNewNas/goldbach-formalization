"""External pi_alt evidence addon. Candidate: root review required before invocation.
No Git, Lean, collector, subprocess, canonical-helper imports, or baseline updates.
validate-source --view original: read-only preflight of originals and baseline.
validate-source --view archive: read-only check of exported addon and baseline.
EXPORT: preflight, exclusive first-time byte copy, then complete archive check.
Any failure stops; partial target is retained and must never be overwritten/retried.
"""
from pathlib import Path, PurePosixPath, PureWindowsPath
import argparse
import hashlib
import json
import os
import re
import stat

PREFIX = 'docs/evidence/external-native-pnt/20261022-pi-alt'
STATE = '.lake/proof-continuation'
REVIEW = 'source-reviews/'
MANIFEST_NAME = '20261022-native-pnt-original-evidence-export-SOURCE-ONLY-manifest.json'
AUTHOR_NAME = '20261022-native-pnt-original-evidence-export-SOURCE-ONLY-author-CP.json'
PEER_NAME = '20261022-native-pnt-original-evidence-export-independent-source-review-HOLD.json'
SIDECARS = {
    'manifest.json': (MANIFEST_NAME, '43d14534bd9b731c5949c50e7e053fb02a552bfd5fa75b1814f9d80da3634f0c'),
    'author-CP.json': (AUTHOR_NAME, '0b40367ffc5762c44a43189a1880a17f1c2294a86c2e4642e8808f6e1b495f97'),
    'peer-review.json': (PEER_NAME, 'b928a02a047d9b98ef778ec5d503e21c9ae19cf201493912adf86ba69021b390'),
}
BASE = 'verification/proof-continuation/2026-10-15/'
BASE_SHA = '956c1a2bb2f15aada2d064b9b42587010ed4f2e34deb27f2aae89812860f13b2'
OLD_VALIDATOR = STATE + '/publication-integrity/independent_checkpoint_20261022_afterc60d71c_190.py'
OLD_VALIDATOR_SHA = '4d51b78265707a7baf3bbc571af6fe862cc6bca105a66f1ab103e381a71c4e6c'
MODULE = 'PrimeNumberTheoremAnd.Consequences'
AUDIT = 'audits/20261022T023156467636Z/'
AUDIT_NAMES = {'OwnedAudit.lean', 'audit-process.json', 'declarations.json',
               'declarations.log', 'receipt.json',
               'replay-' + MODULE + '.json', 'replay-' + MODULE + '.log'}
SLOTS = {'.olean', '.olean.private', '.olean.server', '.ilean', '.ir'}
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
RECORDED_ROOT = '/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'
README = b'''External selected-native pi_alt evidence addon, 2026-10-22

37 original files are copied byte-for-byte; original embedded absolute and LOCAL
paths remain unchanged. manifest.json maps those paths; author-CP.json and
peer-review.json preserve the prior source-only scope and review. Their original
NOT_EXPORTED wording is historical provenance, never rewritten as a receipt.

Only PrimeNumberTheoremAnd.Consequences existing singleton stock/ALL qualification
and all 339 complete serialized records/types/safety/reported standard-three axiom
metadata are archived. This is not a fresh strict producer, nine-module closure,
6029-import proof replay, project bridge, consumer discharge, or owned+339.
Owned baseline remains 190 modules / 4327 declarations / 138 receipts; main OPEN.

The full raw before/after inventories attest unchanged inputs, including 6029
native nodes with explicit five slots, 562 project sources and 690 cache rows.
Most native library sources/objects and all three native binaries remain external
fixed trust, not a self-contained reconstruction environment. Hash inventories
are evidence references; this validator does not re-prove their libraries.

Baseline dependencies are the exact 13 manifest rows (12 physical paths; walker
alias intentional). No original reference is silently updated to a new baseline.
The old190 validator and owned census are not modified. Root separately verifies
existing190 unchanged and staged/commit/tar bytes of this addon. This script makes
no Git membership, remote publication, kernel replay or mathematical claim.

Root-approved invocation order (no automatic retry):
1. validate-source --root ROOT --view original
2. EXPORT --root ROOT
3. validate-source --root ROOT --view archive
Use python with this reviewed candidate or exported validate-addon.py.
Failure stops immediately; originals and any partial addon remain preserved.
Never rerun EXPORT into an existing destination. Root investigates any failure.
'''


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(data.decode('utf-8'), object_pairs_hook=unique)


def relative(name):
    require(isinstance(name, str) and bool(name), 'empty/non-string path')
    p = PurePosixPath(name)
    require(not p.is_absolute() and p.as_posix() == name, 'noncanonical path: ' + name)
    require(all(x not in ('', '.', '..') for x in p.parts), 'path traversal: ' + name)
    for part in p.parts:
        require(not re.search(r'[\\:< >"|?*\x00-\x1f]', part), 'unsafe path component: ' + name)
        require(not part.endswith(('.', ' ')), 'trailing dot/space: ' + name)
        require(part.split('.')[0].upper() not in
                {'CON', 'PRN', 'AUX', 'NUL'} |
                {'COM' + str(i) for i in range(1, 10)} |
                {'LPT' + str(i) for i in range(1, 10)}, 'reserved path: ' + name)
    return p


def no_redirect(path):
    # Check every existing ancestor, including Windows junction/reparse points.
    for p in (path, *path.parents):
        if os.path.lexists(p):
            st = p.lstat()
            require(not stat.S_ISLNK(st.st_mode), 'symlink forbidden: ' + str(p))
            require(not (getattr(st, 'st_file_attributes', 0) & 0x400),
                    'reparse point forbidden: ' + str(p))


def under(root, name):
    p = root.joinpath(*relative(name).parts)
    no_redirect(p)
    require(p.resolve().is_relative_to(root.resolve()), 'resolved escape: ' + name)
    return p


def checked(path, digest, size=None):
    require(re.fullmatch('[0-9a-f]{64}', digest) is not None, 'bad SHA')
    require(path.is_file(), 'missing file: ' + str(path))
    no_redirect(path)
    data = path.read_bytes()
    require(sha(data) == digest, 'SHA mismatch: ' + str(path))
    require(size is None or len(data) == size, 'size mismatch: ' + str(path))
    return data


def windows_from_wsl(path):
    if path.startswith('/mnt/') and len(path) > 7 and path[6] == '/':
        return path[5].upper() + ':\\' + path[7:].replace('/', '\\')
    require(path.startswith('/home/slava/codex-lean-ve/'), 'unrecognized native root')
    return '\\\\wsl.localhost\\Debian' + path.replace('/', '\\')


def attested_source(root, row, require_local):
    wsl = row['source_wsl_absolute']
    # JSON already decoded separators; PureWindowsPath preserves the UNC share.
    win = str(PureWindowsPath(row['source_windows_absolute']))
    require(str(PureWindowsPath(win)).casefold() ==
            str(PureWindowsPath(windows_from_wsl(wsl))).casefold(), 'source path attestation')
    rel = row['source_repo_relative']
    sr = row['source_state_relative']
    if rel is not None:
        relative(rel)
        require(wsl == RECORDED_ROOT + '/' + rel, 'repo source attestation')
        if sr is not None:
            require(rel == STATE + '/' + str(relative(sr)), 'STATE source attestation')
        p = under(root, rel)
        if require_local:
            expected = windows_from_wsl(RECORDED_ROOT) if os.name == 'nt' else RECORDED_ROOT
            require(os.path.normcase(str(root)) == os.path.normcase(expected),
                    'original-view root must be the attested checkout')
        return p
    require(sr is None, 'native source unexpectedly STATE-relative')
    return Path(win if os.name == 'nt' else wsl)


def baseline(root, manifest):
    rows = manifest['reuse_existing190_baseline']
    require(len(rows) == 13, 'baseline rows')
    bm_bytes = checked(under(root, BASE + 'manifest.json'), BASE_SHA, 774118)
    bm = load(bm_bytes)
    require(len(bm['modules']) == 190 and bm['declaration_count'] == 4327, 'owned baseline')
    require(not any(bm[k] for k in ('main_theorem_proved', 'aggregate_build_claimed',
                                   'external_closure_replay_claimed')), 'baseline scope')
    paths = []
    for r in rows:
        name = r['existing_baseline_repo_path']
        require(name.startswith(BASE), 'baseline prefix')
        checked(under(root, name), r['sha256'], r['bytes'])
        if name != BASE + 'manifest.json':
            require(bm['files'][name[len(BASE):]] == r['sha256'], 'baseline manifest coverage')
        paths.append(name)
    require(len(set(paths)) == 12, 'baseline alias census')
    return bm


def semantics(state_data, manifest):
    def data(name):
        require(name in state_data, 'missing original state file: ' + name)
        return state_data[name]
    def j(name):
        return load(data(name))
    b = j('rounds/native-pnt-inputs-20261022-v1/before.json')
    a = j('rounds/native-pnt-inputs-20261022-v1/after.json')
    require(b['phase'] == 'before' and a['phase'] == 'after' and
            a['deep_exact_against_before'] is True and b['inputs'] == a['inputs'], 'deep input equality')
    x = b['inputs']
    require(len(x['native_nodes']) == 6029 and len(x['project_sources562']) == 562 and
            len(x['STATE_cache_and_lib_map']) == 690 and len(x['native_bins']) == 3, 'input census')
    for node in x['native_nodes'].values():
        require(set(node['all_five_slots']) == SLOTS, 'five explicit slots')
        require(all(v is None or re.fullmatch('[0-9a-f]{64}', v)
                    for v in node['all_five_slots'].values()), 'slot SHA/None')
    protected = {r.get('original_reference'): r['sha256']
                 for r in manifest['reuse_existing190_baseline'] if r.get('original_reference') and r['original_reference'] not in
                 ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')}
    protected['preflight_current_oct20.py'] = next(
        r['sha256'] for r in manifest['must_archive_original_files']
        if r['source_state_relative'] == 'preflight_current_oct20.py')
    for row in manifest['must_archive_original_files']:
        if row['category'] == 'exact_native_checker_API_source':
            protected[row['source_wsl_absolute']] = row['sha256']
    require(x['protected_apis'] == protected, 'protected API attestation')
    for pin, digest in x['pins'].items():
        matches = [r for r in manifest['reuse_existing190_baseline']
                   if r.get('original_reference') == pin]
        require(len(matches) == 1 and matches[0]['sha256'] == digest, 'pin binding')
    proper = j('preflights/20261022T021630789741Z-exact-current-' + MODULE + '.json')
    require(proper['status'] == 'READONLY_PROPER_GRAPH_EXISTING_RECURSIVE_CACHES_EXACT', 'proper scope')
    require(x['original_proper']['sha256'] == sha(data(
            'preflights/20261022T021630789741Z-exact-current-' + MODULE + '.json')),
            'proper input reference')
    require(x['collector']['sha256'] == sha(data(
            'rounds/20261022-native-pnt-original-inputs-SOURCE-ONLY.py')), 'collector input reference')
    target_rows = {r['proposed_archive_path']: r for r in manifest['must_archive_original_files']}
    require(target_rows[PREFIX + '/native-target/PrimeNumberTheoremAnd/Consequences.lean']['sha256']
            == x['source_sha256'] == x['native_nodes'][MODULE]['source_sha256'], 'target source binding')
    for suffix in ('.olean', '.ilean'):
        require(target_rows[PREFIX + '/native-target/PrimeNumberTheoremAnd/Consequences' + suffix]['sha256']
                == x['native_nodes'][MODULE]['all_five_slots'][suffix], 'target object binding')
    r = j(AUDIT + 'receipt.json')
    require(r['status'] == 'PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS', 'selected receipt status')
    require(r['targets'] == {MODULE: x['source_sha256']} and
            r['inputs_before'] == r['inputs_after'], 'selected receipt inputs')
    parts = {k: v for k, v in x['native_nodes'][MODULE]['all_five_slots'].items() if v is not None}
    ri = r['inputs_before']
    require(ri['pins'] == x['pins'] and ri['sources'] == r['targets'] and
            ri['owned_object_parts'] == {MODULE: parts} and
            ri['lean_real_sha256'] == x['native_bins']['lean.real'] and
            ri['checker_sha256'] == x['native_bins']['leanchecker'], 'selected input bindings')
    require(not r['external_closure_replay_claimed'] and not r['unconditional_main_claimed'], 'receipt scope')
    require(r['audit_runner_sha256'] == protected['audit_owned.py'] and
            r['source_template_sha256'] == protected['../../verification/parts/p0/queue/AuditTemplate.lean'] and
            r['generated_audit_sha256'] == sha(data(AUDIT + 'OwnedAudit.lean')), 'runner/template binding')
    stocks = [s for s in r['stages'] if s['kind'] == 'stock_replay']
    types = [s for s in r['stages'] if s['kind'] == 'full_inventory_type_axioms']
    require(len(stocks) == len(types) == 1 and stocks[0]['module'] == MODULE and
            types[0]['exit_code'] == 0, 'selected stages')
    stock = stocks[0]['result']
    replay = j(AUDIT + 'replay-' + MODULE + '.json')
    require(replay == stock, 'stock JSON exact')
    ap = j(AUDIT + 'audit-process.json')
    for p in (stock, ap):
        require(p['status'] == 'PASS' and p['returncode'] == 0 and p['guard_error'] is None,
                'process result')
        require(p['rss_guard']['limit_mib'] == 6656 and p['max_rss_kib'] <= 6656 * 1024, 'RSS scope')
    require(ap['command'][1:4] == ['-j2', '-M6144', '-DwarningAsError=true'], 'audit command')
    require(stock['log_sha256'] == sha(data(AUDIT + 'replay-' + MODULE + '.log')) and
            types[0]['log_sha256'] == sha(data(AUDIT + 'declarations.log')), 'log bindings')
    inventory, emitted = {}, {}
    for line in data(AUDIT + 'declarations.log').decode('utf-8').splitlines():
        if line.startswith('P0_QUEUE_INVENTORY '):
            z = load(line.split(' ', 1)[1].encode())
            require(z['module'] not in inventory, 'duplicate inventory'); inventory[z['module']] = z
        elif line.startswith('P0_QUEUE_DECL '):
            z = load(line.split(' ', 1)[1].encode())
            require(z['name'] not in emitted, 'duplicate declaration'); emitted[z['name']] = z
    records = j(AUDIT + 'declarations.json')
    require(len(records) == len(emitted) == r['declaration_counts'][MODULE] == 339, '339 census')
    require({z['name']: z for z in records} == emitted and set(inventory) == {MODULE}, 'JSON/log equality')
    inv = inventory[MODULE]
    require(len(inv['serialized']) == len(set(inv['serialized'])) ==
            len(inv['environment']) == len(set(inv['environment'])) == 339 and
            set(emitted) == set(inv['serialized']) == set(inv['environment']), 'all serialized names')
    for z in records:
        require(z['module'] == MODULE and isinstance(z['type'], str) and z['type'] and
                '⋯' not in z['type'], 'full type')
        require(z['unsafe'] is False and z['partial'] is False and z['axiom'] is False and
                set(z['axioms']) <= STD3, 'safety/reported std3')
    q = j('source-reviews/20261022-root-native-pnt-pi-alt-scoped-qualification.json')
    require(q['supplier'] == emitted['pi_alt'] and q['actual_complete_native_declarations'] == 339 and
            q['owned_modules_added'] == 0 and q['owned_modules'] == 190 and
            q['declarations'] == 4327 and q['original_owned_receipts'] == 138, 'qualification scope')
    require(not any(q[k] for k in ('fresh_nine_module_import_closure_replayed',
            'historical_strict_producer_reproduced', 'project_bridge_materialized',
            'hPNT_consumers_discharged', 'unconditional_main_proved')), 'qualification nonclaims')


def preflight(root, view):
    dest = under(root, PREFIX)
    side = {}
    for target, (source, digest) in SIDECARS.items():
        path = under(root, STATE + '/' + REVIEW + source) if view == 'original' else under(dest, target)
        side[target] = checked(path, digest)
    manifest = load(side['manifest.json'])
    require(manifest['proposed_destination'] == PREFIX and
            manifest['new_archive_file_count'] == 37, 'fixed destination/count')
    baseline(root, manifest)
    if view == 'original':
        checked(under(root, OLD_VALIDATOR), OLD_VALIDATOR_SHA)
    rows = manifest['must_archive_original_files']
    require(len(rows) == 37 and sum(r['bytes'] for r in rows) == 39931065, 'original census')
    targets, state_data, payload = [], {}, {}
    for row in rows:
        target = row['proposed_archive_path']
        require(target.startswith(PREFIX + '/'), 'target prefix')
        name = target[len(PREFIX) + 1:]
        relative(name)
        targets.append(name)
        source = attested_source(root, row, view == 'original')
        path = source if view == 'original' else under(dest, name)
        content = checked(path, row['sha256'], row['bytes'])
        payload[name] = content
        sr = row['source_state_relative']
        if sr is not None:
            require(sr not in state_data, 'duplicate STATE row'); state_data[sr] = content
    require(len({n.casefold() for n in targets}) == 37, 'casefold target collisions')
    audit_set = {n[len(AUDIT):] for n in state_data if n.startswith(AUDIT)}
    require(audit_set == AUDIT_NAMES, 'all seven audit files')
    if view == 'original':
        audit_dir = under(root, STATE + '/' + AUDIT.rstrip('/'))
        actual = set()
        for p in audit_dir.rglob('*'):
            no_redirect(p)
            if p.is_file(): actual.add(p.relative_to(audit_dir).as_posix())
        require(actual == AUDIT_NAMES, 'recursive original audit completeness')
    semantics(state_data, manifest)
    payload.update(side)
    payload['scopeREADME.md'] = README
    payload['validate-addon.py'] = Path(__file__).read_bytes()
    require(len(payload) == 42 and len({n.casefold() for n in payload}) == 42, 'addon file census')
    if view == 'archive':
        actual = set()
        for p in dest.rglob('*'):
            no_redirect(p)
            if p.is_file(): actual.add(p.relative_to(dest).as_posix())
        require(actual == set(payload), 'exact archive file set')
        for name, content in payload.items():
            require(under(dest, name).read_bytes() == content, 'archive byte equality: ' + name)
    return dest, manifest, payload


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('validate-source', 'EXPORT'))
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--view', choices=('original', 'archive'), default='original')
    args = parser.parse_args()
    root = args.root.absolute()
    no_redirect(root)
    require(root.is_dir(), 'root missing')
    require(args.mode != 'EXPORT' or args.view == 'original', 'EXPORT requires original view')
    dest = under(root, PREFIX)
    if args.mode == 'EXPORT':
        require(not os.path.lexists(dest), 'target exists; stop, preserve, no retry/overwrite')
    dest, manifest, payload = preflight(root, args.view)
    if args.mode == 'EXPORT':
        # Complete read-only validation precedes first mutation. Exclusive writes only.
        require(not os.path.lexists(dest), 'target appeared after preflight')
        dest.mkdir(parents=True, exist_ok=False)
        original_rows = {r['proposed_archive_path'][len(PREFIX) + 1:]: r
                         for r in manifest['must_archive_original_files']}
        for name, content in payload.items():
            if name in original_rows:
                row = original_rows[name]
                require(checked(attested_source(root, row, True), row['sha256'], row['bytes'])
                        == content, 'source changed at copy time: ' + name)
            p = under(dest, name)
            p.parent.mkdir(parents=True, exist_ok=True)
            with p.open('xb') as stream:
                require(stream.write(content) == len(content), 'short write: ' + name)
            checked(p, sha(content), len(content))
        preflight(root, 'archive')
    print(json.dumps({'scope': 'EXTERNAL_SELECTED_NATIVE_PNT_ADDON_ONLY',
                      'mode': args.mode, 'view': args.view, 'passed': True,
                      'original_files': 37, 'addon_files': 42, 'native_declarations': 339,
                      'owned_modules': 190, 'owned_declarations': 4327,
                      'owned_added': 0, 'Git_membership_checked': False,
                      'fresh_replay': False, 'main_proved': False}))


if __name__ == '__main__':
    main()
