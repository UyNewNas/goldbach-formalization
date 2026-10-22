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

PREFIX = 'docs/evidence/owned-frontiers/20261022-eu-multiplicity-rational-singular-v1'
STATE = '.lake/proof-continuation'
PLAN = STATE + '/source-reviews/20261022-eu-multiplicity-rational-singular-v1-FROZEN-v1-additive-publication-source-plan.json'
PLAN_SHA = '2a2906feb89f951b39f227c2ac5fb9db37ad24d12d2df3125faabc4157201d36'
ORIGINAL_ROWS_SHA = '4ba763c5b168ef9e3076271665f27f7927941e91c0b5c10aad9d2ee4adfcfd09'
AUTH = STATE + '/publication-integrity/20261022-eu-multiplicity-rational-singular-v1-FROZEN-v1-root-export-authorization.json'
VALIDATION = STATE + '/publication-integrity/20261022-eu-multiplicity-rational-singular-v1-FROZEN-v1-source-validation.json'
BASE = 'verification/proof-continuation/2026-10-15'
BASE_SHA = '956c1a2bb2f15aada2d064b9b42587010ed4f2e34deb27f2aae89812860f13b2'
ACCEPT_SHA = 'f83bdef6b8b20c1f9c3e07314bc2d7d48ed1cf697be020f9dd9d5a5644017d35'
TARGETS = {'ImbalancedChen.Multiplicity': '9d10526b9efe91336095c2bf1ec7fe860fb6e373613b0bf7915c370fb97800a6',
           'ImbalancedChen.RationalPowers': '40d21d2c61d61862e3c29769d2220243ecf7bfb43fb9b9690597dd769f07ca06',
           'ImbalancedChen.SingularSeries': 'ff771bfd1018fc0efaed6a56c26473033787d0de1949f737ef1012d024c9b2b3'}
SCOPE = b'''Additive original evidence for Multiplicity, RationalPowers and SingularSeries.
Root local acceptance:196 modules /4459 per-module serialized records /144 receipts.
Delta: Multiplicity40, RationalPowers18, SingularSeries30 =88 records /3 receipts.
Multiplicity proves the exact positive-receiver Omega<=2 partition, with the
receiver-one correction equal to the indicator that N-1 is prime. RationalPowers
clears a positive denominator and proves the literal real-power representation
bridge; the factor-witness prime case retains exponent nonnegativity.
SingularSeries proves convergence and positivity of the actual odd-prime product
without a leading factor2, the finite correction lower bound, normalization growth
and unit absorption. The prime-divisor interpretation retains N!=0; zero uses the
empty-primeFactors total convention. No sieve or prime-count estimate is supplied.
Analytic lower/upper assumptions, filtered B/hUpper/K/strong distribution and the
main1+1.75 theorem remain OPEN. Difficulty-weighted progress remains30 percent.

Old190 canonical, PNT42 selected-native addon, and193v2 full201 physical files are
protected dependencies, never copied as newly replayed kernel evidence. Failed193v1
partial exactly two files stays preserved. No old193 replay is claimed. PNT remains
a selected qualification, not an owned+339 or full external native closure replay.
All20 serial events,6 preparation stages,original commands/logs/process sidecars,
full captures,strict receipts and stock/ALL complete records are preserved as exact
raw bytes or deterministic gzip. Every full original path and role is retained in
source-plan.json under short p/<index>-<full SHA>.raw/.gz names. Output paths are
checked before writes: at most230 characters and100 per component. Historical
absolute paths and SOURCE-ONLY/HOLD text remain unchanged. Captured old/current
cache paths and foreign source/object/header/registry paths are historical fixed
imported trust: no current-cache substitution or external-path traversal occurs.
Hash inventories do not make a self-contained proof replay. Root independently
checks staged bytes, committed blobs and package membership after actual export.

Protocol: readonly validate-source; root preserves its exact stdout JSON and issues
a new authorization binding source-validation SHA, exporter SHA, plan SHA, prefix
and exclusive/no-overwrite mode; root invokes EXPORT exactly once; validate-archive.
The first error is sticky HOLD. Preserve every partial byte, stdout/stderr/process
record. No retry, repair, restore or cleanup. This validator performs no new kernel
check, Git publication or unconditional main proof. All archive sizes and Git refs
must be measured by root from actual results and are never predicted here.
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
    required = ('root_acceptance_reference', 'root_acceptance_sha256', 'root_acceptance_status',
                'accepted_census_reference', 'accepted_census_sha256', 'accepted_counts', 'delta_counts', 'required_source_rows',
                'source_files_measured', 'source_bytes_measured', 'original_rows_sha256',
                'root_actual_check_reference', 'root_actual_check_status', 'scope_peer_reference', 'required_reference_sources',
                'protected193v2', 'protected_failed193v1')
    require(all(key in plan and plan[key] is not None for key in required), 'Unbound required plan field')
    require(plan['schema'] == 'eu-multiplicity-rational-singular196-additive-source-plan-v1', 'Plan schema')
    require(plan['destination'] == PREFIX and plan['root_acceptance_sha256'] == ACCEPT_SHA, 'Plan target/acceptance')
    require(plan['accepted_counts'] == [196, 4459, 144] and plan['delta_counts'] == [3, 88, 3], 'Plan scope')
    rows = plan['required_source_rows']
    require(len(rows) == plan['source_files_measured'] == 227, 'Fixed original inventory')
    require(plan['original_rows_sha256'] == ORIGINAL_ROWS_SHA, 'Unbound original identity digest')
    require(sum(row['bytes'] for row in rows) == plan['source_bytes_measured'], 'Raw original byte count')
    require(len({(r['anchor'], r['source_relative']) for r in rows}) == len(rows), 'Duplicate original source')
    require(len({r['archive_relative'].casefold() for r in rows}) == len(rows), 'Archive collisions')
    identity = [{key: row[key] for key in ('anchor', 'bytes', 'encoding', 'role', 'sha256', 'source_relative')}
                for row in rows]
    require(digest(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()) == ORIGINAL_ROWS_SHA,
            'Original frozen row identity/order changed')
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
    owned = plan['protected193v2']
    require(owned['prefix'] == 'docs/evidence/owned-frontiers/20261022-three-frontiers-193-v2' and
            len(owned['files']) == 201 and
            owned['files']['archive-manifest.json'] ==
            '8b967a80a5874538de40a9be29a0df2fe17c87533991efa366a366a4c7690dcd', '193v2 protection schema')
    require(files(under(root, owned['prefix'])) == owned['files'], 'Any193v2 byte/path changed')
    partial = plan['protected_failed193v1']
    require(partial['prefix'] == 'docs/evidence/owned-frontiers/20261022-three-frontiers-193' and
            len(partial['files']) == 2, 'Failed193v1 partial protection schema')
    require(files(under(root, partial['prefix'])) == partial['files'], 'Failed193v1 partial changed')
    return {'old190_manifest_sha256': BASE_SHA, 'old190_payload_files': 3661, 'old190_physical_files': 3662,
            'PNT42_map_sha256': digest(json.dumps(pnt['files'], sort_keys=True).encode()), 'PNT_files': 42,
            'owned193v2_map_sha256': digest(json.dumps(owned['files'], sort_keys=True).encode()),
            'owned193v2_files': 201,
            'failed193v1_map_sha256': digest(json.dumps(partial['files'], sort_keys=True).encode()),
            'failed193v1_files': 2}


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
    def source_name(name):
        prefixes = ('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation/',
                    'E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation/')
        name = name.replace('\\', '/')
        for prefix in prefixes:
            if name.startswith(prefix):
                name = name[len(prefix):]
                break
        if name.startswith(('rounds/', 'source-reviews/', 'preflights/', 'runs/', 'audits/',
                            'publication-integrity/')):
            name = STATE + '/' + name
        relative(name)
        return name
    def original(name):
        return data[rows[source_name(name)]['archive_relative']]
    def bound(ref):
        require(isinstance(ref, dict) and set(ref) == {'path', 'sha256'}, 'Reference schema')
        raw = original(ref['path'])
        require(digest(raw) == ref['sha256'], 'Referenced original digest mismatch')
        return raw
    def referenced(value):
        if isinstance(value, dict):
            if isinstance(value.get('path'), str) and isinstance(value.get('sha256'), str):
                bound({'path': value['path'], 'sha256': value['sha256']})
            for child in value.values():
                referenced(child)
        elif isinstance(value, list):
            for child in value:
                referenced(child)
    for name in plan['required_reference_sources']:
        referenced(load(original(name)))
    acceptance = load(original(plan['root_acceptance_reference']))
    require(digest(original(plan['root_acceptance_reference'])) == ACCEPT_SHA, 'Root acceptance identity')
    require(acceptance['status'] == plan['root_acceptance_status'] == 'ROOT_EU_MULTIPLICITY_RATIONAL_SINGULAR_ACTUAL196_TERMINAL_ACCEPTED' and
            [acceptance['owned_modules'], acceptance['declarations'], acceptance['original_receipts']] == [196, 4459, 144],
            'Root accepted scope')
    require(not acceptance['unconditional_main_proved'] and not acceptance['external_closure_replayed'], 'Inflated scope')
    require(acceptance['main_1_plus_1_75'] == 'OPEN' and acceptance['difficulty_weighted_progress_percent'] == 30,
            'Main theorem/progress scope changed')
    require([acceptance['added_modules'], acceptance['added_complete_serialized_declarations'],
             acceptance['added_original_receipts']] == [3, 88, 3], 'Root actual additive count')
    census_raw = original(plan['accepted_census_reference'])
    census = load(census_raw)
    require(digest(census_raw) == acceptance['current_census_sha256'] ==
            plan['accepted_census_sha256'], 'Accepted census identity')
    before_raw = original('rounds/three-frontiers-run-20261022-current190-v2/candidate-census.json')
    require(digest(before_raw) == 'd2889d2ff857a73a6c225a0ef8f4237c3a203d74eb5dd70f2b69ce70b45c6749',
            'Old193 dependency census identity')
    before = load(before_raw)
    require(set(census['modules']) - set(before['modules']) == set(TARGETS), 'Wrong additive target set')
    require(all(census['modules'][n] == v for n, v in before['modules'].items()), 'Old193 whole entries changed')
    require(len(census['modules']) == census['owned_modules'] == 196 and
            census['complete_serialized_declarations'] == 4459 and
            census['original_owned_receipts_rehashed'] == 144, 'Census actual counts')
    old_acceptance = load(original('source-reviews/20261022-root-three-frontiers-193-terminal-acceptance.json'))
    scopes = {item['module']: item for item in acceptance['scope_reviews']}
    require(len(scopes) == len(acceptance['scope_reviews']) == 6, 'Six scoped acceptance bindings')
    require(all(scopes[item['module']] == item for item in old_acceptance['scope_reviews']),
            'Old193 scope entries changed')
    require(acceptance['root_protocol_verification'] == plan['root_actual_check_reference'] and
            acceptance['independent_batch_review'] == plan['scope_peer_reference'] and
            acceptance['root_protocol_process_exit_code'] == 0 and
            acceptance['previous193_scope_reviews_inherited_verbatim'] is True,
            'Root protocol/semantic acceptance bindings')
    actual_check = load(bound(plan['root_actual_check_reference']))
    require(actual_check['status'] == plan['root_actual_check_status'] == 'ROOT_INDEPENDENT_ALL20_PROTOCOL_NATIVE_AND_CURRENT_CENSUS_PASS_PENDING_SEMANTIC_SCOPE_ACCEPTANCE',
            'Root actual successful check identity/status')
    require(actual_check['actual_counts'] == {'owned_modules': 196, 'declarations': 4459, 'original_receipts': 144} and
            actual_check['actual_new_module_record_counts'] == {
                'ImbalancedChen.Multiplicity': 40, 'ImbalancedChen.RationalPowers': 18,
                'ImbalancedChen.SingularSeries': 30}, 'Root actual measured counts')
    require(actual_check['all20_stage_chain_original_logs_and_input_maps_exact'] is True and
            actual_check['current562_sources_exact'] is True and
            actual_check['current_entire_artifact_map_exact'] is True and
            actual_check['baseline_whole_module_entries_unchanged'] is True and
            actual_check['per_target_new_strict'] == actual_check['per_target_singleton_stock_ALL'] == 1 and
            actual_check['retries'] == 0, 'Root actual protocol/census scope')
    require(actual_check['original_native_union_reconstructed_and_all_paths_rehashed'] == {
                'paths': 25590, 'absent_sources': 0,
                'map_sha256': '8ca6e156fea3bd32eaed29bc8d4c8fc5a44ee09ccc1bd5337f9c72491cb6f11b'} and
            actual_check['native_alias_before'] == actual_check['native_alias_after'] and
            len(actual_check['native_alias_before']) == 8 and
            actual_check['current_native_trust_boundary_not_entire_closure_fresh_replay'] is True,
            'Root actual original-native imported-trust boundary')
    peer = load(bound(plan['scope_peer_reference']))
    require(peer['status'] == 'ACTUAL_BATCH_SCOPED_EVIDENCE_PASS_PENDING_ROOT_INDEPENDENT_ACCEPTANCE',
            'Historical actual scoped peer identity/status')
    require({item['module'] for item in peer['new_scope_reviews']} == set(TARGETS), 'Peer exact3 scope set')
    for item in peer['new_scope_reviews']:
        expected_scope = dict(item)
        expected_scope.update(path=plan['scope_peer_reference']['path'],
                              sha256=plan['scope_peer_reference']['sha256'], history_stage_hashes_match=True)
        require(scopes[item['module']] == expected_scope, 'Whole new3 original scope values changed')
    gate_name = 'rounds/20261022-EU-next-three-current193-root-SERIAL-gate.json'
    gate_raw = original(gate_name)
    gate = load(gate_raw)
    require(gate['targets'] == TARGETS and len(gate['pipeline']) == 20, 'Exact3 original gate/pipeline')
    prep = 'rounds/three-frontiers-preparation-20261022-next-three-current193/'
    prep_previous = None
    for index, module in enumerate(TARGETS):
        for offset, kind in enumerate(('proper', 'capture')):
            stage_index = index * 2 + offset
            prep_raw = original(prep + f'{stage_index:03d}-finished.json')
            prep_event = load(prep_raw)
            prep_started = load(original(prep + f'{stage_index:03d}-started.json'))
            require(prep_event['status'] == 'PASS' and
                    prep_event['stage'] == prep_started['stage'] == module + ':' + kind,
                    'Original six preparation stages')
            require(prep_event['previous'] == prep_started['previous'] and
                    (prep_previous is None or prep_event['previous']['sha256'] == prep_previous),
                    'Original preparation chain')
            prep_previous = digest(prep_raw)
        bound(gate['prepared'][module])
    prep_terminal = load(original(prep + 'TERMINAL.json'))
    require(prep_terminal['last_event']['sha256'] == prep_previous, 'Original preparation terminal')
    run = 'rounds/three-frontiers-run-20261022-next-three-current193/'
    previous = None
    events = []
    for index, stage in enumerate(gate['pipeline']):
        event_raw = original(run + f'{index:03d}-finished.json')
        event = load(event_raw)
        started = load(original(run + f'{index:03d}-started.json'))
        require(event['status'] == 'PASS' and event['stage'] == stage == started['stage'], 'Original20 stage scope')
        require(digest(bound(event['started'])) == digest(original(run + f'{index:03d}-started.json')),
                'Original started binding')
        require(event['gate']['sha256'] == started['gate']['sha256'] == digest(gate_raw), 'Original gate binding')
        require(event['previous'] == started['previous'], 'Original previous boundary mismatch')
        if previous is not None:
            require(event['previous']['sha256'] == previous, 'Original20 stage chain mismatch')
        previous = digest(event_raw)
        events.append(event)
    terminal = load(original(run + 'TERMINAL.json'))
    require(terminal['final_event']['sha256'] == previous and terminal['retries'] == 0 and
            terminal['main_1_plus_1_75'] == 'OPEN' and
            terminal['result']['candidate_census']['sha256'] == digest(census_raw), 'Original terminal binding')
    counts = {'ImbalancedChen.Multiplicity': 40, 'ImbalancedChen.RationalPowers': 18,
              'ImbalancedChen.SingularSeries': 30}
    total, axioms = 0, set()
    for index, (module, source_sha) in enumerate(TARGETS.items()):
        strict_event, audit_event = events[3 + index * 6], events[4 + index * 6]
        require(strict_event['result']['execution_counts'] == {
            'runtime_check_invocations': 1, 'actual_new_strict_compilations': 1,
            'matching_strict_evidence_reuses': 0, 'expected_mode': 'NEW_CANONICAL_STRICT'}, 'Original NEW_STRICT scope')
        strict = load(bound(strict_event['result']['strict']))
        require(strict['status'] == 'PASS' and strict['module'] == module and strict['exit_code'] == 0 and
                strict['warnings_as_errors'] is True and strict['binding'] == strict['binding_after'] and
                strict['binding']['source_sha256'] == source_sha, 'Original strict binding')
        result = audit_event['result']
        audit_raw = bound(result['audit'])
        audit = load(audit_raw)
        require(audit['status'] == 'PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and
                audit['targets'] == {module: source_sha} and
                audit['inputs_before'] == audit['inputs_after'] and
                audit['declaration_counts'] == {module: counts[module]} and
                result['stock_ALL_invocations'] == 1, 'Original singleton stock/ALL binding')
        records_raw = bound(result['evidence']['declarations.json'])
        records = load(records_raw)
        entry = census['modules'][module]
        require(len(records) == counts[module] == entry['complete_serialized_declarations'] and
                entry['source_sha256'] == source_sha and entry['owned_receipt_sha256'] == digest(audit_raw) and
                entry['declarations_json_sha256'] == digest(records_raw), 'Original complete record/census binding')
        require(len({record['name'] for record in records}) == len(records), 'Duplicate complete declaration')
        for record in records:
            require(record['module'] == module and isinstance(record['type'], str) and record['type'] and
                    record['axiom'] is False and record['unsafe'] is False and record['partial'] is False and
                    set(record['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Fulltype/safety/std3 scope')
            axioms.update(record['axioms'])
        require(scopes[module]['source_sha256'] == source_sha and scopes[module]['serialized'] == len(records) and
                scopes[module]['declarations_json_sha256'] == digest(records_raw) and
                scopes[module]['strict_receipt_sha256'] == digest(bound(strict_event['result']['strict'])) and
                scopes[module]['audit_receipt_sha256'] == digest(audit_raw) and
                scopes[module]['fulltype_hashes_or_records_match_actual_audit'] is True,
                'New3 scoped complete audit identity')
        total += len(records)
    require(total == 88 and axioms == {'propext', 'Classical.choice', 'Quot.sound'}, 'All88 fulltypes/std3')
    # All frozen originals are pinned. Embedded historical cache/native paths are not traversed.


def validate_source(root):
    require(not under(root, PREFIX).exists(), 'Addon already exists; no EXPORT retry')
    raw = under(root, PLAN).read_bytes()
    plan = check_plan(raw)
    archive_path_budget(root, plan)
    before = protection(root, plan)
    data = source_data(root, plan)
    semantics(plan, data)
    require(protection(root, plan) == before, 'Protected baseline changed while reading')
    return {'status': 'ADDITIVE196_SOURCE_VALIDATION_PASS_READONLY_NOT_EXPORTED',
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
    require(auth['status'] == 'ROOT_AUTHORIZED_EU_MULTIPLICITY_RATIONAL_SINGULAR196_ADDITIVE_EXPORT' and auth['destination'] == PREFIX and
            auth['plan_sha256'] == PLAN_SHA and auth['exporter_sha256'] == actual['validate-addon.py'] and
            auth['source_validation_sha256'] == actual['source-validation.json'], 'Archived approval binding')
    require(validation['exporter_sha256'] == actual['validate-addon.py'] and validation['plan_sha256'] == PLAN_SHA and
            validation['protected'] == before, 'Archived source validation binding')
    require(validation['status'] == 'ADDITIVE196_SOURCE_VALIDATION_PASS_READONLY_NOT_EXPORTED' and
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
    return {'status': 'ADDITIVE196_ARCHIVE_EXACT_PASS_NOT_GIT_PUBLICATION', 'destination': PREFIX,
            'actual_files': len(actual), 'archive_manifest_sha256': actual['archive-manifest.json'],
            'actual_archive_bytes': sum(under(dest, n).stat().st_size for n in actual),
            'raw_original_files': len(raw_data), 'accepted_reference_counts': [196, 4459, 144],
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
    require(auth['status'] == 'ROOT_AUTHORIZED_EU_MULTIPLICITY_RATIONAL_SINGULAR196_ADDITIVE_EXPORT' and auth['destination'] == PREFIX and
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
    manifest = {'schema': 'eu-multiplicity-rational-singular196-additive-archive-v1-compact-paths', 'scope': 'ADDITIVE_ORIGINAL_EVIDENCE_ONLY',
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
