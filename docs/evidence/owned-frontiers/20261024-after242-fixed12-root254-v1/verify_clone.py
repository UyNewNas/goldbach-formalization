"""UNEXECUTED SOURCEONLY finite ROOT254 fixed12 archive/standalone byte verifier.

Future prepare reads explicit ROOT evidence and Git blobs, then writes one fresh
archive directory. It never stages/commits/pushes, edits sources or .gitattributes,
imports evidence/helpers, runs Lean/checkers, or walks historical JSON ancestry.
Clone verification checks archived bytes/records under normal import trust only.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath

WSL_ROOT = '/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'
WINDOWS_ROOT = 'E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'
BASE = 'docs/evidence/owned-frontiers/20261024-after239-three-P3-root242-v1'
BASE_COMMIT = 'a81c99fc2a94a13fd3eb3cef134ce35d95a8a594'
BASE_ARCHIVE_COMMIT = 'bfb69e2f2dc40e562c05952eeb2ed23895fe9099'
BASE_MANIFEST_SHA = 'e2f2d00db4d750bfe88697ff592ffb7f0b64e239f9514a78b7ca5f509f97b62f'
BASE_PLAN_SHA = 'dba4fb4ee773f43c86159132c54f251eec3e4d0f0a958afbc1421a010f0f1642'
BASE_ACCEPTANCE_SHA = '3b04ce1c33f75301fe626cf2e27893a8027fa4ef9219245f2729df321a75cd0a'
BASE_PUBLICATION = {'path': '.lake/proof-continuation/publication-integrity/20261024n-root242-GITHUB-PUBLICATION.json',
                    'sha256': 'd518f6a7eba28c9fe72357faf7accbf0694a0121138e81c78f47d7afb1b85e76'}
TARGET_MODULES = (
    'ImbalancedChen.ActualThirdOriginalFixedpointClippedChord',
    'ImbalancedChen.ActualThirdOriginalRoundedNewOperations',
    'ImbalancedChen.ActualThirdOriginalPositive256Log',
    'ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore',
    'ImbalancedChen.Part4ActualThirdOriginalStoredNodeLocalChecker',
    'ImbalancedChen.ActualThirdOriginalBoxMoments',
    'ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore',
    'ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Data',
    'ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Window',
    'ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check',
    'ImbalancedChen.ActualThirdOriginalSymmetricJensenLeaf',
    'ImbalancedChen.ActualThirdOriginalOrdinaryOldChord',
)
ROOT_STATUS = 'ROOT_AFTER242_FIXED12_TERMINAL_ACCEPTED'
FUTURE_PUBLICATION_STATUS = 'ROOT_AFTER242_FIXED12_GITHUB_PUBLISHED_AND_REMOTE_BRANCH_VERIFIED'
ROLE_FIELDS = {
    'previous_root_acceptance': 'previous_root_acceptance',
    'proposal': 'collector_acceptance_proposal',
    'current_census': 'current_census',
    'complete_declarations': 'complete_declarations',
    'intake': 'complete_original_evidence_intake',
    'collector_source': 'collector_source',
    'collector_source_peer': 'collector_source_peer',
    'terminal_review': 'terminal_independent_review',
    'terminal_execution_cp': 'terminal_independent_execution_cp',
    'terminal_source_peer': 'terminal_independent_source_peer',
    'terminal_runner_source': 'terminal_independent_runner_source',
    'finite_capture': 'normal_import_trust_capture',
    'finite_capture_source': 'finite_capture_source',
    'execution_witness': 'execution_witness',
    'root_observations': 'actual_root_observations',
    'root_adoption_source': 'root_adoption_source',
}
BOUND_ROOT_SHA = '25497a5857a5bf0a531d5d2b9beaeb1766e2f8260e82fe4540f693978d414099'
MAX_RAW = 96 * 1024 * 1024
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
CONTROL_FILES = {'verify_clone.py', 'root-gitattributes-before.raw', 'root-gitattributes-required.raw',
                 'root-gitattributes-proposed.raw', 'README.txt', 'stage-paths.nul'}
SCOPE = {'trust_mode': 'NORMAL_IMPORTED_ENVIRONMENT_TRUST', 'main_1_plus_1_75': 'OPEN',
         'weighted_estimate': 30, 'external_closure_replayed': False,
         'project_import_closure_replayed': False, 'unconditional_main_proved': False,
         'ci_pass_claimed': False}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + '\n').encode('utf-8')


def relative(name):
    need(isinstance(name, str) and name and '\x00' not in name, 'Path string required')
    name = name.replace(chr(92), '/')
    for prefix in (WSL_ROOT, WINDOWS_ROOT):
        if name.startswith(prefix + '/'):
            name = name[len(prefix) + 1:]
            break
    p = PurePosixPath(name)
    need(not p.is_absolute() and ':' not in name and all(x not in ('', '.', '..') for x in name.split('/')), 'Outside fixed repository: ' + name)
    return p.as_posix()


def pair(reference):
    need(isinstance(reference, dict) and set(reference) == {'path', 'sha256'}, 'Exact path/SHA pair required')
    sha = reference['sha256']
    need(isinstance(sha, str) and len(sha) == 64 and set(sha) <= set('0123456789abcdef'), 'Malformed SHA')
    return {'path': relative(reference['path']), 'sha256': sha}


def same(left, right):
    return pair(left) == pair(right)


def same_stream(record, expected, load, require_empty=False):
    """Bind an invocation stream's path/SHA and explicit byte count."""
    need(isinstance(record, dict) and set(record) == {'path', 'sha256', 'bytes'}, 'Exact invocation stream reference required')
    need(type(record['bytes']) is int and record['bytes'] >= 0, 'Invocation stream byte count required')
    need(same({'path': record['path'], 'sha256': record['sha256']}, expected), 'Invocation stream path/SHA binding')
    raw = load(expected)
    need(len(raw) == record['bytes'], 'Invocation stream byte count binding')
    if require_empty:
        need(record['bytes'] == 0, 'Expected empty invocation stderr')
    return True


def accepted_targets(acceptance):
    """Final hashes come only from the supplied exact ROOT acceptance bytes."""
    targets = acceptance['targets']
    need(isinstance(targets, dict) and set(targets) == set(TARGET_MODULES), 'Exact twelve named fixed12 targets required')
    need(all(isinstance(value, str) and len(value) == 64 and set(value) <= set('0123456789abcdef')
             for value in targets.values()), 'ROOT must supply final lowercase source SHA256 values')

    # Stable rule/source ordering independent of the original JSON key order.
    return {module: targets[module] for module in TARGET_MODULES}


def member(root, name):
    path = root / relative(name)
    resolved = path.resolve(strict=True)
    need(resolved.is_relative_to(root.resolve()) and resolved.is_file(), 'Missing/escaping archive member')
    return resolved


def restore(package, row):
    need(set(row) == {'original_path', 'source_sha256', 'source_bytes', 'stored_path', 'stored_sha256', 'encoding'}, 'Inherited payload row schema')
    need(type(row['source_bytes']) is int and 0 <= row['source_bytes'] <= MAX_RAW, 'Inherited payload size')
    raw = member(package, row['stored_path']).read_bytes()
    need(digest(raw) == row['stored_sha256'], 'Inherited stored payload SHA')
    if row['encoding'] == 'gzip-mtime0-empty-filename':
        import io
        with gzip.GzipFile(fileobj=io.BytesIO(raw)) as stream:
            raw = stream.read(row['source_bytes'] + 1)
    else:
        need(row['encoding'] == 'raw', 'Inherited payload encoding')
    need(len(raw) == row['source_bytes'] and digest(raw) == row['source_sha256'], 'Inherited original bytes/SHA')
    return raw


def load_baseline(repo):
    package = repo / BASE
    raw = member(package, 'archive-manifest.json').read_bytes()
    need(digest(raw) == BASE_MANIFEST_SHA and digest(member(package, 'source-plan.json').read_bytes()) == BASE_PLAN_SHA, 'Published baseline archive bytes changed')
    manifest = json.loads(raw)
    need(manifest['schema'] == 'after239-three-P3-arithmetic-finite-original-evidence-archive-v1'
         and manifest['baseline_commit'] == BASE_ARCHIVE_COMMIT, 'Published ROOT239 baseline archive schema/parent commit')
    # The pinned prior archive stores exact raw payload rows, not the older
    # source_refs/gzip schema. Read only its three primary documents in place;
    # do not call its verifier or follow its inherited archive/JSON ancestry.
    primary_rows = {}
    for row in manifest['payloads']:
        name = relative(row['original_path'])
        need(name not in primary_rows, 'Duplicate inherited original locator')
        primary_rows[name] = row
    documents = {}
    for role in ('root_acceptance', 'current_census', 'complete_declarations'):
        reference = pair(manifest['roles'][role])
        row = primary_rows[reference['path']]
        need(set(row) == {'original_path', 'sha256', 'bytes', 'stored_path'}
             and row['sha256'] == reference['sha256'] and type(row['bytes']) is int
             and 0 <= row['bytes'] <= MAX_RAW, 'Inherited primary raw row binding')
        original = member(package, row['stored_path']).read_bytes()
        need(len(original) == row['bytes'] and digest(original) == row['sha256'], 'Inherited primary original raw bytes/SHA')
        documents[role] = json.loads(original)
    need(pair(manifest['roles']['root_acceptance'])['sha256'] == BASE_ACCEPTANCE_SHA, 'Published baseline acceptance SHA')
    accepted = documents['root_acceptance']
    need(accepted['status'] == 'ROOT_AFTER239_THREE_P3_ARITHMETIC_TERMINAL_ACCEPTED'
         and [accepted[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')] == [242, 6870, 6851, 164], 'Published ROOT242 accepted baseline counts/status')
    for role in ('current_census', 'complete_declarations'):
        need(same(accepted[role], manifest['roles'][role]), 'Baseline acceptance primary reference')
    return documents


def guarded(result, exit_key):
    need(result['status'] == 'PASS' and type(result[exit_key]) is int and result[exit_key] == 0
         and result['guard_error'] is None and result['rss_guard']['limit_mib'] == 6656
         and result['rss_guard']['signals'] == [] and type(result['max_rss_kib']) is int
         and 0 <= result['max_rss_kib'] <= 6656 * 1024
         and isinstance(result['resource_reason'], str) and result['resource_reason'].strip(), 'Original guarded process failed')


def record_identity(rows):
    need(isinstance(rows, list) and len({(r['module'], r['name']) for r in rows}) == len(rows), 'Complete record identity')
    for row in rows:
        need(isinstance(row['name'], str) and row['name'] and isinstance(row['type'], str) and row['type'] and '\u22ef' not in row['type']
             and all(row[k] is False for k in ('unsafe', 'partial', 'axiom'))
             and isinstance(row['axioms'], list) and set(row['axioms']) <= STD3, 'Unsafe/truncated/non-std3 complete record')


def validate(load, roles, baseline, source_bytes):
    """Finite archive consistency check; does not execute producers or evidence."""
    need(ROOT_STATUS is not None and isinstance(ROLE_FIELDS, dict), 'ROOT exact acceptance contract not installed')
    need(set(roles) == {'root_acceptance', *ROLE_FIELDS}, 'Exact finite current role set required')
    root = json.loads(load(roles['root_acceptance']))
    root_acceptance_path = pair(roles['root_acceptance'])['path']
    need(root['status'] == ROOT_STATUS
         and root_acceptance_path == '.lake/proof-continuation/source-reviews/20261024p-root-after242-fixed12-terminal-acceptance.json',
         'Actual ROOT254 fixed12 terminal acceptance required at its exact supplied path/hash')
    for role, field in ROLE_FIELDS.items():
        need(same(root[field], roles[role]), 'ROOT current reference binding: ' + role)
    targets = accepted_targets(root)
    for key in ('trust_mode', 'main_1_plus_1_75', 'weighted_estimate', 'external_closure_replayed', 'project_import_closure_replayed', 'unconditional_main_proved'):
        need(root[key] == SCOPE[key], 'ROOT normal import claim scope')
    need(type(root['weighted_estimate']) is int
         and all(root[key] is False for key in ('external_closure_replayed', 'project_import_closure_replayed', 'unconditional_main_proved')), 'ROOT exact scope field types')
    census = json.loads(load(roles['current_census']))
    rows = json.loads(load(roles['complete_declarations']))
    intake = json.loads(load(roles['intake']))
    proposal = json.loads(load(roles['proposal']))
    need(intake['schema'] == 'after242-fixed12-finite-record-append-draft-input-v2'
         and intake['targets'] == targets and set(intake['strict_producers']) == set(targets), 'Exact accepted fixed12 schema/source hashes')
    need(root['targets'] == targets and root['strict_producers'] == intake['strict_producers'], 'ROOT exact target/strict producer map binding')
    need(pair(roles['previous_root_acceptance'])['sha256'] == BASE_ACCEPTANCE_SHA
         and json.loads(load(roles['previous_root_acceptance'])) == baseline['root_acceptance'], 'Published previous ROOT acceptance binding')
    pin_hashes = {name: pair(ref)['sha256'] for name, ref in intake['pins'].items()}
    need(set(pin_hashes) == {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}, 'Project pins')
    tools, commands = intake['tools'], intake['producer_command_paths']
    need(same(proposal['candidate_census'], roles['current_census']) and same(proposal['complete_declarations'], roles['complete_declarations'])
         and same(proposal['complete_original_evidence_intake'], roles['intake']), 'Actual proposal primary bindings')
    record_identity(rows)
    old_census, old_rows = baseline['current_census'], baseline['complete_declarations']
    need({m: census['modules'][m] for m in old_census['modules']} == old_census['modules']
         and set(census['modules']) == set(old_census['modules']) | set(targets), 'Old242 entries deep equality/exact twelve-module append')
    need([r for r in rows if r['module'] not in targets] == old_rows, 'Old6827 records deep equality')
    new_rows = [r for r in rows if r['module'] in targets]
    need(len({r['name'] for r in new_rows}) == len(new_rows)
         and not {r['name'] for r in new_rows} & {r['name'] for r in old_rows}, 'New fullname collision')
    for module in targets:
        need(census['modules'][module]['module'] == module and census['modules'][module]['source_sha256'] == targets[module]
             and digest(source_bytes[module]) == targets[module], 'Actual ROOT source bytes mismatch')
        strict_spec = intake['strict_producers'][module]
        strict = json.loads(load(strict_spec['receipt']))
        guarded(strict, 'exit_code')
        need(strict['module'] == module and strict['warnings_as_errors'] is True and strict['lean_memory_mib'] == 6144
             and strict['binding'] == strict['binding_after'] and strict['binding']['source_sha256'] == targets[module]
             and strict['object_parts'] == census['modules'][module]['object_parts'], 'Original strict accepted source/object binding')
        strict_path = PurePosixPath(relative(strict_spec['receipt']['path']))
        need(strict_path.name == 'receipt.json' and str(strict_path.parent.parent) == '.lake/proof-continuation/runs', 'Original strict run location')
        need(strict['binding']['pins'] == pin_hashes and strict['binding']['lean_real_sha256'] == tools['lean_real']['sha256']
             and strict['binding']['lean_wrapper_sha256'] == tools['lean']['sha256']
             and strict['runtime_sha256'] == strict['runtime_sha256_after'] == tools['runtime']['sha256'], 'Strict pin/compiler/runtime binding')
        need(len(strict['command']) == 7 and strict['command'][:5] == [commands['lean'], '-j2', '-M6144', '-DwarningAsError=true', '-o']
             and strict['command'][-1] == module.replace('.', '/') + '.lean', 'Original strict exact compiler arguments')
        need(relative(strict_spec['stdout']['path']) == str(PurePosixPath(relative(strict_spec['receipt']['path'])).parent / 'stdout.log'), 'Exact original strict stdout')
        load(strict_spec['stdout'])
    need(len(intake['audit_receipts']) == 1, 'Exactly one original fixed12 audit required')
    spec = intake['audit_receipts'][0]
    need(spec['targets'] == targets, 'fixed12 audit final target binding')
    need(set(root['actual_audits']) == {'fixed12'} and same(root['actual_audits']['fixed12'], spec['ref']), 'ROOT exact fixed12 original audit binding')
    audit = json.loads(load(spec['ref']))
    directory = PurePosixPath(relative(spec['ref']['path'])).parent
    need(PurePosixPath(relative(spec['ref']['path'])).name == 'receipt.json'
         and str(directory.parent) == '.lake/proof-continuation/audits', 'Original fixed12 audit location')
    side_names = {'OwnedAudit.lean', 'declarations.json', 'declarations.log', 'audit-process.json'}
    side_names.update('replay-' + m + '.' + ext for m in targets for ext in ('json', 'log'))
    need(set(spec['sidecars']) == side_names, 'All original fixed12 audit sidecars required')
    side = {name: load({'path': str(directory / name), 'sha256': sha}) for name, sha in spec['sidecars'].items()}
    need(audit['status'] == 'PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and audit['targets'] == targets
         and audit['inputs_before'] == audit['inputs_after'] and audit['external_closure_replay_claimed'] is False
         and audit['unconditional_main_claimed'] is False, 'Actual original fixed12 audit status/scope')
    need(audit['inputs_before']['sources'] == targets
         and audit['inputs_before']['owned_object_parts'] == {m: census['modules'][m]['object_parts'] for m in targets}
         and audit['inputs_before']['pins'] == pin_hashes
         and audit['inputs_before']['lean_real_sha256'] == tools['lean_real']['sha256']
         and audit['inputs_before']['checker_sha256'] == tools['leanchecker']['sha256'], 'Audit accepted source/object/pin/compiler snapshots')
    need(audit['generated_audit_sha256'] == digest(side['OwnedAudit.lean'])
         and audit['audit_runner_sha256'] == tools['audit_runner']['sha256']
         and audit['source_template_sha256'] == tools['audit_template']['sha256'], 'Original audit generated source/runner/template')
    process = json.loads(side['audit-process.json'])
    guarded(process, 'returncode')
    need(len(process['command']) == 5 and process['command'][:4] == [commands['lean'], '-j2', '-M6144', '-DwarningAsError=true']
         and relative(process['command'][4]) == str(directory / 'OwnedAudit.lean'), 'Original ALL exact source/arguments')
    full = [s for s in audit['stages'] if s['kind'] == 'full_inventory_type_axioms']
    stocks = [s for s in audit['stages'] if s['kind'] == 'stock_replay']
    need(len(full) == 1 and full[0]['exit_code'] == 0 and full[0]['command'] == process['command']
         and full[0]['log_sha256'] == digest(side['declarations.log']), 'Original ALL stage/log')
    need(len(stocks) == len(targets) and {s['module'] for s in stocks} == set(targets), 'Original fixed12 stock coverage')
    for stage in stocks:
        module, result = stage['module'], stage['result']
        guarded(result, 'returncode')
        need(result['command'] == [commands['leanchecker'], '--verbose', module]
             and result == json.loads(side['replay-' + module + '.json'])
             and result['log_sha256'] == digest(side['replay-' + module + '.log']), 'Original stock command/sidecar')
    emitted, inventory = [], {}
    for line in side['declarations.log'].decode('utf-8').splitlines():
        if line.startswith('P0_QUEUE_DECL '):
            emitted.append(json.loads(line.split(' ', 1)[1]))
        elif line.startswith('P0_QUEUE_INVENTORY '):
            row = json.loads(line.split(' ', 1)[1])
            need(row['module'] not in inventory, 'Duplicate inventory')
            inventory[row['module']] = row
    audit_rows = json.loads(side['declarations.json'])
    key = lambda row: (row['module'], row['name'])
    need(sorted(audit_rows, key=key) == sorted(emitted, key=key) == sorted(new_rows, key=key)
         and set(inventory) == set(targets), 'Original emitted/JSON/census fixed12 complete records')
    counts = {m: sum(r['module'] == m for r in new_rows) for m in targets}
    need(audit['declaration_counts'] == counts, 'Actual audit derived counts')
    for module, count in counts.items():
        names = {r['name'] for r in new_rows if r['module'] == module}
        inv = inventory[module]
        need(count > 0 and len(inv['environment']) == len(set(inv['environment'])) == count
             and len(inv['serialized']) == len(set(inv['serialized'])) == count
             and names == set(inv['serialized']) == set(inv['environment']), 'Complete ALL inventory')
        entry = census['modules'][module]
        need(same({'path': entry['owned_receipt'], 'sha256': entry['owned_receipt_sha256']}, spec['ref'])
             and entry['declarations_json_sha256'] == digest(side['declarations.json'])
             and entry['complete_serialized_declarations'] == count, 'Accepted census original audit binding')
    measured = {'owned_modules': len(census['modules']), 'declarations': len(rows),
                'distinct_constant_fullnames': len({r['name'] for r in rows}),
                'original_receipts': len({relative(e['owned_receipt']) for e in census['modules'].values()}),
                'new_record_counts': counts}
    need(relative(spec['ref']['path']) not in {relative(e['owned_receipt']) for e in old_census['modules'].values()}, 'New fixed12 audit cannot reuse an old primary receipt locator')
    need(census['owned_modules'] == measured['owned_modules'] and census['complete_serialized_declarations'] == measured['declarations']
         and census['distinct_constant_fullnames'] == measured['distinct_constant_fullnames']
         and census['original_owned_receipts_rehashed'] == measured['original_receipts'], 'Census summaries from original complete records')
    need([root[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')]
         == [measured[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')], 'ROOT counts from actual records plus the original fixed12 audit receipt delta')
    expected_added = [len(targets), len(new_rows), len({r['name'] for r in new_rows}), measured['original_receipts'] - len({relative(e['owned_receipt']) for e in old_census['modules'].values()})]
    integer_fields = ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts',
                      'added_modules', 'added_complete_serialized_declarations', 'added_distinct_constant_fullnames', 'added_original_receipts')
    need(all(type(root[key]) is int for key in integer_fields)
         and [root[k] for k in integer_fields[4:]] == expected_added
         and root['actual_new_module_record_counts'] == counts
         and all(type(value) is int for value in root['actual_new_module_record_counts'].values()), 'ROOT exact added counts from actual complete records')
    review = json.loads(load(roles['terminal_review']))
    need(review['status'] == 'FINITE_RECORD_STAGE_TERMINAL_REVIEW_PASS_NOT_ROOT_ACCEPTANCE'
         and review['reviewed_collector_sha256'] == roles['collector_source']['sha256']
         and review['original_audit_group_key'] == 'fixed12'
         and same(review['original_audit_refs']['fixed12'], spec['ref'])
         and set(review['original_audit_refs']) == {'fixed12'}, 'Actual terminal review of exact collector/fixed12 audit')
    derived = review['artifact_derived_counts']
    need([derived[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'unique_owned_receipt_paths')]
         == [measured[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')]
         and derived['new_records_by_module'] == counts and derived['old_entries_deep_equal'] is True
         and derived['old_records_deep_equal'] is True, 'Terminal review actual derived counts/deep equality')
    return measured


def verify_archive(repo, package, expected_root_sha):
    manifest = json.loads(member(package, 'archive-manifest.json').read_bytes())
    need(manifest['schema'] == 'after242-fixed12-finite-original-evidence-archive-v1'
         and manifest['scope'] == SCOPE and manifest['baseline_commit'] == BASE_COMMIT, 'Archive schema/scope/baseline commit')
    need(pair(manifest['roles']['root_acceptance'])['sha256'] == expected_root_sha, 'Pinned ROOT acceptance SHA')
    payloads = manifest['payloads']
    need(len({p['original_path'] for p in payloads}) == len(payloads), 'Duplicate archived original locator')
    need([row['original_path'] for row in payloads] == sorted(relative(row['original_path']) for row in payloads), 'Canonical exact original locator order')
    index = {}
    for ordinal, row in enumerate(payloads):
        need(set(row) == {'original_path', 'sha256', 'bytes', 'stored_path'}, 'Raw payload row schema')
        need(row['stored_path'] == 'p/' + str(ordinal).zfill(3) + '-' + row['sha256'] + '.raw', 'Exact finite raw payload member name')
        raw = member(package, row['stored_path']).read_bytes()
        need(type(row['bytes']) is int and len(raw) == row['bytes'] <= MAX_RAW and digest(raw) == row['sha256'], 'Exact raw archived bytes/SHA/size')
        index[relative(row['original_path'])] = (row['sha256'], raw)
    def load(reference):
        ref = pair(reference)
        need(ref['path'] in index and index[ref['path']][0] == ref['sha256'], 'Explicit original absent/wrong SHA')
        return index[ref['path']][1]
    expected_payloads = {}
    def expect(reference):
        ref = pair(reference)
        need(ref['path'] not in expected_payloads or expected_payloads[ref['path']] == ref['sha256'], 'Conflicting finite payload references')
        expected_payloads[ref['path']] = ref['sha256']
        return load(reference)
    inputs = json.loads(expect(manifest['archive_inputs']))
    need(set(inputs) == {'roles', 'reviewed_helpers', 'baseline_publication', 'terminal_execution_cp'}, 'Archived exact parameter fields')
    need(inputs['roles'] == manifest['roles'] and inputs['reviewed_helpers'] == manifest['reviewed_helpers']
         and same(inputs['terminal_execution_cp'], manifest['terminal_execution_cp'])
         and same(inputs['baseline_publication'], manifest['baseline_publication'])
         and same(manifest['baseline_publication'], BASE_PUBLICATION), 'Archived parameter/manifest exact binding')
    expect(manifest['baseline_publication'])
    for reference in manifest['roles'].values():
        expect(reference)
    for reference in manifest['reviewed_helpers'].values():
        expect(reference)
    expect(manifest['terminal_execution_cp'])
    targets = accepted_targets(json.loads(load(manifest['roles']['root_acceptance'])))
    intake = json.loads(load(manifest['roles']['intake']))
    need(set(intake['strict_producers']) == set(targets) and len(intake['audit_receipts']) == 1, 'Finite original producer scope')
    for spec in intake['strict_producers'].values():
        need(set(spec) == {'receipt', 'stdout'}, 'Finite original strict reference fields')
        expect(spec['receipt'])
        expect(spec['stdout'])
    spec = intake['audit_receipts'][0]
    need(set(spec) == {'ref', 'targets', 'sidecars'}, 'Finite original audit fields')
    expect(spec['ref'])
    directory = PurePosixPath(relative(spec['ref']['path'])).parent
    side_names = {'OwnedAudit.lean', 'declarations.json', 'declarations.log', 'audit-process.json'}
    side_names.update('replay-' + m + '.' + ext for m in targets for ext in ('json', 'log'))
    need(set(spec['sidecars']) == side_names, 'Finite original audit sidecar set')
    for name, sha in spec['sidecars'].items():
        expect({'path': str(directory / name), 'sha256': sha})
    need({name: value[0] for name, value in index.items()} == expected_payloads, 'Unexpected/missing original payload outside exact current scope')
    need(same(manifest['terminal_execution_cp'], manifest['roles']['terminal_execution_cp']), 'Archived ROOT terminal CP reference')
    load(manifest['terminal_execution_cp']).decode('utf-8')
    helpers = manifest['reviewed_helpers']
    need(set(helpers) == {'collector', 'collector_peer', 'reviewer', 'reviewer_peer', 'archiver', 'archiver_peer',
                          'reviewer_invocation', 'reviewer_stdout', 'reviewer_stderr'}, 'Archived helper role set')
    for reference in helpers.values():
        load(reference)
    need(same(helpers['collector'], manifest['roles']['collector_source'])
         and same(helpers['collector_peer'], manifest['roles']['collector_source_peer']), 'Archived ROOT collector/helper binding')
    capture = json.loads(load(manifest['roles']['finite_capture']))
    need(same(helpers['reviewer'], capture['terminal_reviewer_source'])
         and same(helpers['reviewer_peer'], capture['terminal_reviewer_source_peer'])
         and same(capture['terminal_reviewer_runner_source'], manifest['roles']['terminal_runner_source'])
         and same(capture['terminal_review'], manifest['roles']['terminal_review'])
         and same(capture['terminal_review_cp'], helpers['reviewer_invocation']),
         'Archived fixed12 reviewer source/peer/runner/raw invocation binding')
    invocation = json.loads(load(helpers['reviewer_invocation']))
    need(invocation['status'] == 'CHILD_PROCESS_COMPLETED_REVIEW_RESULT_MUST_BE_READ_SEPARATELY'
         and invocation['returncode'] == 0 and same(invocation['reviewer_source'], helpers['reviewer'])
         and same_stream(invocation['stdout'], helpers['reviewer_stdout'], load)
         and same_stream(invocation['stderr'], helpers['reviewer_stderr'], load, require_empty=True)
         and same(helpers['reviewer_stdout'], manifest['roles']['terminal_review']),
         'Archived fixed12 reviewer stdout/stderr/invocation bytes')
    sources = {m: member(repo, m.replace('.', '/') + '.lean').read_bytes() for m in targets}
    baseline = load_baseline(repo)
    counts = validate(load, manifest['roles'], baseline, sources)
    need(manifest['measured_counts'] == counts, 'Archived measured-count summary differs from validated records')
    for module, entry in baseline['current_census']['modules'].items():
        need(digest(member(repo, module.replace('.', '/') + '.lean').read_bytes()) == entry['source_sha256'], 'Inherited accepted source bytes differ in clone: ' + module)
    need(set(manifest['control_files']) == CONTROL_FILES, 'Exact fixed archive control file set')
    for name, row in manifest['control_files'].items():
        raw = member(package, name).read_bytes()
        need(set(row) == {'sha256', 'bytes'} and type(row['bytes']) is int
             and digest(raw) == row['sha256'] and len(raw) == row['bytes'], 'Archive control bytes/SHA')
    expected_files = {p['stored_path'] for p in payloads} | set(manifest['control_files']) | {'archive-manifest.json', 'source-plan.json'}
    need({p.relative_to(package).as_posix() for p in package.rglob('*') if p.is_file()} == expected_files, 'Unexpected/missing archive file')
    plan = json.loads(member(package, 'source-plan.json').read_bytes())
    need(plan['archive_manifest_sha256'] == digest(member(package, 'archive-manifest.json').read_bytes())
         and plan['target_sources'] == targets and plan['scope'] == SCOPE
         and plan['required_publication_status'] == FUTURE_PUBLICATION_STATUS
         and manifest['future_publication_status'] == FUTURE_PUBLICATION_STATUS, 'Source-plan manifest/source/scope binding')
    need(plan['package_path'] == package.relative_to(repo).as_posix()
         and same(plan['root_acceptance'], manifest['roles']['root_acceptance']), 'Plan actual package/ROOT reference')
    stage = sorted([m.replace('.', '/') + '.lean' for m in targets] + ['.gitattributes']
                   + [plan['package_path'] + '/' + p for p in expected_files])
    need(plan['stage_paths'] == stage, 'Only twelve sources, exact archive files and .gitattributes may be staged')
    need(member(package, 'stage-paths.nul').read_bytes() == b'\x00'.join(path.encode() for path in stage) + b'\x00', 'Exact NUL pathspec')
    need(member(package, 'root-gitattributes-required.raw').read_bytes() ==
         (''.join(m.replace('.', '/') + '.lean -text\n' for m in targets) + plan['package_path'] + '/** -text\n').encode(), 'Exactly thirteen new -text rules')
    before = member(package, 'root-gitattributes-before.raw').read_bytes()
    rules = member(package, 'root-gitattributes-required.raw').read_bytes()
    proposed = member(package, 'root-gitattributes-proposed.raw').read_bytes()
    need(proposed == before + (b'\n' if before and not before.endswith(b'\n') else b'') + rules
         and digest(before) == plan['gitattributes_before_sha256']
         and digest(proposed) == plan['gitattributes_proposed_sha256'], 'Attributes exact preimage/thirteen-rule append and plan hashes')
    need(member(repo, '.gitattributes').read_bytes() == proposed, 'Actual committed .gitattributes differs from exact thirteen-rule proposal')
    return {'status': 'FINITE_ARCHIVE_BYTES_TYPES_STD3_SOURCE_HASHES_VERIFIED_NO_LEAN_REPLAY',
            'counts': counts, 'scope': SCOPE, 'full_historical_closure_replayed': False,
            'current_object_or_provider_replay_claimed': False}



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    args = parser.parse_args()
    print(json.dumps(verify_archive(Path(args.root).resolve(strict=True), Path(__file__).resolve().parent, BOUND_ROOT_SHA), sort_keys=True))
