"""UNEXECUTED SOURCEONLY finite after260 next6 archive/standalone byte verifier.

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
BASE = 'docs/evidence/owned-frontiers/20261024-after254-exact6-v1'
BASE_COMMIT = '60e31c25ea408304d3309fa0131c803ee1c082f4'
BASE_ARCHIVE_COMMIT = '11b06e58ae853b69ec2f1415839c64e26758fda8'
BASE_MANIFEST_SHA = 'bb4630932c671a8070559902d16e59f0ee3f10062cfee35b1b4ce9554752f070'
BASE_PLAN_SHA = 'a9420500f3bf47f5337e53d3f248b1a998959b4e6a5bc5428a5cb52d00ac2537'
BASE_ACCEPTANCE_SHA = 'b80e1311ec7e574b40b10dc32df49e4d241f99352e90279dcb854f114f52af86'
BASE_PUBLICATION = {'path': '.lake/proof-continuation/publication-integrity/20261024s-root260-GITHUB-PUBLICATION.json',
                    'sha256': '3808773a966c24928ae8a0ee3d18d05ef0eb4251e7d3de92996147fe2b73ef96'}
TARGET_MODULES = ('ImbalancedChen.Part3ActualKPacketAdapter', 'ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01Data', 'ImbalancedChen.Certificates.OriginalNodeArraysV1.PageTransfer', 'ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01FullCheck', 'ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer', 'ImbalancedChen.Certificates.OriginalNodeArraysV1.InitialPrefix')
ROOT_STATUS = 'ROOT_AFTER260_NEXT6_TERMINAL_ACCEPTED'
FUTURE_PUBLICATION_STATUS = 'ROOT_AFTER260_NEXT6_GITHUB_PUBLISHED_AND_REMOTE_BRANCH_VERIFIED'
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
    'reviewer_invocation': 'terminal_reviewer_runner_invocation',
    'reviewer_stderr': 'terminal_reviewer_runner_stderr',
}
SOURCE_MAP = {'path': '.lake/proof-continuation/source-reviews/20261024v-after260-next6-final-strict-source-map-v2.json', 'sha256': 'f88335470ce6de8166029b0f4a7564b7c8f3b24ba5848e3fa43a301e17bc8462'}
ADOPTER_PEER = {'path': '.lake/proof-continuation/source-reviews/20261024u-after260-next6-capture-adoption-V1-independent-peer-SOURCEONLY.json', 'sha256': '7ac7318933ac3ef8d84e4863831d93ce5a6b6b572518759955a270a02a3ade85'}
COLLECTOR_PEER = {'path': '.lake/proof-continuation/source-reviews/20261024u-after260-next6-finite-record-append-V1-independent-peer-CP-SOURCEONLY.json', 'sha256': '8d4777897cd72413533479d56bf2b9841b17f8f46c1dcf45f16daec5b47a2794'}
REVIEWER_PEER = {'path': '.lake/proof-continuation/source-reviews/20261024u-after260-next6-independent-terminal-review-V1-peer-CP-SOURCEONLY.json', 'sha256': '0a769317a00ec7cbcedcae959cb81b8497d1596d1fc5e433282af9c566434bac'}
BOUND_ROOT_SHA = '0c5870cd426f1505e176baa5ce332169e4d896133ca34404d3d43f244e732730'
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


def validate_adopter_peer(load, reference, adoption_source):
    need(pair(reference) == ADOPTER_PEER, 'Exact actual V6 adoption source peer path/SHA required')
    peer = json.loads(load(reference))
    need(peer['status'] == 'STATIC_SOURCE_REVIEW_PASS_BOUNDED_NOT_EXECUTED_NOT_ROOT_ACCEPTANCE'
         and peer['exact_sources']['capture_sha256'] == '21268aafaa81c60d7b3d44065e7b986c8e6fb3b31c9b5b8d2f67c8515671cd46'
         and peer['exact_sources']['capture_path'] == '.lake/proof-continuation/source-reviews/drafts/20261024u-root-after260-next6-finite-capture-V5-SOURCEONLY.py.txt'
         and peer['exact_sources']['adopter_sha256'] == pair(adoption_source)['sha256']
         and relative(peer['exact_sources']['adopter_path']) == pair(adoption_source)['path'],
         'Actual V6 independent peer must bind the exact accepted adoption source path/SHA')


def load_additional_originals(inputs, load):
    """Only ROOT's explicit finite original-data/prefix receipts; never discover files."""
    rows = inputs['additional_original_receipts']
    need(isinstance(rows, list) and len(rows) <= 64, 'Finite additional original receipt list required')
    names = set()
    for row in rows:
        need(isinstance(row, dict) and set(row) == {'purpose', 'ref'}
             and row['purpose'] in {'original-data-emitter', 'prefix-byte-receipt'}, 'Exact additional original receipt purpose/ref')
        ref = pair(row['ref'])
        need(ref['path'] not in names, 'Duplicate additional original receipt')
        names.add(ref['path'])
        load(ref)


def validate_source_peers(load, helpers, roles):
    need(pair(helpers['collector_peer']) == COLLECTOR_PEER and pair(helpers['reviewer_peer']) == REVIEWER_PEER,
         'Exact actual successor collector/reviewer peers required')
    collector = json.loads(load(COLLECTOR_PEER))
    reviewer = json.loads(load(REVIEWER_PEER))
    need(collector['status'] == 'STATIC_REVIEW_NO_DEFINITE_GATE_REGRESSION_FOUND'
         and same({k: collector['reviewed']['collector'][k] for k in ('path', 'sha256')}, roles['collector_source']), 'Collector actual peer source binding')
    need(reviewer['status'] == 'STATIC_SOURCE_REVIEW_PASS_BOUNDED_NOT_EXECUTED_NOT_ROOT_ACCEPTANCE'
         and reviewer['exact_sources']['reviewer_sha256'] == pair(helpers['reviewer'])['sha256']
         and reviewer['exact_sources']['runner_sha256'] == pair(roles['terminal_runner_source'])['sha256'], 'Reviewer/runner actual peer source bindings')


def accepted_targets(acceptance):
    """Final hashes come only from the supplied exact ROOT acceptance bytes."""
    targets = acceptance['targets']
    need(isinstance(targets, dict) and set(targets) == set(TARGET_MODULES), 'Exact six named exact6 targets required')
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
    need(manifest['schema'] == 'after254-exact6-finite-original-evidence-archive-v1'
         and manifest['baseline_commit'] == BASE_ARCHIVE_COMMIT, 'Published ROOT260 baseline archive schema/parent commit')
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
    need(accepted['status'] == 'ROOT_AFTER254_EXACT6_TERMINAL_ACCEPTED'
         and [accepted[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')] == [260, 8296, 8277, 166], 'Published ROOT260 accepted baseline counts/status')
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
        need(isinstance(row['name'], str) and row['name'] and isinstance(row['type'], str) and row['type'] and '\u22ef' not in row['type'] and not row['type'].endswith('...')
             and all(row[k] is False for k in ('unsafe', 'partial', 'axiom'))
             and isinstance(row['axioms'], list) and set(row['axioms']) <= STD3, 'Unsafe/truncated/non-std3 complete record')


def validate(load, roles, baseline, source_bytes, audit_reference):
    """Finite archive consistency check; does not execute producers or evidence."""
    need(ROOT_STATUS is not None and isinstance(ROLE_FIELDS, dict), 'ROOT exact acceptance contract not installed')
    need(set(roles) == {'root_acceptance', *ROLE_FIELDS}, 'Exact finite current role set required')
    root = json.loads(load(roles['root_acceptance']))
    root_acceptance_path = pair(roles['root_acceptance'])['path']
    need(root['status'] == ROOT_STATUS
         and root_acceptance_path == '.lake/proof-continuation/source-reviews/20261024u-root-after260-next6-terminal-acceptance.json',
         'Actual after260 next6 terminal acceptance required at its exact supplied path/hash')
    for role, field in ROLE_FIELDS.items():
        need(same(root[field], roles[role]), 'ROOT current reference binding: ' + role)
    helpers = json.loads(load(roles['finite_capture']))
    need(helpers['schema'] == 'ROOT_AFTER260_NEXT6_FINITE_NORMAL_IMPORT_CAPTURE_V2'
         and helpers['status'] == 'ROOT_AFTER260_NEXT6_CURRENT_NORMAL_IMPORT_BINDINGS_CAPTURED'
         and same(helpers['terminal_review_cp'], roles['terminal_execution_cp']), 'Exact V5 capture schema/CP binding')
    need(pair(roles['finite_capture_source'])['sha256'] == '21268aafaa81c60d7b3d44065e7b986c8e6fb3b31c9b5b8d2f67c8515671cd46'
         and pair(roles['root_adoption_source'])['sha256'] == '16be8be36cdd90be5f8c278679f491079597c366fd718cfd158125b41fc27e78'
         and pair(roles['terminal_runner_source'])['sha256'] == 'ebdac0a4fd9797da3b0f3bffd50c302d5f4e11cdd661779e216d5819e43e9beb'
         and same(helpers['capture_builder'], roles['finite_capture_source']), 'Reviewed capture V5/adopter V6/runner V2 source SHA binding')
    invocation = json.loads(load(roles['reviewer_invocation']))
    need(set(invocation) == {'schema', 'status', 'reviewer_source', 'argv', 'cwd', 'started_at_utc', 'ended_at_utc', 'returncode', 'stdout', 'stderr', 'returncode_source'}
         and invocation['schema'] == 'AFTER260_NEXT6_FINITE_REVIEWER_INVOCATION_V2'
         and invocation['status'] == 'CHILD_PROCESS_COMPLETED_REVIEW_RESULT_MUST_BE_READ_SEPARATELY'
         and type(invocation['returncode']) is int and invocation['returncode'] == 0
         and invocation['returncode_source'] == 'subprocess.run returncode; not inferred from output streams'
         and same(invocation['reviewer_source'], helpers['terminal_reviewer_source'])
         and pair(invocation['reviewer_source'])['sha256'] == '5f8d0fab9da0dd8b7ed57752b4ec5f7766597f8ca994b58add1db6bcffef9f58'
         and isinstance(invocation['argv'], list) and len(invocation['argv']) >= 2
         and relative(invocation['argv'][1]) == pair(invocation['reviewer_source'])['path']
         and invocation['cwd'] == WSL_ROOT
         and pair(roles['reviewer_invocation'])['path'] == '.lake/proof-continuation/source-reviews/20261024u-after260-next6-independent-terminal-review-V2-invocation.json'
         and pair(roles['reviewer_stderr'])['path'] == '.lake/proof-continuation/source-reviews/20261024u-after260-next6-independent-terminal-review-V2-actual.stderr.log'
         and pair(roles['terminal_review'])['path'] == '.lake/proof-continuation/source-reviews/20261024u-after260-next6-independent-terminal-review-V2-actual.stdout.json'
         and same_stream(invocation['stdout'], roles['terminal_review'], load)
         and same_stream(invocation['stderr'], roles['reviewer_stderr'], load, require_empty=True)
         and same(helpers['terminal_reviewer_runner_invocation'], roles['reviewer_invocation'])
         and same(helpers['terminal_reviewer_runner_stderr'], roles['reviewer_stderr']), 'Exact V2 actual reviewer invocation/stdout/stderr binding')
    targets = accepted_targets(root)
    source_map = json.loads(load(SOURCE_MAP))
    need({module: entry['source']['sha256'] for module, entry in source_map['modules'].items()} == targets, 'Pinned exact6 source-map binding')
    for key in ('trust_mode', 'main_1_plus_1_75', 'weighted_estimate', 'external_closure_replayed', 'project_import_closure_replayed', 'unconditional_main_proved'):
        need(root[key] == SCOPE[key], 'ROOT normal import claim scope')
    need(type(root['weighted_estimate']) is int
         and all(root[key] is False for key in ('external_closure_replayed', 'project_import_closure_replayed', 'unconditional_main_proved')), 'ROOT exact scope field types')
    census = json.loads(load(roles['current_census']))
    rows = json.loads(load(roles['complete_declarations']))
    intake = json.loads(load(roles['intake']))
    proposal = json.loads(load(roles['proposal']))
    need(intake['schema'] == 'after260-next6-finite-record-append-draft-input-v1'
         and intake['targets'] == targets and set(intake['strict_producers']) == set(targets), 'Exact accepted exact6 schema/source hashes')
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
         and set(census['modules']) == set(old_census['modules']) | set(targets), 'Old260 entries deep equality/exact six-module append')
    need([r for r in rows if r['module'] not in targets] == old_rows, 'Old8296 records deep equality')
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
    need(len(intake['audit_receipts']) == 1, 'Exactly one original exact6 audit required')
    spec = intake['audit_receipts'][0]
    need(spec['targets'] == targets and same(spec['ref'], audit_reference), 'exact6 actual audit path/SHA/target binding')
    need(set(root['actual_audits']) == {'exact6'} and same(root['actual_audits']['exact6'], spec['ref']), 'ROOT exact exact6 original audit binding')
    audit = json.loads(load(spec['ref']))
    directory = PurePosixPath(relative(spec['ref']['path'])).parent
    need(PurePosixPath(relative(spec['ref']['path'])).name == 'receipt.json'
         and str(directory.parent) == '.lake/proof-continuation/audits', 'Original exact6 audit location')
    side_names = {'OwnedAudit.lean', 'declarations.json', 'declarations.log', 'audit-process.json'}
    side_names.update('replay-' + m + '.' + ext for m in targets for ext in ('json', 'log'))
    need(set(spec['sidecars']) == side_names, 'All original exact6 audit sidecars required')
    side = {name: load({'path': str(directory / name), 'sha256': sha}) for name, sha in spec['sidecars'].items()}
    need(audit['status'] == 'PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and audit['targets'] == targets
         and audit['inputs_before'] == audit['inputs_after'] and audit['external_closure_replay_claimed'] is False
         and audit['unconditional_main_claimed'] is False, 'Actual original exact6 audit status/scope')
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
    need(len(stocks) == len(targets) and {s['module'] for s in stocks} == set(targets), 'Original exact6 stock coverage')
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
         and set(inventory) == set(targets), 'Original emitted/JSON/census exact6 complete records')
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
    need(relative(spec['ref']['path']) not in {relative(e['owned_receipt']) for e in old_census['modules'].values()}, 'New exact6 audit cannot reuse an old primary receipt locator')
    need(census['owned_modules'] == measured['owned_modules'] and census['complete_serialized_declarations'] == measured['declarations']
         and census['distinct_constant_fullnames'] == measured['distinct_constant_fullnames']
         and census['original_owned_receipts_rehashed'] == measured['original_receipts'], 'Census summaries from original complete records')
    need([root[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')]
         == [measured[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')], 'ROOT counts from actual records plus the original exact6 audit receipt delta')
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
         and review['original_audit_group_key'] == 'exact6'
         and same(review['original_audit_refs']['exact6'], spec['ref'])
         and set(review['original_audit_refs']) == {'exact6'}, 'Actual terminal review of exact collector/exact6 audit')
    derived = review['artifact_derived_counts']
    need([derived[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'unique_owned_receipt_paths')]
         == [measured[k] for k in ('owned_modules', 'declarations', 'distinct_constant_fullnames', 'original_receipts')]
         and derived['new_records_by_module'] == counts and derived['old_entries_deep_equal'] is True
         and derived['old_records_deep_equal'] is True, 'Terminal review actual derived counts/deep equality')
    return measured


def verify_archive(repo, package, expected_root_sha):
    manifest = json.loads(member(package, 'archive-manifest.json').read_bytes())
    need(manifest['schema'] == 'after260-next6-finite-original-evidence-archive-v1'
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
    need(set(inputs) == {'roles', 'reviewed_helpers', 'baseline_publication', 'terminal_execution_cp', 'audit_receipt', 'additional_original_receipts'}, 'Archived exact parameter fields')
    need(inputs['roles'] == manifest['roles'] and inputs['reviewed_helpers'] == manifest['reviewed_helpers']
         and same(inputs['terminal_execution_cp'], manifest['terminal_execution_cp'])
         and same(inputs['baseline_publication'], manifest['baseline_publication'])
         and same(manifest['baseline_publication'], BASE_PUBLICATION), 'Archived parameter/manifest exact binding')
    expect(inputs['audit_receipt'])
    load_additional_originals(inputs, expect)
    expect(SOURCE_MAP)
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
                          'reviewer_invocation', 'reviewer_stdout', 'reviewer_stderr', 'capture_adopter_peer', 'adopter_peer'}, 'Archived helper role set')
    for reference in helpers.values():
        load(reference)
    need(pair(helpers['capture_adopter_peer']) == ADOPTER_PEER, 'Actual successor capture/adoption peer binding')
    need(same(helpers['collector'], manifest['roles']['collector_source'])
         and same(helpers['collector_peer'], manifest['roles']['collector_source_peer']), 'Archived ROOT collector/helper binding')
    validate_adopter_peer(load, helpers['adopter_peer'], manifest['roles']['root_adoption_source'])
    validate_source_peers(load, helpers, manifest['roles'])
    capture = json.loads(load(manifest['roles']['finite_capture']))
    need(same(helpers['reviewer'], capture['terminal_reviewer_source'])
         and same(helpers['reviewer_peer'], capture['terminal_reviewer_source_peer'])
         and same(capture['terminal_reviewer_runner_source'], manifest['roles']['terminal_runner_source'])
         and same(capture['terminal_review'], manifest['roles']['terminal_review'])
         and same(capture['terminal_reviewer_runner_invocation'], helpers['reviewer_invocation'])
         and same(capture['terminal_reviewer_runner_stderr'], helpers['reviewer_stderr'])
         and same(capture['terminal_review_cp'], manifest['roles']['terminal_execution_cp']),
         'Archived exact6 reviewer source/peer/runner/raw invocation binding')
    invocation = json.loads(load(helpers['reviewer_invocation']))
    need(invocation['status'] == 'CHILD_PROCESS_COMPLETED_REVIEW_RESULT_MUST_BE_READ_SEPARATELY'
         and invocation['returncode'] == 0 and same(invocation['reviewer_source'], helpers['reviewer'])
         and same_stream(invocation['stdout'], helpers['reviewer_stdout'], load)
         and same_stream(invocation['stderr'], helpers['reviewer_stderr'], load, require_empty=True)
         and same(helpers['reviewer_stdout'], manifest['roles']['terminal_review']),
         'Archived exact6 reviewer stdout/stderr/invocation bytes')
    sources = {m: member(repo, m.replace('.', '/') + '.lean').read_bytes() for m in targets}
    baseline = load_baseline(repo)
    counts = validate(load, manifest['roles'], baseline, sources, inputs['audit_receipt'])
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
    need(plan['stage_paths'] == stage, 'Only six sources, exact archive files and .gitattributes may be staged')
    need(member(package, 'stage-paths.nul').read_bytes() == b'\x00'.join(path.encode() for path in stage) + b'\x00', 'Exact NUL pathspec')
    need(member(package, 'root-gitattributes-required.raw').read_bytes() ==
         (''.join(m.replace('.', '/') + '.lean -text\n' for m in targets) + plan['package_path'] + '/** -text\n').encode(), 'Exactly seven new -text rules')
    before = member(package, 'root-gitattributes-before.raw').read_bytes()
    rules = member(package, 'root-gitattributes-required.raw').read_bytes()
    proposed = member(package, 'root-gitattributes-proposed.raw').read_bytes()
    need(proposed == before + (b'\n' if before and not before.endswith(b'\n') else b'') + rules
         and digest(before) == plan['gitattributes_before_sha256']
         and digest(proposed) == plan['gitattributes_proposed_sha256'], 'Attributes exact preimage/seven-rule append and plan hashes')
    need(member(repo, '.gitattributes').read_bytes() == proposed, 'Actual committed .gitattributes differs from exact seven-rule proposal')
    return {'status': 'FINITE_ARCHIVE_BYTES_TYPES_STD3_SOURCE_HASHES_VERIFIED_NO_LEAN_REPLAY',
            'counts': counts, 'scope': SCOPE, 'full_historical_closure_replayed': False,
            'current_object_or_provider_replay_claimed': False}



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    args = parser.parse_args()
    print(json.dumps(verify_archive(Path(args.root).resolve(strict=True), Path(__file__).resolve().parent, BOUND_ROOT_SHA), sort_keys=True))
