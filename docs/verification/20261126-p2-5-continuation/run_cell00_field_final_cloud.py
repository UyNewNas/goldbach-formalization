#!/usr/bin/env python3
"""Strict one-owner FieldDecode repair, adapted from the frozen 4f12d9bc driver.

Reuse eight accepted base objects, three original ecfc owners, and ten accepted
split owners. Their aggregate failed receipts remain failed and their original
owner dictionaries/publications remain unchanged. Only the repaired final owner
may execute normal Lean, independent leanchecker, and full-owned/axiom gates.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import traceback

ROOT = Path('/workspace/p25-q96-20261125')
OUT = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt004'
SPLIT = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt003'
PRIOR_FIELD = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt001'
REMAINING = ROOT / '.lake/diagnostic/p25-cell00-remaining-arithmetic-attempt001'
PAYLOAD_FLOORS = ROOT / '.lake/diagnostic/p25-payload-floors-attempt001'
BASE = ROOT / '.lake/diagnostic/p25-cell00-canonical-attempt001/charparse'
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
SPLIT_RESULT_SHA = '00ae4f5be311670b1538e934574a79b56ae0808253711ae1e0c606095d6dfdf0'
SPLIT_PUBLICATION = '2ce35f759db6fdc18373b2842f655d9569fd4f48'
SPLIT_RUNNER_SHA = '3b7740243e09c49d8ebfc0233a5f1a666a865132364d90a075b4980cc965176b'
SPLIT_FAILED_SOURCE_SHA = 'ce7e0131800eb84b3ab2c8dfd8830aaa0b353475594e91b70906b3d1052e77e2'
SPLIT_FAILED_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00FieldDecode.lean'
SPLIT_FAILED_NORMAL_SHA = '623cd44b8f00065842328db445925797cbe3e3ccf8946cc92e12ded6a6a18e0b'
PRIOR_FIELD_PUBLICATION = 'ecfc75049ab7380048fa0c9992e14b787bc908de'
ADAPTED_FROM_REL = 'docs/verification/20261126-p2-5-continuation/run_cell00_five_consumers_cloud.py'
ADAPTED_FROM_SHA = '4f12d9bcb43b2fd4a0b626d5803dfb27b7ec7f05784d005f7378879ccd0d620f'
PRIOR_FIELD_RESULT_SHA = '86afeed917a3361c5457db1b7b3f4546d2e513531288adfab3d3a196ad38eac1'
PRIOR_FIELD_SOURCE_SHA = 'c62cf0315fafe2733393627137963dcb507827c988a49115add3a11422a244ed'
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
BASE_RESULT_SHA = '4dca8c2c7b42feb027895420ddb62e0a314d5f6f440d8b772704eeb146ba37eb'
PAYLOAD_RESULT_SHA = '090463b93761d31023f39111c32522e1f2bb3cbcec46e606f7fc429d69d4a204'
PAYLOAD_FILES_SHA = '76aa078eef969fa6c8d8270529f3d68f50b4bb6762626ba14a484423bbdc4321'
PAYLOAD = 'ImbalancedChen.P2Saving16Cell00TypedPayload'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
ALLOWED_AXIOMS = {'Classical.choice', 'Quot.sound', 'propext'}
REUSED_FIELD_OBJECTS = {'ImbalancedChen.P2Saving16Cell00PayloadBinding': 'f1bff7f79f8e43f8a98e5eca39b520b928b46016a297af9272a6cb2b65f065c8', 'ImbalancedChen.P2OriginalSaving16DecoderCompose': 'df91e32fa010265bb3ad1dba9f317233ce9c1b48beb0c668e5bca70666c452ed', 'ImbalancedChen.P2Saving16Cell00ScalarDecode': '6a313fad2e0bb6a42a0a73e8f0c5c3360576b10e6de8f34511139711a6e64aeb'}
REMAINING_RESULT_SHA = '1e48fc2e2a45b2e4247ab08597586dae6c8cac3cd9a05788e465b5175d262f7c'
REMAINING_PUBLICATION = '5cc2b181f51be2f20ce316256fe2cdf3e691ca69'
REMAINING_RUNNER_SHA = '17b4b2193968c061a8bbb31ac0e3043c8cbf4eb2b22ee010a0359a57c8de4918'
EXTERNAL_SNAPSHOT_SHA = 'b94ab99b39a831a616d626c55c4b89c0a921d15c95319de19063d375bc982728'
EXPECTED_EXTERNAL_COUNT = 5312
EXPECTED_EXTERNAL_COMPANIONS = 10624
SUPPORT = 'ImbalancedChen.P2Saving16Cell00FieldSimp'
SCOPE = 'ImbalancedChen.P2Saving16Cell00FieldDecode'
SCOPED_APPENDIX_REL = 'docs/source-only/20261126-p2-5-cell00-field-split/PRIVATE_SCOPED_SIMP_AUDIT_APPENDIX.lean'
SCOPED_APPENDIX_SHA = 'ff82f03c8c798556f2ed6e18ce4ed5a035057fa616b55664a105a9b5886aa202'
KNOWN_OBJECTS = {'ImbalancedChen.P2OriginalSaving16Decoder': 'fd25815778e3bae5518d3fcc6a5461724b64251f91c4c08e61312fbae4987b39', 'ImbalancedChen.P2OriginalSaving16Q96FloorCore': '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9', 'ImbalancedChen.P2OriginalSaving19SourceJson': '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7', 'ImbalancedChen.P2Saving16StringCharBinding00': 'a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a', 'ImbalancedChen.P2OriginalSaving19SourceJsonFuel': '9928b1cd0dd91cc93ff2055f00d0d147d455dd8d27783cf110e58df3d61bd088', 'ImbalancedChen.P2Saving16Cell00DirectParse': '52cf731b62270e0fdfee8468d813aacfe373853e51035b88c669dd8713393f2a'}
RUNNER_REL = 'docs/verification/20261126-p2-5-continuation/run_cell00_field_final_cloud.py'
SELECTION_REL = 'docs/verification/20261126-p2-5-continuation/cell00-field-final/SOURCE_AND_RECEIPT_SELECTION.json'
SELECTION_SHA = '5a7195c165faa79dfa2e9e9277ef37a8d8ab9819cb6a057692c6e0ff8aba0201'
TARGET = 'ImbalancedChen.P2Saving16Cell00FieldDecode'
FINAL_SOURCE_REL = 'docs/source-only/20261126-p2-5-cell00-field-final/ImbalancedChen/P2Saving16Cell00FieldDecode.lean'
FINAL_SOURCE_SHA = '59cafdc924a5a50d01d25dfb03178208c4f1e13552fdb105d5a5cb43f1f59cc3'
FINAL_PACKAGE_SELECTION_REL = 'docs/source-only/20261126-p2-5-cell00-field-final/SOURCE_SELECTION.json'
FINAL_PACKAGE_SELECTION_SHA = '5d11ceace7898d207f58d5b38385c26686f3502360a62ef2d694dd36a69702ea'
SPLIT_ARTIFACTS_REVIEWED = True
SPLIT_ACCEPTED_MODULES = ['ImbalancedChen.P2Saving16Cell00FieldSimp', 'ImbalancedChen.P2Saving16Cell00FieldBase', 'ImbalancedChen.P2Saving16Cell00Simplex00Decode', 'ImbalancedChen.P2Saving16Cell00Simplex01Decode', 'ImbalancedChen.P2Saving16Cell00Simplex02Decode', 'ImbalancedChen.P2Saving16Cell00Simplex03Decode', 'ImbalancedChen.P2Saving16Cell00Simplex04Decode', 'ImbalancedChen.P2Saving16Cell00Simplex05Decode', 'ImbalancedChen.P2Saving16Cell00Simplex06Decode', 'ImbalancedChen.P2Saving16Cell00Simplex07Decode']
REUSED_OWNERS = ['ImbalancedChen.P2Saving16Cell00PayloadBinding', 'ImbalancedChen.P2OriginalSaving16DecoderCompose', 'ImbalancedChen.P2Saving16Cell00ScalarDecode', 'ImbalancedChen.P2Saving16Cell00FieldSimp', 'ImbalancedChen.P2Saving16Cell00FieldBase', 'ImbalancedChen.P2Saving16Cell00Simplex00Decode', 'ImbalancedChen.P2Saving16Cell00Simplex01Decode', 'ImbalancedChen.P2Saving16Cell00Simplex02Decode', 'ImbalancedChen.P2Saving16Cell00Simplex03Decode', 'ImbalancedChen.P2Saving16Cell00Simplex04Decode', 'ImbalancedChen.P2Saving16Cell00Simplex05Decode', 'ImbalancedChen.P2Saving16Cell00Simplex06Decode', 'ImbalancedChen.P2Saving16Cell00Simplex07Decode']
SPLIT_FRESH_MODULES = [*SPLIT_ACCEPTED_MODULES, TARGET]
SOURCES = {}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def now():
    return datetime.now(timezone.utc).isoformat()

def git(*args, cwd=ROOT):
    return subprocess.check_output(['git', *args], cwd=cwd, timeout=120).decode().strip()

def record_file(path):
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest(path)}

def project_closure(module):
    found = set()

    def visit(name):
        if name in found:
            return
        require(name in SOURCES, f'Unspecified project import: {name}')
        found.add(name)
        for imported in SOURCES[name]['project_imports']:
            visit(imported)

    visit(module)
    return found

def read_audit(log, module):
    lines = log.read_text().splitlines()
    records = [json.loads(s.removeprefix('P0_QUEUE_DECL ')) for s in lines if s.startswith('P0_QUEUE_DECL ')]
    inventories = [json.loads(s.removeprefix('P0_QUEUE_INVENTORY ')) for s in lines if s.startswith('P0_QUEUE_INVENTORY ')]
    imports = [json.loads(s.removeprefix('P0_QUEUE_IMPORTS ')) for s in lines if s.startswith('P0_QUEUE_IMPORTS ')]
    names = sorted(r['name'] for r in records)
    require(len(inventories) == len(imports) == 1 and inventories[0]['module'] == module,
            f'Missing/duplicate full inventory: {module}')
    require(names and len(names) == len(set(names)) and
            names == sorted(inventories[0]['serialized']) == sorted(inventories[0]['environment']),
            f'Incomplete serialized/environment/declaration inventory: {module}')
    require(all(r['module'] == module and not any(r[k] for k in ['axiom', 'partial', 'unsafe']) and
                set(r['axioms']) <= ALLOWED_AXIOMS for r in records), f'Forbidden declaration/axiom: {module}')
    actual = {m for m in imports[0] if m.startswith('ImbalancedChen.')}
    require(actual == project_closure(module), f'Actual project closure mismatch: {module}: {sorted(actual)}')
    return records, inventories[0], sorted(actual)

def audited_imports(log):
    rows = [json.loads(line.removeprefix('P0_QUEUE_IMPORTS '))
            for line in Path(log).read_text().splitlines() if line.startswith('P0_QUEUE_IMPORTS ')]
    require(len(rows) == 1 and len(rows[0]) == len(set(rows[0])),
            'Missing or duplicate full imported-module inventory.')
    return rows[0]

def read_private_scope_audit(log, records, required):
    # Same check as the unchanged Field-split 3b774024 driver, with explicit scope.
    marker = 'P25_PRIVATE_SCOPED_SIMP_INTERFACE '
    rows = [json.loads(s.removeprefix(marker)) for s in Path(log).read_text().splitlines() if s.startswith(marker)]
    require(len(rows) == 1, 'Missing or duplicate imported private scoped-simp interface audit.')
    row = rows[0]
    matches = row['matches']
    require(row['module'] == SUPPORT and row['scope'] == SCOPE and
            row['required_count'] == row['matched_count'] == len(matches) == len(required) == 296 and
            [r['user_name'] for r in matches] == required and len({r['actual_name'] for r in matches}) == 296,
            'Private scoped-simp interface inventory differs.')
    owned = {r['name'] for r in records}
    for match in matches:
        candidates = [name for name in owned if name.endswith('.' + match['user_name'])]
        require(candidates == [match['actual_name']] and match['actual_name'].startswith('_private.'),
                'Scoped-simp name is not the unique actual private declaration in the full owned audit.')
    return row


def public_theorem_statements(source):
    return re.findall(r'(?m)^(theorem\s+([A-Za-z0-9_]+)\b[\s\S]*?)\s*:=\s*by\b', source)



def main():
    global SOURCES
    require(isinstance(FINAL_SOURCE_SHA, str) and re.fullmatch(r'[0-9a-f]{64}', FINAL_SOURCE_SHA) and
            SPLIT_ARTIFACTS_REVIEWED is True,
            'SOURCE_ONLY: repaired source or actual split artifact review is incomplete; block before any filesystem mutation or gate.')
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]),
            'Pass exactly one full lowercase 40-hex publication commit.')
    publication = sys.argv[1]
    require(ROOT.is_dir() and not OUT.exists(), 'Expected checkout missing or attempt already exists; preserve prior attempts.')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 checkout is dirty.')
    OUT.mkdir()
    state = {
        'schema': 'p25-cell00-field-final-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
        'module_order': [TARGET], 'modules': {}, 'dependency_objects': {}, 'dependency_receipts': {},
        'dependency_modules_compiled': [], 'accepted_dependency_gates_rerun': [], 'existing_owners_normally_recompiled': [],
        'original_cell00_sha256': INPUT_SHA, 'host_correctness_credit': False,
        'failed_same_name_field_object_used': False, 'failed_aggregate_relabelled_as_success': False,
        'reused_original_owner_receipts': {}, 'reused_complete_context_validations': {},
        'source_receipt_by_reused_owner': {}, 'public_final_statements_unchanged': False,
        'private_scoped_simp_interface_checked': False, 'raw_root_typed_decode_proved': False,
        'original_archive_decode_proved': False, 'all_cell_finite_guards_proved': False,
        'source_cell_membership_proved': False, 'pulling_ownership_proved': False,
        'Q96_proved': False, 'P2_5_proved': False,
        'complete_external_after_matches_before': False, 'historical_missing_external_hashes_invented': False,
    }
    frozen = {}
    external_entries, providers = [], []
    expected_external = set()
    target_names = {TARGET}
    def write():
        temp = OUT / 'RESULT.tmp'
        temp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
        temp.replace(OUT / 'RESULT.json')

    def bind(path, expected=None):
        path = Path(path)
        actual = digest(path)
        require(expected is None or actual == expected, f'Artifact hash mismatch: {path}')
        require(str(path) not in frozen or frozen[str(path)] == actual, f'Artifact changed during preflight: {path}')
        frozen[str(path)] = actual
        return path

    def artifact(row, expected=None):
        path = bind(row['path'], expected or row['sha256'])
        require(digest(path) == row['sha256'] and path.stat().st_size == row['bytes'], f'Artifact record mismatch: {path}')
        return path

    def check_frozen():
        require(all(digest(path) == h for path, h in frozen.items()), 'Frozen source/object/receipt/log/runtime changed.')

    def external_resolutions():
        require(len(external_entries) == len(expected_external) == EXPECTED_EXTERNAL_COUNT,
                'Complete current external context has not been initialized.')
        for row in external_entries:
            relative = row['module'].replace('.', '/') + '.olean'
            found = [provider / relative for provider in providers if (provider / relative).is_file()]
            require([str(path) for path in found] == [row['object']['path']],
                    'External import provider changed: ' + row['module'])
            companions = [str(found[0]) + suffix for suffix in ['.private', '.server']
                          if Path(str(found[0]) + suffix).is_file()]
            require(companions == [entry['path'] for entry in row['companions']],
                    'External companion inventory changed: ' + row['module'])

    def context_check():
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Selected publication changed during gates.')
        require(git('rev-parse', 'HEAD', cwd=Path(state['runtime']['mathlib_path'])) == MATHLIB_PIN,
                'Mathlib source pin changed during gates.')
        external_resolutions()
        check_frozen()

    def require_external(log, expected_count=EXPECTED_EXTERNAL_COUNT):
        external = {m for m in audited_imports(log) if not m.startswith('ImbalancedChen.')}
        require(external <= expected_external and len(external) == expected_count,
                'Audited external imports are not the selected accepted subset of the complete current snapshot: ' + str(log))
        return external

    def stage_log(row, override=None):
        require(row['exit_code'] == 0 and not row.get('timed_out', False), 'Dependency stage did not pass.')
        path = Path(override) if override is not None else Path(row['log'])
        if not path.is_absolute():
            path = ROOT / path
        bound = bind(path, row['log_sha256'])
        require('log_bytes' not in row or bound.stat().st_size == row['log_bytes'], 'Stage log byte count mismatch.')
        return bound

    def strict_commands(stages, module, source, object_path, audit_source):
        require(stages['replay']['command'] == [str(CHECKER), '--verbose', module], f'Unexpected replay command: {module}')
        for label in ['normal', 'audit']:
            command = stages[label]['command']
            require(command[0] == str(LEAN) and
                    all(flag in command for flag in FLAGS),
                    f'Non-strict accepted stage: {module}/{label}')
        normal = stages['normal']['command']
        require(Path(normal[-1]) == source and Path(normal[normal.index('-o') + 1]) == object_path,
                f'Normal command/source/object binding mismatch: {module}')
        require(Path(stages['audit']['command'][-1]) == audit_source, f'Audit source binding mismatch: {module}')

    def copy_dependency(module, original, expected, provenance, companions=None):
        require(module in SOURCES and module not in target_names, f'Refuse a target/unknown dependency object: {module}')
        if module in KNOWN_OBJECTS:
            require(expected == KNOWN_OBJECTS[module], f'Known accepted object identity mismatch: {module}')
        original = bind(original, expected)
        companions = [] if companions is None else companions
        actual_companions = [str(original) + suffix for suffix in ['.private', '.server']
                             if Path(str(original) + suffix).is_file()]
        require(actual_companions == [row['path'] for row in companions],
                f'Project object companion set differs from accepted inventory: {module}')
        for row in companions:
            artifact(row)
        destination = lib / (module.replace('.', '/') + '.olean')
        if module in state['dependency_objects']:
            previous = state['dependency_objects'][module]
            require(previous['sha256'] == expected and digest(destination) == expected,
                    f'Conflicting accepted object provenance: {module}')
            previous_companions = [(Path(row['path']).suffix, row['sha256']) for row in previous['companions']]
            require(previous_companions == [(Path(row['path']).suffix, row['sha256']) for row in companions],
                    f'Conflicting accepted companion provenance: {module}')
            return
        require(not destination.exists(), f'Unexpected preexisting dependency object: {module}')
        shutil.copyfile(original, destination)
        bind(destination, expected)
        copied_companions = []
        for row in companions:
            target = Path(str(destination) + Path(row['path']).suffix)
            require(not target.exists(), f'Unexpected existing companion: {target}')
            shutil.copyfile(row['path'], target)
            bind(target, row['sha256'])
            copied_companions.append(record_file(target))
        state['dependency_objects'][module] = {
            'path': str(original), 'sha256': expected, 'isolated_path': str(destination),
            'source_sha256': SOURCES[module]['source_sha256'], 'provenance': provenance,
            'companions': copied_companions,
        }

    def modern_owner(container, receipt_path, module):
        owner = container['modules'][module]
        require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                f'Owner not accepted: {module}')
        require(owner['module'] == module and owner['source_origin']['sha256'] == SOURCES[module]['source_sha256'] and
                owner['source_origin']['commit'] == container['publication_commit'] and
                owner['source_origin']['path'] == SOURCES[module]['path'], f'Accepted source-origin binding mismatch: {module}')
        source = artifact(owner['source_copy'], SOURCES[module]['source_sha256'])
        audit_source = artifact(owner['audit_source'])
        required_audit = audit_template.replace(PAYLOAD, module) + (appendix_text if module == SUPPORT else '')
        require(audit_source.read_text() == required_audit, f'Changed complete-audit template: {module}')
        object_path = artifact(owner['object'])
        for label in ['normal', 'replay', 'audit']:
            require(owner['stages'][label]['status'] == 'PASSED', f'Owner stage not marked passed: {module}/{label}')
            stage_log(owner['stages'][label])
        strict_commands(owner['stages'], module, source, object_path, audit_source)
        records, inventory, imports = read_audit(Path(owner['stages']['audit']['log']), module)
        require(records == owner['owned_declarations'] and len(records) == owner['owned_count'] and
                json.loads(artifact(owner['declarations']).read_text()) == records and
                json.loads(artifact(owner['inventory']).read_text()) == inventory and
                owner['actual_project_closure'] == imports, f'Owner inventory/receipt/log mismatch: {module}')
        require(set(SOURCES[module]['public_names']) <= {r['name'] for r in records}, f'Accepted public declarations missing: {module}')
        if module == PAYLOAD:
            require(sorted(r['name'] for r in records) == expected_payload, 'Payload inventory is not exactly all 544 expected names.')
        require_external(owner['stages']['audit']['log'])
        if module == SUPPORT:
            scope = read_private_scope_audit(owner['stages']['audit']['log'], records, expected_private)
            require(json.loads(artifact(owner['private_scoped_simp_interface']).read_text()) == scope,
                    'FieldSimp stored scoped interface differs from actual full-owned audit marker.')
        copy_dependency(module, object_path, owner['object']['sha256'],
                        'Accepted normal/replay/full-owned owner and complete inventory revalidated',
                        owner.get('object_companions', []))
        state['dependency_receipts'][module] = {
            **record_file(receipt_path), 'owner_accepted': True, 'owner_status': owner['status'],
            'owner_publication': owner['source_origin']['commit'], 'owned_count': len(records),
        }

    def verify_reuse_validation(reuse, original_owner, original_receipt_path, container):
        module = original_owner['module']
        require(reuse['module'] == module and reuse['accepted'] is True and
                reuse['status'] == 'REPLAY_COMPLETE_OWNED_REUSE_VALIDATED' and
                reuse['normal_recompiled'] is False and set(reuse['stages']) == {'replay', 'audit'} and
                reuse['source_origin'] == original_owner['source_origin'] and
                reuse['source_copy'] == original_owner['source_copy'] and
                reuse['object']['sha256'] == original_owner['object']['sha256'] and
                artifact(reuse['original_owner_receipt']) == original_receipt_path,
                'Supplemental complete-context validation changed its original owner provenance: ' + module)
        artifact(reuse['source_copy'], SOURCES[module]['source_sha256'])
        artifact(reuse['object'], original_owner['object']['sha256'])
        audit_source = artifact(reuse['audit_source'])
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, module),
                'Supplemental full-owned audit template differs: ' + module)
        for label in ['replay', 'audit']:
            row = reuse['stages'][label]
            require(row['status'] == 'PASSED', 'Supplemental stage not accepted: ' + module + '/' + label)
            stage_log(row)
        require(reuse['stages']['replay']['command'] == [str(CHECKER), '--verbose', module],
                'Supplemental replay command differs: ' + module)
        command = reuse['stages']['audit']['command']
        require(command[0] == str(LEAN) and all(flag in command for flag in FLAGS) and
                Path(command[-1]) == audit_source, 'Supplemental full-owned command differs: ' + module)
        records, inventory, imports = read_audit(Path(reuse['stages']['audit']['log']), module)
        require_external(reuse['stages']['audit']['log'])
        require(records == reuse['owned_declarations'] == original_owner['owned_declarations'] and
                len(records) == reuse['owned_count'] == original_owner['owned_count'] and
                inventory == reuse['inventory'] == json.loads(artifact(original_owner['inventory']).read_text()) and
                imports == reuse['actual_project_closure'] == original_owner['actual_project_closure'] and
                reuse['complete_external_before'] == container['complete_external_before'],
                'Supplemental complete-context audit differs from the original full owner: ' + module)
        artifact(reuse['complete_external_before'])
        state['reused_complete_context_validations'][module] = reuse

    def verify_container_objects(container):
        # Every project module actually imported by a reused owner must resolve
        # to the very same accepted object bytes in the one new isolated root.
        objects = dict(container['dependency_objects'])
        objects.update({module: owner['object'] for module, owner in container['modules'].items()
                        if owner.get('accepted') is True})
        for module, row in objects.items():
            require(module in state['dependency_objects'] and
                    row['sha256'] == state['dependency_objects'][module]['sha256'],
                    'Accepted container project object differs in this isolated root: ' + module)

    def run_stage(owner, label, command, log):
        require(owner['module'] == TARGET and label in {'normal', 'replay', 'audit'},
                'Only the repaired final FieldDecode owner may execute compiler gates.')
        context_check()
        start = time.monotonic()
        row = {'command': command, 'status': 'RUNNING', 'started_utc': now(), 'log': str(log)}
        owner['stages'][label] = row
        write()
        print('P25_FIELD_FINAL_STAGE_START', owner['module'], label, flush=True)
        with log.open('wb') as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            try:
                code = process.wait(timeout=600)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=30)
                code = 124
        row.update(status='PASSED' if code == 0 else 'FAILED', exit_code=code, timed_out=timed_out,
                   seconds=round(time.monotonic() - start, 3), ended_utc=now(),
                   log_sha256=digest(log), log_bytes=log.stat().st_size)
        bind(log, row['log_sha256'])
        state['frozen_inputs'] = dict(frozen)
        write()
        print('P25_FIELD_FINAL_STAGE_RESULT', owner['module'], label,
              json.dumps({k: row[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}), flush=True)
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=owner['module'], failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{owner["module"]} {label} failed with exit {code}.')
        context_check()

    write()
    try:
        split_path = bind(SPLIT / 'RESULT.json', SPLIT_RESULT_SHA)
        split = json.loads(split_path.read_text())
        require(split['schema'] == 'p25-cell00-field-split-strict-v1' and split['accepted'] is False and
                split['status'] == 'MODULE_STAGE_FAILED' and split['publication_commit'] == SPLIT_PUBLICATION and
                split['failed_module'] == TARGET and split['failed_stage'] == 'normal' and
                split['module_order'] == SPLIT_FRESH_MODULES and set(split['modules']) == {*REUSED_OWNERS, TARGET} and
                all(split['modules'][m]['accepted'] is True for m in REUSED_OWNERS) and
                split['modules'][TARGET]['accepted'] is False and
                split['reused_module_order'] == list(REUSED_FIELD_OBJECTS) and
                split['reused_owners_recompiled'] == split['old_owner_normal_recompilations'] == [] and
                split['dependency_modules_compiled'] == [] and split['failed_same_name_field_object_used'] is False and
                split['failed_owner_object_used'] is False and
                split['original_theorem_commands_byte_identical'] is True and
                split['private_scoped_simp_interface_checked'] is True and
                split['complete_external_after_matches_before'] is False and
                split['historical_missing_external_hashes_invented'] is False and
                set(split['owner_receipt_sources']) == set(split['reused_owner_objects']) == set(REUSED_FIELD_OBJECTS) and
                set(split['additional_reuse_validations']) == set(REUSED_FIELD_OBJECTS),
                'Require the actual failed final aggregate with exactly thirteen individually accepted old owners.')
        failed_owner = split['modules'][TARGET]
        require(failed_owner['module'] == TARGET and failed_owner['status'] == 'NORMAL_FAILED' and
                failed_owner['source_origin'] == {'commit': SPLIT_PUBLICATION, 'path': SPLIT_FAILED_SOURCE_REL,
                                                   'sha256': SPLIT_FAILED_SOURCE_SHA} and
                set(failed_owner['stages']) == {'normal'}, 'The prior failed final owner was changed or relabeled.')
        failed_source = artifact(failed_owner['source_copy'], SPLIT_FAILED_SOURCE_SHA)
        failed_normal = failed_owner['stages']['normal']
        require(failed_normal['status'] == 'FAILED' and failed_normal['exit_code'] != 0 and
                failed_normal['timed_out'] is False and failed_normal['log_sha256'] == SPLIT_FAILED_NORMAL_SHA and
                failed_normal['command'] == [str(LEAN), *FLAGS, '--root=' + str(SPLIT / 'src'), '-o',
                    str(SPLIT / 'lib' / (TARGET.replace('.', '/') + '.olean')), str(failed_source)],
                'Prior final failure is not the selected ordinary normal-check failure.')
        failed_log = bind(failed_normal['log'], SPLIT_FAILED_NORMAL_SHA)
        require(failed_log.stat().st_size == failed_normal['log_bytes'], 'Prior normal failure log size differs.')
        state['prior_failed_final_owner'] = failed_owner
        state['failed_split_receipt'] = {**record_file(split_path), 'publication_commit': SPLIT_PUBLICATION,
            'aggregate_accepted': False, 'aggregate_status': split['status'], 'failed_owner_reused': False}
        prior_path = bind(PRIOR_FIELD / 'RESULT.json', PRIOR_FIELD_RESULT_SHA)
        prior = json.loads(prior_path.read_text())
        require(prior['publication_commit'] == PRIOR_FIELD_PUBLICATION and prior['accepted'] is False and
                prior['status'] == 'MODULE_STAGE_FAILED' and prior['failed_module'] == TARGET and
                prior['failed_stage'] == 'normal' and prior['modules'][TARGET]['accepted'] is False and
                prior['modules'][TARGET]['source_origin']['sha256'] == PRIOR_FIELD_SOURCE_SHA and
                split['prior_attempt']['path'] == str(prior_path) and
                split['prior_attempt']['sha256'] == PRIOR_FIELD_RESULT_SHA and
                split['prior_attempt']['accepted'] is False and split['prior_attempt']['failed_owner_reused'] is False,
                'Original ecfc failed-aggregate provenance changed.')
        remaining_path = bind(REMAINING / 'RESULT.json', REMAINING_RESULT_SHA)
        remaining = json.loads(remaining_path.read_text())
        require(remaining['accepted'] is True and remaining['schema'] == 'p25-cell00-remaining-arithmetic-strict-v1' and
                remaining['status'] == 'CELL00_ALL_EIGHT_TYPED_ARITHMETIC_ACCEPTED' and
                remaining['publication_commit'] == REMAINING_PUBLICATION and
                remaining['complete_external_after_matches_before'] is True,
                'Require the accepted current external-context source; no arithmetic proof owner is imported.')
        payload_path = bind(PAYLOAD_FLOORS / 'RESULT.json', PAYLOAD_RESULT_SHA)
        payload_receipt = json.loads(payload_path.read_text())
        require(payload_receipt['accepted'] is True and payload_receipt['modules'][PAYLOAD]['accepted'] is True,
                'Require the actual accepted 544-declaration payload owner.')

        initial_head = git('rev-parse', 'HEAD')
        if initial_head != publication:
            with (OUT / 'PUBLICATION.log').open('wb') as stream:
                subprocess.run(['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false',
                                'fetch', '--no-tags', 'origin', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
                ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', initial_head, publication],
                                          cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, timeout=120)
                require(ancestor.returncode == 0, 'Clean P3 HEAD is not an ancestor of the selected publication.')
                subprocess.run(['git', 'checkout', '--detach', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Target publication mismatch/dirty.')
        state['initial_checkout'] = {'commit': initial_head, 'ancestor_of_selected_publication': True}
        state['publication_checked_out'] = publication
        runner_path = Path(__file__).resolve()
        published_runner = subprocess.check_output(['git', 'show', publication + ':' + RUNNER_REL], cwd=ROOT, timeout=120)
        require(published_runner == runner_path.read_bytes(), 'Executing runner bytes differ from publication.')
        bind(runner_path, hashlib.sha256(published_runner).hexdigest())
        state['runner_publication_binding'] = {'commit': publication, 'path': RUNNER_REL,
            'sha256': digest(runner_path), 'executed_path': str(runner_path)}
        selection_path = bind(ROOT / SELECTION_REL, SELECTION_SHA)
        require(subprocess.check_output(['git', 'show', publication + ':' + SELECTION_REL], cwd=ROOT, timeout=120) == selection_path.read_bytes(),
                'Source/receipt selection differs from publication bytes.')
        selection = json.loads(selection_path.read_text())
        require(selection['schema'] == 'p25-cell00-field-final-source-and-receipt-selection-v1' and
                selection['dependency_receipt_selection_complete'] is True and selection['final_source_selection_complete'] is True and
                selection['fresh_owner_order'] == [TARGET] and selection['fresh_owner_count'] == 1 and
                selection['new_public_source_declaration_count'] == 4 and selection['project_module_count'] == 22 and
                selection['dependency_object_count'] == 21 and
                selection['normal_recompilation_of_existing_owners_permitted'] is False and
                selection['existing_owner_gate_reruns_permitted'] is False and
                selection['failed_same_name_objects_permitted'] is False and
                selection['original_ecfc_owner_receipts_preserved'] is True and
                selection['original_split_owner_receipts_preserved'] is True and
                selection['original_split_aggregate_relabeling_permitted'] is False and
                selection['expected_original_ecfc_owners'] == list(REUSED_FIELD_OBJECTS) and
                selection['expected_accepted_split_owners'] == SPLIT_ACCEPTED_MODULES,
                'Selection changes the one-owner/21-dependency scope or is incomplete.')
        for key, path, sha, commit in [('split', split_path, SPLIT_RESULT_SHA, SPLIT_PUBLICATION),
                                      ('original_ecfc', prior_path, PRIOR_FIELD_RESULT_SHA, PRIOR_FIELD_PUBLICATION),
                                      ('complete_external_context_only', remaining_path, REMAINING_RESULT_SHA, REMAINING_PUBLICATION)]:
            spec = selection['dependencies'][key]
            require(ROOT / spec['path'] == path and spec['sha256'] == sha and spec['publication_commit'] == commit,
                    'Selected dependency receipt identity differs: ' + key)
        require(selection['dependencies']['split']['aggregate_accepted'] is False and
                selection['dependencies']['split']['aggregate_status'] == 'MODULE_STAGE_FAILED' and
                selection['dependencies']['split']['failed_normal_log_sha256'] == SPLIT_FAILED_NORMAL_SHA,
                'The failed split aggregate must remain failed in source selection.')
        SOURCES = selection['source_graph']
        require(len(SOURCES) == 22 and TARGET in SOURCES and SOURCES[TARGET]['path'] == FINAL_SOURCE_REL and
                SOURCES[TARGET]['source_sha256'] == FINAL_SOURCE_SHA, 'Unexpected single-owner source graph.')
        old_driver = bind(ROOT / ADAPTED_FROM_REL, ADAPTED_FROM_SHA)
        require(old_driver.stat().st_size == selection['adapted_from']['bytes'] == 70770 and
                selection['adapted_from']['path'] == ADAPTED_FROM_REL and selection['adapted_from']['sha256'] == ADAPTED_FROM_SHA,
                'The frozen five-consumer draft was changed.')
        state['adapted_from_unchanged_driver'] = record_file(old_driver)
        state['source_and_receipt_selection'] = record_file(selection_path)
        base_path = bind(BASE / 'RESULT.json', BASE_RESULT_SHA)
        base = json.loads(base_path.read_text())
        snapshot = base['normal_snapshot_before']
        require(snapshot['mathlib_pin'] == MATHLIB_PIN and
                git('rev-parse', 'HEAD', cwd=Path(snapshot['mathlib_path'])) == MATHLIB_PIN, 'Mathlib pin mismatch.')
        for binary in [LEAN, CHECKER]:
            bind(binary, snapshot['files'][str(binary)]['sha256'])
        state['runtime'] = {'lean': record_file(LEAN), 'leanchecker': record_file(CHECKER),
                            'mathlib_pin': MATHLIB_PIN, 'mathlib_path': snapshot['mathlib_path']}
        state['runtime_context_receipt'] = record_file(base_path)
        src, lib, audit = OUT / 'src', OUT / 'lib', OUT / 'audit'
        for directory in [src / 'ImbalancedChen', lib / 'ImbalancedChen', audit]:
            directory.mkdir(parents=True)
        tails = base['approved_LEAN_PATH'].split(':')[1:]
        require(tails and all(p and Path(p).is_dir() and
                             Path(p).resolve().is_relative_to(Path('/mathlib').resolve()) and
                             not (Path(p) / 'ImbalancedChen').exists() for p in tails), 'Unexpected Mathlib/project fallback path.')
        env = dict(os.environ)
        env.pop('LEAN_SRC_PATH', None)
        env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
        env['LEAN_PATH'] = ':'.join([str(lib), *tails])
        env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')
        state.update(approved_LEAN_PATH=env['LEAN_PATH'], isolated_library=str(lib), isolated_source_root=str(src))
        for key, receipt, expected_runner in [('split', split, SPLIT_RUNNER_SHA),
                                               ('external_context_only', remaining, REMAINING_RUNNER_SHA)]:
            require(receipt['runtime'] == state['runtime'] and receipt['strict_flags'] == FLAGS and
                    receipt['approved_LEAN_PATH'].split(':')[1:] == tails,
                    'Reused receipt runtime or external paths differ: ' + key)
            artifact(receipt['runner'], expected_runner)
            if key == 'split':
                for path, sha in receipt['frozen_inputs'].items():
                    bind(path, sha)
        state['package_metadata'] = []
        for row in selection['package_pins']:
            path = bind(ROOT / row['path'], row['sha256'])
            require(path.stat().st_size == row['bytes'] and
                    subprocess.check_output(['git', 'show', publication + ':' + row['path']], cwd=ROOT, timeout=120) == path.read_bytes(),
                    'Selected package metadata differs from publication: ' + row['path'])
            state['package_metadata'].append(record_file(path))
        for module, source_spec in SOURCES.items():
            path = bind(ROOT / source_spec['path'], source_spec['source_sha256'])
            require(subprocess.check_output(['git', 'show', f'{publication}:{source_spec["path"]}'], cwd=ROOT, timeout=120) == path.read_bytes(),
                    'Source is not exact publication bytes: ' + module)
            imports = [name for line in re.findall(r'^import\s+([^\n]+)$', path.read_text(), re.M)
                       for name in line.split() if name.startswith('ImbalancedChen.')]
            require(imports == source_spec['project_imports'], 'Frozen source import graph mismatch: ' + module)
            namespace = source_spec.get('public_namespace')
            names = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)', path.read_text(), re.M)
            actual_public = [namespace + '.' + name for name in names] if namespace else []
            require(source_spec['public_names'] == actual_public, 'Frozen public source names differ: ' + module)
        require(selection['expected_project_closures'] == {TARGET: sorted(project_closure(TARGET))} and
                selection['selected_source_roots'] == [TARGET, *REUSED_OWNERS] and
                set().union(*(project_closure(m) for m in [TARGET, *REUSED_OWNERS])) == set(SOURCES) and
                len(SOURCES[TARGET]['public_names']) == 4,
                'The final source graph has missing/extraneous modules or public declarations.')
        final_selection_path = bind(ROOT / FINAL_PACKAGE_SELECTION_REL, FINAL_PACKAGE_SELECTION_SHA)
        final_selection = json.loads(final_selection_path.read_text())
        require(final_selection['schema'] == 'p25-cell00-field-final-source-selection-v1' and
                final_selection['fresh_owner_order'] == [TARGET] and final_selection['fresh_owner_count'] == 1 and
                final_selection['fresh_public_declarations'] == 4 and
                final_selection['selected_bundle_module_count'] == 22 and final_selection['reused_dependency_count'] == 21 and
                final_selection['selected_bundle_modules'] == sorted(SOURCES) and
                final_selection['reused_dependency_modules'] == sorted(set(SOURCES) - {TARGET}) and
                final_selection['expected_target_project_closure_count'] == 18 and
                final_selection['expected_target_project_closure'] == sorted(project_closure(TARGET)) and
                set(final_selection['source_graph']) == set(SOURCES) and
                all(all(final_selection['source_graph'][m][k] == row[k]
                        for k in ['path', 'source_sha256', 'project_imports']) for m, row in SOURCES.items()) and
                final_selection['source_graph'][TARGET]['public_namespace'] == SOURCES[TARGET]['public_namespace'] and
                final_selection['source_graph'][TARGET]['public_names'] == SOURCES[TARGET]['public_names'],
                'Frozen final proof package disagrees with the selected 22-bundle/18-import source graph.')
        state['final_proof_package_selection'] = record_file(final_selection_path)
        old_statements = public_theorem_statements(failed_source.read_text())
        new_statements = public_theorem_statements((ROOT / FINAL_SOURCE_REL).read_text())
        require(old_statements == new_statements and len(new_statements) == 4 and
                [TARGET + '.' + name for _, name in new_statements] == SOURCES[TARGET]['public_names'],
                'The four final theorem statements or their order changed.')
        state['public_final_statements_unchanged'] = True
        state['prior_failed_final_source'] = record_file(failed_source)
        state['source_graph'] = SOURCES
        state['expected_project_imports_by_owner'] = {TARGET: sorted(project_closure(TARGET))}
        appendix_path = bind(ROOT / SCOPED_APPENDIX_REL, SCOPED_APPENDIX_SHA)
        appendix_text = appendix_path.read_text()
        expected_private = [SCOPE + '.' + name for name in re.findall(r'^private theorem ([A-Za-z0-9_]+)\b',
                            (ROOT / SOURCES[SUPPORT]['path']).read_text(), re.M)]
        require(len(expected_private) == len(set(expected_private)) == 296 and
                expected_private == split['source_identity_check']['private_user_names'] and
                re.findall(r'^    "(ImbalancedChen\.[^"]+)"[,\]]', appendix_text, re.M) == expected_private,
                'FieldSimp audit does not cover every original private theorem.')
        require(split['command_identity']['sha256'] == '9f33526038f4d7e403cdbf3e422b386af2d861733e743ea0c0a690f66a7c5657' and
                split['source_identity_check']['original_commands'] == 442 and
                split['source_identity_check']['all_commands_byte_identical'] is True and
                split['scoped_simp_audit_appendix']['sha256'] == SCOPED_APPENDIX_SHA,
                'Original split command/scoped-simp identity evidence differs; the repaired final proof is recorded separately.')
        payload_files_path = bind(ROOT / 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_FILES.json', PAYLOAD_FILES_SHA)
        payload_files = json.loads(payload_files_path.read_text())
        expected_payload = sorted(payload_files['expected_owned_names'])
        require(payload_files['module'] == PAYLOAD and payload_files['expected_owned_declarations'] ==
                len(expected_payload) == len(set(expected_payload)) == 544, 'Payload expected inventory differs.')
        for row in payload_files['files']:
            bind(ROOT / row['path'], row['sha256'])
        audit_template_path = bind(ROOT / payload_files['audit_file'])
        audit_template = audit_template_path.read_text()
        state['audit_template'] = record_file(audit_template_path)

        # The failed aggregate has no success-after claim. Its accepted owner
        # audits and prior complete snapshot are preserved; all current hashes
        # are checked again against the already accepted arithmetic snapshot.
        current_snapshot_path = artifact(remaining['complete_external_before'], EXTERNAL_SNAPSHOT_SHA)
        require(current_snapshot_path == REMAINING / 'COMPLETE_EXTERNAL_BEFORE.json' and
                selection['external_context']['sha256'] == EXTERNAL_SNAPSHOT_SHA,
                'Accepted complete-current snapshot identity differs.')
        current_snapshot = json.loads(current_snapshot_path.read_text())
        providers = [LEAN.parent.parent / 'lib/lean', *map(Path, tails)]
        require(len(providers) == len(set(providers)) and
                all(provider.is_dir() and not (provider / 'ImbalancedChen').exists() for provider in providers) and
                current_snapshot['provider_roots'] == list(map(str, providers)) and
                current_snapshot['schema'] == 'p25-complete-current-external-snapshot-v1' and
                current_snapshot['module_count'] == EXPECTED_EXTERNAL_COUNT and
                current_snapshot['historical_missing_hashes_invented'] is False,
                'Complete-current snapshot/provider provenance differs.')
        expected_external = {row['module'] for row in current_snapshot['entries']}
        require(len(expected_external) == len(current_snapshot['entries']) == EXPECTED_EXTERNAL_COUNT and
                sum(len(row['companions']) for row in current_snapshot['entries']) == EXPECTED_EXTERNAL_COMPANIONS,
                'Complete external module/companion inventory differs.')
        context_start = now()
        for row in current_snapshot['entries']:
            module = row['module']
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module),
                    'Invalid external module name.')
            relative = module.replace('.', '/') + '.olean'
            found = [provider / relative for provider in providers if (provider / relative).is_file()]
            require(len(found) == 1 and str(found[0]) == row['object']['path'],
                    'Missing or shadowed accepted-current provider: ' + module)
            obj = artifact(row['object'])
            require(remaining['frozen_inputs'].get(str(obj)) == row['object']['sha256'],
                    'Accepted current context did not freeze external object: ' + module)
            actual_companions = [str(obj) + suffix for suffix in ['.private', '.server'] if Path(str(obj) + suffix).is_file()]
            require(actual_companions == [item['path'] for item in row['companions']],
                    'Accepted current companion inventory changed: ' + module)
            for companion in row['companions']:
                artifact(companion)
                require(remaining['frozen_inputs'].get(companion['path']) == companion['sha256'],
                        'Accepted current context did not freeze companion: ' + module)
            external_entries.append({'module': module, 'object': row['object'], 'companions': row['companions']})
        expected_external_records = {row['module']: (row['object'], row['companions']) for row in external_entries}
        split_snapshot = json.loads(artifact(split['complete_external_before']).read_text())
        require(split_snapshot['provider_roots'] == list(map(str, providers)) and
                split_snapshot['module_count'] == EXPECTED_EXTERNAL_COUNT and len(split_snapshot['entries']) == EXPECTED_EXTERNAL_COUNT and
                {row['module']: (row['object'], row['companions']) for row in split_snapshot['entries']} == expected_external_records,
                'The original accepted split owners used a different complete context.')
        for row in external_entries:
            for record in [row['object'], *row['companions']]:
                require(split['frozen_inputs'].get(record['path']) == record['sha256'],
                        'Split receipt did not freeze an external object or companion: ' + row['module'])
        before = {'schema': 'p25-complete-current-external-snapshot-reuse-v1',
                  'started_utc': context_start, 'finished_utc': now(), 'provider_roots': list(map(str, providers)),
                  'module_count': len(external_entries), 'source_accepted_receipt': record_file(remaining_path),
                  'source_complete_snapshot': record_file(current_snapshot_path),
                  'all_hashes_reused_from_accepted_current_snapshot': True,
                  'historical_missing_hashes_invented': False, 'entries': external_entries}
        before_path = OUT / 'COMPLETE_EXTERNAL_BEFORE.json'
        before_path.write_text(json.dumps(before, indent=2) + '\n')
        bind(before_path)
        state['complete_external_before'] = record_file(before_path)
        state['external_context_receipt'] = record_file(remaining_path)
        state['external_context_only_proof_owners_imported'] = []
        state['expected_external_imports'] = sorted(expected_external)

        for module, expected_object in REUSED_FIELD_OBJECTS.items():
            selected_receipt = split['owner_receipt_sources'][module]
            require(artifact(selected_receipt, PRIOR_FIELD_RESULT_SHA) == prior_path and
                    selected_receipt['owner_module'] == module and selected_receipt['owner_accepted'] is True and
                    selected_receipt['aggregate_status'] == prior['status'] and selected_receipt['aggregate_accepted'] is False and
                    selected_receipt['owner_source_origin'] == prior['modules'][module]['source_origin'] and
                    selected_receipt['owner_object_sha256'] == expected_object and
                    split['modules'][module] == prior['modules'][module] and
                    prior['modules'][module]['source_origin']['commit'] == PRIOR_FIELD_PUBLICATION and
                    prior['modules'][module]['object']['sha256'] == expected_object,
                    'An original ecfc owner was relabeled or its accepted bytes changed: ' + module)
            row = split['reused_owner_objects'][module]
            require(row['sha256'] == expected_object and row['source_sha256'] == SOURCES[module]['source_sha256'],
                    'Original ecfc reused source/object differs: ' + module)
            bind(row['path'], expected_object)
            bind(row['isolated_path'], expected_object)
        expected_base_dependencies = set().union(*(project_closure(m) for m in [*REUSED_OWNERS, TARGET])) - {*REUSED_OWNERS, TARGET}
        require(set(split['dependency_objects']) == expected_base_dependencies and len(expected_base_dependencies) == 8,
                'The eight original base dependency modules differ from the selected graph.')
        for module, row in split['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'], 'Reused base source hash differs: ' + module)
            bind(row['path'], row['sha256'])
            copy_dependency(module, row['isolated_path'], row['sha256'],
                            'Exact accepted base dependency from unchanged split provenance; no gate rerun', row.get('companions', []))
        for module in REUSED_OWNERS:
            origin = prior if module in REUSED_FIELD_OBJECTS else split
            origin_path = prior_path if module in REUSED_FIELD_OBJECTS else split_path
            modern_owner(origin, origin_path, module)
            state['reused_original_owner_receipts'][module] = origin['modules'][module]
            state['source_receipt_by_reused_owner'][module] = {
                **record_file(origin_path), 'publication_commit': origin['publication_commit'],
                'aggregate_accepted': False, 'aggregate_status': origin['status'], 'owner_accepted': True}
        for module in REUSED_FIELD_OBJECTS:
            verify_reuse_validation(split['additional_reuse_validations'][module], prior['modules'][module], prior_path, split)
        modern_owner(payload_receipt, payload_path, PAYLOAD)
        state['payload_owner_receipt'] = record_file(payload_path)
        for container in [prior, split]:
            verify_container_objects(container)
        state['private_scoped_simp_interface_checked'] = True
        needed = set().union(*(project_closure(m) for m in [TARGET, *REUSED_OWNERS])) - {TARGET}
        require(set(state['dependency_objects']) == needed and len(needed) == 21 and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 21 and
                set(state['reused_original_owner_receipts']) == set(REUSED_OWNERS) and
                set(state['reused_complete_context_validations']) == set(REUSED_FIELD_OBJECTS) and
                not (lib / (TARGET.replace('.', '/') + '.olean')).exists(),
                'Initial isolated root must contain exactly 21 accepted objects and no failed final object.')

        source = src / (TARGET.replace('.', '/') + '.lean')
        source.write_bytes((ROOT / FINAL_SOURCE_REL).read_bytes())
        bind(source, FINAL_SOURCE_SHA)
        audit_path = audit / (TARGET.split('.')[-1] + '.lean')
        audit_path.write_text(audit_template.replace(PAYLOAD, TARGET))
        bind(audit_path)
        owner = {'module': TARGET, 'status': 'PENDING', 'accepted': False,
                 'source_origin': {'commit': publication, 'path': FINAL_SOURCE_REL, 'sha256': FINAL_SOURCE_SHA},
                 'source_copy': record_file(source), 'audit_source': record_file(audit_path),
                 'required_owned_names': SOURCES[TARGET]['public_names'], 'stages': {}}
        state['modules'][TARGET] = owner
        state.update(status='VERIFYING_REPAIRED_FINAL_OWNER', frozen_inputs=dict(frozen))
        context_check()
        write()
        directory = OUT / TARGET.split('.')[-1]
        directory.mkdir()
        object_path = lib / (TARGET.replace('.', '/') + '.olean')
        require(not object_path.exists() and all(m in state['dependency_objects'] for m in project_closure(TARGET) - {TARGET}),
                'Final target exists or an accepted dependency is missing.')
        owner['status'] = 'RUNNING'
        for label, command in [('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(object_path), str(source)]),
                               ('replay', [str(CHECKER), '--verbose', TARGET]),
                               ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(audit_path)])]:
            run_stage(owner, label, command, directory / (label.upper() + '.log'))
            if label == 'normal':
                bind(object_path)
                owner['object'] = record_file(object_path)
                owner['object_companions'] = []
                for suffix in ['.private', '.server']:
                    companion = Path(str(object_path) + suffix)
                    if companion.exists():
                        bind(companion)
                        owner['object_companions'].append(record_file(companion))
                state['frozen_inputs'] = dict(frozen)
                write()
        records, inventory, imports = read_audit(directory / 'AUDIT.log', TARGET)
        require(set(owner['required_owned_names']) <= {r['name'] for r in records}, 'Required final public theorem missing.')
        external = require_external(directory / 'AUDIT.log')
        owner['actual_external_import_count'] = len(external)
        owner['complete_external_before'] = record_file(before_path)
        declarations_path, inventory_path = directory / 'OWNED_DECLARATIONS.json', directory / 'OWNED_INVENTORY.json'
        declarations_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n')
        inventory_path.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + '\n')
        bind(declarations_path)
        bind(inventory_path)
        state['frozen_inputs'] = dict(frozen)
        owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                     owned_count=len(records), owned_declarations=records, actual_project_closure=imports,
                     declarations=record_file(declarations_path), inventory=record_file(inventory_path), ended_utc=now())
        context_check()
        require(set(state['modules']) == {TARGET} and state['module_order'] == [TARGET] and owner['accepted'] is True and
                state['dependency_modules_compiled'] == state['existing_owners_normally_recompiled'] == state['accepted_dependency_gates_rerun'] == [] and
                all(state['reused_original_owner_receipts'][m] == prior['modules'][m] for m in REUSED_FIELD_OBJECTS) and
                all(state['reused_original_owner_receipts'][m] == split['modules'][m] for m in SPLIT_ACCEPTED_MODULES) and
                state['failed_split_receipt']['aggregate_accepted'] is False and
                state['prior_failed_final_owner'] == failed_owner and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 22,
                'Single-owner gate scope or unchanged historical provenance differs.')
        state.update(status='FINAL_FIELD_TYPED_DECODE_ACCEPTED', accepted=True,
                     raw_root_typed_decode_proved=True, complete_external_after_matches_before=True,
                     frozen_inputs=dict(frozen), ended_utc=now())
        write()
        print('P25_FIELD_FINAL_RESULT', json.dumps({'status': state['status'], 'accepted': True,
              'module': TARGET, 'owned_count': owner['owned_count'], 'reused_dependency_objects': 21,
              'original_ecfc_owner_receipts_preserved': 3, 'original_split_owner_receipts_preserved': 10,
              'original_failed_split_aggregate_accepted': False, 'raw_root_typed_decode_proved': True,
              'original_archive_decode_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
              'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json')}, sort_keys=True), flush=True)
    except BaseException as exc:
        if state['status'] != 'MODULE_STAGE_FAILED':
            state['status'] = 'FAILED'
        state.update(accepted=False, error=f'{type(exc).__name__}: {exc}', ended_utc=now())
        (OUT / 'RUNNER_EXCEPTION.log').write_text(traceback.format_exc())
        state['exception_log'] = record_file(OUT / 'RUNNER_EXCEPTION.log')
        write()
        print('P25_FIELD_FINAL_FAILED', json.dumps({'status': state['status'], 'error': state['error'][:1800],
              'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json')}, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
