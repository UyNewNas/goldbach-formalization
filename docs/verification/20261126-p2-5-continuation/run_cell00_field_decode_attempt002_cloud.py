#!/usr/bin/env python3
"""SOURCE ONLY: retry only the repaired FieldDecode owner on P3.

Pass the exact publication commit as argv1. The three earlier accepted owners
are revalidated from attempt001 and reused with their original source origins,
stages and complete owner receipts unchanged. Only FieldDecode is compiled.
The failed aggregate and its failed same-name owner are never relabeled accepted.
Submit only after the original complete FieldDecode diagnostic is reviewed.
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
BASE = ROOT / '.lake/diagnostic/p25-cell00-canonical-attempt001/charparse'
OUT = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt002'
PRIOR = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt001'
PRIOR_RESULT_SHA = '86afeed917a3361c5457db1b7b3f4546d2e513531288adfab3d3a196ad38eac1'
PRIOR_FAILED_SOURCE_SHA = 'c62cf0315fafe2733393627137963dcb507827c988a49115add3a11422a244ed'
PRIOR_FAILED_NORMAL_LOG_SHA = '4528afb43ddd36cf5825ebfe8fe6a82ca7b200ac4f93fbe18a0d5833e9b02a25'
TARGET = 'ImbalancedChen.P2Saving16Cell00FieldDecode'
REUSED_OBJECTS = {
    'ImbalancedChen.P2Saving16Cell00PayloadBinding': 'f1bff7f79f8e43f8a98e5eca39b520b928b46016a297af9272a6cb2b65f065c8',
    'ImbalancedChen.P2OriginalSaving16DecoderCompose': 'df91e32fa010265bb3ad1dba9f317233ce9c1b48beb0c668e5bca70666c452ed',
    'ImbalancedChen.P2Saving16Cell00ScalarDecode': '6a313fad2e0bb6a42a0a73e8f0c5c3360576b10e6de8f34511139711a6e64aeb',
}
PAYLOAD_RESULT_SHA = '090463b93761d31023f39111c32522e1f2bb3cbcec46e606f7fc429d69d4a204'
CHARS_RESULT_SHA = '315bb7c65ca80f821bd109deb226587296e75dca26e9d94d45c92f885e8d92f9'
REPRODUCED = ROOT / '.lake/diagnostic/p25-cell00-decoded-attempt002'
PAYLOAD_RESULT = ROOT / '.lake/diagnostic/p25-payload-floors-attempt001/RESULT.json'
CHARS_RESULT = ROOT / '.lake/diagnostic/p25-decoder-chars-attempt004/RESULT.json'
PACKAGE = Path('docs/source-only/20261126-p2-5-cell00-decoded')
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
OLD_RESULT_SHA = '4dca8c2c7b42feb027895420ddb62e0a314d5f6f440d8b772704eeb146ba37eb'
PAYLOAD_FILES_SHA = '76aa078eef969fa6c8d8270529f3d68f50b4bb6762626ba14a484423bbdc4321'
FUEL_RECEIPT_SHA = '9792af6d5093daf404acebe2a7aeecd0167ff7158ecf07e13b8354c67615e26a'
DIRECT_RECEIPT_SHA = 'a05d2bf89fbf2d57f03d4aa9fae512de96928a38b323bab65bb782520613b8dd'
PAYLOAD = 'ImbalancedChen.P2Saving16Cell00TypedPayload'
CHARS = 'ImbalancedChen.P2OriginalSaving16DecoderChars'
FUEL = 'ImbalancedChen.P2OriginalSaving19SourceJsonFuel'
DIRECT = 'ImbalancedChen.P2Saving16Cell00DirectParse'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
BASE_OBJECTS = {
    'ImbalancedChen.P2OriginalSaving16Decoder':
        'fd25815778e3bae5518d3fcc6a5461724b64251f91c4c08e61312fbae4987b39',
    'ImbalancedChen.P2OriginalSaving16Q96FloorCore':
        '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9',
    'ImbalancedChen.P2OriginalSaving19SourceJson':
        '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7',
    'ImbalancedChen.P2Saving16StringCharBinding00':
        'a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a',
}
REPRODUCED_OBJECTS = {
    FUEL: '9928b1cd0dd91cc93ff2055f00d0d147d455dd8d27783cf110e58df3d61bd088',
    DIRECT: '52cf731b62270e0fdfee8468d813aacfe373853e51035b88c669dd8713393f2a',
}

# Filled from the frozen, inspected source files when this runner is prepared.
SOURCES = {'ImbalancedChen.P2OriginalSaving16Decoder': {'path': 'ImbalancedChen/P2OriginalSaving16Decoder.lean',
                                              'source_sha256': 'e1b23e3de928a97c411d1c6aa73f2059b204d7b9f297105edcd591916b9aee80',
                                              'project_imports': ['ImbalancedChen.P2OriginalSaving16Q96FloorCore',
                                                                  'ImbalancedChen.P2OriginalSaving19SourceJson']},
 'ImbalancedChen.P2OriginalSaving16Q96FloorCore': {'path': 'ImbalancedChen/P2OriginalSaving16Q96FloorCore.lean',
                                                   'source_sha256': '9a456807e6c3a167fd12c1c6e5db492d6c54fd700a1de122ea492774f697c778',
                                                   'project_imports': []},
 'ImbalancedChen.P2OriginalSaving19SourceJson': {'path': 'ImbalancedChen/P2OriginalSaving19SourceJson.lean',
                                                 'source_sha256': 'd58e22ba7e2d92b6c9f2d139993361ae9b827d25d6869fcf38f3837ba7bc3d02',
                                                 'project_imports': []},
 'ImbalancedChen.P2Saving16StringCharBinding00': {'path': 'ImbalancedChen/P2Saving16StringCharBinding00.lean',
                                                  'source_sha256': 'd2353e0a96ce78a8ba2da3d3d47f835593dcf758ea6110fd088c82df038f008c',
                                                  'project_imports': []},
 'ImbalancedChen.P2OriginalSaving19SourceJsonFuel': {'path': 'ImbalancedChen/P2OriginalSaving19SourceJsonFuel.lean',
                                                     'source_sha256': '0c98bd29f628bade9657a6828772fa2499c9be8dd2d3b16bfea5cd206405c1e4',
                                                     'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJson']},
 'ImbalancedChen.P2Saving16Cell00DirectParse': {'path': 'ImbalancedChen/P2Saving16Cell00DirectParse.lean',
                                                'source_sha256': 'fa1c92a5fd127b913958a6a10373e8a041433ac74a4a8c36ab06da709356956c',
                                                'project_imports': ['ImbalancedChen.P2OriginalSaving19SourceJsonFuel',
                                                                    'ImbalancedChen.P2Saving16StringCharBinding00']},
 'ImbalancedChen.P2Saving16Cell00TypedPayload': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00TypedPayload.lean',
                                                 'source_sha256': 'e92848bd075bf82fe7325bd46e3ddcde937cba277387d46a3579560c27aa287b',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16Decoder']},
 'ImbalancedChen.P2OriginalSaving16DecoderChars': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2OriginalSaving16DecoderChars.lean',
                                                   'source_sha256': '01b1e5cff72305ab75aa1feb7c5574469ddfbd51af40cc012d75464a44473ca5',
                                                   'project_imports': ['ImbalancedChen.P2OriginalSaving16Decoder']},
 'ImbalancedChen.P2Saving16Cell00PayloadBinding': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00PayloadBinding.lean',
                                                   'source_sha256': '61722aa2f8d764fa757245784217e2f9cd9442393333cb594e334b1883425c1b',
                                                   'project_imports': ['ImbalancedChen.P2Saving16Cell00TypedPayload',
                                                                       'ImbalancedChen.P2Saving16Cell00DirectParse']},
 'ImbalancedChen.P2OriginalSaving16DecoderCompose': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2OriginalSaving16DecoderCompose.lean',
                                                     'source_sha256': 'b651fb5defedcee7dea0b0b9beee106a984b8ef59bf27104b579fb453faa7e36',
                                                     'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderChars']},
 'ImbalancedChen.P2Saving16Cell00ScalarDecode': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00ScalarDecode.lean',
                                                 'source_sha256': 'ba4424e7db6a4efdcd88278b80c129e15cb9049e193adbf7f0e95825964bb9f3',
                                                 'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderChars',
                                                                     'ImbalancedChen.P2Saving16Cell00TypedPayload']},
 'ImbalancedChen.P2Saving16Cell00FieldDecode': {'path': 'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00FieldDecode.lean',
                                                'source_sha256': '3bca40fbe7f5484ce50da650d9c505026e1634f0c0accdcda3dfe93ab5698b96',
                                                'project_imports': ['ImbalancedChen.P2OriginalSaving16DecoderCompose',
                                                                    'ImbalancedChen.P2Saving16Cell00ScalarDecode']}}
MODULES = [{'module': 'ImbalancedChen.P2Saving16Cell00PayloadBinding',
  'namespace': 'ImbalancedChen.P2Saving16Cell00PayloadBinding',
  'public_count': 1,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00PayloadBinding.rootValue_eq_rawRoot'},
 {'module': 'ImbalancedChen.P2OriginalSaving16DecoderCompose',
  'namespace': 'ImbalancedChen.P2OriginalSaving16OriginalArchive',
  'public_count': 6,
  'required_final_name': 'ImbalancedChen.P2OriginalSaving16OriginalArchive.decodeArray_arr'},
 {'module': 'ImbalancedChen.P2Saving16Cell00ScalarDecode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00ScalarDecode',
  'public_count': 227,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00ScalarDecode.integer015_decoded'},
 {'module': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'namespace': 'ImbalancedChen.P2Saving16Cell00FieldDecode',
  'public_count': 146,
  'required_final_name': 'ImbalancedChen.P2Saving16Cell00FieldDecode.rawRoot_decoded'}]


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
    seen = set()

    def visit(name):
        if name in seen:
            return
        require(name in SOURCES, f'Unspecified project dependency: {name}')
        seen.add(name)
        for imported in SOURCES[name]['project_imports']:
            visit(imported)

    visit(module)
    return seen


def read_audit(log, module):
    lines = log.read_text().splitlines()
    records = [json.loads(s.removeprefix('P0_QUEUE_DECL ')) for s in lines if s.startswith('P0_QUEUE_DECL ')]
    inventories = [json.loads(s.removeprefix('P0_QUEUE_INVENTORY ')) for s in lines if s.startswith('P0_QUEUE_INVENTORY ')]
    imports = [json.loads(s.removeprefix('P0_QUEUE_IMPORTS ')) for s in lines if s.startswith('P0_QUEUE_IMPORTS ')]
    names = sorted(r['name'] for r in records)
    require(len(inventories) == len(imports) == 1 and inventories[0]['module'] == module,
            f'Missing or duplicate full audit inventory: {module}')
    require(names and len(names) == len(set(names)) and
            names == sorted(inventories[0]['serialized']) == sorted(inventories[0]['environment']),
            f'Complete serialized/environment/declaration inventory mismatch: {module}')
    require(all(r['module'] == module and not any(r[k] for k in ['unsafe', 'partial', 'axiom']) and
                set(r['axioms']) <= ALLOWED_AXIOMS for r in records),
            f'Unsafe/partial/axiom or forbidden transitive axiom: {module}')
    actual = {m for m in imports[0] if m.startswith('ImbalancedChen.')}
    require(actual == project_closure(module), f'Unexpected actual project imports for {module}: {sorted(actual)}')
    return records, inventories[0], sorted(actual)


def main():
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]),
            'Pass exactly one full lowercase 40-hex publication commit.')
    publication = sys.argv[1]
    require(ROOT.is_dir(), 'Expected P3 checkout is missing.')
    require(not OUT.exists(), f'Preserve prior attempt: {OUT}')
    require(not git('status', '--porcelain', '--untracked-files=no'), 'Tracked P3 worktree is dirty.')
    OUT.mkdir()
    state = {
        'schema': 'p25-cell00-field-decode-retry-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
        'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
        'module_order': [TARGET], 'modules': {},
        'reused_module_order': list(REUSED_OBJECTS), 'reused_owner_objects': {}, 'owner_receipt_sources': {},
        'reused_owners_recompiled': [], 'failed_same_name_field_object_used': False,
        'dependency_modules_compiled': [], 'dependency_objects': {}, 'dependency_receipts': {},
        'private_records_written': [], 'original_cell00_sha256': INPUT_SHA,
        'failed_owner_object_used': False, 'host_correctness_credit': False,
        'certified_reader_ast_binding_proved': False, 'raw_root_typed_decode_proved': False,
        'original_string_typed_decode_proved': False, 'geometric_jensen_binding_proved': False,
        'Q96_proved': False, 'P2_5_proved': False,
    }
    frozen = {}

    def write():
        temp = OUT / 'RESULT.tmp'
        temp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
        temp.replace(OUT / 'RESULT.json')

    def bind(path, expected=None):
        path = Path(path)
        actual = digest(path)
        require(expected is None or actual == expected, f'Frozen artifact hash mismatch: {path}')
        require(str(path) not in frozen or frozen[str(path)] == actual, f'Artifact changed during preflight: {path}')
        frozen[str(path)] = actual
        return path

    def artifact(row, expected=None):
        path = bind(row['path'], expected or row['sha256'])
        require(digest(path) == row['sha256'], f'Artifact record hash mismatch: {path}')
        require(path.stat().st_size == row['bytes'], f'Artifact byte count mismatch: {path}')
        return path

    def check_frozen():
        require(all(digest(p) == h for p, h in frozen.items()), 'A frozen source/object/log/receipt/runtime changed.')

    def stage_log(row, override=None):
        require(row['exit_code'] == 0 and not row.get('timed_out', False), 'Dependency stage did not pass.')
        path = Path(override) if override is not None else Path(row['log'])
        if not path.is_absolute():
            path = ROOT / path
        return bind(path, row['log_sha256'])

    def copy_dependency(module, original, expected, provenance):
        require(module in SOURCES and module != TARGET and module not in state['dependency_objects'],
                f'Unknown, failed-target or duplicate dependency source: {module}')
        original = bind(original, expected)
        destination = lib / (module.replace('.', '/') + '.olean')
        require(not destination.exists(), f'Dependency copy target already exists: {module}')
        shutil.copyfile(original, destination)
        bind(destination, expected)
        state['dependency_objects'][module] = {
            'path': str(original), 'sha256': expected, 'isolated_path': str(destination),
            'source_sha256': SOURCES[module]['source_sha256'], 'provenance': provenance,
        }

    def verify_component(receipt_path, receipt, module):
        bind(receipt_path)
        owner = receipt['modules'][module]
        require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                f'Required future owner is not accepted: {module}')
        require(owner['module'] == module and owner['source_origin']['sha256'] == SOURCES[module]['source_sha256'],
                f'Accepted future source identity mismatch: {module}')
        require(owner['source_origin']['commit'] == receipt['publication_commit'] and
                owner['source_origin']['path'] == SOURCES[module]['path'],
                f'Accepted future publication/path binding mismatch: {module}')
        source_copy = artifact(owner['source_copy'], SOURCES[module]['source_sha256'])
        audit_source = artifact(owner['audit_source'])
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, module),
                f'Accepted owner used a different complete-audit template: {module}')
        object_path = artifact(owner['object'])
        for label in ['normal', 'replay', 'audit']:
            stage = owner['stages'][label]
            require(stage['status'] == 'PASSED', f'Accepted owner stage is not marked passed: {module}/{label}')
            stage_log(stage)
            command = stage['command']
            if label == 'replay':
                require(command == [str(CHECKER), '--verbose', module], f'Unexpected accepted replay command: {module}')
            else:
                require(command[0] == str(LEAN) and all(f in command for f in ['-t0', '-j1', '-M11264', '-DwarningAsError=true']),
                        f'Accepted owner was not compiled/audited with strict flags: {module}/{label}')
        normal_command = owner['stages']['normal']['command']
        require(Path(normal_command[-1]) == source_copy and
                Path(normal_command[normal_command.index('-o') + 1]) == object_path,
                f'Accepted normal command does not bind this source/object pair: {module}')
        require(Path(owner['stages']['audit']['command'][-1]) == audit_source,
                f'Accepted audit command/source mismatch: {module}')
        records, inventory, imports = read_audit(Path(owner['stages']['audit']['log']), module)
        require(records == owner['owned_declarations'] and len(records) == owner['owned_count'],
                f'Accepted owner declaration receipt differs from actual audit log: {module}')
        require(json.loads(artifact(owner['declarations']).read_text()) == records and
                json.loads(artifact(owner['inventory']).read_text()) == inventory,
                f'Accepted owner inventory/declaration file mismatch: {module}')
        require(owner['actual_project_closure'] == imports, f'Accepted import closure receipt mismatch: {module}')
        if module == PAYLOAD:
            require(sorted(r['name'] for r in records) == expected_payload, 'Accepted payload is not all 544 expected declarations.')
            require(owner['object']['sha256'] == '1c61948df2571b065f3b27ae2eeeff1202b942e39bb16229f93c9cc40b1e8c75',
                    'Accepted payload object identity differs.')
        elif module == CHARS:
            required = {'ImbalancedChen.P2OriginalSaving16OriginalArchive.' + n
                        for n in ['parseInteger_ofList', 'parseRational_ofList', 'decodeNat_number_ofList']}
            require(required <= {r['name'] for r in records}, 'Accepted Chars public equations are incomplete.')
            require(owner['object']['sha256'] == 'af720770a2f637e468c1f153b76891e0c6efedd627d3d144ca20024e638a1c7d',
                    'Accepted Chars object identity differs.')
        else:
            require(module in REUSED_OBJECTS and owner['object']['sha256'] == REUSED_OBJECTS[module],
                    'Only one of the three exact prior accepted owners may be reused.')
            spec = next(s for s in MODULES if s['module'] == module)
            public = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)',
                                source_copy.read_text(), re.M)
            required = [spec['namespace'] + '.' + n for n in public]
            require(len(public) == len(set(public)) == spec['public_count'] == owner['owned_count'] and
                    owner['required_owned_names'] == required and spec['required_final_name'] in required and
                    set(required) <= {r['name'] for r in records},
                    'Prior accepted owner public/full declaration inventory differs.')
        for dependency in project_closure(module) - {module}:
            require(dependency in state['dependency_objects'], f'Accepted dependency not yet present: {dependency}')
            expected = state['dependency_objects'][dependency]['sha256']
            row = receipt['dependency_objects'][dependency]
            require(row['sha256'] == expected and
                    row['source_sha256'] == SOURCES[dependency]['source_sha256'],
                    f'Accepted owner dependency binding mismatch: {dependency}')
            bind(row['path'], expected)
            bind(row['isolated_path'], expected)
        copy_dependency(module, object_path, owner['object']['sha256'],
                        'Accepted owner entry with normal/replay/full-owned logs and complete inventory revalidated')
        state['dependency_receipts'][module] = {
            **record_file(receipt_path), 'owner_status': owner['status'], 'owner_accepted': True,
            'aggregate_status': receipt['status'], 'aggregate_accepted': receipt['accepted'],
            'owned_count': len(records), 'source_origin': owner['source_origin'],
        }

    def verify_reproduced_original_acceptance():
        # Bind the original local acceptance packages, not the failed Decoded owner.
        fuel_dir = ROOT / 'docs/verification/20261126-p2-5-continuation/fuel_stability'
        fuel_receipt_path = bind(fuel_dir / 'verification.json', FUEL_RECEIPT_SHA)
        fuel_receipt = json.loads(fuel_receipt_path.read_text())
        require(fuel_receipt['module'] == FUEL and fuel_receipt['status'] == 'passed' and
                fuel_receipt['source_sha256'] == SOURCES[FUEL]['source_sha256'] and
                fuel_receipt['object_sha256'] == REPRODUCED_OBJECTS[FUEL] and
                fuel_receipt['inputs_unchanged'] is True and
                fuel_receipt['full_owned_declarations_all_safe_total_nonaxiom'] is True,
                'Original Fuel acceptance receipt is incomplete or mismatched.')
        require([s['label'] for s in fuel_receipt['stages']] == ['strict-compile', 'replay', 'full-owned-audit'],
                'Fuel acceptance stages differ.')
        for row in fuel_receipt['stages']:
            stage_log(row, fuel_dir / Path(row['log']).name)
        fuel_records, _, _ = read_audit(fuel_dir / 'full-owned-audit.log', FUEL)
        require(len(fuel_records) == fuel_receipt['full_owned_declaration_count'], 'Fuel owned-count mismatch.')
        direct_dir = ROOT / 'docs/source-only/20261126-p2-5-cell00-segmented'
        direct_receipt_path = bind(direct_dir / 'RESULT.json', DIRECT_RECEIPT_SHA)
        direct_receipt = json.loads(direct_receipt_path.read_text())
        entries = [r for r in direct_receipt['modules'] if r['module'] == DIRECT]
        require(len(entries) == 1, 'DirectParse acceptance owner is absent or duplicated.')
        entry = entries[0]
        require(entry['accepted_local_strict_replay_full_owned'] is True and
                entry['source_sha256'] == SOURCES[DIRECT]['source_sha256'] and
                entry['object_sha256'] == REPRODUCED_OBJECTS[DIRECT], 'DirectParse original acceptance mismatch.')
        require([s['mode'] for s in entry['stages']] == ['normal', 'kernel', 'audit'], 'DirectParse acceptance stages differ.')
        for stage in entry['stages']:
            path = bind(direct_dir / stage['receipt'], stage['receipt_sha256'])
            row = json.loads(path.read_text())
            require(row['module'] == DIRECT and row['mode'] == stage['mode'] and row['exit_code'] == 0 and
                    row['termination_reason'] is None and row['source_sha256'] == SOURCES[DIRECT]['source_sha256'] and
                    row['object_sha256'] == REPRODUCED_OBJECTS[DIRECT], 'DirectParse original stage binding mismatch.')
            bind(path.with_suffix('.log'), row['log_sha256'])
            if stage['mode'] == 'audit':
                require(row['audit_passed'] and row['inventory_complete'] and row['all_safe_total_nonaxiom'],
                        'DirectParse original full-owned audit was not accepted.')
                records, _, _ = read_audit(path.with_suffix('.log'), DIRECT)
                require(len(records) == row['full_owned_count'] == entry['declaration_count'], 'DirectParse inventory count mismatch.')
                bind(path.with_suffix('.lean'), row['audit_source_sha256'])
        state['original_reproduced_acceptance'] = {
            FUEL: record_file(fuel_receipt_path), DIRECT: record_file(direct_receipt_path)}

    def run_stage(owner, label, command, log):
        require(owner['module'] == TARGET, 'Only repaired FieldDecode may run compiler gates.')
        check_frozen()
        start = time.monotonic()
        row = {'command': command, 'started_utc': now(), 'status': 'RUNNING', 'log': str(log)}
        owner['stages'][label] = row
        write()
        print('P25_FIELD_DECODE_STAGE_START', owner['module'], label, flush=True)
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
        write()
        print('P25_FIELD_DECODE_STAGE_RESULT', owner['module'], label,
              json.dumps({k: row[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}), flush=True)
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=owner['module'], failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{owner["module"]} {label} failed with exit {code}.')
        check_frozen()

    write()
    try:
        prior_path = bind(PRIOR / 'RESULT.json', PRIOR_RESULT_SHA)
        prior_run = json.loads(prior_path.read_text())
        require(prior_run['schema'] == 'p25-cell00-field-decode-strict-v1' and
                prior_run['accepted'] is False and prior_run['status'] == 'MODULE_STAGE_FAILED' and
                prior_run['failed_module'] == TARGET and prior_run['failed_stage'] == 'normal' and
                set(prior_run['modules']) == {s['module'] for s in MODULES} and
                prior_run['dependency_modules_compiled'] == [] and prior_run['failed_owner_object_used'] is False and
                re.fullmatch(r'[0-9a-f]{40}', prior_run['publication_commit']),
                'Expected exact failed attempt001 aggregate with three accepted owners.')
        failed_owner = prior_run['modules'][TARGET]
        require(failed_owner['accepted'] is False and failed_owner['status'] == 'NORMAL_FAILED' and
                failed_owner['source_origin']['sha256'] == PRIOR_FAILED_SOURCE_SHA and
                failed_owner['source_origin']['commit'] == prior_run['publication_commit'] and
                failed_owner['source_origin']['path'] == SOURCES[TARGET]['path'] and
                failed_owner['stages']['normal']['exit_code'] != 0 and
                failed_owner['stages']['normal']['log_sha256'] == PRIOR_FAILED_NORMAL_LOG_SHA and
                failed_owner['stages']['normal']['log_bytes'] == 58970,
                'Prior failed FieldDecode evidence differs; no same-name owner fallback is permitted.')
        old_failed_source = artifact(failed_owner['source_copy'], PRIOR_FAILED_SOURCE_SHA)
        old_failed_log = bind(failed_owner['stages']['normal']['log'], PRIOR_FAILED_NORMAL_LOG_SHA)
        require(old_failed_log.stat().st_size == 58970, 'Prior full diagnostic log is incomplete.')
        for module in REUSED_OBJECTS:
            owner = prior_run['modules'][module]
            require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
                    owner['object']['sha256'] == REUSED_OBJECTS[module],
                    f'Prior owner is not the exact accepted reusable object: {module}')
        state['prior_attempt'] = {
            **record_file(prior_path), 'status': prior_run['status'], 'accepted': False,
            'publication_commit': prior_run['publication_commit'], 'failed_module': TARGET,
            'failed_source_copy': record_file(old_failed_source), 'full_failed_normal_log': record_file(old_failed_log),
            'failed_owner_reused': False,
        }
        # Missing/pending future owners fail here before compilation or checkout.
        future = {}
        for path, module, receipt_sha in [(PAYLOAD_RESULT, PAYLOAD, PAYLOAD_RESULT_SHA),
                                          (CHARS_RESULT, CHARS, CHARS_RESULT_SHA)]:
            receipt = json.loads(bind(path, receipt_sha).read_text())
            owner = receipt['modules'][module]
            require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                    f'Preflight requires accepted {module}; no failed/pending object fallback.')
            require(re.fullmatch(r'[0-9a-f]{40}', receipt['publication_commit']), 'Invalid dependency publication commit.')
            future[module] = receipt
        allowed_heads = {publication, prior_run['publication_commit'], *[r['publication_commit'] for r in future.values()]}
        require(git('rev-parse', 'HEAD') in allowed_heads, 'P3 HEAD is neither the dependency publication nor target publication.')
        if git('rev-parse', 'HEAD') != publication:
            with (OUT / 'PUBLICATION.log').open('wb') as stream:
                subprocess.run(['git', 'fetch', '--no-tags', 'origin', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
                subprocess.run(['git', 'checkout', '--detach', publication], cwd=ROOT,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=True)
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Publication checkout mismatch/dirty.')
        state['publication_checked_out'] = publication
        old_path = bind(BASE / 'RESULT.json', OLD_RESULT_SHA)
        old = json.loads(old_path.read_text())
        snapshot = old['normal_snapshot_before']
        require(snapshot['mathlib_pin'] == MATHLIB_PIN and
                git('rev-parse', 'HEAD', cwd=Path(snapshot['mathlib_path'])) == MATHLIB_PIN, 'Mathlib pin mismatch.')
        for binary in [LEAN, CHECKER]:
            bind(binary, snapshot['files'][str(binary)]['sha256'])
        state['runtime'] = {'lean': record_file(LEAN), 'leanchecker': record_file(CHECKER),
                            'mathlib_pin': MATHLIB_PIN, 'mathlib_path': snapshot['mathlib_path']}
        require(prior_run['runtime'] == state['runtime'], 'Prior accepted owners used a different runtime.')
        state['canonical_dependency_receipt_source'] = record_file(old_path)
        state['prior_charparse_status'] = old['status']
        src, lib, audit = OUT / 'src', OUT / 'lib', OUT / 'audit'
        for directory in [src / 'ImbalancedChen', lib / 'ImbalancedChen', audit]:
            directory.mkdir(parents=True)
        tails = old['approved_LEAN_PATH'].split(':')[1:]
        require(tails and all(p and Path(p).is_dir() and
                             Path(p).resolve().is_relative_to(Path('/mathlib').resolve()) and
                             not (Path(p) / 'ImbalancedChen').exists() for p in tails),
                'Pinned Mathlib paths missing or contain project fallback modules.')
        env = dict(os.environ)
        env.pop('LEAN_SRC_PATH', None)
        env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
        env['LEAN_PATH'] = ':'.join([str(lib), *tails])
        env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')
        state.update(approved_LEAN_PATH=env['LEAN_PATH'], isolated_library=str(lib), isolated_source_root=str(src))

        # Bind all project source hashes and verify the explicit import graph.
        for module, spec in SOURCES.items():
            path = bind(ROOT / spec['path'], spec['source_sha256'])
            published = subprocess.check_output(['git', 'show', f'{publication}:{spec["path"]}'], cwd=ROOT, timeout=120)
            require(published == path.read_bytes(), f'Project source differs from exact publication: {module}')
            imports = [name for line in re.findall(r'^import\s+([^\n]+)$', path.read_text(), re.M)
                       for name in line.split() if name.startswith('ImbalancedChen.')]
            require(imports == spec['project_imports'], f'Frozen source import graph mismatch: {module}')
        state['source_graph'] = SOURCES
        state['expected_project_imports_by_owner'] = {s['module']: sorted(project_closure(s['module'])) for s in MODULES}
        # The prior failed target's published file is the sole deliberately
        # superseded source. Its immutable copied preimage remains bound above.
        superseded = ROOT / SOURCES[TARGET]['path']
        require(prior_run['frozen_inputs'].get(str(superseded)) == PRIOR_FAILED_SOURCE_SHA,
                'The old frozen source map does not contain the expected failed target.')
        for path, h in prior_run['frozen_inputs'].items():
            if Path(path) == superseded:
                continue
            require(Path(path) != PRIOR / 'lib' / (TARGET.replace('.', '/') + '.olean'),
                    'A failed target object unexpectedly appears in the prior_run frozen proof inputs.')
            bind(path, h)
        state['superseded_failed_source'] = {
            'path': str(superseded), 'old_sha256': PRIOR_FAILED_SOURCE_SHA,
            'new_sha256': SOURCES[TARGET]['source_sha256'],
            'preserved_old_copy': record_file(old_failed_source),
            'reason': 'Only the failed owner source changes; all accepted owner inputs remain exact.',
        }

        for module, expected_object in BASE_OBJECTS.items():
            prior = old['dependency_objects'][module]
            require(prior['sha256'] == expected_object, f'Canonical dependency hash mismatch: {module}')
            receipt_path = bind(prior['receipt'], prior['receipt_sha256'])
            receipt = json.loads(receipt_path.read_text())
            require(receipt['accepted'] is True and receipt['module'] == module, f'Base dependency is not accepted: {module}')
            if module.endswith('P2Saving16StringCharBinding00'):
                require(receipt['primary_object_sha256'] == expected_object and
                        receipt['candidate_sha256'] == SOURCES[module]['source_sha256'] and
                        receipt['full_owned_audit_accepted'] is True, 'Raw character binding acceptance mismatch.')
                for label in ['normal', 'replay', 'audit']:
                    stage_log(receipt[label])
                for relative, h in receipt['artifacts'].items():
                    bind(receipt_path.parent / relative, h)
                bind(receipt['audit_source'], receipt['audit_source_sha256'])
            else:
                require(receipt['object_sha256'] == expected_object and
                        receipt['source_sha256'] == SOURCES[module]['source_sha256'],
                        f'Base accepted source/object pair mismatch: {module}')
                for label in ['replay', 'audit']:
                    stage_log(receipt[label])
                for relative, h in receipt['artifacts'].items():
                    bind(ROOT / relative, h)
            copy_dependency(module, prior['path'], expected_object, 'Exact canonical accepted dependency receipt/object reused')
            state['dependency_receipts'][module] = record_file(receipt_path)

        files_path = bind(ROOT / PACKAGE / 'TYPED_PAYLOAD_FILES.json', PAYLOAD_FILES_SHA)
        payload_files = json.loads(files_path.read_text())
        expected_payload = sorted(payload_files['expected_owned_names'])
        require(payload_files['module'] == PAYLOAD and payload_files['expected_owned_declarations'] ==
                len(expected_payload) == len(set(expected_payload)) == 544, 'Expected payload inventory differs.')
        require(payload_files['original_input_sha256'] == INPUT_SHA, 'Payload original input hash mismatch.')
        for entry in payload_files['files']:
            bind(ROOT / entry['path'], entry['sha256'])
        audit_template_path = bind(ROOT / payload_files['audit_file'])
        audit_template = audit_template_path.read_text()
        state['payload_files_manifest'] = record_file(files_path)
        state['audit_template'] = record_file(audit_template_path)
        verify_component(PAYLOAD_RESULT, future[PAYLOAD], PAYLOAD)
        verify_component(CHARS_RESULT, future[CHARS], CHARS)

        verify_reproduced_original_acceptance()
        reproduced_path = bind(REPRODUCED / 'RESULT.json')
        reproduced = json.loads(reproduced_path.read_text())
        require(reproduced['module'] == 'ImbalancedChen.P2Saving16Cell00Decoded', 'Unexpected reproduction container owner.')
        state['reproduction_container'] = {
            **record_file(reproduced_path), 'container_status': reproduced['status'],
            'container_owner_used': False, 'only_exact_accepted_reproductions_used': True,
        }
        for module, expected_object in REPRODUCED_OBJECTS.items():
            rows = [r for r in reproduced['reproduced_accepted_objects'] if r['module'] == module]
            require(len(rows) == 1, f'Accepted reproduced module missing/duplicated: {module}')
            row = rows[0]
            require(row['exact_accepted_object_match'] is True and row['object_sha256'] == expected_object and
                    row['source_sha256'] == SOURCES[module]['source_sha256'], f'Reproduced object binding mismatch: {module}')
            dependency = reproduced['dependencies'][module]
            require(dependency['sha256'] == expected_object and dependency['source_sha256'] == SOURCES[module]['source_sha256'],
                    f'Reproduction dependency metadata mismatch: {module}')
            object_path = REPRODUCED / 'lib' / (module.replace('.', '/') + '.olean')
            require(Path(dependency['path']) == object_path, f'Unexpected reproduction object location: {module}')
            bind(REPRODUCED / 'src' / (module.replace('.', '/') + '.lean'), SOURCES[module]['source_sha256'])
            log = bind(REPRODUCED / (module.split('.')[-1] + '-REPRODUCE.log'), row['log_sha256'])
            copy_dependency(module, object_path, expected_object, 'Byte-identical reproduction of separately accepted strict/replay/full-owned object')
            state['dependency_receipts'][module] = {'reproduction_receipt': record_file(reproduced_path),
                                                  'reproduction_log': record_file(log), 'entry': row}
        needed = set().union(*(project_closure(s['module']) for s in MODULES)) - {s['module'] for s in MODULES}
        require(set(state['dependency_objects']) == needed, 'Isolated dependency set differs from actual source graph.')
        require(len(list((lib / 'ImbalancedChen').glob('*.olean'))) == len(needed) == 8, 'Unexpected dependency object in isolated library.')
        require(set(prior_run['dependency_objects']) == needed,
                'Prior aggregate base-dependency inventory differs from the reviewed source graph.')
        for module, row in prior_run['dependency_objects'].items():
            require(row['source_sha256'] == SOURCES[module]['source_sha256'] and
                    row['sha256'] == state['dependency_objects'][module]['sha256'],
                    f'Prior accepted owner dependency identity differs in the fresh root: {module}')
            bind(row['path'], row['sha256'])
            bind(row['isolated_path'], row['sha256'])
        for module in REUSED_OBJECTS:
            verify_component(prior_path, prior_run, module)
            state['reused_owner_objects'][module] = state['dependency_objects'].pop(module)
            # Preserve the original publication, stage logs, paths, timestamps
            # and owner status exactly. The new aggregate is a selection view.
            state['modules'][module] = json.loads(json.dumps(prior_run['modules'][module]))
            state['owner_receipt_sources'][module] = {
                **record_file(prior_path), 'owner_module': module,
                'owner_source_origin': prior_run['modules'][module]['source_origin'],
                'owner_object_sha256': REUSED_OBJECTS[module],
                'aggregate_status': prior_run['status'], 'aggregate_accepted': False,
                'owner_accepted': True,
            }
        existing = needed | set(REUSED_OBJECTS)
        require(set(state['dependency_objects']) == needed and len(needed) == 8 and
                set(state['reused_owner_objects']) == set(REUSED_OBJECTS) and
                len(list((lib / 'ImbalancedChen').glob('*.olean'))) == len(existing) == 11 and
                not (lib / (TARGET.replace('.', '/') + '.olean')).exists(),
                'The fresh library must contain exactly eight base dependencies and three prior accepted owners.')
        state.update(reused_owners_accepted=True, certified_reader_ast_binding_proved=True,
                     reused_owner_receipt_policy='Exact original owner entries, publication identities and complete stage receipts retained')

        for spec in [MODULES[-1]]:
            module = spec['module']
            source_path = ROOT / SOURCES[module]['path']
            source_copy = src / (module.replace('.', '/') + '.lean')
            source_copy.write_bytes(source_path.read_bytes())
            bind(source_copy, SOURCES[module]['source_sha256'])
            public = re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)', source_path.read_text(), re.M)
            require(len(public) == len(set(public)) == spec['public_count'], f'Frozen public declaration count mismatch: {module}')
            required = [spec['namespace'] + '.' + n for n in public]
            require(spec['required_final_name'] in required, f'Required final declaration missing: {module}')
            audit_path = audit / (module.split('.')[-1] + '.lean')
            audit_path.write_text(audit_template.replace(PAYLOAD, module))
            bind(audit_path)
            state['modules'][module] = {
                'module': module, 'status': 'PENDING', 'accepted': False,
                'source_origin': {'commit': publication, 'path': SOURCES[module]['path'],
                                  'sha256': SOURCES[module]['source_sha256']},
                'source_copy': record_file(source_copy), 'audit_source': record_file(audit_path),
                'required_owned_names': required, 'stages': {},
            }
        state.update(status='VERIFYING_COMPOSITION_OWNERS', frozen_inputs=dict(frozen))
        check_frozen()
        write()

        for spec in [MODULES[-1]]:
            module = spec['module']
            owner = state['modules'][module]
            owner['status'] = 'RUNNING'
            directory = OUT / module.split('.')[-1]
            directory.mkdir()
            source_path = src / (module.replace('.', '/') + '.lean')
            object_path = lib / (module.replace('.', '/') + '.olean')
            audit_path = audit / (module.split('.')[-1] + '.lean')
            require(not object_path.exists(), f'Unexpected existing target object: {module}')
            commands = [
                ('normal', [str(LEAN), *FLAGS, '--root=' + str(src), '-o', str(object_path), str(source_path)]),
                ('replay', [str(CHECKER), '--verbose', module]),
                ('audit', [str(LEAN), *FLAGS, '--root=' + str(audit), str(audit_path)]),
            ]
            for label, command in commands:
                run_stage(owner, label, command, directory / (label.upper() + '.log'))
                if label == 'normal':
                    require(object_path.is_file(), f'Normal compile produced no object: {module}')
                    bind(object_path)
                    owner['object'] = record_file(object_path)
                    state['frozen_inputs'] = dict(frozen)
                    write()
            records, inventory, imports = read_audit(directory / 'AUDIT.log', module)
            require(set(owner['required_owned_names']) <= {r['name'] for r in records}, f'Public theorem missing from full owned audit: {module}')
            declarations_path = directory / 'OWNED_DECLARATIONS.json'
            declarations_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n')
            inventory_path = directory / 'OWNED_INVENTORY.json'
            inventory_path.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + '\n')
            owner.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True,
                         owned_count=len(records), owned_declarations=records, actual_project_closure=imports,
                         declarations=record_file(declarations_path), inventory=record_file(inventory_path), ended_utc=now())
            check_frozen()
            write()
            print('P25_FIELD_DECODE_OWNER_ACCEPTED', module, len(records), owner['object']['sha256'], flush=True)
        require(all(o['accepted'] for o in state['modules'].values()), 'Not all four composition owners accepted.')
        require(set(state['modules']) == {s['module'] for s in MODULES} and
                state['module_order'] == [TARGET] and state['reused_owners_recompiled'] == [] and
                state['dependency_modules_compiled'] == [] and state['failed_same_name_field_object_used'] is False,
                'Incremental target/reuse policy changed.')
        require(all(state['modules'][m] == prior_run['modules'][m] for m in REUSED_OBJECTS),
                'A reused owner entry was relabeled or modified.')
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Publication changed during verification.')
        check_frozen()
        state.update(status='FULL_AST_BINDING_AND_RAW_ROOT_TYPED_DECODE_ACCEPTED', accepted=True,
                     certified_reader_ast_binding_proved=True, raw_root_typed_decode_proved=True, ended_utc=now())
        write()
        print('P25_FIELD_DECODE_RESULT', json.dumps({
            'status': state['status'], 'accepted': True,
            'owned_counts': {m: o['owned_count'] for m, o in state['modules'].items()},
            'original_string_typed_decode_proved': False, 'geometric_jensen_binding_proved': False,
            'Q96_proved': False, 'P2_5_proved': False,
            'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json'),
        }, sort_keys=True), flush=True)
    except BaseException as exc:
        if state['status'] != 'MODULE_STAGE_FAILED':
            state['status'] = 'FAILED'
        state.update(accepted=False, error=f'{type(exc).__name__}: {exc}', ended_utc=now())
        (OUT / 'RUNNER_EXCEPTION.log').write_text(traceback.format_exc())
        state['exception_log'] = record_file(OUT / 'RUNNER_EXCEPTION.log')
        write()
        print('P25_FIELD_DECODE_FAILED', json.dumps({
            'status': state['status'], 'error': state['error'][:1800],
            'result_path': str(OUT / 'RESULT.json'), 'result_sha256': digest(OUT / 'RESULT.json'),
        }, sort_keys=True), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
