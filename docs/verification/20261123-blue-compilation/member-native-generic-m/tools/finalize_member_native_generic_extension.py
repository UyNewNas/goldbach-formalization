#!/usr/bin/env python3
"""Seal current native generic-M verification and reviewable evidence."""
from pathlib import Path
import datetime
import difflib
import fcntl
import hashlib
import json
import subprocess
import time

ROOT = Path('/workspace/blue-member-native-generic-extension-validation')
CANDIDATE = Path('/workspace/blue-member-native-generic-extension-candidate')
DEST = 'docs/verification/20261123-blue-compilation/member-native-generic-m'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    lock = (ROOT / 'controller.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    validation_path = ROOT / 'validation/VALIDATION_RESULTS.json'
    validation = json.loads(validation_path.read_text())
    assert validation['kernel']['exit_code'] == validation['types_and_axioms']['exit_code'] == 0
    adoption = json.loads((ROOT / 'ADOPTION_RECEIPT.json').read_text())
    manifest = json.loads((CANDIDATE / 'OVERLAY_MANIFEST.json').read_text())
    before_context = json.loads((ROOT / 'BEFORE_CONTEXT.json').read_text())
    snapshots = validation['source_and_five_outputs_per_module']
    for path, expected in snapshots.items():
        actual = Path(path)
        assert actual.stat().st_size == expected['bytes'] and sha(actual) == expected['sha256']
    unchanged = {}
    for section in ['old_cap100_providers', 'four_external_suppliers', 'configuration_and_pins']:
        for label, record in before_context[section].items():
            path = Path(record['path'])
            assert sha(path) == record['sha256']
            unchanged[label] = record
    save(ROOT / 'UNCHANGED_BOUNDARIES_AFTER.json', unchanged)
    public_names = {row['qualified_public_name'] for row in manifest['declarations'] if row['visibility'] == 'public'}
    actual_extension_names = {row['name'] for row in validation['declarations'] if row['module'] == manifest['extension']['module']}
    assert public_names <= actual_extension_names
    for row in manifest['declarations']:
        if row['visibility'] == 'private':
            assert any(name.startswith('_private.') and name.endswith('.' + row['name']) for name in actual_extension_names)
    for record in adoption['files'][1:]:
        short = record['module'].split('.')[-1]
        old = (ROOT / (short + '.before.lean')).read_bytes()
        new = Path(record['path']).read_bytes()
        assert new == manifest['consumer']['new_import_prefix'].encode() + old
        (ROOT / (short + '.patch')).write_text(''.join(difflib.unified_diff(
            old.decode().splitlines(keepends=True), new.decode().splitlines(keepends=True),
            fromfile='a/' + record['exact_upstream_source']['install_path'],
            tofile='b/' + record['exact_upstream_source']['install_path'])))

    guard_log = Path('/workspace/blue-build-tools/runtime-evidence/compiler-commands.jsonl')
    cmd = ['python3', '/workspace/blue-build-tools/run_guarded.py', 'lake', '--no-build',
           'build', *['+' + row['module'] + ':olean' for row in adoption['files']]]
    stock = {'command': cmd, 'cwd': '/workspace/blue-member-build',
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'guard_log_start_bytes': guard_log.stat().st_size}
    save(ROOT / 'FINAL_STOCK_PROCESS.json', stock)
    started = time.monotonic()
    with (ROOT / 'final-stock.log').open('wb') as output:
        result = subprocess.run(cmd, cwd=stock['cwd'], stdout=output, stderr=subprocess.STDOUT)
    raw = guard_log.read_bytes()[stock['guard_log_start_bytes']:]
    commands = [json.loads(line) for line in raw.splitlines()]
    source_calls = [r for r in commands if r['tool'] == 'lean' and
                    ('--stdin' in r['input_args'] or any(a.endswith('.lean') for a in r['input_args']))]
    stock.update(exit_code=result.returncode, elapsed_seconds=time.monotonic() - started,
                 finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 source_compiler_calls=len(source_calls), guard_log_end_bytes=guard_log.stat().st_size,
                 log_sha256=sha(ROOT / 'final-stock.log'))
    save(ROOT / 'FINAL_STOCK_PROCESS.json', stock)
    (ROOT / 'FINAL_STOCK_GUARD_COMMANDS.jsonl').write_bytes(raw)
    assert result.returncode == 0 and not source_calls
    for path, expected in snapshots.items():
        assert sha(Path(path)) == expected['sha256']
    normal = json.loads((ROOT / 'NORMAL_PROCESS.json').read_text())
    complete_raw = guard_log.read_bytes()[normal['guard_log_start_bytes']:stock['guard_log_end_bytes']]
    all_commands = [json.loads(line) for line in complete_raw.splitlines()]
    source_commands = [r for r in all_commands if r['tool'] == 'lean' and
                       ('--stdin' in r['input_args'] or any(a.endswith('.lean') for a in r['input_args']))]
    assert len(source_commands) == 4
    assert all(all(flag in r['command'] for flag in ['-t0', '-j2', '-M12288']) for r in source_commands)
    (ROOT / 'ALL_GUARDED_COMMANDS.jsonl').write_bytes(complete_raw)
    selection_path = Path('/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json')
    overlay = {'schema': 'member_native_existing_generic_M_exact_source_selection_overrides_v1',
               'base_member_selection': str(selection_path), 'base_member_selection_sha256': sha(selection_path),
               'native_base_pin_retained': manifest['native_base_commit_retained'],
               'mathlib_pin_retained': manifest['mathlib_revision_retained'],
               'lean_toolchain_retained': manifest['lean_toolchain_retained'],
               'published_source_commit': manifest['published_commit'],
               'new_extension': {'module': manifest['extension']['module'], 'source_sha256': manifest['extension']['sha256'],
                                 'install_path': manifest['extension']['module'].replace('.', '/') + '.lean',
                                 'installed_path': '/workspace/blue-member-build/.lake/packages/goldbach/' + manifest['extension']['module'].replace('.', '/') + '.lean',
                                 'imports': manifest['extension']['imports'], 'byte_exact_published_declaration_blocks': manifest['declarations'],
                                 'new_public_source_blocks': 11, 'private_source_blocks': 7,
                                 'private_source_blocks_include_six_existing_helpers': True,
                                 'local_owned_declarations_including_generated': validation['declaration_counts'][manifest['extension']['module']]},
               'native_consumer_import_only_overrides': adoption['files'][1:],
               'old_providers_and_four_external_suppliers_byte_unchanged': True,
               'no_mathematical_definition_or_assumption_changes': True,
               'local_validation_results_sha256': sha(validation_path),
               'data_inputs': [],
               'historical_acceptance_limit': manifest['acceptance_limit']}
    save(ROOT / 'NATIVE_SOURCE_SELECTION_OVERRIDES.json', overlay)
    summary = {'schema': 'member_native_existing_generic_M_extension_local_acceptance_v1',
               'result': 'PASS_NORMAL_BUILD_NAMED_KERNEL_FULL_OWNED_TYPES_STANDARD_AXIOMS_AND_ZERO_SOURCE_STOCK',
               'diagnosis': 'Current source selection omitted the already-published arbitrary-M interface; both exact consumers failed on its missing identifier. No new Buchstab theorem was invented and no substantive manuscript gap identified.',
               'normal_build': normal, 'named_kernel': validation['kernel'],
               'full_owned_types_and_axioms': validation['types_and_axioms'],
               'owned_declaration_counts': validation['declaration_counts'],
               'total_owned_declarations': sum(validation['declaration_counts'].values()),
               'observed_axioms': validation['observed_axioms'],
               'copied_source_declaration_blocks': 18, 'copied_public_source_blocks': 11,
               'copied_private_source_blocks': 7, 'copied_private_blocks_include_six_old_helpers': True,
               'new_mathematical_definitions': [],
               'copied_published_headers_and_proof_bodies_byte_exact': True,
               'omega_original_bytes_preserved': 4333, 'nonunit_original_bytes_preserved': 4282,
               'three_sources_and_fifteen_outputs_unchanged_through_kernel_audit_and_stock': True,
               'old_providers_four_external_suppliers_and_all_pins_byte_unchanged': True,
               'source_compiler_guard': {'memory_mib': 12288, 'trust': 0, 'threads': 2,
                                         'actual_source_invocations_including_audit': len(source_commands)},
               'native_normal_options': 'Original native Lake options retained; no heartbeat/recursion option was raised for these proof sources.',
               'kernel_scope': 'Exact three named modules relative to existing imports; no fresh all-import kernel replay claim.',
               'kernel_memory_flag': 'No -M source-compiler flag claimed for leanchecker.',
               'final_stock': stock, 'validation_results_sha256': sha(validation_path),
               'scope_limitations': [manifest['acceptance_limit'],
                                     'Historical 4151-source acceptance is provenance, not current local object acceptance; this new composition was compiled and audited locally.',
                                     'P6 sources/cache, Member project proof sources, frozen archives and dependency pins were not edited.']}
    save(ROOT / 'ACCEPTANCE_SUMMARY.json', summary)
    files = []
    def add(path, relative):
        files.append({'source': str(path), 'destination': DEST + '/' + relative,
                      'sha256': sha(path), 'bytes': path.stat().st_size})
    for path in sorted(ROOT.rglob('*')):
        if path.is_file() and path.name not in ['PUBLISH_FILES.json', 'controller.lock']:
            add(path, 'local/' + str(path.relative_to(ROOT)))
    for path in sorted(CANDIDATE.rglob('*')):
        if path.is_file():
            add(path, 'published-source-candidate/' + str(path.relative_to(CANDIDATE)))
    for name in ['adopt_member_native_generic_extension.py', 'validate_member_native_generic_extension.py',
                 'finalize_member_native_generic_extension.py']:
        add(Path('/workspace/blue-build-tools') / name, 'tools/' + name)
    assert len({r['destination'] for r in files}) == len(files)
    save(ROOT / 'PUBLISH_FILES.json', {'schema': 'reviewable_publish_files_v1',
                                     'source_root': str(ROOT), 'destination_root': DEST, 'files': files})
    print(json.dumps({'publish_list': str(ROOT / 'PUBLISH_FILES.json'),
                      'publish_list_sha256': sha(ROOT / 'PUBLISH_FILES.json'),
                      'files': len(files), 'bytes': sum(r['bytes'] for r in files),
                      'validation_results_sha256': sha(validation_path),
                      'acceptance_summary_sha256': sha(ROOT / 'ACCEPTANCE_SUMMARY.json'),
                      'final_stock': stock}))


if __name__ == '__main__':
    main()
