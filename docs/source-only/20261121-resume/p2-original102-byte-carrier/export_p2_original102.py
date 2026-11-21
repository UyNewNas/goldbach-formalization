"""UNEXECUTED P2 original102 byte-carrier source proposal; no proof admission.

The three R4 reference files remain byte-identical. This wrapper supplies P2's
producer profile and finite selection. Only ZIP metadata may use bounded raw
deflate; object payloads use the original stored-member reader. No nested tar,
toolchain, object import, subprocess, collector, fixture or proof code is run.
ROOT must independently review and replace every pending execution control.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import struct
import sys
import zlib

import range_transport as T

HERE = Path(__file__).resolve().parent
REPO = 'UyNewNas/goldbach-formalization'
RUN = 43670444098
HEAD = 'b125727f46472dda7cc0c03b068e50788b1071e8'
BRANCH = 'ci/p2-integer-mass-r24-20261115'
SOURCE = '1d5867005258cfbb02f9e860b594d7f2ed552445'
SIX = ['olean', 'olean.private', 'olean.server', 'ilean', 'ir', 'ir.sig']
CP_NAMES = ['CHECKPOINT.json', 'RAW_FILES.jsonl', 'SNAPSHOT_ACQUISITION.json']
ABI_NAMES = ['RETAINED_OBJECTS.json', 'CACHE_CHECKPOINT_RETENTION.json',
             'CHECKPOINT_SUMMARY.json', 'CHECKPOINT_COLLECTOR_INPUT.json',
             'checkpoint-collection.log']


def bind_control():
    control = T.load(HERE / 'EXPORT_CONTROL.PENDING.json')
    T.check(control.get('driverReady') is True and
            control.get('execute') == 'ALLOW_INDEPENDENTLY_REVIEWED_P2_ORIGINAL102_DATA_ONLY',
            'PENDING_ROOT_P2_SOURCE_TREE_CALLER_AND_INDEPENDENT_AUTHORIZATION')
    T.check(all(control.get(k) is not None for k in
                ['independent_source_review', 'actual_tree_review', 'fresh_dispatch_review',
                 'branch_CAS_duplicate_queue_review']), 'ROOT_REVIEW_INPUTS_MISSING')
    T.check(os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux' and
            os.environ.get('GITHUB_REPOSITORY') == REPO and
            os.environ.get('GITHUB_EVENT_NAME') == control.get('event_name') and
            os.environ.get('GITHUB_REF') == control.get('ref'), 'REVIEWED_GITHUB_CALLER_REQUIRED')
    raw = (HERE / 'PUBLIC_SELECTION.json').read_bytes()
    T.check(T.digest(raw) == control.get('selection_sha256'), 'PUBLIC_SELECTION_PIN_CHANGED')
    source_names = {'export_p2_original102.py', 'export_r4_five.py',
                    'range_transport.py', 'original_archive_reader.py'}
    T.check(set(control.get('source_sha256', {})) == source_names, 'EXACT_SOURCE_SET_REQUIRED')
    for name, expected in control['source_sha256'].items():
        T.check(T.digest((HERE / name).read_bytes()) == expected, 'EXPORT_SOURCE_PIN_CHANGED')
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
    present = {p.relative_to(workspace).as_posix() for ext in ['*.yml', '*.yaml']
               for p in (workspace / '.github/workflows').glob(ext)}
    rows = control.get('reviewed_workflows', [])
    reviewed = {r['path']: r for r in rows}
    T.check(bool(reviewed) and len(reviewed) == len(rows) and set(reviewed) == present,
            'ROOT_COMPLETE_ACTUAL_WORKFLOW_PROJECTION_REQUIRED')
    for name, row in reviewed.items():
        T.safe_member(name)
        body = (workspace / name).read_bytes()
        T.check(len(body) == row['bytes'] and T.digest(body) == row['sha256'],
                'ACTUAL_WORKFLOW_BYTES_CHANGED')
    manifest = json.loads(raw)
    T.check(manifest['schema'] == 'p2-original102-public-byte-selection-v1' and
            manifest['producer'] == dict(repository=REPO, run=RUN, job=132679068390,
                head=HEAD, branch=BRANCH, source_commit=SOURCE, run_attempt='1'),
            'ORIGINAL_PRODUCER_CHANGED')
    T.check(len(manifest['modules']) == 102 and
            len({r['module'] for r in manifest['modules']}) == 102 and
            manifest['six_facets'] == SIX, 'EXACT_ORIGINAL102_SET_REQUIRED')
    for row in manifest['modules']:
        T.check(re.fullmatch(r'ImbalancedChen\.[A-Za-z0-9_.]+', row['module']) is not None,
                'UNEXPECTED_MODULE_NAME')
        T.check(row['olean']['relative_path'] ==
                '.lake/build/lib/lean/' + row['module'].replace('.', '/') + '.olean',
                'ORIGINAL_OLEAN_RELATIVE_PATH_CHANGED')
        for obj in [row['source'], row['olean']]:
            T.safe_member(obj['relative_path'])
            T.check(re.fullmatch('[0-9a-f]{64}', obj['sha256']) is not None,
                    'ORIGINAL_PRIOR_SOURCE_OR_OLEAN_SHA_MISSING')
    T.check([(a['role'], a['artifact'], a['artifactBytes'], a['githubWholeArtifactDigest'])
             for a in manifest['anchors']] == [
        ('CP', 14144403630, 3736616987,
         '5176cfa5a70038a8f59965a700b420f284b019e6eddc950682e587206e3ce7cd'),
        ('ABI', 14146017608, 1966192859,
         'ce5a475b0e02ccbaa3f88ec239c4be6c4685ca115fea44696023ee24db9f8086')],
        'ORIGINAL_TWO_ARCHIVES_CHANGED')
    T.check(all(a['run'] == RUN and a['head_sha'] == HEAD for a in manifest['anchors']),
            'ANCHOR_PRODUCER_CHANGED')
    T.check(manifest['limits'] == dict(range_chunk_bytes=T.CHUNK,
        total_network_and_uncompressed_bytes=T.TOTAL, CP_metadata_aggregate_bytes=64*T.MIB,
        ABI_metadata_aggregate_bytes=32*T.MIB, central_directory_bytes_each=16*T.MIB,
        api_metadata_bytes_each=T.MIB), 'R4_REVIEWED_CAPS_MUST_NOT_GROW')
    return manifest


class P2ArchiveReader(T.StrictArchiveReader):
    """Use inherited bounded transport, with an explicit P2 identity constructor."""
    def __init__(self, anchor, journal):
        self.journal = journal
        # Skip only R4's hard-coded constructor profile, never its transport.
        T.ArchiveReader.__init__(self, anchor)
        T.check(self.metadata['workflow_run']['head_sha'] == HEAD and
                self.metadata['workflow_run']['head_branch'] == BRANCH,
                'ORIGINAL_P2_PRODUCER_HEAD_OR_BRANCH_CHANGED')


def p2_record(record):
    # R4's generic helpers attach their producer constants to in-memory receipts.
    # Correct those labels for this explicit P2 caller; original bytes are untouched.
    record['official_producer_head'] = HEAD
    record['official_producer_run'] = RUN
    return record


def metadata(reader, inventory, name, journal, cap, expected=None):
    """Bounded first acquisition of original metadata, supporting ZIP 0 or 8.

    The new deflate branch is metadata-only and separately requires review.
    Plain and compressed lengths, local/central identity, EOF and CRC are checked.
    No compressed object or nested container is accepted by this branch.
    """
    T.safe_member(name)
    T.check(name.lower().endswith(('.json', '.jsonl', '.log', '.txt', '.lean')),
            'ONLY_METADATA_OR_ORIGINAL_AUDIT_SOURCE_ALLOWED')
    T.check(name in inventory, 'EXACT_METADATA_MEMBER_MISSING_NO_ALIAS')
    row = inventory[name]
    T.check(not row['is_directory'] and row['bytes'] <= cap and row['zip']['z'] <= cap,
            'METADATA_PLAIN_OR_COMPRESSED_CAP_HOLD')
    if row['zip']['c'] == 0:
        result = p2_record(T.metadata_member(reader, inventory, name, journal))
    else:
        T.check(row['zip']['c'] == 8 and not row['flags'] & 65 and
                not name.lower().endswith(('.tar', '.tar.gz', '.tgz', '.zip')),
                'ONLY_BOUNDED_RAW_DEFLATE_METADATA_PERMITTED')
        key = (reader.anchor['artifact'], name)
        if key in journal.saved:
            result = journal.saved[key]
        else:
            e = row['zip']
            journal.preflight_uncompressed(row['bytes'])
            h = struct.unpack('<IHHHHHIIIHH', reader.part(e['h'], 30))
            sig, version, flags, method, mt, md, crc, compressed, plain, nl, xl = h
            T.check(sig == 0x04034b50 and method == e['c'] and flags == row['flags'],
                    'DEFLATE_METADATA_LOCAL_HEADER_CHANGED')
            local_name = reader.part(e['h'] + 30, nl + xl)[:nl]
            T.check(local_name.decode('utf-8' if flags & 0x800 else 'cp437') == name,
                    'DEFLATE_METADATA_LOCAL_NAME_CHANGED')
            if not flags & 8:
                T.check((crc, compressed, plain) == (e['crc'], e['z'], e['s']),
                        'DEFLATE_METADATA_LOCAL_CENTRAL_DISAGREEMENT')
            start = e['h'] + 30 + nl + xl
            T.check(e['s'] == row['bytes'] and start + e['z'] <= row['central_offset'],
                    'DEFLATE_METADATA_WINDOW_CHANGED')
            packed = reader.part(start, e['z']) if e['z'] else b''
            decoder = zlib.decompressobj(-15)
            raw = decoder.decompress(packed, row['bytes'] + 1)
            T.check(len(raw) == row['bytes'] and decoder.eof and not decoder.unused_data and
                    not decoder.unconsumed_tail and zlib.crc32(raw) == e['crc'],
                    'DEFLATE_METADATA_LENGTH_EOF_OR_CRC_CHANGED')
            target = journal.output / 'original-metadata' / str(reader.anchor['artifact']) / name
            written = T.write_bytes(target, raw)
            result = dict(artifact=reader.anchor['artifact'], member=name, **written,
                expected_sha256=None, expected_sha_authority='ORIGINAL_METADATA_FIRST_ACQUISITION',
                crc32=f'{e["crc"]:08x}', zip=e, official_producer_head=HEAD,
                official_producer_run=RUN, whole_archive_digest_recomputed=False,
                status='ORIGINAL_METADATA_ONLY_NOT_ADMISSION', root_local_physical_availability='UNKNOWN')
            journal.uncompressed_bytes += len(raw)
            journal.saved[key] = result
            journal.records.append(result)
    if expected is not None:
        T.check(result['sha256'] == expected['sha256'] and result['bytes'] == expected['bytes'],
                'ORIGINAL_LIGHT_METADATA_SHA_OR_LENGTH_CHANGED')
        result['expected_sha256'] = expected['sha256']
        result['expected_sha_authority'] = 'ORIGINAL_R24_PUBLIC_LIGHT_RECEIPT'
    return result


def unique_rows(rows, key, code):
    result = {r[key]: r for r in rows}
    T.check(len(result) == len(rows), code)
    return result


def original_path(root, relative):
    T.safe_member(relative)
    return (root / relative).as_posix()


def derive_project(cp, manifest):
    roots = set()
    for module in manifest['modules']:
        obj = module['olean']
        suffix = '/' + obj['relative_path']
        matches = [(p, r) for p, r in cp['files'].items()
                   if p.endswith(suffix) and r.get('sha256') == obj['sha256']]
        T.check(len(matches) == 1, 'ORIGINAL_OLEAN_SHA_TO_PROJECT_MAPPING_NOT_UNIQUE_HOLD')
        path, row = matches[0]
        root = PurePosixPath(path[:-len(suffix)])
        T.check(root.is_absolute() and '..' not in root.parts and
                row.get('original_path') == path, 'ORIGINAL_PROJECT_PATH_INVALID')
        roots.add(root)
    T.check(len(roots) == 1, 'ORIGINAL102_DO_NOT_SHARE_ONE_PROJECT_HOLD')
    return roots.pop()


def original_slot(reader, inventory, cp, index, path, expected, journal):
    if path not in cp['files'] and path not in index:
        return dict(original_path=path, original_presence=False, bytes=None, sha256=None,
                    snapshot_sha256=expected.get('sha256'), member=None,
                    completed=None, quarantined=None, classification=None)
    name, identity = T.original_payload(cp, index, dict(original_path=path, **expected))
    if expected.get('sha256') is None:
        identity['expected_identity_authority'] = 'ORIGINAL_P2_CP_RAW_FILES_FIRST_ACQUISITION'
    record = p2_record(T.known_member(reader, inventory, name, identity, journal, path))
    old = cp['files'][path]
    return dict(original_path=path, original_presence=True, bytes=record['bytes'],
                sha256=record['sha256'], snapshot_sha256=expected.get('sha256'),
                member=name, expected_identity_authority=identity['expected_identity_authority'],
                original_file_record=old, completed=old.get('completed'),
                quarantined=old.get('quarantined'), classification=old.get('classification'),
                status=old.get('status'))


def export(manifest, journal):
    readers, inventories = {}, {}
    # Both bounded TOCs precede ALL metadata bodies and every payload selection.
    for anchor in manifest['anchors']:
        role = anchor['role']
        readers[role] = P2ArchiveReader(anchor, journal)
        inventories[role] = T.directory(readers[role], journal)
    names = dict(CP=CP_NAMES, ABI=ABI_NAMES + [r['member'] for r in manifest['light_receipts']])
    acquired = dict(CP={}, ABI={})
    prior = {r['member']: r for r in manifest['light_receipts']}
    for role in ['CP', 'ABI']:
        cap = (64 if role == 'CP' else 32) * T.MIB
        T.check(len(names[role]) == len(set(names[role])) and
                all(n in inventories[role] for n in names[role]),
                'ORIGINAL_ARCHIVE_ROLE_OR_EXACT_METADATA_NAME_HOLD')
        T.check(sum(inventories[role][n]['bytes'] for n in names[role]) <= cap and
                sum(inventories[role][n]['zip']['z'] for n in names[role]) <= cap,
                'ORIGINAL_METADATA_AGGREGATE_CAP_HOLD')
        for name in names[role]:
            acquired[role][name] = metadata(readers[role], inventories[role], name,
                                           journal, cap, prior.get(name))
    cp_record = acquired['CP']['CHECKPOINT.json']
    cp = T.load(cp_record['path'])
    T.check(cp['schema'] == 't01-coherent-build-checkpoint-v3' and
            cp['source_commit'] == SOURCE and str(cp['run_id']) == str(RUN) and
            str(cp['run_attempt']) == '1' and isinstance(cp['files'], dict),
            'ORIGINAL_CP_PRODUCER_OR_SCHEMA_HOLD')
    snapshot = T.load(acquired['CP']['SNAPSHOT_ACQUISITION.json']['path'])
    T.check(snapshot['raw_index'] == 'RAW_FILES.jsonl' and
            snapshot['acquisition_phase_complete'] is True and snapshot['kernel_verified'] is False,
            'ORIGINAL_RAW_ACQUISITION_SCHEMA_HOLD')
    index = T.raw_index(acquired['CP']['RAW_FILES.jsonl']['path'])
    abi = {n: T.load(acquired['ABI'][n]['path']) for n in ABI_NAMES if n.endswith('.json')}
    light = {n: T.load(acquired['ABI'][n]['path']) for n in
             ['VALIDATION_MANIFEST.json', 'BATCH_ACCEPTANCE.json', 'BATCH_OBJECTS_BEFORE.json',
              'CACHE_FINAL_INPUT_AUDIT.json', 'DRIVER_BINDING.json']}
    binding = light['CACHE_FINAL_INPUT_AUDIT.json']['binding']
    T.check(binding['driver_commit'] == HEAD and str(binding['run_id']) == str(RUN) and
            str(binding['run_attempt']) == '1' and binding['source_commit'] == SOURCE,
            'ORIGINAL_CACHE_BINDING_HOLD')
    ret = abi['CACHE_CHECKPOINT_RETENTION.json']
    summary = abi['CHECKPOINT_SUMMARY.json']
    adapted = abi['CHECKPOINT_COLLECTOR_INPUT.json']
    validation = light['VALIDATION_MANIFEST.json']
    T.check(ret['binding'] == binding and ret['collector_sha256'] == manifest['collector_sha256'] and
            ret['adapter_sha256'] == manifest['adapter_sha256'] and
            ret['input_sha256'] == acquired['ABI']['CHECKPOINT_COLLECTOR_INPUT.json']['sha256'] and
            ret['stdout_sha256'] == acquired['ABI']['checkpoint-collection.log']['sha256'] and
            summary['checkpoint_sha256'] == cp_record['sha256'] and
            cp['manifest_sha256'] == ret['input_sha256'], 'ORIGINAL_COLLECTOR_CROSS_LINK_HOLD')
    T.check(adapted['files'] == validation['modules'] and adapted['data_inputs'] == [] and
            validation['source_commit'] == SOURCE and
            adapted['targets'] == [dict(closure_modules=[r['module'] for r in validation['modules']],
                source_identity_sha256=T.canonical(validation['modules']))] and
            cp['source_identity_sha256'] == adapted['targets'][0]['source_identity_sha256'],
            'ORIGINAL_SOURCE_GRAPH_CROSS_LINK_HOLD')
    original_sources = unique_rows(validation['modules'], 'module', 'DUPLICATE_ORIGINAL_SOURCE_MODULE')
    module_names = [r['module'] for r in manifest['modules']]
    batch = light['BATCH_ACCEPTANCE.json']
    T.check(list(original_sources) == module_names and batch['modules'] == module_names and
            batch['proof_artifact_hash'] == acquired['ABI']['BATCH_OBJECTS_BEFORE.json']['sha256'],
            'ORIGINAL102_CHECKER_SNAPSHOT_SET_HOLD')
    driver = light['DRIVER_BINDING.json']
    T.check(driver['driver_commit'] == HEAD and driver['ref'] == 'refs/heads/' + BRANCH,
            'ORIGINAL_DRIVER_BINDING_HOLD')
    retained = abi['RETAINED_OBJECTS.json']
    T.check(retained['archive'] == 'compiled-objects-and-sources.tar.gz' and
            retained['archive'] in inventories['ABI'], 'ORIGINAL_NESTED_ARCHIVE_NAME_HOLD')
    # The tar's bytes are never requested. Its old manifest/declared SHA is retained.
    kept = unique_rows(retained['files'], 'path', 'DUPLICATE_ORIGINAL_RETAINED_PATH')
    modules = unique_rows(cp['modules'], 'module', 'DUPLICATE_ORIGINAL_CP_MODULE')
    root = derive_project(cp, manifest)
    configuration = {}
    for key in ['lean_toolchain', 'lake_manifest', 'lakefile']:
        profile = manifest['source_profile'][key]
        expected = dict(sha256=profile['sha256'], bytes=profile['bytes'],
                        expected_identity_authority='ORIGINAL_R24_SOURCE_PROFILE')
        configuration[key] = original_slot(readers['CP'], inventories['CP'], cp, index,
            original_path(root, profile['path']), expected, journal)
        T.check(configuration[key]['original_presence'] and profile['path'] in kept and
                kept[profile['path']]['sha256'] == profile['sha256'] and
                kept[profile['path']]['bytes'] == profile['bytes'],
                'ORIGINAL_CONFIGURATION_CP_ABI_CROSS_LINK_HOLD')
    runtime_audit = T.load(acquired['ABI']['runtime/audit.json']['path'])
    state_name = 'runtime/state.json'
    T.check(state_name in inventories['ABI'] and
            sum(inventories['ABI'][n]['bytes'] for n in names['ABI']) +
            inventories['ABI'][state_name]['bytes'] <= 32*T.MIB and
            sum(inventories['ABI'][n]['zip']['z'] for n in names['ABI']) +
            inventories['ABI'][state_name]['zip']['z'] <= 32*T.MIB,
            'ORIGINAL_RUNTIME_METADATA_AGGREGATE_CAP_HOLD')
    state_record = metadata(readers['ABI'], inventories['ABI'], state_name, journal, T.MIB)
    T.check(state_record['sha256'] == runtime_audit['state_sha256'] and
            acquired['ABI']['runtime/compiler-commands.jsonl']['sha256'] ==
            runtime_audit['command_log_sha256'] and
            T.load(state_record['path']) == cp['runtime_state'],
            'ORIGINAL_CP_RUNTIME_STATE_CROSS_LINK_HOLD')
    rows, unavailable = [], []
    for module in manifest['modules']:
        name = module['module']
        source = original_sources[name]
        T.check(all(source[k] == module['source'][k] for k in
                    ['sha256', 'bytes', 'source_commit', 'origin_path']) and
                source['install_path'] == module['source']['relative_path'],
                'ORIGINAL_SOURCE_SELECTION_CHANGED')
        T.check(name in modules, 'ORIGINAL_MODULE_CLASSIFICATION_MISSING_HOLD')
        old = modules[name]
        stem = name.replace('.', '/')
        slots = {'source': module['source']['relative_path'],
                 **{f: '.lake/build/lib/lean/' + stem + '.' + f for f in SIX},
                 'trace': '.lake/build/lib/lean/' + stem + '.trace',
                 'setup': '.lake/build/ir/' + stem + '.setup.json'}
        for path in old.get('required_output_parts', []):
            rel = PurePosixPath(path).relative_to(root).as_posix()
            T.check(rel in slots.values() or rel in
                    ['.lake/build/ir/' + stem + '.c', '.lake/build/ir/' + stem + '.bc'],
                    'UNRECOGNIZED_ORIGINAL_REQUIRED_OUTPUT_HOLD')
            if rel not in slots.values():
                slots['original_required_' + PurePosixPath(rel).suffix[1:]] = rel
        results = {}
        for slot, rel in slots.items():
            expected = dict(sha256=None, bytes=None,
                            expected_identity_authority='ORIGINAL_CP_RAW_FILES_FIRST_ACQUISITION')
            if slot == 'source':
                expected.update(sha256=module['source']['sha256'], bytes=module['source']['bytes'],
                                expected_identity_authority='ORIGINAL_R24_STAGE_SOURCE_SHA')
            if slot == 'olean':
                expected.update(sha256=module['olean']['sha256'],
                                expected_identity_authority='ORIGINAL_R24_BATCH_OBJECTS_BEFORE_OLEAN_ONLY')
                T.check(light['BATCH_OBJECTS_BEFORE.json'].get(rel) == expected['sha256'],
                        'ORIGINAL_BATCH_OLEAN_SNAPSHOT_SHA_CHANGED')
            path = original_path(root, rel)
            results[slot] = original_slot(readers['CP'], inventories['CP'], cp, index,
                                          path, expected, journal)
            if not results[slot]['original_presence']:
                unavailable.append(dict(module=name, slot=slot, relative_path=rel))
            if slot in ['source', 'olean']:
                T.check(rel in kept and kept[rel]['sha256'] == expected['sha256'] and
                        (not results[slot]['original_presence'] or
                         kept[rel]['bytes'] == results[slot]['bytes']),
                        'ORIGINAL_ABI_RETAINED_SOURCE_OR_OLEAN_CP_BIND_HOLD')
        rows.append(dict(module=name, slots=results, original_module_record=old,
            original_completed=old.get('completed_guarded_compile_candidate'),
            original_quarantined=old.get('quarantined'), original_status=old.get('status'),
            original_classification=old.get('classification'),
            original_kernel_verified=old.get('kernel_verified')))
    T.write_json(journal.output / 'ORIGINAL102_SELECTION_RESULT.json', dict(
        schema='p2-original102-original-metadata-and-bytes-only-v1', modules=rows,
        original_checkpoint_status=cp.get('status'), original_checkpoint_issues=cp.get('issues'),
        original_checkpoint_green=cp.get('green'), original_retained_manifest=retained,
        original_collector_exit_code=ret.get('exit_code'), original_summary=summary,
        original_configuration=configuration, original_batch_receipt=batch,
        unavailable_requested_slots=unavailable,
        all_requested_slots_present=not unavailable, original_classifications_modified=False,
        nested_archive_body_requested=False, proof_acceptance=False, reuseReady=False))
    if unavailable:
        journal.failure('REQUESTED_ORIGINAL_SLOTS_ABSENT_NULLS_PRESERVED', count=len(unavailable))
    journal.complete_selection = not unavailable


def public_record(record, output):
    result = dict(record)
    if 'path' in result:
        result['relative_carrier_path'] = Path(result.pop('path')).relative_to(output).as_posix()
    return result


def main():
    manifest = bind_control()  # Pending by default; before output or network.
    temporary = Path(os.environ['RUNNER_TEMP']).resolve()
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
    output = temporary / 'p2-original102-byte-carrier'
    T.check(not output.exists() and output.is_relative_to(temporary) and
            not output.is_relative_to(workspace), 'FRESH_DISJOINT_OUTPUT_REQUIRED')
    output.mkdir()
    journal = T.Journal(output)
    try:
        export(manifest, journal)
    except Exception as error:
        journal.failure(str(error) if isinstance(error, T.Hold) else type(error).__name__,
                        phase='P2_ORIGINAL102_BYTE_EXPORT_HOLD')
    finally:
        available = []
        verified = {r['path'] for r in journal.records}
        for path in sorted(output.rglob('*')):
            if path.is_file() and not path.is_symlink():
                with path.open('rb') as stream:
                    sha = hashlib.file_digest(stream, 'sha256').hexdigest()
                available.append(dict(path=path.relative_to(output).as_posix(),
                    bytes=path.stat().st_size, sha256=sha,
                    remote_original_identity_verified=path.as_posix() in verified))
        T.write_json(output / 'AVAILABLE_OUTPUT_BYTES.json', dict(files=available,
            unverified_partial_files_preserved=True, fresh_runner_identity_published=False))
        receipt = dict(schema='p2-original102-byte-carrier-receipt-v1',
            status='HOLD_WITH_AVAILABLE_BYTES' if journal.failures else 'FINITE_ORIGINAL_BYTES_ONLY',
            original_producer=manifest['producer'],
            originals=[public_record(r, output) for r in journal.records], failures=journal.failures,
            total_network_bytes=journal.total_network_bytes,
            reserved_network_upper_bound=journal.reserved_network_bytes,
            selected_uncompressed_bytes=journal.uncompressed_bytes,
            complete_requested_selection=journal.complete_selection,
            whole_artifact_downloaded=False, whole_artifact_digest_recomputed=False,
            nested_tar_body_downloaded=False, mathematical_compiler_events=0,
            toolchain_installed_or_loaded=False, object_or_IR_loads=0, kernel_replays=0,
            original_classifications_modified=False, consumer_admission=False,
            proof_acceptance=False, new_green=0, reuseReady=False,
            fresh_runner_identity_published=False, root_local_physical_availability='UNKNOWN')
        T.write_json(output / 'EXPORT_RECEIPT.json', receipt)
        print(json.dumps(dict(status=receipt['status'], files=len(journal.records), reuseReady=False)))
    return 1 if journal.failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
