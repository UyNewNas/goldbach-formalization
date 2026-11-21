"""R4 five-object ORIGINAL BYTE CARRIER draft. No proof/toolchain/object load.

This wrapper is independent of every compiler/runtime/admission gate. It only
calls the reviewed stdlib Range transport and writes sanitized byte receipts.
ROOT must replace the pending data-export control after exact source/tree review.
"""
import hashlib
import json
import os
from pathlib import Path
import sys

import range_transport as T

HERE = Path(__file__).resolve().parent
REPO = 'UyNewNas/goldbach-formalization'
HEAD = 'dfeabf9b5e88703c8700a388d53277132e586b90'
RUN = 43681964804
MODULES = [
 'LeanPool.KloostermanWeil.Carlitz.ClassGhost',
 'LeanPool.KloostermanWeil.Carlitz.RelevantIrreducibles',
 'LeanPool.KloostermanWeil.Carlitz.IrreducibleGhost',
 'LeanPool.KloostermanWeil.Carlitz.NewtonIndex',
 'LeanPool.KloostermanWeil.Carlitz.NewtonSum',
]


def bind_manifest():
    control = T.load(HERE / 'EXPORT_CONTROL.json')
    # No networking, candidate import, qualification helper or object loader
    # occurs before this pending approval and exact caller/tree projection gate.
    T.check(control['driverReady'] is True and control['execute'] == 'ALLOW_REVIEWED_R4_DATA_EXPORT_ONLY',
            'PENDING_ROOT_N09_SOURCE_ACTUAL_TREE_AND_CALLER_REVIEW')
    T.check(control['independent_source_and_actual_tree_allowlist'] is not None and
            control['fresh_run_ref_duplicate_review'] is not None,
            'ACTUAL_TREE_OR_FRESH_DISPATCH_REVIEW_ABSENT')
    T.check(os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux' and
            os.environ.get('GITHUB_REPOSITORY') == REPO and
            os.environ.get('GITHUB_EVENT_NAME') == 'push' and
            os.environ.get('GITHUB_REF') == control['branch'],
            'EXACT_REVIEWED_DATA_CARRIER_CALLER_REQUIRED')
    raw = (HERE / 'INPUT_MANIFEST.json').read_bytes()
    T.check(T.digest(raw) == control['input_manifest_sha256'], 'INPUT_MANIFEST_PIN_CHANGED')
    manifest = json.loads(raw)
    T.check(set(control['source_sha256']) == {'export_r4_five.py', 'range_transport.py', 'original_archive_reader.py'},
            'EXACT_EXPORTER_SOURCE_SET_REQUIRED')
    for name, expected in control['source_sha256'].items():
        T.check(T.digest((HERE / name).read_bytes()) == expected, 'EXPORT_SOURCE_PIN_CHANGED')
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
    present = {p.relative_to(workspace).as_posix() for ext in ['*.yml', '*.yaml']
               for p in (workspace / '.github/workflows').glob(ext)}
    reviewed = {r['path']: r for r in control['reviewed_workflows']}
    T.check(bool(reviewed) and len(reviewed) == len(control['reviewed_workflows']) and
            set(reviewed) == present, 'COMPLETE_ACTUAL_WORKFLOW_PROJECTION_MISSING')
    for path, row in reviewed.items():
        body = (workspace / path).read_bytes()
        T.check(len(body) == row['bytes'] and T.digest(body) == row['sha256'],
                'REVIEWED_WORKFLOW_BYTES_CHANGED')
    T.check(manifest['schema'] == 'weil-r4-five-finite-byte-selection-v1' and
            manifest['producer_binding']['driver_commit'] == HEAD and
            manifest['producer_binding']['run_id'] == str(RUN) and
            manifest['producer_binding']['source_commit'] == 'e364670c1f9a59b64d395be22371ea3d0b406ffc' and
            manifest['modules'] == MODULES, 'EXACT_R4_PRODUCER_OR_FIVE_MODULE_SET_CHANGED')
    T.check([(a['role'], a['artifact']) for a in manifest['anchors']] ==
            [('CP', 14154067123), ('PROOF', 14153902698)], 'ORIGINAL_R4_ARCHIVES_CHANGED')
    T.check(manifest['limits'] == dict(range_chunk_bytes=T.CHUNK,
        total_network_and_uncompressed_bytes=T.TOTAL, CP_metadata_aggregate_bytes=64*T.MIB,
        PROOF_metadata_aggregate_bytes=32*T.MIB, central_directory_bytes_each=16*T.MIB,
        api_metadata_bytes_each=T.MIB), 'R3_REVIEWED_HARD_CAPS_MUST_NOT_GROW')
    expected_paths = set()
    project = '/home/runner/work/_temp/t01-project/'
    for module in MODULES:
        stem = module.replace('.', '/')
        expected_paths.update([project+stem+'.lean', project+'.lake/build/ir/'+stem+'.setup.json'])
        expected_paths.update(project+'.lake/build/lib/lean/'+stem+s for s in
                             ['.olean', '.olean.server', '.olean.private', '.ir.sig', '.ir', '.ilean'])
    T.check(len(expected_paths) == 40 and {r['original_path'] for r in manifest['known_objects']} == expected_paths,
            'EXACT_FIVE_SOURCE_SETUP_ALL_SIX_FACETS_REQUIRED')
    T.check(len(manifest['known_objects']) == 40 and
            all(r['sha256'] and r['bytes'] >= 0 for r in manifest['known_objects']),
            'TRUSTED_LIGHT_OUTPUT_IDENTITY_MISSING')
    T.check(set(manifest['required_metadata']) == {'CP', 'PROOF'} and
            manifest['required_metadata'] == dict(CP=['CHECKPOINT.json', 'RAW_FILES.jsonl', 'SNAPSHOT_ACQUISITION.json'],
                PROOF=['WEIL_RETENTION.json', 'CHECKPOINT_SUMMARY.json']), 'ACTUAL_WRITER_NAME_SET_CHANGED')
    return manifest


def export(manifest, journal):
    readers, inventories, metadata = {}, {}, {}
    for anchor in manifest['anchors']:
        role = anchor['role']
        reader = T.StrictArchiveReader(anchor, journal)
        inventory = T.directory(reader, journal)
        readers[role], inventories[role], metadata[role] = reader, inventory, {}
        names = manifest['required_metadata'][role]
        T.check(all(n in inventory for n in names), 'EXACT_CURRENT_WRITER_METADATA_MISSING')
        cap = 64*T.MIB if role == 'CP' else 32*T.MIB
        capped = [*names, *(['checkpoint-collection.log'] if role == 'PROOF' else [])]
        T.check(all(n in inventory for n in capped) and
                sum(inventory[n]['bytes'] for n in capped) <= cap, 'ORIGINAL_METADATA_AGGREGATE_CAP_HOLD')
        for name in names:
            metadata[role][name] = T.metadata_member(reader, inventory, name, journal)
    cp_record = metadata['CP']['CHECKPOINT.json']
    cp = T.load(cp_record['path'])
    T.check(cp['schema'] == manifest['checkpoint_schema'] and
            cp['source_commit'] == manifest['producer_binding']['source_commit'] and
            str(cp['run_id']) == str(RUN) and str(cp['run_attempt']) == '1' and
            cp['source_identity_sha256'] == manifest['trusted_source_graph_sha256'] and
            T.canonical(cp['runtime_state']) == manifest['trusted_runtime_state_canonical_sha256'],
            'CURRENT_R4_CP_LIGHT_SOURCE_RUNTIME_CROSS_BIND_FAILED')
    snapshot = T.load(metadata['CP']['SNAPSHOT_ACQUISITION.json']['path'])
    T.check(snapshot['raw_index'] == 'RAW_FILES.jsonl' and
            snapshot['acquisition_phase_complete'] is True and snapshot['kernel_verified'] is False,
            'ORIGINAL_SNAPSHOT_SCHEMA_CHANGED')
    index = T.raw_index(metadata['CP']['RAW_FILES.jsonl']['path'])
    selected = [*manifest['known_objects'], *manifest['exact_CP_log_difference']]
    T.check(len({r['original_path'] for r in selected}) == len(selected), 'DUPLICATE_ORIGINAL_PATH_SELECTION')
    exported = {}
    for expected in selected:
        name, identity = T.original_payload(cp, index, expected)
        exported[expected['original_path']] = T.known_member(readers['CP'], inventories['CP'], name,
            identity, journal, expected['original_path'])
    ret_record = metadata['PROOF']['WEIL_RETENTION.json']
    summary_record = metadata['PROOF']['CHECKPOINT_SUMMARY.json']
    ret, summary = T.load(ret_record['path']), T.load(summary_record['path'])
    writer = manifest['actual_writer_pins']['collector']
    T.check(ret['binding'] == manifest['producer_binding'] and ret['exit_code'] == 0 and
            not ret['integrity_errors'] and ret['checkpoint_sha256'] == cp_record['sha256'] and
            ret['root_source_count'] == 34 and ret['root_source_rows_sha256'] == manifest['trusted_source_graph_sha256'] and
            ret['collector_sha256'] == writer['sha256'] and ret['collector_bytes'] == writer['bytes'] and
            ret['actual_collector_summary_sha256'] == summary_record['sha256'] and
            summary == ret['actual_collector_summary'] and summary['checkpoint_sha256'] == cp_record['sha256'] and
            summary['green'] is False, 'ORIGINAL_R4_COLLECTOR_RETENTION_SUMMARY_CHAIN_HOLD')
    T.known_member(readers['PROOF'], inventories['PROOF'], 'checkpoint-collection.log', dict(bytes=None,
        sha256=ret['stdout_sha256'], expected_identity_authority='ORIGINAL_R4_RETENTION_FIRST_OFFICIAL_ACQUISITION'), journal)
    project = '/home/runner/work/_temp/t01-project/'
    logs = '/home/runner/work/_temp/weil34-evidence/'
    provenance = exported[project+'T01_PROVENANCE.json']
    collector = exported[logs+'CHECKPOINT_COLLECTOR_INPUT.json']
    capture_record = exported[logs+'WEIL_RAW_CAPTURE.json']
    T.check(provenance['sha256'] == ret['provenance_sha256'] and
            collector['sha256'] == ret['collector_manifest_sha256'] and
            capture_record['sha256'] == ret['raw_capture_sha256'], 'ORIGINAL_COMPONENT_CROSS_LINK_CHANGED')
    prov, original_manifest, capture = [T.load(r['path']) for r in [provenance, collector, capture_record]]
    T.check(prov['binding'] == manifest['producer_binding'] and
            T.canonical(prov['modules']) == manifest['trusted_full_source_rows_sha256'] and
            T.canonical(original_manifest['files']) == manifest['trusted_source_graph_sha256'] and
            capture['binding'] == manifest['producer_binding'] and not capture['integrity_errors'],
            'ORIGINAL_GRAPH_PROVENANCE_CAPTURE_FAILED')
    captured = {r['path']: r for r in capture['files']}
    for expected in manifest['known_objects']:
        T.check(expected['original_path'] in captured and all(
            captured[expected['original_path']][k] == expected[k] for k in ['bytes', 'sha256']),
            'SELECTED_SOURCE_SETUP_FACET_ABSENT_FROM_ACTUAL_CAPTURE')
    tar = logs + capture['archive']
    T.check(tar in cp['files'] and cp['files'][tar]['sha256'] == capture['archive_sha256'],
            'NESTED_TAR_METADATA_LINK_CHANGED_NO_BODY_FETCH')
    T.write_json(journal.output/'ORIGINAL_CROSS_LINKS.json', dict(
        status='R4_ORIGINAL_BYTE_CROSS_LINKS_ONLY_NOT_ADMISSION', producer_binding=manifest['producer_binding'],
        checkpoint_sha256=cp_record['sha256'], retention_sha256=ret_record['sha256'],
        original_completed_and_quarantine_classifications_preserved=True, whole_archive_digest_recomputed=False,
        nested_tar_body_requested=False, root_local_physical_availability='UNKNOWN', reuseReady=False))
    journal.complete_selection = True


def main():
    # Pending controls are checked BEFORE output setup or any network operation.
    manifest = bind_manifest()
    temporary = Path(os.environ['RUNNER_TEMP']).resolve()
    output = temporary/'weil-r4-five-byte-carrier'
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
    T.check(not output.exists() and output.is_relative_to(temporary) and not output.is_relative_to(workspace),
            'FRESH_DISJOINT_CARRIER_OUTPUT_REQUIRED')
    output.mkdir(); journal = T.Journal(output)
    try:
        export(manifest, journal)
    except Exception as error:
        journal.failure(str(error) if isinstance(error, T.Hold) else type(error).__name__, phase='R4_BYTE_EXPORT_HOLD')
    finally:
        verified = {r['path'] for r in journal.records}
        available = []
        for p in sorted(output.rglob('*')):
            if p.is_file() and not p.is_symlink():
                with p.open('rb') as stream:
                    current_sha = hashlib.file_digest(stream, 'sha256').hexdigest()
                available.append(dict(path=p.relative_to(output).as_posix(), bytes=p.stat().st_size,
                    sha256=current_sha,
                    remote_original_identity_verified=p.as_posix() in verified,
                    root_local_physical_availability='UNKNOWN'))
        T.write_json(output/'AVAILABLE_OUTPUT_BYTES.json', dict(files=available, unverified_partial_files_preserved=True))
        receipt = dict(schema='weil-r4-five-original-byte-carrier-receipt-v1',
            status='HOLD_WITH_AVAILABLE_BYTES' if journal.failures else 'FINITE_ORIGINAL_R4_BYTES_EXPORTED_ONLY',
            carrier=dict(commit=os.environ.get('GITHUB_SHA'), run=os.environ.get('GITHUB_RUN_ID'),
                actual_parent_runtime_verified=False),
            original_proof_producer=dict(driver_commit=HEAD, run_id=str(RUN), source_commit=manifest['producer_binding']['source_commit']),
            originals=journal.records, failures=journal.failures,
            total_network_bytes=journal.total_network_bytes,
            reserved_network_upper_bound=journal.reserved_network_bytes,
            selected_uncompressed_bytes=journal.uncompressed_bytes,
            complete_finite_selection_exported_remotely=journal.complete_selection,
            held_light_original_reference_manifest_sha256=manifest['held_light_reference_manifest_sha256'],
            whole_CP_or_proof_downloaded=False, whole_archive_digest_recomputed=False,
            nested_tar_body_downloaded=False, mathematical_compiler_events=0,
            toolchain_installed_or_loaded=False, olean_or_IR_loaded=False,
            old_CP_classifications_modified=False, consumer_admission=False, proof_acceptance=False,
            reuseReady=False, root_local_physical_availability='UNKNOWN')
        T.write_json(output/'EXPORT_RECEIPT.json', receipt)
        print(json.dumps(dict(status=receipt['status'], files=len(journal.records), reuseReady=False)))
    return 1 if journal.failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
