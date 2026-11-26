#!/usr/bin/env python3
"""Strictly recheck 219 receipt chains and retain their archive on the cloud host.

Only archive metadata is printed. No archive body, base64 payload or transfer is
produced by this command. Only the 73 new object bodies are included.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import os
import sys
import tarfile

sys.dont_write_bytecode = True
from receipt_checks import (ATTEMPT, TOOL_REL, canonical, fp, read, require,
                            validate_success, verification_files)
from verify_fields import bind_context_to_package, load_configuration


def data_pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def recheck_archive(path, expected_manifest):
    expected = {row['member']: row for row in expected_manifest['members']}
    require(len(expected) == len(expected_manifest['members']), 'Duplicate archive member plan')
    seen = set()
    with tarfile.open(path, 'r:xz') as archive:
        for item in archive:
            relative = PurePosixPath(item.name)
            require(item.isfile() and not relative.is_absolute() and '..' not in relative.parts,
                    'Unsafe/non-file archive member')
            require(item.name not in seen, 'Duplicate actual archive member')
            seen.add(item.name)
            data = archive.extractfile(item).read()
            if item.name == 'EXPORT_MANIFEST.json':
                require(json.loads(data) == expected_manifest, 'Archive manifest differs from frozen plan')
            else:
                require(item.name in expected, f'Unexpected archive member: {item.name}')
                require(data_pin(data) == {key: expected[item.name][key] for key in ('bytes', 'sha256')},
                        f'Archive bytes differ from frozen plan: {item.name}')
    require(seen == set(expected) | {'EXPORT_MANIFEST.json'}, 'Missing archive member')


def write_verified_archive(output, entries, manifest):
    """Freeze before packing, re-read the tar, and compare every input afterwards."""
    output = canonical(output)
    partial = canonical(output.with_name(output.name + '.partial'))
    require(not output.exists() and not partial.exists(), 'Refuse to replace an existing export or partial export')
    before = {str(path): fp(path) for path in entries.values()}
    expected = {row['member']: row for row in manifest['members']}
    require(set(entries) == set(expected), 'Archive plan and selected paths differ')
    for member, path in entries.items():
        require(data_pin(path.read_bytes()) == {key: expected[member][key] for key in ('bytes', 'sha256')},
                'Source changed before archive creation')
    output.parent.mkdir(parents=True, exist_ok=True)
    canonical(output.parent, True)
    with partial.open('xb') as stream:
        with tarfile.open(fileobj=stream, mode='w:xz', preset=6) as archive:
            for member, path in sorted(entries.items()):
                # Source installation deliberately uses hardlinks. Emit each
                # selected member as regular bytes, never tar inode aliases.
                data = path.read_bytes()
                info = tarfile.TarInfo(member)
                info.type = tarfile.REGTYPE
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))
            body = (json.dumps(manifest, indent=2) + '\n').encode()
            info = tarfile.TarInfo('EXPORT_MANIFEST.json')
            info.size, info.mode, info.mtime = len(body), 0o644, 0
            archive.addfile(info, io.BytesIO(body))
    recheck_archive(partial, manifest)
    for path, identity in before.items():
        require(fp(path) == identity, f'Input changed while packing; partial export retained: {path}')
    # link is exclusive and never replaces an existing destination.
    canonical(output)
    os.link(partial, output)
    partial.unlink()
    return fp(output)


def main():
    require(sys.flags.optimize == 0, 'Run without Python optimization')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, required=True)
    ap.add_argument('--attempt', required=True)
    ap.add_argument('--label', default='v1')
    args = ap.parse_args()
    require(ATTEMPT.fullmatch(args.attempt) and ATTEMPT.fullmatch(args.label), 'Invalid attempt/export label')
    stage = canonical(args.stage, True)
    here = canonical(Path(os.path.abspath(__file__)).parent, True)
    require(here == stage / TOOL_REL, 'Exporter must run from its exact packaged stage')
    config, registry, baseline = load_configuration(here)
    success_path = stage / 'verification' / args.attempt / 'SUCCESS.json'
    context, steps = validate_success(success_path)
    bind_context_to_package(context, here, config, registry)
    require(Path(context['stage']) == stage, 'Export stage differs from accepted context')
    success = read(success_path)
    entries = {}

    def select(path):
        path = canonical(path, True)
        require(path.is_relative_to(stage), f'Cannot archive a file outside this stage: {path}')
        member = str(path.relative_to(stage))
        previous = entries.setdefault(member, path)
        require(previous == path, 'Conflicting archive member')

    for row in config['targets']:
        relative = Path(row['module'].replace('.', '/'))
        for directory, suffix in [('sources', '.lean'), ('project', '.lean'), ('objects', '.olean')]:
            select(stage / directory / relative.with_suffix(suffix))
        select(here / row['audit_relative_path'])
    for row in config['workflow_files']:
        select(here / row['relative_path'])
    select(here / 'FIELDS_VERIFIER.json')
    for row in read(here / 'BASELINE_EVIDENCE.json')['members']:
        select(here / row['relative_path'])
    for path in verification_files(stage, [row['module'] for row in config['targets']]):
        select(path)
    new_objects = {row['module'].replace('.', '/') + '.olean' for row in config['targets']}
    archived_objects = {member.removeprefix('objects/') for member in entries if member.startswith('objects/')}
    require(archived_objects == new_objects and len(archived_objects) == 73, 'Old or missing object body in export')
    require(not any(member.endswith('.olean') and not member.startswith('objects/') for member in entries),
            'Unexpected object body outside new object root')
    owned = [step['result'] for step in steps if step['result']['mode'] == 'owned']
    manifest = {'schema': 'cell05_fields_cloud_export_v1', 'status': 'SEVENTY_THREE_NEW_OWNERS_NORMAL_KERNEL_FULL_OWNED_PASSED',
                'attempt': args.attempt, 'success_member': str(success_path.relative_to(stage)), 'success': fp(success_path),
                'source_candidate_version': config['schema'], 'members': [
                    {'member': member, **data_pin(path.read_bytes())} for member, path in sorted(entries.items())],
                'accepted_targets': 73, 'accepted_steps': 219,
                'newly_executed_steps': success['newly_executed_steps'], 'reused_steps': success['reused_steps'],
                'step_counts': {'normal': 73, 'kernel': 73, 'owned': 73},
                'owned_declaration_count': sum(row['owned_declaration_count'] for row in owned),
                'old_supplier_object_bodies_included': False, 'old_supplier_proof_commands': 0,
                'baseline': baseline, 'original_nonrow_arrays': ['active8_enumeration', 'vertices', 'vertex_values',
                    'all_original_constraint_minima', 'facet_vertices', 'face_ledger'],
                'metadata_prefix_fields': 5, 'row_count_host_plan': 56,
                'original_input_bytes': 201042, 'vertex_count_host_plan': 28,
                'whole_geometry_decoded': False, 'P2_6_complete': False,
                'Lean_executed_for_export': False, 'automatic_full_archive_transfer': False}
    output = stage / 'exports' / f'fields-{args.attempt}-{args.label}-evidence.tar.xz'
    canonical(output)
    report_path = canonical(output.with_name(output.name + '.json'))
    require(not report_path.exists(), 'Refuse to replace an export report')
    identity = write_verified_archive(output, entries, manifest)
    bind_context_to_package(context, here, config, registry)
    validate_success(success_path)
    report = {'schema': 'cell05_fields_cloud_export_report_v1', 'status': 'PASS_EXPORT_RECHECK',
              'archive': identity, 'listed_members': len(entries), 'archive_members': len(entries) + 1,
              'accepted_targets': 73, 'accepted_steps': 219,
              'newly_executed_steps': success['newly_executed_steps'], 'reused_steps': success['reused_steps'],
              'old_supplier_object_bodies_included': False, 'archive_member_recheck_passed': True,
              'selected_inputs_unchanged_while_packing': True, 'Lean_executed_for_export': False,
              'automatic_full_archive_transfer': False}
    with report_path.open('x') as stream:
        stream.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
