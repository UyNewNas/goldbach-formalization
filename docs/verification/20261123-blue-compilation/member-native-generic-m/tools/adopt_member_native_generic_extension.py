#!/usr/bin/env python3
"""Independently verify published slices, then adopt only authorized native sources."""
from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
CANDIDATE = Path('/workspace/blue-member-native-generic-extension-candidate')
EVIDENCE = Path('/workspace/blue-member-native-generic-extension-validation')
NATIVE = Path('/workspace/blue-member-build/.lake/packages/goldbach')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def process_snapshot(paths):
    matches, lean = [], []
    relative = {str(p.relative_to(NATIVE)) for p in paths}
    for process in Path('/proc').iterdir():
        if not process.name.isdigit():
            continue
        try:
            argv = [a.decode(errors='replace') for a in (process / 'cmdline').read_bytes().split(b'\0') if a]
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
        if not argv:
            continue
        if Path(argv[0]).name not in ['lean', 'lean-runtime'] and not any('lean-wrapper.py' in a for a in argv[:2]):
            continue
        record = {'pid': int(process.name), 'argv': argv}
        lean.append(record)
        if any(str(p) in argv for p in paths) or any(a in relative for a in argv):
            matches.append(record)
    assert not matches, matches
    return {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'watched_source_paths': [str(p) for p in paths],
            'matching_active_or_queued_lean_wrappers': matches,
            'all_observed_source_lean_or_wrappers': lean}


def main():
    manifest_path = CANDIDATE / 'OVERLAY_MANIFEST.json'
    manifest = json.loads(manifest_path.read_text())
    assert sha(manifest_path.read_bytes()) == '03e0656e714869984faa6aa87a3c523ddedd6cf42c4ade455147cbf5c5ff9aec'
    extension = manifest['extension']
    data = (CANDIDATE / extension['candidate_path']).read_bytes()
    assert sha(data) == extension['sha256']
    source_files, rows = {}, []
    remaining = bytearray(data)
    for row in manifest['declarations']:
        source = (CANDIDATE / row['source_snapshot']).read_bytes()
        assert sha(source) == row['source_file_sha256']
        assert hashlib.sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest() == row['source_blob_sha1']
        start, end = row['source_byte_range_half_open']
        cstart, cend = row['candidate_byte_range_half_open']
        block = source[start:end]
        assert data[cstart:cend] == block and sha(block) == row['declaration_sha256']
        split = block.index(b':=') + 2
        assert sha(block[:split]) == row['header_sha256'] and sha(block[split:]) == row['proof_body_sha256']
        if row['role'] == 'existing_private_helper':
            old = NATIVE / row['source_path'].removeprefix('research/wu2008/src/')
            assert block in old.read_bytes(), row['name']
        remaining[cstart:cend] = b' ' * (cend - cstart)
        source_files[row['source_path']] = {'sha256': row['source_file_sha256'], 'git_blob_sha1': row['source_blob_sha1']}
        rows.append({'name': row['name'], 'visibility': row['visibility'],
                     'exact_published_header_and_proof_body': True, 'declaration_sha256': row['declaration_sha256']})
    spec = importlib.util.spec_from_file_location('proof_record', '/workspace/blue-build-tools/record_p6_repair.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    outside = [line.strip() for line in module.without_comments(remaining.decode()).splitlines() if line.strip()]
    assert outside == ['import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform',
                       'set_option autoImplicit false', 'open Set MeasureTheory Filter',
                       'open scoped BigOperators Topology', 'namespace LiLiuPrereqBuchstab',
                       'end LiLiuPrereqBuchstab'], outside
    assert len(rows) == 18 and sum(x['visibility'] == 'public' for x in rows) == 11
    assert 'buchstabPrimeKernel_abel_unrestricted' not in module.without_comments(data.decode())
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', module.without_comments(data.decode()))
    for boundary in manifest['unchanged_boundaries']:
        assert sha(Path(boundary['live_path']).read_bytes()) == boundary['sha256']
    selection = json.loads(Path('/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json').read_text())
    prefix = manifest['consumer']['new_import_prefix'].encode()
    consumer_modules = ['MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabUniform',
                        'MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform']
    adoption = [{'module': extension['module'], 'path': str(NATIVE / (extension['module'].replace('.', '/') + '.lean')),
                 'before': None, 'after': extension['sha256'], 'bytes': len(data), 'operation': 'create_missing_only'}]
    consumer_data = []
    for name in consumer_modules:
        selected = selection['native_sources'][name]
        path = Path(selected['installed_path'])
        before = path.read_bytes()
        assert sha(before) == selected['sha256']
        original = subprocess.check_output(['git', 'show', selected['source_commit'] + ':' + selected['source_path']], cwd=NATIVE)
        assert original == before
        assert hashlib.sha1(b'blob ' + str(len(before)).encode() + b'\0' + before).hexdigest() == selected['git_blob_sha1']
        short = name.split('.')[-1]
        assert (EVIDENCE / (short + '.before.lean')).read_bytes() == before
        after = prefix + before
        if name == manifest['consumer']['module']:
            assert after == (CANDIDATE / manifest['consumer']['candidate_path']).read_bytes()
        (EVIDENCE / (short + '.postimage.lean')).write_bytes(after)
        adoption.append({'module': name, 'path': str(path), 'before': sha(before), 'after': sha(after),
                         'before_bytes': len(before), 'bytes': len(after),
                         'operation': 'prepend_one_import_to_exact_baseline', 'exact_upstream_source': selected,
                         'all_original_bytes_preserved_as_suffix': True})
        consumer_data.append((path, before, after))
    review = {'schema': 'member_native_published_generic_extension_independent_static_review_v1',
              'result': 'PASS_EXACT_PUBLISHED_SLICES_AND_AUTHORIZED_IMPORT_ONLY_CONSUMERS',
              'reviewer': 'build_workflow', 'manifest_sha256': sha(manifest_path.read_bytes()),
              'published_commit': manifest['published_commit'], 'source_files_verified_by_sha256_and_git_blob': source_files,
              'declared_source_blocks': rows, 'public_blocks': 11, 'private_blocks': 7,
              'old_private_helpers_included_in_private_count': 6,
              'omitted_unused_public_block': 'buchstabPrimeKernel_abel_unrestricted; copied Ioc proof calls existing prime_abel_log_error_le directly',
              'other_executable_wrapper_commands': outside,
              'mathematical_scope': 'Same actual Buchstab/count objects; published arbitrary M>=2 and u0>1/epsilon>0 precede X; X precedes all x>=X and all u in [u0,M]. No M=100 specialization or new mathematical definition.',
              'consumer_scope': 'Only one new import before each exact upstream source; all original source bytes/statements/bodies/constants/assumptions retained.',
              'no_compiler_acceptance_claim': True}
    save(EVIDENCE / 'INDEPENDENT_STATIC_REVIEW.json', review)
    watched = [Path(row['path']) for row in adoption]
    save(EVIDENCE / 'ACTIVE_QUEUED_IMMEDIATE_PRE_ADOPTION.json', process_snapshot(watched))
    target = watched[0]
    assert not target.exists()
    with target.open('xb') as output:
        output.write(data)
    for path, before, after in consumer_data:
        process_snapshot(watched)
        assert path.read_bytes() == before
        descriptor, temporary = tempfile.mkstemp(prefix=path.name + '.adoption-', dir=path.parent)
        try:
            with os.fdopen(descriptor, 'wb') as output:
                output.write(after)
            assert path.read_bytes() == before
            os.replace(temporary, path)
        finally:
            if Path(temporary).exists():
                Path(temporary).unlink()
    for row in adoption:
        assert sha(Path(row['path']).read_bytes()) == row['after']
    for boundary in manifest['unchanged_boundaries']:
        assert sha(Path(boundary['live_path']).read_bytes()) == boundary['sha256']
    save(EVIDENCE / 'ADOPTION_RECEIPT.json', {'schema': 'member_native_published_generic_M_adoption_v1',
                                            'status': 'EXACT_SOURCE_ADOPTED_PENDING_LOCAL_COMPILE',
                                            'manifest_sha256': sha(manifest_path.read_bytes()),
                                            'files': adoption, 'old_providers_external_suppliers_and_pins_unchanged': True,
                                            'p6_project_source_or_cache_edited': False})
    print(json.dumps({'status': 'ADOPTED_PENDING_LOCAL_COMPILE', 'files': adoption}, ensure_ascii=False))


if __name__ == '__main__':
    main()
