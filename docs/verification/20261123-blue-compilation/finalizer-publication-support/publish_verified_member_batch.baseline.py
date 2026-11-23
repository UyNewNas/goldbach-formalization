#!/usr/bin/env python3
"""Publish completed, independently reviewed Member evidence without rerunning Lean."""
import hashlib
import json
import shutil
import sys
from pathlib import Path

repo = Path('/workspace/goldbach-formalization')
base = Path('docs/verification/20261123-blue-compilation')
member = Path('/workspace/blue-member-build')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def write(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')

overrides_path = repo / base / 'MEMBER_SOURCE_OVERRIDES.json'
overrides = read(overrides_path)
existing = {x['module'] for x in overrides['source_overrides']}
published = []
staging_paths = []
for key in sys.argv[1:]:
    mask = key == 'mask'
    source = Path('/workspace/blue-mask-transport-repair' if mask else '/workspace/blue-member-import-repair' if key == 'import' else f'/workspace/blue-member-repair-batch{key}')
    destination = repo / base / ('member-mask-transport' if mask else 'member-import-repair' if key == 'import' else f'member-repair-batch{key}')
    manifest = read(source / 'PUBLICATION_FILES.json')
    review = read(source / 'INDEPENDENT_REVIEW.json')
    findings = review.get('findings', review.get('blocking_findings', review.get('review_findings')))
    outcome = review.get('outcome', review.get('status', review.get('result')))
    if findings and all(x.get('severity') == 'ALREADY_CLARIFIED_METADATA_LABEL' for x in findings):
        assert outcome == 'PASS_INDEPENDENT_REVIEW'
        for finding in findings:
            assert finding['source_or_validation_impact'] is False
            assert finding['additional_clarification_needed'] is False
            clarification = finding['pre_release_clarification']
            path = Path(clarification['path'])
            assert path.parent == source
            assert path.stat().st_size == clarification['bytes'] and sha(path) == clarification['sha256']
            assert any(x['path'] == path.name and x['sha256'] == clarification['sha256'] for x in manifest.get('files', manifest.get('publication_files')))
        findings = []  # The original review and already-bound clarification stay unchanged.
    required_supplement = None
    if findings:
        assert review.get('blocking_source_or_math_findings', review.get('blocking_source_or_mathematical_findings')) == []
        assert all(x.get('severity') == 'minor_metadata' for x in findings)
        assert (source / 'PUBLICATION_ADDENDUM.json').exists(), 'Required metadata supplement must be bound before publication'
        if outcome == 'PASS_SOURCE_MATHEMATICS_IDENTITY_AND_RECORDED_VALIDATION_WITH_METADATA_CLARIFICATION':
            complete = read(source / 'PUBLIC_HEADERS_COMPLETE.json')
            assert complete['all_complete_headers_byte_exact'] and complete['all_definition_chunks_byte_exact']
            required_supplement = 'PUBLIC_HEADERS_COMPLETE.json'
        elif outcome == 'PASS_SOURCE_MATHEMATICS_AND_RECORDED_255_PUBLIC_VALIDATION_WITH_METADATA_SUPPLEMENT':
            complete = read(source / 'LOG_POINT_FULL_HEADERS_REVIEW.json')
            assert complete['actual_public_theorems'] == 27 and complete['comment_false_declaration_retains_excluded']
            assert len(complete['headers']) == 27
            for header in complete['headers']:
                assert header['complete_header_before'] == header['complete_header_after']
                assert hashlib.sha256(header['complete_header_before'].encode()).hexdigest() == header['header_sha256_before'] == header['header_sha256_after']
            required_supplement = 'LOG_POINT_FULL_HEADERS_REVIEW.json'
        else:
            assert outcome == 'PASS_SOURCE_SCOPE_IDENTITY_AND_RECORDED_VALIDATION_WITH_MINOR_METADATA_CLARIFICATION'
            correction = read(source / 'PUBLICATION_ADDENDUM.json')['metadata_correction']
            assert correction['module'] == 'ImbalancedChen.CurrentChenUpsilon10OverlapDivisorSplit'
            assert correction['field'] == 'neutral_verification_pointer_before_first_canonical_compile'
            assert correction['recorded_value'] is True and correction['actual_value'] is False
    else:
        assert findings == [], source
        if outcome == 'NO_BLOCKING_FINDINGS_METADATA_CLARIFICATION_RECORDED':
            assert review['reviewer_is_candidate_author'] is False
            assert review['metadata_notes']
        else:
            assert str(outcome).startswith(('NO_FINDINGS', 'PASS_')) or outcome == 'NO_SOURCE_MATHEMATICAL_OR_EVIDENCE_BLOCKER_FOUND', source
    results = read(source / 'VALIDATION_RESULTS.json')
    assert results['only_standard_axioms']
    assert results['status'].startswith('PASS_')
    if mask:
        selection = {results['module']: read(source / 'REPAIR_RECEIPT.json')['source_selection']}
        snapshots = {results['module']: results['source_plus_five_outputs']}
        counts = {results['module']: results['all_environment_public_exports']}
        assert all(x['exit_code'] == 0 for x in results['stages'])
        assert results['source_and_all_five_outputs_unchanged_across_kernel_audit']
    else:
        release = read(source / 'FINAL_RELEASE.json')
        assert sha(source / 'PUBLICATION_FILES.json') == release['publication_files_sha256']
        assert sha(source / 'VALIDATION_RESULTS.json') == release['validation_results_sha256']
        assert release['normal_kernel_audit_all_exit0']
        selection = read(source / 'SOURCE_SELECTION.json')
        snapshots = results['source_plus_five_outputs']
        counts = results['public_export_counts']
        assert all(x['exit_code'] == 0 for x in results['normal_commands'])
        assert all(x['exit_code'] == 0 for x in results['kernel_commands'])
        assert results['audit_command']['exit_code'] == 0
        assert results['source_plus_five_outputs_unchanged_across_kernel_and_audit']
    for module, items in snapshots.items():
        for rel, record in items.items():
            path = member / rel
            assert path.stat().st_size == record['bytes'] and sha(path) == record['sha256'], path
    files = list(manifest.get('files', manifest.get('publication_files')))
    assert len({f['path'] for f in files}) == len(files), source
    for name in ['PUBLICATION_FILES.json', 'INDEPENDENT_REVIEW.json', 'PUBLICATION_ADDENDUM.json', 'FINAL_RELEASE.json', 'INDEPENDENT_REVIEW_FILES.json', 'PREPARED_INDEPENDENT_REVIEW.json', 'FINAL_REVIEW_NEW_FILES_MANIFEST.json']:
        path = source / name
        if path.exists() and name not in {f['path'] for f in files}:
            files.append({'path': name, 'sha256': sha(path), 'bytes': path.stat().st_size})
    independent_files = source / 'INDEPENDENT_REVIEW_FILES.json'
    if independent_files.exists():
        late = read(independent_files)
        reference = late.get('base_publication_manifest', late.get('original_publication_manifest', late.get('original_manifest')))
        reference_sha = reference['sha256'] if reference else late.get('original_PUBLICATION_FILES_sha256')
        assert reference_sha == sha(source / 'PUBLICATION_FILES.json')
        if 'original_FINAL_RELEASE_sha256' in late:
            assert late['original_FINAL_RELEASE_sha256'] == sha(source / 'FINAL_RELEASE.json')
        if 'original_release' in late:
            assert late['original_release']['sha256'] == sha(source / 'FINAL_RELEASE.json')
        additions = late.get('files_to_add_separately', late.get('new_files_to_add_separately', late.get('new_files', late.get('files', []))))
        for item in additions:
            rel = Path(item['path'])
            if rel.is_absolute():
                rel = rel.relative_to(source)
            normalized = {'path': str(rel), 'bytes': item['bytes'], 'sha256': item['sha256']}
            duplicate = next((f for f in files if f['path'] == str(rel)), None)
            if duplicate is None:
                files.append(normalized)
            else:
                assert duplicate['sha256'] == normalized['sha256']
    final_review_files = source / 'FINAL_REVIEW_NEW_FILES_MANIFEST.json'
    if final_review_files.exists():
        late = read(final_review_files)
        assert late['original_publication_manifest_sha256'] == sha(source / 'PUBLICATION_FILES.json')
        assert (late.get('old_manifest_or_evidence_modified') is False
                or late.get('old_records_unchanged') is True)
        for item in late['files']:
            rel = Path(item['path'])
            assert not rel.is_absolute() and '..' not in rel.parts
            duplicate = next((f for f in files if f['path'] == str(rel)), None)
            if duplicate is None:
                files.append(item)
            else:
                assert duplicate['sha256'] == item['sha256'] and duplicate['bytes'] == item['bytes']
    if (source / 'PUBLICATION_ADDENDUM.json').exists():
        addendum = read(source / 'PUBLICATION_ADDENDUM.json')
        assert addendum['original_publication_manifest_sha256'] == sha(source / 'PUBLICATION_FILES.json')
        additions = addendum.get('additional_files', [addendum['additional_file']] if 'additional_file' in addendum else [])
        assert any(x['path'] == 'INDEPENDENT_REVIEW.json' and x['sha256'] == sha(source / 'INDEPENDENT_REVIEW.json') for x in additions)
        if required_supplement:
            assert any(x['path'] == required_supplement and x['sha256'] == sha(source / required_supplement) for x in additions)
        for item in additions:
            if item['path'] not in {f['path'] for f in files}:
                files.append(item)
    for f in files:
        rel = Path(f['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        path = source / rel
        assert path.stat().st_size == f['bytes'] and sha(path) == f['sha256'], path
        out = destination / rel
        if out.exists():
            assert sha(out) == f['sha256'], out
    for module, info in selection.items():
        assert module not in existing, module
        name = module.split('.')[-1]
        canonical = Path(module.replace('.', '/') + '.lean')
        prefix = Path('.') if mask else Path(name)
        before = source / prefix / 'baseline.lean'
        after = source / prefix / 'candidate.lean'
        assert sha(before) == info['preimage_sha256']
        assert sha(after) == info['postimage_sha256'] == sha(member / canonical)
        main_exists = (repo / canonical).exists()
        main_matches = main_exists and sha(repo / canonical) == info['postimage_sha256']
        if main_matches:
            postimage = canonical
            staging_paths.append(str(canonical))
        else:
            if main_exists:
                # A selected historical module may share a name with a different
                # canonical draft. Keep that file intact and publish the exact
                # accepted source only as an explicit isolated install overlay.
                assert not mask
                recorded_main = release['actual_source_readback'][module]
                assert recorded_main['main_exists']
                assert sha(repo / canonical) == recorded_main['main_source_sha256']
            postimage = destination.relative_to(repo) / prefix / 'candidate.lean'
        entry = {
            'module': module, 'install_path': str(canonical),
            'preimage': {'source_location': 'published_byte_exact_baseline', 'repository_path': str(destination.relative_to(repo) / prefix / 'baseline.lean'), 'sha256': info['preimage_sha256']},
            'postimage': {'source_location': 'this_tree', 'repository_path': str(postimage), 'sha256': info['postimage_sha256']},
            'main_canonical_source_created': False,
            'main_canonical_source_exists': main_exists,
            'main_canonical_source_matches_postimage': main_matches,
            'validation': 'normal_lake_named_module_kernel_all_environment_public_types_axioms_passed',
            'audited_environment_public_exports': counts[module],
            'module_source_record': str(destination.relative_to(repo / base) / ('REPAIR_RECEIPT.json' if mask else 'SOURCE_SELECTION.json')),
            'independent_review': str(destination.relative_to(repo / base) / 'INDEPENDENT_REVIEW.json'),
        }
        if main_exists and not main_matches:
            entry['different_main_canonical_source_preserved_sha256'] = sha(repo / canonical)
        if results.get('full_owned_including_private_generated'):
            entry['full_owned_including_private_generated'] = True
            entry['audited_environment_owned_exports'] = results['owned_export_counts'][module]
            entry['validation'] = 'normal_lake_named_module_kernel_all_environment_owned_types_axioms_including_private_generated_passed'
        overrides['source_overrides'].append(entry)
        existing.add(module)
    for f in files:
        out = destination / f['path']
        out.parent.mkdir(parents=True, exist_ok=True)
        if not out.exists():
            shutil.copyfile(source / f['path'], out)
        assert sha(out) == f['sha256']
    write(destination / 'PUBLICATION_INTEGRITY.json', {
        'schema': 'member_verified_batch_publication_integrity_v1',
        'result': 'PASS_EXACT_MANIFEST_SOURCE_OUTPUT_AND_INDEPENDENT_REVIEW_BINDINGS',
        'original_manifest_sha256': sha(source / 'PUBLICATION_FILES.json'), 'files': files,
        'relative_module_subdirectories_preserved': True,
        'source_and_five_outputs_current_hashes_rechecked': True,
        'public_exports': sum(counts.values()), 'public_exports_by_module': counts,
        'full_owned_including_private_generated': results.get('full_owned_including_private_generated', False),
        'owned_exports_by_module': results.get('owned_export_counts'),
        'main_absent_sources_remain_explicit_postimages': True,
        'raw_evidence_bytes_preserved': True, 'successful_Lean_checks_repeated': False,
        'board_node_mapping_verified': False,
    })
    staging_paths.append(str(destination.relative_to(repo)))
    published.append({'key': key, 'files': len(files), 'modules': len(selection), 'public_exports': sum(counts.values())})

overrides['scope'] = 'Verified Member project postimages, plus separately registered native source overlay. Stage-only modules have explicit postimage/install paths; frozen archives remain unchanged. These batches do not establish complete board coverage.'
write(overrides_path, overrides)
write(Path('/workspace/blue-build-tools/MEMBER_LAST_PUBLICATION_PATHS.json'), {'staging_paths': staging_paths + [str(overrides_path.relative_to(repo))], 'batches': published})
print(json.dumps({'batches': published, 'total_member_source_overrides': len(overrides['source_overrides'])}))
