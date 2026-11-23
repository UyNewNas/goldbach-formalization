#!/usr/bin/env python3
"""Publish completed, independently reviewed Member evidence without rerunning Lean."""
import hashlib
import json
import shutil
import restore_lossless_evidence as lossless
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

def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _relative_record(source, record):
    """Validate a regular, byte-exact relative artifact without changing it."""
    rel = Path(record['path'])
    _require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == record['path'],
             'Artifact path must be an exact relative path')
    path = source / rel
    _require(path.is_file() and not path.is_symlink(), f'Expected regular artifact: {path}')
    data = path.read_bytes()
    _require(type(record['bytes']) is int and len(data) == record['bytes']
             and hashlib.sha256(data).hexdigest() == record['sha256'],
             f'Artifact hash/size mismatch: {path}')
    return data


def _late_finalizer_record(source, manifest, review, original_entry):
    """Authenticate only the three explicitly reviewed finalizer-stdout formats."""
    publication_sha = sha(source / 'PUBLICATION_FILES.json')
    empty_entry = {'path': 'finalizer.log', 'bytes': 0,
                   'sha256': hashlib.sha256(b'').hexdigest()}
    _require(original_entry == empty_entry, 'Only the original empty finalizer entry may drift')
    binding_path = source / 'LATE_FINALIZER_LOG_BINDING.json'
    late_manifest_path = source / 'FINAL_REVIEW_NEW_FILES_MANIFEST.json'
    late_manifest = read(late_manifest_path)
    _require(late_manifest['original_publication_manifest_sha256'] == publication_sha
             and late_manifest.get('old_records_unchanged') is True,
             'Final review manifest must bind the original publication')
    additions = late_manifest['files']
    _require(len({x['path'] for x in additions}) == len(additions), 'Duplicate final review artifact')
    # Both the immutable binding and the very review accepting its sole finding
    # must already have exact hashes in the final-review additions manifest.
    for name in ['LATE_FINALIZER_LOG_BINDING.json', 'INDEPENDENT_REVIEW.json']:
        matches = [x for x in additions if x['path'] == name]
        _require(len(matches) == 1, f'Unbound late-review artifact: {name}')
        data = _relative_record(source, matches[0])
        if name == 'INDEPENDENT_REVIEW.json':
            _require(json.loads(data) == review, 'Review differs from bound review bytes')
    binding = read(binding_path)
    schema = binding['schema']
    outcome = review.get('outcome', review.get('status', review.get('result')))
    _require(str(outcome).startswith('PASS_'), 'Late stdout requires an accepting review')
    findings = review.get('findings', review.get('blocking_findings', review.get('review_findings')))
    _require(isinstance(findings, list) and len(findings) == 1, 'Exactly one late-stdout finding required')
    for key in ['blocking_findings', 'blocking_source_or_math_findings',
                'blocking_source_or_mathematical_findings', 'review_findings']:
        if key in review:
            _require(review[key] == [], f'Additional review findings cannot be suppressed: {key}')
    finding = findings[0]
    _require(finding.get('severity') == 'minor_metadata', 'Only the late stdout metadata finding is allowed')
    if schema == 'late_finalizer_stdout_manifest_binding_v1':
        _require(binding['original_publication_manifest_sha256'] == publication_sha
                 and binding['original_empty_finalizer_entry'] == empty_entry
                 and binding.get('original_records_unchanged_by_review') is True,
                 'Canonical late binding does not preserve the original manifest')
        actual = binding['actual_finalizer_log']
        final = binding['exact_stdout_equals_final_release']
        _require(actual['path'] == 'finalizer.log' and final['path'] == 'FINAL_RELEASE.json'
                 and final.get('byte_for_byte_equal') is True, 'Wrong canonical stdout/FINAL paths')
        impact = 'Only this auxiliary stdout manifest entry; normal/kernel/audit logs, selected sources, proof outputs and full-owned acceptance evidence are unaffected.'
        _require(set(finding) <= {'severity', 'path', 'summary', 'impact', 'disposition', 'source_or_validation_impact'}
                 and finding.get('path') == 'PUBLICATION_FILES.json / finalizer.log',
                 'Canonical finding must concern only the finalizer manifest entry')
        _require(('source_or_validation_impact' not in finding or finding['source_or_validation_impact'] is False)
                 and ('impact' not in finding or finding['impact'] is False or finding['impact'] == impact)
                 and (finding.get('source_or_validation_impact') is False
                      or finding.get('impact') is False or finding.get('impact') == impact),
                 'Source or validation impact cannot be waived')
        actual = {k: actual[k] for k in ['path', 'bytes', 'sha256']}
        final_record = {k: final[k] for k in ['path', 'bytes', 'sha256']}
    elif schema == 'immutable_late_finalizer_stdout_log_binding_v1':
        publication = binding['original_publication']
        _require(publication['path'] == str(source / 'PUBLICATION_FILES.json')
                 and publication['bytes'] == (source / 'PUBLICATION_FILES.json').stat().st_size
                 and publication['sha256'] == publication_sha
                 and binding['original_manifest_entry'] == empty_entry
                 and binding.get('old_records_unchanged') is True
                 and binding.get('original_manifest_and_log_not_rewritten') is True,
                 'Immutable late binding does not preserve the exact original publication')
        raw_actual = binding['actual_finalizer_log']
        raw_final = binding['actual_FINAL_RELEASE']
        _require(raw_actual['path'] == str(source / 'finalizer.log')
                 and raw_final['path'] == str(source / 'FINAL_RELEASE.json')
                 and binding.get('actual_finalizer_log_equals_FINAL_RELEASE_bytes') is True,
                 'Wrong immutable stdout/FINAL paths or equality flag')
        cause = 'Finalizer stdout appended the exact FINAL_RELEASE.json bytes after its publication manifest captured an empty log. Proof/source/validation logs are unaffected.'
        _require(set(finding) == {'severity', 'file', 'original_manifest_entry', 'current_actual',
                                 'cause', 'actual_log_equals_FINAL_RELEASE_original_bytes'}
                 and finding['file'] == 'finalizer.log'
                 and finding['original_manifest_entry'] == empty_entry
                 and finding['current_actual'] == raw_actual
                 and finding['actual_log_equals_FINAL_RELEASE_original_bytes'] is True
                 and finding['cause'] == binding['cause'] == cause,
                 'Immutable finding must describe only the exact unaffected late stdout')
        actual = {'path': 'finalizer.log', 'bytes': raw_actual['bytes'], 'sha256': raw_actual['sha256']}
        final_record = {'path': 'FINAL_RELEASE.json', 'bytes': raw_final['bytes'], 'sha256': raw_final['sha256']}
    elif schema == 'immutable_late_finalizer_stdout_binding_v1':
        publication = binding['original_publication_manifest']
        raw_final = binding['original_final_release']
        mismatch = binding['only_mismatch']
        raw_actual = mismatch['current_actual_file']
        _require(publication['path'] == str(source / 'PUBLICATION_FILES.json')
                 and publication['bytes'] == (source / 'PUBLICATION_FILES.json').stat().st_size
                 and publication['sha256'] == publication_sha
                 and raw_final['path'] == str(source / 'FINAL_RELEASE.json')
                 and mismatch['original_manifest_entry'] == empty_entry
                 and raw_actual['path'] == str(source / 'finalizer.log')
                 and binding.get('finalizer_stdout_bytes_exactly_equal_final_release') is True
                 and binding.get('permitted_publication_exception_exact_path') == 'finalizer.log'
                 and binding.get('old_manifest_log_release_result_source_objects_unchanged') is True
                 and binding['publication_entry_count'] == len(manifest.get('files', manifest.get('publication_files')))
                 and binding['other_original_entries_rehashed_and_exact'] == binding['publication_entry_count'] - 1,
                 'Third late format must bind only the same exact empty stdout entry')
        impact = 'Only this auxiliary stdout manifest entry; normal/kernel/audit logs, selected sources, proof outputs and full-owned acceptance evidence are unaffected.'
        _require(set(finding) <= {'severity', 'path', 'summary', 'impact', 'disposition', 'source_or_validation_impact'}
                 and finding.get('path') == 'PUBLICATION_FILES.json / finalizer.log',
                 'Canonical finding must concern only the finalizer manifest entry')
        _require(('source_or_validation_impact' not in finding or finding['source_or_validation_impact'] is False)
                 and ('impact' not in finding or finding['impact'] is False or finding['impact'] == impact)
                 and (finding.get('source_or_validation_impact') is False
                      or finding.get('impact') is False or finding.get('impact') == impact),
                 'Source or validation impact cannot be waived')
        actual = {'path': 'finalizer.log', 'bytes': raw_actual['bytes'], 'sha256': raw_actual['sha256']}
        final_record = {'path': 'FINAL_RELEASE.json', 'bytes': raw_final['bytes'], 'sha256': raw_final['sha256']}
    else:
        raise ValueError('Unsupported late finalizer binding schema')
    stdout = _relative_record(source, actual)
    final_bytes = _relative_record(source, final_record)
    _require(stdout == final_bytes, 'Finalizer stdout must equal FINAL_RELEASE byte for byte')
    _require(json.loads(final_bytes)['publication_files_sha256'] == publication_sha,
             'FINAL_RELEASE must refer to the same original publication')
    return actual, {
        'path': 'finalizer.log', 'binding_schema': schema,
        'binding_path': binding_path.name, 'binding_sha256': sha(binding_path),
        'final_review_manifest_sha256': sha(late_manifest_path),
        'original_manifest_sha256': publication_sha,
        'original_manifest_entry': dict(original_entry), 'actual_finalizer_log': actual,
        'actual_FINAL_RELEASE': final_record, 'stdout_equals_FINAL_RELEASE_bytes': True,
        'original_manifest_current_exact': False,
        'scope': 'Only the empty finalizer stdout entry; all source, proof output and other artifact records remain strict.',
    }


def prepare_publication_files(source, manifest, review):
    """Read-only gate: return exact copy records plus at most one bound stdout exception."""
    original = manifest.get('files', manifest.get('publication_files'))
    _require(isinstance(original, list), 'Missing publication file list')
    files = [dict(record) for record in original]
    _require(len({x['path'] for x in files}) == len(files), 'Duplicate publication artifact')
    exception = None
    for index, record in enumerate(files):
        if record['path'] == 'finalizer.log':
            path = source / record['path']
            if path.stat().st_size != record['bytes'] or sha(path) != record['sha256']:
                files[index], exception = _late_finalizer_record(source, manifest, review, record)
                continue
        if lossless.is_large_evidence(record):
            lossless.validate_raw(source, record)
        else:
            _relative_record(source, record)
    return files, exception


LOSSLESS_HELPER_BYTES = 12953
LOSSLESS_HELPER_SHA256 = '37a595c62167d5773b370490b824d50989f25166842f5d4d0bf7ec3137af5f15'


def preflight_publication_carriers(source, destination, files):
    large = [record for record in files if lossless.is_large_evidence(record)]
    if not large:
        return
    _require(lossless.digest_file(Path(lossless.__file__))
             == (LOSSLESS_HELPER_BYTES, LOSSLESS_HELPER_SHA256),
             'Lossless helper differs from the independently reviewed bytes')
    raw_paths = {record['path'] for record in files}
    reserved = {'LOSSLESS_ARTIFACTS.json', 'restore_lossless_evidence.py'}
    reserved.update(record['path'] + '.gz' for record in large)
    _require(not raw_paths.intersection(reserved), 'Carrier/metadata collides with an original raw record')
    for record in large:
        lossless.preflight_destination(destination, record)


def copy_publication_artifact(source, destination, record):
    if lossless.is_large_evidence(record):
        return lossless.create_carrier(source, destination, record)
    out = destination / record['path']
    out.parent.mkdir(parents=True, exist_ok=True)
    if not out.exists():
        shutil.copyfile(source / record['path'], out)
    assert sha(out) == record['sha256']
    return {'raw': dict(record), 'repository': dict(record)}


def main(argv=None):
    overrides_path = repo / base / 'MEMBER_SOURCE_OVERRIDES.json'
    overrides = read(overrides_path)
    existing = {x['module'] for x in overrides['source_overrides']}
    published = []
    staging_paths = []
    for key in (sys.argv[1:] if argv is None else argv):
        mask = key == 'mask'
        source = Path('/workspace/blue-mask-transport-repair' if mask else '/workspace/blue-member-import-repair' if key == 'import' else f'/workspace/blue-member-repair-batch{key}')
        destination = repo / base / ('member-mask-transport' if mask else 'member-import-repair' if key == 'import' else f'member-repair-batch{key}')
        manifest = read(source / 'PUBLICATION_FILES.json')
        review = read(source / 'INDEPENDENT_REVIEW.json')
        files, finalizer_exception = prepare_publication_files(source, manifest, review)
        findings = review.get('findings', review.get('blocking_findings', review.get('review_findings')))
        outcome = review.get('outcome', review.get('status', review.get('result')))
        if finalizer_exception is not None:
            # Only the exact single late-stdout finding was authenticated above;
            # keep the original review bytes and record this exception in integrity.
            findings = []
        elif findings and all(x.get('severity') == 'ALREADY_CLARIFIED_METADATA_LABEL' for x in findings):
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
        # files already passed strict checks, with only the authenticated stdout replacement.
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
        preflight_publication_carriers(source, destination, files)
        for f in files:
            rel = Path(f['path'])
            assert not rel.is_absolute() and '..' not in rel.parts
            path = source / rel
            assert path.stat().st_size == f['bytes'] and sha(path) == f['sha256'], path
            out = destination / rel
            if lossless.is_large_evidence(f):
                lossless.preflight_destination(destination, f)
            elif out.exists():
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
        artifacts = [copy_publication_artifact(source, destination, f) for f in files]
        carriers = [row for row in artifacts if 'carrier' in row]
        small_files = [row['repository'] for row in artifacts if 'repository' in row]
        lossless_integrity = (lossless.finish_publication(destination, carriers,
                              sha(source / 'PUBLICATION_FILES.json'), small_files)
                              if carriers else {})
        write(destination / 'PUBLICATION_INTEGRITY.json', {
            'schema': 'member_verified_batch_publication_integrity_v1',
            'result': ('PASS_SOURCE_OUTPUT_AND_REVIEW_WITH_BOUND_LATE_FINALIZER_STDOUT'
                       if finalizer_exception else 'PASS_EXACT_MANIFEST_SOURCE_OUTPUT_AND_INDEPENDENT_REVIEW_BINDINGS'),
            'original_manifest_exception': finalizer_exception,
            'original_manifest_current_exact': finalizer_exception is None,
            'original_manifest_entries_current_exact': len(manifest.get('files', manifest.get('publication_files'))) - int(finalizer_exception is not None),
            'original_manifest_sha256': sha(source / 'PUBLICATION_FILES.json'), 'files': files,
            'relative_module_subdirectories_preserved': True,
            'source_and_five_outputs_current_hashes_rechecked': True,
            'public_exports': sum(counts.values()), 'public_exports_by_module': counts,
            'full_owned_including_private_generated': results.get('full_owned_including_private_generated', False),
            'owned_exports_by_module': results.get('owned_export_counts'),
            'main_absent_sources_remain_explicit_postimages': True,
            'raw_evidence_bytes_preserved': True, 'successful_Lean_checks_repeated': False,
            'board_node_mapping_verified': False,
            **lossless_integrity,
        })
        staging_paths.append(str(destination.relative_to(repo)))
        published.append({'key': key, 'files': len(files), 'modules': len(selection), 'public_exports': sum(counts.values())})

    overrides['scope'] = 'Verified Member project postimages, plus separately registered native source overlay. Stage-only modules have explicit postimage/install paths; frozen archives remain unchanged. These batches do not establish complete board coverage.'
    write(overrides_path, overrides)
    write(Path('/workspace/blue-build-tools/MEMBER_LAST_PUBLICATION_PATHS.json'), {'staging_paths': staging_paths + [str(overrides_path.relative_to(repo))], 'batches': published})
    print(json.dumps({'batches': published, 'total_member_source_overrides': len(overrides['source_overrides'])}))


if __name__ == '__main__':
    main()
