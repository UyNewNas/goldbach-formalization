#!/usr/bin/env python3
"""Local-only mapping preparation; inspect old evidence, never run Lean."""
import hashlib
import json
from pathlib import Path
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
REMOTE = '/workspace/p25-q96-20261125'
EVIDENCE = REPO / 'docs/verification/20261126-p2-5-resumed'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    template = json.loads((HERE / 'RECOVERY_MANIFEST.template.json').read_text())
    consumer_path = EVIDENCE / 'consumer-attempt005/RESULT.json'
    consumer = json.loads(consumer_path.read_text())
    inventory_path = EVIDENCE / 'p3-cache-recovery/RECOVERY_MANIFEST.json'
    inventory = json.loads(inventory_path.read_text())
    witness_path = EVIDENCE / 'p3-cache-recovery/expected-original-witnesses.json'
    witnesses = json.loads(witness_path.read_text())['snapshot']['files']
    requirements = {r['required_path']: r['expected_sha256']
                    for r in template['historical_artifact_requirements']}
    for r in witnesses:
        requirements[r['realpath']] = r['sha256']
    # Publication-bound source inputs are immutable even if never cached before.
    for spec in consumer['source_graph'].values():
        requirements[REMOTE + '/' + spec['path']] = spec['source_sha256']
    sources = {}
    for r in template['historical_artifact_requirements']:
        local = r.get('verified_source')
        if local:
            p = REPO / local['path']
            if p.is_file() and sha(p) == r['expected_sha256']:
                sources.setdefault(r['expected_sha256'], []).append(
                    {'kind': 'repo_file', 'path': local['path'], 'bytes': p.stat().st_size})
    for spec in consumer['source_graph'].values():
        p = REPO / spec['path']
        if p.is_file() and sha(p) == spec['source_sha256']:
            sources.setdefault(spec['source_sha256'], []).append(
                {'kind': 'repo_file', 'path': spec['path'], 'bytes': p.stat().st_size})
    wanted = set(requirements.values())
    basenames = {Path(p).name for p in requirements}
    # Old executed runners have different basenames from their published files.
    # Bind those already present source bytes by hash, without regenerating them.
    for directory in [EVIDENCE, REPO / 'docs/verification/20261126-p2-5-continuation']:
        for p in directory.glob('*.py'):
            h = sha(p)
            if h in wanted:
                sources.setdefault(h, []).append({'kind':'repo_file',
                    'path':str(p.relative_to(REPO)), 'bytes':p.stat().st_size})
    archives = sorted((REPO / 'docs/verification/20261126-p2-5-continuation').glob('*.tar.*'))
    archives += sorted((REPO / 'docs/verification/20261126-p2-5-continuation/cell00-five-consumers/review-fixes').glob('*.tar.*'))
    archive_records = []
    # The separate 41-object inventory owns compiled-object discovery. Only
    # historical non-object members are inspected here, once per known archive.
    for archive in archives:
        archive_sha = sha(archive)
        rel = str(archive.relative_to(REPO))
        archive_records.append({'path': rel, 'sha256': archive_sha,
                                'bytes': archive.stat().st_size})
        if archive_sha in wanted:
            sources.setdefault(archive_sha, []).append(
                {'kind': 'repo_file', 'path': rel, 'bytes': archive.stat().st_size})
        with tarfile.open(archive, 'r|*') as tf:
            for member in tf:
                if (not member.isfile() or member.name.endswith(('.olean', '.ilean'))
                        or Path(member.name).name not in basenames):
                    continue
                assert member.size <= 256 * 1024 * 1024
                stream = tf.extractfile(member)
                h = hashlib.sha256()
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    h.update(block)
                digest = h.hexdigest()
                if digest in wanted:
                    sources.setdefault(digest, []).append({'kind': 'repo_archive',
                        'path': rel, 'archive_sha256': archive_sha,
                        'member': member.name, 'bytes': member.size})
    objects = {}
    for module, row in inventory['objects'].items():
        # Final P3 locations must enter the resolver before any missing object
        # can be selected for normal rematerialization. No new search is made.
        for location in row['verified_locations']:
            if location.get('environment') != 'P3' or location.get('matches') is not True:
                continue
            assert location['sha256'] == row['historical_object_sha256']
            if location['kind'] == 'file':
                source = {'kind':'remote_file','path':location['path'],'bytes':location['bytes']}
            elif location['kind'] == 'archive_member':
                source = {'kind':'remote_archive','path':location['archive'],
                          'member':location['member'],'bytes':location['bytes']}
            else:
                raise ValueError('Unknown verified P3 source kind')
            sources.setdefault(location['sha256'], []).append(source)
        spec = consumer['source_graph'][module]
        objects[module] = {'sha256': row['historical_object_sha256'],
            'source': spec['path'], 'source_sha256': spec['source_sha256'],
            'project_imports': spec['project_imports'],
            'aliases': sorted(p for p, h in requirements.items()
                              if h == row['historical_object_sha256'] and p.endswith('.olean'))}
    cfg = {'schema': 'p25-cache-rematerialization-selection-v1', 'target_root': REMOTE,
        'consumer_receipt': {'path': str(consumer_path.relative_to(REPO)), 'sha256': sha(consumer_path)},
        'witness_manifest': {'path': str(witness_path.relative_to(REPO)), 'sha256': sha(witness_path)},
        'object_inventory': {'path':str(inventory_path.relative_to(REPO)), 'sha256':sha(inventory_path)},
        'p3_object_inventory_complete': inventory.get('scope', {}).get('p3_41_scan_completed') is True
             and type(inventory.get('scope', {}).get('p3_scan_exit_code')) is int
             and inventory['scope']['p3_scan_exit_code'] == 0
             and any(r.get('environment') == 'P3' and r.get('files_scanned', 0) > 0
                     for r in inventory['scan_scope_and_errors']),
        'requirements': [{'path': p, 'sha256': h} for p, h in sorted(requirements.items())],
        'sources_by_sha256': {h: list({json.dumps(r, sort_keys=True): r for r in rows}.values())
                             for h, rows in sorted(sources.items())},
        'objects': objects, 'allowed_normal_rebuild_modules': sorted(inventory['missing_modules']),
        'runtime': template['runtime'], 'witnesses': witnesses,
        'cas_archives': ['/workspace/rescue-export-20261126/' + x for x in
                         ['core-residual.tar.xz', 'priority-objects.tar.xz',
                          'evidence-receipts.tar.xz', 'remaining-archives.tar.xz']],
        'archive_mapping_inputs': archive_records,
        'initial_free_reserve_bytes': 320 * 1024 * 1024,
        'per_stage_free_reserve_bytes': 256 * 1024 * 1024,
        'normal_stage_wall_seconds': 600,
        'forbidden_v7_target_objects': [REMOTE + '/.lake/diagnostic/' + attempt +
             '/lib/' + m.replace('.', '/') + '.olean'
             for attempt, modules in [('p25-cell00-five-consumers-attempt004', consumer['module_order']),
                 ('p25-cell00-five-consumers-attempt005', consumer['module_order'][1:])]
             for m in modules],
        'future_v7_output': REMOTE + '/.lake/diagnostic/p25-cell00-four-consumers-attempt007'}
    (HERE / 'RECOVERY_SELECTION.json').write_text(json.dumps(cfg, ensure_ascii=False, indent=2) + '\n')
    missing = [{'sha256': h, 'required_paths': [p for p, digest in requirements.items() if digest == h],
                'is_project_object': h in {r['sha256'] for r in objects.values()}}
               for h in sorted(wanted - set(sources))]
    summary = {'schema': 'p25-offline-recovery-mapping-v1',
        'status': 'LOCAL_MAPPING_ONLY_NO_CLOUD_OR_LEAN_EXECUTION',
        'selection_sha256': sha(HERE / 'RECOVERY_SELECTION.json'),
        'required_path_count': len(requirements), 'unique_required_hash_count': len(wanted),
        'unique_hashes_with_declared_source': len(wanted & set(sources)),
        'unique_hashes_with_repository_source': sum(h in wanted and any(
            r['kind'].startswith('repo_') for r in rows) for h, rows in sources.items()),
        'pending_cas_external_payload_or_existing_target_resolution': missing}
    (HERE / 'OFFLINE_MAPPING_REPORT.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items()
                      if k != 'pending_cas_external_payload_or_existing_target_resolution'}))
    print('PENDING_UNIQUE_HASHES', len(missing))


if __name__ == '__main__':
    main()
