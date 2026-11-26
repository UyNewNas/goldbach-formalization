"""Prepare exact, locally checked deduplication of shape transport views.

No remote calls or Git mutations. The complete original artifacts remain intact.
The published binary archive and four small files suffice to recreate all saved
chunk bytes, JSON stdout and base64 transport pages without recompressing gzip.
"""
from pathlib import Path
import base64
import hashlib
import json

SOURCE = Path('/tmp/p24-canonical-A-shape-evidence-20261126')
OUTPUT = Path('/tmp/p24-integration-repairs-20261126/canonical-a-draft02-prepared-inputs')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fingerprint(path):
    raw = path.read_bytes()
    return {'origin': str(path), 'bytes': len(raw), 'sha256': sha(raw)}


def same(raw, original):
    assert raw == original.read_bytes(), original
    return fingerprint(original)


def pages_spec(path, stdout):
    pages = json.loads(path.read_bytes())
    metadata = []
    restored = []
    for page in pages:
        assert base64.b64decode(page['output_base64'], validate=True) == stdout[page['offset']:page['next_offset']]
        row = dict(page)
        row['output_base64'] = None  # Keep the exact key position for JSON reconstruction.
        metadata.append(row)
        out = dict(row)
        out['output_base64'] = base64.b64encode(stdout[row['offset']:row['next_offset']]).decode()
        restored.append(out)
    raw = (json.dumps(restored, ensure_ascii=False, indent=2) + '\n').encode()
    return {'pages': metadata, 'original': same(raw, path)}


def main():
    OUTPUT.mkdir(exist_ok=False)
    artifacts = {}
    for name in ['blocks.stdout.log.gz', 'shape-diagnostic.json', 'complete-block-summary.json.gz',
                 'complete-block-owned-link.json.gz', 'InspectBlocks.lean']:
        artifacts[name] = fingerprint(SOURCE / name)
    archive = (SOURCE / 'blocks.stdout.log.gz').read_bytes()
    assert len(archive) == 7577341 and sha(archive) == '709c2f0d26d4481f2845edd7d2726e677842eda447f455297178dab7259a25d0'
    encoded_files = []
    for name in ['complete-block-summary.json.gz', 'complete-block-owned-link.json.gz']:
        data = (SOURCE / name).read_bytes()
        text = base64.b64encode(data) + b'\n'
        destination = OUTPUT / (name + '.base64')
        destination.write_bytes(text)
        assert base64.b64decode(destination.read_bytes(), validate=False) == data
        encoded_files.append({'encoded': fingerprint(destination), 'original': artifacts[name],
                              'encoding': 'base64 with one terminal newline'})

    chunks = []
    duplicate_bytes = 0
    for index in range(8):
        prefix = SOURCE / 'chunks' / f'chunk-{index:02d}'
        log_path = prefix.with_name(prefix.name + '-task.log')
        output = log_path.read_bytes()
        marker = 'P24_A_SHAPE_CHUNK '
        assert output.startswith(marker.encode())
        record = json.loads(output[len(marker):])
        data = archive[record['offset']:record['end']]
        assert base64.b64decode(record.pop('data'), validate=True) == data
        restored_record = dict(record, data=base64.b64encode(data).decode())
        stdout = (marker + json.dumps(restored_record, sort_keys=True) + '\n').encode()
        entry = {'index': index, 'record_without_data': record, 'marker': marker,
                 'binary_chunk': same(data, prefix.with_suffix('.bin')),
                 'task_stdout': same(stdout, log_path),
                 'output_pages': pages_spec(prefix.with_name(prefix.name + '-output-pages.json'), stdout)}
        duplicate_bytes += entry['binary_chunk']['bytes'] + entry['task_stdout']['bytes'] + entry['output_pages']['original']['bytes']
        chunks.append(entry)

    metadata_log = (SOURCE / 'metadata-task.log').read_bytes()
    marker = 'P24_A_SHAPE_METADATA '
    meta = json.loads(metadata_log[len(marker):])
    names = list(meta['payloads'])
    for name in names:
        assert base64.b64decode(meta['payloads'][name], validate=True) == (SOURCE / name).read_bytes()
    del meta['payloads']
    restored_meta = dict(meta, payloads={name: base64.b64encode((SOURCE / name).read_bytes()).decode() for name in names})
    restored_stdout = (marker + json.dumps(restored_meta, sort_keys=True) + '\n').encode()
    metadata = {'record_without_payloads': meta, 'payload_file_names': names, 'marker': marker,
                'task_stdout': same(restored_stdout, SOURCE / 'metadata-task.log'),
                'output_pages': pages_spec(SOURCE / 'metadata-output-pages.json', restored_stdout)}
    duplicate_bytes += metadata['task_stdout']['bytes'] + metadata['output_pages']['original']['bytes']
    original_stdout = (SOURCE / 'original-shape-task.log').read_bytes()
    original_task = {'published_stdout': fingerprint(SOURCE / 'original-shape-task.log'),
                     'output_pages': pages_spec(SOURCE / 'original-shape-task-output-pages.json', original_stdout)}
    duplicate_bytes += original_task['output_pages']['original']['bytes']
    result = {'schema': 1, 'purpose': 'Exact reversible transport-view deduplication; not evidence omission or gate credit.',
              'complete_originals_retained_locally': True, 'original_files_deleted_or_changed': False,
              'archive_blob_sha': 'a0d5c412533cd98ca31babfe996d8b9fc48730ce', 'artifacts': artifacts,
              'base64_preserved_small_gzips': encoded_files, 'chunks': chunks,
              'metadata_task': metadata, 'original_shape_task': original_task,
              'every_reconstructed_chunk_stdout_and_page_file_byte_equal_locally': True,
              'duplicate_transport_bytes_represented_reversibly': duplicate_bytes,
              'json_stdout_recipe': 'marker + json.dumps(record, sort_keys=True) + single newline; original metadata fields preserved',
              'json_page_file_recipe': 'json.dumps(pages, ensure_ascii=False, indent=2) + single newline; original key order preserved',
              'canonical_credit': False}
    path = OUTPUT / 'shape-transport-reconstruction.json'
    path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'transport_map': fingerprint(path), 'encoded_files': encoded_files,
                      'duplicate_bytes_represented_reversibly': duplicate_bytes,
                      'all_original_byte_comparisons_passed': True}, sort_keys=True))


if __name__ == '__main__':
    main()
