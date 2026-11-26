"""Recreate redundant transport files from published original artifacts + map.

No original absolute path from the map is read. All writes go into a new output
directory. No remote/Git/proof/audit operation is performed.
"""
from pathlib import Path
import argparse
import base64
import hashlib
import json


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require_bytes(raw, row):
    assert len(raw) == row['bytes'] and sha(raw) == row['sha256']


def restore(mapping_path, artifacts, output):
    mapping = json.loads(Path(mapping_path).read_bytes())
    artifacts, output = Path(artifacts), Path(output)
    output.mkdir(exist_ok=False)
    originals = {}
    for name, row in mapping['artifacts'].items():
        path = artifacts / name
        if path.is_file():
            raw = path.read_bytes()
        else:
            raw = base64.b64decode((artifacts / (name + '.base64')).read_bytes(), validate=False)
        require_bytes(raw, row)
        originals[name] = raw
    produced = []

    def write(name, raw, expected):
        require_bytes(raw, expected)
        target = output / name
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(raw)
        produced.append({'path': name, 'bytes': len(raw), 'sha256': sha(raw)})

    def pages(name, specification, stdout):
        rows = []
        for original in specification['pages']:
            row = dict(original)
            assert row['output_base64'] is None
            row['output_base64'] = base64.b64encode(stdout[row['offset']:row['next_offset']]).decode()
            rows.append(row)
        write(name, (json.dumps(rows, ensure_ascii=False, indent=2) + '\n').encode(), specification['original'])

    archive = originals['blocks.stdout.log.gz']
    for entry in mapping['chunks']:
        row = dict(entry['record_without_data'])
        data = archive[row['offset']:row['end']]
        row['data'] = base64.b64encode(data).decode()
        stdout = (entry['marker'] + json.dumps(row, sort_keys=True) + '\n').encode()
        prefix = f"chunks/chunk-{entry['index']:02d}"
        write(prefix + '.bin', data, entry['binary_chunk'])
        write(prefix + '-task.log', stdout, entry['task_stdout'])
        pages(prefix + '-output-pages.json', entry['output_pages'], stdout)
    meta = mapping['metadata_task']
    row = dict(meta['record_without_payloads'])
    row['payloads'] = {name: base64.b64encode(originals[name]).decode() for name in meta['payload_file_names']}
    stdout = (meta['marker'] + json.dumps(row, sort_keys=True) + '\n').encode()
    write('metadata-task.log', stdout, meta['task_stdout'])
    pages('metadata-output-pages.json', meta['output_pages'], stdout)
    original = mapping['original_shape_task']
    stdout = (artifacts / 'original-shape-task.log').read_bytes()
    require_bytes(stdout, original['published_stdout'])
    pages('original-shape-task-output-pages.json', original['output_pages'], stdout)
    return {'all_reconstructed_file_bytes_and_sha256_passed': True,
            'original_absolute_paths_not_read': True, 'files': produced,
            'canonical_credit': False, 'remote_or_git_operations': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mapping', type=Path, required=True)
    parser.add_argument('--artifacts-dir', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(restore(args.mapping, args.artifacts_dir, args.output_dir), sort_keys=True))
