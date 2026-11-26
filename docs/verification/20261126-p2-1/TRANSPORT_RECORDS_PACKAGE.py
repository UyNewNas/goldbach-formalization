#!/usr/bin/env python3
"""One-time local archive transport-record packaging; no network or Lean credit."""
import argparse
import hashlib
import io
import json
import lzma
import os
from pathlib import Path
import re
import stat
import tarfile
import tempfile
import types

HELPER_SHA = '5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d'
REQUIRED = ('result', 'capture-publication')
OPTIONAL = ('receipt', 'cold-retention', 'hot-removal', 'terminal')
INDEX_NAME = 'MEMBERS.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def inode(path):
    current = path.lstat()
    return current.st_dev, current.st_ino


def load_original(path):
    require(path.is_absolute() and path.resolve(strict=True) == path
            and stat.S_ISREG(path.lstat().st_mode), 'Original helper path is not canonical regular')
    raw = path.read_bytes()
    require(sha(raw) == HELPER_SHA, 'Original helper SHA differs')
    helper = types.ModuleType('original_p21_transport_for_packaging')
    helper.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), helper.__dict__)
    helper.frozen_bytes(path, HELPER_SHA, len(raw))
    return helper


def read_original(helper, path):
    stream, before = helper.regular(path)
    with stream:
        raw = stream.read()
        helper.unchanged(path, stream, before)
    return raw, before


def actual_blob(publication):
    result = publication['result']
    require(isinstance(result, dict) and result.get('isError', False) is False, 'Git response is an error')
    body = result.get('structuredContent')
    require(isinstance(body, dict) and isinstance(body.get('sha'), str)
            and re.fullmatch('[0-9a-f]{40}', body['sha']), 'Actual Git structuredContent.sha is missing')
    require(publication.get('github_blob_verified') is True and publication['remote_blob_sha'] == body['sha'],
            'Saved Git response binding differs')
    return body['sha']


def safe_name(name):
    return bool(re.fullmatch(r'archive\.[0-9]{5}\.(result|capture-publication|receipt|cold-retention|hot-removal|terminal)\.json', name))


def parse_indices(text, count):
    values = []
    for item in text.split(','):
        require(re.fullmatch('[0-9]+(-[0-9]+)?', item), 'Invalid explicit part selection')
        ends = [int(x) for x in item.split('-')]
        low, high = ends[0], ends[-1]
        require(0 <= low <= high < count, 'Part selection is outside original plan')
        values.extend(range(low, high + 1))
    require(values and len(set(values)) == len(values), 'Empty or duplicate part selection')
    return sorted(values)


def atomic_new(helper, path, raw):
    require(path.is_absolute() and path.parent.resolve(strict=True) == path.parent,
            'Output parent is not canonical')
    if os.path.lexists(path):
        helper.frozen_bytes(path, sha(raw), len(raw))
        return
    fd, name = tempfile.mkstemp(prefix=path.name + '.', suffix='.partial', dir=path.parent)
    temp = Path(name)
    created = os.fstat(fd)
    owned = (created.st_dev, created.st_ino)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        require(inode(temp) == owned, 'Owned package temporary was replaced before publication')
        os.link(temp, path)
        require(inode(path) == owned, 'Published path is not the owned package inode')
        helper.frozen_bytes(path, sha(raw), len(raw))
    finally:
        require(inode(temp) == owned, 'Refusing to delete a replacement temporary inode')
        temp.unlink()


def package(helper, plan, plan_sha, directory, indices, output):
    require(not plan['synthetic_test_only'], 'This packaging run requires the real production plan')
    require(directory.is_absolute() and directory.resolve(strict=True) == directory and directory.is_dir(),
            'Source directory is not canonical')
    pieces = plan['assets']['archive']['parts']
    contents, stamps, missing, rows = {}, {}, {}, []
    for index in indices:
        prefix = f'archive.{index:05}'
        values = {}
        absent = []
        for kind in REQUIRED + OPTIONAL:
            name = prefix + '.' + kind + '.json'
            require(safe_name(name), 'Unsafe archive member name')
            path = directory / name
            if not os.path.lexists(path):
                require(kind in OPTIONAL, 'Missing completed-part publication record: ' + name)
                absent.append(name)
                continue
            raw, before = read_original(helper, path)
            contents[name], stamps[name], values[kind] = raw, before, json.loads(raw)
        result, publication = values['result'], values['capture-publication']
        require(result['asset'] == 'archive' and type(result['index']) is int and result['index'] == index,
                'Archive result identity differs')
        receipt = result['receipt']
        piece = pieces[index]
        require(receipt['asset'] == 'archive' and receipt['status'] == 'VERIFIED_ORIGINAL_PART'
                and all(receipt[k] == v and type(receipt[k]) is type(v) for k, v in piece.items())
                and re.fullmatch('[0-9a-f]{32}', receipt['job_id'])
                and result['job_id'] == receipt['job_id']
                and re.fullmatch('[0-9a-f]{64}', receipt['raw_capture_calls_sha256']),
                'Original completed-part receipt differs from pinned plan')
        require(actual_blob(result['publication']) == piece['git_blob_sha'], 'Actual archive Git blob differs')
        require(publication.get('asset', 'archive') == 'archive' and type(publication['index']) is int
                and publication['index'] == index and actual_blob(publication) == publication['git_blob_sha']
                and publication['raw_capture_calls_sha256'] == receipt['raw_capture_calls_sha256']
                and publication['path'] == f'docs/verification/20261126-p2-1/transport-captures/archive-{index:05}.json.xz',
                'Actual original capture publication differs')
        if 'receipt' in values:
            require(values['receipt'] == receipt, 'Separate original receipt differs')
        if 'cold-retention' in values:
            cold = values['cold-retention']
            require(cold['schema'] == 'p21-cold-capture-retention/v1' and cold['asset'] == 'archive'
                    and type(cold['index']) is int and cold['index'] == index
                    and cold['plan_sha256'] == plan_sha and cold['producer_sha256'] == HELPER_SHA
                    and cold['synthetic_test_only'] is False and cold['receipt'] == receipt,
                    'Cold record identity differs')
            for kind, key in [('result', 'archive_publication'), ('capture-publication', 'capture_publication')]:
                raw = contents[prefix + '.' + kind + '.json']
                require(cold[key] == {'bytes': len(raw), 'sha256': sha(raw)}, 'Cold record original-byte binding differs')
        if 'hot-removal' in values:
            removal = values['hot-removal']
            cold_name = prefix + '.cold-retention.json'
            require('cold-retention' in values and removal['asset'] == 'archive'
                    and type(removal['index']) is int and removal['index'] == index
                    and removal['cold_retention_sha256'] == sha(contents[cold_name]), 'Hot-removal binding differs')
        if 'terminal' in values:
            terminal = values['terminal']
            state = helper.payload(terminal, 'get_task')
            require(terminal['arguments'] == {'task_id': receipt['job_id']}
                    and state['job_id'] == state['task_id'] == receipt['job_id']
                    and state['status'] == 'succeeded' and type(state['exit_code']) is int and state['exit_code'] == 0
                    and state['log_truncated'] is False and state['log_discarded_bytes'] == 0
                    and state['log_bytes'] == piece['bytes'], 'Original saved terminal differs')
        missing[str(index)] = absent
        rows.append({'index': index, 'job_id': receipt['job_id'], 'part_sha256': piece['sha256'],
                     'part_git_blob_sha': piece['git_blob_sha'], 'raw_capture_calls_sha256': receipt['raw_capture_calls_sha256'],
                     'capture_xz_git_blob_sha': publication['git_blob_sha']})
    members = [{'path': name, 'bytes': len(raw), 'sha256': sha(raw)} for name, raw in sorted(contents.items())]
    complete = indices == list(range(len(pieces)))
    index_value = {'schema': 'p21-original-transport-record-members/v1', 'asset': 'archive',
                   'coverage_status': 'ALL_PLANNED_ARCHIVE_PARTS' if complete else 'PARTIAL',
                   'expected_part_count': len(pieces), 'included_part_count': len(indices),
                   'included_indices': indices, 'plan_sha256': plan_sha, 'producer_sha256': HELPER_SHA,
                   'source_snapshot_commit': plan['source_snapshot_commit'], 'git_commit': plan['git_commit'],
                   'git_tree': plan['git_tree'], 'required_record_kinds': list(REQUIRED),
                   'optional_record_kinds': list(OPTIONAL), 'absent_optional_records': missing,
                   'parts': rows, 'members': members, 'compile_credit': False, 'kernel_credit': False}
    index_raw = encode(index_value)
    packed = {**contents, INDEX_NAME: index_raw}
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode='w', format=tarfile.USTAR_FORMAT) as tar:
        for name, raw in sorted(packed.items()):
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.uid, info.gid, info.mtime = len(raw), 0o644, 0, 0, 0
            info.uname = info.gname = ''
            tar.addfile(info, io.BytesIO(raw))
    tar_raw = stream.getvalue()
    compressed = lzma.compress(tar_raw, format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64, preset=6)
    require(lzma.decompress(compressed) == tar_raw, 'Pack compression round trip differs')
    with tarfile.open(fileobj=io.BytesIO(tar_raw), mode='r:') as tar:
        entries = tar.getmembers()
        require([p.name for p in entries] == sorted(packed) and len(entries) == len(packed), 'Unexpected tar members')
        for entry in entries:
            require(entry.isreg() and (entry.name == INDEX_NAME or safe_name(entry.name))
                    and entry.uid == entry.gid == entry.mtime == 0 and entry.mode == 0o644
                    and entry.uname == entry.gname == '' and not entry.pax_headers,
                    'Unsafe or nondeterministic tar header')
            require(tar.extractfile(entry).read() == packed[entry.name], 'Tar member does not preserve source bytes')
    # Recheck every selected original and the set of present optional records.
    # Originals are never rewritten, removed or reserialized into package members.
    for name, raw in contents.items():
        again, before = read_original(helper, directory / name)
        require(again == raw and before == stamps[name], 'Original record changed during packaging: ' + name)
    for absent in missing.values():
        require(not any(os.path.lexists(directory / name) for name in absent), 'An optional record appeared; rerun snapshot')
    archive_path = output.with_name(output.name + '.tar.xz')
    description_path = output.with_name(output.name + '.json')
    descriptor = {'schema': 'p21-original-transport-record-package/v1',
                  'coverage_status': index_value['coverage_status'], 'asset': 'archive',
                  'expected_part_count': len(pieces), 'included_part_count': len(indices), 'included_indices': indices,
                  'plan_sha256': plan_sha, 'producer_sha256': HELPER_SHA,
                  'archive': {'path': archive_path.name, 'bytes': len(compressed), 'sha256': sha(compressed),
                              'git_blob_sha': helper.blob_sha(compressed)},
                  'uncompressed_tar': {'bytes': len(tar_raw), 'sha256': sha(tar_raw)},
                  'generated_index': {'path': INDEX_NAME, 'bytes': len(index_raw), 'sha256': sha(index_raw)},
                  'original_record_count': len(members), 'original_record_bytes': sum(p['bytes'] for p in members),
                  'members': members, 'absent_optional_records': missing,
                  'format': {'tar': 'ustar', 'order': 'ASCII filename', 'mtime': 0, 'uid': 0, 'gid': 0,
                             'mode': '0644', 'uname': '', 'gname': '', 'compression': 'xz', 'preset': 6, 'check': 'CRC64'},
                  'large_capture_files_included': False, 'binary_parts_included': False,
                  'compile_credit': False, 'kernel_credit': False}
    atomic_new(helper, archive_path, compressed)
    atomic_new(helper, description_path, encode(descriptor))
    return {'description_path': str(description_path), 'description_sha256': sha(encode(descriptor)),
            **{k: descriptor[k] for k in ['coverage_status', 'expected_part_count', 'included_part_count',
                                          'original_record_count', 'original_record_bytes', 'archive']}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--helper', type=Path, required=True)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--plan-sha256', required=True)
    parser.add_argument('--directory', type=Path, required=True)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument('--indices', help='Explicit inclusive ranges, e.g. 0-4 or 0-4,136-140')
    selection.add_argument('--all', action='store_true', help='Require records for every planned archive part')
    parser.add_argument('--output-prefix', type=Path, required=True)
    args = parser.parse_args()
    helper = load_original(args.helper)
    plan = helper.load_plan(args.plan, args.plan_sha256)
    count = len(plan['assets']['archive']['parts'])
    indices = list(range(count)) if args.all else parse_indices(args.indices, count)
    print(json.dumps(package(helper, plan, args.plan_sha256, args.directory, indices, args.output_prefix),
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
