#!/usr/bin/env python3
"""Lossless cold storage around the unchanged P2.1 transfer verifier.

No network, compiler or Git operation is performed. `retain` never removes hot
files. `evict` is separate and first replays the original acceptance from the
locally retained, Git-blob-bound capture. `assemble` invokes the original
assembler with an equal-valued list that materializes only its current part.
"""
import argparse
import base64
from contextlib import ExitStack
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import stat
import tempfile
import types

HELPER_SHA256 = '5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d'
SCHEMA = 'p21-cold-capture-retention/v1'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode()


def identity(path):
    s = path.lstat()
    return s.st_dev, s.st_ino


def canonical_directory(path):
    require(path.is_absolute() and path.resolve(strict=True) == path and path.is_dir(),
            'Directory is not canonical: ' + str(path))
    return path


def load_helper(path):
    require(path.is_absolute() and path.resolve(strict=True) == path
            and stat.S_ISREG(path.lstat().st_mode), 'Helper must be its real original file')
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == HELPER_SHA256, 'Frozen helper SHA256 differs')
    helper = types.ModuleType('p21_frozen_original_transfer')
    helper.__file__ = str(path)
    # Execute exactly the bytes just verified, with their actual original path.
    exec(compile(raw, str(path), 'exec'), helper.__dict__)
    require(helper.sha(path.read_bytes()) == HELPER_SHA256, 'Helper changed while loading')
    return helper


class RestoreArea:
    """Own only the explicitly created directory and file inodes; never rmtree."""
    def __init__(self, parent):
        self.path = Path(tempfile.mkdtemp(prefix='p21-cold-restore-', dir=parent))
        self.inode = identity(self.path)
        self.files = {}

    def put(self, name, raw):
        require(identity(self.path) == self.inode, 'Restore directory was replaced')
        p = self.path / name
        require(p.name == name and '..' not in name, 'Invalid restored filename')
        with p.open('xb') as stream:
            created = os.fstat(stream.fileno())
            self.files[p] = (created.st_dev, created.st_ino)
            require(identity(p) == self.files[p], 'Restore path changed after creation')
            stream.write(raw)
            require(identity(p) == self.files[p] and identity(self.path) == self.inode,
                    'Restore path changed during writing')
        return p

    def clear(self):
        require(identity(self.path) == self.inode, 'Restore directory was replaced')
        for p, inode in list(self.files.items()):
            require(os.path.lexists(p) and identity(p) == inode,
                    'Refusing to clean a replaced restore file: ' + str(p))
            p.unlink()
            del self.files[p]

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.clear()
        require(identity(self.path) == self.inode, 'Restore directory was replaced')
        self.path.rmdir()  # An unexpected/foreign file is deliberately not deleted.


class MaterializedParts(list):
    def __init__(self, values, store, asset, area):
        super().__init__(values)
        self.store, self.asset, self.area = store, asset, area
        self.iterator = None
        self.receipts = []
        self.record_hashes = []

    def __iter__(self):
        require(self.iterator is None, 'Cold part traversal may only be started once')
        self.iterator = self.walk()
        return self.iterator

    def walk(self):
        for piece in list.__iter__(self):
            try:
                record, record_sha = self.store.materialize(self.asset, piece['index'], self.area)
                self.receipts.append(record['receipt'])
                self.record_hashes.append({'index': piece['index'], 'sha256': record_sha})
                yield piece
            finally:
                self.area.clear()

    def close(self):
        if self.iterator is not None:
            self.iterator.close()


class ColdStore:
    def __init__(self, helper_path, plan_path, plan_sha, directory, allow_synthetic=False):
        self.helper = load_helper(helper_path)
        self.plan = self.helper.load_plan(plan_path, plan_sha)
        self.plan_sha = plan_sha
        self.directory = canonical_directory(directory)
        self.allow_synthetic = allow_synthetic

    def prefix(self, asset, index):
        require(isinstance(asset, str) and re.fullmatch('[a-z_]+', asset)
                and asset in self.plan['assets'] and type(index) is int
                and 0 <= index < len(self.plan['assets'][asset]['parts']), 'Invalid asset/index')
        return f'{asset}.{index:05}'

    def read_json(self, path):
        stream, before = self.helper.regular(path)
        with stream:
            raw = stream.read()
            self.helper.unchanged(path, stream, before)
        return json.loads(raw), {'bytes': len(raw), 'sha256': self.helper.sha(raw)}

    def atomic_new(self, path, raw):
        canonical_directory(path.parent)
        if os.path.lexists(path):
            self.helper.frozen_bytes(path, self.helper.sha(raw), len(raw))
            return
        fd, name = tempfile.mkstemp(prefix=path.name + '.', suffix='.partial', dir=path.parent)
        temp = Path(name)
        created = os.fstat(fd)
        inode = (created.st_dev, created.st_ino)
        try:
            with os.fdopen(fd, 'wb') as stream:
                stream.write(raw)
                stream.flush()
                os.fsync(stream.fileno())
            require(identity(temp) == inode, 'Atomic-write path changed before linking')
            os.link(temp, path)  # No overwrite, including a racing new destination.
            require(identity(path) == inode, 'Atomic-write destination is not the created inode')
        finally:
            require(identity(temp) == inode, 'Refusing to clean a replaced atomic-write file')
            temp.unlink()

    @staticmethod
    def actual_git_sha(publication):
        result = publication['result']
        require(isinstance(result, dict) and result.get('isError', False) is False,
                'Git tool returned an error')
        structured = result.get('structuredContent')
        require(isinstance(structured, dict) and isinstance(structured.get('sha'), str)
                and re.fullmatch('[0-9a-f]{40}', structured['sha']), 'Missing actual Git structuredContent.sha')
        require(publication.get('github_blob_verified') is True
                and publication.get('remote_blob_sha') == structured['sha'], 'Git publication metadata differs')
        return structured['sha']

    def publication(self, asset, index):
        prefix = self.prefix(asset, index)
        path = self.directory / (prefix + '.capture-publication.json')
        publication, binding = self.read_json(path)
        require(publication.get('asset', asset) == asset and type(publication.get('index')) is int
                and publication['index'] == index, 'Capture publication refers to another part')
        require(publication['path'] == f'docs/verification/20261126-p2-1/transport-captures/{asset}-{index:05}.json.xz',
                'Capture publication path differs')
        require(self.actual_git_sha(publication) == publication['git_blob_sha'], 'Capture Git blob differs')
        for key in ('bytes', 'raw_capture_bytes'):
            require(type(publication[key]) is int and publication[key] > 0, 'Invalid capture byte count')
        for key in ('sha256', 'raw_capture_calls_sha256'):
            require(re.fullmatch('[0-9a-f]{64}', publication[key]), 'Invalid capture digest')
        raw_binding = None
        if asset == 'archive':
            raw, raw_binding = self.read_json(self.directory / (prefix + '.result.json'))
            require(raw['asset'] == asset and type(raw['index']) is int and raw['index'] == index,
                    'Archive publication refers to another part')
            require(self.actual_git_sha(raw['publication']) == self.plan['assets'][asset]['parts'][index]['git_blob_sha'],
                    'Actual archive Git blob differs from the original plan')
        return publication, binding, raw_binding

    def cold_path(self, asset, index):
        self.prefix(asset, index)
        cold = self.directory / 'cold-captures'
        cold.mkdir(exist_ok=True)
        canonical_directory(cold)
        return cold / f'{asset}-{index:05}.json.xz'

    def checked_capture(self, publication, compressed):
        require(len(compressed) == publication['bytes'] and self.helper.sha(compressed) == publication['sha256']
                and self.helper.blob_sha(compressed) == publication['git_blob_sha']
                == self.actual_git_sha(publication), 'Compressed original capture/Git bytes differ')
        decoder = lzma.LZMADecompressor(memlimit=256 * 1024 * 1024)
        raw = decoder.decompress(compressed, max_length=publication['raw_capture_bytes'] + 1)
        require(len(raw) == publication['raw_capture_bytes'] and decoder.eof and not decoder.unused_data
                and self.helper.sha(raw) == publication['raw_capture_calls_sha256'], 'Original capture round trip differs')
        return raw

    def restore_raw(self, asset, index, raw, area):
        prefix = self.prefix(asset, index)
        capture = json.loads(raw)
        binary = bytearray()
        for page in capture['pages']:
            body = self.helper.payload(page, 'read_task_output')
            binary.extend(base64.b64decode(body['output_base64'], validate=True))
            require(len(binary) <= self.plan['assets'][asset]['parts'][index]['bytes'], 'Capture expands beyond its part')
        calls_path = area.put(prefix + '.capture.json', raw)
        binary_path = area.put(prefix + '.bin', binary)
        # All original status, exact submission, page/offset/EOF and byte gates run.
        _, receipt = self.helper.accept(self.plan, self.plan_sha, asset, index, binary_path, calls_path,
                                        allow_synthetic=self.allow_synthetic)
        return receipt

    def retain(self, asset, index, xz_source=None):
        prefix = self.prefix(asset, index)
        binary, calls = (self.directory / (prefix + s) for s in ('.bin', '.capture.json'))
        _, receipt = self.helper.accept(self.plan, self.plan_sha, asset, index, binary, calls,
                                        allow_synthetic=self.allow_synthetic)
        publication, binding, raw_binding = self.publication(asset, index)
        require(receipt['raw_capture_calls_sha256'] == publication['raw_capture_calls_sha256'], 'Published capture differs')
        existing_receipt = self.directory / (prefix + '.receipt.json')
        if os.path.lexists(existing_receipt):
            require(self.read_json(existing_receipt)[0] == receipt, 'Saved original acceptance receipt differs')
        raw = self.helper.frozen_bytes(calls, receipt['raw_capture_calls_sha256'], publication['raw_capture_bytes'])
        cold_path = self.cold_path(asset, index)
        source = xz_source if xz_source is not None else cold_path
        if os.path.lexists(source):
            compressed = self.helper.frozen_bytes(source, publication['sha256'], publication['bytes'])
        else:
            require(xz_source is None, 'Supplied compressed capture does not exist')
            compressed = lzma.compress(raw, preset=6)
        require(self.checked_capture(publication, compressed) == raw, 'Compressed capture does not preserve original bytes')
        self.atomic_new(cold_path, compressed)
        # Read the retained regular file back before publishing a retention record.
        restored = self.checked_capture(publication, self.helper.frozen_bytes(cold_path, publication['sha256'], publication['bytes']))
        with RestoreArea(self.directory) as area:
            require(self.restore_raw(asset, index, restored, area) == receipt, 'Restored original acceptance differs')
        record = {'schema': SCHEMA, 'synthetic_test_only': self.plan['synthetic_test_only'],
                  'plan_sha256': self.plan_sha, 'producer_sha256': HELPER_SHA256, 'asset': asset, 'index': index,
                  'cold_capture': {'path': str(cold_path.relative_to(self.directory)),
                                   **{k: publication[k] for k in ('bytes', 'sha256', 'git_blob_sha')}},
                  'raw_capture_bytes': len(raw), 'raw_capture_calls_sha256': receipt['raw_capture_calls_sha256'],
                  'capture_publication': binding, 'archive_publication': raw_binding, 'receipt': receipt,
                  'hot_removal_by_retain': False, 'compile_credit': False, 'kernel_credit': False}
        self.atomic_new(self.directory / (prefix + '.cold-retention.json'), encoded(record))
        return record

    def materialize(self, asset, index, area):
        prefix = self.prefix(asset, index)
        record, record_info = self.read_json(self.directory / (prefix + '.cold-retention.json'))
        require(record['schema'] == SCHEMA and record['plan_sha256'] == self.plan_sha
                and record['producer_sha256'] == HELPER_SHA256 and record['asset'] == asset
                and type(record['index']) is int and record['index'] == index
                and record['synthetic_test_only'] is self.plan['synthetic_test_only'], 'Cold retention identity differs')
        publication, binding, raw_binding = self.publication(asset, index)
        require(record['capture_publication'] == binding and record['archive_publication'] == raw_binding,
                'Retained original publication bytes changed')
        cold = self.cold_path(asset, index)
        require(record['cold_capture'] == {'path': str(cold.relative_to(self.directory)),
                                          **{k: publication[k] for k in ('bytes', 'sha256', 'git_blob_sha')}}
                and record['raw_capture_bytes'] == publication['raw_capture_bytes']
                and record['raw_capture_calls_sha256'] == publication['raw_capture_calls_sha256'], 'Cold capture binding differs')
        raw = self.checked_capture(publication, self.helper.frozen_bytes(cold, publication['sha256'], publication['bytes']))
        receipt = self.restore_raw(asset, index, raw, area)
        require(receipt == record['receipt'], 'Restored original job/capture/part acceptance differs')
        return record, record_info['sha256']

    def evict(self, asset, index):
        prefix = self.prefix(asset, index)
        retained = [self.directory / (prefix + '.cold-retention.json'),
                    self.cold_path(asset, index),
                    self.directory / (prefix + '.capture-publication.json')]
        if asset == 'archive':
            retained.append(self.directory / (prefix + '.result.json'))
        with ExitStack() as handles:
            pinned = []
            for path in retained:
                stream, before = self.helper.regular(path)
                handles.enter_context(stream)
                pinned.append((path, stream, before))

            def originals_unchanged():
                for path, stream, before in pinned:
                    self.helper.unchanged(path, stream, before)

            with RestoreArea(self.directory) as area:
                record, record_sha = self.materialize(asset, index, area)
            originals_unchanged()
            receipt = record['receipt']
            hot = []
            for suffix, expected_sha, count in (('.bin', receipt['sha256'], receipt['bytes']),
                                                ('.capture.json', receipt['raw_capture_calls_sha256'], record['raw_capture_bytes'])):
                path = self.directory / (prefix + suffix)
                if not os.path.lexists(path):
                    continue
                stream, before = self.helper.regular(path)
                handles.enter_context(stream)
                self.helper.frozen_bytes(path, expected_sha, count)
                self.helper.unchanged(path, stream, before)
                hot.append((path, stream, before))
            # Verify both hot files and all retained originals before removing any.
            originals_unchanged()
            for path, stream, before in hot:
                self.helper.unchanged(path, stream, before)
            removed = []
            for path, stream, before in hot:
                originals_unchanged()
                self.helper.unchanged(path, stream, before)
                path.unlink()
                removed.append(path.name)
            originals_unchanged()
        report = {'schema': 'p21-cold-hot-removal/v1', 'asset': asset, 'index': index,
                  'cold_retention_sha256': record_sha, 'removed_verified_hot_files': removed,
                  'cold_originals_preserved': True, 'compile_credit': False, 'kernel_credit': False}
        if removed:
            self.atomic_new(self.directory / (prefix + '.hot-removal.json'), encoded(report))
        return report

    def assemble(self, asset, output):
        require(asset in self.plan['assets'], 'Unknown asset')
        with RestoreArea(self.directory) as area:
            parts = MaterializedParts(self.plan['assets'][asset]['parts'], self, asset, area)
            plan = {**self.plan, 'assets': {**self.plan['assets'], asset: {**self.plan['assets'][asset], 'parts': parts}}}
            require(plan == self.plan and len(parts) == len(self.plan['assets'][asset]['parts']),
                    'Parts adapter changed original plan values')
            try:
                result = self.helper.assemble(plan, self.plan_sha, asset, area.path, output,
                                              allow_synthetic=self.allow_synthetic)
                require(result['verified_parts'] == parts.receipts, 'Original assembler acceptance differs from cold records')
                return {**result, 'cold_retention_records': parts.record_hashes, 'compile_credit': False, 'kernel_credit': False}
            finally:
                parts.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--helper', type=Path, required=True, help='Actual original transfer_p21_evidence.py path')
    sub = parser.add_subparsers(dest='command', required=True)
    for command in ('retain', 'evict', 'assemble'):
        p = sub.add_parser(command)
        p.add_argument('plan', type=Path)
        p.add_argument('plan_sha256')
        p.add_argument('asset')
        if command != 'assemble':
            p.add_argument('index', type=int)
        p.add_argument('directory', type=Path)
        if command == 'retain':
            p.add_argument('--xz-source', type=Path)
        if command == 'assemble':
            p.add_argument('output', type=Path)
    args = parser.parse_args()
    store = ColdStore(args.helper, args.plan, args.plan_sha256, args.directory)
    if args.command == 'retain':
        result = store.retain(args.asset, args.index, args.xz_source)
    elif args.command == 'evict':
        result = store.evict(args.asset, args.index)
    else:
        result = store.assemble(args.asset, args.output)
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
