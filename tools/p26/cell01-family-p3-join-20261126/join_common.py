#!/usr/bin/env python3
"""Small adapters for exact bodies consumed by the frozen Cell01 validator."""
from pathlib import Path, PurePosixPath
import hashlib
import importlib.util
import io
import json
import sys
import tarfile

sys.dont_write_bytecode = True
OLD = Path('/workspace/p26-continuation-59264dd64286')
ROW000_ROOT = OLD / 'cell01-row000-original-floor'
ROW000_ATTEMPT = ROW000_ROOT / 'attempts/20261126T045413255133Z-03f42f40'
GENERIC_ROOT = OLD / 'original-floor-family/generic-v2-r14'
GENERIC_ATTEMPT = GENERIC_ROOT / 'attempts/generic-v2-r14-first'
PREFIX_ROOT = OLD / 'cell01-batch-C-finite-v2'
PINS = {
    'executor_manifest': (1800, '34d65a335862bdc81a2f6df7c2a6c9fb511186e696759cb8b8a745b578bf62e9'),
    'source_manifest': (406865, 'b5fa17d1eaeaaf0a40bb5cf8aa8b9b1fd0fd449be24e103eea2e838993c42cdc'),
    'supplier_delta': (1155979, 'b4607f9b5c56816b99b32b250215688cb4f33938a34b45c187c2080789190d15'),
    'object_archive': (39794840, 'a16d07fe3489855e1c69a5c2658824b8b7fce7fc44ab527d3a88eb5e8451899b'),
    'object_manifest': (409031, '8d001ee3a7bfbe4c2d6f7708c86b59977d3212053ba54bbe697143ed0a2064df'),
    'P3_present': (450204, '8d8c49452c45465f93d307a99f04abf2775ee094ce8dcff45e74c67702d7c217'),
    'P3_missing': (241935, '60aa829ab21abf61b8e363cd8abd3235683f9c13fb6307e074cfc3fd284ea685'),
    'P3_inventory': (6072, '1379b5955b9bb350cb0e15cb752bcdc7cb33cb22ee0c20c55e33035e0e5421b3'),
    'row000_archive': (886800, '1b88f393c1ccb1e9cd3c9804e86277ab9089badcd7b68b3f417cf74b6a02cea7'),
    'moment_closure': (148114, 'f2d7f7f7f1a1f9dcedb966538511fb653b32969796d91d87980dcc7f279dda37'),
}
CLOSURES = {'HIGHER_MOMENTS_PINNED_CLOSURE.json', 'GEOMETRY01_ACCEPTED_PINNED_CLOSURE.json',
            'FULL_SOURCE_CLOSURE.json', 'SUPPLIER_KERNEL_COMPLETION.json'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def identity_bytes(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def expected(key):
    size, digest = PINS[key]
    return {'bytes': size, 'sha256': digest}


def checked_local(path, pin):
    path = Path(path).absolute()
    need(path.resolve() == path and not path.is_symlink() and path.is_file(), 'Noncanonical control file')
    data = path.read_bytes()
    need(identity_bytes(data) == {k: pin[k] for k in ('bytes', 'sha256')}, 'Changed pinned control: ' + str(path))
    return data


def load_executor(path):
    path = Path(path).absolute()
    manifest = json.loads(checked_local(path.parent / 'CODE_MANIFEST.json', expected('executor_manifest')))
    for row in manifest['files']:
        rel = PurePosixPath(row['member'])
        need(not rel.is_absolute() and '..' not in rel.parts, 'Unsafe executor member')
        checked_local(path.parent / rel, row)
    need(path.name == 'family_run.py', 'Frozen family entry point required')
    spec = importlib.util.spec_from_file_location('p26_frozen_family_p3_join', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def original_pin(delta, key):
    row = delta[key]
    return {'path': str(ROW000_ROOT / row['member']), 'bytes': row['bytes'], 'sha256': row['sha256']}


def canonical_group(F, delta):
    row = next(x for x in delta['additional_suppliers'] if x['module'] == F.ROW000)
    return {'module': F.ROW000, 'source': row['source_provider'], 'object': row['object_provider'],
            'provenance': {'run': original_pin(delta, 'original_RUN'),
                           'input': original_pin(delta, 'original_INPUT'),
                           'index': original_pin(delta, 'original_RESULT'), 'records': row['records']}}


class TraceBodies:
    """Observe only actual old_chain reads; no recursive copying of INPUT.files."""
    def __init__(self, F, reader):
        self.F, self.reader = F, reader
        self.entries, self.data = {}, {}
        self.accesses = set()

    def resolve(self, reference):
        ref = self.F.E.identity(reference)
        path = Path(ref['path'])
        need('row001' not in str(path).lower() and path.suffix in {'.json', '.log', '.lean'},
             'Row001/non-body file forbidden in a transferable body set')
        key = tuple(ref[k] for k in ('path', 'bytes', 'sha256'))
        self.accesses.add(key)
        if key not in self.data:
            data = self.reader(ref)
            need(self.F.same(identity_bytes(data), ref), 'Original body byte conflict: ' + str(path))
            self.entries[key], self.data[key] = ref, data
        return path

    def bytes(self, reference):
        self.resolve(reference)
        return self.data[tuple(reference[k] for k in ('path', 'bytes', 'sha256'))]

    def json(self, reference):
        return json.loads(self.bytes(reference))

    def text(self, reference):
        return self.bytes(reference).decode()


def trace_chain(F, store, group, rows):
    store.accesses = set()
    run = store.json(group['provenance']['run'])
    runtime = {key: run[key] for key in ('lean_binary', 'leanchecker_binary')} if 'lean_binary' in run else None
    if runtime is None:
        first = store.json(group['provenance']['records'][0]['receipt'])
        context = store.json(first['context'])
        runtime = {key: context[key] for key in ('lean_binary', 'leanchecker_binary')}
    result = F.old_chain(group['provenance'], group['module'], group['source'], group['object'],
                         runtime, store, rows)
    group['body_refs'] = [store.entries[key] for key in sorted(store.accesses)]
    return result


def body_manifest_and_archive(F, output, role, groups, store, source_pins, recheck):
    output = F.canonical(output)
    need(not output.exists(), 'Evidence output exists; inspect it before any recovery')
    entries, payload = [], {}
    for key in sorted(store.entries):
        ref, data = store.entries[key], store.data[key]
        member = 'bodies/' + ref['sha256'] + Path(ref['path']).suffix
        need(member not in payload or payload[member] == data, 'Content-addressed body conflict')
        payload[member] = data
        entries.append({'original': ref, 'member': member})
    manifest = {'schema': 'p26_family_selected_original_bodies_v1', 'role': role,
                'groups': groups, 'entries': entries, 'original_body_references': len(entries),
                'unique_body_files': len(payload), 'source_pins': source_pins,
                'row001_bodies_included': False, 'supplier_objects_included': False,
                'Lean_commands': 0, 'new_proof_credit': 0}
    manifest_data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    payload['EVIDENCE_MANIFEST.json'] = manifest_data
    output.mkdir(parents=True)
    manifest_path, archive_path = output / 'EVIDENCE_MANIFEST.json', output / 'selected-bodies.tar.xz'
    with manifest_path.open('xb') as stream:
        stream.write(manifest_data)
    with archive_path.open('xb') as raw, tarfile.open(fileobj=raw, mode='w:xz', preset=6) as archive:
        for member, data in sorted(payload.items()):
            info = tarfile.TarInfo(member)
            info.size, info.mode, info.mtime = len(data), 0o444, 0
            archive.addfile(info, io.BytesIO(data))
    seen = set()
    with tarfile.open(archive_path, 'r:xz') as archive:
        for item in archive:
            need(item.isfile() and item.name in payload and item.name not in seen,
                 'Evidence archive member inventory differs')
            data = archive.extractfile(item).read()
            need(data == payload[item.name], 'Evidence body archive readback differs')
            seen.add(item.name)
    need(seen == set(payload), 'Incomplete evidence archive readback')
    recheck()
    result = {'schema': 'p26_family_selected_original_bodies_result_v1',
              'status': 'PASS_EXACT_SELECTED_BODY_ARCHIVE_READBACK', 'role': role,
              'archive': F.fp(archive_path), 'manifest': F.fp(manifest_path),
              'original_body_references': len(entries), 'unique_body_files': len(payload) - 1,
              'archive_members': len(payload), 'original_body_bytes': sum(len(v) for k, v in payload.items()
                                                                       if k != 'EVIDENCE_MANIFEST.json'),
              'Lean_commands': 0, 'new_proof_credit': 0, 'row001_bodies_included': False,
              'supplier_objects_included': False}
    F.write(output, output / 'RESULT.json', result)
    return result
