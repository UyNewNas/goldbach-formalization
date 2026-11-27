#!/usr/bin/env python3
"""Restore only previously accepted object bytes, without invoking Lean."""
import base64
import datetime
import hashlib
import json
import pathlib
import tarfile
import urllib.request

P = pathlib.Path
ROOT = P('/workspace/p29-recovered-inputs-20261128')
OLD = P('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')
GRAPH = OLD / 'verification-finset-prod-resume-v6/consumer-actual-imports-bindings.json'
GRAPH_SHA = '9ca216b1d0c19c50050f2d16028359ceb42d6f3f3f2fc4ac10a9d389413de8f8'
RECEIPT = P('/workspace/p29-nonempty-inputs-20261126-14206fd/BYTE_RECEPTION_RECEIPT.json')
RECEIPT_SHA = '1104d485e61164f2b2c1eb6e7c7a06ac4af212599cec0c511f0299106d17d6c3'
SCAN = P('/workspace/p29-continuation-stage-20261128/recovery-candidates.json')
NONRADIAL_BLOB = '8a8702a17098ae6129603a421d94f48526cfd653'
ARCHIVES = {
    'affine': {
        'path': '/workspace/p29-polyhedral-affine-7981839-archive/complete.tar.xz',
        'bytes': 3450196,
        'sha256': '6b870ac526725d644bed57b6f12f8afb7bd3fbd6c9c21f6bf9ec7442cd572b5d',
        'manifest': 'manifest.json',
        'manifest_sha256': 'cfdc0789e901cc032b131c56c36a487558a916c3e164503f6e8b31152b408a58',
    },
    'omitted': {
        'path': str(OLD / 'qualified-omitted-prime-wall.tar.xz'),
        'bytes': 13529388,
        'sha256': '08f8d568f01d80dd4b4fa490b7fbe0d117265e343ebaef0c9d346579f544d978',
        'manifest': 'FILE_MANIFEST.json',
        'manifest_sha256': '9c6092358690df4615ae8f99f2383e06528f18077b25448c2a724569ac393a02',
    },
    'unit128_existing': {
        'path': '/workspace/p29-omitted-inputs-20261126-b23868d/archives/unit128.tar.xz',
        'bytes': 5933976,
        'sha256': '06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f',
        'manifest': 'FILE_MANIFEST.json',
        'manifest_sha256': 'f6246295885137041434ed75c773e4e1d578345bdd552c1033caba016fe36ec3',
    },
    'nonradial15_Git_fallback': {
        'path': str(ROOT / 'archives/nonradial15.tar.xz'),
        'bytes': 102274,
        'sha256': 'c48f8974537d91d1113a9d67b71ca7a3ee0407a67ced3476456f1f85ece56cbb',
        'manifest': 'FILE_MANIFEST.json',
        'manifest_sha256': '0fbfafc4f8d37fcf129d615a2fb710508d096be94590873de7627ef7135c0019',
        'git_blob': NONRADIAL_BLOB,
    },
}


def require(value, message):
    if not value:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def identity(path):
    path = P(path)
    before = path.stat()
    with path.open('rb') as stream:
        sha = hashlib.file_digest(stream, 'sha256').hexdigest()
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            'Input changed while hashing: ' + str(path))
    return {'path': str(path.resolve(strict=True)), 'bytes': after.st_size, 'sha256': sha}


def check(path, pin):
    actual = identity(path)
    require(actual['bytes'] == pin['bytes'] and actual['sha256'] == pin['sha256'], 'Byte identity mismatch: ' + str(path))
    return actual


def write_exact(path, raw):
    path = P(path)
    require(not path.is_symlink() and all(not p.is_symlink() for p in path.parents), 'Refusing symlink destination')
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        require(path.is_file() and path.read_bytes() == raw, 'Refusing overwrite: ' + str(path))
    else:
        with path.open('xb') as stream:
            stream.write(raw)


def load_pinned(path, sha):
    raw = P(path).read_bytes()
    require(digest(raw) == sha, 'Metadata pin mismatch: ' + str(path))
    return json.loads(raw)


archive_cache = {}


def archive_member(provider, member, expected):
    spec = ARCHIVES[provider]
    path = P(spec['path'])
    if provider == 'nonradial15_Git_fallback' and not path.exists():
        url = 'https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/' + NONRADIAL_BLOB
        request = urllib.request.Request(url, headers={'User-Agent': 'p29-exact-byte-recovery', 'Accept': 'application/vnd.github+json'})
        with urllib.request.urlopen(request, timeout=45) as response:
            payload = response.read(2000000)
        record = json.loads(payload)
        require(record['sha'] == NONRADIAL_BLOB and record['encoding'] == 'base64', 'Wrong Git blob response')
        raw = base64.b64decode(record['content'])
        require(len(raw) == spec['bytes'] and digest(raw) == spec['sha256'], 'Downloaded archive identity differs')
        require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == NONRADIAL_BLOB, 'Git blob digest differs')
        write_exact(path, raw)
    if provider not in archive_cache:
        check(path, spec)
        # The original Nonradial15 transport is gzip; the other transports are
        # xz. The fixed whole-file digest authenticates bytes before detection.
        stream = tarfile.open(path, 'r:*')
        members = stream.getmembers()
        require(len({m.name for m in members}) == len(members), 'Duplicate archive member')
        for m in members:
            p = pathlib.PurePosixPath(m.name)
            require(not p.is_absolute() and '..' not in p.parts and '\\' not in m.name, 'Unsafe archive name')
            require(m.isfile() or m.isdir(), 'Non-regular archive entry')
        manifest = stream.getmember(spec['manifest'])
        require(manifest.isfile(), 'Manifest is not a regular file')
        manifest_raw = stream.extractfile(manifest).read()
        require(digest(manifest_raw) == spec['manifest_sha256'], 'Archive manifest pin differs')
        archive_cache[provider] = stream
    stream = archive_cache[provider]
    item = stream.getmember(member)
    require(item.isfile() and item.size == expected['bytes'], 'Object archive member has wrong type or size')
    raw = stream.extractfile(item).read()
    require(len(raw) == expected['bytes'] and digest(raw) == expected['sha256'], 'Archived object differs from original accepted bytes')
    return raw, {'method': 'exact_original_archive_member', 'archive_path': str(path),
                 'archive_sha256': spec['sha256'], 'archive_bytes': spec['bytes'],
                 'member': member, 'manifest_sha256': spec['manifest_sha256'],
                 **({'git_blob': spec['git_blob']} if 'git_blob' in spec else {})}


def main():
    graph = load_pinned(GRAPH, GRAPH_SHA)
    receipt = load_pinned(RECEIPT, RECEIPT_SHA)
    scan = json.loads(SCAN.read_text())
    candidates = {}
    for row in scan['matching_candidates']:
        candidates.setdefault(row['module'], []).append(row)
    missing = []
    for row in graph['parts']:
        original = row['identity']
        if not P(original['path']).is_file():
            require(row['facet'] == '.olean' and row['module'].startswith('ImbalancedChen.'), 'Unexpected missing old input')
            missing.append((row['module'], original, {'graph_path': str(GRAPH), 'graph_sha256': GRAPH_SHA}, None))
    require(len(missing) == 55, 'Old missing count changed; inspect before recovery')
    for module, row in receipt['selected_objects'].items():
        original = {'path': row['selected_path'], 'bytes': row['bytes'], 'sha256': row['sha256']}
        if not P(original['path']).is_file():
            missing.append((module, original, {'receipt_path': str(RECEIPT), 'receipt_sha256': RECEIPT_SHA}, row['provenance']))
    require(len(missing) == 67 and len({m for m, *_ in missing}) == 67, 'Expected precisely 67 missing project objects')
    mappings = []
    for module, original, authority, provider in missing:
        require(not P(original['path']).exists(), 'Original missing path is an unexpected non-file: ' + original['path'])
        if module in candidates:
            selected_copy = candidates[module][0]
            candidate_pin = check(selected_copy['path'], original)
            raw = P(candidate_pin['path']).read_bytes()
            provenance = {'method': 'live_copy_matching_original_accepted_bytes', 'copy_source': candidate_pin,
                          'candidate_scan_path': str(SCAN), 'candidate_scan_sha256': identity(SCAN)['sha256']}
        elif module == 'ImbalancedChen.AffinePrimeWallReserve':
            raw, provenance = archive_member('affine', 'project/.lake/p2-private/lib/ImbalancedChen/AffinePrimeWallReserve.olean', original)
        elif module == 'ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall':
            raw, provenance = archive_member('omitted', 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5OmittedPrimeWall.olean', original)
        else:
            require(provider is not None and provider['provider'] in ARCHIVES, 'No exact byte provider: ' + module)
            raw, provenance = archive_member(provider['provider'], provider['object_member'], original)
        require(len(raw) == original['bytes'] and digest(raw) == original['sha256'], 'Copy changed before restoration')
        dest = ROOT / 'objects' / (module.replace('.', '/') + '.olean')
        write_exact(dest, raw)
        selected = check(dest, original)
        mappings.append({'module': module, 'facet': '.olean', 'original': original, 'selected': selected,
                         'provenance': {**provenance, 'accepted_identity_authority': authority}})
    methods = {}
    for row in mappings:
        methods[row['provenance']['method']] = methods.get(row['provenance']['method'], 0) + 1
        check(row['selected']['path'], row['original'])
    output = {'schema': 'p29_exact_old_byte_relocations_v1', 'recovery_root': str(ROOT),
              'original_graph_sha256': GRAPH_SHA, 'original_receipt_sha256': RECEIPT_SHA,
              'object_count': len(mappings), 'methods': methods, 'old_paths_modified': 0,
              'lean_invocations': 0, 'new_formal_credit': 0, 'mappings': mappings}
    path = ROOT / 'RECOVERY_INDEX.json'
    write_exact(path, (json.dumps(output, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode())
    for stream in archive_cache.values():
        stream.close()
    print(json.dumps({'result': 'PASS_67_EXACT_OLD_BYTES_RELOCATED', 'index': identity(path),
                      'methods': methods, 'old_paths_modified': 0, 'lean_invocations': 0}, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
