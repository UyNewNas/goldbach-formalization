"""One exact FullMember key in two registries, plus one pinned adoption JSON.

All file content reads are bounded, cached by device/inode, and read-only.
There is no Lean invocation, filesystem write, search, or dependency recursion.
"""
import base64
import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import sys
import tarfile

MODULE = 'ImbalancedChen.Part5OriginalH430FullMemberMeasurable'
BASENAME = 'Part5OriginalH430FullMemberMeasurable'
ROOTS = (
    Path('/workspace/p2-9-20261125'),
    Path('/workspace/p2-saving16-20261125'),
)
ADOPTION = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/'
                'staged-45362510169/project-adoptions/attempt-001/PROJECT_CACHE_ADOPTION.json')
ADOPTION_SHA256 = 'c481b63afedeb846f3a07371518c692b3ce71eeb2050fe48b9fc2b527a763269'
LIMITS = {
    'registry': 64 * 1024 * 1024,
    'source': 1024 * 1024,
    'object_identity': 64 * 1024 * 1024,
    'adoption': 32 * 1024 * 1024,
    'explicit_receipt': 8 * 1024 * 1024,
}
MAX_EXPLICIT_RECEIPTS_PER_RECORD = 16
MAX_ARCHIVE_BYTES_EMITTED = 1_350_000
MAX_STDOUT_BYTES = 1_900_000

artifacts = {}
artifact_origins = {}
read_cache = {}
attempted_inodes = set()
observed_paths = {}
errors = []
content_reads = []


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(raw):
    return json.dumps(raw, sort_keys=True, separators=(',', ':')).encode()


def identity(st):
    return {k: getattr(st, k) for k in (
        'st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns')}


def observe(path):
    path = Path(path)
    if not path.is_absolute() or '..' in path.parts:
        raise ValueError('nonabsolute or parent-traversing pointer: ' + str(path))
    if not path.is_relative_to('/workspace'):
        raise ValueError('pointer outside /workspace: ' + str(path))
    resolved = path.resolve(strict=True)
    if not resolved.is_relative_to('/workspace'):
        raise ValueError('resolved pointer outside /workspace: ' + str(path))
    ls, ss = path.lstat(), path.stat()
    if not stat.S_ISREG(ss.st_mode):
        raise ValueError('not a regular file: ' + str(path))
    return {'requested_path': str(path), 'resolved_path': str(resolved),
            'lstat': identity(ls), 'stat': identity(ss)}


def read_once(path, kind, keep_bytes=True):
    """A final metadata check is separate; there is no second content read."""
    path = Path(path)
    before = observe(path)
    if before['stat']['st_size'] > LIMITS[kind]:
        raise ValueError('input byte limit for ' + kind + ': ' + str(path))
    key = (before['stat']['st_dev'], before['stat']['st_ino'])
    if str(path) in observed_paths and observed_paths[str(path)] != before:
        raise ValueError('path changed since its first observation: ' + str(path))
    observed_paths[str(path)] = before
    if key in read_cache:
        item = read_cache[key]
        if item['stat'] != before['stat']:
            raise ValueError('cached inode changed: ' + str(path))
        if keep_bytes and item['raw'] is None:
            raise ValueError('refuse a second byte read for previously hashed inode')
        return item
    if key in attempted_inodes:
        raise ValueError('refuse a second content-read attempt after an earlier incomplete read')
    attempted_inodes.add(key)
    h = hashlib.sha256()
    chunks = [] if keep_bytes else None
    count = 0
    with path.open('rb') as f:
        if identity(os.fstat(f.fileno())) != before['stat']:
            raise ValueError('opened file identity differs: ' + str(path))
        while True:
            block = f.read(min(1024 * 1024, LIMITS[kind] - count + 1))
            if not block:
                break
            count += len(block)
            if count > LIMITS[kind]:
                raise ValueError('file grew beyond byte limit: ' + str(path))
            h.update(block)
            if chunks is not None:
                chunks.append(block)
        if identity(os.fstat(f.fileno())) != before['stat']:
            raise ValueError('file identity changed during read: ' + str(path))
    if observe(path) != before or count != before['stat']['st_size']:
        raise ValueError('path identity changed during read: ' + str(path))
    item = {'raw': b''.join(chunks) if chunks is not None else None,
            'bytes': count, 'sha256': h.hexdigest(), 'stat': before['stat']}
    read_cache[key] = item
    content_reads.append({'path': str(path), 'kind': kind,
                          'bytes': count, 'sha256': item['sha256']})
    return item


def put(name, raw, origin):
    if name in artifacts:
        if artifacts[name] != raw:
            raise ValueError('artifact name collision: ' + name)
        return
    artifacts[name] = raw
    artifact_origins[name] = origin


def resolved_pointer(root, value):
    if not isinstance(value, str) or not value or '\0' in value:
        raise ValueError('missing or invalid explicit record pointer')
    p = Path(value)
    return p if p.is_absolute() else root / p


def receipt_pointers(record):
    """Only explicit JSON pointers under record qualification/audit/receipt keys.

    Never follows external snapshots, dependency fields, commands, logs, or
    pointers inside a receipt's contents. Unknown pointer shapes stay in the
    preserved selected record for later review.
    """
    out = []

    def walk(value, chain, inherited_sha=None):
        if isinstance(value, dict):
            pin = value.get('sha256', inherited_sha)
            for key, child in value.items():
                low = str(key).lower()
                if low in ('external_snapshot', 'external_check', 'deps',
                           'dependency_signatures', 'dependency_file_check',
                           'command', 'commands', 'log', 'logs'):
                    continue
                if isinstance(child, str) and child.endswith('.json') and (
                    low == 'path' or low.endswith('_path') or
                    any(word in low for word in ('receipt', 'qualification', 'audit'))
                ):
                    out.append({'record_field': '.'.join(chain + [str(key)]),
                                'path': child, 'expected_sha256': pin})
                elif isinstance(child, (dict, list)):
                    walk(child, chain + [str(key)], pin)
        elif isinstance(value, list):
            for i, child in enumerate(value):
                if isinstance(child, (dict, list)):
                    walk(child, chain + [str(i)], inherited_sha)

    for key, value in record.items():
        if not any(word in key.lower() for word in ('qualification', 'receipt', 'audit')):
            continue
        if isinstance(value, str) and value.endswith('.json'):
            out.append({'record_field': key, 'path': value,
                        'expected_sha256': record.get(key + '_sha256')})
        elif isinstance(value, (dict, list)):
            walk(value, [key])
    if len(out) > MAX_EXPLICIT_RECEIPTS_PER_RECORD:
        raise ValueError('too many explicit receipt pointers; refusing wider read')
    return out


def check_pin(item, expected, label):
    if expected is None:
        return None
    if not isinstance(expected, str) or not re.fullmatch('[0-9a-f]{64}', expected):
        errors.append(label + ': invalid expected SHA256 field')
        return False
    ok = item['sha256'] == expected
    if not ok:
        errors.append(label + ': SHA256 mismatch')
    return ok


report = {
    'schema': 'p29_fullmember_and_pinned_project_adoption_readonly_v1',
    'module': MODULE,
    'script_sha256': sha(globals().get('SOURCE_TEXT', '').encode()),
    'registries': [],
    'adoption': {},
    'bounds': dict(LIMITS, max_archive_bytes_emitted=MAX_ARCHIVE_BYTES_EMITTED,
                   max_stdout_bytes=MAX_STDOUT_BYTES),
    'new_Lean_invocations': 0,
    'remote_filesystem_writes': 0,
    'dependency_recursion': False,
    'Affine54_source_object_or_log_reads': 0,
    'qualification_claim': False,
    'new_formal_credit': 0,
}

for root in ROOTS:
    label = root.name
    row = {'root': str(root), 'registry': str(root / '.lake/p2-private/records.json')}
    report['registries'].append(row)
    try:
        registry = read_once(row['registry'], 'registry')
        row.update({'registry_bytes': registry['bytes'],
                    'registry_sha256': registry['sha256']})
        data = json.loads(registry['raw'])
        if not isinstance(data, dict):
            raise ValueError('registry is not a module-keyed JSON object')
        row['exact_key_present'] = MODULE in data
        if MODULE not in data:
            continue
        record = data[MODULE]
        if not isinstance(record, dict) or record.get('module', MODULE) != MODULE:
            raise ValueError('selected record module/schema mismatch')
        record_bytes = canonical(record)
        row['record_canonical_sha256'] = sha(record_bytes)
        row['record_artifact'] = label + '/selected-record.canonical.json'
        put(row['record_artifact'], record_bytes,
            {'kind': 'derived_canonical_selected_record', 'registry': row['registry'],
             'key': MODULE, 'registry_sha256': registry['sha256']})
        row['source_and_object'] = {}
        for field, ext, kind, keep in (
            ('source', '.lean', 'source', True),
            ('object', '.olean', 'object_identity', False),
        ):
            binding = {'original_record_pointer': record.get(field),
                       'expected_sha256': record.get(field + '_sha256')}
            row['source_and_object'][field] = binding
            try:
                path = resolved_pointer(root, record.get(field))
                if path.name != BASENAME + ext:
                    raise ValueError('refuse pointer to a different module basename')
                item = read_once(path, kind, keep)
                binding.update({'path': str(path), 'bytes': item['bytes'],
                                'sha256': item['sha256'],
                                'expected_sha256_matches': check_pin(
                                    item, binding['expected_sha256'], label + ':' + field)})
                if keep:
                    name = label + '/' + BASENAME + ext
                    put(name, item['raw'], {'kind': 'original_source_bytes',
                                           'path': str(path)})
                    binding['artifact'] = name
                else:
                    binding['object_bytes_exported'] = False
            except Exception as exc:
                binding['error'] = type(exc).__name__ + ': ' + str(exc)
                errors.append(label + ':' + field + ': ' + binding['error'])
        pointers = receipt_pointers(record)
        row['explicit_qualification_receipt_pointers'] = pointers
        for number, pointer in enumerate(pointers):
            try:
                path = resolved_pointer(root, pointer['path'])
                is_adoption = path == ADOPTION
                item = read_once(path, 'adoption' if is_adoption else 'explicit_receipt')
                pointer.update({'resolved_requested_path': str(path),
                                'bytes': item['bytes'], 'sha256': item['sha256'],
                                'expected_sha256_matches': check_pin(
                                    item, pointer['expected_sha256'], label + ':receipt')})
                name = ('PROJECT_CACHE_ADOPTION.original.json' if is_adoption else
                        label + '/explicit-receipt-' + str(number) + '.original.json')
                put(name, item['raw'], {'kind': 'original_receipt_bytes',
                                       'path': str(path), 'record_field': pointer['record_field']})
                pointer['artifact'] = name
                pointer['contents_recursively_followed'] = False
            except Exception as exc:
                pointer['error'] = type(exc).__name__ + ': ' + str(exc)
                errors.append(label + ':receipt: ' + pointer['error'])
    except Exception as exc:
        row['error'] = type(exc).__name__ + ': ' + str(exc)
        errors.append(label + ': ' + row['error'])

try:
    item = read_once(ADOPTION, 'adoption')
    report['adoption'] = {
        'path': str(ADOPTION), 'bytes': item['bytes'], 'sha256': item['sha256'],
        'expected_sha256': ADOPTION_SHA256,
        'expected_sha256_matches': check_pin(item, ADOPTION_SHA256, 'pinned_adoption'),
        'artifact': 'PROJECT_CACHE_ADOPTION.original.json',
        'contents_recursively_followed': False,
    }
    put('PROJECT_CACHE_ADOPTION.original.json', item['raw'],
        {'kind': 'original_pinned_project_adoption_bytes', 'path': str(ADOPTION)})
    if report['adoption']['expected_sha256_matches']:
        adoption_data = json.loads(item['raw'])
        report['adoption']['json_type'] = type(adoption_data).__name__
        if isinstance(adoption_data, dict):
            report['adoption']['top_level_keys'] = list(adoption_data)
except Exception as exc:
    report['adoption']['error'] = type(exc).__name__ + ': ' + str(exc)
    errors.append('pinned_adoption: ' + report['adoption']['error'])

final_identities = []
for requested, before in observed_paths.items():
    entry = {'before': before}
    try:
        after = observe(requested)
        entry.update({'after': after, 'stable': after == before})
        if after != before:
            errors.append('final file identity changed: ' + requested)
    except Exception as exc:
        entry.update({'stable': False, 'error': type(exc).__name__ + ': ' + str(exc)})
        errors.append('final identity check: ' + requested + ': ' + entry['error'])
    final_identities.append(entry)

report.update({
    'content_reads': content_reads,
    'maximum_content_read_attempts_per_unique_inode': 1,
    'content_read_attempted_inode_count': len(attempted_inodes),
    'final_stability_check': 'path/resolved-path/lstat/fstat-derived identity including size/mtime_ns/ctime_ns; metadata only, no second content hash',
    'final_file_identities': final_identities,
    'errors': errors,
    'status': 'EXACT_READ_ONLY_COLLECTION_COMPLETE' if not errors else 'READ_ONLY_COLLECTION_HAS_ERRORS',
})
put('READONLY_RESULT.json', json.dumps(report, indent=2, ensure_ascii=False).encode() + b'\n',
    {'kind': 'derived_collection_report'})
manifest = {name: {'bytes': len(raw), 'sha256': sha(raw),
                   'origin': artifact_origins[name]}
            for name, raw in sorted(artifacts.items())}
manifest_raw = json.dumps(manifest, indent=2, ensure_ascii=False).encode() + b'\n'
buf = io.BytesIO()
with tarfile.open(fileobj=buf, mode='w:xz', preset=6) as archive:
    for name, raw in sorted(dict(artifacts, **{'MANIFEST.json': manifest_raw}).items()):
        info = tarfile.TarInfo(name)
        info.size = len(raw)
        info.mtime = 0
        info.mode = 0o444
        archive.addfile(info, io.BytesIO(raw))
archive_bytes = buf.getvalue()
emitted = archive_bytes[:MAX_ARCHIVE_BYTES_EMITTED]
complete = len(emitted) == len(archive_bytes)
meta = {
    'schema': report['schema'], 'status': report['status'],
    'script_sha256': report['script_sha256'],
    'archive_bytes': len(archive_bytes), 'archive_sha256': sha(archive_bytes),
    'archive_member_count': len(artifacts) + 1,
    'manifest_sha256': sha(manifest_raw),
    'complete_archive_transmitted': complete,
    'transmitted_offset': 0, 'transmitted_bytes': len(emitted),
    'transmitted_sha256': sha(emitted),
    'untransmitted_bytes': len(archive_bytes) - len(emitted),
    'archive_persisted_on_remote_filesystem': False,
    'fullmember_keys': [{k: row.get(k) for k in (
        'root', 'registry_sha256', 'exact_key_present', 'record_canonical_sha256', 'error')}
        for row in report['registries']],
    'adoption': {k: report['adoption'].get(k) for k in (
        'path', 'bytes', 'sha256', 'expected_sha256', 'expected_sha256_matches',
        'artifact', 'contents_recursively_followed')},
    'error_count': len(errors),
    'errors_preview_max_32_of_1000_chars': [e[:1000] for e in errors[:32]],
    'content_read_count': len(content_reads),
    'new_Lean_invocations': 0, 'remote_filesystem_writes': 0,
    'new_formal_credit': 0,
}
output = ('P29_FULLMEMBER_ADOPTION_META ' + json.dumps(meta, separators=(',', ':')) + '\n' +
          'P29_FULLMEMBER_ADOPTION_ARCHIVE_BASE64 ' + base64.b64encode(emitted).decode() + '\n')
if len(output.encode()) > MAX_STDOUT_BYTES:
    raise RuntimeError('refuse to emit stdout beyond explicit byte limit')
sys.stdout.write(output)
sys.exit(1 if errors else (0 if complete else 4))
