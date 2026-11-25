#!/usr/bin/env bash
set -euo pipefail
python3 -B - <<'PY'
import base64, collections, hashlib, io, json, lzma, os, stat, tarfile, time

ROOT = '/workspace/p1-complete-proof'
MODULES = (
    'ImbalancedChen.P5OriginalSignedMidpoint',
    'ImbalancedChen.P5OriginalTaylorFiveDimensionalMidpoint',
    'ImbalancedChen.P5RecordedOldFifthBlockTotals',
    'ImbalancedChen.P5SubdivisionStoredParentArchive',
)
MAX_RELATIVE_DEPTH = 12
MAX_DIRECTORIES = 25000
MAX_DIRECTORY_ENTRIES = 250000
MAX_SCAN_SECONDS = 120
MAX_RECEIPTS = 64
MAX_RECEIPT_BYTES = 4 * 1024 * 1024
MAX_TOTAL_RECEIPT_BYTES = 16 * 1024 * 1024
MAX_BOUNDARY_DETAILS = 256
MAX_ARCHIVE_BYTES = 4 * 1024 * 1024
EXPORT_DIRECTORY = '20261125-p14-continuation-export'
OUTPUT_NAME = 'object-only-normal-locator-01.tar.xz'

assert hasattr(os, 'O_NOFOLLOW') and os.open in os.supports_dir_fd
assert os.scandir in os.supports_fd
DIR_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
READ_FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
counts = collections.Counter()
boundary_counts = collections.Counter()
boundaries, rows, payloads = [], [], {}
stop_reason = None
started = time.monotonic()

def original_path(parts):
    return ROOT + ('/' + '/'.join(parts) if parts else '')

def boundary(reason, parts, error=None):
    boundary_counts[reason] += 1
    if len(boundaries) < MAX_BOUNDARY_DETAILS:
        item = {'reason': reason, 'path': original_path(parts)}
        if error is not None:
            item['errno'] = error.errno
        boundaries.append(item)

def halt(reason, parts):
    global stop_reason
    if stop_reason is None:
        stop_reason = reason
        boundary(reason, parts)

def time_or_stop(parts):
    if stop_reason is not None:
        return True
    if time.monotonic() - started >= MAX_SCAN_SECONDS:
        halt('SCAN_TIME_LIMIT', parts)
        return True
    return False

def identity(s):
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)

def probe_normal(normal_fd, parts, module):
    target = (*parts, module, 'NORMAL_PASS.json')
    if time_or_stop(parts):
        return
    if len(target) > MAX_RELATIVE_DEPTH:
        boundary('RECEIPT_PATH_DEPTH_LIMIT', target)
        return
    if len(rows) >= MAX_RECEIPTS:
        halt('RECEIPT_COUNT_LIMIT', target)
        return
    counts['exact_module_directory_probes'] += 1
    try:
        module_fd = os.open(module, DIR_FLAGS, dir_fd=normal_fd)
    except FileNotFoundError:
        counts['missing_exact_module_directories'] += 1
        return
    except OSError as exc:
        boundary('MODULE_DIRECTORY_REJECTED_NOFOLLOW', (*parts, module), exc)
        return
    try:
        try:
            file_fd = os.open('NORMAL_PASS.json', READ_FLAGS, dir_fd=module_fd)
        except FileNotFoundError:
            counts['missing_normal_pass_files'] += 1
            return
        except OSError as exc:
            boundary('NORMAL_PASS_OPEN_REJECTED_NOFOLLOW', target, exc)
            return
        try:
            with os.fdopen(file_fd, 'rb') as stream:
                before = os.fstat(stream.fileno())
                if not stat.S_ISREG(before.st_mode):
                    boundary('NONREGULAR_NORMAL_PASS', target)
                    return
                if before.st_size > MAX_RECEIPT_BYTES:
                    boundary('PER_RECEIPT_BYTE_LIMIT', target)
                    return
                if counts['receipt_bytes_read'] + before.st_size > MAX_TOTAL_RECEIPT_BYTES:
                    halt('TOTAL_RECEIPT_BYTE_LIMIT', target)
                    return
                data = stream.read(before.st_size)
                counts['receipt_bytes_read'] += len(data)
                after = os.fstat(stream.fileno())
            current = os.stat('NORMAL_PASS.json', dir_fd=module_fd, follow_symlinks=False)
            if (len(data) != before.st_size or not stat.S_ISREG(current.st_mode)
                    or identity(before) != identity(after) or identity(before) != identity(current)):
                boundary('NORMAL_PASS_CHANGED_DURING_READ', target)
                return
        except OSError as exc:
            boundary('NORMAL_PASS_READ_OR_POSTSTAT_ERROR', target, exc)
            return
        parsed_ok, module_matches = False, None
        try:
            parsed = json.loads(data)
            parsed_ok = True
            if isinstance(parsed, dict):
                module_matches = parsed.get('module') == module
        except (ValueError, UnicodeError, RecursionError):
            pass
        name = 'receipts/' + str(len(rows)).zfill(5) + '.NORMAL_PASS.json'
        payloads[name] = data
        rows.append({'path': name, 'source_path': original_path(target),
                     'requested_module': module, 'bytes': len(data),
                     'sha256': hashlib.sha256(data).hexdigest(),
                     'json_parse_ok': parsed_ok,
                     'receipt_module_field_matches_requested': module_matches,
                     'full_original_bytes_preserved': True,
                     'acceptance_claimed': False})
    finally:
        os.close(module_fd)

def walk(directory_fd, parts):
    if time_or_stop(parts):
        return
    if counts['directories_opened_for_search'] >= MAX_DIRECTORIES:
        halt('DIRECTORY_COUNT_LIMIT', parts)
        return
    counts['directories_opened_for_search'] += 1
    if parts and parts[-1] == 'normal':
        counts['normal_directories_observed'] += 1
        for module in MODULES:
            probe_normal(directory_fd, parts, module)
    if time_or_stop(parts):
        return
    child_directories = []
    try:
        with os.scandir(directory_fd) as entries:
            for entry in entries:
                if time_or_stop(parts):
                    return
                if counts['directory_entries_examined'] >= MAX_DIRECTORY_ENTRIES:
                    halt('DIRECTORY_ENTRY_LIMIT', parts)
                    return
                counts['directory_entries_examined'] += 1
                assert entry.name not in ('.', '..') and '/' not in entry.name
                if entry.is_symlink():
                    boundary('SYMLINK_NOT_FOLLOWED', (*parts, entry.name))
                elif entry.is_dir(follow_symlinks=False):
                    child_directories.append(entry.name)
    except OSError as exc:
        boundary('DIRECTORY_LISTING_ERROR', parts, exc)
        return
    for name in sorted(child_directories):
        child = (*parts, name)
        if time_or_stop(parts):
            return
        if len(child) >= MAX_RELATIVE_DEPTH:
            boundary('DIRECTORY_DEPTH_NOT_DESCENDED', child)
            continue
        try:
            child_fd = os.open(name, DIR_FLAGS, dir_fd=directory_fd)
        except OSError as exc:
            boundary('DIRECTORY_OPEN_REJECTED_NOFOLLOW', child, exc)
            continue
        try:
            walk(child_fd, child)
        finally:
            os.close(child_fd)

root_fd = os.open('/', DIR_FLAGS)
try:
    for component in ROOT.strip('/').split('/'):
        next_fd = os.open(component, DIR_FLAGS, dir_fd=root_fd)
        os.close(root_fd)
        root_fd = next_fd
    try:
        prior_export_fd = os.open(EXPORT_DIRECTORY, DIR_FLAGS, dir_fd=root_fd)
    except FileNotFoundError:
        prior_export_fd = None
    if prior_export_fd is not None:
        try:
            try:
                os.stat(OUTPUT_NAME, dir_fd=prior_export_fd, follow_symlinks=False)
            except FileNotFoundError:
                pass
            else:
                raise FileExistsError('fixed output already exists; no search performed')
        finally:
            os.close(prior_export_fd)
    walk(root_fd, ())
    manifest = {
        'schema': 'p14_bounded_original_normal_locator_v1',
        'status': 'BOUNDED_EXISTING_NORMAL_OBSERVATION_NOT_ACCEPTANCE',
        'root': ROOT, 'exact_modules': list(MODULES),
        'only_input_file_pattern': '*/normal/<one exact module>/NORMAL_PASS.json',
        'maximum_relative_path_components_including_receipt_filename': MAX_RELATIVE_DEPTH,
        'directory_names_at_depth_12_are_not_descended': True,
        'limits': {'directories': MAX_DIRECTORIES, 'directory_entries': MAX_DIRECTORY_ENTRIES,
                   'scan_seconds': MAX_SCAN_SECONDS, 'receipts': MAX_RECEIPTS,
                   'per_receipt_bytes': MAX_RECEIPT_BYTES,
                   'total_receipt_bytes_read': MAX_TOTAL_RECEIPT_BYTES,
                   'boundary_details': MAX_BOUNDARY_DETAILS, 'archive_bytes': MAX_ARCHIVE_BYTES},
        'counters': dict(counts), 'scan_stop_reason': stop_reason,
        'unsearched_boundary_counts': dict(boundary_counts),
        'unsearched_boundary_details': boundaries,
        'omitted_boundary_detail_count': sum(boundary_counts.values()) - len(boundaries),
        'unsearched_regions': ['all locations outside the fixed root',
            'receipt paths with more than 12 relative components',
            'symlink targets and unreadable or changed paths',
            'remaining directories after any operational limit stops the search'],
        'files': rows, 'file_count': len(rows),
        'retained_candidates_by_module': {m: sum(r['requested_module'] == m for r in rows)
                                          for m in MODULES},
        'full_json_delivery': 'Each listed archive member preserves all original NORMAL_PASS bytes.',
        'not_found_is_not_global_absence': True,
        'existing_objects_must_not_be_deleted_or_force_rebuilt': True,
        'source_commit_or_context_rewritten': False,
        'non_target_file_contents_opened': False,
        'compiler_or_kernel_invoked': False,
        'acceptance_claimed': False, 'whole_P1_4_complete': False,
    }
    payloads['EXPORT_MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode='w', format=tarfile.PAX_FORMAT) as tar:
        for name in sorted(payloads):
            data = payloads[name]
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mode = 0o644
            info.mtime = 0
            info.uid = info.gid = 0
            info.uname = info.gname = ''
            tar.addfile(info, io.BytesIO(data))
    blob = lzma.compress(raw.getvalue(), preset=6)
    assert len(blob) <= MAX_ARCHIVE_BYTES, 'archive exceeds fixed transport budget; no output created'
    try:
        os.mkdir(EXPORT_DIRECTORY, dir_fd=root_fd)
    except FileExistsError:
        pass
    export_fd = os.open(EXPORT_DIRECTORY, DIR_FLAGS, dir_fd=root_fd)
    try:
        # O_EXCL supplies xb semantics; O_NOFOLLOW also rejects an existing symlink.
        output_fd = os.open(OUTPUT_NAME, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                            0o600, dir_fd=export_fd)
        with os.fdopen(output_fd, 'wb') as stream:
            stream.write(blob)
    finally:
        os.close(export_fd)
    print(json.dumps({'status': 'BOUNDED_NORMAL_LOCATOR_EXPORT_NOT_ACCEPTANCE',
        'path': ROOT + '/' + EXPORT_DIRECTORY + '/' + OUTPUT_NAME,
        'bytes': len(blob), 'sha256': hashlib.sha256(blob).hexdigest(),
        'manifest_sha256': hashlib.sha256(payloads['EXPORT_MANIFEST.json']).hexdigest(),
        'file_count': len(rows), 'scan_stop_reason': stop_reason,
        'not_found_is_not_global_absence': True,
        'acceptance_claimed': False, 'whole_P1_4_complete': False}), flush=True)
    print('P14_NORMAL_LOCATOR_BASE64_BEGIN', flush=True)
    print(base64.b64encode(blob).decode(), flush=True)
    print('P14_NORMAL_LOCATOR_BASE64_END', flush=True)
finally:
    os.close(root_fd)
PY
