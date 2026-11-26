"""Exactly 28 readonly candidate observations; no Lean, search, or file writes."""
import datetime
import hashlib
import json
import os
import stat
import sys
import time

PAYLOAD = {'rows': [{'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBands', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean', 'bytes': 1005224, 'sha256': '7af00b12866a5df8dc2da5157172281aa509182a2a321390d60db10588b43b23'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBase', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean', 'bytes': 495736, 'sha256': 'bdb45e61412726782fc7801b23f786f8436a763d94330223c38c698e49137979'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBaseEstimate', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean', 'bytes': 302232, 'sha256': 'a0ed17870cc9b34aa77cc1eacc96380f26a136e98f5aba1a8f5e70418b0ff195'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean', 'bytes': 417864, 'sha256': '40e6739d0928ae2c70deca8b80307dd87595f0076c851e4a2cf9e0098a749b75'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean', 'bytes': 215320, 'sha256': '539aa96f95335718ebeaab8c69e9cdbdd5d00d7c929e8c61909592dfff628d7d'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean', 'bytes': 313800, 'sha256': 'f78a815dea0aad0833aac831dc2233cdcd3fd5c7681d6220be3b253786b1b5ee'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabIntegral', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean', 'bytes': 355112, 'sha256': '812cb313a21b538c183715b1b829d286628fd30a8a067ca43fb915a54b9a083b'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean', 'bytes': 239240, 'sha256': '1f48755c44eadce94bfd62332f1ca9c8892aefd7692a34407ecbcdb8350bcaef'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean', 'bytes': 708360, 'sha256': '85e0756e603bb8b5e51b87247b989a3eb0a7c0c25c9b6dfb1e786ebf2fbca739'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean', 'bytes': 452912, 'sha256': '326ca610964a3a6b2659cd4230681c266abbeb48c7b1fc0fcca322f33c592d90'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformAbel', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean', 'bytes': 1921552, 'sha256': '0891f3fa7c30839054029fa5b2b3d28b116a9bddb8a74e2207d223913ff0b368'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformFixedCompat', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean', 'bytes': 1339680, 'sha256': '71575dea300b4d15714d5c92392589faed3542cc3ee13a51284dbb6e0eb9faa1'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean']}, {'module': 'MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean', 'bytes': 320080, 'sha256': 'd5dcdada890ec4dc434a88a504b217db32372af941be97b722cb077116e3dc5f'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean']}, {'module': 'MathlibNt.Wu2008DoubleSieve.NonunitRoughUniformCore', 'P1_pin': {'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean', 'bytes': 379328, 'sha256': 'eb25d766e699e3e43d931758b0aa55a15d8da89b48f256bbee26064e7202713b'}, 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean']}], 'index_git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f', 'index_bytes': 35907, 'index_sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf'}
ROOTS = [
    '/workspace/p2-saving16-20261125/.lake/p2-private/lib',
    '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib',
]
PER_FILE_READ_LIMIT = 8 * 1024 * 1024
TOTAL_READ_LIMIT = 64 * 1024 * 1024
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
clock = time.monotonic()


def stamp(value):
    return [value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns]


def kind(mode):
    if stat.S_ISREG(mode):
        return 'regular_file'
    if stat.S_ISLNK(mode):
        return 'symlink'
    if stat.S_ISDIR(mode):
        return 'directory'
    return 'other_nonregular'


def observe(path):
    result = {'entry_exists': None, 'target_exists': None}
    try:
        link = os.lstat(path)
    except OSError as exc:
        result.update(entry_exists=False if isinstance(exc, FileNotFoundError) else None,
                      lstat_error={'errno': exc.errno, 'type': type(exc).__name__, 'message': str(exc)})
        return result
    result.update(entry_exists=True, entry_type=kind(link.st_mode), lstat_stamp=stamp(link))
    try:
        target = os.stat(path)
    except OSError as exc:
        result.update(target_exists=False if isinstance(exc, FileNotFoundError) else None,
                      stat_error={'errno': exc.errno, 'type': type(exc).__name__, 'message': str(exc)})
        return result
    result.update(target_exists=True, target_type=kind(target.st_mode), target_stamp=stamp(target))
    return result


assert isinstance(SOURCE_TEXT, str)
assert PAYLOAD['index_git_blob'] == '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'
assert PAYLOAD['index_sha256'] == 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf'
assert len(PAYLOAD['rows']) == 14
assert len({r['module'] for r in PAYLOAD['rows']}) == 14
candidates = []
for row in PAYLOAD['rows']:
    relative = row['module'].replace('.', '/') + '.olean'
    assert row['module'].startswith(('MathlibNt.SieveTheory.LiLiuPrereqBuchstab',
                                      'MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform'))
    assert row['P2_candidates'] == [root + '/' + relative for root in ROOTS]
    assert row['P1_pin']['path'] == '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/' + relative
    assert isinstance(row['P1_pin']['bytes'], int) and 0 < row['P1_pin']['bytes'] < PER_FILE_READ_LIMIT
    assert len(row['P1_pin']['sha256']) == 64 and all(c in '0123456789abcdef' for c in row['P1_pin']['sha256'])
    for root_index, path in enumerate(row['P2_candidates']):
        candidates.append({'module': row['module'], 'path': path, 'root_index': root_index,
                           'expected_P1_pin': row['P1_pin']})
assert len(candidates) == 28 and len({r['path'] for r in candidates}) == 28

cache = {}
rows = []
bytes_read = 0
physical_reads = 0
shared_hash_uses = 0
for candidate in candidates:
    row = dict(candidate)
    path = row['path']
    before = observe(path)
    row['before'] = before
    row['sha256'] = None
    row['observed_bytes'] = None
    row['hash_reused_from'] = None
    row['hash_stable_during_read'] = False
    if before.get('target_exists') is True and before.get('target_type') == 'regular_file':
        key = tuple(before['target_stamp'])
        row['observed_bytes'] = key[2]
        try:
            assert key[2] <= PER_FILE_READ_LIMIT, 'candidate exceeds explicit per-file read bound'
            if key in cache:
                cached = cache[key]
                row['sha256'] = cached['sha256']
                row['hash_reused_from'] = cached['path']
                shared_hash_uses += 1
            else:
                assert bytes_read + key[2] <= TOTAL_READ_LIMIT, 'explicit total byte-read bound exceeded'
                flags = os.O_RDONLY | os.O_NONBLOCK | os.O_CLOEXEC
                fd = os.open(path, flags)
                with os.fdopen(fd, 'rb') as stream:
                    opened = os.fstat(stream.fileno())
                    assert stat.S_ISREG(opened.st_mode), 'candidate changed to a nonregular file before open'
                    assert stamp(opened) == list(key), 'opened physical object differs from observed stamp'
                    digest = hashlib.sha256()
                    count = 0
                    while True:
                        chunk = stream.read(65536)
                        if not chunk:
                            break
                        count += len(chunk)
                        bytes_read += len(chunk)
                        assert count <= PER_FILE_READ_LIMIT and bytes_read <= TOTAL_READ_LIMIT, 'byte-read bound exceeded while hashing'
                        digest.update(chunk)
                    closed = os.fstat(stream.fileno())
                    assert stamp(opened) == stamp(closed), 'physical object changed while hashing'
                    assert count == key[2], 'read length differs from original observed size'
                    row['fstat_before'] = stamp(opened)
                    row['fstat_after'] = stamp(closed)
                    row['sha256'] = digest.hexdigest()
                    physical_reads += 1
            after_read = observe(path)
            row['after_hash'] = after_read
            assert before == after_read, 'candidate path or target changed during hash/reuse'
            row['hash_stable_during_read'] = True
            if key not in cache:
                cache[key] = {'sha256': row['sha256'], 'path': path}
        except (OSError, AssertionError) as exc:
            row['hash_error'] = {'type': type(exc).__name__, 'message': str(exc)}
    rows.append(row)

for row in rows:
    row['final'] = observe(row['path'])
    row['observation_unchanged_through_final_pass'] = row['before'] == row['final']
    row['size_matches_P1'] = row['observed_bytes'] == row['expected_P1_pin']['bytes']
    row['sha_matches_P1'] = row['sha256'] == row['expected_P1_pin']['sha256']
    row['stable_exact_P1_match'] = bool(row['hash_stable_during_read'] and
        row['observation_unchanged_through_final_pass'] and row['size_matches_P1'] and row['sha_matches_P1'])
    if not row['observation_unchanged_through_final_pass']:
        row['classification'] = 'CHANGED_DURING_OBSERVATION'
    elif row['before'].get('entry_exists') is False:
        row['classification'] = 'NO_ENTRY_AT_THIS_EXACT_CANDIDATE'
    elif row['before'].get('target_exists') is False:
        row['classification'] = 'NO_TARGET_AT_THIS_EXACT_CANDIDATE'
    elif row['stable_exact_P1_match']:
        row['classification'] = 'STABLE_EXACT_P1_OBJECT_BYTES'
    elif row['before'].get('target_exists') is True and row['before'].get('target_type') != 'regular_file':
        row['classification'] = 'NONREGULAR_TARGET'
    elif row['hash_stable_during_read']:
        row['classification'] = 'STABLE_DIFFERENT_BYTES_OR_SIZE'
    else:
        row['classification'] = 'READ_OR_STAT_ERROR_OR_EXPLICIT_READ_BOUND'

classifications = {}
for row in rows:
    key = row['classification']
    classifications[key] = classifications.get(key, 0) + 1
per_module = {}
for row in rows:
    item = per_module.setdefault(row['module'], {'matching_candidate_paths': [], 'checked_candidates': []})
    item['checked_candidates'].append({'path': row['path'], 'classification': row['classification']})
    if row['stable_exact_P1_match']:
        item['matching_candidate_paths'].append(row['path'])

result = {
    'schema': 'p29_P2_exact_28_native_candidate_readonly_observation_v1',
    'status': 'COMPLETE_READONLY_CANDIDATE_OBSERVATIONS_NOT_COMPILE_OR_SUPPLIER_QUALIFICATION',
    'started_utc': started,
    'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'elapsed_seconds': time.monotonic() - clock,
    'controller_sha256': hashlib.sha256(SOURCE_TEXT.encode()).hexdigest(),
    'index_git_blob': PAYLOAD['index_git_blob'],
    'index_bytes': PAYLOAD['index_bytes'],
    'index_sha256': PAYLOAD['index_sha256'],
    'physical_cache_key': ['st_dev', 'st_ino', 'st_size', 'st_mtime_ns', 'st_ctime_ns'],
    'physical_cache_requires_stable_open_read_close_and_path_stamps': True,
    'read_bounds': {'per_file_bytes': PER_FILE_READ_LIMIT, 'total_bytes': TOTAL_READ_LIMIT},
    'counts': {'candidate_paths': len(rows), 'modules': len(per_module), 'classifications': classifications,
               'physical_objects_hashed': physical_reads, 'total_object_bytes_read': bytes_read,
               'stable_physical_hash_cache_entries': len(cache), 'physical_hash_reuses': shared_hash_uses,
               'modules_with_at_least_one_stable_exact_P1_candidate': sum(bool(v['matching_candidate_paths']) for v in per_module.values())},
    'rows': rows,
    'per_module': per_module,
    'boundary': {'scope_only_these_28_exact_paths': True, 'unlisted_P2_locations_not_searched': True,
                 'missing_candidate_is_global_P2_absence': False, 'source_files_read': 0,
                 'filesystem_writes_requested': 0, 'Lean_invocations': 0, 'old_kernel_owned_replays': 0,
                 'native515_snapshot_modified': False, 'new_formal_credit': 0,
                 'native_or_standard_input_union_qualified': False},
}
encoded = json.dumps(result, sort_keys=True, separators=(',', ':'))
assert len(encoded.encode()) < 131072, 'bounded complete stdout would be exceeded'
print(encoded, flush=True)
