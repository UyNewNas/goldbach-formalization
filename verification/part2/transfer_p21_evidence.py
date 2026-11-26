#!/usr/bin/env python3
"""P2.1 exact-byte evidence transport. Byte transport only; no proof credit.

Reuse the existing 1_200_000-byte Git evidence part convention.

After root has observed the finalizer's successful terminal job and exact
FINALIZATION.json path, byte count and SHA256:

  plan FINALIZATION_PATH FINALIZATION_SHA256 FINALIZATION_BYTES REMOTE_PLAN_PATH
       [RETENTION_PATH RETENTION_SHA256]
      -> stdout: one transfer-manifest JSON (save and pin its own SHA256).
Optional retention pins a successful PERSISTENT_COPY.json; the original
FINALIZATION bytes are never rewritten, and every actual file is frozen normally.

  emit PLAN_PATH PLAN_SHA256 ASSET INDEX
      -> stdout: ONLY the exact raw bytes of one <=1_200_000-byte part.

  job-request LOCAL_PLAN_PATH PLAN_SHA256 ASSET INDEX ATTEMPT
      -> exact run_command argument object. Root submits that object unchanged.
The canonical command fixes helper/plan paths, digests, asset/index and a unique
stderr pathname. It checks helper SHA independently, emits only raw bytes, then
requires an empty stderr file. No echo, tracing, or hash summaries go to stdout.

Retrieve ONLY output_base64 from read_task_output, decoding every page as bytes
and assembling at its actual byte offset. Persist the complete original tool
responses separately. Never encode or re-encode the decoded UTF-8 output field.
Capture names: ASSET.00000.bin and ASSET.00000.capture.json, etc.
Capture schema (all call envelopes contain the COMPLETE unmodified tool result):
  {schema: 'p21-raw-task-capture/v1', synthetic_test_only: false,
   attempt: ACTUAL_ATTEMPT_LABEL,
   submission: {tool: RUN_TOOL, arguments: ACTUAL_ARGUMENTS, result: RAW_RESULT},
   terminal: {tool: GET_TOOL, arguments: {task_id: ID}, result: RAW_RESULT},
   pages: [{tool: READ_TOOL, arguments: {task_id: ID, offset: N, limit: L},
            result: RAW_RESULT}, ...]}
Store the observed successful terminal result BEFORE collecting the final pages.
Neither job_id nor offset is echoed by P2 read_task_output; bind its actual request.
No normalized success/continuity booleans are accepted as evidence.

  accept PLAN_PATH PLAN_SHA256 ASSET INDEX CAPTURE_PATH RAW_CALLS_PATH
      -> stdout: verified part receipt, including SHA256 and Git blob SHA1.
  assemble PLAN_PATH PLAN_SHA256 ASSET CAPTURE_DIRECTORY OUTPUT_PATH
      -> validates every part's receipt/hash, writes a new output, verifies its
         full original hash, and renames only that owned partial file.
         An existing exact OUTPUT is reused ONLY AFTER revalidating this round's
         complete part evidence. Owned unique partial files are cleaned on failure.

This helper does not call any cloud, GitHub, Library, network, or compiler API.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import stat
import sys
import tempfile

PART_BYTES = 1_200_000
TOOL_PREFIX = 'mcp__codex_apps__cloud_compile_private_8e1da5a7_'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob_sha(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode('ascii') + b'\0' + data).hexdigest()

def stamp(s):
    return {key: getattr(s, key) for key in
            ('st_dev', 'st_ino', 'st_mode', 'st_nlink', 'st_size', 'st_mtime_ns', 'st_ctime_ns')}

def regular(path):
    require(path.is_absolute() and path.resolve(strict=True) == path, 'Noncanonical source: ' + str(path))
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'Nonregular source: ' + str(path))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    stream = os.fdopen(fd, 'rb')
    require(stamp(os.fstat(fd)) == stamp(before), 'Source changed before open')
    return stream, stamp(before)

def unchanged(path, stream, before):
    require(path.resolve(strict=True) == path and stamp(path.lstat()) == before
            and stamp(os.fstat(stream.fileno())) == before, 'Source stamp changed: ' + str(path))

def frozen_bytes(path, expected_sha, expected_bytes=None):
    stream, before = regular(path)
    with stream:
        raw = stream.read()
        unchanged(path, stream, before)
    require(sha(raw) == expected_sha and (expected_bytes is None or len(raw) == expected_bytes), 'Pinned bytes differ')
    return raw

def freeze(info):
    path = Path(info['path'])
    require(re.fullmatch('[0-9a-f]{64}', info['sha256']) is not None, 'Bad expected digest')
    stream, before = regular(path)
    digest, pieces, count = hashlib.sha256(), [], 0
    with stream:
        while True:
            data = stream.read(PART_BYTES)
            if not data:
                break
            pieces.append({'index': len(pieces), 'offset': count, 'bytes': len(data),
                           'sha256': sha(data), 'git_blob_sha': blob_sha(data)})
            digest.update(data)
            count += len(data)
        unchanged(path, stream, before)
    require(count == info['bytes'] == before['st_size'] and digest.hexdigest() == info['sha256'], 'Finalization file binding differs')
    return {'path': str(path), 'bytes': count, 'sha256': info['sha256'], 'stamp': before, 'parts': pieces}

def make_plan(path, expected_sha, expected_bytes, remote_plan_path, synthetic_test_only=False,
              retention_path=None, retention_sha=None):
    raw = frozen_bytes(path, expected_sha, expected_bytes)
    final = json.loads(raw)
    require(len(final['joint_receipt_probe_log']) == 3, 'Need all three original joint files')
    infos = {
        'finalization': {'path': str(path), 'bytes': len(raw), 'sha256': expected_sha},
        'archive': final['archive'],
        'export_manifest': final['export_manifest'],
        'joint_receipt': final['joint_receipt_probe_log'][0],
        'joint_probe': final['joint_receipt_probe_log'][1],
        'joint_log': final['joint_receipt_probe_log'][2],
        'verification': final['verification'],
    }
    require(len({r['path'] for r in infos.values()}) == len(infos), 'Unexpected duplicate asset path')
    require((retention_path is None) == (retention_sha is None), 'Retention path and digest are required together')
    binding = None
    if retention_path is not None:
        retained_raw = frozen_bytes(retention_path, retention_sha)
        retained = json.loads(retained_raw)
        require(type(retained['finalizer_exit_code']) is int and retained['finalizer_exit_code'] == 0,
                'Retention requires a successful finalizer')
        original, persistent = Path(retained['original_output']), Path(retained['persistent_output'])
        require(original.is_absolute() and persistent.is_absolute(), 'Retention output paths must be absolute')
        rows = retained['copied_files']
        require(isinstance(rows, list), 'Persistent copies must be a list')
        joint_sources = {info['path'] for info in final['joint_receipt_probe_log']}
        copies, destinations = {}, set()
        for row in rows:
            source, target = Path(row['source']), Path(row['path'])
            require(source.is_absolute() and target.is_absolute()
                    and str(source) == row['source'] and '..' not in source.parts
                    and str(target) == row['path'] and '..' not in target.parts
                    and (source.is_relative_to(original) or row['source'] in joint_sources)
                    and target.is_relative_to(persistent)
                    and type(row['bytes']) is int and row['bytes'] >= 0
                    and re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None,
                    'Invalid persistent copy binding')
            require(row['source'] not in copies and row['path'] not in destinations,
                    'Duplicate persistent copy mapping')
            copies[row['source']] = row
            destinations.add(row['path'])
        final_copy = next((row for row in rows if row['path'] == str(path)), None)
        require(final_copy is None or (final_copy['bytes'] == len(raw) and final_copy['sha256'] == expected_sha),
                'Persistent FINALIZATION binding differs')
        replacements = {}
        for name, info in infos.items():
            row = copies.get(info['path'])
            if row is not None:
                require(row['bytes'] == info['bytes'] and row['sha256'] == info['sha256'],
                        'Persistent copy differs from FINALIZATION: ' + name)
                replacements[name] = {key: row[key] for key in ('source', 'path', 'bytes', 'sha256')}
                infos[name] = {**info, 'path': row['path']}
        binding = {'path': str(retention_path), 'bytes': len(retained_raw), 'sha256': retention_sha,
                   'original_output': str(original), 'persistent_output': str(persistent),
                   'replacements': replacements}
        infos['retention'] = {key: binding[key] for key in ('path', 'bytes', 'sha256')}
        require(len({r['path'] for r in infos.values()}) == len(infos), 'Unexpected duplicate retained asset path')
    assets = {name: freeze(info) for name, info in infos.items()}
    for entry in assets.values():
        require(stamp(Path(entry['path']).lstat()) == entry['stamp'], 'Asset changed during planning')
    require(remote_plan_path.is_absolute() and remote_plan_path.parent.resolve(strict=True) == remote_plan_path.parent
            and remote_plan_path.resolve(strict=False) == remote_plan_path, 'Remote plan path is redirected')
    plan = {'schema': 'p21-final-raw-stdout-parts/v2', 'part_bytes': PART_BYTES,
            'producer_sha256': sha(Path(__file__).read_bytes()),
            'producer_path': str(Path(__file__).resolve()), 'remote_plan_path': str(remote_plan_path),
            'remote_cwd': str(Path.cwd().resolve()), 'synthetic_test_only': synthetic_test_only,
            'finalization_sha256': expected_sha, 'git_commit': final['git_commit'],
            'source_snapshot_commit': final['source_snapshot_commit'], 'git_tree': final['git_tree'],
            'assets': assets, 'compile_credit': False, 'kernel_credit': False}
    if binding is not None:
        plan['retention_binding'] = binding
    return plan

def load_plan(path, expected_sha):
    plan = json.loads(frozen_bytes(path, expected_sha))
    require(plan['schema'] == 'p21-final-raw-stdout-parts/v2' and plan['part_bytes'] == PART_BYTES, 'Unexpected plan format')
    require(plan['producer_sha256'] == sha(Path(__file__).read_bytes()), 'Producer bytes changed')
    for entry in plan['assets'].values():
        offset = 0
        for index, piece in enumerate(entry['parts']):
            require(piece['index'] == index and piece['offset'] == offset
                    and 0 < piece['bytes'] <= PART_BYTES, 'Noncontiguous part plan')
            offset += piece['bytes']
        require(offset == entry['bytes'], 'Part plan has wrong total size')
    return plan

def emit(plan, asset, index):
    entry = plan['assets'][asset]
    require(0 <= index < len(entry['parts']), 'Part index out of range')
    piece = entry['parts'][index]
    path = Path(entry['path'])
    stream, before = regular(path)
    with stream:
        require(before == entry['stamp'], 'Frozen source stamp differs')
        stream.seek(piece['offset'])
        data = stream.read(piece['bytes'])
        unchanged(path, stream, before)
    require(len(data) == piece['bytes'] and sha(data) == piece['sha256']
            and blob_sha(data) == piece['git_blob_sha'], 'Frozen part bytes differ')
    sys.stdout.buffer.write(data)
    sys.stdout.buffer.flush()

def job_request(plan, plan_sha, asset, index, attempt):
    require(asset in plan['assets'] and re.fullmatch('[a-z_]+', asset) is not None, 'Invalid asset name')
    require(0 <= index < len(plan['assets'][asset]['parts']), 'Part index out of range')
    require(re.fullmatch('[a-zA-Z0-9_-]{1,64}', attempt) is not None, 'Invalid attempt label')
    require(re.fullmatch('[0-9a-f]{64}', plan_sha) is not None, 'Invalid plan digest')
    producer, remote_plan = plan['producer_path'], plan['remote_plan_path']
    err = str(Path(remote_plan).parent / f'{asset}.{index:05}.{attempt}.stderr')
    check_code = ('import hashlib,pathlib,sys; '
                  'assert hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest()==sys.argv[2]')
    check = shlex.join(['python3', '-I', '-B', '-c', check_code, producer, plan['producer_sha256']])
    emit_command = shlex.join(['python3', '-I', '-B', producer, 'emit', remote_plan, plan_sha, asset, str(index)])
    command = ('set -euo pipefail\nset -o noclobber\n{\n  ' + check + '\n  ' + emit_command
               + '\n} 2>' + shlex.quote(err) + '\ntest ! -s ' + shlex.quote(err) + '\n')
    return {'command': command, 'cwd': plan['remote_cwd'], 'cpu_threads': 1,
            'memory_mb': 512, 'timeout_seconds': 120}

def payload(envelope, suffix):
    require(envelope['tool'] == TOOL_PREFIX + suffix and isinstance(envelope['arguments'], dict), 'Wrong tool/request envelope')
    result = envelope['result']
    require(isinstance(result, dict) and result.get('isError', False) is False, 'Tool returned an error')
    structured = result.get('structuredContent')
    contents = result.get('content', [])
    parsed = None
    if contents:
        require(len(contents) == 1 and contents[0]['type'] == 'text', 'Unexpected MCP content wrapper')
        parsed = json.loads(contents[0]['text'])
        require(isinstance(parsed, dict), 'Tool payload is not an object')
    if structured is not None:
        require(isinstance(structured, dict) and (parsed is None or parsed == structured), 'MCP response layers disagree')
        return structured
    require(parsed is not None, 'Missing tool payload')
    return parsed

def validate_capture(plan, plan_sha, asset, index, data, capture, allow_synthetic=False):
    require(capture['schema'] == 'p21-raw-task-capture/v1', 'Wrong capture schema')
    synthetic = capture['synthetic_test_only']
    require(type(synthetic) is bool and (not synthetic or allow_synthetic)
            and plan['synthetic_test_only'] is synthetic, 'Synthetic evidence cannot enter production acceptance')
    piece = plan['assets'][asset]['parts'][index]
    submitted = capture['submission']
    expected = job_request(plan, plan_sha, asset, index, capture['attempt'])
    require(submitted['arguments'] == expected, 'Actual submission differs from the pinned canonical job request')
    response = payload(submitted, 'run_command')
    job = response['job_id']
    require(isinstance(job, str) and re.fullmatch('[0-9a-f]{32}', job) is not None, 'Invalid submitted job ID')
    terminal = capture['terminal']
    require(terminal['arguments'] == {'task_id': job}, 'Terminal request refers to another job')
    state = payload(terminal, 'get_task')
    require(state['job_id'] == state['task_id'] == job and state['cwd'] == expected['cwd']
            and state['status'] == 'succeeded' and type(state['exit_code']) is int and state['exit_code'] == 0,
            'Actual producer job is not succeeded/rc0 at the bound cwd')
    require(state['log_truncated'] is False and type(state['log_discarded_bytes']) is int
            and state['log_discarded_bytes'] == 0 and type(state['log_bytes']) is int
            and state['log_bytes'] == piece['bytes'] == len(data), 'Terminal log length/flags differ')
    pages = capture['pages']
    require(isinstance(pages, list) and bool(pages), 'No raw page evidence')
    cursor = 0
    for index_in_capture, page in enumerate(pages):
        request = page['arguments']
        require(set(request) == {'task_id', 'offset', 'limit'} and request['task_id'] == job
                and type(request['offset']) is int and request['offset'] == cursor
                and type(request['limit']) is int and request['limit'] > 0, 'Page request is foreign, missing, overlapping or out of order')
        body = payload(page, 'read_task_output')
        require(body['log_truncated'] is False and type(body['discarded_bytes']) is int
                and body['discarded_bytes'] == 0, 'A page reports lost bytes')
        require(isinstance(body['stream'], str) and bool(body['stream']), 'Missing stream descriptor')
        require(isinstance(body['output_base64'], str), 'No lossless page bytes')
        raw = base64.b64decode(body['output_base64'], validate=True)
        require(len(raw) <= request['limit'] and type(body['next_offset']) is int
                and body['next_offset'] == cursor + len(raw), 'Page offset does not match raw byte count')
        require(data[cursor:cursor + len(raw)] == raw, 'Raw page bytes differ from the saved capture')
        last = index_in_capture == len(pages) - 1
        require(type(body['eof']) is bool and body['eof'] is last, 'Missing final EOF or premature EOF')
        require(last or bool(raw), 'Empty nonterminal page')
        cursor += len(raw)
    require(cursor == len(data) == piece['bytes'], 'Page coverage is incomplete')
    return job

def accept(plan, plan_sha, asset, index, capture_path, calls_path, allow_synthetic=False):
    entry = plan['assets'][asset]
    require(0 <= index < len(entry['parts']), 'Part index out of range')
    piece = entry['parts'][index]
    stream, before = regular(calls_path)
    with stream:
        saved = stream.read()
        unchanged(calls_path, stream, before)
    capture = json.loads(saved)
    data = frozen_bytes(capture_path, piece['sha256'], piece['bytes'])
    require(blob_sha(data) == piece['git_blob_sha'], 'Git blob digest differs')
    job = validate_capture(plan, plan_sha, asset, index, data, capture, allow_synthetic)
    return data, {'asset': asset, **piece, 'job_id': job, 'raw_capture_calls_sha256': sha(saved),
                  'status': 'SYNTHETIC_VALIDATED_PART' if capture['synthetic_test_only'] else 'VERIFIED_ORIGINAL_PART'}

def digest_file(path):
    stream, before = regular(path)
    with stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
        unchanged(path, stream, before)
    return before['st_size'], digest

def assemble(plan, plan_sha, asset, directory, output, allow_synthetic=False):
    entry = plan['assets'][asset]
    require(output.is_absolute() and output.parent.resolve(strict=True) == output.parent, 'Output parent is redirected')
    require(not plan['synthetic_test_only'] or allow_synthetic, 'Synthetic plan is not production evidence')
    exists = os.path.lexists(output)
    partial = dest = own_inode = None
    if not exists:
        fd, name = tempfile.mkstemp(prefix=output.name + '.', suffix='.partial', dir=output.parent)
        partial = Path(name)
        own_inode = (os.fstat(fd).st_dev, os.fstat(fd).st_ino)
        dest = os.fdopen(fd, 'wb')
    h, count, receipts = hashlib.sha256(), 0, []
    try:
        for piece in entry['parts']:
            prefix = f'{asset}.{piece["index"]:05}'
            data, receipt = accept(plan, plan_sha, asset, piece['index'], directory / (prefix + '.bin'),
                                   directory / (prefix + '.capture.json'), allow_synthetic)
            if dest is not None:
                dest.write(data)
            h.update(data)
            count += len(data)
            receipts.append(receipt)
        if dest is not None:
            dest.close()
            dest = None
        require((count, h.hexdigest()) == (entry['bytes'], entry['sha256']), 'Reassembled original hash differs')
        require(digest_file(output if exists else partial) == (entry['bytes'], entry['sha256']), 'Full written/existing original readback differs')
        if not exists:
            os.link(partial, output)  # Does not replace an existing destination.
        return {'asset': asset, 'path': str(output),
                'status': ('SYNTHETIC_REASSEMBLED' if plan['synthetic_test_only'] else
                           'REUSED_WITH_VERIFIED_TRANSFER_EVIDENCE' if exists else 'VERIFIED_REASSEMBLED_ORIGINAL'),
                'bytes': count, 'sha256': h.hexdigest(), 'verified_parts': receipts}
    finally:
        if dest is not None:
            dest.close()
        if partial is not None and os.path.lexists(partial):
            current = partial.lstat()
            require((current.st_dev, current.st_ino) == own_inode, 'Owned partial path was replaced; refusing cleanup')
            partial.unlink()

def main(argv):
    require(bool(argv), 'Choose plan, job-request, emit, accept or assemble; no default operation')
    if argv[0] == 'plan':
        require(len(argv) in (5, 7), 'plan PATH SHA256 BYTES REMOTE_PLAN_PATH [RETENTION_PATH RETENTION_SHA256]')
        result = make_plan(Path(argv[1]), argv[2], int(argv[3]), Path(argv[4]),
                           retention_path=Path(argv[5]) if len(argv) == 7 else None,
                           retention_sha=argv[6] if len(argv) == 7 else None)
    else:
        require(len(argv) >= 4, 'A pinned plan and asset are required')
        plan = load_plan(Path(argv[1]), argv[2])
        asset = argv[3]
        if argv[0] == 'job-request':
            require(len(argv) == 6, 'job-request PLAN SHA256 ASSET INDEX ATTEMPT')
            result = job_request(plan, argv[2], asset, int(argv[4]), argv[5])
        elif argv[0] == 'emit':
            require(len(argv) == 5, 'emit PLAN SHA256 ASSET INDEX')
            emit(plan, asset, int(argv[4]))
            return
        elif argv[0] == 'accept':
            require(len(argv) == 7, 'accept PLAN SHA256 ASSET INDEX CAPTURE RAW_CALLS')
            _, result = accept(plan, argv[2], asset, int(argv[4]), Path(argv[5]), Path(argv[6]))
        elif argv[0] == 'assemble':
            require(len(argv) == 6, 'assemble PLAN SHA256 ASSET CAPTURE_DIRECTORY OUTPUT')
            result = assemble(plan, argv[2], asset, Path(argv[4]), Path(argv[5]))
        else:
            raise ValueError('Unknown operation')
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == '__main__':
    try:
        main(sys.argv[1:])
    except Exception as error:
        print(type(error).__name__ + ': ' + str(error), file=sys.stderr)
        raise SystemExit(1)
