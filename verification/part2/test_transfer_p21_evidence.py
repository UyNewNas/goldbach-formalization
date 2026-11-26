#!/usr/bin/env python3
"""Synthetic/local byte-transport regression only. No MCP, Lean, Git or network calls."""
import base64
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

import transfer_p21_evidence

SCRIPT = Path(transfer_p21_evidence.__file__).resolve()
M = vars(transfer_p21_evidence)
PASSED = []

def rejected(action):
    try:
        action()
    except (ValueError, KeyError, TypeError):
        return
    raise AssertionError('Invalid transport evidence was accepted')

def envelope(suffix, arguments, body):
    return {'tool': M['TOOL_PREFIX'] + suffix, 'arguments': arguments,
            'result': {'content': [{'type': 'text', 'text': json.dumps(body)}],
                       'structuredContent': None, 'isError': False}}

def main():
    with tempfile.TemporaryDirectory(prefix='p21-transfer-synthetic-', dir='/tmp') as name:
        root = Path(name)
        captures, outputs = root / 'captures', root / 'outputs'
        captures.mkdir()
        outputs.mkdir()
        original_output = root / 'tmpfs'
        original_output.mkdir()
        def put(name, data):
            path = root / name
            path.write_bytes(data)
            return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
        archive_data = (bytes(range(256)) * 4688)[:1_200_017]
        final = {
            'archive': put('tmpfs/archive.bin', archive_data),
            'export_manifest': put('tmpfs/manifest.json', b'{"synthetic_only":true}\n'),
            'joint_receipt_probe_log': [put('joint-receipt.json', b'{"synthetic_only":true}\n'),
                                       put('Joint.lean', b'-- synthetic only\n'), put('joint.log', b'')],
            'verification': put('tmpfs/verification.json', b'{"synthetic_only":true}\n'),
            'git_commit': 'synthetic-only', 'source_snapshot_commit': 'synthetic-only', 'git_tree': 'synthetic-only',
        }
        final_info = put('tmpfs/FINALIZATION.json', (json.dumps(final) + '\n').encode())
        plan_path = root / 'PLAN.json'
        plan = M['make_plan'](Path(final_info['path']), final_info['sha256'], final_info['bytes'], plan_path,
                              synthetic_test_only=True)
        plan_path.write_text(json.dumps(plan))
        plan_sha = hashlib.sha256(plan_path.read_bytes()).hexdigest()
        M['load_plan'](plan_path, plan_sha)
        require = M['require']
        require(len(plan['assets']) == 7 and len(plan['assets']['archive']['parts']) == 2
                and 'retention_binding' not in plan, 'Wrong synthetic inventory')
        PASSED.append('seven source assets; exactly two archive parts, 1200000 + 17 raw bytes')
        originals = {}
        for index, piece in enumerate(plan['assets']['archive']['parts']):
            request = M['job_request'](plan, plan_sha, 'archive', index, 'synthetic-attempt')
            # Execute the canonical producer command locally, never via a cloud/MCP tool.
            child = subprocess.run(['bash', '-c', request['command']], cwd=request['cwd'], capture_output=True)
            require(child.returncode == 0 and child.stderr == b'' and child.stdout == archive_data[piece['offset']:piece['offset'] + piece['bytes']], 'Canonical producer differs')
            job = f'{index + 1:032x}'
            submission = envelope('run_command', request, {'job_id': job, 'status': 'queued', 'queue_position': 0})
            state = {'job_id': job, 'task_id': job, 'cwd': request['cwd'], 'status': 'succeeded', 'exit_code': 0,
                     'log_bytes': len(child.stdout), 'log_truncated': False, 'log_discarded_bytes': 0}
            pages = []
            cursor = 0
            while cursor < len(child.stdout):
                data = child.stdout[cursor:cursor + 65536]
                arguments = {'task_id': job, 'offset': cursor, 'limit': 65536}
                cursor += len(data)
                body = {'output': data.decode('utf-8', errors='replace'),
                        'output_base64': base64.b64encode(data).decode('ascii'), 'stream': 'combined',
                        'next_offset': cursor, 'eof': cursor == len(child.stdout),
                        'log_truncated': False, 'discarded_bytes': 0}
                pages.append(envelope('read_task_output', arguments, body))
            capture = {'schema': 'p21-raw-task-capture/v1', 'synthetic_test_only': True,
                       'attempt': 'synthetic-attempt', 'submission': submission,
                       'terminal': envelope('get_task', {'task_id': job}, state), 'pages': pages}
            prefix = captures / f'archive.{index:05}'
            Path(str(prefix) + '.bin').write_bytes(child.stdout)
            Path(str(prefix) + '.capture.json').write_text(json.dumps(capture))
            originals[index] = capture
            M['accept'](plan, plan_sha, 'archive', index, Path(str(prefix) + '.bin'),
                        Path(str(prefix) + '.capture.json'), allow_synthetic=True)
        PASSED.append('actual local binary stdout survives all byte values/NULs; raw MCP-shaped pages match byte-for-byte')
        raw_path = captures / 'archive.00000.bin'
        calls_path = captures / 'archive.00000.capture.json'
        def check_capture(value, message):
            calls_path.write_text(json.dumps(value))
            rejected(lambda: M['accept'](plan, plan_sha, 'archive', 0, raw_path, calls_path, allow_synthetic=True))
            PASSED.append(message)
        value = copy.deepcopy(originals[0]); value['pages'][1]['arguments']['offset'] += 1
        check_capture(value, 'reject a discontinuous page request offset')
        value = copy.deepcopy(originals[0]); body = json.loads(value['pages'][0]['result']['content'][0]['text']); body['next_offset'] += 1
        value['pages'][0]['result']['content'][0]['text'] = json.dumps(body)
        check_capture(value, 'reject next_offset inconsistent with decoded byte length')
        value = copy.deepcopy(originals[0]); body = json.loads(value['terminal']['result']['content'][0]['text']); body['status'] = 'failed'
        value['terminal']['result']['content'][0]['text'] = json.dumps(body)
        check_capture(value, 'reject failed status even with exit_code zero')
        value = copy.deepcopy(originals[0]); value['submission']['arguments']['command'] = value['submission']['arguments']['command'].replace('test ! -s', 'test -e')
        check_capture(value, 'reject a submitted command without the exact empty-stderr guard')
        value = copy.deepcopy(originals[0]); body = json.loads(value['pages'][0]['result']['content'][0]['text']); body['eof'] = True
        value['pages'][0]['result']['content'][0]['text'] = json.dumps(body)
        check_capture(value, 'reject premature EOF')
        value = copy.deepcopy(originals[0]); body = json.loads(value['pages'][0]['result']['content'][0]['text']); body['output_base64'] += '\n'
        value['pages'][0]['result']['content'][0]['text'] = json.dumps(body)
        check_capture(value, 'reject non-strict base64')
        calls_path.write_text(json.dumps(originals[0]))
        saved = raw_path.read_bytes(); raw_path.write_bytes(bytes([saved[0] ^ 1]) + saved[1:])
        rejected(lambda: M['accept'](plan, plan_sha, 'archive', 0, raw_path, calls_path, allow_synthetic=True))
        raw_path.write_bytes(saved)
        PASSED.append('reject wrong raw capture SHA256 with unchanged length')
        rejected(lambda: M['accept'](plan, plan_sha, 'archive', 0, raw_path, calls_path))
        PASSED.append('production acceptance refuses explicitly synthetic tool records')
        out = outputs / 'archive.bin'
        M['assemble'](plan, plan_sha, 'archive', captures, out, allow_synthetic=True)
        require(out.read_bytes() == archive_data, 'Whole archive differs')
        bad = copy.deepcopy(originals[1]); body = json.loads(bad['terminal']['result']['content'][0]['text']); body['exit_code'] = 1
        bad['terminal']['result']['content'][0]['text'] = json.dumps(body)
        second = captures / 'archive.00001.capture.json'; second.write_text(json.dumps(bad))
        rejected(lambda: M['assemble'](plan, plan_sha, 'archive', captures, out, allow_synthetic=True))
        PASSED.append('existing exact output does not bypass this round\'s failed part evidence')
        retry = outputs / 'retry.bin'
        rejected(lambda: M['assemble'](plan, plan_sha, 'archive', captures, retry, allow_synthetic=True))
        require(not retry.exists() and not list(outputs.glob('*.partial')), 'Failed owned partial was retained')
        second.write_text(json.dumps(originals[1]))
        M['assemble'](plan, plan_sha, 'archive', captures, retry, allow_synthetic=True)
        require(retry.read_bytes() == archive_data, 'Retry failed')
        PASSED.append('failure cleans only its owned partial; unchanged inputs can retry successfully')
        M['assemble'](plan, plan_sha, 'joint_log', captures, outputs / 'joint.log', allow_synthetic=True)
        require((outputs / 'joint.log').stat().st_size == 0, 'Empty joint log differs')
        PASSED.append('zero-byte joint log preserved without a producer job')
        retained = root / 'persistent'
        retained.mkdir()
        copied = []
        for info in (final_info, final['archive'], final['export_manifest'], final['verification']):
            source = Path(info['path'])
            target = retained / source.name
            source.rename(target)
            copied.append({**info, 'source': str(source), 'path': str(target)})
        joint_copies = retained / 'joint-artifacts'
        joint_copies.mkdir()
        for info in final['joint_receipt_probe_log']:
            source = Path(info['path'])
            target = joint_copies / source.name
            target.write_bytes(source.read_bytes())
            copied.append({**info, 'source': str(source), 'path': str(target)})
        final_path = retained / 'FINALIZATION.json'
        retention_path = retained / 'PERSISTENT_COPY.json'
        retention = {'finalizer_exit_code': 0, 'original_output': str(original_output),
                     'persistent_output': str(retained), 'copied_files': copied,
                     'omitted_generated_packages': []}
        def save_retention(value):
            retention_path.write_text(json.dumps(value) + '\n')
            return hashlib.sha256(retention_path.read_bytes()).hexdigest()
        def retained_plan(digest):
            return M['make_plan'](final_path, final_info['sha256'], final_info['bytes'], plan_path,
                                  synthetic_test_only=True, retention_path=retention_path, retention_sha=digest)
        retention_sha = save_retention(retention)
        kept = retained_plan(retention_sha)
        require(len(kept['assets']) == 8 and len(kept['retention_binding']['replacements']) == 6,
                'Retention changed the asset inventory')
        require(kept['assets']['retention']['path'] == str(retention_path)
                and kept['assets']['retention']['sha256'] == retention_sha
                and kept['assets']['retention']['bytes'] == retention_path.stat().st_size,
                'Original retention bytes are not a frozen asset')
        require(kept['retention_binding']['path'] == str(retention_path)
                and kept['retention_binding']['sha256'] == retention_sha
                and kept['retention_binding']['bytes'] == retention_path.stat().st_size,
                'Retention receipt is not pinned')
        for asset in ('archive', 'export_manifest', 'verification'):
            original = final[asset]
            replacement = kept['retention_binding']['replacements'][asset]
            require(not Path(original['path']).exists()
                    and replacement == {**original, 'source': original['path'],
                                        'path': str(retained / Path(original['path']).name)}
                    and kept['assets'][asset]['path'] == replacement['path'], 'Retained source binding differs')
        for asset, original in zip(('joint_receipt', 'joint_probe', 'joint_log'), final['joint_receipt_probe_log']):
            require(Path(original['path']).is_file()
                    and not Path(original['path']).is_relative_to(original_output)
                    and kept['retention_binding']['replacements'][asset] ==
                    {**original, 'source': original['path'], 'path': str(joint_copies / Path(original['path']).name)}
                    and kept['assets'][asset]['path'] == str(joint_copies / Path(original['path']).name),
                    'External joint source binding differs')
        require(hashlib.sha256(final_path.read_bytes()).hexdigest() == final_info['sha256'],
                'Original FINALIZATION bytes were changed')
        PASSED.append('real moved tmpfs files and copied external joint files use pinned bindings; original FINALIZATION and joint bytes remain intact')
        rejected(lambda: retained_plan('0' * 64))
        PASSED.append('reject a wrong retention receipt SHA256')
        bad = copy.deepcopy(retention)
        bad['copied_files'].append({**copied[1], 'path': str(retained / 'other-archive.bin')})
        rejected(lambda: retained_plan(save_retention(bad)))
        PASSED.append('reject duplicate retention sources even with different destinations')
        bad = copy.deepcopy(retention)
        bad['copied_files'][1]['path'] = copied[0]['path']
        rejected(lambda: retained_plan(save_retention(bad)))
        PASSED.append('reject duplicate retention destinations')
        for source in (root / 'unlisted.bin', original_output / '..' / 'unlisted.bin'):
            bad = copy.deepcopy(retention)
            bad['copied_files'].append({**copied[1], 'source': str(source),
                                        'path': str(retained / 'unlisted-copy.bin')})
            rejected(lambda: retained_plan(save_retention(bad)))
        PASSED.append('reject unknown external or traversal sources outside the declared original output')
        for exit_code in (1, False):
            bad = copy.deepcopy(retention)
            bad['finalizer_exit_code'] = exit_code
            rejected(lambda: retained_plan(save_retention(bad)))
        PASSED.append('reject failed or noninteger finalizer exit codes')
        for row_index in (0, 1, 4):
            for key, value in (('bytes', copied[row_index]['bytes'] + 1), ('sha256', '0' * 64)):
                bad = copy.deepcopy(retention)
                bad['copied_files'][row_index][key] = value
                rejected(lambda: retained_plan(save_retention(bad)))
        PASSED.append('reject retention sizes or digests that disagree with original FINALIZATION')
        retention_sha = save_retention(retention)
        retained_archive = Path(copied[1]['path'])
        retained_archive.write_bytes(bytes([archive_data[0] ^ 1]) + archive_data[1:])
        rejected(lambda: retained_plan(retention_sha))
        retained_archive.write_bytes(archive_data)
        PASSED.append('retained files still pass the original full-byte SHA256 freeze')
        physical_archive = retained / 'physical-archive.bin'
        retained_archive.rename(physical_archive)
        retained_archive.symlink_to(physical_archive)
        rejected(lambda: retained_plan(retention_sha))
        retained_archive.unlink()
        physical_archive.rename(retained_archive)
        PASSED.append('retained files still reject a noncanonical symlink source')
        retained_plan_path = root / 'RETAINED_PLAN.json'
        child = subprocess.run(['python3', str(SCRIPT), 'plan', str(final_path), final_info['sha256'],
                                str(final_info['bytes']), str(retained_plan_path), str(retention_path),
                                retention_sha], capture_output=True)
        require(child.returncode == 0 and child.stderr == b'', 'Retention plan CLI failed')
        retained_plan_path.write_bytes(child.stdout)
        actual_plan_sha = hashlib.sha256(child.stdout).hexdigest()
        actual_plan = M['load_plan'](retained_plan_path, actual_plan_sha)
        require(actual_plan['retention_binding'] == kept['retention_binding'], 'CLI retention binding differs')
        request = M['job_request'](actual_plan, actual_plan_sha, 'retention', 0, 'local-retention')
        child = subprocess.run(['bash', '-c', request['command']], cwd=request['cwd'], capture_output=True)
        require(child.returncode == 0 and child.stderr == b'' and child.stdout == retention_path.read_bytes(),
                'Canonical producer did not emit original retention bytes')
        PASSED.append('CLI pins the eighth retention asset and canonical producer emits its exact original bytes')
    report = {'kind': 'SYNTHETIC_LOCAL_ONLY_NOT_P2_EVIDENCE', 'helper_path': str(SCRIPT),
              'helper_sha256': hashlib.sha256(SCRIPT.read_bytes()).hexdigest(),
              'test_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'checks_passed': len(PASSED), 'checks': PASSED, 'cloud_calls': 0, 'lean_calls': 0,
              'github_calls': 0, 'library_calls': 0}
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
