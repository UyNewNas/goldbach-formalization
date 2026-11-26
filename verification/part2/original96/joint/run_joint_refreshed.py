#!/usr/bin/env python3
"""Run the frozen joint probe using the accepted division-refresh objects."""

import argparse
import base64
import hashlib
import io
import json
import lzma
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time


ROOT = Path('/workspace/p2-1-original96-20261126')
HERE = Path(__file__).resolve().parent
REFRESH_ATTEMPT = Path('evidence/original96-division-refresh/attempt-abjdgbxc')
ARCHIVE = ROOT / REFRESH_ATTEMPT / 'division-refresh.tar.xz'
ARCHIVE_SIZE = 772132
ARCHIVE_SHA = '3a144376344bbf133ea24f7c5f4236ccc0dd9264d675be87fed13c2df30708e9'
SUMMARY_SHA = 'ded7ae98463bc93fd121465d2602fb9fc1edcbf2d26d757d169c64349dead0a3'
REFERENCE_SHA = '09f62777eb9996fb7c7d41e27238afec282b904a8072cc9555d055c6ec43cfc5'
FROZEN_HELPERS = {
    'run_joint_increment.py': 'd4be3348f0d1d12dc4721409fd7b89b9563203b8a99bbb0aaeaf7ecfc610f664',
    'freeze_joint_reference.py': '5af69fa31010ebf08f0189eae29b278ce588e074673c9cc1fed7c1d6cf33a901',
}
DIVISION = 'ImbalancedChen.Certificates.P2OriginalP160DirectDivision'


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def refreshed_group(archive, original, roots, checks):
    raw = archive.read_bytes()
    require(len(raw) == ARCHIVE_SIZE and digest(raw) == ARCHIVE_SHA, 'refresh archive identity differs')
    summary_path = REFRESH_ATTEMPT / 'summary.json'
    records_path = Path('.lake/p2-private/records.json')
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:xz') as tar:
        def member(path):
            info = tar.getmember(str(path))
            require(info.isfile(), 'expected regular archive member: ' + str(path))
            return tar.extractfile(info).read()

        summary_raw = member(summary_path)
        require(digest(summary_raw) == SUMMARY_SHA, 'refresh summary identity differs')
        summary = json.loads(summary_raw)
        require(summary['status'] == 'ACCEPTED_ORIGINAL96_DIVISION_REFRESH' and
                summary['freshly_compiled_this_attempt'] == summary['fresh_audit_and_replay'] == [DIVISION] and
                summary['source_comparison_reused'] and not summary['source_comparison_executed_this_attempt'] and
                summary['source_comparison'] == original['source_comparison'] and
                summary['owned_declarations'] == summary['unique_owned_declarations'] == 118 and
                summary['union_owned_declarations'] == 18699 and not summary['union_duplicate_owned_declarations'],
                'unexpected refresh acceptance summary')
        records_raw = member(records_path)
        require(digest(records_raw) == summary['records_sha256'], 'refresh compiler records differ')
        records = json.loads(records_raw)
        owners = summary['owner_bindings']
        require(set(owners) == set(summary['modules']) == set(original['modules']) and
                sum(row['count'] for row in owners.values()) == 118, 'refresh owner selection differs')
        for name, owner in owners.items():
            for field in ('source', 'object', 'receipt', 'declarations'):
                path, expected = owner[field]
                path = ROOT / path
                require(digest(member(path.relative_to(ROOT))) == expected, 'archive binding differs: ' + str(path))
                owner[field] = [str(path), expected]
            receipt = json.loads(member(Path(owner['receipt'][0]).relative_to(ROOT)))
            require(receipt['module'] == name and receipt['accepted'] and
                    receipt['compile_closure_signature'] == records[name]['closure_signature'] and
                    receipt['source_sha256'] == records[name]['source_sha256'] == owner['source'][1] and
                    receipt['object_sha256'] == records[name]['object_sha256'] == owner['object'][1] and
                    receipt['artifacts'][str(Path(owner['declarations'][0]).relative_to(ROOT))] ==
                    owner['declarations'][1], 'refresh receipt binding differs: ' + name)
        frozen = {str(ROOT / path): expected for path, expected in summary['reviewed_inputs'].items()}
        frozen.update({str(ARCHIVE): ARCHIVE_SHA, str(ROOT / summary_path): SUMMARY_SHA,
                       str(ROOT / records_path): summary['records_sha256']})
    return {'owners': owners, 'frozen_files': frozen, 'proof_inputs': summary['proof_inputs'],
            'roots': roots, 'checks': checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit-base64', action='store_true')
    args = parser.parse_args()
    require(Path.cwd().resolve() == ROOT, f'execute within {ROOT}')
    for name, expected in FROZEN_HELPERS.items():
        require(digest((HERE / name).read_bytes()) == expected, 'frozen joint helper differs: ' + name)
    from freeze_joint_reference import NEW_CHECKS, NEW_ROOTS, shared_providers
    from run_joint_increment import BLOCK_CHECKS, LEAN, loaded_paths, owned, prepare_overlay, sha, verify_bindings

    reference_path = HERE / 'joint-reference.json.xz'
    raw = reference_path.read_bytes()
    require(digest(raw) == REFERENCE_SHA, 'old joint reference differs')
    reference = json.loads(lzma.decompress(raw))
    old = reference['old']
    new = refreshed_group(ARCHIVE, reference['new_archive']['summary'], NEW_ROOTS, NEW_CHECKS)
    providers = shared_providers(old, new)
    probe = HERE / 'Joint.lean'
    checks = old['checks'] + new['checks']
    roots = old['roots'] + new['roots']
    require(len(old['owners']) == 140 and len(new['owners']) == 3 and len(roots) == 7 and
            len(checks) == 30 and reference['source_form_contracts'] == 10, 'wrong probe scope')

    attempts = ROOT / 'evidence/original96-joint-compatibility'
    attempts.mkdir(parents=True, exist_ok=True)
    attempt = Path(tempfile.mkdtemp(prefix='attempt-refreshed-', dir=attempts))
    log = attempt / 'joint.log'
    binding_args = (old, new, probe, reference['probe_sha256'], reference_path, REFERENCE_SHA)
    try:
        before = verify_bindings(*binding_args)
        old_names, new_names = owned(old), owned(new)
        require(len(old_names) == 18581 and len(new_names) == 118 and not old_names & new_names,
                'owned declaration union differs: ' + str(sorted(old_names & new_names)[:12]))
        overlay = attempt / 'lib'
        expected = prepare_overlay(overlay, old, new)
        env = dict(os.environ, LEAN_PATH=str(overlay) + ':' + old['lean_path'], LEAN_SYSROOT=old['lean_sysroot'])
        command = [str(LEAN), '-t0', '-j1', '-M11264', '-DwarningAsError=true', str(probe)]
        start = time.monotonic()
        with log.open('wb') as stream:
            result = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT)
        elapsed = round(time.monotonic() - start, 3)
        require(result.returncode == 0, f'joint probe failed ({result.returncode}): {log}\n' +
                log.read_text(errors='replace')[-6000:])
        observed = loaded_paths(log)
        changed = sorted(name for name in observed.keys() | expected.keys() if observed.get(name) != expected.get(name))
        require(not changed, 'actual loaded paths differ: ' + str(changed[:12]))
        require(BLOCK_CHECKS | set(roots) <= observed.keys() and len(observed) == 6727, 'root import inventory differs')
        require(verify_bindings(*binding_args) == before, 'bound inputs changed during joint probe')
        for name in old['owners'].keys() | new['owners'].keys():
            require(Path(observed[name][0]).resolve(strict=True) == Path(observed[name][1]),
                    'project overlay changed after compilation: ' + name)
        final = {'status': 'JOINT_INCREMENT_COMPATIBLE', 'attempt': str(attempt), 'command': command,
                 'exit_code': result.returncode, 'seconds': elapsed, 'log_sha256': sha(log),
                 'reference_sha256': REFERENCE_SHA, 'refresh_archive_sha256': ARCHIVE_SHA,
                 'refresh_summary_sha256': SUMMARY_SHA, 'probe_sha256': reference['probe_sha256'],
                 'bound_files_sha256': before, 'inputs_unchanged': True,
                 'lean_path': env['LEAN_PATH'], 'lean_sysroot': env['LEAN_SYSROOT'],
                 'project_modules': 143, 'project_overlay_objects': 143, 'retained_old_nonproject_paths': 6584,
                 'old_owned': 18581, 'new_owned': 118, 'distinct_owned': len(old_names | new_names),
                 'duplicate_owned': 0, 'loaded_modules': len(observed), 'native_modules': len(old['native_modules']),
                 'native_facets': sum(map(len, old['native_modules'].values())), 'shared_providers': sorted(providers),
                 'all40_checks': 40, 'roots': roots, 'public_type_checks': 30, 'source_form_contracts': 10,
                 'compile_credit': False, 'kernel_credit': False, 'audit_credit': False,
                 'full_p2_1_complete': False, 'full_p2_complete': False}
        summary_path = attempt / 'summary.json'
        summary_path.write_text(json.dumps(final, indent=2) + '\n')
        evidence = attempt / 'joint-evidence.tar.xz'
        with tarfile.open(evidence, 'w:xz') as tar:
            for path in (probe, log, summary_path):
                tar.add(path, arcname=path.name)
        size = evidence.stat().st_size
        require(4 * ((size + 2) // 3) <= 600000, 'joint evidence exceeds base64 return bound')
        print('P21_JOINT_INCREMENT ' + json.dumps(final), flush=True)
        print('P21_JOINT_ARCHIVE ' + json.dumps({'path': str(evidence), 'bytes': size, 'sha256': sha(evidence)}), flush=True)
        if args.emit_base64:
            print('P21_JOINT_ARCHIVE_BASE64 ' + base64.b64encode(evidence.read_bytes()).decode(), flush=True)
    except Exception as error:
        (attempt / 'failure.json').write_text(json.dumps({'error': str(error)}) + '\n')
        raise


if __name__ == '__main__':
    main()
