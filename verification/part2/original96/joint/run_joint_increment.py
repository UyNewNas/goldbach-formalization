#!/usr/bin/env python3
"""Strict compatibility probe over already accepted P2.1 sources and objects."""

import argparse
import base64
import hashlib
import json
import lzma
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time

from freeze_joint_reference import NEW_ARCHIVE, new_reference, shared_providers


ROOT = Path('/workspace/p2-1-original96-20261126')
HERE = Path(__file__).resolve().parent
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
LEAN_SHA256 = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB = Path('/workspace/compile-deps/mathlib')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
BLOCK_CHECKS = {f'ImbalancedChen.Certificates.OriginalNodeArraysV1.Block{i:02}FullCheck' for i in range(40)}
ARTIFACT_FIELDS = ('source', 'object', 'receipt', 'declarations')
PROJECT_COMPANIONS = ('.olean.server', '.olean.private', '.ir', '.ir.sig')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def signature(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def read_checked_json(path, expected):
    raw = Path(path).read_bytes()
    require(hashlib.sha256(raw).hexdigest() == expected, 'binding differs: ' + str(path))
    return json.loads(raw)


def verify_bindings(old, new, probe, probe_sha, reference_path, reference_sha):
    files = {str(LEAN): LEAN_SHA256, str(probe): probe_sha, str(reference_path): reference_sha}

    def pin(path, expected):
        require(files.setdefault(path, expected) == expected, 'conflicting frozen digests: ' + path)

    for group in (old, new):
        for path, expected in group['frozen_files'].items():
            pin(path, expected)
        for row in group['owners'].values():
            for field in ARTIFACT_FIELDS:
                pin(*row[field])
    for name, facets in old['native_modules'].items():
        search = old['loaded_modules'][name][0].removesuffix('.olean')
        for suffix, (physical, expected) in facets.items():
            require(Path(search + suffix).resolve(strict=True) == Path(physical),
                    'native physical resolution differs: ' + name + suffix)
            pin(physical, expected)
    for path, expected in files.items():
        require(sha(path) == expected, 'binding differs: ' + path)
    records = json.loads(Path(old['records']).read_bytes())
    require(signature({name: records[name] for name in old['owners']}) == old['selected_records_sha256'],
            'old selected compiler records differ')
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB, text=True).strip() == MATHLIB_PIN,
            'Mathlib pin differs')
    return signature(files)


def owned(group):
    names = set()
    for name, owner in group['owners'].items():
        inventory = read_checked_json(*owner['declarations'])['declarations']
        current = {row['name'] for row in inventory}
        require(len(current) == len(inventory) == owner['count'] and
                all(row.get('module') == name for row in inventory), 'owner inventory differs: ' + name)
        require(not names.intersection(current), 'overlapping owned declarations at ' + name)
        names.update(current)
    require(set(group['checks']) <= names, 'a public target is absent from accepted owned inventories')
    return names


def loaded_paths(log):
    loaded = {}
    with log.open() as stream:
        for line in stream:
            if not line.startswith('P21_IMPORT '):
                continue
            row = json.loads(line.removeprefix('P21_IMPORT '))
            name, path = row['module'], row['olean']
            require(name not in loaded, 'duplicate runtime module: ' + name)
            loaded[name] = [path, str(Path(path).resolve(strict=True))]
    return loaded


def prepare_overlay(overlay, old, new):
    # Lean chooses one package root for ImbalancedChen before looking up a
    # module. All accepted project objects must be visible in that root.
    expected = dict(old['loaded_modules'])
    for name, owner in {**old['owners'], **new['owners']}.items():
        original = Path(owner['object'][0])
        physical = original.resolve(strict=True)
        if name in old['owners']:
            require(str(physical) == expected[name][1], 'old project physical path differs: ' + name)
        stem = str(original).removesuffix('.olean')
        require(not any(Path(stem + suffix).is_file() for suffix in PROJECT_COMPANIONS),
                'unexpected project loader facet: ' + name)
        logical = overlay / (name.replace('.', '/') + '.olean')
        logical.parent.mkdir(parents=True, exist_ok=True)
        logical.symlink_to(physical)
        expected[name] = [str(logical), str(physical)]
    return expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, default=HERE / 'joint-reference.json.xz')
    parser.add_argument('--reference-sha256', required=True)
    parser.add_argument('--emit-base64', action='store_true', help='emit at most 600,000 base64 bytes')
    args = parser.parse_args()
    require(Path.cwd().resolve() == ROOT, f'execute within {ROOT}')
    probe = HERE / 'Joint.lean'
    raw = args.reference.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == args.reference_sha256, 'reference digest differs')
    reference = json.loads(lzma.decompress(raw))
    require(reference['schema'] == 'p21-original96-joint-reference-v1' and
            reference['source_form_contracts'] == 10,
            'unexpected reference schema')
    old, archived = reference['old'], reference['new_archive']
    require(Path(archived['path']) == NEW_ARCHIVE, 'unexpected new acceptance archive path')
    new = new_reference(NEW_ARCHIVE, archived['sha256'], archived['bytes'], archived['summary'])
    providers = shared_providers(old, new)
    require(len(old['owners']) == 140 and len(new['owners']) == 3 and
            not set(old['owners']).intersection(new['owners']) and
            len(old['roots']) == 5 and len(new['roots']) == 2 and
            len(old['checks']) == 26 and len(new['checks']) == 4 and
            BLOCK_CHECKS <= old['owners'].keys(), 'wrong joint scope')

    attempts = ROOT / 'evidence/original96-joint-compatibility'
    attempts.mkdir(parents=True, exist_ok=True)
    attempt = Path(tempfile.mkdtemp(prefix='attempt-', dir=attempts))
    log = attempt / 'joint.log'
    bound = [old, new, probe, reference['probe_sha256'], args.reference, args.reference_sha256]
    try:
        before = verify_bindings(*bound)
        old_names, new_names = owned(old), owned(new)
        duplicates = old_names & new_names
        require(len(old_names) == 18581 and len(new_names) == 122 and not duplicates,
                'accepted declaration union differs: ' + str(sorted(duplicates)[:10]))

        overlay = attempt / 'lib'
        expected = prepare_overlay(overlay, old, new)
        env = dict(os.environ, LEAN_PATH=str(overlay) + ':' + old['lean_path'], LEAN_SYSROOT=old['lean_sysroot'])
        command = [str(LEAN), '-t0', '-j1', '-M11264', '-DwarningAsError=true', str(probe)]
        started = time.monotonic()
        with log.open('wb') as output:
            result = subprocess.run(command, env=env, stdout=output, stderr=subprocess.STDOUT)
        elapsed = round(time.monotonic() - started, 3)
        require(result.returncode == 0, f'joint probe failed ({result.returncode}): {log}')
        observed = loaded_paths(log)
        different = sorted(name for name in observed.keys() | expected.keys()
                           if observed.get(name) != expected.get(name))
        require(not different, 'actual loaded paths differ: ' + str(different[:10]))
        require(BLOCK_CHECKS | set(old['roots'] + new['roots']) <= observed.keys() and
                len(observed) == 6727, 'root or BlockNNFullCheck import inventory differs')
        require(verify_bindings(*bound) == before, 'bound inputs changed during joint probe')
        for name in old['owners'].keys() | new['owners'].keys():
            require(Path(observed[name][0]).resolve(strict=True) == Path(observed[name][1]),
                    'project overlay changed after compilation: ' + name)

        final = {'status': 'JOINT_INCREMENT_COMPATIBLE', 'attempt': str(attempt),
                 'reference_sha256': args.reference_sha256, 'bound_files_sha256': before,
                 'probe_sha256': reference['probe_sha256'], 'command': command,
                 'exit_code': result.returncode, 'seconds': elapsed,
                 'log_sha256': sha(log), 'lean_path': env['LEAN_PATH'], 'lean_sysroot': env['LEAN_SYSROOT'],
                 'inputs_unchanged': True, 'project_modules': 143, 'old_owned': 18581, 'new_owned': 122,
                 'project_overlay_objects': 143, 'retained_old_nonproject_paths': 6584,
                 'distinct_owned': len(old_names | new_names), 'duplicate_owned': 0,
                 'loaded_modules': len(observed), 'native_modules': len(old['native_modules']),
                 'native_facets': sum(map(len, old['native_modules'].values())),
                 'shared_providers': sorted(providers), 'new_archive_sha256': archived['sha256'],
                 'all40_checks': 40, 'roots': old['roots'] + new['roots'],
                 'public_type_checks': 30, 'source_form_contracts': 10,
                 'compile_credit': False, 'kernel_credit': False, 'audit_credit': False,
                 'full_p2_1_complete': False, 'full_p2_complete': False}
        summary = attempt / 'summary.json'
        summary.write_text(json.dumps(final, indent=2) + '\n')
        archive = attempt / 'joint-evidence.tar.xz'
        with tarfile.open(archive, 'w:xz') as tar:
            for path in (probe, log, summary):
                tar.add(path, arcname=path.name)
        size = archive.stat().st_size
        require(4 * ((size + 2) // 3) <= 600000, 'joint evidence exceeds base64 return bound')
        print('P21_JOINT_INCREMENT ' + json.dumps(final), flush=True)
        print('P21_JOINT_ARCHIVE ' + json.dumps({'path': str(archive), 'bytes': size, 'sha256': sha(archive)}), flush=True)
        if args.emit_base64:
            print('P21_JOINT_ARCHIVE_BASE64 ' + base64.b64encode(archive.read_bytes()).decode(), flush=True)
    except Exception as error:
        (attempt / 'failure.json').write_text(json.dumps({'error': str(error)}) + '\n')
        raise


if __name__ == '__main__':
    main()
