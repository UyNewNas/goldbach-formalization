#!/usr/bin/env python3
"""Materialize existing, unchanged Git sources before the unchanged P1.4 runner.

This is source deployment only: no Lean, Lake, kernel or acceptance command is
called. Existing exact files are reused; known repair preimages are deferred to
run_stage.py. Only an unchanged-source manifest row may create an absent file.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError('P1.4 source deployment requires Python assertions')

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
SCRIPT_PATH = 'docs/p1/20261125/p14-continuation/materialize_sources.py'
DRIVER_PATH = 'docs/p1/20261125/p14-continuation/run_stage.py'
DRIVER_SHA = 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1'


def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--manifest', required=True, action='append')
    parser.add_argument('--run', required=True, action='store_true')
    parser.add_argument('--worker', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    source = args.source_commit
    assert re.fullmatch(r'[0-9a-f]{40}', source)
    assert args.manifest and len(args.manifest) == len(set(args.manifest))
    assert all(re.fullmatch(r'docs/p1/20261125/p14-continuation/stages/[a-z0-9-]+\.json', p)
               for p in args.manifest)
    executed_bytes = Path(__file__).read_bytes()
    assert executed_bytes == git(source, SCRIPT_PATH), 'executing script differs from published Git source'
    driver_bytes = git(source, DRIVER_PATH)
    assert hashlib.sha256(driver_bytes).hexdigest() == DRIVER_SHA
    base = types.ModuleType('unchanged_p14_driver')
    exec(compile(driver_bytes, DRIVER_PATH, 'exec'), base.__dict__)
    api_bytes = git(base.API_COMMIT, base.API_PATH)
    assert base.sha(api_bytes) == base.API_SHA
    api = base.load(api_bytes, 'p14_existing_api')
    raw = {p: git(api.TOOLS, p) for p in api.PINS}
    assert all(base.sha(raw[p]) == digest for p, digest in api.PINS.items())
    h = base.load(raw[api.HELPER], 'p14_existing_helper')
    d = base.load(raw[api.PRIMITIVES], 'p14_existing_primitives')
    assert base.sha(base.REVIEW.read_bytes()) == base.REVIEW_SHA
    review = json.loads(base.REVIEW.read_bytes())
    runtime = d.runtime_binding(h)
    assert runtime == review['existing_runtime_bindings']
    assert {p: d.fingerprint(base.PROJECT / p) for p in
            ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')} == review['runtime_configuration_bindings']
    assert not (base.PROJECT / 'lakefile.lean').exists()
    protected = h.check_roots()
    manifests, declared, updates, payloads, deferred = {}, {}, [], {}, []
    for path in args.manifest:
        data = git(source, path)
        manifest = json.loads(data)
        assert manifest['schema'] == 'p14_existing_frontier_stage_v1'
        assert re.fullmatch(r'[a-z0-9-]+', manifest['stage']) and manifest['modules']
        manifests[path] = base.sha(data)
        for row in manifest['modules']:
            module, rel = row['module'], row['path']
            assert re.fullmatch(r'ImbalancedChen(?:\.[A-Za-z_][A-Za-z0-9_]*)+', module)
            assert rel == h.module_path(module) and module not in declared
            assert re.fullmatch(r'[0-9a-f]{40}', row['preimage_commit'])
            payload = git(source, rel)
            assert base.sha(payload) == row['after_sha256']
            assert base.sha(git(row['preimage_commit'], rel)) == row['before_sha256']
            target = base.PROJECT / rel
            assert all(not p.is_symlink() for p in [target, *target.parents]), 'source path contains a symlink'
            assert not target.exists() or target.is_file(), 'source path is not a regular file'
            actual = base.sha(target.read_bytes()) if target.is_file() else None
            declared[module] = {k: row[k] for k in ('path', 'before_sha256', 'after_sha256')}
            if actual is None:
                assert row['before_sha256'] == row['after_sha256'], 'absent repair source needs its own installation plan'
            elif actual != row['after_sha256']:
                assert actual == row['before_sha256'], 'unknown source preimage: ' + module
                deferred.append(module)
                continue
            payloads[rel] = payload
            updates.append({'module': module, 'path': rel, 'before_sha256': None,
                            'after_sha256': row['after_sha256'], 'cloud_source_mutation_required': True})
    preflight = d.preflight_sources(base.PROJECT, updates, payloads)
    binding = {'source_commit': source, 'script_sha256': base.sha(executed_bytes),
               'unchanged_driver_sha256': DRIVER_SHA, 'manifests': manifests, 'declared_sources': declared,
               'runtime': runtime, 'protected_roots': protected, 'acceptance_claimed': False}
    key = base.sha(json.dumps(manifests, sort_keys=True).encode())[:16]
    root = base.ROOT / 'source-materialization' / source / key
    if args.worker is None:
        before = d.original_git_state(REPO)
        d.save(root / 'BINDING.json', binding)
        executed = root / 'executed-materializer.py'
        d.write_frozen(executed, executed_bytes)
        run = d.attempt(root / 'runs')
        d.save(run / 'GIT_BEFORE.json', before)
        child = ['python3', '-B', str(executed), '--source-commit', source, '--run', '--worker', str(run)]
        for path in args.manifest:
            child.extend(['--manifest', path])
        try:
            return subprocess.run(h.serialize(0, run / 'VALIDATION_LANE.json', child)).returncode
        finally:
            after = d.original_git_state(REPO)
            d.save(run / 'GIT_AFTER.json', after)
            assert after == before, 'original source checkout changed'
    run = args.worker.resolve()
    assert run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir()
    d.verify_lane(h)
    assert json.loads((root / 'BINDING.json').read_bytes()) == binding
    d.save(run / 'SOURCE_PREFLIGHT.json', {'sources': preflight, 'deferred_repairs': deferred})
    installed = d.install_sources(base.PROJECT, updates, payloads, run / 'source-backups', h)
    d.save(run / 'SOURCE_INSTALL.json', installed)
    result = {'status': 'SOURCE_DEPLOYMENT_ONLY_NOT_ACCEPTANCE', 'source_commit': source,
              'installed_or_reused': [row['module'] for row in installed], 'deferred_repairs': deferred,
              'protected_roots': h.check_roots(), 'acceptance_claimed': False}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
