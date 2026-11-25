#!/usr/bin/env python3
"""Apply only the two manifest-bound first-compile source repairs with backups.

The complete 316-source graph and fixed runtime are checked before either source
can change. Existing postimages are no-ops; unknown preimages hold. The unchanged
Batch5 installer owns backup and replacement operations. No cache or proof build
is requested, and the original additive installer and acceptance driver stay fixed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261125-p15-singleton-proper-power-v1')
PREFIX = 'docs/p1/20261125/p15-singleton-proper-power/'
SCRIPT = PREFIX + 'apply_source_repairs.py'
REPAIRS = PREFIX + 'FIRST_COMPILE_REPAIRS.json'
REPAIRS_SHA = '617250ec7dfb19bfd892bea012bc08639993897c447253363b718b9af08116ff'
FAILED_SOURCE_COMMIT = '1a259e113c0977c8cb2814492ff3bd6ab7cdc475'
DRIVER_SHA = 'f260f575ed6f8a7998fd901d42f0f1cd87115c879c0dc3b2c10f04a7f9b35313'
ADDITIVE_INSTALLER_SHA = '901c3c585574f8427045e18bf7d78dcfa6d32b05e0c551cbc42b382584d9e08d'
TARGETS = ('ImbalancedChen.P1OriginalSingletonPointwiseData',
           'ImbalancedChen.P1Full87TrueDPolicyDelta')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def load_driver(commit):
    code = git_file(commit, PREFIX + 'run_selected.py')
    require(sha(code) == DRIVER_SHA, 'original acceptance driver differs')
    require(sha(git_file(commit, PREFIX + 'install_sources.py')) == ADDITIVE_INSTALLER_SHA,
            'original additive installer differs')
    driver = ModuleType('published_p15_singleton_driver')
    driver.__file__ = PREFIX + 'run_selected.py'
    exec(compile(code, driver.__file__, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT),
            'unexpected installation environment')
    return driver, driver.helpers(), code


def context(driver, s, review):
    observed = {p: s.d.fingerprint(PROJECT / p)
                for p in review['runtime_configuration_bindings']}
    require(observed == review['runtime_configuration_bindings'] and
            not os.path.lexists(PROJECT / 'lakefile.lean'), 'existing configuration differs')
    runtime = s.d.runtime_binding(s.h)
    require(runtime == review['existing_runtime_bindings'], 'existing runtime differs')
    protected = {m: driver.file_binding(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    require(protected == s.h.FOUR_ROOTS, 'protected root differs')
    return {'configuration': observed, 'runtime': runtime, 'protected_roots': protected}


def check_binding(raw, binding, description):
    actual = {'bytes': len(raw), 'sha256': sha(raw)}
    if 'git_blob' in binding:
        actual['git_blob'] = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    require(all(binding.get(k) == v for k, v in actual.items()), description + ' binding differs')


def reconstruct(preimage, splices):
    require(isinstance(splices, list) and splices, 'empty repair splice list')
    pieces, cursor = [], 0
    for row in splices:
        lo, hi = row['pre_start_byte'], row['pre_end_byte']
        require(type(lo) is int and type(hi) is int and cursor <= lo < hi <= len(preimage),
                'repair intervals are not ordered nonoverlapping preimage intervals')
        old, new = row['old_utf8'].encode('utf-8'), row['new_utf8'].encode('utf-8')
        require(preimage[lo:hi] == old and old != new, 'exact repair preimage interval differs')
        pieces.extend((preimage[cursor:lo], new))
        cursor = hi
    pieces.append(preimage[cursor:])
    return b''.join(pieces)


def repair_inputs(driver, s, commit, graph, sources):
    raw = driver.pinned(commit, REPAIRS, REPAIRS_SHA)
    manifest = json.loads(raw)
    require(manifest.get('schema') == 'p15_first_compile_source_repairs_v1' and
            manifest.get('failed_source_commit') == FAILED_SOURCE_COMMIT and
            manifest.get('expected_project_source_count') == 316 and
            manifest.get('expected_other_identical_source_count') == 314,
            'first-compile repair manifest scope differs')
    files = manifest['files']
    require([row['module'] for row in files] == list(TARGETS), 'repair owners differ')
    for binding in [manifest['unchanged_driver'], manifest['unchanged_additive_installer'],
                    *manifest['unchanged_historical_bindings']]:
        check_binding(git_file(commit, binding['path']), binding, 'retained published input')
        check_binding(git_file(FAILED_SOURCE_COMMIT, binding['path']), binding,
                      'retained failed-commit input')
    old_binding = manifest['failed_source_closure']
    require(old_binding['path'] == driver.CLOSURE, 'failed source closure path differs')
    old_raw = git_file(FAILED_SOURCE_COMMIT, old_binding['path'])
    check_binding(old_raw, old_binding, 'failed source closure')
    old = json.loads(old_raw)
    require(old['targets'] == list(driver.TARGETS) and old['missing'] == [] and
            set(old['project_sources']) == set(graph) and len(graph) == 316,
            'repair changed the full source closure scope')
    for module, row in old['project_sources'].items():
        require(row['path'] == s.h.module_path(module) and row['imports'] == graph[module],
                'repair changed project import graph: ' + module)
        if module not in TARGETS:
            require(row['sha256'] == sources[module],
                    'outside the two authorized source repairs: ' + module)
    preimages, payloads, updates = {}, {}, []
    for row in files:
        module, path = row['module'], row['path']
        require(path == s.h.module_path(module) and module in graph and
                row['before']['sha256'] == old['project_sources'][module]['sha256'] and
                row['after']['sha256'] == sources[module], 'repair source identity differs')
        before, after = git_file(FAILED_SOURCE_COMMIT, path), git_file(commit, path)
        check_binding(before, row['before'], 'published repair preimage')
        check_binding(after, row['after'], 'published repair postimage')
        require(reconstruct(before, row['exact_byte_splices']) == after and before != after,
                'published postimage is not the exact authorized byte repair')
        require(s.h.imports(before) == s.h.imports(after), 'repair changes imports')
        require(before.count(b'\r\n') == after.count(b'\r\n') and
                before.endswith(b'\n') and after.endswith(b'\n'), 'repair changes line-ending contract')
        for replacement in row['replacements']:
            old_text, new_text = replacement['old_utf8'], replacement['new_utf8']
            require(type(replacement['count']) is int and replacement['count'] > 0 and
                    before.count(old_text.encode('utf-8')) == replacement['count'] and
                    sum(r['old_utf8'] == old_text and r['new_utf8'] == new_text
                        for r in row['exact_byte_splices']) == replacement['count'],
                    'repair replacement count differs')
        preimages[path], payloads[path] = before, after
        updates.append({'module': module, 'path': path,
                        'before_sha256': row['before']['sha256'],
                        'after_sha256': row['after']['sha256'],
                        'cloud_source_mutation_required': True})
    return manifest, raw, preimages, payloads, updates


def apply_repairs(driver, s, commit, run):
    require(__debug__, 'Python assertions are required by the immutable source installer')
    s.d.verify_lane(s.h)
    manifest, graph, sources, closure_binding = driver.source_manifest(s, commit, list(driver.TARGETS))
    require(manifest['targets'] == list(driver.TARGETS) and len(graph) == 316 and
            len(set(graph) - set(TARGETS)) == 314, 'complete 316-source closure required')
    _, _, reuse_binding = driver.reuse_manifest(s, commit, graph, sources)
    repairs, repairs_raw, preimages, payloads, updates = repair_inputs(driver, s, commit, graph, sources)
    review = json.loads(driver.pinned(commit, driver.REVIEW, driver.REVIEW_SHA))
    for path, expected in review['source_configuration_bindings'].items():
        check_binding(git_file(commit, path), expected, 'published configuration')
    before = context(driver, s, review)
    observed = {}
    for module in sorted(graph):
        relative = s.h.module_path(module)
        path = PROJECT / relative
        require(path.parent.resolve() == (PROJECT / 'ImbalancedChen').resolve() and
                not path.parent.is_symlink() and not path.is_symlink() and path.is_file(),
                'expected existing regular source: ' + module)
        actual = path.read_bytes()
        published = git_file(commit, relative)
        require(sha(published) == sources[module], 'published source changed: ' + module)
        if module in TARGETS:
            require(actual in (preimages[relative], payloads[relative]),
                    'UNKNOWN_REPAIR_PREIMAGE: ' + module)
        else:
            require(actual == published, 'UNRELATED_SOURCE_DIFFERS: ' + module)
        observed[module] = sha(actual)
    actual_graph, actual = s.h.project_graph(PROJECT, manifest['targets'])
    require(actual_graph == graph and {m: r['sha256'] for m, r in actual.items()} == observed,
            'installed graph/source changed during full repair preflight')
    require(context(driver, s, review) == before, 'runtime context changed during preflight')
    s.d.write_frozen(run / 'FIRST_COMPILE_REPAIRS.json', repairs_raw)
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {
        'source_commit': commit, 'failed_source_commit': FAILED_SOURCE_COMMIT,
        'repairs': {'path': REPAIRS, 'bytes': len(repairs_raw), 'sha256': sha(repairs_raw)},
        'closure': closure_binding, 'p3_reuse': reuse_binding, 'updates': updates,
        'all_316_sources_before': observed, 'unchanged_other_source_count': 314,
        'context_before': before, 'cache_write_requested': False})
    # All 316 sources and both exact repair preimages have passed before this
    # call. The pinned helper rechecks the entire two-file batch before backups,
    # then replaces only these two source paths; postimages stay untouched.
    records = s.h.install_sources(PROJECT, updates, payloads, run / 'backups')
    require([row['module'] for row in records] == list(TARGETS), 'installed repair scope differs')
    for row in records:
        if row['mutated']:
            backup = run / 'backups' / row['path']
            require(backup.is_file() and not backup.is_symlink() and
                    backup.read_bytes() == preimages[row['path']], 'source backup differs')
    actual_graph, actual = s.h.project_graph(PROJECT, manifest['targets'])
    require(actual_graph == graph and {m: r['sha256'] for m, r in actual.items()} == sources,
            'post-repair complete source graph/hash differs')
    after = context(driver, s, review)
    require(after == before, 'runtime/configuration/protected source changed')
    result = {'status': 'EXACT_SOURCE_REPAIRS_VERIFIED_NOT_COMPILED',
              'source_commit': commit, 'failed_source_commit': FAILED_SOURCE_COMMIT,
              'failed_job': repairs['failed_job'], 'project_source_count': len(graph),
              'unchanged_other_source_count': 314, 'repair_records': records,
              'mutated_sources': [r['module'] for r in records if r['mutated']],
              'already_after_noop': [r['module'] for r in records if not r['mutated']],
              'context_before': before, 'context_after': after,
              'cache_write_requested': False, 'dependency_rebuild_requested': False,
              'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', result)
    s.ops.emit('P15_FIRST_COMPILE_SOURCE_REPAIRS_APPLIED', **result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    require(re.fullmatch('[0-9a-f]{40}', commit), 'require a full source commit SHA')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source-commit must name a commit')
    require(Path(__file__).read_bytes() == git_file(commit, SCRIPT),
            'executed repair script differs from selected published commit')
    driver, s, code = load_driver(commit)
    base = ROOT / commit / 'first-compile-source-repairs'
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name)
                and run.is_dir(), 'unexpected source-repair worker path')
        apply_repairs(driver, s, commit, run)
        return 0
    run = s.d.attempt(base)
    before = s.d.original_git_state(REPO)
    s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-source-repairs.py'
    s.d.write_frozen(executed, Path(__file__).read_bytes())
    s.d.write_frozen(run / 'published-driver.py', code)
    try:
        command = s.ops.run(run, 'serialized-source-repairs',
            s.h.serialize(0, run / 'SOURCE_REPAIR_LANE.json',
                ['python3', '-B', str(executed), '--source-commit', commit,
                 '--inside-lane', str(run)]), relay=True)
        require(command['exit_code'] == 0, 'source repairs held or failed')
    finally:
        after = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        require(after == before, 'original dirty repository state changed')
    return 0


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
