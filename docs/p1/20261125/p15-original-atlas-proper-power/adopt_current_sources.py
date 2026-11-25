#!/usr/bin/env python3
"""Adopt the exact existing fixes and finite-source layering; never build or edit caches."""
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
ROOT = Path('/workspace/p1-complete-proof/20261125-p15-original-atlas-proper-power-v1')
PREFIX = 'docs/p1/20261125/p15-original-atlas-proper-power/'
SCRIPT = PREFIX + 'adopt_current_sources.py'
MANIFEST = PREFIX + 'SOURCE_DEPLOYMENT.json'
BASE_COMMIT = 'bbcf75642ec19ebd976820c89011e83351856756'
REUSED_COMMIT = 'a392cd8efcf4f0b4adf3d12f2d8db41370309ed3'
REUSED_PREFIX = 'docs/verification/20261123-blue-compilation/reindex-isolated/postimages/'
EXISTING_FIXES = {
    'ImbalancedChen.P5OriginalHBMediumChartReserves',
    'ImbalancedChen.P5SmoothChartPhysicalHBBranch',
    'ImbalancedChen.P5ActualMultiGroupHBChartScale',
    'ImbalancedChen.P5ActualHBChartEventualClosure',
    'ImbalancedChen.P5OriginalChartRoughCutoff',
    'ImbalancedChen.P5ExactOriginalSmoothDyadicPartition',
    'ImbalancedChen.P5ActualLabelledPrimeSmoothCharts',
    'ImbalancedChen.Part3OriginalProperPowerChartCount',
    'ImbalancedChen.Part3ActualOriginalProperPowerChartBridge',
}
LAYERED = {'ImbalancedChen.Part3FiniteLambdaOverLogDictionary',
           'ImbalancedChen.Part3AllKLambdaChartCorrection'}
NEW_OWNERS = {'ImbalancedChen.Part3FiniteLambdaOverLogCore',
              'ImbalancedChen.PrimeProductsMellinExactMeanInsertion',
              'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
              'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
              'ImbalancedChen.P1OriginalSingletonSmoothLicence',
              'ImbalancedChen.P1OriginalSingletonAtlasProperPower'}
INACTIVE = {'ImbalancedChen.Part3FiniteLambdaOverLogDictionary'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def load_driver(commit):
    raw = git_file(commit, PREFIX + 'run_selected.py')
    driver = ModuleType('published_atlas_driver')
    driver.__file__ = PREFIX + 'run_selected.py'
    exec(compile(raw, driver.__file__, 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT) and
         set(driver.TARGETS) == NEW_OWNERS and len(driver.TARGETS) == 6,
         'six-owner compiler environment differs')
    return driver, driver.helpers(), raw


def context(driver, s, review):
    config = {p: s.d.fingerprint(PROJECT / p)
              for p in review['runtime_configuration_bindings']}
    need(config == review['runtime_configuration_bindings'] and
         not os.path.lexists(PROJECT / 'lakefile.lean'), 'runtime configuration differs')
    runtime = s.d.runtime_binding(s.h)
    need(runtime == review['existing_runtime_bindings'], 'runtime guard bindings differ')
    roots = {m: driver.file_binding(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    need(roots == s.h.FOUR_ROOTS, 'protected P1 roots differ')
    return {'configuration': config, 'runtime': runtime, 'protected_roots': roots}


def exact_binding(raw, row):
    need({'bytes': len(raw), 'sha256': sha(raw)} ==
         {k: row[k] for k in ['bytes', 'sha256']}, 'source binding differs')


def source_path(s, module):
    path = PROJECT / s.h.module_path(module)
    need(path.parent.resolve() == (PROJECT / 'ImbalancedChen').resolve() and
         not path.parent.is_symlink() and not path.is_symlink(), 'noncanonical source path')
    return path


def owner_cache(s, modules):
    result = {}
    for module in sorted(modules):
        stem = module.replace('.', '/')
        for extension in ['.olean', '.trace', '.olean.private', '.olean.server']:
            relative = '.lake/build/lib/lean/' + stem + extension
            path = PROJECT / relative
            need(not path.is_symlink(), 'unexpected cache symlink')
            result[relative] = s.d.fingerprint(path) if path.is_file() else None
    return result


def adopt(driver, s, commit, run):
    need(__debug__, 'immutable helper assertions are required')
    s.d.verify_lane(s.h)
    current, graph, sources, binding = driver.source_manifest(s, commit, list(driver.TARGETS))
    need(len(graph) == 168 and set(current['targets']) == NEW_OWNERS,
         'full 168-source closure required')
    manifest_raw = git_file(commit, MANIFEST)
    manifest = json.loads(manifest_raw)
    need(manifest['schema'] == 'p15_atlas_exact_source_deployment_v1' and
         manifest['base_commit'] == BASE_COMMIT and manifest['project_source_count'] == 168,
         'deployment manifest scope differs')
    changes, additions = manifest['changes'], manifest['additions']
    need(len(changes) == 11 and {r['module'] for r in changes} == EXISTING_FIXES | LAYERED,
         'existing-source mutation scope differs')
    need(len(additions) == 6 and {r['module'] for r in additions} == NEW_OWNERS,
         'new-owner addition scope differs')
    need(({r['module'] for r in changes} - set(graph)) == INACTIVE,
         'inactive dictionary source scope differs')
    need(manifest['source_closure_sha256'] == sha(git_file(commit, driver.CLOSURE)),
         'deployment/full-source-closure binding differs')
    review = json.loads(driver.pinned(commit, driver.REVIEW, driver.REVIEW_SHA))
    for path, expected in review['source_configuration_bindings'].items():
        exact_binding(git_file(commit, path), expected)
    before = context(driver, s, review)
    before_cache = owner_cache(s, EXISTING_FIXES | LAYERED | NEW_OWNERS)
    preimages, payloads, updates = {}, {}, []
    for row in changes:
        module, relative = row['module'], row['path']
        need(relative == s.h.module_path(module), 'changed source path differs')
        old, new = git_file(BASE_COMMIT, relative), git_file(commit, relative)
        exact_binding(old, row['before'])
        exact_binding(new, row['after'])
        need(old != new, 'declared source change is a no-op')
        if module in EXISTING_FIXES:
            need(new == git_file(REUSED_COMMIT, REUSED_PREFIX + relative),
                 'existing proof is not the exact accepted postimage')
            need(s.h.imports(old) == s.h.imports(new), 'existing fix changes imports')
        if module in graph:
            need(sha(new) == sources[module], 'changed owner differs from complete closure')
        preimages[module], payloads[relative] = old, new
        updates.append({'module': module, 'path': relative,
                        'before_sha256': sha(old), 'after_sha256': sha(new),
                        'cloud_source_mutation_required': True})
    for row in additions:
        module, relative = row['module'], row['path']
        need(relative == s.h.module_path(module) and module in graph,
             'new source path differs')
        new = git_file(commit, relative)
        exact_binding(new, row['after'])
        need(sha(new) == sources[module], 'new owner differs from complete closure')
        payloads[relative] = new
    observed = {}
    for module in sorted(set(graph) | INACTIVE):
        path = source_path(s, module)
        published = git_file(commit, s.h.module_path(module))
        if module in graph:
            need(sha(published) == sources[module], 'published full source differs')
        actual = path.read_bytes() if path.is_file() else None
        need(actual is not None or not os.path.lexists(path), 'source is not a regular file')
        if module in preimages:
            need(actual in (preimages[module], published), 'unknown existing source preimage: ' + module)
            if actual == preimages[module]:
                for ext in ['.olean', '.olean.private', '.olean.server']:
                    key = '.lake/build/lib/lean/' + module.replace('.', '/') + ext
                    need(before_cache[key] is None,
                         'EXISTING_OBJECT_REQUIRES_REUSE_REVIEW_BEFORE_SOURCE_CHANGE: ' + module)
        elif module in NEW_OWNERS:
            need(actual is None or actual == published, 'new owner conflicts with existing source: ' + module)
        else:
            need(actual == published, 'unrelated source differs: ' + module)
        observed[module] = None if actual is None else sha(actual)
    need(context(driver, s, review) == before and
         owner_cache(s, EXISTING_FIXES | LAYERED | NEW_OWNERS) == before_cache,
         'source-adoption context changed during full preflight')
    s.d.save(run / 'SOURCE_DEPLOYMENT_PLAN.json', {
        'source_commit': commit, 'manifest_sha256': sha(manifest_raw),
        'complete_source_closure': binding, 'observed_source_sha256': observed,
        'context_before': before, 'touched_owner_cache_before': before_cache,
        'existing_changes': updates, 'additions': additions})
    # The immutable helper checks all existing preimages, makes backups, and
    # replaces only the eleven exact source paths. It never writes a cache.
    changed = s.h.install_sources(PROJECT, updates, payloads, run / 'source-backups')
    added, reused = [], []
    for row in additions:
        path = source_path(s, row['module'])
        data = payloads[row['path']]
        if path.exists():
            need(path.is_file() and path.read_bytes() == data, 'new owner changed after preflight')
            reused.append(row['module'])
        else:
            with path.open('xb') as stream:
                stream.write(data)
            added.append(row['module'])
    actual_graph, actual = s.h.project_graph(PROJECT, current['targets'])
    need(actual_graph == graph and {m: r['sha256'] for m, r in actual.items()} == sources,
         'complete post-adoption source graph differs')
    for module in INACTIVE:
        need(source_path(s, module).read_bytes() == payloads[s.h.module_path(module)],
             'complementary inactive provider differs')
    after = context(driver, s, review)
    after_cache = owner_cache(s, EXISTING_FIXES | LAYERED | NEW_OWNERS)
    need(after == before and after_cache == before_cache, 'runtime or touched owner cache changed')
    result = {'status': 'EXACT_ATLAS_SOURCE_ADOPTION_VERIFIED_NOT_COMPILED',
              'source_commit': commit, 'full_project_source_count': len(graph),
              'inactive_provider_updates': sorted(INACTIVE), 'source_changes': changed,
              'added_owners': added, 'existing_new_owner_sources_reused': reused,
              'runtime_configuration_unchanged': True, 'touched_owner_cache_unchanged': True,
              'cache_writes_requested': False, 'Lean_invocations': 0,
              'new_Lean_acceptance': False, 'whole_P1_5_complete': False}
    s.d.save(run / 'SOURCE_DEPLOYMENT_RESULT.json', result)
    s.ops.emit('P15_ATLAS_SOURCES_ADOPTED', **result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    need(re.fullmatch('[0-9a-f]{40}', commit), 'full source commit required')
    need(Path(__file__).read_bytes() == git_file(commit, SCRIPT), 'executed script differs from publication')
    driver, s, code = load_driver(commit)
    base = ROOT / commit / 'source-adoption-layered'
    if args.inside_lane:
        run = args.inside_lane.resolve()
        need(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
             'unexpected source-adoption worker directory')
        adopt(driver, s, commit, run)
        return 0
    run = s.d.attempt(base)
    before = s.d.original_git_state(REPO)
    s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-source-adoption.py'
    s.d.write_frozen(executed, Path(__file__).read_bytes())
    s.d.write_frozen(run / 'published-driver.py', code)
    try:
        command = s.ops.run(run, 'serialized-layered-source-adoption',
            s.h.serialize(0, run / 'SOURCE_ADOPTION_LANE.json',
                ['python3', '-B', str(executed), '--source-commit', commit,
                 '--inside-lane', str(run)]), relay=True)
        need(command['exit_code'] == 0, 'source adoption held or failed')
    finally:
        after = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        need(after == before, 'original dirty Git metadata changed')
    return 0


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
