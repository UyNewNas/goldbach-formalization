"""Bind/install exact34 source and the unchanged original26a6 configuration.

This source may execute only in a separately root-finalized GitHub driver.
"""
import hashlib
import os
from pathlib import Path
import re
import shutil
import sys

from coherent_cache import HERE, WEIL, checked, git, read, require, sha, write

BUNDLE = HERE.parent
SOURCE = '9c26636f2bf35991f0fb16e4fe76eb165bdee056'


def data():
    return read(BUNDLE/'STAGE_A34.json')


def roots():
    return Path(os.environ['PROJECT']).resolve(), Path(os.environ['LOGS']).resolve()


def committed(workspace, commit, row):
    relative = Path(row['path'])
    require(not relative.is_absolute() and '..' not in relative.parts, 'Committed path escape')
    path = workspace/relative
    checked(path, row)
    require(git('-C', workspace, 'show', commit+':'+relative.as_posix()) == path.read_bytes(),
            'Working input differs from actual committed bytes')
    return path


def bind():
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux', 'GitHub Linux only')
    require(os.environ['CACHE_SCOPE'] == WEIL, 'Explicit independent Weil scope required')
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
    commit = os.environ['GITHUB_SHA']
    control = BUNDLE/'ROOT_CONTROL.json'
    require(git('-C', workspace, 'show', commit+':'+control.relative_to(workspace).as_posix()) == control.read_bytes(),
            'Root control not committed')
    c = read(control)
    require(c['schema'] == 'weil34-original26a6-root-control-v1' and c['cache_scope'] == WEIL,
            'Wrong root-controlled caller scope')
    require(c['driverReady'] is True and c['source_commit'] == SOURCE
            and os.environ['SOURCE_COMMIT'] == SOURCE, 'STATIC package is not an authorized ready driver')
    require(re.fullmatch('[0-9a-f]{40}', c['driver_base']) is not None
            and c['driver_branch'].startswith('ci/'), 'ROOT must freeze a concrete direct parent/branch')
    require(os.environ['GITHUB_EVENT_NAME'] == 'push'
            and os.environ['GITHUB_REF'] == 'refs/heads/'+c['driver_branch'], 'Wrong driver event/ref')
    parents = [x[7:].decode() for x in git('-C', workspace, 'cat-file', 'commit', commit).split(b'\n\n', 1)[0].splitlines()
               if x.startswith(b'parent ')]
    require(parents == [c['driver_base']], 'Actual driver direct parent differs')
    require(BUNDLE == (workspace/c['bundle_path']).resolve(), 'Wrong committed bundle location')
    registry = read(BUNDLE/'REGISTRY.json')
    require(sha(BUNDLE/'REGISTRY.json') == c['registry_sha256'], 'ROOT registry pin differs')
    for row in registry['files']:
        committed(workspace, commit, dict(row, path=(Path(c['bundle_path'])/row['path']).as_posix()))
    workflows = {r['path']:r for r in c['reviewed_driver_workflows']}
    actual = {p.relative_to(workspace).as_posix() for ext in ['*.yml', '*.yaml']
              for p in (workspace/'.github/workflows').glob(ext)}
    require(len(workflows) == len(c['reviewed_driver_workflows']) and set(workflows) == actual
            and c['workflow_path'] in actual
            and c['other_auto_push_exclusion_review'] == 'PASS_EXACT_REVIEWED_DRIVER_WORKFLOW_BYTES',
            'ROOT must freeze the entire real workflow projection, including push exclusions')
    for row in workflows.values():
        committed(workspace, commit, row)
    from cache_bootstrap import ADOPTION
    require(c['bootstrap_cache'] == ADOPTION, 'Original same-producer Cache144 adoption changed')
    scope = data()
    require(len(scope['source_rows']) == len(scope['compile_order']) == 34
            and scope['source_commit'] == SOURCE
            and sha(BUNDLE/'configuration/lakefile.toml') == scope['profile']['sha256']
            and scope['profile']['bytes'] == 487, 'Original exact34/full26a6 scope changed')
    binding = dict(scope=WEIL, driver_commit=commit, run_id=os.environ['GITHUB_RUN_ID'],
                   run_attempt=os.environ['GITHUB_RUN_ATTEMPT'], job=os.environ['GITHUB_JOB'],
                   source_commit=SOURCE, source_manifest_sha256=sha(BUNDLE/'STAGE_A34.json'),
                   root_control_sha256=sha(control), registry_sha256=sha(BUNDLE/'REGISTRY.json'))
    return c, binding


def installed():
    c, binding = bind()
    project, _ = roots()
    for row in data()['source_rows']:
        source = project/row['installation_path']
        checked(source, row)
        from weil_inputs import header
        parsed = header(source.read_text(encoding='utf-8'))
        require(parsed['is_module'] == row['source_module_mode']
                and [r['module'] for r in parsed['explicit_imports']] == row['imports'],
                'Frozen vendor graph is not the real source header')
    for row in read(HERE/'inputs/T01_26A6_PROFILE_BRIDGE.json')['configuration']:
        checked(project/row['install_path'], row)
    audit = BUNDLE/'WeilAudit.lean'
    expected = dict(bytes=audit.stat().st_size, sha256=sha(audit))
    checked(project/'T01Audit.lean', expected)
    _, logs = roots()
    checked(logs/'T01Audit.lean', expected)
    checked(project/'LEANPOOL_LICENSE', c['license'])
    return binding


def stage():
    c, binding = bind()
    project, logs = roots()
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
    source = (workspace/c['source_checkout']).resolve()
    require(source.is_relative_to(workspace)
            and git('-C', source, 'rev-parse', 'HEAD').decode().strip() == SOURCE,
            'Exact immutable published source checkout required')
    require(not project.exists() and not project.is_relative_to(workspace), 'Separate fresh original-profile project required')
    project.mkdir(parents=True)
    logs.mkdir(parents=True, exist_ok=True)
    for row in read(HERE/'inputs/T01_26A6_PROFILE_BRIDGE.json')['configuration']:
        p = BUNDLE/row['path']
        checked(p, row)
        shutil.copyfile(p, project/row['install_path'])
    for row in data()['source_rows']:
        content = source/row['source_path']
        checked(content, row)
        require(git('-C', source, 'show', SOURCE+':'+row['source_path']) == content.read_bytes(), 'Vendor source is not exact committed bytes')
        dest = project/row['installation_path']
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(content, dest)
    license_row = c['license']
    license_path = source/license_row['path']
    checked(license_path, license_row)
    shutil.copyfile(license_path, project/'LEANPOOL_LICENSE')
    # These legacy collector slots describe the actual34; they add no lake library.
    shutil.copyfile(BUNDLE/'WeilAudit.lean', project/'T01Audit.lean')
    shutil.copyfile(BUNDLE/'WeilAudit.lean', logs/'T01Audit.lean')
    write(project/'T01_PROVENANCE.json', dict(schema='weil34-exact-source-original-profile-provenance-v1',
          binding=binding, modules=data()['source_rows'], adapter_stage_B='HOLD', full_J=False))
    write(logs/'WEIL_STAGE.json', dict(binding=binding, profile_sha256=sha(project/'lakefile.toml'),
          source_rows=data()['source_rows'], new_lake_library_added=False, proof_acceptance=False))
    installed()


if __name__ == '__main__':
    require(sys.argv[1:] == ['stage'], 'Only source staging is implemented here')
    stage()
