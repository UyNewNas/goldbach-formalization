"""GitHub-only draft caller for one read-only stored checkpoint import."""
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True

from coherent_cache import CacheSession, PARENT as SCOPE, checked, read, require, sha, write
from plan_probe import H_AGG, compose, import_header, physical, read_pinned
from probe_policy import PROBE_SHA, verify_environment

PLAN = 'STORED_IMPORT_PLAN.json'
LAUNCH = 'STORED_IMPORT_LAUNCH.json'
RESULT = 'STORED_IMPORT_RESULT.json'
CLASSIFICATION = 'EXACT_STORED_IMPORT_ONLY_PROBE'

def installed_header(project, aggregate):
    probe = project / 'StoredImportProbe.lean'
    header = import_header(read_pinned(aggregate, H_AGG))
    with probe.open('xb') as out:
        out.write(header)
    read_pinned(probe, PROBE_SHA)

def planned(session, aggregate, pkg_lock):
    overlay = physical(Path(os.environ['STORED_IMPORT_OVERLAY']))
    p = session.project
    official_core = physical(Path(session.state['realbin']).parent / 'lib/lean')
    probe, record = compose(p, overlay, official_core, aggregate, pkg_lock)
    path = physical(p / 'StoredImportProbe.lean')
    require(read_pinned(path, PROBE_SHA) == probe, 'Probe header changed')
    record['exact_guard_arguments'] = [*record['argv_prefix'], str(path)]
    return record

def audit_once(session, plan_path, prior, expected):
    commands = session.policy_audit()
    events = [
        json.loads(x) for x in (session.logs / 'CACHE_PREEXEC_EVENTS.jsonl').read_text().splitlines()
        if x.strip()
    ]
    launch = session.receipt(LAUNCH)
    added = commands[len(prior):]
    require(commands[:len(prior)] == prior and len(added) == 1, 'Unexpected compiler command census')
    event = events[-1]
    require(event['classification'] == CLASSIFICATION and launch['pid'] == event['pid'] == added[0]['pid'],
            'Guarded child differs from committed launch')
    require(launch['argv'] == event['argv'] == expected['exact_guard_arguments'],
            'Guarded child arguments changed')
    environment = event['stored_import_environment']
    require(environment == launch['stored_import_environment'] and environment['plan_sha256'] == sha(plan_path)
            and environment['sysroot'] == session.state['shadow']
            and environment['lean_path'] == expected['lean_path'], 'Recorded child search path changed')
    return launch

def run(aggregate, pkg_lock):
    session = CacheSession(SCOPE)
    session.require_fixtures()
    session.qualification_inputs()
    before = session.verify_restored()
    prior = session.policy_audit()
    plan = planned(session, aggregate, pkg_lock)
    p, logs = session.project, session.logs
    plan_path = logs / PLAN
    write(plan_path, plan)
    policy = read(logs / 'CACHE_PREEXEC_POLICY.json')
    rows = [r for r in policy['admitted_commands'] if r['phase'] == 'qualified-project']
    require(len(rows) == 1 and rows[0]['classification'] == CLASSIFICATION
            and rows[0]['argv'] == plan['exact_guard_arguments'], 'Probe is not the sole scoped admission')
    source = rows[0]['source']
    checked(source['path'], source)
    session.emit('CACHE_CALLER_INPUTS.json', {
        'status': 'EXACT_IMPORT_ONLY_SOURCE_ADMITTED_ONCE',
        'qualification_sha256': sha(logs / 'CACHE_QUALIFICATION.json'),
        'stored_import_plan_sha256': sha(plan_path),
        'sources': {source['path']: source},
    })
    session.caller_inputs()
    env = dict(os.environ, LEAN_PATH=plan['lean_path'])
    env.pop('LEAN_SRC_PATH', None)
    verify_environment(plan_path, sha(plan_path), session.state['shadow'],
                       plan['official_core_root_expected_in_dist'], env)
    wrapper = physical(Path(session.state['shadow']) / 'bin/lean')
    argv = [str(wrapper), *plan['exact_guard_arguments'][3:]]
    with (logs / 'stored-import.stdout').open('xb') as out, (logs / 'stored-import.stderr').open('xb') as err:
        child = subprocess.run(argv, cwd=p, env=env, stdout=out, stderr=err, timeout=900)
    session.emit('STORED_IMPORT_PROCESS.json', {
        'exit_code': child.returncode, 'argv': argv,
        'stdout_sha256': sha(logs / 'stored-import.stdout'),
        'stderr_sha256': sha(logs / 'stored-import.stderr'),
    })
    require(child.returncode == 0, 'Exact Lean import-only child failed; see process logs')
    launch = audit_once(session, plan_path, prior, plan)
    require(planned(session, aggregate, pkg_lock) == plan, 'Restored input changed during import')
    require(session.verify_restored() == before, 'Original stock parent restore changed during import')
    session.qualification_inputs()
    session.caller_inputs()
    require(set(p.glob('StoredImportProbe.*')) == {Path(source['path'])}, 'Unexpected probe outputs')
    session.emit(RESULT, {
        'status': 'PASS_EXACT_IMPORT_ONLY_NOT_AGGREGATE_ACCEPTANCE',
        'import_roots': 73, 'physical_package_parts': plan['package_count'],
        'plan_sha256': sha(plan_path), 'launch_pid': launch['pid'],
        'process_sha256': sha(logs / 'STORED_IMPORT_PROCESS.json'),
        'protected_source_compiler_starts': 0, 'new_objects_emitted': 0,
        'aggregate_compiled': False, 'aggregate_kernel_replayed': False,
        'aggregate_owned_type_and_axiom_audit': False,
    })

def main():
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux',
            'GitHub Linux only')
    mode, *args = sys.argv[1:]
    if mode == 'install-header' and len(args) == 1:
        installed_header(physical(Path(os.environ['PROJECT'])), Path(args[0]))
    elif mode == 'run' and len(args) == 2:
        run(*map(Path, args))
    else:
        raise ValueError('Expected install-header AGGREGATE or run AGGREGATE PACKAGE_LOCK')

if __name__ == '__main__':
    main()
