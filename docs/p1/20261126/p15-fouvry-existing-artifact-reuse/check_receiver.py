#!/usr/bin/env python3
"""Read fixed native-package metadata; optionally query four stock dependency hashes.

No artifact installation or proof compilation is implemented. Stock Lake is run
only inside an already available, verified read-only bwrap namespace and the
unchanged P1 guard/serializer. Failure to obtain that view is an explicit HOLD.
"""
import argparse
import contextlib
import errno
import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
PACKAGE = PROJECT / '.lake/packages/goldbach'
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-fouvry-existing-artifact-reuse-v1')
PREFIX = 'docs/p1/20261126/p15-fouvry-existing-artifact-reuse/'
SCRIPT = PREFIX + 'check_receiver.py'
BINDINGS = PREFIX + 'EVIDENCE_BINDINGS.json'
BINDINGS_SHA = 'f23c272c28132d6281d991fe2b546740f50d0019574200f25313355799c06f3e'
HELPER_COMMIT = 'd20acdf13882e17d97833064f5e7c54f3192b03c'
HELPER_PATH = 'docs/p1/20261125/p15-singleton-proper-power/run_selected.py'
HELPER_SHA = 'f260f575ed6f8a7998fd901d42f0f1cd87115c879c0dc3b2c10f04a7f9b35313'
REVIEW_PATH = 'docs/p1/20261125/runtime-configuration/review.json'
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
GOLDBACH_REVISION = '09b97db5764ade1246bfb77206baa1b124760958'
NATIVE = 'MathlibNt.AnalyticNumberTheory.LargeSieve.'
FRONTIER = tuple(NATIVE + 'LiLiuPrereqFouvry' + name for name in
                 ('Completion', 'StepanovHasse', 'StepanovNonzero', 'HarcosPowerSum'))
COMPLETE = NATIVE + 'LiLiuPrereqFouvryCompleteWeil'
PARENTS = tuple(NATIVE + 'LiLiuPrereqFouvry' + name for name in
                ('OddPrimePower', 'TwoPower', 'LocalGlobalBridge'))
PRESERVE = NATIVE + 'LiLiuPrereqFouvryArithmeticPoisson'
MODULES = FRONTIER + (COMPLETE,) + PARENTS + (PRESERVE,)
LIB_SUFFIXES = ('.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
                '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash',
                '.trace', '.ir', '.ir.hash', '.ir.sig', '.ir.sig.hash')
IR_SUFFIXES = ('.c', '.c.hash', '.setup.json', '.bc', '.bc.hash', '.o', '.o.hash',
               '.o.export', '.o.export.hash')
HEX16 = re.compile(r'[0-9a-f]{16}')
ANSI = re.compile(r'\x1b\[[0-9;]*[A-Za-z]')
UNEXPECTED_LAKE_ACTION = re.compile(
    r'\[\s*\d+\s*/\s*\d+\s*\]\s+(?:Built|Failed|Unpacked|Downloaded|Fetched|Restored)\b')

# This probe runs in the same namespace construction as every Lake query. It
# attempts no write to a pre-existing project, dependency, runtime, or cache.
READONLY_PROBE = r'''import json, os, re, sys
from pathlib import Path
run = Path(sys.argv[1]).resolve(strict=True)
protected = json.loads(sys.argv[2])
decode = lambda s: re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), s)
outside = []
for line in Path('/proc/self/mountinfo').read_text().splitlines():
    fields = line.split()
    path = Path(decode(fields[4]))
    if 'rw' in fields[5].split(',') and path != run and run not in path.parents:
        outside.append(str(path))
readonly = all(os.statvfs(p).f_flag & os.ST_RDONLY for p in protected)
own_rw = not (os.statvfs(run / 'tmp').f_flag & os.ST_RDONLY)
ok = readonly and own_rw and not outside
if ok:
    with (run / 'tmp' / 'namespace-probe-marker').open('xb') as out:
        out.write(b'owned query evidence only\n')
print(json.dumps({'schema': 'p15_readonly_namespace_probe_v1',
                  'protected_paths_readonly': bool(readonly),
                  'all_writable_mounts_within_owned_run': not outside,
                  'owned_tmp_writable': bool(own_rw),
                  'protected_path_count': len(protected), 'ok': bool(ok)}))
raise SystemExit(0 if ok else 3)
'''


class Hold(Exception):
    pass


def require(ok, code):
    if not ok:
        raise Hold(code)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fingerprint(path):
    """Hash an existing regular file, or report absence; never create a sidecar."""
    if not os.path.lexists(path):
        return None
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, 'rb') as source:
        before = os.fstat(source.fileno())
        require(stat.S_ISREG(before.st_mode), 'NONREGULAR_INPUT')
        digest = hashlib.sha256()
        for block in iter(lambda: source.read(1024 * 1024), b''):
            digest.update(block)
        after = os.fstat(source.fileno())
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns),
            'INPUT_CHANGED_DURING_READ')
    return {'bytes': before.st_size, 'sha256': digest.hexdigest()}


def git_file(commit, path, repo=REPO):
    # The explicit option also fails closed on a Git version that lacks the
    # no-lazy-fetch capability; an unknown environment variable alone would not.
    environment = dict(os.environ, GIT_OPTIONAL_LOCKS='0', GIT_NO_LAZY_FETCH='1',
                       GIT_TERMINAL_PROMPT='0')
    return subprocess.check_output(['git', '--no-lazy-fetch', 'show', commit + ':' + path],
                                   cwd=repo, env=environment, stderr=subprocess.DEVNULL)


def load_inputs(commit):
    code = git_file(commit, SCRIPT)
    require(code == Path(__file__).read_bytes(), 'EXECUTED_SCRIPT_DIFFERS_FROM_COMMIT')
    raw = git_file(commit, BINDINGS)
    require(sha(raw) == BINDINGS_SHA, 'FIXED_BINDINGS_DIFFER')
    manifest = json.loads(raw)
    require(manifest['schema'] == 'p15_fouvry_existing_artifact_readonly_reuse_bindings_v1'
            and manifest['project'] == str(PROJECT)
            and manifest['repository'] == str(REPO)
            and manifest['goldbach_package'] == str(PACKAGE)
            and manifest['source_goldbach_revision'] == GOLDBACH_REVISION
            and manifest['frontier_modules'] == list(FRONTIER)
            and manifest['direct_native_parents'] == list(PARENTS)
            and manifest['complete_weil_module'] == COMPLETE
            and set(manifest['known_source_pins']) == set(FRONTIER + (COMPLETE, PRESERVE))
            and set(manifest['donor_candidates']) == set(FRONTIER + (COMPLETE,)),
            'FIXED_NATIVE_SCOPE_DIFFERS')
    old = git_file(HELPER_COMMIT, HELPER_PATH)
    require(sha(old) == HELPER_SHA, 'PUBLISHED_HELPER_DIFFERS')
    driver = ModuleType('unchanged_published_p15_driver')
    driver.__file__ = HELPER_PATH
    exec(compile(old, HELPER_PATH, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT) == (REPO, PROJECT), 'HELPER_ENVIRONMENT_DIFFERS')
    helpers = driver.helpers()
    review_raw = git_file(HELPER_COMMIT, REVIEW_PATH)
    require(sha(review_raw) == REVIEW_SHA, 'RUNTIME_REVIEW_DIFFERS')
    return manifest, helpers, json.loads(review_raw), code, raw


def artifact_paths(module):
    require(module in MODULES, 'OUTSIDE_FIXED_NATIVE_SCOPE')
    rel = module.replace('.', '/')
    return {suffix: PACKAGE / '.lake/build/lib/lean' / (rel + suffix)
            for suffix in LIB_SUFFIXES} | {
        suffix: PACKAGE / '.lake/build/ir' / (rel + suffix) for suffix in IR_SUFFIXES}


def snapshot(s, manifest, review):
    require(PROJECT.resolve() == PROJECT and PACKAGE.resolve() == PACKAGE,
            'PROJECT_OR_PACKAGE_ROUTE_DIFFERS')
    configs = {p: fingerprint(Path(p)) for p in manifest['receiver_configuration_pins']}
    require(configs == manifest['receiver_configuration_pins'], 'NATIVE_OR_PROJECT_CONFIG_DIFFERS')
    runtime = s.d.runtime_binding(s.h)
    require(runtime == review['existing_runtime_bindings'], 'EXISTING_RUNTIME_DIFFERS')
    roots = {m: fingerprint(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    require(all(v is not None and v['sha256'] == s.h.FOUR_ROOTS[m] for m, v in roots.items()),
            'PROTECTED_SOURCE_ROOT_DIFFERS')
    modules = {}
    for module in MODULES:
        modules[module] = {
            'source': fingerprint(PACKAGE / (module.replace('.', '/') + '.lean')),
            'artifacts': {ext: fingerprint(p) for ext, p in artifact_paths(module).items()}}
    return {'configuration': configs, 'runtime': runtime, 'protected_roots': roots,
            'modules': modules}


def bounded_bytes(path, limit):
    binding = fingerprint(path)
    if binding is None or binding['bytes'] > limit:
        return None
    raw = path.read_bytes()
    require({'bytes': len(raw), 'sha256': sha(raw)} == binding, 'INPUT_CHANGED_DURING_READ')
    return raw


def trace_summary(module):
    paths = artifact_paths(module)
    raw = bounded_bytes(paths['.trace'], 2 * 1024 * 1024)
    if raw is None:
        return {'status': 'ABSENT_OR_EXCEEDS_BOUNDED_TRACE_READ'}
    try:
        value = json.loads(raw)
        inputs = dict(value.get('inputs', []))
        outputs = value.get('outputs', {})
        dep_hash = value.get('depHash')
        sides = {}
        for ext, field in (('.olean', 'o'), ('.ilean', 'i'), ('.c', 'c')):
            side = bounded_bytes(paths[ext + '.hash'], 64)
            text = side.decode('ascii').strip() if side is not None else ''
            valid = HEX16.fullmatch(text) is not None
            expected = [text + ext] if field == 'o' else text + ext
            sides[ext] = {'lake_hash': text if valid else None,
                          'sidecar_matches_trace_output': valid and outputs.get(field) == expected}
        return {'status': 'PUBLIC_TRACE_FIELDS_READ',
                'depHash': dep_hash if isinstance(dep_hash, str) and HEX16.fullmatch(dep_hash) else None,
                'synthetic_false': value.get('synthetic', False) is False,
                'synthetic_field_present': 'synthetic' in value,
                'legacy_olean': outputs.get('m') is False,
                'module_name_matches': 'Module.name: ' + module in inputs,
                'native_package_is_goldbach': 'Package.id?: (some goldbach)' in inputs,
                'native_lean_args_empty': 'Module.leanArgs: #[]' in inputs,
                'lean_version_caption_matches':
                    'Lean 4.33.0, commit 62eed1db4d67327ec8120be05f1a1b0847d74561' in inputs,
                'output_hash_bindings': sides}
    except (ValueError, TypeError, UnicodeError):
        return {'status': 'UNRESOLVED_TRACE_SCHEMA'}


def source_metadata(s, manifest, before):
    result = {}
    for module in MODULES:
        relative = module.replace('.', '/') + '.lean'
        actual = before['modules'][module]['source']
        row = {'path': str(PACKAGE / relative), 'observed': actual}
        if module in manifest['known_source_pins']:
            expected = manifest['known_source_pins'][module]
            raw = bounded_bytes(PACKAGE / relative, 1024 * 1024)
            row.update(expected=expected['source'],
                       source_matches_fixed_pin=actual == expected['source'],
                       literal_imports_match_fixed_pin=raw is not None and
                       s.h.imports(raw) == expected['imports'])
        else:
            # No parent source hash was present in the old bounded probes. A
            # fixed Git revision may resolve it; observed bytes never self-pin.
            try:
                committed = git_file(GOLDBACH_REVISION, relative, PACKAGE)
                binding = {'bytes': len(committed), 'sha256': sha(committed)}
                row.update(source_anchor_commit=GOLDBACH_REVISION, source_anchor=binding,
                           source_anchor_matches=actual == binding,
                           source_identity_status='MATCHES_FIXED_GOLDBACH_REVISION' if actual == binding
                           else 'UNRESOLVED_SOURCE_DIFFERS_FROM_FIXED_REVISION')
            except subprocess.CalledProcessError:
                row.update(source_anchor_commit=GOLDBACH_REVISION, source_anchor=None,
                           source_anchor_matches=False,
                           source_identity_status='UNRESOLVED_FIXED_GIT_OBJECT_UNAVAILABLE')
        row['trace'] = trace_summary(module)
        result[module] = row
    return result


def sandbox_argv(binary, run, command):
    return [str(binary), '--unshare-user', '--unshare-pid', '--unshare-net',
            '--cap-drop', 'ALL', '--ro-bind', '/', '/',
            '--proc', '/proc', '--remount-ro', '/proc',
            '--bind', str(run), str(run), '--die-with-parent', '--chdir', str(PROJECT),
            '--setenv', 'TMPDIR', str(run / 'tmp'), '--'] + list(command)


def quiet_command(s, run, name, argv):
    # The immutable helper saves its normal local command/log evidence. Its
    # replay excerpts are not emitted by this diagnostic or its public result.
    with contextlib.redirect_stdout(io.StringIO()):
        record = s.ops.run(run, name, argv, cwd=PROJECT, relay=False)
    return record


def public_command(record):
    return {k: record[k] for k in ('exit_code', 'log_bytes', 'log_sha256',
                                   'actual_built_modules', 'actual_failed_modules')}


def last_log_line(path):
    last, unexpected = '', False
    with Path(path).open(encoding='utf-8', errors='replace') as source:
        for line in source:
            clean = ANSI.sub('', line).strip()
            if clean:
                last = clean if len(clean) <= 1024 else ''
            unexpected |= UNEXPECTED_LAKE_ACTION.search(clean) is not None
    return last, unexpected


def namespace_tool_binding(binary):
    require(binary.is_file() and os.access(binary, os.X_OK), 'READONLY_NAMESPACE_UNAVAILABLE')
    require(not (binary.stat().st_mode & (stat.S_ISUID | stat.S_ISGID)),
            'PRIVILEGED_NAMESPACE_BINARY_NOT_ALLOWED')
    try:
        require(not os.getxattr(binary, 'security.capability'),
                'PRIVILEGED_NAMESPACE_BINARY_NOT_ALLOWED')
    except OSError as exc:
        require(exc.errno == errno.ENODATA, 'NAMESPACE_BINARY_CAPABILITIES_UNRESOLVED')
    with binary.open('rb') as stream:
        require(stream.read(4) == b'\x7fELF', 'READONLY_NAMESPACE_TOOL_NOT_ELF')
    observed = binary.stat()
    return {**fingerprint(binary), 'mode': stat.S_IMODE(observed.st_mode),
            'uid': observed.st_uid, 'gid': observed.st_gid, 'file_capabilities': 'absent'}


def query_four(s, manifest, review, before, run, report):
    binary = Path('/usr/bin/bwrap')
    require(binary.is_file() and os.access(binary, os.X_OK), 'READONLY_NAMESPACE_UNAVAILABLE')
    binary = binary.resolve(strict=True)
    binding = namespace_tool_binding(binary)
    report['readonly_tool'] = {'path': str(binary), **binding}
    (run / 'tmp').mkdir(exist_ok=False)
    probe = run / 'read_only_namespace_probe.py'
    s.d.write_frozen(probe, READONLY_PROBE.encode())
    protected = sorted({str(PROJECT), str(PACKAGE), str(REPO),
                        *manifest['receiver_configuration_pins'], *review['existing_runtime_bindings']})
    # Absent lakefile.lean is pinned as absent, so its existing parent is checked.
    protected = sorted({str(Path(p) if Path(p).exists() else Path(p).parent) for p in protected})
    command = sandbox_argv(binary, run, ['python3', '-B', str(probe), str(run), json.dumps(protected)])
    observed = quiet_command(s, run, 'readonly-namespace-probe', s.h.guard(0, command))
    report['namespace_probe_command'] = public_command(observed)
    require(observed['exit_code'] == 0, 'READONLY_NAMESPACE_UNUSABLE')
    line, _ = last_log_line(observed['log'])
    try:
        flags = json.loads(line)
    except ValueError:
        raise Hold('READONLY_NAMESPACE_PROBE_UNBOUND_OUTPUT') from None
    require(flags == {'schema': 'p15_readonly_namespace_probe_v1',
                      'protected_paths_readonly': True,
                      'all_writable_mounts_within_owned_run': True,
                      'owned_tmp_writable': True, 'protected_path_count': len(protected), 'ok': True},
            'READONLY_NAMESPACE_PROBE_FAILED')
    report['namespace_probe'] = flags
    require(snapshot(s, manifest, review) == before, 'PRE_QUERY_INPUT_CHANGED')
    for module in FRONTIER:
        require(namespace_tool_binding(binary) == binding, 'READONLY_NAMESPACE_TOOL_CHANGED')
        command = sandbox_argv(binary, run, ['lake', '--no-build', 'query', '+' + module + ':depHash'])
        record = quiet_command(s, run, module.rsplit('.', 1)[-1] + '-depHash', s.h.guard(0, command))
        row = {'module': module, 'expected_donor_depHash': manifest['donor_candidates'][module]['depHash'],
               'command': public_command(record), 'receiver_depHash': None,
               'matches_saved_donor_depHash': None, 'status': 'HOLD'}
        report['frontier_queries'].append(row)
        require(snapshot(s, manifest, review) == before, 'QUERY_INPUT_CHANGED')
        require(namespace_tool_binding(binary) == binding, 'READONLY_NAMESPACE_TOOL_CHANGED')
        line, action = last_log_line(record['log'])
        require(record['exit_code'] == 0 and not record['actual_built_modules'] and
                not record['actual_failed_modules'] and not action,
                'STOCK_QUERY_HELD_WITHOUT_CACHE_REPAIR')
        require(HEX16.fullmatch(line), 'STOCK_QUERY_NO_UNAMBIGUOUS_DEP_HASH')
        matches = line == row['expected_donor_depHash']
        row.update(receiver_depHash=line, matches_saved_donor_depHash=matches,
                   status='DEP_HASH_MATCH' if matches else 'DEP_HASH_MISMATCH')


def public_summary(report, result_path):
    """Keep stdout small; full public fingerprints remain in the owned receipt."""
    fields = ('schema', 'source_commit', 'mode', 'status', 'failure_code',
              'script_sha256', 'bindings_sha256', 'readonly_tool', 'namespace_probe',
              'namespace_probe_command', 'frontier_queries',
              'source_artifact_configuration_runtime_unchanged',
              'before_snapshot_sha256', 'after_snapshot_sha256',
              'repository_git_metadata_unchanged', 'frozen_inputs_unchanged',
              'worker_exit_code', 'worker_reported_status', 'worker_failure_code',
              'complete_weil_native_parent_stock_readiness',
              'overall_ready_for_cache_adoption', 'proof_compilation_requested',
              'cache_transfer_requested', 'trace_or_config_or_guard_changes_requested',
              'new_lean_acceptance')
    result = {k: report[k] for k in fields if k in report}
    result['public_result'] = {'path': str(result_path), **fingerprint(result_path)}
    sources = report.get('source_metadata', {})
    artifacts = report.get('receiver_artifact_fingerprints', {})
    result['direct_native_parents'] = {
        m: {'source': sources.get(m, {}).get('observed'),
            'source_identity_status': sources.get(m, {}).get('source_identity_status'),
            'olean': artifacts.get(m, {}).get('.olean'),
            'trace_file': artifacts.get(m, {}).get('.trace'),
            'trace_metadata': sources.get(m, {}).get('trace')} for m in PARENTS}
    return result


def worker(commit, run, query, manifest, s, review, code, raw):
    s.d.verify_lane(s.h)
    report = {'schema': 'p15_fouvry_receiver_readonly_compatibility_result_v1',
              'source_commit': commit, 'mode': 'query' if query else 'metadata',
              'script_sha256': sha(code), 'bindings_sha256': sha(raw),
              'project': str(PROJECT), 'native_package': str(PACKAGE),
              'saved_observation_bindings': manifest['saved_observation_bindings'],
              'frontier_queries': [], 'status': 'HOLD',
              'complete_weil_native_parent_stock_readiness': 'NOT_TESTED',
              'overall_ready_for_cache_adoption': False,
              'proof_compilation_requested': False, 'cache_transfer_requested': False,
              'trace_or_config_or_guard_changes_requested': False,
              'new_lean_acceptance': False}
    before = None
    error = None
    try:
        before = snapshot(s, manifest, review)
        report['source_metadata'] = source_metadata(s, manifest, before)
        report['receiver_artifact_fingerprints'] = {
            m: row['artifacts'] for m, row in before['modules'].items()}
        for module in FRONTIER + (COMPLETE, PRESERVE):
            row = report['source_metadata'][module]
            require(row['source_matches_fixed_pin'] and row['literal_imports_match_fixed_pin'],
                    'KNOWN_NATIVE_SOURCE_OR_IMPORTS_DIFFER')
        preserve = manifest['arithmetic_poisson_preserve']['observed']
        require(all(before['modules'][PRESERVE]['artifacts'][ext] == value['fingerprint']
                    for ext, value in preserve.items() if ext != 'source'),
                'PRESERVED_ARITHMETIC_POISSON_ARTIFACT_DIFFERS')
        if query:
            query_four(s, manifest, review, before, run, report)
            report['status'] = ('FOUR_FRONTIER_DEP_HASHES_MATCH_DONOR'
                                if all(row['matches_saved_donor_depHash'] for row in report['frontier_queries'])
                                else 'FRONTIER_DEP_HASH_MISMATCH')
        else:
            report['status'] = 'METADATA_RECORDED_COMPATIBILITY_UNRESOLVED'
    except Hold as exc:
        error = str(exc)
    except Exception as exc:
        error = 'UNEXPECTED_' + type(exc).__name__
    finally:
        if before is not None:
            try:
                after = snapshot(s, manifest, review)
                report['source_artifact_configuration_runtime_unchanged'] = after == before
                report['before_snapshot_sha256'] = sha(json.dumps(before, sort_keys=True).encode())
                report['after_snapshot_sha256'] = sha(json.dumps(after, sort_keys=True).encode())
                if after != before:
                    error = 'FINAL_INPUT_CHANGED'
            except Exception:
                report['source_artifact_configuration_runtime_unchanged'] = False
                error = 'FINAL_CONTEXT_CHECK_FAILED'
        if error:
            report.update(status='HOLD', failure_code=error)
        s.d.save(run / 'PUBLIC_RESULT.json', report)
        print(json.dumps(public_summary(report, run / 'PUBLIC_RESULT.json'), sort_keys=True), flush=True)
    return 3 if error else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--query', action='store_true', help='attempt only the four fixed stock depHash queries')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    require(re.fullmatch('[0-9a-f]{40}', args.source_commit), 'FULL_SOURCE_COMMIT_REQUIRED')
    manifest, s, review, code, raw = load_inputs(args.source_commit)
    base = ROOT / args.source_commit
    if args.inside_lane:
        run = args.inside_lane.resolve(strict=True)
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name)
                and not run.is_relative_to(PROJECT) and not run.is_relative_to(REPO),
                'UNEXPECTED_OWNED_EVIDENCE_PATH')
        return worker(args.source_commit, run, args.query, manifest, s, review, code, raw)
    run = s.d.attempt(base)
    require(run.resolve() == run and not base.is_symlink(), 'EVIDENCE_PATH_IS_SYMLINKED')
    executed = run / 'executed-check-receiver.py'
    s.d.write_frozen(executed, code)
    s.d.write_frozen(run / 'EVIDENCE_BINDINGS.json', raw)
    before = s.d.original_git_state(REPO)
    child = ['python3', '-B', str(executed), '--source-commit', args.source_commit,
             '--inside-lane', str(run)] + (['--query'] if args.query else [])
    record = quiet_command(s, run, 'serialized-readonly-check',
                           s.h.serialize(0, run / 'QUERY_LANE.json', child))
    after = s.d.original_git_state(REPO)
    stable = before == after
    payload = bounded_bytes(run / 'PUBLIC_RESULT.json', 256 * 1024)
    report = json.loads(payload) if payload is not None else {
        'schema': 'p15_fouvry_receiver_readonly_compatibility_result_v1',
        'status': 'HOLD', 'failure_code': 'SERIALIZED_WORKER_NO_PUBLIC_RESULT'}
    frozen = (fingerprint(executed) == {'bytes': len(code), 'sha256': sha(code)} and
              fingerprint(run / 'EVIDENCE_BINDINGS.json') == {'bytes': len(raw), 'sha256': sha(raw)})
    report.update(repository_git_metadata_unchanged=stable, frozen_inputs_unchanged=frozen,
                  worker_exit_code=record['exit_code'])
    if record['exit_code'] != 0:
        report['worker_reported_status'] = report.get('status')
        report['worker_failure_code'] = report.get('failure_code')
        report.update(status='HOLD', failure_code='SERIALIZED_WORKER_DID_NOT_EXIT_ZERO')
    if not stable or not frozen:
        report.update(status='HOLD', failure_code='FINAL_REPOSITORY_OR_FROZEN_INPUT_CHANGED')
    s.d.save(run / 'PUBLIC_FINAL_RESULT.json', report)
    print(json.dumps(public_summary(report, run / 'PUBLIC_FINAL_RESULT.json'), sort_keys=True), flush=True)
    return 0 if stable and frozen and record['exit_code'] == 0 and report.get('status') != 'HOLD' else 3


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    os.environ['GIT_TERMINAL_PROMPT'] = '0'
    try:
        raise SystemExit(main())
    except Hold as exc:
        print(json.dumps({'status': 'HOLD', 'failure_code': str(exc)}), flush=True)
        raise SystemExit(3)
    except Exception as exc:
        print(json.dumps({'status': 'HOLD', 'failure_code': 'UNEXPECTED_' + type(exc).__name__}), flush=True)
        raise SystemExit(3)
