#!/usr/bin/env python3
"""Add only the missing complete-owned audit to exact SignedMidpoint artifacts.

The batch3 normal/kernel receipts remain the primary evidence.  This caller never
builds the target, invokes leanchecker, installs sources, or creates NORMAL_PASS.
--check is read-only.  A prior execution (even incomplete) is held, never retried.
The original serializer, guard, helper methods and Lean audit body are unchanged.
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
    raise RuntimeError('P1.4 audit guards forbid optimized Python execution')

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261128-p14-signed-owned-supplement')
PREFIX = 'docs/p1/20261128/p14-signed-owned-supplement/'
DRIVER = PREFIX + 'run_signed_owned_supplement.py'
MANIFEST = PREFIX + 'MANIFEST.json'
MODULE = 'ImbalancedChen.P5OriginalSignedMidpoint'
SHORT = MODULE.split('.')[-1]
SOURCE = MODULE.replace('.', '/') + '.lean'
LEGACY_COMMIT = 'a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52'
LEGACY_PREFIX = 'docs/verification/20261123-blue-compilation/member-repair-batch3/'
LEGACY_REVIEW = 'docs/p1/20261125/p14-continuation/REUSED_LEGACY_MIDPOINT_ARCHIVE.json'
LEGACY_REVIEW_SHA = '8d85bd418d3d4df79c584b78d0ab793999fbec77c3cc3ec8568f0545ae776058'
LEGACY_VERIFIER_SHA = '098a3b929ab6972a5eb6dc96576ad74f3fbd9e771775db5d3e0fd67db6adf9ab'
SEED_PREFIX = 'docs/verification/20261123-blue-compilation/member-repair-batch84/seed42-owned-only/'
SEED_MODULE = 'ImbalancedChen.P2Winner9CompleteSeedBlock42'
SEED_RUNNER_SHA = '46ae3fcdd278da88399f09a59edfb46cda94bdfdde875626e1d53710a7de0310'
SEED_TEMPLATE_SHA = '07f877ede58cfbea82f799daf124e63a82f252ba1589d87b9290aa99b7d02e84'
TOOLS_COMMIT = '220c14630ffd266f824bdbf0977147ecb740c0dd'
HELPERS = {
    'docs/p1/20261124/batch5-parallel/run_batch5_parallel.py':
        '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5',
    'docs/p1/20261125/batch10-resume/resume_batch10.py':
        '63e999403a1d39251642097c8a03e8b60983df785267fcca32f118b57aab2f71',
}
REVIEW = Path('/workspace/p1-complete-proof/20261125-batch16-repairs-v1/9ea714790c06b2270f2028555d9ba774b152d536/expression-two/inputs/review.json')
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
STATE = '/workspace/blue-build-tools/member-runtime-evidence/state.json'
LEAN_RUNTIME = '/workspace/blue-build-tools/member-runtime/p0-ci-shadow-toolchain/bin/lean-runtime'
RESOURCES = ['-t0', '-j2', '-M12288', '-D', 'maxRecDepth=100000', '-D', 'maxHeartbeats=4000000']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = ['sorryAx', '…', '⋯', '...']


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)


def pinned(repo, commit, specification):
    raw = git(repo, commit, specification['path'])
    need({'bytes': len(raw), 'sha256': sha(raw)} ==
         {key: specification[key] for key in ('bytes', 'sha256')},
         'frozen Git evidence differs: ' + specification['path'])
    return raw


def load(raw, name):
    module = types.ModuleType(name)
    module.__file__ = '<unchanged pinned Git object: ' + name + '>'
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def legacy_inputs(repo, manifest):
    """Read the published originals, without invoking Lean or writing a receipt."""
    need(manifest['schema'] == 'p14_signed_legacy_owned_only_supplement_v1' and
         manifest['module'] == MODULE and manifest['legacy_evidence_commit'] == LEGACY_COMMIT,
         'supplement scope or original evidence anchor differs')
    need(manifest['legacy_review']['path'] == LEGACY_REVIEW and
         manifest['legacy_review']['sha256'] == LEGACY_REVIEW_SHA and
         manifest['legacy_verifier']['path'] == LEGACY_REVIEW.replace(
             'REUSED_LEGACY_MIDPOINT_ARCHIVE.json', 'verify_legacy_evidence.py') and
         manifest['legacy_verifier']['sha256'] == LEGACY_VERIFIER_SHA,
         'frozen legacy review or verifier differs')
    review = json.loads(pinned(repo, LEGACY_COMMIT, manifest['legacy_review']))
    pinned(repo, LEGACY_COMMIT, manifest['legacy_verifier'])
    owner = review['owners'][MODULE]
    need(manifest['frozen_primary_evidence'] == owner['evidence_files'] and
         manifest['source_plus_five_original_snapshot'] == owner['source_plus_five_original_snapshot'] and
         manifest['original_public_names'] == owner['declaration_names'] and
         manifest['private_source_theorem_suffixes'] == ['anchored_remainder', 'half_weight_integral'],
         'primary receipts, source/output snapshot or declared original scope differs')
    raw = {row['path']: pinned(repo, LEGACY_COMMIT, row) for row in owner['evidence_files']}
    original = json.loads(raw[LEGACY_PREFIX + 'VALIDATION_RESULTS.json'])
    snapshot = owner['source_plus_five_original_snapshot']
    need(len(snapshot) == 6 and original['source_plus_five_outputs'][MODULE] == snapshot and
         original['modules'][MODULE] == snapshot[SOURCE]['sha256'], 'original snapshot mismatch')
    commands = {}
    for kind in ('normal', 'kernel'):
        need(json.loads(raw[LEGACY_PREFIX + SHORT + '-AFTER_' + kind.upper() + '.json']) == snapshot,
             'original source-plus-five changed: ' + kind)
        command = json.loads(raw[LEGACY_PREFIX + SHORT + '-' + kind + '-command.json'])
        need([row for row in original[kind + '_commands'] if row['name'] == SHORT + '-' + kind] == [command],
             'original command differs from original validation result')
        suffix = ['lake', 'build', MODULE + ':olean'] if kind == 'normal' else [
            'lake', 'env', 'leanchecker', '--verbose', MODULE]
        need(command['argv'] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', STATE] + suffix and
             command['cwd'] == str(PROJECT) and command['exit_code'] == 0,
             'original command scope or exit status differs')
        log = raw[LEGACY_PREFIX + command['log']]
        need(sha(log) == command['log_sha256'], 'original command log mismatch')
        if kind == 'normal':
            need(('Built ' + MODULE).encode() in log, 'original target build is absent')
        else:
            need(log.decode().strip() == 'replaying ' + MODULE, 'original kernel target differs')
        commands[kind] = command
    need(original['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_PUBLIC_TYPES_AXIOMS' and
         all(original[key] for key in ('only_standard_axioms', 'pp_all_true_no_elisions',
                                      'source_plus_five_outputs_unchanged_across_kernel_and_audit')),
         'original public audit prerequisites differ')
    public = [row for row in json.loads(raw[LEGACY_PREFIX + 'PUBLIC_EXPORTS.json']) if row['module'] == MODULE]
    need(len(public) == 7 and {row['name'] for row in public} == set(owner['declaration_names']) and
         all(not row['is_axiom_declaration'] and set(row['transitive_axioms']) <= ALLOWED for row in public),
         'original seven public exports differ')
    for key, path, digest in (
        ('original_owned_only_runner', SEED_PREFIX + 'run_owned_only.py', SEED_RUNNER_SHA),
        ('original_owned_only_template', SEED_PREFIX + 'OwnedOnlyAudit.lean', SEED_TEMPLATE_SHA),
    ):
        need(manifest[key]['path'] == path and manifest[key]['sha256'] == digest,
             'unchanged owned-only reference differs')
        pinned(repo, LEGACY_COMMIT, manifest[key])
    template = pinned(repo, LEGACY_COMMIT, manifest['original_owned_only_template'])
    need(template.count(SEED_MODULE.encode()) == 2 and manifest['audit_template_module_substitution'] ==
         {'from': SEED_MODULE, 'to': MODULE, 'occurrences': 2}, 'audit template substitution differs')
    for key in ('normal_kernel_reexecution_permitted', 'source_or_build_output_mutation_permitted',
                'synthesized_NORMAL_PASS_permitted', 'full_owned_count_preassumed',
                'whole_P1_4_complete', 'preparation_is_acceptance'):
        need(manifest[key] is False, 'supplement boundary changed: ' + key)
    need(manifest['runtime_review_path'] == str(REVIEW) and manifest['runtime_review_sha256'] == REVIEW_SHA and
         manifest['immutable_helper_commit'] == TOOLS_COMMIT and
         {row['path']: row['sha256'] for row in manifest['immutable_helpers']} == HELPERS and
         manifest['runtime_lane'] == 0 and manifest['runtime_state'] == STATE and
         manifest['actual_lean_runtime'] == LEAN_RUNTIME and manifest['actual_resource_arguments'] == RESOURCES and
         set(manifest['allowed_transitive_axioms']) == ALLOWED, 'immutable runtime boundary differs')
    return {'snapshot': snapshot, 'public': public, 'commands': commands,
            'audit_bytes': template.replace(SEED_MODULE.encode(), MODULE.encode()), 'raw': raw}


def read_owned(text, original_public):
    """Check the complete dynamic owner inventory, then match all old publics."""
    need(not any(token in text for token in FORBIDDEN), 'forbidden axiom or elided audit output')
    def rows(prefix):
        return [json.loads(line[len(prefix):]) for line in text.splitlines() if line.startswith(prefix)]
    inventories = rows('MEMBER_OWNED_NAMES ')
    records = rows('AUDIT_RECORD ')
    need(len(inventories) == 1, 'exactly one complete owned-name inventory is required')
    names = inventories[0]['names']
    need(names and len(names) == len(set(names)) and names == [row['name'] for row in records],
         'owned inventory is empty, duplicated or incomplete')
    need(rows('MEMBER_OWNED_MODULE ') == [{'module': MODULE, 'count': len(names)}] and
         rows('MEMBER_OWNED_COUNT ') == [len(names)], 'owned module/total counts differ')
    fields = {'name', 'module', 'kind', 'is_private', 'type', 'type_expression', 'universe_parameters', 'axioms'}
    for row in records:
        need(set(row) == fields and row['module'] == MODULE and
             row['kind'] in {'theorem', 'definition', 'opaque', 'quotient', 'inductive', 'constructor', 'recursor'} and
             type(row['is_private']) is bool and isinstance(row['type'], str) and row['type'] and
             isinstance(row['type_expression'], str) and row['type_expression'] and
             isinstance(row['universe_parameters'], list) and
             all(isinstance(value, str) for value in row['universe_parameters']) and
             isinstance(row['axioms'], list) and set(row['axioms']) <= ALLOWED,
             'owned record lacks complete type, AST, universes or allowed axioms')
        need(not any(token in row['type'] or token in row['type_expression'] for token in FORBIDDEN),
             'decoded type or AST contains elision/forbidden axiom')
    public = {row['name']: row for row in records if not row['is_private']}
    need(set(public) == {row['name'] for row in original_public}, 'original public-name set changed')
    for old in original_public:
        row = public[old['name']]
        need(row['module'] == old['module'] and row['type_expression'] == old['type_expression'] and
             row['universe_parameters'] == old['universe_parameters'] and
             set(row['axioms']) == set(old['transitive_axioms']), 'original public type/AST/universes/axioms changed')
    for suffix in ('anchored_remainder', 'half_weight_integral'):
        need(any(row['is_private'] and row['name'].endswith('.' + suffix) for row in records),
             'source private theorem is absent from dynamic owned inventory: ' + suffix)
    return records


def live_binding(h, d, review, original):
    runtime = d.runtime_binding(h)
    configuration = {path: d.fingerprint(PROJECT / path) for path in
                     ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')}
    need(runtime == review['existing_runtime_bindings'] and
         configuration == review['runtime_configuration_bindings'] and not (PROJECT / 'lakefile.lean').exists(),
         'existing runtime/guard/serializer/configuration binding changed')
    snapshot = d.snapshot(PROJECT, MODULE)
    need(snapshot == original['snapshot'], 'live source-plus-five does not match exact batch3 originals; HOLD')
    return {'source_plus_five': snapshot, 'runtime': runtime, 'configuration': configuration,
            'protected_roots': h.check_roots()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    source = args.source_commit
    need(re.fullmatch(r'[0-9a-f]{40}', source) is not None, 'a full published Git source commit is required')
    driver = Path(__file__).read_bytes()
    need(driver == git(REPO, source, DRIVER), 'executing caller differs from claimed published Git source')
    manifest_raw = git(REPO, source, MANIFEST)
    manifest = json.loads(manifest_raw)
    original = legacy_inputs(REPO, manifest)
    need(git(REPO, source, SOURCE) == original['raw'][SOURCE], 'claimed source changed since original batch3')
    need(manifest['audit_template']['path'] == PREFIX + 'OwnedOnlyAudit.lean' and
         pinned(REPO, source, manifest['audit_template']) == original['audit_bytes'],
         'full-owned audit body changed beyond its two module substitutions')
    raw_helpers = [pinned(REPO, TOOLS_COMMIT, row) for row in manifest['immutable_helpers']]
    need([row['path'] for row in manifest['immutable_helpers']] == list(HELPERS), 'helper order changed')
    h, d = [load(raw, name) for raw, name in zip(raw_helpers, ('original_batch5', 'original_batch10'))]
    review_raw = REVIEW.read_bytes()
    need(sha(review_raw) == REVIEW_SHA, 'frozen runtime review changed')
    review = json.loads(review_raw)
    current = live_binding(h, d, review, original)
    binding = {'schema': 'p14_signed_owned_only_execution_binding_v1', 'source_commit': source,
               'module': MODULE, 'driver_sha256': sha(driver), 'manifest_sha256': sha(manifest_raw),
               'audit_sha256': sha(original['audit_bytes']), 'legacy_evidence_commit': LEGACY_COMMIT,
               'legacy_review_sha256': LEGACY_REVIEW_SHA, 'live_before': current,
               'normal_kernel_reexecution_permitted': False, 'whole_P1_4_complete': False}
    if args.check:
        need(not args.worker, '--worker cannot be used with the read-only check')
        print(json.dumps({'status': 'READ_ONLY_LEGACY_IDENTITY_CHECK_PASS_NOT_ACCEPTANCE',
                          **binding, 'existing_execution_present': (ROOT / 'run').exists()}), flush=True)
        return 0
    run = ROOT / 'run'
    if not args.worker:
        need(not run.exists(), 'existing audit execution is held for receipt review; repetition is forbidden')
        before_git = d.original_git_state(REPO)
        d.save(ROOT / 'BINDING.json', binding)
        d.write_frozen(ROOT / 'inputs/MANIFEST.json', manifest_raw)
        d.write_frozen(ROOT / 'inputs/OwnedOnlyAudit.lean', original['audit_bytes'])
        executed = ROOT / 'executed-driver.py'
        d.write_frozen(executed, driver)
        run.mkdir()  # Exclusive reservation: no second process can replay this audit.
        d.save(run / 'GIT_BEFORE.json', before_git)
        child = ['python3', '-B', str(executed), '--source-commit', source, '--run', '--worker']
        try:
            return subprocess.run(h.serialize(0, run / 'VALIDATION_LANE.json', child)).returncode
        finally:
            after_git = d.original_git_state(REPO)
            d.save(run / 'GIT_AFTER.json', after_git)
            need(after_git == before_git, 'original repository checkout changed')
    d.verify_lane(h)
    lane = json.loads((run / 'VALIDATION_LANE.json').read_bytes())
    need(lane['status'] == 'VALIDATION_LANE_ACQUIRED' and lane['state'] == STATE,
         'original lane 0 serializer receipt differs')
    need(json.loads((ROOT / 'BINDING.json').read_bytes()) == binding and
         (ROOT / 'inputs/MANIFEST.json').read_bytes() == manifest_raw and
         (ROOT / 'inputs/OwnedOnlyAudit.lean').read_bytes() == original['audit_bytes'],
         'frozen supplement inputs changed while acquiring lane')
    d.save(run / 'LIVE_BEFORE.json', current)
    for kind in ('normal', 'kernel'):
        for suffix in ('-command.json', '.log'):
            name = SHORT + '-' + kind + suffix
            d.write_frozen(ROOT / 'inputs/legacy' / name, original['raw'][LEGACY_PREFIX + name])
    state = json.loads(Path(STATE).read_bytes())
    journal = Path(state['log'])
    journal_before = journal.stat()
    audit_path = ROOT / 'inputs/OwnedOnlyAudit.lean'
    input_args = ['-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000',
                  '--root=' + str(audit_path.parent), str(audit_path)]
    try:
        command = d.record_command(PROJECT, run, 'audit', h.guard(0, ['lake', 'env', 'lean'] + input_args))
    finally:
        after = live_binding(h, d, review, original)
        d.save(run / 'LIVE_AFTER.json', after)
        need(after == current, 'live source/outputs/runtime/protected roots changed across audit')
    journal_after = journal.stat()
    need(journal_after.st_ino == journal_before.st_ino and journal_after.st_size >= journal_before.st_size,
         'guard journal rotated or shrank during audit')
    with journal.open('rb') as stream:
        stream.seek(journal_before.st_size)
        tail = stream.read(journal_after.st_size - journal_before.st_size)
    d.write_frozen(run / 'ACTUAL_GUARD_JOURNAL_TAIL.jsonl', tail)
    events = [json.loads(line) for line in tail.splitlines()]
    need(len(events) == 1, 'the serialized audit must produce exactly one actual guard event')
    event = events[0]
    need(event['tool'] == 'lean' and event['cwd'] == str(PROJECT) and event['input_args'] == input_args and
         event['command'] == [LEAN_RUNTIME] + RESOURCES + input_args[2:] and
         event['sysroot'] == str(Path(LEAN_RUNTIME).parent.parent), 'actual guarded audit invocation differs')
    d.save(run / 'ACTUAL_AUDIT_RUNTIME.json', {
        'state': STATE, 'state_sha256': d.fingerprint(STATE)['sha256'], 'journal': str(journal),
        'before_byte_offset': journal_before.st_size, 'after_byte_offset': journal_after.st_size,
        'captured_tail_sha256': sha(tail), 'actual_runtime': event})
    need(command['exit_code'] == 0 and not command['actual_built_modules'],
         'owned-only audit failed or unexpectedly built a project module')
    records = read_owned((run / 'audit.log').read_text(), original['public'])
    d.save(run / 'OWNED_EXPORTS.json', records)
    d.save(run / 'PUBLIC_EXPORTS.json', [row for row in records if not row['is_private']])
    result = {
        'schema': 'p14_signed_complete_owned_supplement_result_v1',
        'status': 'PASS_LEGACY_NORMAL_KERNEL_PLUS_COMPLETE_OWNED_SUPPLEMENT',
        'source_commit': source, 'module': MODULE, 'source_sha256': current['source_plus_five'][SOURCE]['sha256'],
        'legacy_evidence_commit': LEGACY_COMMIT, 'legacy_primary_commands': original['commands'],
        'legacy_primary_evidence': manifest['frozen_primary_evidence'],
        'new_normal_invocations': 0, 'new_kernel_invocations': 0, 'new_full_owned_audit_invocations': 1,
        'owned_total': len(records), 'public_total': sum(not row['is_private'] for row in records),
        'private_total': sum(row['is_private'] for row in records),
        'full_owned_including_private_generated': True, 'full_types_AST_universes_std3_axioms': True,
        'original_seven_public_AST_universes_axioms_unchanged': True,
        'source_plus_five_exact_original_and_unchanged': True, 'audit_command': command,
        'whole_P1_4_complete': False,
    }
    d.save(run / 'SIGNED_COMPLETE_OWNED_SUPPLEMENT_RESULT.json', result)
    print(json.dumps(result), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
