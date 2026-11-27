"""One original Partition owner; retained Dictionary inputs and readonly replay.

INPUTS remains None until independently reviewed real probe evidence is bound.
The original Dictionary acceptance stays at 040d; this adapter only reads its
immutable receipts and exact forty-module input subset.  It never runs a new
Dictionary acceptance pass.  The original Variation reader remains at f7e.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PACKET = 'docs/p1/20261127/p15-signed-exit-partition'
TARGET = 'ImbalancedChen.P1SignedExitPartition'
NAME = 'P1SignedExitPartition.lean'
LIVE = 'ImbalancedChen/' + NAME
ORIGINAL_COMMIT = '040d46058821746c69c5183b3f6c22792287c4ba'
EVIDENCE_COMMIT = '3c9bc8fbb8dcd8adc9e4f69c53aab7f41b8d5508'
VARIATION_COMMIT = 'f7e9219f4860a819758d52752c5a9309dd14a8c7'
VAR_ADAPTER = 'docs/p1/20261127/p15-mellin-variation/run_variation.py'
VAR_ADAPTER_SHA = '1c132fefea799e8a3a3127defb07785138e3669e1f80beee2f5aa733b1914f50'
SUPPORT = PACKET + '/support/probe_inputs_v1.py'
SUPPORT_SHA = 'e3b4522c78f92c59701f394310d21f28cbc5ebbbfacd8e0707cd67b48c8a01d3'
SUPPORT_BYTES = 19059
ORIGINAL_SHA = 'cb4d4bb096d7de762cb23925af58624736bcfd753251f348b352acc67bdd2ad9'
PARSER_FIXED_SHA = '19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c'
PROJECT_IMPORTS = ['ImbalancedChen.FirstExitHistoricalLevels']
IMPORTS = PROJECT_IMPORTS + ['Mathlib.Algebra.BigOperators.Group.Finset.Piecewise']
DECLARATIONS = (
    ('def', 'p1SignedExitStates', False),
    ('def', 'p1SignedExitValue', False),
    ('theorem', 'p1_firstExitCorrection_eq_exitStates_sum', False),
    ('theorem', 'p1_mem_exitStates_rejected', False),
    ('theorem', 'p1_mem_exitStates_parent_retained', False),
    ('theorem', 'p1_mem_exitStates_carrier_decomposition', False),
    ('theorem', 'p1_mem_exitStates_rank_bound', False),
    ('theorem', 'p1_mem_exitStates_sign_mass', False),
    ('theorem', 'p1_firstExitCorrection_depthSplice_sub_eq_frontier_sum', False),
    ('theorem', 'p1_sum_finite_fibres', True),
    ('def', 'p1SignedExitHistoryKey', False),
    ('def', 'p1SignedExitHistoryKeys', False),
    ('theorem', 'p1_firstExitCorrection_eq_rank_history_partition', False),
    ('theorem', 'p1_retainedPolynomial_eq_product_add_rank_history_partition', False),
    ('theorem', 'p1_actualThirdCappedCorrection_eq_rank_history_partition', False),
)
FIRST_FAILURE = {
    'job_id': 'job_26dda8849e2f4038b3a5eb22f333d49b',
    'source_sha256': ORIGINAL_SHA,
    'result_sha256': 'b87a76b34d3df676d1f65817582711ab83c5e3e6903bdd77abfb9c7d61f55554',
    'log_sha256': 'f5faaf911b3ac6c4ab71bee14c836b9058a9e37096a66e527cf648f562f0acbd',
    'driver_sha256': SUPPORT_SHA,
}
INPUTS = None


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': digest(raw)}


def regular(path):
    need(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return path.read_bytes()


def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def validate_inputs():
    # This must precede every Git, filesystem, helper or compiler operation.
    need(isinstance(INPUTS, dict), 'UNBOUND: actual successful exact-source probe is required')
    need(re.fullmatch('[0-9a-f]{64}', INPUTS.get('source_sha256', '')) is not None and
         type(INPUTS.get('source_bytes')) is int and INPUTS['source_bytes'] > 0 and
         isinstance(INPUTS.get('probe'), dict) and isinstance(INPUTS.get('failed_probes'), list) and
         INPUTS['failed_probes'], 'incomplete real source/probe/failure bindings')
    for index, row in enumerate([*INPUTS['failed_probes'], INPUTS['probe']]):
        need(isinstance(row, dict) and re.fullmatch('job_[0-9a-f]{32}', row.get('job_id', '')) and
             isinstance(row.get('directory'), str) and
             type(row.get('result_bytes')) is int and row['result_bytes'] > 0 and
             type(row.get('source_bytes')) is int and row['source_bytes'] > 0 and
             all(isinstance(row.get(k), str) and re.fullmatch('[0-9a-f]{64}', row[k])
                 for k in ('source_sha256', 'result_sha256', 'driver_sha256', 'log_sha256')),
             'incomplete actual probe row: ' + str(index))
    first = INPUTS['failed_probes'][0]
    need(all(first.get(k) == value for k, value in FIRST_FAILURE.items()),
         'original actual failed cb4 probe must remain first and immutable')
    need(INPUTS['probe']['source_sha256'] == INPUTS['source_sha256'] and
         INPUTS['probe']['source_bytes'] == INPUTS['source_bytes'], 'successful probe source identity differs')
    publications = [row.get('publication') for row in INPUTS['failed_probes']]
    need(len(set(publications)) == len(publications) and
         all(isinstance(p, str) and re.fullmatch('failed-v[1-9][0-9]*', p) for p in publications),
         'failed probe publication directories must be distinct and fixed')


def proof_mask(source):
    """Preserve complete statements, equation definitions and every non-proof byte.

    These frozen theorems use ':= by'; their bodies are indented.  Some theorem
    statements themselves contain 'let states :=', so first-':=' splitting is
    explicitly unsuitable.  The recursive equation definition has no ':=' at
    its start and is preserved in full.
    """
    text = source.decode('utf-8')
    matches = list(re.finditer(r'^(private )?(def|theorem) (\w+)\b', text, re.MULTILINE))
    census = tuple((m.group(2), m.group(3), bool(m.group(1))) for m in matches)
    need(census == DECLARATIONS, 'original declaration kinds/names/order/visibility differ')
    spans = []
    for index, match in enumerate(matches):
        if match.group(2) != 'theorem':
            continue
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        marker = re.search(r':=\s*by\b', text[match.end():end])
        need(marker is not None, 'original theorem proof delimiter differs: ' + match.group(3))
        start = match.end() + marker.end()
        # The next column-zero command/doc-comment closes this indented proof.
        following = re.search(r'(?m)^[^\s]', text[start:end])
        stop = start + following.start() if following else end
        spans.append((start, stop))
    for start, stop in reversed(spans):
        text = text[:start] + '\n<ORIGINAL_THEOREM_PROOF_BODY>\n\n' + text[stop:]
    return text


def verify_repair(old, parser_fixed, new):
    need(len(old) == 15982 and digest(old) == ORIGINAL_SHA, 'original source differs')
    before = b'        else [{selectedPrefix := p :: pre, positive := !positive,\n          mass := mass * h p, remaining := ps}]'
    after = b'        else [{selectedPrefix := p :: pre, positive := !positive, mass := mass * h p, remaining := ps}]'
    need(old.count(before) == 1 and parser_fixed == old.replace(before, after, 1) and
         len(parser_fixed) == 15972 and digest(parser_fixed) == PARSER_FIXED_SHA,
         'only the original reviewed record-literal layout repair is permitted')
    need(fingerprint(new) == {'bytes': INPUTS['source_bytes'], 'sha256': INPUTS['source_sha256']},
         'selected exact source differs')
    need(proof_mask(parser_fixed) == proof_mask(new),
         'complete theorem statement, definition, namespace, comment or other non-proof bytes changed')
    need(re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', new.decode()) is None,
         'forbidden proof escape in selected source')


def probe_file(c, row, publication, rel):
    path = Path(row['directory']) / rel
    raw = regular(path)
    need(raw == git(c.commit, PACKET + '/' + publication + '/' + rel),
         'exact original probe evidence differs: ' + publication + '/' + rel)
    return raw


def command(c, directory, name, expected, allowed, exit_code=0):
    cmd = c.s.api.read_json(directory / (name + '-command.json'))
    log = directory / (name + '.log')
    need(cmd['argv'] == expected and cmd['cwd'] == str(PROJECT) and cmd['exit_code'] == exit_code and
         cmd['actual_failed_modules'] == [] and set(cmd['actual_built_modules']) <= allowed and
         cmd['log'] == str(log) and fingerprint(regular(log)) ==
             {'bytes': cmd['log_bytes'], 'sha256': cmd['log_sha256']},
         'original command provenance differs: ' + name)
    return cmd


def probe_record(c, row, publication, successful):
    run = Path(row['directory'])
    need(run.is_absolute() and run.resolve() == run and run.name == 'attempt-00000' and
         run.parent.name == row['source_sha256'] and
         run.parent.parent.parent == Path('/workspace/p1-complete-proof') and
         re.fullmatch('20261127-p15-signed-exit-partition-probe-v[1-9][0-9]*', run.parent.parent.name),
         'unexpected original probe directory')
    core = ('PROBE_RESULT.json', NAME, 'probe_driver.py', 'probe-command.json', 'probe.log',
            'serialized-probe-command.json', 'serialized-probe.log', 'LANE.json',
            'PRESERVED_BEFORE.json', 'PRESERVED_AFTER.json', 'GIT_BEFORE.json', 'GIT_AFTER.json',
            TARGET + '/direct-import-stock-readiness-command.json',
            TARGET + '/direct-import-stock-readiness.log')
    raw = {rel: probe_file(c, row, publication, rel) for rel in core}
    result = json.loads(raw['PROBE_RESULT.json'])
    need(fingerprint(raw['PROBE_RESULT.json']) ==
             {'bytes': row['result_bytes'], 'sha256': row['result_sha256']} and
         fingerprint(raw[NAME]) == {'bytes': row['source_bytes'], 'sha256': row['source_sha256']} and
         digest(raw['probe_driver.py']) == row['driver_sha256'] and
         digest(raw['probe.log']) == row['log_sha256'], 'probe source/driver/result/log pin differs')
    need(result['schema'] == 'p15_signed_exit_partition_no_output_probe_v1' and
         result['target'] == TARGET and result['source_base'] == ORIGINAL_COMMIT and
         result['source_path'] == LIVE and result['source_sha256'] == row['source_sha256'] and
         result['source_bytes'] == row['source_bytes'] and
         type(result['exit_code']) is int and
         (result['exit_code'] == 0 if successful else result['exit_code'] != 0) and
         result['probe_passed'] is successful and result['preservation_passed'] is True and
         result['output_object_requested'] is False and result['new_owner_accepted'] is False and
         result['new_formal_credit'] == 0 and result['whole_P1_5_complete'] is False and
         result['direct_imports'] == IMPORTS and result['project_dependency_count'] == 40 and
         result['dependency_artifact_positions'] == 840 and
         result['protected_dictionary_sources'] == 289 and
         result['protected_dictionary_dependency_artifact_positions'] == 6048 and
         result['dictionary_reference'] == c.x.retained.reference and
         result['variation_original_acceptance'] == c.x.variation,
         'probe scope, original dependency identities or terminal result differs')
    expected = c.s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(run / NAME)])
    probe = command(c, run, 'probe', expected, set(), result['exit_code'])
    need(result['command'] == probe, 'probe result and raw original command disagree')
    direct = command(c, run / TARGET, 'direct-import-stock-readiness',
        c.s.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in IMPORTS]), set())
    need(result['direct_import_readiness'] == direct, 'probe original direct-import command differs')
    before, after = json.loads(raw['PRESERVED_BEFORE.json']), json.loads(raw['PRESERVED_AFTER.json'])
    need(before == after and raw['GIT_BEFORE.json'] == raw['GIT_AFTER.json'] and
         before['actual_dependency_context'] == c.g.snapshot(c.s, c.x.spec) and
         before['dictionary_acceptance_reference'] == c.x.retained.reference and
         before['variation'] == c.x.v.accepted(c.x.c) and
         before['native_direct_import']['required_existing_inputs'] ==
             c.support.native_input(c.x)['required_existing_inputs'],
         'probe input/preservation chain differs')
    worker = ['python3', '-B', str(run / 'probe_driver.py'), '--worker']
    outer_argv = c.s.h.serialize(0, run / 'LANE.json', worker)
    command(c, run, 'serialized-probe', outer_argv, set(), result['exit_code'])
    lane = json.loads(raw['LANE.json'])
    state = outer_argv[outer_argv.index('--state') + 1]
    need(lane['status'] == 'VALIDATION_LANE_FINISHED' and lane['exit_code'] == result['exit_code'] and
         lane['argv'] == worker and lane['state'] == state and
         lane['state_sha256'] == digest(regular(Path(state))) and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True,
         'probe outer serializer/lane is incomplete or misbound')
    need(all(not list(run.glob(pattern)) for pattern in
             ('*.olean*', '*.ilean*', '*.trace*', '*.c', '*.ir', '*.o', '*.bc')),
         'no-output probe contains an output object')
    return result


def verified_probe(c):
    prior_rows = INPUTS['failed_probes']
    previous = None
    directories = set()
    for row in prior_rows:
        result = probe_record(c, row, row['publication'], False)
        need(result['previous_failure'] == previous, 'failed probe chronological predecessor differs')
        previous = {'task_id': row['job_id'], 'source_sha256': row['source_sha256'],
                    'result_sha256': row['result_sha256'], 'log_sha256': row['log_sha256']}
        directories.add(row['directory'])
    current = INPUTS['probe']
    result = probe_record(c, current, 'probe', True)
    need(result['previous_failure'] == previous and
         regular(Path(current['directory']) / NAME) == c.new,
         'successful exact-source probe or retained failure predecessor differs')
    directories.add(current['directory'])
    observed = set()
    for root in Path('/workspace/p1-complete-proof').glob('20261127-p15-signed-exit-partition-probe-v*'):
        need(root.is_dir() and root.resolve() == root, 'unexpected probe history root')
        for source in root.iterdir():
            need(source.is_dir() and re.fullmatch('[0-9a-f]{64}', source.name) and source.resolve() == source,
                 'unexpected probe source history')
            for attempt in source.iterdir():
                need(attempt.is_dir() and re.fullmatch('attempt-[0-9]{5}', attempt.name) and attempt.resolve() == attempt,
                     'unexpected probe attempt history')
                observed.add(str(attempt))
    need(observed == directories, 'prior or partial source probe omitted; preserve and inspect')
    return {'job_id': current['job_id'], 'directory': current['directory'],
            'result_sha256': current['result_sha256'], 'driver_sha256': current['driver_sha256'],
            'source_sha256': current['source_sha256'], 'failed_probe_count': len(prior_rows),
            'outer_probe_completion_verified': True, 'formal_credit_from_probe': 0}


def load(commit):
    validate_inputs()
    need(isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit) and
         commit not in (ORIGINAL_COMMIT, VARIATION_COMMIT, EVIDENCE_COMMIT), 'new source publication required')
    runner = git(commit, PACKET + '/run_partition.py')
    need(runner == regular(Path(__file__)), 'executed adapter differs from exact publication')
    support_raw = git(commit, SUPPORT)
    need(fingerprint(support_raw) == {'bytes': SUPPORT_BYTES, 'sha256': SUPPORT_SHA}, 'frozen probe input helper differs')
    support = ModuleType('frozen_partition_probe_inputs')
    support.__file__ = SUPPORT
    exec(compile(support_raw, SUPPORT, 'exec'), support.__dict__)
    need((support.REPO, support.PROJECT, support.ACCEPTANCE_ROOT, support.TARGET) ==
         (REPO, PROJECT, ROOT, TARGET), 'probe helper fixed roots/target differ')
    raw = git(VARIATION_COMMIT, VAR_ADAPTER)
    need(digest(raw) == VAR_ADAPTER_SHA, 'original Variation adapter differs')
    v = ModuleType('original_variation_reader')
    v.__file__ = str(ROOT / VARIATION_COMMIT / 'published-entrypoints/run_variation.py')
    exec(compile(raw, VAR_ADAPTER, 'exec'), v.__dict__)
    vc = v.load(VARIATION_COMMIT)
    variation = v.check(vc)
    need(variation['status'] == 'REVALIDATED', 'original Variation acceptance is unavailable')
    retained = support.dictionary_reference(v, vc)
    dep_spec = support.dependency_spec(vc, retained)
    old = git(ORIGINAL_COMMIT, LIVE)
    parser_fixed = git(commit, PACKET + '/parser-fixed-baseline.lean')
    new = git(commit, PACKET + '/' + NAME)
    verify_repair(old, parser_fixed, new)
    need(git(commit, LIVE) == new and git(commit, PACKET + '/original-source.lean') == old and
         vc.s.h.imports(new) == IMPORTS, 'canonical/original source or complete import list differs')
    x = SimpleNamespace(v=v, c=vc, retained=retained, spec=dep_spec, variation=variation)
    graph = {**dep_spec.graph, TARGET: list(PROJECT_IMPORTS)}
    sources = {**dep_spec.sources, TARGET: INPUTS['source_sha256']}
    need(len(graph) == len(sources) == 41 and vc.s.h.closure(graph, [TARGET]) == set(graph),
         'formal owner graph is not exactly forty old dependencies plus Partition')
    spec = SimpleNamespace(graph=graph, sources=sources,
        manifest={'project_sources': {TARGET: {'all_imports': list(IMPORTS)}}})
    base = ROOT / commit
    c = SimpleNamespace(support=support, x=x, g=vc.g, s=vc.s, spec=spec,
        old=old, new=new, parser_fixed=parser_fixed, runner=runner, base=base,
        run=base / 'signed-exit-partition-operation', commit=commit)
    c.ident = {'commit': commit, 'module': TARGET,
        'original_source_commit': ORIGINAL_COMMIT, 'original_source_sha256': ORIGINAL_SHA,
        'parser_fixed_baseline_sha256': PARSER_FIXED_SHA, 'new_source_sha256': INPUTS['source_sha256'],
        'dictionary_original_reference': retained.reference, 'variation_original_acceptance': variation,
        'actual_project_dependencies': 40, 'formal_graph_sources': 41,
        'probe': verified_probe(c), 'adapter_sha256': digest(runner), 'probe_helper_sha256': SUPPORT_SHA,
        'publication': PACKET + '/' + NAME, 'whole_P1_5_complete': False}
    return c


def fixed(c):
    """Same old-input protection as the probe, intentionally excluding its target_state."""
    x = c.x
    need(c.g.file_binding(PROJECT / c.s.h.module_path(c.support.DICTIONARY)) ==
         x.retained.documents['normal_context']['project_sources'][c.support.DICTIONARY] and
         c.g.module_artifacts(c.s, c.support.DICTIONARY) == x.retained.owner['all_observed_target_artifacts'],
         'original Dictionary source/artifacts differ')
    need(x.v.check(x.c) == x.variation, 'original Variation readonly identity changed')
    return {'actual_dependency_context': c.g.snapshot(c.s, x.spec),
        'dictionary_all_source_and_artifact_metadata': c.support.full_dictionary_metadata(x),
        'dictionary_acceptance_reference': x.retained.reference,
        'variation': x.v.accepted(x.c), 'existing_owners': x.v.fixed(x.c),
        'native_direct_import': c.support.native_input(x)}


def owner_roots(c):
    return sorted(p / TARGET for p in ROOT.iterdir() if p.is_dir() and
                  re.fullmatch('[0-9a-f]{40}', p.name) and os.path.lexists(p / TARGET))


def fresh(c):
    need(not owner_roots(c), 'prior/partial owner found; preserve and inspect without rerun')
    c.g.require_fresh_owner(TARGET, c.g.module_artifacts(c.s, TARGET))
    stem = PROJECT / '.lake/build/lib/lean' / TARGET.replace('.', '/')
    need(all(not os.path.lexists(Path(str(stem) + ext)) for ext in ('.trace.nobuild', '.ir.sig.hash')),
         'partial extra target artifact found')
    path = PROJECT / LIVE
    state = regular(path) if os.path.lexists(path) else None
    need(state in (None, c.old), 'foreign or unpublished target installation requires inspection')
    return state


def accepted(c):
    need(owner_roots(c) == [c.base / TARGET], 'owner missing or competing prior owner exists')
    existing = c.g.existing_owner(c.s, c.commit, c.spec, TARGET)
    c.g.require_completed_existing_owner(c.s, c.commit, c.spec, TARGET, existing)
    folders = list((c.base / TARGET / 'audits').iterdir())
    need(len(folders) == 1, 'expected one immutable complete-owned audit')
    result = c.s.api.read_json(folders[0] / 'lane-0/VALIDATION_RESULTS.json')
    records = c.s.api.read_json(folders[0] / 'lane-0/OWNED_EXPORTS.json')
    need(result['only_standard_axioms'] is True and result['full_owned_including_private_generated'] is True and
         result['total_owned_exports'] == len(records) and
         result['total_public_exports'] == sum(not row['is_private'] for row in records),
         'incomplete owned/private audit or nonstandard axioms')
    public = {row['name'] for row in records if not row['is_private']}
    need(all('ImbalancedChen.' + name in public for _, name, private in DECLARATIONS if not private),
         'original public declaration missing from actual owned audit')
    return {'owned': result['total_owned_exports'], 'public': result['total_public_exports'],
        'axioms': sorted({axiom for row in records for axiom in row['axioms']}),
        'binding': c.g.acceptance_binding(c.s, c.commit, TARGET)}


def install(c, prior):
    path = PROJECT / LIVE
    need(path.parent.resolve() == path.parent, 'unexpected source-parent symlink')
    c.s.d.write_frozen(c.run / 'original-published.lean', c.old)
    if prior is not None:
        c.s.d.write_frozen(c.run / 'original-installed.lean', prior)
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.signed-exit-install-', delete=False) as stream:
        temporary = Path(stream.name)
        try:
            os.fchmod(stream.fileno(), 0o644 if prior is None else path.stat().st_mode & 0o777)
            stream.write(c.new)
            stream.flush()
            os.fsync(stream.fileno())
            if prior is None:
                os.link(temporary, path)
            else:
                need(regular(path) == prior, 'live original changed before source replacement')
                os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)
    need(regular(path) == c.new, 'installed source differs')
    descriptor = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    c.s.d.save(c.run / 'INSTALL.json', {'identity': c.ident, 'original_present': prior is not None})


def worker(c):
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__) == c.run / 'executed.py' and c.run.resolve() == c.run, 'unexpected formal worker path')
    need(c.s.api.read_json(c.run / 'GIT_BEFORE.json') == c.s.d.original_git_state(REPO), 'checkout changed before worker')
    before = fixed(c)
    c.s.d.save(c.run / 'PRESERVED_BEFORE.json', before)
    try:
        prior = fresh(c)
        direct = c.g.direct_import_readiness(c.s, c.spec, TARGET, c.run)
        need(fixed(c) == before and fresh(c) == prior, 'no-build preflight changed existing inputs')
        install(c, prior)
        c.g.run_owner(c.s, c.commit, c.base, c.run, TARGET, c.spec.graph, c.spec.sources)
        owner = accepted(c)
    finally:
        after = fixed(c)
        c.s.d.save(c.run / 'PRESERVED_AFTER.json', after)
        need(before == after, 'formal operation changed original dependencies or acceptance')
    c.s.d.save(c.run / 'WORKER_PASS.json', {'identity': c.ident, 'owner': owner, 'native_stock': direct})


def dispatch(c):
    fresh(c)
    need(c.run.resolve() == c.run, 'unexpected operation symlink')
    c.run.mkdir(parents=True, exist_ok=False)
    c.s.d.write_frozen(c.run / 'executed.py', c.runner)
    before = c.s.d.original_git_state(REPO)
    c.s.d.save(c.run / 'GIT_BEFORE.json', before)
    try:
        outer = c.s.ops.run(c.run, 'serialized-partition', c.s.h.serialize(0, c.run / 'LANE.json',
            ['python3', '-B', str(c.run / 'executed.py'), '--source-commit', c.commit, '--worker']),
            cwd=PROJECT, relay=True)
        need(outer['exit_code'] == 0 and outer['actual_failed_modules'] == [] and
             set(outer['actual_built_modules']) <= {TARGET}, 'formal serialized scope/status differs')
        passed = c.s.api.read_json(c.run / 'WORKER_PASS.json')
        need(passed['identity'] == c.ident and passed['owner'] == accepted(c), 'incomplete original worker evidence')
    finally:
        after = c.s.d.original_git_state(REPO)
        c.s.d.save(c.run / 'GIT_AFTER.json', after)
        need(before == after, 'original dirty checkout Git state changed')
    c.s.d.save(c.run / 'PASS.json', {'identity': c.ident,
        'worker': c.s.d.fingerprint(c.run / 'WORKER_PASS.json'), 'command': outer,
        'preserved': c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json')})


def check(c):
    need(c.run.resolve() == c.run, 'unexpected operation symlink')
    if not os.path.lexists(c.run):
        prior = fresh(c)
        fixed(c)
        return {'status': 'FRESH', 'identity': c.ident, 'old_source_present': prior is not None,
                'normal_or_kernel_commands_executed': 0}
    read = c.s.api.read_json
    need((c.run / 'PASS.json').is_file(), 'partial/failed formal operation; preserve and inspect')
    passed = read(c.run / 'PASS.json')
    installed = read(c.run / 'INSTALL.json')
    need(regular(c.run / 'executed.py') == c.runner and regular(c.run / 'original-published.lean') == c.old and
         passed['identity'] == c.ident and installed['identity'] == c.ident and
         isinstance(installed['original_present'], bool) and
         passed['worker'] == c.s.d.fingerprint(c.run / 'WORKER_PASS.json'), 'formal provenance differs')
    backup = c.run / 'original-installed.lean'
    need(regular(backup) == c.old if installed['original_present'] else not os.path.lexists(backup), 'original source backup differs')
    worker_result = read(c.run / 'WORKER_PASS.json')
    need(worker_result['identity'] == c.ident and worker_result['owner'] == accepted(c), 'original owned acceptance differs')
    need(read(c.run / 'GIT_BEFORE.json') == read(c.run / 'GIT_AFTER.json') and
         passed['preserved'] == c.s.d.fingerprint(c.run / 'PRESERVED_BEFORE.json') ==
         c.s.d.fingerprint(c.run / 'PRESERVED_AFTER.json'), 'operation before/after preservation differs')
    recorded, current = read(c.run / 'PRESERVED_BEFORE.json'), fixed(c)
    need(all(recorded[k] == current[k] for k in
             ('actual_dependency_context', 'dictionary_acceptance_reference', 'variation')) and
         recorded['native_direct_import']['required_existing_inputs'] ==
             current['native_direct_import']['required_existing_inputs'] and
         recorded['existing_owners']['environment'] == current['existing_owners']['environment'],
         'original actual dependency content, native inputs or runtime changed')
    # Other owners may subsequently be accepted. Broad metadata is checked at
    # this operation's boundaries, never retroactively treated as a new proof.
    outer = command(c, c.run, 'serialized-partition',
        c.s.h.serialize(0, c.run / 'LANE.json',
            ['python3', '-B', str(c.run / 'executed.py'), '--source-commit', c.commit, '--worker']), {TARGET})
    direct = command(c, c.run / TARGET, 'direct-import-stock-readiness',
        c.s.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in IMPORTS]), set())
    need(outer == passed['command'] and direct == worker_result['native_stock'], 'original dispatcher or stock command differs')
    lane = read(c.run / 'LANE.json')
    state = outer['argv'][outer['argv'].index('--state') + 1]
    need(lane['status'] == 'VALIDATION_LANE_FINISHED' and lane['exit_code'] == 0 and
         lane['argv'] == ['python3', '-B', str(c.run / 'executed.py'), '--source-commit', c.commit, '--worker'] and
         lane['state'] == state and lane['state_sha256'] == digest(regular(Path(state))) and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True,
         'formal outer serializer/lane is incomplete or misbound')
    return {'status': 'REVALIDATED', 'identity': c.ident,
            'owner': {k: value for k, value in worker_result['owner'].items() if k != 'binding'},
            'normal_or_kernel_commands_executed': 0, 'whole_P1_5_complete': False}


def main():
    validate_inputs()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ('run', 'check', 'worker'):
        mode.add_argument('--' + name, action='store_true')
    args = parser.parse_args()
    c = load(args.source_commit)
    if args.worker:
        worker(c)
    else:
        if args.run:
            dispatch(c)
        print(json.dumps(check(c), sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
