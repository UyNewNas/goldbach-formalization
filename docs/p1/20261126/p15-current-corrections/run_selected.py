#!/usr/bin/env python3
"""Run an explicit subset of 21 current P1 owners through the unchanged acceptance API.

Published Git binds all 360 sources; live checks cover only the selected closure.
Original accepted suppliers keep their own source commits, receipts and artifacts.
This driver never installs sources, imports cache files or rebuilds a supplier.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
RUNNER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
OBSERVATIONS = 'docs/p1/20261126/p15-current-corrections/FIXED_DEPENDENCY_OBSERVATIONS.json'
SOURCE_ANCHOR = '1576fac11ccf44b4fc6e652fc76e8c2f71655f58'
API = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
MODULE = re.compile(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9']*)+")
SHA256 = re.compile(r'[0-9a-f]{64}')
MANIFEST_SHA = '198861fae512aa5213a1e779bac287b5bc5551991f4e7508e4d51fe819755d73'
OBSERVATIONS_SHA = '54fe15ebb2f2468246ffa196bc9874faeb9f624ac66da451ae2616c862ff5895'
TARGETS = ['ImbalancedChen.P1OriginalSingletonProperPower', 'ImbalancedChen.P1OriginalHistoricalProperPower', 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary', 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy', 'ImbalancedChen.P1OriginalSingletonSmoothLicence', 'ImbalancedChen.P1OriginalSingletonAtlasProperPower', 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid', 'ImbalancedChen.P1OriginalSingletonAtlasTrim', 'ImbalancedChen.P1OriginalSingletonSupportData', 'ImbalancedChen.P1OriginalSingletonCutoffData', 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches', 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime', 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses', 'ImbalancedChen.P5LicensedOriginalIntegerProfile', 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward', 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily', 'ImbalancedChen.Part3AllKLambdaChartCorrection', 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound', 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment', 'ImbalancedChen.P5OriginalSharpPrimeSynthesis', 'ImbalancedChen.P5PrimeDivisorMeanCorrection']
SUPPLIER_IDENTITIES = {'initial4': ('d20acdf13882e17d97833064f5e7c54f3192b03c', 316, '/workspace/p1-complete-proof/20261125-p15-singleton-proper-power-v1'), 'atlas10': ('418ad4b9a5f2d992871062258a2eefd7fdf4b9ee', 68, '/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1/atlas10'), 'core': ('ef450be0a89b6a3f88b3bca19d06e04e7967fa18', 168, '/workspace/p1-complete-proof/20261125-p15-original-atlas-proper-power-v1'), 'mellin': ('21789da92213323d645122cfcc7dff9c10dc82d6', 168, '/workspace/p1-complete-proof/20261125-p15-original-atlas-proper-power-v1'), 'brun': ('418ad4b9a5f2d992871062258a2eefd7fdf4b9ee', 77, '/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1/p3-20')}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def pinned(commit, path, digest):
    raw = git_file(commit, path)
    require(hashlib.sha256(raw).hexdigest() == digest, 'published pin differs: ' + path)
    return raw


def helpers():
    raw = pinned(API_COMMIT, API, API_SHA)
    api = ModuleType('published_batch13')
    api.__file__ = API
    exec(compile(raw, API, 'exec'), api.__dict__)
    require((api.REPO, api.PROJECT, api.TOOLS) == (REPO, PROJECT, TOOLS), 'unexpected helper environment')
    code = {p: pinned(TOOLS, p, sha) for p, sha in api.PINS.items()}
    return SimpleNamespace(api=api, h=api.load(code[api.HELPER], 'batch5'),
                           ops=api.load(code[api.OPS], 'batch6'),
                           d=api.load(code[api.PRIMITIVES], 'primitives'), e9=code[api.E9])


def file_binding(path):
    require(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular_fingerprint(s, path):
    require(path.is_file() and not path.is_symlink(),
            'expected existing regular cache file; adoption is separate: ' + str(path))
    return s.d.fingerprint(path)


def run_owner(s, commit, base, run, m, graph, sources):
    folder = base / m
    s.d.write_frozen(folder / 'inputs/e9.py', s.e9)
    # A different Git commit can have the identical proof/dependency context.
    # Hold its retained computation for inspection; the pinned API still owns
    # receipt validation, and this wrapper never rebases an acceptance receipt.
    previous = [p / m for p in ROOT.iterdir()
                if p.is_dir() and p.name != commit and re.fullmatch('[0-9a-f]{40}', p.name)
                and (p / m).is_dir()]
    normal_dir = folder / 'normal' / m
    if not os.path.lexists(normal_dir / 'NORMAL_PASS.json') and any(normal_dir.glob('attempt-*/normal-started.json')):
        previous.append(folder)
    if previous:
        current = s.api.context(commit, PROJECT, m, graph, sources, s.h, s.d)
        current = {k: v for k, v in current.items() if k != 'source_commit'}
        for old in previous:
            normal = old / 'normal' / m
            bindings = []
            receipt = normal / 'NORMAL_PASS.json'
            if receipt.is_file():
                bindings.append((receipt, json.loads(receipt.read_bytes())['dependency_context']))
            for started in normal.glob('attempt-*/normal-started.json'):
                context = started.parent / 'CONTEXT_BEFORE.json'
                require(context.is_file(), 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(started))
                bindings.append((started, json.loads(context.read_bytes())))
            for path, binding in bindings:
                identity = {k: v for k, v in binding.items() if k != 'source_commit'}
                require(identity.keys() == current.keys() and binding.get('source_commit') == old.parent.name,
                        'RETAINED_HISTORY_REQUIRES_INSPECTION: incomplete or misbound context in ' + str(path))
                require(identity != current, 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(path))
            require(bindings or (not any((old / 'plans').glob('*.json')) and
                                 not any((old / 'audits').glob('*'))),
                    'RETAINED_HISTORY_REQUIRES_INSPECTION: missing normal context in ' + str(old))
    # Preserve a partial audit even if its normal later becomes unavailable.
    for plan in (folder / 'plans').glob('*.json'):
        require((folder / 'audits' / plan.stem / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(plan))
    for directory in (folder / 'audits').glob('*'):
        require((directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(directory))
    passed = s.api.normal_one(commit, PROJECT, folder, m, graph, sources, s.h, s.ops, s.d)
    accepted = set()
    s.api.audit(commit, PROJECT, folder, {m: passed}, graph, sources, s.h, s.ops,
                s.d, run / m, accepted)
    require(accepted == {m}, 'owner missing from validated audit receipt')


def artifact_paths(module):
    require(MODULE.fullmatch(module), 'invalid module name')
    relative = module.replace('.', '/')
    lib = '.lake/build/lib/lean/' + relative
    ir = '.lake/build/ir/' + relative
    return [lib + ext for ext in ('.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
                                  '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash',
                                  '.trace', '.ir', '.ir.hash', '.ir.sig')] + [
        ir + ext for ext in ('.c', '.c.hash', '.setup.json', '.bc', '.bc.hash', '.o', '.o.hash',
                            '.o.export', '.o.export.hash')]


def module_artifacts(s, module):
    result = {}
    for relative in artifact_paths(module):
        path = PROJECT / relative
        if os.path.lexists(path):
            require(path.is_file() and not path.is_symlink(), 'unexpected artifact entry: ' + relative)
            result[relative] = s.d.fingerprint(path)
        else:
            result[relative] = None
    return result


def require_fresh_owner(module, artifacts):
    present = [path for path, value in artifacts.items() if value is not None]
    require(not present, 'UNEXPECTED_EXISTING_TARGET_ARTIFACT_REQUIRES_INSPECTION: ' +
            module + ': ' + ', '.join(present))


def existing_owner(s, commit, spec, module):
    folder = ROOT / commit / module
    artifacts = module_artifacts(s, module)
    normal_path = folder / 'normal' / module / 'NORMAL_PASS.json'
    if not os.path.lexists(normal_path):
        require_fresh_owner(module, artifacts)
        return {'status': 'MISSING_WITHOUT_NORMAL_RECEIPT', 'artifacts': artifacts}
    normal = s.api.read_json(normal_path)
    s.api.normal_valid(commit, PROJECT, module, normal,
                       s.api.context(commit, PROJECT, module, spec.graph, spec.sources, s.h, s.d), s.h, s.d)
    return {'status': 'BOUND_CURRENT_NORMAL_RECEIPT', 'artifacts': artifacts, 'normal': normal}


def require_completed_existing_owner(s, commit, spec, module, state):
    require(state['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT',
            'NONSELECTED_TARGET_DEPENDENCY_REQUIRES_OWN_COMPLETE_ACCEPTANCE: ' + module)
    folder = ROOT / commit / module
    for plan in (folder / 'plans').glob('*.json'):
        require((folder / 'audits' / plan.stem / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(plan))
    accepted = set()
    for directory in (folder / 'audits').glob('*'):
        require(directory.is_dir() and not directory.is_symlink() and
                (directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(directory))
        accepted.update(s.api.audit_valid(commit, PROJECT, directory,
            s.api.read_json(directory / 'AUDIT_PLAN.json'), {module: state['normal']},
            spec.graph, spec.sources, s.h, s.d))
    require(accepted == {module}, 'NONSELECTED_TARGET_DEPENDENCY_NOT_ACCEPTED: ' + module)


def acceptance_binding(s, commit, module):
    folder = ROOT / commit / module
    normal = folder / 'normal' / module / 'NORMAL_PASS.json'
    audits = []
    for directory in sorted((folder / 'audits').glob('*')):
        result = directory / 'lane-0/VALIDATION_RESULTS.json'
        plan = directory / 'AUDIT_PLAN.json'
        audits.append({'plan': {'path': str(plan), **regular_fingerprint(s, plan)},
                       'result': {'path': str(result), **regular_fingerprint(s, result)}})
    require(audits, 'missing completed owner audit')
    return {'module': module, 'normal_receipt': {'path': str(normal), **regular_fingerprint(s, normal)},
            'audits': audits, 'source_plus_five_outputs': s.d.snapshot(PROJECT, module),
            'all_observed_target_artifacts': module_artifacts(s, module)}


def direct_import_readiness(s, spec, module, run):
    imports = spec.manifest['project_sources'][module]['all_imports']
    require(imports and all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", dep) for dep in imports),
            'EMPTY_OR_UNKNOWN_DIRECT_IMPORT_SET_REQUIRES_INSPECTION: ' + module)
    command = s.ops.run(run / module, 'direct-import-stock-readiness',
        s.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in imports]), cwd=PROJECT)
    require(command['exit_code'] == 0 and command['actual_built_modules'] == [] and
            command['actual_failed_modules'] == [], 'DIRECT_IMPORTS_NOT_READY_NO_REBUILD_ALLOWED: ' + module)
    return command


def selection(requested):
    require(requested and len(requested) == len(set(requested)), 'explicit unique nonempty --targets required')
    require(set(requested) <= set(TARGETS), 'outside the fixed 21-owner correction whitelist')
    return [module for module in TARGETS if module in requested]


def valid_fingerprint(value):
    return (isinstance(value, dict) and set(value) == {'bytes', 'sha256'} and
            isinstance(value['bytes'], int) and not isinstance(value['bytes'], bool) and value['bytes'] >= 0 and
            isinstance(value['sha256'], str) and SHA256.fullmatch(value['sha256']) is not None)


def published_binding(binding):
    require(set(binding) >= {'commit', 'path', 'bytes', 'sha256'} and
            re.fullmatch('[0-9a-f]{40}', binding['commit']) and
            not Path(binding['path']).is_absolute() and '..' not in Path(binding['path']).parts,
            'invalid published binding')
    raw = pinned(binding['commit'], binding['path'], binding['sha256'])
    require(len(raw) == binding['bytes'], 'published byte count differs: ' + binding['path'])
    return raw


def source_manifest(s, commit, selected):
    selected = selection(selected)
    raw = pinned(commit, MANIFEST, MANIFEST_SHA)
    manifest = json.loads(raw)
    require(manifest['schema'] == 'p15_current_corrections_source_and_reuse_manifest_v1' and
            manifest['project'] == str(PROJECT) and manifest['source_anchor_commit'] == SOURCE_ANCHOR and
            manifest['targets'] == TARGETS and manifest['target_count'] == 21 and
            manifest['project_module_count'] == 360, 'fixed correction source scope differs')
    rows = manifest['project_sources']
    require(len(rows) == 360, 'full published source inventory differs')
    graph, sources = {}, {}
    for module, row in rows.items():
        require(MODULE.fullmatch(module) and row['path'] == s.h.module_path(module) and
                SHA256.fullmatch(row['sha256']) and all(dep in rows for dep in row['imports']),
                'invalid published source row: ' + module)
        payload = git_file(commit, row['path'])
        require(payload == git_file(SOURCE_ANCHOR, row['path']) and
                len(payload) == row['bytes'] and s.api.sha(payload) == row['sha256'] and
                hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest() == row['git_blob'] and
                s.h.imports(payload) == row['all_imports'] and
                [dep for dep in row['all_imports'] if dep.startswith('ImbalancedChen.')] == row['imports'],
                'committed source/import identity differs: ' + module)
        graph[module], sources[module] = row['imports'], row['sha256']
    require(set(graph) == s.h.closure(graph, TARGETS), 'published graph is not the exact 21-root closure')
    supplier, fixed = manifest['accepted_suppliers'], manifest['fixed_dependencies']
    blocked = set(manifest['unaccepted_p3_dependencies'])
    parts = [set(TARGETS), set(supplier), set(fixed), blocked]
    require([len(part) for part in parts] == [21, 17, 303, 19] and
            set.union(*parts) == set(graph) and sum(map(len, parts)) == len(graph),
            'owner/supplier/fixed/unaccepted partition differs')
    groups = manifest['accepted_supplier_groups']
    require(set(groups) == set(SUPPLIER_IDENTITIES), 'supplier group whitelist differs')
    for name, (source_commit, count, root) in SUPPLIER_IDENTITIES.items():
        group = groups[name]
        require((group['source_commit'], group['published_source_count'], group['evidence_root']) ==
                (source_commit, count, root) and group['run'] == 'runs/attempt-00000' and
                set(group['owners']) == {m for m in supplier if supplier[m]['group'] == name},
                'original acceptance identity differs: ' + name)
    require(set(manifest['target_source_origins']) == set(TARGETS), 'per-owner source origins incomplete')
    for module, origin in manifest['target_source_origins'].items():
        require(published_binding(origin['canonical_source']) == git_file(commit, rows[module]['path']),
                'original canonical source provenance differs: ' + module)
        for review in origin['source_reviews']:
            published_binding(review)
    observation = manifest['object_observation_binding']
    require(observation['path'] == OBSERVATIONS and observation['sha256'] == OBSERVATIONS_SHA,
            'fixed object observation binding differs')
    observed_raw = pinned(commit, OBSERVATIONS, OBSERVATIONS_SHA)
    require(len(observed_raw) == observation['bytes'], 'fixed observation byte count differs')
    observed = json.loads(observed_raw)
    require(observed['schema'] == 'p15_current_corrections_retained_object_observations_v1' and
            observed['project'] == str(PROJECT) and len(observed['modules']) == 8 and
            observed['new_cloud_probe_performed'] is False, 'fixed object observation scope differs')
    for module, policy in fixed.items():
        require(policy['required_extensions'] == ['.olean', '.trace'], 'dependency pin scope differs')
        if policy['kind'] == 'retained_accepted_normal_dependency_context':
            witness = policy['witness_owner']
            require(witness in supplier and module in s.h.closure(graph, [witness]) - {witness},
                    'invalid retained normal context witness: ' + module)
        else:
            require(policy['kind'] == 'retained_object_observation' and policy['observation_key'] == module and
                    module in observed['modules'], 'unknown fixed dependency provenance: ' + module)
            record = observed['modules'][module]
            require(record['module'] == module and record['project'] == str(PROJECT) and
                    record['source'] == {'bytes': rows[module]['bytes'], 'sha256': rows[module]['sha256']} and
                    all(valid_fingerprint(record['outputs'].get(ext)) for ext in ('.olean', '.trace')),
                    'recorded fixed object source or pin differs: ' + module)
    active = s.h.closure(graph, selected)
    binding = {'source_commit': commit, 'source_anchor_commit': SOURCE_ANCHOR,
        'manifest': {'path': MANIFEST, 'bytes': len(raw), 'sha256': s.api.sha(raw)},
        'observations': observation, 'full_published_source_count': len(graph),
        'selected_live_source_count': len(active), 'selected_targets': selected,
        'full_published_graph_claimed_equal_to_current_live_graph': False}
    return manifest, graph, sources, observed, binding


def retained_read(s, spec, path, expected=None):
    require(path.is_file() and path.resolve() == path, 'missing/nonregular retained evidence: ' + str(path))
    raw = path.read_bytes()
    fp = {'bytes': len(raw), 'sha256': s.api.sha(raw)}
    if expected is not None:
        require(all(fp.get(k) == v for k, v in expected.items()), 'retained evidence pin differs: ' + str(path))
    require(str(path) not in spec.retained_inputs or spec.retained_inputs[str(path)] == fp,
            'retained evidence changed during reading: ' + str(path))
    spec.retained_inputs[str(path)] = fp
    return raw


def historical_group(s, spec, name):
    if name in spec.historical_groups:
        return spec.historical_groups[name]
    fixed = spec.manifest['accepted_supplier_groups'][name]
    commit = fixed['source_commit']
    manifest = json.loads(published_binding(fixed['source_graph']))
    rows = manifest['project_sources']
    require(len(rows) == fixed['published_source_count'], 'historical graph count differs')
    graph, sources = {}, {}
    for module, row in rows.items():
        require(MODULE.fullmatch(module) and row['path'] == s.h.module_path(module) and
                all(dep in rows for dep in row['imports']), 'historical graph row differs')
        raw = git_file(commit, row['path'])
        require(s.api.sha(raw) == row['sha256'] and
                [dep for dep in s.h.imports(raw) if dep.startswith('ImbalancedChen.')] == row['imports'],
                'historical committed graph/source differs: ' + module)
        graph[module], sources[module] = row['imports'], row['sha256']
    public = json.loads(published_binding(fixed['public_evidence']))
    base = Path(fixed['evidence_root']) / commit
    run = base / fixed['run']
    code = published_binding(fixed['driver'])
    require(retained_read(s, spec, run / 'executed-driver.py') == code,
            'retained executed supplier driver differs')
    if name == 'mellin':
        require(public['source_commit'] == commit and public['platform']['job_id'] == fixed['compiler_job'] and
                public['platform']['exit_code'] == 0 and public['new_acceptance_scope'] == fixed['owners'],
                'fixed Mellin terminal identity differs')
        original = json.loads(retained_read(s, spec, run / 'RESULT.json'))
        require(original == {k: v for k, v in public['result'].items() if k not in ('batch6', 'path')},
                'Mellin retained result differs from published terminal observation')
        audit_rows = [row for row in public['normal_and_audit'] if row.get('name') == 'audit-lane-0']
        require(len(audit_rows) == 1 and audit_rows[0].get('batch6') == 'END' and
                audit_rows[0].get('exit_code') == 0 and audit_rows[0].get('built') == [] and
                audit_rows[0].get('failed') == [], 'Mellin published audit-lane success identity differs')
        retained_read(s, spec, run / fixed['owners'][0] / 'audit-lane-0.log',
                      {'sha256': audit_rows[0]['log_sha256']})
    else:
        require(public['source_commit'] == commit and public['compiler_job'] == fixed['compiler_job'] and
                set(public['owners']) == set(fixed['owners']), 'historical public acceptance scope differs')
        expected = ({'sha256': public['original_result_sha256']} if name == 'initial4'
                    else public['original_result'])
        original = json.loads(retained_read(s, spec, run / 'RESULT.json', expected))
    require(original['source_commit'] == commit and set(fixed['owners']) <= set(original['accepted_owners']) and
            not set(fixed['owners']).intersection(original['failures']) and
            not any(k in original for k in ('context_error', 'final_context_error', 'git_error')),
            'supplier original run does not retain these accepted owners')
    for stem in ('CONTEXT', 'GIT'):
        require(retained_read(s, spec, run / (stem + '_BEFORE.json')) ==
                retained_read(s, spec, run / (stem + '_AFTER.json')),
                'retained supplier compile context changed')
    result = SimpleNamespace(fixed=fixed, commit=commit, base=base, graph=graph, sources=sources,
                             public=public, original=original)
    spec.historical_groups[name] = result
    return result


def retained_owner(s, spec, module, validate_live=False):
    if module not in spec.historical_owners:
        supplier = spec.manifest['accepted_suppliers'][module]
        group = historical_group(s, spec, supplier['group'])
        own_closure = s.h.closure(group.graph, [module])
        require(own_closure == s.h.closure(spec.graph, [module]) and
                all(group.sources[m] == spec.sources[m] for m in own_closure),
                'supplier current source closure differs from its original acceptance: ' + module)
        folder = group.base / module
        expected = None if supplier['group'] == 'mellin' else group.public['owners'][module]['receipt_bindings']['normal']
        path = folder / 'normal' / module / 'NORMAL_PASS.json'
        normal = json.loads(retained_read(s, spec, path, expected))
        binding = normal['dependency_context']
        expected_objects = {'.lake/build/lib/lean/' + m.replace('.', '/') + ext
                            for m in own_closure - {module} for ext in ('.olean', '.trace')}
        require(normal['module'] == module and normal['source_commit'] == group.commit and
                normal['status'] == 'NORMAL_PASS_AUDIT_PENDING' and binding['source_commit'] == group.commit and
                binding['project_sources'] == {m: group.sources[m] for m in sorted(own_closure)} and
                set(binding['dependency_objects_and_traces']) == expected_objects and
                all(valid_fingerprint(v) for v in binding['dependency_objects_and_traces'].values()) and
                binding['configuration'] == spec.review['runtime_configuration_bindings'] and
                binding['existing_runtime'] == spec.review['existing_runtime_bindings'],
                'historical normal context is incomplete or misbound: ' + module)
        if supplier['group'] == 'mellin':
            recorded = [row for row in group.public['normal_and_audit'] if row.get('name') == 'normal']
            require(len(recorded) == 1 and recorded[0]['exit_code'] == 0 and recorded[0]['built'] == [module] and
                    normal['normal_command']['log_sha256'] == recorded[0]['log_sha256'],
                    'Mellin original normal log identity differs')
        spec.historical_owners[module] = SimpleNamespace(group=group, normal=normal, normal_path=path,
            folder=folder, live_validated=False)
    owner = spec.historical_owners[module]
    if validate_live and not owner.live_validated:
        group = owner.group
        require(s.h.closure(group.graph, [module]) <= spec.active, 'supplier validation exceeds selected live closure')
        audits = sorted((owner.folder / 'audits').glob('*'))
        require(len(audits) == 1 and audits[0].is_dir() and not audits[0].is_symlink() and
                re.fullmatch('[0-9a-f]{20}', audits[0].name), 'ambiguous or missing retained supplier audit')
        audit, public_bindings = audits[0], {}
        if spec.manifest['accepted_suppliers'][module]['group'] != 'mellin':
            public_bindings = group.public['owners'][module]['receipt_bindings']
        refs = {'audit_plan': audit / 'AUDIT_PLAN.json',
                'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
                'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
                'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
                'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
        for key, path in refs.items():
            retained_read(s, spec, path, public_bindings.get(key))
        plan = s.api.read_json(refs['audit_plan'])
        require(s.api.audit_valid(group.commit, PROJECT, audit, plan, {module: owner.normal},
                group.graph, group.sources, s.h, s.d) == {module}, 'original supplier full audit differs')
        result = s.api.read_json(refs['audit_result'])
        owner.live_validated = True
        spec.supplier_evidence[module] = {'source_commit': group.commit,
            'compiler_job': group.fixed['compiler_job'], 'source_sha256': group.sources[module],
            'published_source_count': group.fixed['published_source_count'],
            'selected_supplier_live_closure_count': len(s.h.closure(group.graph, [module])),
            'normal': {'path': str(owner.normal_path), **spec.retained_inputs[str(owner.normal_path)]},
            'audit_plan': {'path': str(refs['audit_plan']), **spec.retained_inputs[str(refs['audit_plan'])]},
            'audit_result': {'path': str(refs['audit_result']), **spec.retained_inputs[str(refs['audit_result'])]},
            'owned_count': result['total_owned_exports'], 'public_count': result['total_public_exports'],
            'original_group_worker_exit_code': group.original['worker_exit_code'],
            'original_full_audit_revalidated_without_execution': True,
            'receipt_rebound_to_current_commit': False, 'Lean_or_kernel_executed_for_supplier': False}
    return owner


def fixed_dependency_pins(s, spec, module):
    policy = spec.manifest['fixed_dependencies'][module]
    stem = '.lake/build/lib/lean/' + module.replace('.', '/')
    if policy['kind'] == 'retained_accepted_normal_dependency_context':
        owner = retained_owner(s, spec, policy['witness_owner'])
        context = owner.normal['dependency_context']
        require(context['project_sources'].get(module) == spec.sources[module],
                'retained dependency source identity differs')
        return {stem + ext: context['dependency_objects_and_traces'][stem + ext] for ext in ('.olean', '.trace')}
    record = spec.observed['modules'][module]
    require(set(record['outputs']) <= {'.olean', '.trace', '.ilean', '.olean.private', '.olean.server'},
            'unexpected observed artifact extension')
    return {stem + ext: value for ext, value in record['outputs'].items()}


def environment(s, review):
    configuration = {p: regular_fingerprint(s, PROJECT / p) for p in review['runtime_configuration_bindings']}
    require(configuration == review['runtime_configuration_bindings'] and
            not os.path.lexists(PROJECT / 'lakefile.lean'), 'runtime configuration differs')
    runtime = s.d.runtime_binding(s.h)
    require(runtime == review['existing_runtime_bindings'], 'existing runtime binding differs')
    protected = {m: file_binding(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    require(protected == s.h.FOUR_ROOTS, 'protected original roots differ')
    return {'configuration': configuration, 'runtime': runtime, 'protected_roots': protected}


def snapshot(s, spec):
    result = environment(s, spec.review)
    sources = {m: file_binding(PROJECT / s.h.module_path(m)) for m in sorted(spec.active)}
    require(sources == {m: spec.sources[m] for m in sorted(spec.active)}, 'selected live source context differs')
    dependencies = {}
    for module, expected in sorted(spec.dependency_pins.items()):
        actual = module_artifacts(s, module)
        require(all(actual.get(path) == value for path, value in expected.items()),
                'PRESERVED_DEPENDENCY_PIN_DIFFERS: ' + module)
        dependencies[module] = actual
    retained = {path: regular_fingerprint(s, Path(path)) for path in spec.retained_inputs}
    require(retained == spec.retained_inputs, 'original retained acceptance evidence changed')
    result.update(selected_live_sources=sources, preserved_dependency_artifacts=dependencies,
                  retained_original_evidence=retained, committed_inputs=spec.input_bindings)
    return result


def preflight(s, commit, selected):
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source-commit must name a commit')
    executed = Path(__file__).read_bytes()
    require(executed == git_file(commit, RUNNER), 'executed runner differs from committed source')
    manifest, graph, sources, observed, inputs = source_manifest(s, commit, selected)
    active = s.h.closure(graph, selected)
    blocked = sorted(active & set(manifest['unaccepted_p3_dependencies']))
    require(not blocked, 'UNACCEPTED_P3_SUPPLIERS_REQUIRE_SEPARATE_ACCEPTANCE: ' + ', '.join(blocked))
    review_raw = pinned(commit, REVIEW, REVIEW_SHA)
    review = json.loads(review_raw)
    for path, expected in review['source_configuration_bindings'].items():
        raw = git_file(commit, path)
        require({'bytes': len(raw), 'sha256': s.api.sha(raw)} == expected, 'published configuration differs: ' + path)
    actual_graph, actual = s.h.project_graph(PROJECT, selected)
    require(actual_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in actual.items()} == {m: sources[m] for m in active},
            'selected installed source graph differs; source installation is separate')
    spec = SimpleNamespace(manifest=manifest, graph=graph, sources=sources, observed=observed,
        review=review, active=active, selected=set(selected), order=s.d.compile_order([], selected, graph),
        input_bindings={**inputs, 'runtime_review': {'path': REVIEW, 'bytes': len(review_raw), 'sha256': s.api.sha(review_raw)},
                        'runner': {'path': RUNNER, 'bytes': len(executed), 'sha256': s.api.sha(executed)}},
        retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})
    environment(s, review)
    for module in sorted(active & set(manifest['accepted_suppliers'])):
        retained_owner(s, spec, module, validate_live=True)
        spec.dependency_pins[module] = module_artifacts(s, module)
    for module in sorted(active & set(manifest['fixed_dependencies'])):
        spec.dependency_pins[module] = fixed_dependency_pins(s, spec, module)
    active_targets = active & set(TARGETS)
    spec.initial_owners = {m: existing_owner(s, commit, spec, m) for m in sorted(active_targets)}
    for module in sorted(active_targets - set(selected)):
        require_completed_existing_owner(s, commit, spec, module, spec.initial_owners[module])
        spec.dependency_pins[module] = module_artifacts(s, module)
    require(set(spec.dependency_pins) == active - set(selected), 'selected dependency readiness inventory incomplete')
    spec.baseline = snapshot(s, spec)
    return spec


def worker(s, commit, selected, run):
    s.d.verify_lane(s.h)
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [], 'failures': {},
              'acceptance_bindings': {}, 'direct_import_readiness': {}, 'reused_complete_selected_owners': [],
              'whole_P1_complete': False, 'whole_P1_5_complete': False,
              'acceptance_class': 'SELECTED_CURRENT_P1_BRIDGES_AND_ORIGINAL_PROVIDERS',
              'accepted_supplier_recompile_requested': False, 'dependency_rebuild_requested': False,
              'old_receipts_rebound': False, 'old_P3_REUSE_changed': False}
    spec = None
    try:
        spec = preflight(s, commit, selected)
        result['targets'] = spec.order
        result['original_supplier_acceptance_bindings'] = spec.supplier_evidence
        result['published_source_count'] = len(spec.graph)
        result['selected_live_source_count'] = len(spec.active)
        s.d.save(run / 'CONTEXT_BEFORE.json', spec.baseline)
        s.d.save(run / 'COMMITTED_INPUT_BINDINGS.json', spec.input_bindings)
        for module in spec.order:
            require(snapshot(s, spec) == spec.baseline, 'source/runtime/preserved evidence context changed')
            other_owners = {m: module_artifacts(s, m) for m in TARGETS if m != module}
            try:
                state = spec.initial_owners[module]
                complete = (ROOT / commit / module / 'audits').is_dir() and any(
                    (ROOT / commit / module / 'audits').glob('*/lane-0/VALIDATION_RESULTS.json'))
                if complete:
                    require_completed_existing_owner(s, commit, spec, module, state)
                    result['reused_complete_selected_owners'].append(module)
                else:
                    result['direct_import_readiness'][module] = direct_import_readiness(s, spec, module, run)
                    require(snapshot(s, spec) == spec.baseline and
                            {m: module_artifacts(s, m) for m in other_owners} == other_owners,
                            'preserved dependency/other target changed during import readiness')
                    run_owner(s, commit, ROOT / commit, run, module, spec.graph, spec.sources)
                require(snapshot(s, spec) == spec.baseline and
                        {m: module_artifacts(s, m) for m in other_owners} == other_owners,
                        'preserved context or another owner changed during acceptance')
                result['acceptance_bindings'][module] = acceptance_binding(s, commit, module)
                result['accepted_owners'].append(module)
                s.ops.emit('CURRENT_CORRECTION_OWNER_ACCEPTED', module=module)
            except Exception as error:
                result['failures'][module] = str(error)
                s.ops.emit('CURRENT_CORRECTION_OWNER_HELD_OR_FAILED', module=module, reason=str(error))
                break
        if not result['failures']:
            before = {m: module_artifacts(s, m) for m in TARGETS}
            stock = s.ops.run(run, 'final-stock-readiness', s.h.guard(0, ['lake', '--no-build', 'build'] +
                             ['+' + m + ':olean' for m in spec.order]), cwd=PROJECT)
            require(stock['exit_code'] == 0 and stock['actual_built_modules'] == [] and
                    stock['actual_failed_modules'] == [], 'FINAL_STOCK_READINESS_FAILED_NO_REBUILD_ALLOWED')
            require({m: module_artifacts(s, m) for m in TARGETS} == before,
                    'target artifact changed during final stock readiness')
            result['final_stock_readiness'] = stock
    except Exception as error:
        result['context_error'] = str(error)
    finally:
        if spec is not None:
            try:
                after = snapshot(s, spec)
                s.d.save(run / 'CONTEXT_AFTER.json', after)
                require(after == spec.baseline, 'source/runtime/preserved evidence context changed')
            except Exception as error:
                result['final_context_error'] = str(error)
    s.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('context_error') or result.get('final_context_error')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--targets', nargs='+', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit, selected = args.source_commit, selection(args.targets)
    require(re.fullmatch('[0-9a-f]{40}', commit), 'source-commit requires a full lowercase SHA')
    s = helpers()
    if args.check:
        require(args.inside_lane is None, 'read-only check does not use a lane')
        spec = preflight(s, commit, selected)
        print(json.dumps({'status': 'PUBLISHED_SOURCES_AND_SELECTED_EXISTING_ACCEPTANCE_CONTEXT_VERIFIED',
            'source_commit': commit, 'targets': spec.order, 'published_source_count': len(spec.graph),
            'selected_live_source_count': len(spec.active), 'preserved_dependency_count': len(spec.dependency_pins),
            'original_supplier_acceptance_bindings': spec.supplier_evidence,
            'stock_readiness_performed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}))
        return 0
    base = ROOT / commit
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                'invalid correction worker directory')
        return worker(s, commit, selected, run)
    preflight(s, commit, selected)
    run = s.d.attempt(base / 'runs')
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [], 'failures': {},
              'whole_P1_complete': False, 'whole_P1_5_complete': False}
    try:
        s.d.save(run / 'GIT_BEFORE.json', s.d.original_git_state(REPO))
        executed = run / 'executed-driver.py'
        s.d.write_frozen(executed, Path(__file__).read_bytes())
        child = ['python3', '-B', str(executed), '--source-commit', commit, '--targets', *selected,
                 '--run', '--inside-lane', str(run)]
        command = s.ops.run(run, 'serialized-worker',
                           s.h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        if (run / 'WORKER_RESULT.json').is_file():
            result.update(s.api.read_json(run / 'WORKER_RESULT.json'))
        result['worker_exit_code'] = command['exit_code']
        require(command['exit_code'] == 0, 'serialized worker exited ' + str(command['exit_code']))
    except Exception as error:
        result['dispatch_error'] = str(error)
    finally:
        try:
            after = s.d.original_git_state(REPO)
            s.d.save(run / 'GIT_AFTER.json', after)
            require(after == s.api.read_json(run / 'GIT_BEFORE.json'), 'original dirty Git state changed')
        except Exception as error:
            result['git_error'] = str(error)
    success = (set(result['accepted_owners']) == set(selected) and not result['failures'] and
               not any(key in result for key in ('context_error', 'final_context_error', 'dispatch_error', 'git_error')))
    result['all_selected_owners_accepted'] = success
    s.d.save(run / 'RESULT.json', result)
    s.ops.emit('P15_CURRENT_CORRECTIONS_RESULT', path=str(run / 'RESULT.json'), **result)
    return int(not success)


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    raise SystemExit(main())
