#!/usr/bin/env python3
"""Strict single-owner Cell05AllRowGaps executor; all old proofs are read-only reuse."""
import argparse
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import time
import types

STAGE = Path('/workspace/p26-cell05-all-row-gaps-20261127-v1')
TOOL_REL = Path('tools/p26/cell05-all-row-gaps-20261127')
SHORT = 'P2OriginalSaving19Cell05AllRowGaps'
MODULE = 'ImbalancedChen.' + SHORT
SHAPE_MODULE = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape'
PURE_MODULES = {'ImbalancedChen.P2OriginalSaving19RowNumericsPure', 'ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure'}
MODES = ('normal', 'kernel', 'owned')
SCOPE = 'Cell05 all 56 original concrete geometry rows: positive gap sum and stored mean-gap equality only'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(path, exists=True):
    path = Path(path)
    need(path.is_absolute() and '..' not in path.parts, 'Absolute canonical path required')
    cursor = Path(path.anchor)
    for part in path.parts[1:]:
        cursor /= part
        try:
            st = cursor.lstat()
        except FileNotFoundError:
            need(not exists, 'Missing canonical path: ' + str(cursor))
            continue
        need(not stat.S_ISLNK(st.st_mode), 'Symlink rejected: ' + str(cursor))
    return path


def checked_bytes(path, pin):
    path = canonical(path)
    need(path.is_file(), 'Regular file required')
    body = path.read_bytes()
    need(len(body) == pin['bytes'] and hashlib.sha256(body).hexdigest() == pin['sha256'], 'Pinned file changed: ' + str(path))
    return body


def load_source(path, pin, name):
    """Execute exactly the authenticated cached bytes, never a pyc or a second read."""
    need(name not in sys.modules, 'Conflicting already loaded helper: ' + name)
    body = checked_bytes(path, pin)
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(body, str(path), 'exec'), module.__dict__)
    return module


def authenticate(here, digest):
    need(re.fullmatch(r'[0-9a-f]{64}', digest), 'Invalid workflow manifest SHA')
    path = canonical(here / 'WORKFLOW_MANIFEST.json')
    body = path.read_bytes()
    need(hashlib.sha256(body).hexdigest() == digest, 'Wrong workflow manifest')
    manifest = json.loads(body)
    need(manifest['schema'] == 'p26_cell05_all_row_gaps_workflow_v1', 'Wrong workflow schema')
    rows = manifest['files']
    names = [r['relative_path'] for r in rows]
    need(len(names) == len(set(names)) and {'run_gaps.py', 'CONFIG.json'} <= set(names), 'Incomplete workflow manifest')
    cached = {}
    for row in rows:
        relative = Path(row['relative_path'])
        need(not relative.is_absolute() and '..' not in relative.parts and relative.name != '__init__.py', 'Unsafe workflow member')
        cached[str(relative)] = checked_bytes(here / relative, row)
    need(not any(p.name == '__pycache__' or p.suffix in {'.pyc', '.so'} for p in here.rglob('*')), 'Unexpected executable cache')
    need({str(p.relative_to(here)) for p in here.rglob('*.py')} <= set(names), 'Unpinned Python source')
    config = json.loads(cached['CONFIG.json'])
    need(config['schema'] == 'p26_cell05_all_row_gaps_config_v1' and config['stage'] == str(STAGE), 'Wrong fixed stage/configuration')
    return config, manifest


def pointer(value, path):
    need(path.startswith('/'), 'Expected an absolute JSON pointer')
    for raw in path.split('/')[1:]:
        key = raw.replace('~1', '/').replace('~0', '~')
        value = value[int(key)] if isinstance(value, list) else value[key]
    return value


def project_imports(source):
    return re.findall(r'^import (ImbalancedChen\.[\w.]+)$', source, re.M)


def validate_pure2(R, root, transport_pin, shape_context):
    """Join the two original canonical normal+kernel authorities without inventing old owned evidence."""
    root = R.canonical(root, True)
    transport = json.loads(checked_bytes(root / 'TRANSPORT.json', transport_pin))
    need(transport['schema'] == 'p26_cell05_all_row_gaps_pure2_transport_v1' and transport['module_count'] == 2,
         'Wrong pure supplier transport')
    need(all(transport[k] == 0 for k in ('old_normal_commands_replayed', 'old_kernel_commands_replayed', 'new_Lean_commands')) and
         all(transport[k] is False for k in ('historical_explicit_trust_zero_claimed', 'historical_loaded_runtime_inventory_claimed',
                                            'new_supplier_owned_audits_claimed', 'P2_6_complete')), 'Pure transport scope changed')
    files = transport['files']
    names = [row['relative_path'] for row in files]
    need(len(files) == 16 and len(set(names)) == 16, 'Incomplete pure2 inventory')
    actual = {str(p.relative_to(root)) for p in R.tree_files(root, set(names) | {'TRANSPORT.json'})}
    need(actual == set(names) | {'TRANSPORT.json'}, 'Pure2 inventory differs')
    bodies, frozen = {}, [R.fp(root / 'TRANSPORT.json')]
    for row in files:
        p = Path(row['relative_path'])
        need(not p.is_absolute() and '..' not in p.parts, 'Unsafe pure member')
        bodies[str(p)] = checked_bytes(root / p, row)
        frozen.append(R.fp(root / p))
    manifest = json.loads(bodies['MANIFEST.json'])
    need(R.same(R.fp(root / 'MANIFEST.json'), transport['original_manifest']) and
         manifest['schema'] == 'p26_cell00_480_portable_transfer_manifest_v1', 'Wrong original canonical manifest')
    entries = {r['archive_path']: r for r in manifest['files']}
    need(len(entries) == len(manifest['files']), 'Duplicate original archive member')
    origins = {}
    for row in files:
        if row['relative_path'] != 'MANIFEST.json':
            old = row['original_manifest_row']
            need(entries[row['relative_path']] == old and R.same(old, row), 'Changed original member binding')
            origins[old['original_path']] = row['relative_path']
    audit, runtime = json.loads(bodies['AUDIT.json']), json.loads(bodies['RUNTIME.json'])
    need(audit['schema'] == 'p26_cell00_480_readonly_recovery_audit_v1' and audit['failures'] == [] and
         audit['source_object_hashes_match'] is True and audit['receipt_metadata_not_rewritten'] is True and
         audit['runtime'] == runtime, 'Original canonical audit/runtime differs')
    need(runtime['mathlib_pin'] == shape_context['runtime']['mathlib_commit'] and
         runtime['lean_commit'] in shape_context['runtime']['lean_version'] and
         runtime['portable_LEAN_PATH_rule'] == '<extracted_bundle>/objects followed by separately verified matching external dependency roots',
         'Portable runtime version/commit contract differs')
    bins = {Path(r['path']).name: r for r in runtime['runtime_files_observed']}
    need(R.same(bins['lean'], shape_context['runtime']['lean_binary']) and
         R.same(bins['leanchecker'], shape_context['runtime']['leanchecker_binary']), 'Pure canonical compiler/checker bytes differ')
    modules = {r['module']: r for r in audit['modules'] if r['module'] in PURE_MODULES}
    need(set(modules) == PURE_MODULES and transport['original_modules'] == [modules[r['module']] for r in transport['original_modules']],
         'Pure canonical module records differ')
    all_deps = dict(shape_context['dependencies'])
    selected = {}
    for name in sorted(PURE_MODULES):
        row = modules[name]
        source = root / 'sources' / (name.replace('.', '/') + '.lean')
        obj = root / 'objects' / (name.replace('.', '/') + '.olean')
        need(R.same(R.fp(source), row['source']) and R.same(R.fp(obj), row['object']) and row['object_siblings'] == [], 'Pure source/object mismatch')
        need(re.findall(r'^import ([\w.]+)$', source.read_text(), re.M) == row['imports'], 'Pure source import graph differs')
        selected[name] = {'source': R.fp(source), 'object': R.fp(obj)}
    all_deps.update(selected)
    records = []
    for name in sorted(PURE_MODULES):
        row = modules[name]
        need(row['acceptance_boundary'] == 'DIRECT_NORMAL_AND_KERNEL_RECEIPTS_VERIFIED' and set(row['receipts']) == {'normal', 'kernel'}, 'Wrong old acceptance boundary')
        for mode in ('normal', 'kernel'):
            authority = row['receipts'][mode]
            prior = authority['prior_hash_pin']
            closure = json.loads(bodies[origins[prior['manifest']]])
            need(pointer(closure, prior['pointer']) == authority['receipt'], 'Original closure receipt pointer differs')
            receipt_path = root / origins[authority['receipt']['path']]
            need(R.same(R.fp(receipt_path), authority['receipt']) and authority['json_pointer'] == '', 'Original raw result pin differs')
            result = R.read(receipt_path)
            need(result['module'] == name and result['mode'] == mode and result['attempt'] == 'namespace-v2' and
                 result['status'] == 'succeeded' and type(result['exit_code']) is int and result['exit_code'] == 0 and
                 result['input_before'] == result['input_after'] and result['Mathlib_pin'] == runtime['mathlib_pin'], 'Original normal/kernel result differs')
            need(R.same(result['source'], row['source']) and R.same(result['object'], row['object']), 'Old receipt source/object binding differs')
            expected_argv = ([bins['lean']['path'], '-j1', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0', '-o', result['object']['path'], result['source']['path']]
                             if mode == 'normal' else [bins['leanchecker']['path'], '--verbose', name])
            need(result['argv'] == expected_argv and result['cwd'] == str(Path(result['source']['path']).parents[1]), 'Original argv/cwd differs')
            need(result['LEAN_PATH'].split(os.pathsep)[1:] == [r['path'] for r in runtime['original_external_LEAN_PATH_roots']], 'Original external search path differs')
            expected_dep_names = {'ImbalancedChen.P2OriginalSaving19SourceJson', 'ImbalancedChen.P2OriginalSaving19ArchiveSchema',
                                  'ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure'} if name.endswith('RowNumericsPure') else set()
            need({d['module'] for d in result['dependencies']} == expected_dep_names and len(result['dependencies']) == len(expected_dep_names), 'Old project dependency context differs')
            for dep in result['dependencies']:
                current = all_deps[dep['module']]
                need(R.same(dep['source'], current['source']) and R.same(dep['object'], current['object']), 'Same-name old supplier conflict: ' + dep['module'])
            log_path = root / origins[result['log']['path']]
            need(R.same(R.fp(log_path), result['log']), 'Original log/result pin differs')
            log = log_path.read_text()
            need(not re.search(r'(?:^|:\s*|\s)(?:warning|error|fatal error):', log, re.I | re.M), 'Diagnostic in accepted old log')
            if mode == 'kernel':
                need(log.strip() == 'replaying ' + name, 'Wrong original kernel replay log')
            elif name.endswith('Q96ArithmeticPure'):
                need(log == '', 'Original no-print normal log changed')
            else:
                found = re.fullmatch(r"'ImbalancedChen.P2OriginalSaving19RowNumericsPure.rowDataChecksFor_iff_originalForm' depends on axioms: \[([^\]]*)\]\s*", log)
                need(found is not None and {x.strip() for x in found[1].split(',')} <= ALLOWED, 'Original normal axiom log differs')
            records.append({'module': name, 'mode': mode, 'original_receipt': authority['receipt'], 'current_receipt': R.fp(receipt_path),
                            'original_log': result['log'], 'current_log': R.fp(log_path)})
    return {'schema': 'cell05_pure2_reuse_validated_v1', 'dependencies': selected, 'records': records,
            'frozen_files': frozen, 'accepted_old_normal_kernel_records': 4, 'new_supplier_owned_audits': 0,
            'historical_explicit_trust_zero_claimed': False, 'historical_loaded_inventory_claimed': False, 'old_proof_commands': 0}


class Runner:
    def __init__(self, stage, R, V, E, S, context):
        self.stage, self.R, self.V, self.E, self.S, self.ctx = Path(stage), R, V, E, S, context
        self.receipts = self.stage / 'verification'
        self.run = self.receipts / 'RUN.json'
        self.source = self.stage / 'project/ImbalancedChen' / (SHORT + '.lean')
        self.object = self.stage / 'objects/ImbalancedChen' / (SHORT + '.olean')
        self.audit = Path(context['targets'][0]['audit']['path'])

    def command_fields(self, mode, previous):
        need(mode in MODES and ((mode == 'normal') == (previous is None)), 'Invalid new command order')
        ctx, R = self.ctx, self.R
        common = [ctx['runtime']['lean_binary']['path'], '--trust=0', '-DwarningAsError=true', '-j1', '-M12288',
                  '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
        argv = (common + ['-o', str(self.object), 'ImbalancedChen/' + SHORT + '.lean'] if mode == 'normal' else
                [ctx['runtime']['leanchecker_binary']['path'], '--verbose', MODULE] if mode == 'kernel' else common + [str(self.audit)])
        target = ctx['targets'][0]
        return {'schema': 'cell05_all_row_gaps_command_v1', 'run': R.fp(self.run), 'module': MODULE, 'mode': mode,
                'previous_accepted': previous, 'argv': argv, 'cwd': ctx['cwd'], 'environment': ctx['environment'],
                'source': target['source'], 'audit_source': target['audit'], 'dependencies': ctx['dependencies'],
                'object_before': None if previous is None else R.fp(self.object)}

    def log_facts(self, mode, log):
        need(not re.search(r'(?:^|:\s*|\s)(?:warning|error|fatal error):', log, re.I | re.M), 'Diagnostic in successful log')
        if mode == 'kernel':
            need(log.strip() == 'replaying ' + MODULE, 'Wrong new kernel replay log')
            return {}
        if mode == 'owned':
            markers = ('P26_GEOMETRY01_AUDIT_IMPORTS ', 'P26_GEOMETRY01_AUDIT_INVENTORY ', 'P26_GEOMETRY01_AUDIT_DECL ', 'P26_GEOMETRY01_AUDIT_COMPLETE ')
            need(all(line.startswith(markers) for line in log.splitlines() if line.strip()), 'Unexpected full-owned output')
            return {'owned': self.R.parse_target_owned(log, self.ctx, MODULE)}
        source = self.source.read_text()
        names = re.findall(r'^#print axioms (\w+)$', source, re.M)
        need(len(names) == len(set(names)) and len(names) > 0, 'Missing/duplicate explicit axiom prints')
        rows = list(re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])\s*", log))
        need(''.join(m[0] for m in rows) == log and len(rows) == len(names), 'Incomplete or unknown printed output')
        for token, row in zip(names, rows):
            public = MODULE + '.' + token
            private = re.search(r'^private\s+(?:theorem|def|abbrev)\s+' + re.escape(token) + r'\b', source, re.M)
            allowed_name = row[1] == public or (private and re.fullmatch(r'_private\.' + re.escape(MODULE) + r'\.\d+\.' + re.escape(public), row[1]))
            need(allowed_name, 'Printed declaration does not belong to this source/module')
        axioms = {x.strip() for row in rows for x in (row[2] or '').split(',') if x.strip()}
        need(axioms <= ALLOWED, 'Forbidden normal axiom')
        return {'printed_declarations': [r[1] for r in rows], 'printed_axioms': sorted(axioms)}

    def step_paths(self, mode):
        return tuple(self.receipts / (mode + suffix) for suffix in ('-command.json', '.log', '-result.json', '-accepted.json'))

    def printed_owned_bindings(self, owned):
        """Retain exact log spellings and bind each public/private pretty alias to one real owned name."""
        printed = self.log_facts('normal', self.step_paths('normal')[1].read_text())['printed_declarations']
        names = {r['name'] for r in owned['declarations']}
        source = self.source.read_text()
        bindings = []
        for display in printed:
            matches = [display] if display in names else []
            token = display.rsplit('.', 1)[1]
            if not matches and display == MODULE + '.' + token and re.search(
                    r'^private\s+(?:theorem|def|abbrev)\s+' + re.escape(token) + r'\b', source, re.M):
                pattern = r'_private\.' + re.escape(MODULE) + r'\.\d+\.' + re.escape(display)
                matches = [name for name in names if re.fullmatch(pattern, name)]
            need(len(matches) == 1, 'Printed name lacks a unique complete-owned declaration')
            bindings.append({'printed': display, 'owned_name': matches[0]})
        need(len({r['owned_name'] for r in bindings}) == len(bindings), 'Printed names alias the same owned declaration')
        return bindings

    def witness_path(self, mode):
        return self.stage / 'launch-witnesses' / (mode + '.json')

    def witness_fields(self, mode, command):
        return {'schema': 'cell05_all_row_gaps_launch_v1', 'module': MODULE, 'mode': mode, 'run': self.R.fp(self.run), 'command': command}

    def verify_witness(self, mode, command):
        path = self.witness_path(mode)
        need(self.R.read(path) == self.witness_fields(mode, command), 'Durable launch witness differs')
        return self.R.fp(path)

    def publish_witness(self, mode, command):
        path = self.witness_path(mode)
        self.R.dump_new(path, self.witness_fields(mode, command))
        for p in (self.run, Path(command['path']), path):
            with p.open('rb') as stream:
                os.fsync(stream.fileno())
        for p in (self.receipts, path.parent, self.stage):
            self.S.sync_directory(p)
        return self.verify_witness(mode, command)

    def metrics_ok(self, result, started):
        return (all(type(x) in (int, float) and math.isfinite(x) and x > 0 for x in (started, result['finished_unix'], result['elapsed_seconds'])) and
                result['started_unix'] == started and result['finished_unix'] >= started and result['elapsed_seconds'] <= self.ctx['wall_limit_seconds'] and
                type(result['peak_rss_bytes']) is int and 0 <= result['peak_rss_bytes'] <= self.ctx['rss_limit_bytes'])

    def verify_step(self, mode, previous):
        R = self.R
        cp, lp, rp, sp = self.step_paths(mode)
        command, result = R.read(cp), R.read(rp)
        need('started_unix' in command and {k: v for k, v in command.items() if k != 'started_unix'} == self.command_fields(mode, previous), 'Command differs from frozen plan')
        witness = self.verify_witness(mode, R.fp(cp))
        need(result['schema'] == 'cell05_all_row_gaps_result_v1' and result['status'] == 'succeeded' and
             type(result['exit_code']) is int and result['exit_code'] == 0 and result['termination_reason'] is None and
             self.metrics_ok(result, command['started_unix']) and result['launch_witness'] == witness, 'Unsuccessful or invalid new result')
        need(all(result[k] == command[k] for k in ('run', 'module', 'mode', 'source', 'audit_source', 'dependencies')), 'New command/result binding differs')
        need(result['command'] == R.fp(cp) and result['log'] == R.fp(lp) and result['object'] == R.fp(self.object) and result['object']['bytes'] > 0, 'New result evidence changed')
        facts = self.log_facts(mode, lp.read_text())
        if mode == 'owned':
            owned = facts.pop('owned')
            need(R.checked(result['owned_declarations'], self.receipts / 'owned-declarations.json') == owned and
                 result['owned_declaration_count'] == owned['owned_declaration_count'], 'Incomplete new owned evidence')
            need(result['printed_owned_bindings'] == self.printed_owned_bindings(owned), 'Normal/full-owned name binding differs')
        need(all(result.get(k) == v for k, v in facts.items()), 'Normal print evidence differs')
        seal = {'schema': 'cell05_all_row_gaps_accepted_v1', 'status': 'accepted', 'run': R.fp(self.run), 'module': MODULE, 'mode': mode,
                'launch_witness': witness, 'command': R.fp(cp), 'result': R.fp(rp), 'object': R.fp(self.object)}
        need(R.read(sp) == seal, 'New accepted seal differs')
        return R.fp(sp)

    def prior_steps(self):
        R = self.R
        names = {'RUN.json', 'SUCCESS.json', 'STOPPED.json', 'owned-declarations.json'} | {p.name for mode in MODES for p in self.step_paths(mode)}
        R.tree_files(self.receipts, names)
        R.tree_files(self.stage / 'launch-witnesses', {m + '.json' for m in MODES})
        accepted = []
        for mode in MODES:
            paths = self.step_paths(mode)
            present = [p.exists() for p in paths]
            witness = self.witness_path(mode)
            if not any(present) and not witness.exists():
                continue
            need(witness.exists() and present[0], 'Orphan/missing launch witness or command; preserve without replay')
            self.verify_witness(mode, R.fp(paths[0]))
            need(all(present) and len(accepted) == MODES.index(mode), 'Incomplete/non-prefix evidence; preserve without replay')
            accepted.append(self.verify_step(mode, accepted[-1] if accepted else None))
        need(not (self.receipts / 'STOPPED.json').exists(), 'Stopped stage retained; no replay')
        need(self.object.exists() == bool(accepted), 'Unreceipted/missing new object')
        need((self.receipts / 'owned-declarations.json').exists() == (len(accepted) == 3), 'Orphan/missing full owned inventory')
        if (self.receipts / 'SUCCESS.json').exists() or (self.stage / 'REUSE_INDEX.json').exists() or R.tree_files(self.stage / 'exports'):
            need(len(accepted) == 3, 'Published final evidence with missing accepted prefix')
        return accepted

    def process(self, argv, cwd, env, log):
        return self.S.run_process(self.V, argv, cwd, env, log)

    def execute(self, mode, previous, check):
        R = self.R
        check()
        need(not any(p.exists() for p in self.step_paths(mode)), 'Refusing to repeat new command')
        history = self.prior_steps()
        need(len(history) == MODES.index(mode) and (history[-1] if history else None) == previous, 'New command lacks exact prior acceptance')
        cp, lp, rp, sp = self.step_paths(mode)
        command = self.command_fields(mode, previous)
        command['started_unix'] = time.time()
        R.dump_new(cp, command)
        cp_pin = R.fp(cp)
        witness = self.publish_witness(mode, cp_pin)
        print(json.dumps({'mode': mode, 'status': 'started'}), flush=True)
        rc, reason, peak, elapsed = self.process(command['argv'], command['cwd'], {k: v for k, v in command['environment'].items() if v is not None}, lp)
        result = {k: command[k] for k in ('run', 'module', 'mode', 'source', 'audit_source', 'dependencies')}
        result.update(schema='cell05_all_row_gaps_result_v1', status='failed', launch_witness=witness, command=cp_pin,
                      exit_code=rc, termination_reason=reason, started_unix=command['started_unix'], finished_unix=time.time(),
                      elapsed_seconds=elapsed, peak_rss_bytes=peak, log=R.fp(lp), object=R.fp(self.object) if self.object.exists() else None)
        try:
            check()
            need(R.fp(cp) == cp_pin and R.read(cp) == command and self.verify_witness(mode, cp_pin) == witness, 'Command/witness changed during execution')
            need(all(self.verify_step(MODES[i], history[i-1] if i else None) == p for i, p in enumerate(history)), 'Prior acceptance changed during execution')
            need(rc == 0 and reason is None and self.metrics_ok(result, command['started_unix']), 'New command failed or exceeded limits')
            need(result['object'] and result['object']['bytes'] > 0 and (mode == 'normal' or result['object'] == command['object_before']), 'Missing or mutated new object')
            facts = self.log_facts(mode, lp.read_text())
            if mode == 'owned':
                owned = facts.pop('owned')
                result['printed_owned_bindings'] = self.printed_owned_bindings(owned)
                op = self.receipts / 'owned-declarations.json'
                R.dump_new(op, owned)
                result.update(owned_declarations=R.fp(op), owned_declaration_count=owned['owned_declaration_count'])
            result.update(facts, status='succeeded')
        except Exception as exc:
            result['validation_error'] = repr(exc)
        R.dump_new(rp, result)
        if result['status'] != 'succeeded':
            R.dump_new(self.receipts / 'STOPPED.json', {'schema': 'cell05_all_row_gaps_stopped_v1', 'status': 'stopped',
                'run': R.fp(self.run), 'failed_result': R.fp(rp), 'preceding_acceptances': len(history), 'P2_6_complete': False})
            raise RuntimeError('Failed new command retained: ' + str(rp) + ': ' + result.get('validation_error', 'command failure'))
        R.dump_new(sp, {'schema': 'cell05_all_row_gaps_accepted_v1', 'status': 'accepted', 'run': R.fp(self.run), 'module': MODULE,
                       'mode': mode, 'launch_witness': witness, 'command': cp_pin, 'result': R.fp(rp), 'object': R.fp(self.object)})
        seal = self.verify_step(mode, previous)
        print(json.dumps({'mode': mode, 'status': 'accepted', 'elapsed_seconds': elapsed, 'peak_rss_bytes': peak}), flush=True)
        return seal

    def require_published(self):
        for p in (self.receipts / 'SUCCESS.json', self.stage / 'REUSE_INDEX.json', self.stage / 'exports/gaps-evidence.tar.xz'):
            need(p.is_file(), 'Missing retained final evidence: ' + str(p))
            self.R.canonical(p, True)

    def finish(self, accepted, check, verify_only=False):
        R, E, ctx = self.R, self.E, self.ctx
        if verify_only:
            self.require_published()
        check()
        need(len(accepted) == 3 and self.prior_steps() == accepted, 'Three exact new acceptances required')
        def summary(path, value):
            if verify_only:
                need(R.read(path) == value, 'Retained final summary differs')
            else:
                self.S.recorded(R, path, value)
        success = self.receipts / 'SUCCESS.json'
        summary(success, {'schema': 'cell05_all_row_gaps_success_v1', 'status': 'succeeded', 'run': R.fp(self.run),
            'accepted_targets': 1, 'accepted_steps': 3, 'records': [{'module': MODULE, 'mode': m, 'accepted': p} for m,p in zip(MODES,accepted)],
            'object': R.fp(self.object), 'old_supplier_count': 128, 'project_closure_count': 129, 'old_proof_commands': 0,
            'scope': SCOPE, 'P2_6_complete': False})
        index = self.stage / 'REUSE_INDEX.json'
        summary(index, {'schema': 'cell05_all_row_gaps_reuse_index_v1', 'shape_success': ctx['shape_success'], 'shape_run': ctx['shape_run'],
            'shape_reused_steps': 3, 'shape_imported_project_modules': 126, 'pure2_reuse': ctx['pure2_reuse'],
            'pure2_old_normal_kernel_records': 4, 'new_success': R.fp(success), 'new_owners': 1, 'new_steps': 3,
            'new_row_conditions': {'cell': 5, 'rows': 56, 'RowDataChecksFor_clauses': [3,5]},
            'new_complete_ten_clause_rows': 0, 'new_Archive_bound_rows': 0, 'scope': SCOPE, 'P2_6_complete': False})
        paths = [index, self.source, self.object, self.audit, *R.tree_files(self.receipts),
                 *(self.witness_path(m) for m in MODES), *R.tree_files(self.stage / TOOL_REL),
                 *R.tree_files(self.stage / 'inputs/pure2'), self.stage / 'SUPPLIER_REUSE.json']
        entries = {str(p.relative_to(self.stage)): p for p in paths}
        for pin in ctx['predecessor_artifacts']:
            p = R.canonical(pin['path'], True)
            need(R.fp(p) == pin, 'Predecessor archive input changed')
            entries['predecessor/' + str(p.relative_to(Path(ctx['shape_stage'])))] = p
        manifest = {'schema': 'cell05_all_row_gaps_export_v1', 'accepted_targets': 1, 'accepted_steps': 3,
            'pure2_supplier_object_bodies': 2, 'predecessor_archive_included': True, 'other_supplier_objects_copied': 0,
            'new_supplier_owned_audits': 0, 'original_live_guard_validator_passed': False,
            'runtime_guard': ctx['runtime_guard'], 'recovery_certificate': ctx['recovery_certificate'], 'scope': SCOPE, 'P2_6_complete': False,
            'members': [{'member': member, **E.data_pin(p.read_bytes())} for member,p in sorted(entries.items())]}
        output = self.stage / 'exports/gaps-evidence.tar.xz'
        if verify_only or output.exists():
            E.recheck_archive(output, manifest)
        else:
            E.write_verified_archive(output, entries, manifest)
        check()
        need(self.prior_steps() == accepted, 'Evidence changed during archive publication')
        print(json.dumps({'status': 'RETAINED_EVIDENCE_VERIFIED' if verify_only else 'ALL_ROW_GAPS_SUCCESS',
              'success': R.fp(success), 'reuse_index': R.fp(index), 'archive': R.fp(output), 'accepted_targets': 1,
              'accepted_steps': 3, 'old_proof_commands': 0, 'P2_6_complete': False}), flush=True)


def bootstrap_shape(config):
    shape = config['shape']
    S = load_source(Path(shape['driver']['path']), shape['driver'], 'accepted_shape_driver')
    need(str(S.STAGE) == shape['stage'] and str(S.TOOL / 'complete_shape.py') == shape['driver']['path'], 'Wrong predecessor code/stage')
    pins = json.loads(checked_bytes(shape['configuration']['path'], shape['configuration']))
    checked_bytes(shape['recovery_binding']['path'], shape['recovery_binding'])
    return S, pins


def historical_worker(config):
    S, _ = bootstrap_shape(config)
    sys.argv = [str(S.TOOL / 'complete_shape.py'), 'verify', '--recovery-binding-sha256', config['shape']['recovery_binding']['sha256']]
    S.main()


def verify_shape(config, here, workflow_sha, R):
    shape = config['shape']
    for key in ('driver', 'configuration', 'recovery_binding', 'run', 'success', 'index', 'archive'):
        checked_bytes(shape[key]['path'], shape[key])
    # This child can select only the unmodified predecessor's read-only verify entrypoint.
    argv = [sys.executable, '-I', '-S', '-B', str(here / 'run_gaps.py'), 'historical', '--workflow-sha256', workflow_sha]
    proc = subprocess.run(argv, cwd=here, env={'PATH': os.defpath, 'LC_ALL': 'C'}, capture_output=True, timeout=1800)
    need(proc.returncode == 0 and not proc.stderr, 'Accepted Shape read-only verification failed: ' + proc.stderr[-2000:].decode(errors='replace'))
    summary = json.loads(proc.stdout)
    need(summary['status'] == 'RETAINED_EVIDENCE_VERIFIED' and summary['accepted_targets'] == 1 and summary['accepted_steps'] == 3 and
         summary['success'] == shape['success'] and summary['combined_index'] == shape['index'] and summary['archive'] == shape['archive'] and
         summary['P2_6_complete'] is False, 'Unexpected predecessor verification view')
    return R.checked(shape['run'], shape['run']['path'])


def runtime_join(R, config, old):
    pin = config['runtime_compatibility']
    need(pin in old['recovery_frozen_inputs'], 'Runtime compatibility not bound by accepted recovery')
    data = R.checked(pin, pin['path'])
    need(data['schema'] == 'cell05_connections_runtime_compatibility_pins_v1' and data['kernel_compatibility_replays_required'] == 0 and
         data['historical_loaded_inventory_retroactively_claimed'] is False, 'Wrong runtime compatibility contract')
    root = Path(pin['path']).parent
    frozen = [pin]
    for row in data['files']:
        current = R.fp(root / row['relative_path'])
        need(R.same(current,row) and current in old['recovery_frozen_inputs'], 'Unbound runtime compatibility body')
        frozen.append(current)
    comparison = R.read(root / 'runtime-evidence/RUNTIME_COMPARISON.json')
    need(comparison['status'] == 'ALL_TEN_LOGICAL_ROOT_INVENTORIES_MATCH_EXACTLY' and len(comparison['comparison']) == 10 and
         all(row['equal'] is True and row['p1_count'] == row['p2_count'] and row['p1_sha'] == row['p2_sha'] for row in comparison['comparison']) and
         comparison['historical_loaded_inventory_retroactively_claimed'] is False, 'Accepted full-root runtime comparison differs')
    return frozen


def derive_dependencies(R, old, shape_success, pure):
    need(len(old['dependencies']) == 125 and len(old['targets']) == 1 and old['targets'][0]['module'] == SHAPE_MODULE, 'Unexpected accepted Shape closure')
    deps = {name: {'source': row['installed_source'], 'object': row['installed_object']} for name,row in old['dependencies'].items()}
    deps[SHAPE_MODULE] = {'source': old['targets'][0]['source'], 'object': shape_success['object']}
    need(not set(deps) & PURE_MODULES and set(pure['dependencies']) == PURE_MODULES, 'Unexpected supplier overlap')
    deps.update(pure['dependencies'])
    need(len(deps) == 128 and MODULE not in deps, 'Wrong new supplier set')
    return deps


def install_dependencies(R, stage, deps, existing):
    installed = {}
    for module,row in deps.items():
        current = dict(row)
        for kind,folder,suffix in (('source','project','.lean'),('object','objects','.olean')):
            origin = row[kind]
            p = R.canonical(stage / folder / (module.replace('.','/') + suffix))
            if not p.exists():
                need(not existing, 'Missing established supplier copy')
                body = checked_bytes(origin['path'],origin)
                p.parent.mkdir(parents=True,exist_ok=True)
                R.canonical(p.parent,True)
                with p.open('xb') as f:
                    f.write(body)
            need(R.same(R.fp(p),origin) and not p.samefile(origin['path']), 'Wrong or shared supplier copy')
            current['installed_'+kind] = R.fp(p)
        installed[module] = current
    return installed


def check_namespace(R, stage, ctx):
    modules = set(ctx['dependencies'])
    for folder,suffix in (('project','.lean'),('objects','.olean')):
        old = {name.replace('.','/')+suffix for name in modules}
        target = MODULE.replace('.','/')+suffix
        paths = {str(p.relative_to(stage/folder)) for p in R.tree_files(stage/folder,old|{target})}
        need(old <= paths and (folder != 'project' or target in paths), 'Incomplete new namespace')
    for root in ctx['environment']['LEAN_PATH'].split(os.pathsep)[1:] + [str(Path(ctx['environment']['LEAN_SYSROOT'])/'lib/lean')]:
        path = R.canonical(root,True)
        need(not os.path.lexists(path/'ImbalancedChen') and not os.path.lexists(path/'ImbalancedChen.olean'), 'Fallback project namespace')


def make_context(R, config, here, old, pure, deps, runtime_files, workflow_sha):
    source = STAGE/'project/ImbalancedChen'/(SHORT+'.lean')
    audit = here/'owned-audits'/(SHORT+'.lean')
    checked_bytes(source,config['source']);checked_bytes(audit,config['audit'])
    imports = project_imports(source.read_text())
    need(imports == [SHAPE_MODULE,'ImbalancedChen.P2OriginalSaving19RowNumericsPure'], 'New direct import scope differs')
    graph = {name: project_imports(Path(row['installed_source']['path']).read_text()) for name,row in deps.items()}
    seen = set()
    def visit(name):
        if name in seen:return
        need(name in graph, 'Unprovided project import: '+name)
        seen.add(name)
        for dep in graph[name]:visit(dep)
    for name in imports:visit(name)
    need(seen == set(deps) and len(seen)==128, 'Source graph does not match exact 129-module scope')
    environment = dict(old['environment'])
    roots = environment['LEAN_PATH'].split(os.pathsep)
    need(roots[0] == config['shape']['stage']+'/objects', 'Wrong predecessor object namespace')
    environment['LEAN_PATH'] = os.pathsep.join([str(STAGE/'objects'),*roots[1:]])
    workflow_files = [R.fp(p) for p in R.tree_files(here)]
    predecessor = [config['shape'][k] for k in ('driver','configuration','recovery_binding','run','success','index','archive')]
    return {'schema':'cell05_all_row_gaps_run_v1','stage':str(STAGE),'cwd':str(STAGE/'project'),'environment':environment,
        'runtime':old['runtime'],'runtime_guard':old['runtime_guard'],'original_runtime_guard':old['original_runtime_guard'],
        'recovery_certificate':old['recovery_certificate'],'recovery_history':old['recovery_history'],
        'original_live_guard_validator_passed':False,'runtime_compatibility_files':runtime_files,
        'workflow_sha256':workflow_sha,'workflow_files':workflow_files,'shape_stage':config['shape']['stage'],
        'shape_run':config['shape']['run'],'shape_success':config['shape']['success'],'predecessor_artifacts':predecessor,
        'pure2_reuse':R.fp(STAGE/'SUPPLIER_REUSE.json'),'pure2_frozen_files':pure['frozen_files'],
        'targets':[{'module':MODULE,'source':R.fp(source),'audit':R.fp(audit),'project_imports':imports,'transitive_dependencies':sorted(deps)}],
        'dependencies':deps,'rss_limit_bytes':12*1024**3,'wall_limit_seconds':900,'scope':SCOPE,'old_proof_commands':0,'P2_6_complete':False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=('preflight','run',*MODES,'verify','historical'))
    parser.add_argument('--workflow-sha256',required=True)
    args = parser.parse_args()
    need(sys.flags.isolated and sys.flags.dont_write_bytecode and not sys.flags.optimize, 'Use python3 -I -S -B with assertions enabled')
    here = canonical(Path(__file__).parent)
    need(here == STAGE/TOOL_REL and canonical(__file__) == here/'run_gaps.py','Wrong deployed new runner')
    config,_ = authenticate(here,args.workflow_sha256)
    if args.action == 'historical':
        historical_worker(config)
        return
    S,pins = bootstrap_shape(config)
    with S.child_import_boundary(S.OLD_TOOL,pins):
        R,V,E = S.bootstrap(S.OLD,S.OLD_TOOL,pins)
    old = verify_shape(config,here,args.workflow_sha256,R)
    pure = validate_pure2(R,STAGE/'inputs/pure2',config['pure2_transport'],old)
    runtime_files = runtime_join(R,config,old)
    shape_success = R.checked(config['shape']['success'],config['shape']['success']['path'])
    deps = derive_dependencies(R,old,shape_success,pure)
    stage_lock = R.canonical(STAGE/'EXECUTION.lock')
    verify_only = args.action=='verify'
    if verify_only:
        for p in (stage_lock,STAGE/'objects/ImbalancedChen',STAGE/'verification',STAGE/'SUPPLIER_REUSE.json',STAGE/'verification/RUN.json'):
            R.canonical(p,True)
    with stage_lock.open('rb' if verify_only else 'a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        run = STAGE/'verification/RUN.json'
        existing = run.exists()
        need(existing or not (R.tree_files(STAGE/'verification') or R.tree_files(STAGE/'launch-witnesses')), 'RUN missing from old new-stage evidence')
        need(existing or not (STAGE/'objects/ImbalancedChen'/(SHORT+'.olean')).exists(), 'Unreceipted target object')
        deps = install_dependencies(R,STAGE,deps,existing or verify_only)
        if verify_only:
            need(R.read(STAGE/'SUPPLIER_REUSE.json')==pure,'Frozen pure2 reuse differs')
        else:
            S.recorded(R,STAGE/'SUPPLIER_REUSE.json',pure)
        ctx = make_context(R,config,here,old,pure,deps,runtime_files,args.workflow_sha256)
        if verify_only:
            need(R.read(run)==ctx,'Frozen new RUN differs')
        else:
            S.recorded(R,run,ctx)
        runner = Runner(STAGE,R,V,E,S,ctx)
        def check():
            current,_ = authenticate(here,args.workflow_sha256)
            need(current==config and verify_shape(config,here,args.workflow_sha256,R)==old,'Predecessor or workflow view changed')
            need(validate_pure2(R,STAGE/'inputs/pure2',config['pure2_transport'],old)==pure and runtime_join(R,config,old)==runtime_files,'Pure/runtime join changed')
            need(R.read(run)==ctx and R.read(STAGE/'SUPPLIER_REUSE.json')==pure,'New context changed')
            check_namespace(R,STAGE,ctx)
            files = [*ctx['workflow_files'],*ctx['pure2_frozen_files'],*ctx['runtime_compatibility_files'],ctx['targets'][0]['source'],ctx['targets'][0]['audit']]
            files += [pin for row in deps.values() for pin in row.values()]
            for pin in files:
                need(R.fp(pin['path'])==pin,'Frozen execution input changed: '+pin['path'])
        check()
        accepted = runner.prior_steps()
        if args.action=='preflight':
            print(json.dumps({'status':'PASS_PREFLIGHT','old_suppliers':128,'project_closure':129,'accepted_existing_steps':len(accepted),'new_proof_commands':0,'P2_6_complete':False}))
            return
        if verify_only:
            runner.finish(accepted,check,True)
            return
        if args.action=='run':modes=MODES[len(accepted):]
        else:
            index=MODES.index(args.action)
            need(index<=len(accepted),'Requested mode lacks prior acceptance')
            modes=[args.action] if index==len(accepted) else []
        for mode in modes:
            accepted.append(runner.execute(mode,accepted[-1] if accepted else None,check))
        if len(accepted)==3:runner.finish(accepted,check)
        else:print(json.dumps({'status':'ACCEPTED_PREFIX','accepted_steps':len(accepted),'new_commands':len(modes)}))


if __name__=='__main__':
    main()
