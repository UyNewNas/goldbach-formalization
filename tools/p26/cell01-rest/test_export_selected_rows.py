#!/usr/bin/env python3
"""Synthetic selection/runtime regressions only: no Lean, Git or cloud calls."""
from pathlib import Path
import ast
import copy
import hashlib
import importlib.util
import json
import shlex
import sys
import tarfile
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('selected_export', HERE / 'export_selected_rows.py')
selected = importlib.util.module_from_spec(spec)
spec.loader.exec_module(selected)


def fixture(scenario):
    verifier = {'batches': {'C': list(range(98, 144))}, 'targets': [
        {'original_ordinal': n, 'module': f'ImbalancedChen.P2OriginalSaving19Cell01Row{n:03d}Finite'}
        for n in range(2, 144)]}
    prefix = scenario == 'c-prefix-budget-pause'
    rows = list(range(98, 107)) if prefix else list(range(107, 144))
    run = {'batch_label': 'C' if prefix else None,
           'selected_ordinals': list(range(98, 144)) if prefix else rows,
           'attempt': 'synthetic-selection'}
    records = []
    for n in rows:
        module = f'ImbalancedChen.P2OriginalSaving19Cell01Row{n:03d}Finite'
        for mode in selected.MODES:
            records.append({'module': module, 'mode': mode, 'status': 'succeeded',
                'receipt': {'path': f'/synthetic/verification/synthetic-selection/{module.split(".")[-1]}/{mode}-result.json',
                            'bytes': 100, 'sha256': 'a' * 64}})
    terminal = {**copy.deepcopy(run), 'status': 'BUDGET_PAUSE' if prefix else 'succeeded',
                'batch_complete': not prefix, 'completed_rows': rows, 'records': records,
                'frozen_inputs_unchanged': True}
    if prefix:
        terminal.update(where='before_row', module=None, mode=None, remaining_ordinals=list(range(107, 144)))
    else:
        terminal['accepted_targets'] = 37
    markers = {'PARTIAL.json' if prefix else 'SUCCESS.json'}
    return run, terminal, verifier, markers


def choose(scenario, values):
    run, terminal, verifier, markers = values
    return selected.select_acceptance(run, terminal, verifier, scenario, markers)


def mcp_fixture(scenario):
    prefix = scenario == 'c-prefix-budget-pause'
    stage = Path('/workspace/p26-continuation-59264dd64286/' +
                 ('cell01-batch-C-finite-v2' if prefix else 'cell01-rest-finite-v2'))
    attempt = 'p1-cell01-batch-C-v2-canonical1' if prefix else 'cell01-rows107-143-v2'
    argv = ['python3', '-B', str(stage / selected.TOOL / 'Cell01Batch_verify.py'), '--stage', str(stage),
            '--cache-root', '/workspace/p26-continuation-59264dd64286/' +
            ('cell01-finite-suppliers-P1' if prefix else 'cell01-row000')]
    if prefix:
        argv += ['--toolchain-bin', '/workspace/toolchains/lean-4.33.0-rc1-linux/bin',
                 '--mathlib', '/workspace/goldbach-formalization/.lake/packages/mathlib',
                 '--mathlib-packages', '/workspace/goldbach-formalization/.lake/packages',
                 '--batch', 'C', '--attempt', attempt,
                 '--task-budget-seconds', '600', '--row-start-reserve-seconds', '90']
    else:
        argv += ['--rows', *map(str, range(107, 144)), '--attempt', attempt]
    task = {'status': 'succeeded', 'exit_code': 0, 'output_truncated': False,
            'command': shlex.join(argv), 'task_id': 'synthetic-only', 'runtime_seconds': 1.25,
            'memory_peak_bytes' if prefix else 'peak_memory_bytes': 1024}
    if prefix:
        task['memory_peak_source'] = 'maximum of sampled aggregate RSS and wait4 per-process high-water RSS'
    return task, stage, attempt, argv


class SelectionBoundaries(unittest.TestCase):
    def test_exact_two_ranges_and_record_prefix(self):
        for scenario, count in [('c-prefix-budget-pause', 9), ('c-tail-success', 37)]:
            values = fixture(scenario)
            got = choose(scenario, values)
            self.assertEqual(len(got['ordinals']), count)
            self.assertEqual(len(values[1]['records']), count * 3)
            self.assertFalse(got['full_C_batch_claimed'])
            self.assertFalse(got['cross_context_aggregation_performed'])
            self.assertEqual(got['batch_complete'], scenario == 'c-tail-success')
            # The exact frozen verifier has a separate schema for reused steps.
            record = values[1]['records'][0]
            record['reused_successful_receipt'] = record.pop('receipt')
            record.pop('status')
            self.assertEqual(choose(scenario, values), got)

    def test_reject_scope_status_marker_and_incomplete_triple(self):
        mutations = {
            'false_success_on_prefix': lambda r, t, v, m: t.update(status='succeeded'),
            'partial_claims_complete': lambda r, t, v, m: t.update(batch_complete=True),
            'wrong_completed_range': lambda r, t, v, m: t.update(completed_rows=list(range(98, 106))),
            'remaining_omits_107': lambda r, t, v, m: t.update(remaining_ordinals=list(range(108, 144))),
            'started_an_incomplete_next_row': lambda r, t, v, m: t.update(where='before_mode', module='row107', mode='kernel'),
            'failed_marker_present': lambda r, t, v, m: m.add('STOPPED.json'),
            'contradictory_success_marker': lambda r, t, v, m: m.add('SUCCESS.json'),
            'missing_final_owned': lambda r, t, v, m: t['records'].pop(),
            'reordered_modes': lambda r, t, v, m: t['records'].reverse(),
            'extra_record': lambda r, t, v, m: t['records'].append(copy.deepcopy(t['records'][-1])),
            'failed_record': lambda r, t, v, m: t['records'][0].update(status='failed'),
            'ambiguous_ref': lambda r, t, v, m: t['records'][0].update(reused_successful_receipt=t['records'][0]['receipt']),
            'relative_ref_path': lambda r, t, v, m: t['records'][0]['receipt'].update(path='relative.json'),
            'unknown_record_metadata': lambda r, t, v, m: t['records'][0].update(error='failure'),
            'run_terminal_disagree': lambda r, t, v, m: r.update(attempt='wrong'),
            'wrong_manifest_ordinal': lambda r, t, v, m: v['targets'][96].update(module='ImbalancedChen.WRONG'),
            'overstated_prefix_count': lambda r, t, v, m: t.update(accepted_targets=46),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                values = fixture('c-prefix-budget-pause')
                mutate(*values)
                with self.assertRaises(ValueError):
                    choose('c-prefix-budget-pause', values)
        for label, mutate in {
            'tail_label_C': lambda r, t, v, m: (r.update(batch_label='C'), t.update(batch_label='C')),
            'tail_36_targets': lambda r, t, v, m: t.update(accepted_targets=36),
            'tail_incomplete': lambda r, t, v, m: t.update(batch_complete=False),
            'tail_partial_marker': lambda r, t, v, m: m.add('PARTIAL.json'),
            'tail_has_remaining': lambda r, t, v, m: t.update(remaining_ordinals=[143]),
            'tail_run_selects_C46': lambda r, t, v, m: (r.update(selected_ordinals=list(range(98, 144))), t.update(selected_ordinals=list(range(98, 144)))),
        }.items():
            with self.subTest(label=label):
                values = fixture('c-tail-success')
                mutate(*values)
                with self.assertRaises(ValueError):
                    choose('c-tail-success', values)

    def test_mcp_explicit_argv_binding_and_rejections(self):
        for scenario in selected.SCENARIOS:
            task, stage, attempt, argv = mcp_fixture(scenario)
            command = selected.recorded_command(task, stage, attempt, scenario)
            self.assertEqual(command.batch, 'C' if scenario.endswith('pause') else None)
        bad_argv = {
            'batch_instead_of_explicit_tail': lambda a: a[:a.index('--rows')] + ['--batch', 'C', '--attempt', 'cell01-rows107-143-v2'],
            'shell_expansion': lambda a: a[:a.index('--rows') + 1] + ['$(seq', '107', '143)', '--attempt', 'cell01-rows107-143-v2'],
            'duplicate_row': lambda a: a[:a.index('--attempt')] + ['143'] + a[a.index('--attempt'):],
            'duplicate_flag': lambda a: a + ['--attempt', 'cell01-rows107-143-v2'],
            'unknown_flag': lambda a: a + ['--trust-anything'],
            'different_attempt': lambda a: a[:-1] + ['wrong'],
            'wrapper_shell': lambda a: ['sh', '-c', shlex.join(a)],
            'illegal_task_budget': lambda a: a + ['--task-budget-seconds', '0'],
        }
        for label, mutate in bad_argv.items():
            with self.subTest(label=label):
                task, stage, attempt, argv = mcp_fixture('c-tail-success')
                task['command'] = shlex.join(mutate(argv))
                with self.assertRaises(ValueError):
                    selected.recorded_command(task, stage, attempt, 'c-tail-success')
        task, stage, attempt, _ = mcp_fixture('c-prefix-budget-pause')
        task['exit_code'] = 1
        with self.assertRaises(ValueError):
            selected.recorded_command(task, stage, attempt, 'c-prefix-budget-pause')

    def test_unaccounted_failed_or_incomplete_attempt_file(self):
        with tempfile.TemporaryDirectory(prefix='selected-evidence-test-') as name:
            stage = Path(name)
            root = stage / 'verification/prefix'
            root.mkdir(parents=True)
            audit = selected.Audit(stage)
            for filename in ('RUN.json', 'PARTIAL.json'):
                path = root / filename
                path.write_text('{}')
                audit.add(path, 'synthetic-context')
            selected.exact_attempt_inventory(root, audit)
            extra = root / 'ImbalancedChen.P2OriginalSaving19Cell01Row107Finite/normal-result.json'
            extra.parent.mkdir()
            extra.write_text('{"status": "failed"}')
            with self.assertRaisesRegex(ValueError, 'unaccounted'):
                selected.exact_attempt_inventory(root, audit)

    def test_actual_runtime_paths_git_metadata_and_metric_field_identity(self):
        with tempfile.TemporaryDirectory(prefix='selected-runtime-test-') as name:
            root = Path(name)
            for label in ('p1', 'p3'):
                toolchain = root / label / 'toolchain'
                mathlib = root / label / 'mathlib'
                packages = root / label / 'packages'
                for p in (toolchain, mathlib, packages):
                    p.mkdir(parents=True)
                task, stage, attempt, _ = mcp_fixture('c-prefix-budget-pause' if label == 'p1' else 'c-tail-success')
                command = selected.recorded_command(task, stage, attempt,
                    'c-prefix-budget-pause' if label == 'p1' else 'c-tail-success')
                command.toolchain_bin, command.mathlib, command.mathlib_packages = map(str, (toolchain, mathlib, packages))
                run = {'cache_root': command.cache_root, 'wall_limit_seconds': command.wall_seconds,
                       'rss_limit_bytes': command.rss_gib * 1024**3, 'task_budget_seconds': command.task_budget_seconds,
                       'lean_binary': {'path': str(toolchain / 'lean')},
                       'leanchecker_binary': {'path': str(toolchain / 'leanchecker')},
                       'mathlib_packages_root': str(packages)}
                self.assertEqual(selected.bind_recorded_runtime(command, run), mathlib)
                bad = copy.deepcopy(run)
                bad['leanchecker_binary']['path'] = '/wrong/leanchecker'
                with self.assertRaises(ValueError):
                    selected.bind_recorded_runtime(command, bad)
                measurements = selected.mcp_measurements(task)
                field = 'memory_peak_bytes' if label == 'p1' else 'peak_memory_bytes'
                self.assertEqual(measurements['proof_MCP_peak_memory_field'], field)
                self.assertEqual(measurements['proof_MCP_memory_peak_source'], task.get('memory_peak_source'))
                task['memory_peak_bytes' if label == 'p3' else 'peak_memory_bytes'] = 1024
                with self.assertRaises(ValueError):
                    selected.mcp_measurements(task)
                gitdir = mathlib / '.git'
                gitdir.mkdir()
                head = gitdir / 'HEAD'
                head.write_text(selected.MATHLIB_COMMIT + '\n')
                audit = selected.Audit(root)
                self.assertEqual(selected.read_git_commit(mathlib, audit)['commit'], selected.MATHLIB_COMMIT)
                head.write_text('0' * 40 + '\n')
                with self.assertRaisesRegex(ValueError, 'changed'):
                    audit.unchanged()
                head.write_text('ref: refs/heads/frozen\n')
                (gitdir / 'packed-refs').write_text(selected.MATHLIB_COMMIT + ' refs/heads/frozen\n')
                self.assertEqual(selected.read_git_commit(mathlib, selected.Audit(root))['commit'], selected.MATHLIB_COMMIT)
                loose = gitdir / 'refs/heads/frozen'
                loose.parent.mkdir(parents=True)
                loose.write_text(selected.MATHLIB_COMMIT + '\n')
                self.assertEqual(selected.read_git_commit(mathlib, selected.Audit(root))['commit'], selected.MATHLIB_COMMIT)

    def test_prefix_archive_reports_only_nine_objects_and_incomplete_C(self):
        with tempfile.TemporaryDirectory(prefix='selected-export-test-') as name:
            root = Path(name)
            stage = root / 'stage'
            stage.mkdir()
            audit = selected.Audit(stage)
            scope = choose('c-prefix-budget-pause', fixture('c-prefix-budget-pause'))
            rows = []
            for n in scope['ordinals']:
                module = f'ImbalancedChen.P2OriginalSaving19Cell01Row{n:03d}Finite'
                path = stage / 'objects' / (module.replace('.', '/') + '.olean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(f'SYNTHETIC-OBJECT-{n}'.encode())
                audit.add(path, 'synthetic-only-not-a-Lean-object')
                rows.append({'module': module, 'ordinal': n})
            task, _, _, _ = mcp_fixture('c-prefix-budget-pause')
            report = {**scope, 'attempt': 'synthetic-only', 'accepted_targets': 9, 'accepted_steps': 27,
                'rows': rows, 'owned_declarations': 9 * 292, 'new_target_object_bodies': 9,
                'step_counts': {mode: 9 for mode in selected.MODES}, 'newly_executed_steps': 27,
                'reused_steps': 0, 'axioms_union': sorted(selected.ALLOWED), 'old_suppliers': 399,
                'supplier_files_rehashed_in_cache_and_stage': 1596, 'input_fingerprint_files_checked': 1939,
                'runtime_context_sha256': 'b' * 64, 'step_elapsed_sum_seconds': 1.0,
                'sampled_Lean_process_tree_peak_bytes': 1024, 'old_supplier_object_bodies_included': False,
                'P2_6_complete': False, 'MCP_measurements': selected.mcp_measurements(task),
                'fixture_is_synthetic_not_proof_acceptance': True}
            output = root / 'output'
            summary = selected.export(audit, report, output)
            self.assertTrue(summary['archive_readback_all_members_passed'])
            for filename in ('SUMMARY.json', 'EXPORT_MANIFEST.json', 'INDEPENDENT_REVIEW.json'):
                value = json.loads((output / filename).read_text())
                self.assertFalse(value['batch_complete'])
                self.assertFalse(value['full_C_batch_claimed'])
                self.assertFalse(value['cross_context_aggregation_performed'])
                self.assertEqual(value['ordinals'], list(range(98, 107)))
                self.assertEqual(value['remaining_ordinals'], list(range(107, 144)))
                self.assertEqual(value['accepted_targets'], 9)
                self.assertEqual(value['accepted_steps'], 27)
            with tarfile.open(output / 'evidence.tar.xz', 'r:xz') as archive:
                members = archive.getmembers()
                self.assertTrue(all(m.isreg() for m in members))
                self.assertEqual(sum(m.name.startswith('objects/') for m in members), 9)
                self.assertTrue(all('Row107Finite' not in m.name for m in members))
            with self.assertRaisesRegex(ValueError, 'replace'):
                selected.export(audit, report, output)

    def test_accepted_v1_bytes_and_strict_core_preserved(self):
        old_path = HERE / 'export_batch_evidence.py'
        old = old_path.read_text()
        new = (HERE / 'export_selected_rows.py').read_text()
        self.assertEqual(hashlib.sha256(old_path.read_bytes()).hexdigest(), selected.V1_EXPORTER_SHA256)
        def definitions(text):
            return {node.name: node for node in ast.parse(text).body if isinstance(node, (ast.FunctionDef, ast.ClassDef))}
        old_defs, new_defs = definitions(old), definitions(new)
        for name in ('need', 'canonical', 'pin', 'fp', 'same', 'read', 'body', 'imports', 'Audit', 'load_reviewed_driver'):
            with self.subTest(unchanged_function=name):
                self.assertEqual(ast.dump(old_defs[name]), ast.dump(new_defs[name]))
        # Only the current host's binary provider changes in the historical join.
        expected_history = ast.get_source_segment(old, old_defs['historical_boundary'])
        expected_history = expected_history.replace('def historical_boundary(stage, registry, audit, driver):',
            'def historical_boundary(stage, registry, audit, driver, current_runtime):')
        expected_history = expected_history.replace(
            "need(same(prior_run[key], fp('/toolchains/bin/' + ('lean' if key == 'lean_binary' else 'leanchecker'))), 'Recurrence compiler byte identity differs')",
            "need(same(prior_run[key], audit.watch(current_runtime[key]['path'], current_runtime[key], exact_path=True)),\n             'Recurrence compiler byte identity differs')")
        self.assertEqual(ast.dump(ast.parse(expected_history).body[0]), ast.dump(new_defs['historical_boundary']))
        # Exact receipt validation, closure traversal, full-owned parsing and row chain checks are unchanged.
        start = '    selected_objects, rows, steps, union = {}, [], [], set()\n'
        stop = '    proof_mcp = read(mcp_path)\n'
        old_core = old[old.index(start):old.index(stop)]
        new_core = new[new.index(start):new.index('    exact_attempt_inventory(root, audit)')]
        self.assertEqual(old_core, new_core)
        # Packing and readback keep the already accepted regular-payload implementation.
        start = '    output.mkdir(parents=True, exist_ok=False)\n'
        stop = '    for name, data in [(\'EXPORT_MANIFEST.json\''
        self.assertEqual(old[old.index(start):old.index(stop)], new[new.index(start):new.index(stop)])


if __name__ == '__main__':
    unittest.main(verbosity=2)
