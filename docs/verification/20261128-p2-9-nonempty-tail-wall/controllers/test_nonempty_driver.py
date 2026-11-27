import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class NonemptyDriverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).with_name("run_nonempty.py")
        assert path.is_file(), "The single-target driver has not been implemented"
        spec = importlib.util.spec_from_file_location("nonempty_driver", path)
        cls.d = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.d)

    def test_merge_rejects_different_bytes_or_paths_for_same_part(self):
        row = {"module": "Mathlib.A", "facet": ".olean", "identity": {
            "path": "/a/A.olean", "bytes": 1, "sha256": "a" * 64}}
        self.assertEqual(len(self.d.merge_parts([row], [row])), 1)
        for field, value in (("sha256", "b" * 64), ("path", "/b/A.olean")):
            bad = {**row, "identity": {**row["identity"], field: value}}
            with self.assertRaisesRegex(self.d.VerificationError, "conflict"):
                self.d.merge_parts([row], [bad])

    def test_new_directory_and_writes_never_overwrite_or_follow_symlinks(self):
        with tempfile.TemporaryDirectory() as raw:
            parent = Path(raw)
            base = parent / "new"
            self.d.claim_base(base, False)
            target = base / "file"
            self.d.write_exact(target, b"safe")
            self.d.write_exact(target, b"safe")
            with self.assertRaises(self.d.VerificationError):
                self.d.claim_base(base, False)
            with self.assertRaises(self.d.VerificationError):
                self.d.write_exact(target, b"changed")
            linked = base / "link"
            linked.symlink_to(target)
            with self.assertRaises(self.d.VerificationError):
                self.d.write_exact(linked, b"safe")
            self.assertEqual(target.read_bytes(), b"safe")

    def test_exact_source_imports_and_configuration_only_change_target(self):
        text = "import ImbalancedChen.A\nimport Mathlib.B\n\nnamespace Example\n"
        self.assertEqual(self.d.source_imports(text), ["ImbalancedChen.A", "Mathlib.B"])
        original = ('name = "p29"\n[[lean_lib]]\nname = "ImbalancedChen"\n'
                    'roots = ["' + self.d.OLD_TARGET + '"]\n'
                    'globs = ["' + self.d.OLD_TARGET + '"]\n'
                    '[[require]]\nname = "mathlib"\n')
        changed = self.d.adapt_lakefile(original.encode())
        self.assertEqual(changed.decode(), original.replace(self.d.OLD_TARGET, self.d.TARGET))
        with self.assertRaises(self.d.VerificationError):
            self.d.adapt_lakefile(original.replace('globs = [', 'other = [').encode())

    def test_identity_rehash_detects_same_path_mutation(self):
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / "A.olean"
            p.write_bytes(b"abc")
            expected = {"path": str(p), "bytes": 3, "sha256": hashlib.sha256(b"abc").hexdigest()}
            self.assertEqual(self.d.check_identity(expected)["sha256"], expected["sha256"])
            p.write_bytes(b"abd")
            with self.assertRaisesRegex(self.d.VerificationError, "sha256"):
                self.d.check_identity(expected)

    def test_unknown_parts_are_reported_without_becoming_authorities(self):
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / "B.olean"
            p.write_bytes(b"new")
            rows = [{"module": "Mathlib.B", "is_module": False, "direct_imports": [],
                     "parts": [{"path": str(p), "resolved_path": str(p)}]}]
            result = self.d.bind_parts(rows, {})
            self.assertEqual(result["parts"], [])
            self.assertEqual(result["missing"][0]["module"], "Mathlib.B")
            self.assertEqual(result["missing"][0]["facet"], ".olean")
            self.assertEqual(result["missing"][0]["identity"]["sha256"], hashlib.sha256(b"new").hexdigest())

    def test_known_part_must_resolve_to_exact_original_path(self):
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / "A.olean"
            p.write_bytes(b"abc")
            identity = {"path": str(p), "bytes": 3, "sha256": hashlib.sha256(b"abc").hexdigest()}
            auth = {("Mathlib.A", ".olean"): {"module": "Mathlib.A", "facet": ".olean", "identity": identity}}
            rows = [{"module": "Mathlib.A", "is_module": False, "direct_imports": [],
                     "parts": [{"path": str(p), "resolved_path": str(p)}]}]
            self.assertEqual(len(self.d.bind_parts(rows, auth)["parts"]), 1)
            q = Path(raw) / "other" / "A.olean"
            q.parent.mkdir()
            q.write_bytes(b"abc")
            rows[0]["parts"] = [{"path": str(q), "resolved_path": str(q)}]
            with self.assertRaisesRegex(self.d.VerificationError, "path"):
                self.d.bind_parts(rows, auth)

    def test_postprobe_adds_only_target_and_preserves_every_old_identity(self):
        old = {"module": "Mathlib.A", "facet": ".olean", "identity": {"path": "/A", "bytes": 1, "sha256": "a" * 64}}
        target = {"module": self.d.TARGET, "facet": ".olean", "identity": {"path": "/T", "bytes": 2, "sha256": "b" * 64}}
        self.d.compare_pre_post([old], [old, target])
        for after in ([target], [old, {**target, "facet": ".ir"}], [{**old, "identity": {**old["identity"], "bytes": 2}}, target]):
            with self.assertRaises(self.d.VerificationError):
                self.d.compare_pre_post([old], after)

    def test_successful_stage_is_reused_and_a_failed_normal_is_not_rerun(self):
        with tempfile.TemporaryDirectory() as raw:
            d = self.d
            d.out = Path(raw)
            d.root = Path(raw) / "project"
            d.runs = []
            d.stage = lambda *a, **kw: self.fail("A completed or failed normal stage must not be repeated")
            log = d.out / "normal-build.log"
            log.write_bytes(b"")
            process = {"stage": "normal-build", "command": ["lean", "A.lean"], "cwd": str(d.root),
                       "exit_code": 0, "log_path": str(log), "log_sha256": hashlib.sha256(b"").hexdigest()}
            (d.out / "normal-build-process.json").write_text(json.dumps(process))
            self.assertEqual(d.run_stage_once("normal-build", ["lean", "A.lean"])["exit_code"], 0)
            process["exit_code"] = 1
            (d.out / "normal-build-process.json").write_text(json.dumps(process))
            with self.assertRaises(self.d.VerificationError):
                d.run_stage_once("normal-build", ["lean", "A.lean"])

    def test_relocation_preserves_bytes_and_cannot_hide_changed_original(self):
        with tempfile.TemporaryDirectory() as raw:
            d = self.d
            original = Path(raw) / "old" / "A.olean"
            selected = Path(raw) / "A.olean"
            selected.write_bytes(b"accepted")
            pin = {"path": str(original), "bytes": 8, "sha256": hashlib.sha256(b"accepted").hexdigest()}
            d.relocations = {str(original): {"original": pin, "selected": {**pin, "path": str(selected)}, "provenance": {"member": "A.olean"}}}
            try:
                self.assertEqual(d.select_identity(pin)["path"], str(selected))
                original.parent.mkdir()
                original.write_bytes(b"changed!")
                with self.assertRaisesRegex(d.VerificationError, "sha256"):
                    d.select_identity(pin)
            finally:
                d.relocations = {}

    def test_all_direct_project_headers_are_checked_against_bound_sources(self):
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / "A.lean"
            p.write_text("import ImbalancedChen.B\nimport Mathlib.C\n")
            rows = [{"module": "ImbalancedChen.A", "is_module": False,
                     "direct_imports": ["Init", "ImbalancedChen.B", "Mathlib.C"]}]
            self.d.check_headers(rows, {"ImbalancedChen.A"}, {"ImbalancedChen.A": {"path": str(p)}}, {})
            rows[0]["direct_imports"].remove("ImbalancedChen.B")
            with self.assertRaisesRegex(self.d.VerificationError, "header/source"):
                self.d.check_headers(rows, {"ImbalancedChen.A"}, {"ImbalancedChen.A": {"path": str(p)}}, {})

    def test_guard_log_rejects_supplier_source_or_duplicate_target_call(self):
        with tempfile.TemporaryDirectory() as raw:
            d = self.d
            d.src = Path(raw) / "Target.lean"
            d.guardlog = Path(raw) / "guard.jsonl"
            row = {"tool": "lean", "cwd": raw, "input_args": [str(d.src)]}
            d.guardlog.write_text(json.dumps(row) + "\n")
            self.assertEqual(len(d.verify_guard_sources()), 1)
            for added in (row, {**row, "input_args": ["OldSupplier.lean"]}):
                d.guardlog.write_text(json.dumps(row) + "\n" + json.dumps(added) + "\n")
                with self.assertRaises(d.VerificationError):
                    d.verify_guard_sources()

    def test_resumed_setup_is_bound_to_the_original_created_state(self):
        check = getattr(self.d, "verify_setup_record", None)
        self.assertTrue(callable(check), "Resumed setup needs an immutable state binding")
        with tempfile.TemporaryDirectory() as raw:
            folder = Path(raw)
            state = folder / "state.json"
            log = folder / "runtime-setup.log"
            state.write_text('{"root":"fixed"}')
            log.write_text("prepared\n")
            record = {"exit_code": 0, "command": ["guard", "setup"],
                      "state_sha256": self.d.sha(state), "log_sha256": self.d.sha(log)}
            check(record, ["guard", "setup"], state, log)
            state.write_text('{"root":"changed"}')
            with self.assertRaises(self.d.VerificationError):
                check(record, ["guard", "setup"], state, log)

    def test_final_stability_includes_supplemental_standard_parts(self):
        check = getattr(self.d, "verify_final_part_stability", None)
        self.assertTrue(callable(check), "Every actually used supplemental part must survive the audits unchanged")
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / "Additional.olean"
            p.write_bytes(b"accepted")
            row = {"module": "Mathlib.Additional", "facet": ".olean",
                   "identity": {"path": str(p), "bytes": 8, "sha256": hashlib.sha256(b"accepted").hexdigest()},
                   "authority": "original_accepted_gate_graph"}
            check([row])
            p.write_bytes(b"modified")
            with self.assertRaisesRegex(self.d.VerificationError, "sha256"):
                check([row])

    def test_package_mapping_is_exact_manifest_bound_subset(self):
        merge = getattr(self.d, "merge_package_paths", None)
        self.assertTrue(callable(merge), "Explicit package paths need a manifest join")
        names = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph', 'LeanSearchClient', 'plausible']
        original = {name: '/workspace/goldbach-p2/.lake/packages/' + name for name in names}
        original['mathlib'] = '/workspace/compile-deps/mathlib'
        revisions = {name: str(i) * 40 for i, name in enumerate(names, 1)}
        rows = [{'name': name, 'original_path': original[name],
                 'selected_path': '/workspace/compile-deps/mathlib/.lake/packages/' + name,
                 'manifest_revision': revisions[name]} for name in names]
        document = {'schema': 'p29_exact_manifest_package_path_relocations_v1', 'mappings': rows}
        selected = merge(original, revisions, document)
        self.assertEqual(selected['mathlib'], original['mathlib'])
        self.assertEqual(selected['Qq'], '/workspace/compile-deps/mathlib/.lake/packages/Qq')
        for changed in ({**rows[0], 'original_path': '/wrong/Cli'},
                        {**rows[0], 'manifest_revision': '0' * 40},
                        {**rows[0], 'selected_path': '/unreviewed/Cli'}):
            with self.assertRaises(self.d.VerificationError):
                merge(original, revisions, {**document, 'mappings': [changed, *rows[1:]]})
        with self.assertRaises(self.d.VerificationError):
            merge(original, revisions, {**document, 'mappings': [rows[0], *rows]})

    def test_compiled_library_selection_keeps_old_q_q_and_only_moves_unused_cli(self):
        translate = getattr(self.d, "select_library_search_paths", None)
        self.assertTrue(callable(translate), "Package metadata relocation must not replace accepted library bytes")
        original = {'Cli': '/old/Cli', 'Qq': '/old/Qq'}
        selected = {'Cli': '/new/Cli', 'Qq': '/new/Qq'}
        paths = ['/project/lib', '/old/Cli/.lake/build/lib/lean', '/old/Qq/.lake/build/lib/lean', '/old/Cli-suffix/lib']
        self.assertEqual(translate(paths, original, selected),
                         ['/project/lib', '/new/Cli/.lake/build/lib/lean', '/old/Qq/.lake/build/lib/lean', '/old/Cli-suffix/lib'])

    def test_package_checkout_rejects_parent_git_identity_and_dirty_config(self):
        check = getattr(self.d, "verify_package_checkout", None)
        self.assertTrue(callable(check), "Selected package directory must itself be the fixed checkout")
        with tempfile.TemporaryDirectory() as raw:
            repo = Path(raw) / 'repo'
            repo.mkdir()
            subprocess.run(['git', 'init', '-q', str(repo)], check=True)
            (repo / 'lakefile.toml').write_text('name = "test"\n')
            subprocess.run(['git', '-C', str(repo), 'add', 'lakefile.toml'], check=True)
            subprocess.run(['git', '-C', str(repo), '-c', 'user.name=Local Test', '-c', 'user.email=test@example.invalid',
                            '-c', 'commit.gpgsign=false', 'commit', '-qm', 'fixture'], check=True)
            revision = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
            self.assertEqual(check(repo, revision)['revision'], revision)
            child = repo / 'cache-only'
            child.mkdir()
            with self.assertRaisesRegex(self.d.VerificationError, 'checkout root'):
                check(child, revision)
            (repo / 'lakefile.toml').write_text('name = "changed"\n')
            with self.assertRaisesRegex(self.d.VerificationError, 'configuration'):
                check(repo, revision)

    def test_historical_stat_change_is_revalidated_only_for_exact_original_bytes(self):
        with tempfile.TemporaryDirectory() as raw:
            d = self.d
            p = Path(raw) / 'A.olean'
            p.write_bytes(b'accepted')
            current = d.stamp(p)
            historical = current.copy()
            historical[1] += 1
            row = {'module': 'Mathlib.A', 'facet': '.olean', 'stat_snapshot': historical,
                   'identity': {'path': str(p), 'bytes': 8, 'sha256': hashlib.sha256(b'accepted').hexdigest()}}
            try:
                observed = d.relocate_part(row)
            except d.VerificationError as error:
                self.fail('Exact original bytes must establish a current stat baseline: ' + str(error))
            self.assertEqual(observed['stat_snapshot'], current)
            event = d.same_path_revalidations[str(p)]
            self.assertEqual(event['historical_stat_snapshot'], historical)
            self.assertEqual(event['current_stat_snapshot'], current)
            self.assertTrue(event['byte_identity_unchanged'])
            p.write_bytes(b'modified')
            with self.assertRaisesRegex(d.VerificationError, 'sha256'):
                d.relocate_part(row)

    def test_current_stat_change_after_normal_is_rejected_even_with_same_bytes(self):
        row = {'module': 'Mathlib.A', 'facet': '.olean', 'stat_snapshot': [1, 2, 3, 4, 5],
               'identity': {'path': '/A', 'bytes': 3, 'sha256': 'a' * 64}}
        target = {'module': self.d.TARGET, 'facet': '.olean', 'identity': {'path': '/T', 'bytes': 2, 'sha256': 'b' * 64}}
        changed = {**row, 'stat_snapshot': [1, 2, 3, 4, 6]}
        with self.assertRaises(self.d.VerificationError):
            self.d.compare_pre_post([row], [changed, target])

    def test_current_stat_change_during_audits_is_rejected_even_with_same_bytes(self):
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / 'A.olean'
            p.write_bytes(b'accepted')
            row = {'module': 'Mathlib.A', 'facet': '.olean', 'stat_snapshot': self.d.stamp(p),
                   'identity': {'path': str(p), 'bytes': 8, 'sha256': hashlib.sha256(b'accepted').hexdigest()}}
            self.d.verify_final_part_stability([row])
            stat = p.stat()
            os.utime(p, ns=(stat.st_atime_ns, stat.st_mtime_ns + 1000000))
            with self.assertRaises(self.d.VerificationError):
                self.d.verify_final_part_stability([row])


if __name__ == "__main__":
    unittest.main()
