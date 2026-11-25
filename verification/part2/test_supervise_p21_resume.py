"""Synthetic scheduler tests. No Lean processes or remote repositories."""
from contextlib import chdir, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import supervise_p21_resume as s


def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


class Supervision(unittest.TestCase):
    def setUp(self):
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        change = chdir(d.name)
        change.__enter__()
        self.addCleanup(change.__exit__, None, None, None)
        self.root = Path(d.name)
        self.enterContext(patch.object(s, "ROOT", self.root))

    def test_startup_reports_real_failures_once_excludes_provisional_postcheck(self):
        with redirect_stdout(StringIO()) as out:
            log = s.PRIVATE / "failed.log"
            put(log, "concrete failure")
            r = {"exit_code": 1, "log": str(log)}
            pending = {"exit_code":125, "external_check":{"status":"PENDING_BATCH_POSTCHECK"}}
            put(s.RECORDS, {"A": r, "B": dict(pending, attempts=[{"exit_code":0,"log":str(log)}]),
                            "C":dict(pending, attempts=[{"exit_code":1,"log":str(log)}])})
            put(s.AUDITS / "A/latest.json", {"error":"audit failed", "audit":{"log":str(log)}, "replay":{"log":str(log)}})
            monitor = s.Failures()
            monitor.poll(["A", "B", "C"])
            monitor.poll(["A", "B", "C"])
            self.assertEqual(out.getvalue().count("FAIL_LOG"), 4)
            self.assertIn("FAIL_RECEIPT C compile 1 registry 125", out.getvalue())
            self.assertEqual(out.getvalue().count("concrete failure"), 4)

    def test_actual_strict_driver_summaries_reschedule_pending_and_recheck_success_receipts(self):
        b = s.BUCHSTAB
        names = ["A", "B", b]
        for n in names:
            put(s.AUDITS / n / "latest.json", {"accepted":True, "stale_environment":"must recheck"})
        put(s.TARGETS, {"modules":[{"module":n} for n in names]})
        snapshots = [self.root / "base", self.root / "ext"]
        for p in snapshots:
            put(p, "test")
        normal, audit, sync = [], [], []
        def run(argv, *_):
            if argv[1] == str(s.NORMAL):
                targets = argv[2:argv.index("--workers")]
                normal.append(targets)
                pending = ["B"] if targets == ["A", "B"] else []
                code = 2 if pending else 0
                return code, {"roots":targets, "total":len(targets), "successful_closure":len(targets)-len(pending),
                              "pending":pending, "failed_or_blocked":[], "exit_code":code, "complete":not pending}
            self.assertEqual(argv[1], str(s.AUDIT))
            batch = argv[2:argv.index("--memory-mb")]
            audit.extend(batch)
            return 0, {"modules":{n:{"accepted":True, "reused":True} for n in batch},
                       "requested":len(batch), "accepted":len(batch), "all_accepted":True}
        def update():
            sync.append(1)
            return str(len(sync))   # Every new head is docs-only, with the same meaningful fingerprint.
        with patch.object(s, "identity"), patch.object(s, "update", update), patch.object(s, "snapshots", return_value=snapshots), \
             patch.object(s, "selection", return_value=([["A", "B"],[b]], names, {n:{n} for n in names},"same")), \
             patch.object(s, "run", run), patch.object(s.signal, "setitimer"), patch.object(s.sys,"argv",["test"]), \
             redirect_stdout(StringIO()) as out:
            s.main()
        self.assertEqual(normal, [["A", "B"], ["B"], [b]])
        self.assertCountEqual(audit, names)
        self.assertIn("READY_FOR_EXPORT", out.getvalue())

    def test_missing_driver_summary_is_a_stop(self):
        with self.assertRaisesRegex(ValueError, "exit 1 without a complete progress summary"):
            s.progress(["A"], {"A":{"A"}}, {}, 1)

    def test_different_checkout_branch_or_repository_refused(self):
        origin = "https://github.com/UyNewNas/goldbach-formalization.git"
        for root, branch, url in [(str(self.root.parent), "refs/heads/"+s.BRANCH, origin),
                                  (str(self.root), "HEAD", origin),
                                  (str(self.root), "refs/heads/wrong", origin),
                                  (str(self.root), "refs/heads/"+s.BRANCH, origin.replace("UyNewNas", "other"))]:
            with self.subTest(root=root, branch=branch, url=url), patch.object(s,"git",side_effect=[root,branch,url]):
                with self.assertRaises(ValueError):
                    s.identity()

    def test_budget_during_source_check_halts_before_launch(self):
        put(s.TARGETS, {"modules":[{"module":"A"}]})
        with patch.object(s, "identity"), patch.object(s, "snapshots"), patch.object(s, "update", return_value="head"), \
             patch.object(s, "selection", side_effect=s.BudgetExpired("source check")), \
             patch.object(s, "run") as launch, patch.object(s.signal, "setitimer"), patch.object(s.sys,"argv",["test"]):
            with self.assertRaises(s.BudgetExpired):
                s.main()
            launch.assert_not_called()
        with patch.object(s.subprocess, "Popen") as process:
            with self.assertRaises(s.BudgetExpired):
                s.run(["inert", "driver"], None, [], 0)
            process.assert_not_called()

    def test_stops_during_spawn_or_before_reader_start_reap_the_owned_group(self):
        for when in ("inside_popen", "reader_start"):
            child = Mock(pid=123, stdout=StringIO(""))
            def spawn(*args, **kwargs):
                if when == "inside_popen":
                    s.signal.raise_signal(s.signal.SIGALRM)
                return child
            with self.subTest(when=when), patch.object(s.subprocess, "Popen", spawn), \
                 patch.object(s.threading.Thread, "start", side_effect=s.BudgetExpired("late")), \
                 patch.object(s.os, "killpg") as kill, redirect_stdout(StringIO()):
                with self.assertRaises(s.BudgetExpired):
                    s.run(["inert", "driver"], None, [], s.time.monotonic() + 60)
                kill.assert_called_once_with(123, s.signal.SIGKILL)
                child.wait.assert_called_once_with()

    def test_wrong_base_digest_or_redirected_extension_refused(self):
        base = self.root / "base"
        put(base, {"modules":dict.fromkeys(range(515))})
        self.enterContext(patch.object(s, "BASE", base))
        with self.assertRaisesRegex(ValueError, "515-provider"):
            s.snapshots()
        self.enterContext(patch.object(s, "BASE_SHA", s.sha(base)))
        helper = s.TOOLS / "extend_p21_buchstab_native_snapshot.py"
        put(helper, "pinned")
        dest = s.PRIVATE / "p21-buchstab-native" / s.BASE_SHA / s.sha(helper)
        elsewhere = self.root / "elsewhere"
        put(elsewhere, {"modules":dict.fromkeys(range(518))})
        dest.mkdir(parents=True)
        (dest / "EXTERNAL_SNAPSHOT.json").symlink_to(elsewhere)
        put(dest / "QUALIFICATION.json", {"status":"ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED"})
        with self.assertRaisesRegex(ValueError, "controlled Buchstab"):
            s.snapshots()

    def test_failed_subprocess_only_held_on_exact_strict_snapshot_and_log(self):
        name = "A"
        checker = "/test/leanchecker"
        log = (s.AUDITS / name / "attempt-001/replay.log").resolve()
        put(log, "failed")
        lean = self.root / "lean"
        put(lean, "inert")
        frozen = {"project":{name:{"source_sha256":"s","object_sha256":"o"}}, "leanchecker_sha256":"c",
                  "template_sha256":"t","external_snapshot":{"context":"old"}}
        receipt = {"accepted":False, "module":name, "error":"failed", "source_sha256":"s","object_sha256":"o",
                   "input_snapshot":frozen,"input_sha256":s.key(frozen), "replay_binding":frozen,
                   "compile_closure_signature":"cs","replay":{"exit_code":1,"inputs_unchanged":True,
                       "command":[checker,"--verbose",name],"log":str(log),"log_sha256":s.sha(log)}}
        put(s.AUDITS / name / "latest.json", receipt)
        put(s.RECORDS, {name:{"closure_signature":"cs"}})
        live = Mock(return_value=frozen)
        audit = SimpleNamespace(LEAN=str(lean), LEANCHECKER=checker, MATHLIB="/test", PIN="pin",
                                project_nodes=Mock(return_value={}),snapshot=live,json_digest=s.key,
                                replay_context=lambda x:x,verify_compilation=Mock())
        ext = SimpleNamespace(ExternalSnapshot=Mock(return_value=SimpleNamespace(modules={},verify=Mock())),
                              mark_project_nodes=Mock())
        def matched():
            with redirect_stdout(StringIO()) as out:
                s.identical_failures(self.root/"snap", [name])
            return json.loads(out.getvalue())["identical_failures"]
        with patch.dict(s.sys.modules,run_winner9_private_audit=audit,winner9_external_snapshot=ext), \
             patch.object(s,"git",return_value="pin"), patch.object(s.subprocess,"check_output",return_value="version"):
            self.assertEqual(matched(), [name])
            live.return_value = dict(frozen, leanchecker_sha256="new")
            self.assertEqual(matched(), [])
            live.return_value = dict(frozen, external_snapshot={"context":"new"})
            self.assertEqual(matched(), [])
            live.return_value = frozen
            put(log, "changed log")
            self.assertEqual(matched(), [])


if __name__ == "__main__":
    unittest.main()
