"""Exercise the sparse fast-forward gate using two local Git repositories."""
from contextlib import chdir
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import supervise_p21_resume as s


def git(root, *args, data=None):
    return subprocess.check_output(["git", "-C", str(root), *args], input=data).decode().strip()


class SparseFF(unittest.TestCase):
    def setUp(self):
        tmp = self.enterContext(tempfile.TemporaryDirectory())
        self.work, self.donor = Path(tmp) / "worker", Path(tmp) / "donor"
        self.donor.mkdir()
        git(self.donor, "init", "-q", "-b", s.BRANCH)
        git(self.donor, "config", "user.name", "fixture")
        git(self.donor, "config", "user.email", "fixture@example.invalid")
        self.name = "history with spaces.json"
        (self.donor / self.name).write_text("old")
        git(self.donor, "add", self.name)
        git(self.donor, "commit", "-qm", "original")
        git(Path(tmp), "clone", "-q", str(self.donor), str(self.work))
        self.enterContext(chdir(self.work))
        self.enterContext(patch.object(s, "ROOT", self.work))
        # The production identity permits only the dedicated GitHub origin.
        # In this fixture Git performs its real fetch against a temporary local donor.
        self.enterContext(patch.object(s, "identity"))
        self.head = git(self.work, "rev-parse", "HEAD")
        oid = git(self.work, "rev-parse", "HEAD:" + self.name)
        manifest = s.PRIVATE / "P21_SPARSE_WORKTREE.json"
        self.result = s.PRIVATE / "P21_SPARSE_RESULT.json"
        manifest.parent.mkdir(parents=True)
        raw = json.dumps({"index":git(self.work, "rev-parse", "--git-path", "index"),
                          "candidates":[{"path":self.name,"git_blob":oid}]}).encode()
        manifest.write_bytes(raw)
        self.enterContext(patch.object(s, "SPARSE_SHA", hashlib.sha256(raw).hexdigest()))
        self.result.write_text(json.dumps({"manifest":str(self.work / manifest),"manifest_sha256":s.SPARSE_SHA,
                                           "skip_flags_oid_absence_verified":True,"new_head":self.head}))
        git(self.work, "update-index", "--skip-worktree", "--", self.name)
        Path(self.name).unlink()

    def publish(self, name="fix.lean"):
        (self.donor / name).write_text("new")
        git(self.donor, "add", name)
        git(self.donor, "commit", "-qm", "update")
        return git(self.donor, "rev-parse", "HEAD")

    def rejected(self, message, want=None):
        with self.assertRaisesRegex(ValueError, message):
            s.update(expected=want, require_sparse=True)
        self.assertEqual(git(self.work, "rev-parse", "HEAD"), self.head)

    def test_disjoint_ff_pinned_then_advance_again(self):
        want = self.publish()
        self.assertEqual(s.update(expected=want, require_sparse=True), want)
        want = self.publish("another.lean")
        self.assertEqual(s.update(expected=want, require_sparse=True), want)
        self.assertFalse(os.path.lexists(self.name))
        self.assertTrue(git(self.work, "ls-files", "-v", "--", self.name).startswith("S "))

    def test_changed_candidate_rejected(self):
        self.publish(self.name)
        self.rejected("changes archived")

    def test_renamed_candidate_rejected(self):
        git(self.donor, "mv", self.name, "renamed")
        git(self.donor, "commit", "-qm", "rename")
        self.rejected("changes archived")

    def test_flag_loss_rejected(self):
        git(self.work, "update-index", "--no-skip-worktree", "--", self.name)
        self.rejected("Sparse index differs")

    def test_changed_index_oid_rejected(self):
        oid = git(self.work, "hash-object", "-w", "--stdin", data=b"other")
        git(self.work, "update-index", "--cacheinfo", "100644", oid, self.name)
        git(self.work, "update-index", "--skip-worktree", "--", self.name)
        self.rejected("Sparse index differs")

    def test_reappearing_entry_rejected(self):
        Path(self.name).symlink_to("missing-target")
        self.rejected("Unexpected sparse entry")

    def test_result_binding_rejected(self):
        self.result.write_text('{"manifest_sha256":"incorrect"}')
        self.rejected("Unexpected sparse recovery")

    def test_mismatching_pin_rejected_before_ff(self):
        self.publish()
        self.rejected("differs from expected", self.head)
