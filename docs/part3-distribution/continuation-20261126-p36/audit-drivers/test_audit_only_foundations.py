"""Behavioral guards for the one fixed foundation audit continuation."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "audit_only_foundations", Path(__file__).with_name("audit_only_foundations.py"))
driver = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(driver)


def timeout_parent():
    compiler = "/toolchains/bin/lean"
    modules, commands = {}, []
    for module in driver.TARGETS:
        relative = module.replace(".", "/")
        command = [compiler, "-t0", "-j1", "-R", str(driver.PROJECT),
                   "-DwarningAsError=true", "-o",
                   str(driver.PROJECT / ".lake/p36-six-core-build/lib/lean" / (relative + ".olean")),
                   str(driver.PROJECT / (relative + ".lean"))]
        modules[module] = {"action": "compiled", "strict": True,
                           "exit_code": 0, "command": command}
        commands.append({"name": "compile-" + module, "exit_code": 0,
                         "command": command})
    for module in driver.TARGETS:
        commands.append({"name": "replay-" + module, "exit_code": 0,
                         "command": ["/toolchains/bin/leanchecker", "--verbose", module]})
    commands.append({"name": "owned-inventory-audit", "exit_code": 124,
                     "elapsed_seconds": driver.PARENT_AUDIT_ELAPSED,
                     "log": str(driver.RUN / "owned-inventory-audit.log"),
                     "command": [compiler, "-t0", "-j1", "-DwarningAsError=true",
                                 "-R", str(driver.RUN), str(driver.RUN / "P36OwnedAudit.lean")]})
    return {"status": "FAILED", "strict_owned": True,
            "targets": list(driver.TARGETS), "blockers": [],
            "compiler": {"path": compiler}, "modules": modules, "commands": commands,
            "planned_external_cache_mirrors": [], "external_cache_mirrors": {},
            "error": "owned-inventory-audit failed with exit 124; see "
                     + str(driver.RUN / "owned-inventory-audit.log") + "\n"
                     + "Runner: this runner's child exceeded its configured timeout.\n"}


class ParentTerminalTests(unittest.TestCase):
    def rejected(self, report):
        with self.assertRaises(RuntimeError):
            driver.validate_parent_terminal(report)

    def test_allows_exact_final_audit_timeout_after_strict_compile_and_replay(self):
        self.assertIsNone(driver.validate_parent_terminal(timeout_parent()))

    def test_rejects_other_failure_and_nonterminal_audit(self):
        original = timeout_parent()
        changed = deepcopy(original)
        changed["commands"][-1]["exit_code"] = 1
        self.rejected(changed)
        changed = deepcopy(original)
        changed["error"] = "Input or object changed during this run"
        self.rejected(changed)
        changed = deepcopy(original)
        changed["commands"].append({"name": "unexpected-followup", "exit_code": 0})
        self.rejected(changed)
        changed = deepcopy(original)
        changed["status"] = "COMPILED"
        self.rejected(changed)
        changed = deepcopy(original)
        changed["commands"][-1]["elapsed_seconds"] = 12.0
        self.rejected(changed)

    def test_rejects_missing_failed_or_duplicate_replay(self):
        original = timeout_parent()
        replay_name = "replay-" + driver.TARGETS[0]
        changed = deepcopy(original)
        changed["commands"] = [c for c in changed["commands"] if c["name"] != replay_name]
        self.rejected(changed)
        changed = deepcopy(original)
        next(c for c in changed["commands"] if c["name"] == replay_name)["exit_code"] = 1
        self.rejected(changed)
        changed = deepcopy(original)
        changed["commands"].insert(-1, deepcopy(next(c for c in changed["commands"]
                                                   if c["name"] == replay_name)))
        self.rejected(changed)

    def test_rejects_changed_targets_or_non_strict_compilation(self):
        original = timeout_parent()
        changed = deepcopy(original)
        changed["targets"] = changed["targets"][:-1]
        self.rejected(changed)
        changed = deepcopy(original)
        changed["modules"][driver.TARGETS[0]]["strict"] = False
        self.rejected(changed)
        changed = deepcopy(original)
        changed["commands"][0]["exit_code"] = 1
        self.rejected(changed)
        changed = deepcopy(original)
        command = [arg for arg in changed["commands"][0]["command"] if arg != "-t0"]
        changed["commands"][0]["command"] = command
        changed["modules"][driver.TARGETS[0]]["command"] = command
        self.rejected(changed)
        changed = deepcopy(original)
        command = changed["commands"][0]["command"]
        command[command.index("-o") + 1] = "/tmp/unbound.olean"
        self.rejected(changed)

    def test_rejects_nonempty_mirror_state(self):
        for field, value in [("planned_external_cache_mirrors", ["MathlibNt.Example"]),
                             ("external_cache_mirrors", {"MathlibNt.Example": {}})]:
            with self.subTest(field=field):
                changed = timeout_parent()
                changed[field] = value
                self.rejected(changed)

    def test_unfilled_bindings_fail_closed(self):
        with patch.object(driver, "PARENT_TASK", "a24f-parent-identity-for-test"), \
                patch.object(driver, "PARENT_REPORT_SHA", ""):
            with self.assertRaisesRegex(RuntimeError, "Unfilled fixed binding: PARENT_REPORT_SHA"):
                driver.require_fixed_bindings()


if __name__ == "__main__":
    unittest.main()
