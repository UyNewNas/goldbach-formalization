#!/usr/bin/env python3
"""Fresh scoped compilation; not the R19 gate or original runtime qualification.

Uses the original strict flags and exact historical parent bindings. Frozen
physical execution inputs are sufficient for this separately labelled run;
missing historical provider receipts remain missing, never synthesized.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import lzma
import os
from pathlib import Path
import subprocess
import sys

import prepare_halfopen as p

STRICT_FLAGS = ["-t0", "-j1", "-M11264", "-DwarningAsError=true",
                "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
PREPARER_SHA = "2c1c02be4ac8f1d3a0c38e697be700654a4a7fe205574a03a5fd5a9e363b47e3"
NONEXECUTION_ROLES = {
    "original-checkpoint", "byte-export-manifest", "exact-request", "source-census",
    "byte-staging-receipt", "original-trace", "fresh-native-compile-log",
    "native-provider-receipt", "native-qualification-receipt", "batteries-overlay-receipt",
    "fresh-native-producer-script", "qualification-adapter", "original-descriptor-validator",
}
HISTORICAL_SETUP = (
    "/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/"
    "qualifications/attempt-002/fresh/Architect.Command/actual.setup.json"
)
SETUP_SHA = "90681b8d0156649c34988c20e54489650dc9b510f39d44459c506b6f274a6af4"
COMPANIONS = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".so")


def signature(value):
    return p.sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def split_runtime_files(value):
    required, omitted = {}, {}
    for name, row in value["files"].items():
        if row["role"] in NONEXECUTION_ROLES:
            omitted[name] = dict(**row, reason="Historical provenance/producer metadata; not an input to these explicit commands")
        elif name == HISTORICAL_SETUP:
            p.require(row == dict(bytes=155, role="resumed-fresh-actual-input", sha256=SETUP_SHA),
                      "Unexpected historical setup identity")
            omitted[name] = dict(**row, reason="Original Architect.Command invocation setup; current commands never pass --setup")
        else:
            required[name] = row
    for name in value["resolutions"].values():
        p.require(name in required, "A resolved executable import was omitted")
    for row in value["modules"].values():
        p.require(row["source"] in required and row["object"] in required, "A native source/object was omitted")
    for key in ("lean", "leanchecker"):
        p.require(value["runtime"][key] in required, "A runtime binary was omitted")
    return required, omitted


class ExecutionBoundary:
    """A separate physical-input checker. It never instantiates a partial old verifier."""
    def __init__(self, root, snapshot, plan):
        self.root, self.snapshot, self.plan = root, snapshot, plan
        self.snapshot_body = p.read_regular(snapshot)
        raw = lzma.decompress(self.snapshot_body) if snapshot.suffix == ".xz" else self.snapshot_body
        p.require(p.sha(raw) == p.SNAPSHOT_SHA, "Original snapshot bytes differ")
        self.value = json.loads(raw)
        p.require(self.value["context_signature"] == plan["original_external_binding"]["context_signature"],
                  "Historical runtime binding differs")
        self.required, self.omitted = split_runtime_files(self.value)
        self.runtime = self.value["runtime"]
        self.lib = root / ".lake/p2-private/lib"
        self.search = [self.lib] + [Path(s) for s in self.runtime["lean_path"]]
        p.require(len(self.search) == len(set(self.search)), "Duplicate runtime search root")
        p.original_helpers(root)
        from winner9_external_snapshot import PhysicalHashes
        self.hashes = PhysicalHashes()
        self.binding = dict(schema="p25-fresh-scoped-physical-runtime-v1",
                            original_snapshot_sha256=p.SNAPSHOT_SHA,
                            original_snapshot_context_signature=self.value["context_signature"],
                            original_external_snapshot_verified=False,
                            required_files=len(self.required), required_file_map_sha256=signature(self.required),
                            omitted_historical_files=len(self.omitted),
                            omitted_file_map_sha256=signature(self.omitted),
                            lean_path=list(map(str, self.search)), lean_sysroot=self.runtime["sysroot"])

    def evidence(self):
        return dict(schema="p25-fresh-scoped-runtime-input-plan-v1", **p.CREDIT,
                    binding=self.binding, required_files=self.required, omitted_historical_files=self.omitted,
                    omitted_by_role=dict(Counter(r["role"] for r in self.omitted.values())),
                    missing_omitted_files=[n for n in self.omitted if not Path(n).is_file()])

    def environment(self):
        env = dict(os.environ)
        p.require(not env.get("LD_PRELOAD"), "Unexpected LD_PRELOAD")
        env.pop("LEAN_SRC_PATH", None)
        env["LEAN_SYSROOT"] = self.runtime["sysroot"]
        env["LEAN_PATH"] = os.pathsep.join(map(str, self.search))
        return env

    def verify(self):
        p.require(p.read_regular(self.snapshot) == self.snapshot_body, "Snapshot changed")
        for name, row in self.required.items():
            path = Path(name)
            p.require(path.is_file() and path.stat().st_size == row["bytes"]
                      and self.hashes.digest(path) == row["sha256"], "Physical execution input differs: " + name)
        # The resolution check preserves the original first-package-root rule.
        for module, expected in self.value["resolutions"].items():
            relative = Path(module.replace(".", "/") + ".olean")
            found = None
            for root in self.search:
                candidate = root / relative
                if candidate.is_file():
                    found = candidate.resolve()
                    break
                p.require(not (root / module.split(".", 1)[0]).is_dir(),
                          "Earlier incomplete package root shadows runtime: " + module)
            p.require(found == Path(expected).resolve(), "Runtime import resolves elsewhere: " + module)
            stem = expected[:-len(".olean")]
            for suffix in COMPANIONS:
                companion = Path(stem + suffix)
                if companion.exists() or companion.is_symlink():
                    p.require(str(companion) in self.required, "Unfrozen runtime companion: " + str(companion))
        for package, row in self.value["packages"].items():
            current = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=row["root"], text=True).strip()
            p.require(current == row["commit"], "Native Git pin differs: " + package)
        current = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd="/workspace/compile-deps/mathlib", text=True).strip()
        p.require(current == self.plan["toolchain"]["mathlib_commit"], "Mathlib Git pin differs")
        for key in ("lean", "leanchecker"):
            p.require(os.access(self.runtime[key], os.X_OK), "Runtime binary is not executable: " + key)
        p.require(self.required[self.runtime["lean"]]["sha256"] == self.plan["toolchain"]["lean_binary_sha256"],
                  "Lean binary differs from historical parent compiler")
        return self.binding


def module_closure(plan, target):
    names = set()
    def visit(name):
        if name in names:
            return
        names.add(name)
        for dep in plan["modules"][name]["direct_project_imports"]:
            visit(dep)
    visit(target)
    return names


def project_inputs(root, plan, target, fresh, include_target=False):
    """Exact project closure; fresh objects have their own new evidence signature."""
    result = {}
    for name in sorted(module_closure(plan, target)):
        row = plan["modules"][name]
        source = (root / row["source"]).resolve(strict=True)
        p.require(source.is_relative_to(root), "Source link escaped repo")
        p.read_regular(source, row["source_sha256"], row["source_bytes"])
        item = dict(source=row["source"], source_sha256=row["source_sha256"])
        if name == target and not include_target:
            result[name] = item
            continue
        obj = root / ".lake/p2-private/lib" / (name.replace(".", "/") + ".olean")
        if row["action"] == "restore_existing_bytes":
            old = row["historical_binding"]
            p.require(p.existing_exact(obj, old["object_sha256"], old["object_bytes"]), "Missing old parent: " + name)
            item.update(object_sha256=old["object_sha256"], object_bytes=old["object_bytes"],
                        dependency_signature=old["closure_signature"], origin="historical_exact_parent")
            for suffix in COMPANIONS[1:]:
                extra = Path(str(obj)[:-len(".olean")] + suffix)
                p.require(not extra.exists() and not extra.is_symlink(), "Unbound old project companion: " + str(extra))
        else:
            p.require(name in fresh, "Fresh parent requires its new normal receipt: " + name)
            known = fresh[name]
            p.require(p.existing_exact(obj, known["object_sha256"], known["object_bytes"]), "Fresh object changed: " + name)
            item.update(object_sha256=known["object_sha256"], object_bytes=known["object_bytes"],
                        dependency_signature=known["fresh_signature"], origin="fresh_scoped_normal")
            for suffix in COMPANIONS[1:]:
                extra = Path(str(obj)[:-len(".olean")] + suffix)
                p.require(not extra.exists() and not extra.is_symlink(), "Unbound fresh project companion: " + str(extra))
        result[name] = item
    return result


def freeze(root, plan, target, fresh, boundary, include_target=False):
    p.require(p.build_manifest(root) == plan, "Source/input plan changed")
    return dict(manifest_sha256=p.sha(p.encoded(plan)), runtime=boundary.verify(),
                project=project_inputs(root, plan, target, fresh, include_target),
                preparer_sha256=p.sha(p.read_regular(Path(p.__file__), PREPARER_SHA)),
                normal_driver_sha256=p.sha(p.read_regular(Path(__file__))))


def load_normal(path, digest, root, plan, boundary, fresh=None):
    receipt = json.loads(p.read_regular(path, digest))
    p.require(receipt["schema"] == "p25-fresh-scoped-normal-v1"
              and receipt["fresh_normal_compile_passed"] is True
              and receipt["normal"]["exit_code"] == 0 and receipt["inputs_unchanged"] is True,
              "No passed fresh normal receipt")
    p.require(receipt["manifest_sha256"] == p.sha(p.encoded(plan))
              and receipt["runtime"] == boundary.binding
              and receipt["strict_flags"] == STRICT_FLAGS
              and receipt["normal_driver_sha256"] == p.sha(p.read_regular(Path(__file__))),
              "Fresh normal input identity differs")
    p.require(receipt["module"] in (p.CHRONOLOGY, p.TARGET), "Unexpected fresh owner")
    p.require(receipt["source_sha256"] == plan["modules"][receipt["module"]]["source_sha256"],
              "Fresh source binding differs")
    p.read_regular(root / receipt["normal"]["log"], receipt["normal"]["log_sha256"])
    p.require(receipt["fresh_signature"] == signature(receipt["fresh_binding"]), "Fresh signature differs")
    p.require(receipt["fresh_binding"]["object_sha256"] == receipt["object_sha256"], "Fresh object signature differs")
    expected_command = [boundary.runtime["lean"], *STRICT_FLAGS, plan["modules"][receipt["module"]]["source"],
                        "-o", str(path.parent / "compiled.olean")]
    p.require(receipt["normal"]["command"] == expected_command, "Fresh compiler command differs")
    p.read_regular(path.parent / "compiled.olean", receipt["object_sha256"], receipt["object_bytes"])
    current = freeze(root, plan, receipt["module"], fresh or {}, boundary)
    p.require(receipt["frozen_inputs"] == current, "Fresh receipt dependencies/runtime changed")
    deps = plan["modules"][receipt["module"]]["direct_project_imports"]
    expected_binding = dict(schema="p25-fresh-scoped-normal-binding-v1", module=receipt["module"],
                            source_sha256=receipt["source_sha256"], object_sha256=receipt["object_sha256"],
                            toolchain=plan["toolchain"], runtime=boundary.binding,
                            direct_dependencies={d: current["project"][d] for d in deps})
    p.require(receipt["fresh_binding"] == expected_binding, "Fresh direct-dependency signature differs")
    return receipt


def run(args):
    root = args.root.resolve(strict=True)
    out = args.out_dir.absolute()
    p.require(out.is_relative_to(root) and not out.exists() and not out.is_symlink(),
              "Output must be a new directory inside the isolated repo")
    p.read_regular(Path(p.__file__), PREPARER_SHA)
    plan = p.build_manifest(root)
    _, audit = p.original_helpers(root)
    boundary = ExecutionBoundary(root, args.snapshot or root / (p.RESUMED + "p2-round14-context/EXTERNAL_SNAPSHOT.json.xz"), plan)
    fresh = {}
    if args.chronology_normal:
        p.require(args.chronology_normal_sha256 is not None, "Chronology receipt SHA required")
        prior = load_normal(args.chronology_normal, args.chronology_normal_sha256, root, plan, boundary)
        p.require(prior["module"] == p.CHRONOLOGY, "Wrong prior fresh owner")
        fresh[p.CHRONOLOGY] = prior
    target = args.target
    p.require(target != p.TARGET or p.CHRONOLOGY in fresh, "HalfOpen requires the fresh Chronology normal receipt")
    object_path = root / ".lake/p2-private/lib" / (target.replace(".", "/") + ".olean")
    for suffix in COMPANIONS:
        path = Path(str(object_path)[:-len(".olean")] + suffix)
        p.require(not path.exists() and not path.is_symlink(), "Fresh compilation will not overwrite: " + str(path))
    env = boundary.environment()
    p.publish_new(out / "EXECUTION_INPUT_PLAN.json", p.encoded(boundary.evidence()))
    p.publish_new(out / "MINIMAL_INPUT_MANIFEST.json", p.encoded(plan))
    receipt = dict(schema="p25-fresh-scoped-normal-v1", **p.CREDIT, module=target,
                   fresh_normal_compile_passed=False, manifest_sha256=p.sha(p.encoded(plan)),
                   source_sha256=plan["modules"][target]["source_sha256"],
                   runtime=boundary.binding, strict_flags=STRICT_FLAGS,
                   normal_driver_sha256=p.sha(p.read_regular(Path(__file__))))
    try:
        print("SCOPED_PHYSICAL_PREFLIGHT", target, flush=True)
        before = freeze(root, plan, target, fresh, boundary)
        version = subprocess.check_output([boundary.runtime["lean"], "--version"], env=env, text=True).strip()
        p.require(version == plan["toolchain"]["lean_version"], "Lean version differs")
        generated = out / "compiled.olean"
        command = [boundary.runtime["lean"], *STRICT_FLAGS, plan["modules"][target]["source"],
                   "-o", str(generated)]
        print("SCOPED_NORMAL_COMPILE", target, flush=True)
        receipt["normal"] = audit.run_process(command, out / "normal.log", root, env)
        after = freeze(root, plan, target, fresh, boundary)
        receipt.update(inputs_unchanged=after == before, frozen_inputs=before)
        p.require(receipt["normal"]["exit_code"] == 0, "Scoped normal compilation failed")
        p.require(after == before, "Inputs changed during normal compilation")
        body = p.read_regular(generated)
        # These project modules historically have only the declared .olean output.
        for suffix in COMPANIONS[1:]:
            extra = Path(str(generated)[:-len(".olean")] + suffix)
            p.require(not extra.exists() and not extra.is_symlink(), "Unexpected output companion requires explicit binding: " + str(extra))
        receipt.update(object_sha256=p.sha(body), object_bytes=len(body))
        deps = plan["modules"][target]["direct_project_imports"]
        binding = dict(schema="p25-fresh-scoped-normal-binding-v1", module=target,
                       source_sha256=receipt["source_sha256"], object_sha256=receipt["object_sha256"],
                       toolchain=plan["toolchain"], runtime=boundary.binding,
                       direct_dependencies={d: before["project"][d] for d in deps})
        receipt.update(fresh_binding=binding, fresh_signature=signature(binding))
        p.publish_new(object_path, body)
        fresh[target] = receipt
        receipt["post_publish_inputs"] = freeze(root, plan, target, fresh, boundary, include_target=True)
        receipt.update(fresh_normal_compile_passed=True, status="FRESH_SCOPED_NORMAL_PASSED",
                       object_path=str(object_path), object_publication="new exact bytes; no old record written")
    except Exception as error:
        receipt.update(status="FRESH_SCOPED_NORMAL_INCOMPLETE", error=str(error))
        raise
    finally:
        p.publish_new(out / "NORMAL_RESULT.json", p.encoded(receipt))
    print(json.dumps(dict(status=receipt["status"], module=target, object_sha256=receipt["object_sha256"],
                          normal_receipt=str(out / "NORMAL_RESULT.json"),
                          normal_receipt_sha256=p.sha(p.encoded(receipt)), R19_accepted=False, P2_5_proved=False)))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=p.ROOT)
    parser.add_argument("--snapshot", type=Path)
    parser.add_argument("--target", choices=(p.CHRONOLOGY, p.TARGET), required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--chronology-normal", type=Path)
    parser.add_argument("--chronology-normal-sha256")
    args = parser.parse_args()
    return run(args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print("SCOPED_NORMAL_REFUSED " + str(error), file=sys.stderr)
        sys.exit(2)
