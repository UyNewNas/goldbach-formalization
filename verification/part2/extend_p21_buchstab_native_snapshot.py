#!/usr/bin/env python3
"""Extend a qualified native input snapshot with three pinned Buchstab providers."""
import argparse
import copy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from inspect_winner9_owner_native import MATHLIB_PIN, git, imports
from qualify_winner9_native_cache import LOAD_SUFFIXES, atomic_missing, core_header
from winner9_external_snapshot import ExternalSnapshot, PINS, PhysicalHashes, native, require, signature

TARGETS = tuple("MathlibNt.SieveTheory." + leaf for leaf in (
    "LiLiuPrereqBuchstabFunction", "LiLiuPrereqBuchstabBounds", "LiLiuBuchstabTailPropagation"))
FRESH = "FRESH_PRIVATE_SOURCE_COMPILATION"


def publish(path, value):
    raw = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    atomic_missing(path, raw, hashlib.sha256(raw).hexdigest())


def relative(name, suffix):
    return name.replace(".", "/") + suffix


def first_root(roots, name):
    prefix = name.split(".", 1)[0]
    for root in roots:
        if (root / prefix).is_dir() or (root / (prefix + ".olean")).is_file():
            return root
    raise ValueError("No search root for " + name)


class Extension:
    def __init__(self, args):
        self.project = args.project_root.resolve(strict=True)
        self.lib = self.project / ".lake/p2-private/lib"
        self.hashes = PhysicalHashes()
        require(self.hashes.digest(args.snapshot) == args.snapshot_sha256, "Base snapshot digest differs")
        raw = json.loads(args.snapshot.read_text())
        self.base = ExternalSnapshot(args.snapshot, lean=raw["runtime"]["lean"], mathlib_pin=MATHLIB_PIN,
                                     project_lib=self.lib)
        require(len(self.base.modules) == 515, "Expected the 515-module base environment")
        self.value = copy.deepcopy(self.base.value)
        self.files, self.modules = self.value["files"], self.value["modules"]
        self.resolutions = self.value["resolutions"]
        self.gold = Path(raw["packages"]["goldbach"]["root"])
        self.script = Path(__file__).resolve()
        self.out = (self.project / ".lake/p2-private/p21-buchstab-native" /
                    self.base.raw_sha256 / self.hashes.digest(self.script))
        self.out.mkdir(exist_ok=True, parents=True)
        self.bind(self.base.path, "parent-snapshot")
        for filename in (__file__, core_header.__code__.co_filename, imports.__code__.co_filename,
                         ExternalSnapshot.verify.__code__.co_filename):
            self.bind(Path(filename), "extension-qualification-code")
        runtime = raw["runtime"]
        self.source_roots = [Path(runtime["sysroot"]) / "src/lean", Path(runtime["sysroot"]) / "src/lean/lake"]
        self.source_roots.extend(p.parents[3] for p in self.base.search_path
                                 if p.as_posix().endswith("/.lake/build/lib/lean"))
        lock = self.project / "lake-manifest.json"
        self.bind(lock, "project-package-pins")
        self.pins = {p["name"].lower(): p["rev"] for p in json.loads(lock.read_text())["packages"]}
        self.extra_roots = {}
        self.source_names = {}
        for p in self.base.files:
            if p.endswith(".lean"):
                self.source_names.setdefault(Path(p).name, []).append(Path(p))
        self.old_root = first_root(self.base.search_path, TARGETS[0])
        self.original_links = {}
        # Copy link names only. Reject stray loadable objects in this namespace:
        # overlaying a partial shadow or accepting stray providers would change lookup.
        for path in sorted((self.old_root / "MathlibNt").rglob("*")):
            if not path.is_file() or not path.name.endswith(LOAD_SUFFIXES):
                continue
            rel = path.relative_to(self.old_root)
            provider = str(rel).split(".olean")[0].split(".ir")[0].replace("/", ".")
            require(provider in self.base.modules and str(path.resolve()) in self.base.files,
                    "Unqualified native facet in the selected namespace: " + str(path))
            self.original_links[str(rel)] = path.resolve()
        if (self.old_root / "MathlibNt.olean").exists():
            for suffix in LOAD_SUFFIXES:
                path = self.old_root / ("MathlibNt" + suffix)
                if path.exists():
                    require(str(path.resolve()) in self.base.files, "Unfrozen namespace root")
                    self.original_links[path.name] = path.resolve()
        self.links = dict(self.original_links)

    def bind(self, p, role, expected=None):
        p = p.resolve(strict=True)
        record = {"bytes": p.stat().st_size, "sha256": self.hashes.digest(p), "role": role}
        old = self.files.setdefault(str(p), record)
        require(old["sha256"] == record["sha256"] and old["bytes"] == record["bytes"] and
                (expected is None or expected == record["sha256"]), "Physical input changed: " + str(p))
        return old["sha256"]

    def view(self, name):
        root = self.out / "views" / name
        for rel, target in self.links.items():
            link = root / rel
            link.parent.mkdir(parents=True, exist_ok=True)
            if not link.is_symlink():
                require(not link.exists(), "Refusing to replace existing overlay entry: " + str(link))
                link.symlink_to(target)
            require(link.resolve(strict=True) == target, "Overlay link changed: " + str(link))
        actual = {str(p.relative_to(root)) for p in root.rglob("*") if p.is_symlink() or p.is_file()}
        require(actual == set(self.links), "Unexpected or missing files in overlay")
        return root

    def pinned_source(self, name):
        rel = relative(name, ".lean")
        source = self.gold / rel
        expected = git(self.gold, "rev-parse", PINS["goldbach"] + ":" + rel).decode().strip()
        raw = source.read_bytes()
        require(hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == expected,
                "Source differs from the pinned Git blob: " + name)
        self.bind(source, "pinned-buchstab-source")
        return source, expected

    def standard_source(self, name):
        rel = relative(name, ".lean")
        matches = [p / rel for p in self.source_roots if str(p / rel) in self.base.files]
        if not matches:
            # A restored object overlay (notably Batteries) need not expose
            # its checkout as a search root. Recover only an already frozen
            # source in the package's exact commit and original Git location.
            pin = self.pins.get(name.split(".")[0].lower())
            for p in self.source_names.get(Path(rel).name, []):
                if not pin or not str(p).endswith("/" + rel):
                    continue
                root = p.parents[len(name.split(".")) - 1]
                if not (root / ".git").exists() or git(root, "rev-parse", "HEAD").decode().strip() != pin:
                    continue
                blob = git(root, "rev-parse", pin + ":" + rel).decode().strip()
                raw = p.read_bytes()
                require(hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == blob,
                        "Frozen standard source differs from its Git blob: " + name)
                self.extra_roots[root] = pin
                matches.append(p)
        require(matches and len({self.base.files[str(p)]["sha256"] for p in matches}) == 1,
                "No unambiguous frozen source for " + name)
        return matches[0]

    def recheck_base(self):
        self.base.verify()
        for root, pin in self.extra_roots.items():
            require(git(root, "rev-parse", "HEAD").decode().strip() == pin, "Standard-source checkout changed")

    def inputs(self, direct, roots):
        found, visiting = {}, set()

        def visit(name):
            if name in found:
                return
            require(name not in visiting, "Source import cycle: " + name)
            visiting.add(name)
            if native(name):
                require(name in self.modules, "Missing qualified native predecessor: " + name)
                source = Path(self.modules[name]["source"])
            else:
                source = self.standard_source(name)
            stem = first_root(roots, name) / relative(name, "")
            wanted = self.resolutions.get(name)
            public = Path(str(stem) + ".olean").resolve(strict=True)
            require(wanted is not None and public == Path(wanted), "Unqualified resolution for " + name)
            parts = {}
            for suffix in LOAD_SUFFIXES:
                part = Path(str(stem) + suffix)
                if part.is_file():
                    path = str(part.resolve())
                    require(path in self.files, "Unfrozen loadable import facet: " + path)
                    parts[path] = self.bind(part, "import-facet")
            text = source.read_text()
            # The pinned header reader recognizes public/meta imports. Private
            # imports contribute the same dependency edges to this traversal.
            deps, prelude = core_header(re.sub(r"(?m)^(\s*)private(\s+(?:meta\s+)?import\s+)",
                                               r"\1public\2", text))
            if native(name):
                require(deps == self.modules[name]["imports"], "Parsed native header differs: " + name)
            if not prelude and name != "Init" and "Init" not in deps:
                deps = ["Init", *deps]
            for dep in deps:
                visit(dep)
            found[name] = {"source": str(source), "source_sha256": self.bind(source, "import-source"),
                           "imports": deps, "facets": parts}
            visiting.remove(name)
        for dep in direct:
            visit(dep)
        return found

    def fresh(self, name):
        source, blob = self.pinned_source(name)
        direct = imports(source.read_text())
        header, prelude = core_header(source.read_text())
        require(header == direct, "Unsupported native source header: " + name)
        root = self.view(name)
        roots = [self.lib, root, *self.base.search_path[1:]]
        runtime = self.value["runtime"]
        env = self.base.environment(os.environ)
        env["LEAN_PATH"] = os.pathsep.join(map(str, roots))
        starting = direct if prelude or "Init" in direct else ["Init", *direct]
        closure = self.inputs(starting, roots)
        deps = {d: self.modules[d]["closure_signature"] for d in direct if native(d)}
        context = {"module": name, "parent": self.base.raw_sha256, "source": str(source),
                   "source_sha256": self.bind(source, "pinned-buchstab-source"), "git_blob_sha1": blob,
                   "direct_imports": direct, "dependency_signatures": deps, "input_signature": signature(closure),
                   "lean_path": env["LEAN_PATH"], "sysroot": env["LEAN_SYSROOT"], "cwd": str(self.gold),
                   "lean": runtime["lean"], "lean_sha256": self.files[runtime["lean"]]["sha256"],
                   "compiler_script_sha256": self.hashes.digest(self.script)}
        receipt_path = self.out / "providers" / (name + ".json")
        previous = receipt_path.exists()
        if previous:
            receipt = json.loads(receipt_path.read_text())
            run = Path(receipt["run"])
            require(run.is_relative_to(self.out / "runs") and receipt["context"] == context,
                    "Earlier provider used a different context")
        else:
            runs = self.out / "runs"
            runs.mkdir(exist_ok=True)
            run = Path(tempfile.mkdtemp(prefix=name.split(".")[-1] + "-", dir=runs))
        stem = run / relative(name, "")
        stem.parent.mkdir(parents=True, exist_ok=True)
        log = run / "compile.log"
        command = [runtime["lean"], "-t0", "-j1", "-M6144", "-DwarningAsError=true",
                   relative(name, ".lean"), "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean", "--json"]
        self.recheck_base()
        if previous:
            require(receipt["status"] == FRESH and receipt["command"] == command and receipt["exit_code"] == 0
                    and receipt["inputs_unchanged"] is True and receipt["inputs"] == closure,
                    "Prior provider lacks matching successful compilation evidence")
            self.bind(log, "buchstab-compile-log", receipt["log_sha256"])
        else:
            begin = time.monotonic()
            with log.open("x") as stream:
                result = subprocess.run(command, cwd=self.gold, env=env, stdout=stream, stderr=subprocess.STDOUT)
            require(result.returncode == 0, f"{name}: Lean exit {result.returncode}, see {log}")
            receipt = {"status": FRESH, "module": name, "context": context, "run": str(run), "command": command,
                       "exit_code": result.returncode, "seconds": round(time.monotonic()-begin, 3),
                       "log_sha256": self.bind(log, "buchstab-compile-log"), "inputs": closure,
                       "compile_credit": False, "kernel_credit": False}
        self.recheck_base()
        require(self.view(name) == root and self.inputs(starting, roots) == closure and
                self.pinned_source(name)[1] == blob and self.hashes.digest(self.script) == context["compiler_script_sha256"],
                "Binding changed during compilation")
        parts = {s: self.bind(Path(str(stem) + s), "fresh-buchstab-artifact")
                 for s in (*LOAD_SUFFIXES, ".ilean") if Path(str(stem) + s).is_file()}
        require(".olean" in parts and ".ilean" in parts, "Missing requested compiler output")
        if previous:
            require(receipt["objects"] == parts, "Prior provider output changed")
        else:
            receipt.update(inputs_unchanged=True, objects=parts)
            publish(receipt_path, receipt)
        self.bind(receipt_path, "fresh-buchstab-provider")
        for s in parts:
            self.links[relative(name, s)] = Path(str(stem) + s)
        provider = {"status": FRESH, "receipt": str(receipt_path)}
        row = {"package": "goldbach", "source": str(source), "git_blob_sha1": blob,
               "object": str(stem) + ".olean", "imports": direct, "dependency_signatures": deps, "provider": provider}
        bound = {k: row[k] for k in ("source", "object", "imports", "dependency_signatures", "provider")}
        row["closure_signature"] = signature(dict(bound, module=name, source_sha256=context["source_sha256"],
                                                  object_sha256=parts[".olean"]))
        self.modules[name] = row
        self.resolutions[name] = row["object"]

    def run(self):
        for name in TARGETS:
            if name not in self.modules:
                self.fresh(name)
        overlay = self.view("all")
        # This provider inventory is an input to the consumer's verification.
        # Keep it outside the published result until its candidate is verified.
        qualification = self.out / "candidates/provider-inventory.json"
        publish(qualification, {"status": "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED", "parent": self.base.raw_sha256,
                                "providers": {n: self.modules[n]["provider"] for n in TARGETS},
                                "compile_credit": False, "kernel_credit": False})
        self.value["runtime"]["lean_path"].insert(0, str(overlay))
        self.value["qualification"] = {"path": str(qualification), "sha256": self.bind(qualification, "qualification"),
                                       "status": "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED"}
        self.value.pop("context_signature")
        self.value["context_signature"] = signature(self.value)
        candidate = self.out / "candidates/combined-snapshot.json"
        publish(candidate, self.value)
        checked = ExternalSnapshot(candidate, lean=self.value["runtime"]["lean"], mathlib_pin=MATHLIB_PIN,
                                   project_lib=self.lib)
        path = self.out / "EXTERNAL_SNAPSHOT.json"
        atomic_missing(path, candidate.read_bytes(), checked.raw_sha256)
        publish(self.out / "QUALIFICATION.json", {"status": "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED",
                "verified_snapshot": str(path), "snapshot_sha256": checked.raw_sha256,
                "context_signature": checked.context_signature, "parent_sha256": self.base.raw_sha256,
                "compile_credit": False, "kernel_credit": False})
        print(json.dumps({"snapshot": str(path), "sha256": self.hashes.digest(path), "modules": len(self.modules),
                          "compile_credit": False, "kernel_credit": False}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=Path)
    parser.add_argument("--snapshot-sha256", required=True)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    task = Extension(parser.parse_args())
    with (task.out / "writer.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        task.run()
