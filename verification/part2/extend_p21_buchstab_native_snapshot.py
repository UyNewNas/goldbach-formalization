#!/usr/bin/env python3
"""Extend a qualified native input snapshot with three pinned Buchstab providers."""
import argparse
import base64
import copy
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time

from inspect_winner9_owner_native import MATHLIB_PIN, git, imports
from qualify_winner9_native_cache import LOAD_SUFFIXES, atomic_missing, core_header
from winner9_external_snapshot import ExternalSnapshot, PINS, PROVIDER_STATUSES, PhysicalHashes, native, require, signature

TARGETS = tuple("MathlibNt.SieveTheory." + leaf for leaf in (
    "LiLiuPrereqBuchstabFunction", "LiLiuPrereqBuchstabBounds", "LiLiuBuchstabTailPropagation"))
FRESH = "FRESH_PRIVATE_SOURCE_COMPILATION"
CASING = "Lake.Util.Casing"
CASING_BASE = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
CASING_RECEIPT_SHA = "903fbc57d2a7882ae9e025c8183fbd46f552f17ab166816bc67743eb92a6952c"


# Same inventory primitive as LongSlotNormalizationAudit.lean. The observer
# has no import of its own. Shell.lean at v4.33.0-rc1 accepts the original
# module filename with --stdin, so the observer elaborates its actual header
# in the same main module, cwd and provider search roots as the source process.
OBSERVER = """
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    let path ← liftIO <| Lean.findOLean moduleName
    let row := Json.mkObj [("module", toJson moduleName.toString), ("olean", toJson path.toString)]
    liftIO <| IO.println s!"P21_IMPORT {row.compress}"
  let summary := Json.mkObj [("main", toJson env.mainModule.toString), ("count", toJson env.header.moduleNames.size)]
  liftIO <| IO.println s!"P21_HEADER {summary.compress}"
""".encode()


def probe_source(raw, direct):
    # These three pinned files begin with plain legacy imports, then a blank
    # line. Reject other formats. Preserve the exact bytes of that prefix.
    lines = raw.splitlines(keepends=True)
    require(direct and len(lines) > len(direct) and not lines[len(direct)].strip()
            and all(line.rstrip(b"\r\n") == ("import " + name).encode()
                    for line, name in zip(lines, direct)), "Unsupported pinned legacy import header")
    return b"".join(lines[:len(direct) + 1]) + OBSERVER


def unique_fields(pairs):
    fields = dict(pairs)
    require(len(fields) == len(pairs), "Duplicate field in observer JSON")
    return fields


def observed(log, name, direct):
    # --json wraps the single run_cmd's captured stdout as one SerialMessage.
    require(log.startswith(b"{") and log.endswith(b"}\n") and log.count(b"\n") == 1
            and b"\r" not in log, "Expected exactly one JSON observer message")
    message = json.loads(log.decode("utf-8"), object_pairs_hook=unique_fields)
    require(isinstance(message, dict), "Expected observer message object")
    body = message.pop("data", None)
    # One line per import, then one preserved blank line, then the observer.
    line = len(direct) + 2 + OBSERVER.splitlines().index(b"run_cmd do")
    expected = {"caption": "", "fileName": relative(name, ".lean"), "isSilent": False,
                "keepFullRange": False, "kind": "[anonymous]", "severity": "information",
                "pos": {"column": 0, "line": line}, "endPos": {"column": len("run_cmd"), "line": line}}
    # Compare JSON types as well as values (Python would accept 0 as False).
    require(json.dumps(message, sort_keys=True) == json.dumps(expected, sort_keys=True),
            "Unexpected observer message metadata")
    require(isinstance(body, str) and body.endswith("\n") and "\r" not in body,
            "Expected newline-terminated observer data")
    lines = body[:-1].split("\n")
    rows = {}
    for entry in lines[:-1]:
        require(entry.startswith("P21_IMPORT {") and entry.endswith("}"), "Unexpected observer import line")
        row = json.loads(entry.removeprefix("P21_IMPORT "), object_pairs_hook=unique_fields)
        require(row.keys() == {"module", "olean"} and all(isinstance(v, str) and v for v in row.values()),
                "Malformed observed import")
        module = row["module"]
        require(module not in rows, "Duplicate observed import: " + module)
        rows[module] = row["olean"]
    header = lines[-1]
    require(header.startswith("P21_HEADER {") and header.endswith("}"), "Expected final observer header")
    summary = json.loads(header.removeprefix("P21_HEADER "), object_pairs_hook=unique_fields)
    require(type(summary.get("count")) is int and summary == {"main": name, "count": len(rows)}
            and name not in rows and {"Init", *direct} <= rows.keys(),
            "Incomplete actual legacy header inventory: " + name)
    return rows

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
        self.casing = self.bind_lake_casing()

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

    def bind_lake_casing(self):
        """Reuse one standard toolchain input from an observed, byte-frozen P3 audit."""
        require(self.base.raw_sha256 == CASING_BASE and CASING not in self.base.value["resolutions"],
                "Unexpected base for Lake.Util.Casing evidence")
        self.casing_hashes = {}
        def bind(path, role, expected):
            require(path.resolve(strict=True) == path, "Non-canonical Casing evidence path")
            digest = self.bind(path, role, expected)
            self.casing_hashes[path] = digest
            return digest

        evidence_dir = self.project / "verification/parts/p3/long-slot-normalization"
        publication = evidence_dir / "receipt.json"
        bind(publication, "historical-casing-input-receipt", CASING_RECEIPT_SHA)
        raw = publication.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == CASING_RECEIPT_SHA, "Historical P3 receipt changed")
        published = json.loads(raw)
        for filename in ("lean-toolchain", "lake-manifest.json"):
            bind(self.project / filename, "historical-casing-runtime-pin",
                      published["scope_guard"]["frozen_configs_and_complete_gates"][filename])
        archive = evidence_dir / "local-evidence.tar.xz.b64"
        archive_sha = bind(archive, "historical-casing-input-evidence", published["evidence"]["archive_base64_sha256"])
        encoded = archive.read_bytes()
        require(hashlib.sha256(encoded).hexdigest() == archive_sha, "Historical Casing archive changed")
        stem = "execution/20261012T090930892745Z-audit"
        with tarfile.open(fileobj=io.BytesIO(base64.b64decode(encoded)), mode="r:xz") as tar:
            def member(path):
                return tar.extractfile(path).read()
            inventory = member(stem + "-imports.json")
            receipt = json.loads(member(stem + "-receipt.json"))
            actual = json.loads(member(stem + "-actual-imports.json"))
            config = member("runtime/runtime-config.json")
        require(published["selected_gates"]["audit"] == receipt and receipt["scoped_gate_passed"] is True and receipt["returncode"] == 0
                and receipt["actual_imports_match_predicted_paths"] is True
                and receipt["all_import_sources_and_object_parts_unchanged"] is True
                and receipt["import_snapshot_sha256"] == hashlib.sha256(inventory).hexdigest()
                and receipt["runtime_config_sha256"] == hashlib.sha256(config).hexdigest(),
                "Historical Casing input evidence failed")
        history = json.loads(inventory)
        old = Path(receipt["environment"]["LEAN_SYSROOT"])
        sysroot = Path(self.value["runtime"]["sysroot"])
        source = Path("src/lean/lake/Lake/Util/Casing.lean")
        parts = [Path("lib/lean/Lake/Util/Casing" + suffix) for suffix in LOAD_SUFFIXES]
        expected = {"module": CASING, "source": str(old / source), "olean": str(old / parts[0]),
                    "parts": [str(old / p) for p in parts]}
        require([row for row in history["modules"] if row["module"] == CASING] == [expected]
                and [row for row in actual if row["module"] == CASING] == [{"module": CASING, "olean": expected["olean"]}],
                "Historical Lake.Util.Casing source, facet set or observed resolution differs")
        # P3 used the stock Lake frontend and checker. Its runtime config binds
        # those tools and both shared libraries. The parent pins the current Lean binary.
        tools = json.loads(config)["stock_tools_and_driver"]
        for leaf in ("bin/lake", "bin/leanchecker", "lib/lean/libleanshared.so", "lib/lean/libLake_shared.so"):
            bind(sysroot / leaf, "historical-casing-toolchain",
                      tools[str(old / leaf)]["sha256"])
        frozen = {}
        for rel in [source, *parts]:
            path = sysroot / rel
            bind(path, "historical-casing-input", history["sha256"][str(old / rel)])
            frozen[str(path)] = self.files[str(path)]
        self.resolutions[CASING] = str(sysroot / parts[0])
        return sysroot / source, frozen

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
        for path, digest in self.casing_hashes.items():
            require(path.resolve(strict=True) == path and self.hashes.digest(path) == digest,
                    "Historical Casing input changed: " + str(path))
        for root, pin in self.extra_roots.items():
            require(git(root, "rev-parse", "HEAD").decode().strip() == pin, "Standard-source checkout changed")

    def inputs(self, observed_paths, roots):
        found = {}
        for name, observed_path in observed_paths.items():
            new_native = native(name) and name not in self.base.modules
            historical_casing = name == CASING and self.casing is not None
            if historical_casing:
                source, frozen = self.casing
                wanted = self.resolutions[name]
            elif new_native:
                require(name in TARGETS and name in self.modules, "Missing qualified native predecessor: " + name)
                frozen, wanted = self.files, self.resolutions.get(name)
            else:
                frozen, wanted = self.base.files, self.base.value["resolutions"].get(name)
            if native(name):
                row = (self.modules if new_native else self.base.modules)[name]
                provider = row["provider"]
                require(provider["status"] in PROVIDER_STATUSES and provider["receipt"] in frozen
                        and row["object"] == wanted, "Native predecessor lacks a qualified provider: " + name)
                if new_native:
                    require(provider == {"status": FRESH, "receipt": str(self.out / "providers" / (name + ".json"))},
                            "New native predecessor lacks its own successful private compile: " + name)
                source = Path(row["source"])
            elif not historical_casing:
                source = self.standard_source(name)
            source = source.resolve(strict=True)
            require(str(source) in frozen and wanted in frozen, "Unfrozen source or resolution: " + name)
            stem = first_root(roots, name) / relative(name, "")
            expected = (first_root(self.base.search_path, name) / relative(name, "")
                        if name in self.base.value["resolutions"] else Path(wanted).with_suffix(""))
            public = Path(str(stem) + ".olean").resolve(strict=True)
            require(Path(observed_path).is_absolute() and Path(observed_path).resolve(strict=True) == public
                    and public == Path(wanted), "Observed object differs from qualified resolution: " + name)
            parts = {}
            for suffix in LOAD_SUFFIXES:
                part, original = Path(str(stem) + suffix), Path(str(expected) + suffix)
                if historical_casing:
                    require(part.is_file(), "Missing qualified Casing facet: " + suffix)
                require(part.is_file() == original.is_file(), "Qualified facet set differs: " + name + suffix)
                if part.is_file():
                    physical = part.resolve(strict=True)
                    require(physical == original.resolve(strict=True) and str(physical) in frozen,
                            "Unfrozen or redirected loadable import facet: " + str(part))
                    parts[suffix] = {"path": str(physical), "sha256": self.bind(
                        physical, "import-facet", frozen[str(physical)]["sha256"])}
            found[name] = {"source": str(source), "source_sha256": self.bind(
                source, "import-source", frozen[str(source)]["sha256"]), "facets": parts}
            if native(name):
                found[name]["closure_signature"] = row["closure_signature"]
        return found

    def observe(self, name, source, direct, roots, env, phase):
        raw = probe_source(source.read_bytes(), direct)
        folder = self.out / "probes" / name
        probe, log = folder / "Header.lean", folder / (phase + ".log")
        probe_sha = hashlib.sha256(raw).hexdigest()
        atomic_missing(probe, raw, probe_sha)
        argv = [self.value["runtime"]["lean"], "-t0", "-j1", "-M6144", "-DwarningAsError=true",
                "--stdin", relative(name, ".lean"), "--json"]
        self.recheck_base()
        result = subprocess.run(argv, input=raw, cwd=self.gold, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        if result.returncode != 0:
            with tempfile.NamedTemporaryFile(dir=folder, prefix=phase + "-failed-", delete=False) as f:
                f.write(result.stdout)
            print("HEADER_INVENTORY_FAILURE_LOG", f.name, result.stdout[-12000:].decode(errors="replace"), flush=True)
            raise ValueError(f"Header inventory exit {result.returncode}: {f.name}")
        try:
            paths = observed(result.stdout, name, direct)
            closure = self.inputs(paths, roots)
        except (ValueError, OSError):
            with tempfile.NamedTemporaryFile(dir=folder, prefix=phase + "-inventory-failed-", delete=False) as f:
                f.write(result.stdout)
            print("HEADER_INVENTORY_VALIDATION_FAILURE_LOG", f.name, hashlib.sha256(result.stdout).hexdigest(), flush=True)
            raise
        log_sha = hashlib.sha256(result.stdout).hexdigest()
        atomic_missing(log, result.stdout, log_sha)
        witness = {"source": str(probe), "source_sha256": self.bind(probe, "input-probe-source", probe_sha),
                   "command": argv, "log": str(log), "log_sha256": self.bind(log, "input-probe-log", log_sha),
                   "inventory_sha256": signature(closure), "exit_code": 0}
        return closure, witness

    def fresh(self, name):
        source, blob = self.pinned_source(name)
        direct = imports(source.read_text())
        header, prelude = core_header(source.read_text())
        require(header == direct and not prelude, "Unsupported native source header: " + name)
        root = self.view(name)
        roots = [self.lib, root, *self.base.search_path[1:]]
        runtime = self.value["runtime"]
        env = self.base.environment(os.environ)
        env["LEAN_PATH"] = os.pathsep.join(map(str, roots))
        closure, before_probe = self.observe(name, source, direct, roots, env, "before")
        deps = {d: self.modules[d]["closure_signature"] for d in direct if native(d)}
        context = {"module": name, "parent": self.base.raw_sha256, "source": str(source),
                   "source_sha256": self.bind(source, "pinned-buchstab-source"), "git_blob_sha1": blob,
                   "direct_imports": direct, "dependency_signatures": deps, "input_signature": signature(closure),
                   "before_probe": before_probe,
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
            if result.returncode != 0:
                print("NATIVE_COMPILATION_FAILURE_LOG", str(log), log.read_text(errors="replace")[-12000:], flush=True)
            require(result.returncode == 0, f"{name}: Lean exit {result.returncode}, see {log}")
            receipt = {"status": FRESH, "module": name, "context": context, "run": str(run), "command": command,
                       "exit_code": result.returncode, "seconds": round(time.monotonic()-begin, 3),
                       "log_sha256": self.bind(log, "buchstab-compile-log"), "inputs": closure,
                       "compile_credit": False, "kernel_credit": False}
        self.recheck_base()
        require(self.view(name) == root, "Provider overlay changed")
        after, after_probe = self.observe(name, source, direct, roots, env, "after")
        require(after == closure and
                self.pinned_source(name)[1] == blob and self.hashes.digest(self.script) == context["compiler_script_sha256"],
                "Binding changed during compilation")
        parts = {s: self.bind(Path(str(stem) + s), "fresh-buchstab-artifact")
                 for s in (*LOAD_SUFFIXES, ".ilean") if Path(str(stem) + s).is_file()}
        require(".olean" in parts and ".ilean" in parts, "Missing requested compiler output")
        if previous:
            require(receipt["objects"] == parts and receipt["after_probe"] == after_probe,
                    "Prior provider evidence changed")
        else:
            receipt.update(inputs_unchanged=True, objects=parts, after_probe=after_probe)
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
