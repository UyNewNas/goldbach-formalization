#!/usr/bin/env python3
"""Bind existing native inputs for the actual P2.7 source closure.

The verified Winner9 snapshot is a read-only donor, never an expanded request.
Missing providers require the original coherent checkpoint, the anchored P6
TailPropagation receipt, or either of its two explicitly bound P6 prerequisites.
This program invokes no Lean/Lake/object loader.
Only a fresh directory in the isolated project is written. Its final gate is
the unchanged ExternalSnapshot consumer; no proof or compilation credit follows.

Small census/binding/map helpers are adapted from the concurrent P2.4 adapter
whose reviewed input SHA is recorded below. That worktree is neither imported
nor modified. The shared original descriptor checker remains byte-for-byte.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

sys.dont_write_bytecode = True
import repack_winner9_native_cache as carrier
from inspect_winner9_owner_native import git as readonly_git, imports as source_imports
from qualify_winner9_native_cache import LOAD_SUFFIXES, PROTOCOL, PROTOCOL_SHA256
from winner9_external_snapshot import (ExternalSnapshot, PhysicalHashes, PINS, SCHEMA,
                                      STATUS, native, require, signature)

ROOT = "ImbalancedChen.P2PairedCertificateCompletion"
MATHLIB_PIN = carrier.PINS["mathlib"]
P24_HELPER_SOURCE_SHA = "7d6d21862fe96b2c504befd03d02c235839b499d034cf833abc75e57bc8230d3"
TAIL = "MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation"
P6_ROOT = "/workspace/blue-p6-build"
MEMBER_ROOT = "/workspace/blue-member-build"
P6_EVIDENCE = "/workspace/blue-member-aggregate-evidence"
P6_RECEIPT = P6_EVIDENCE + "/P6_SINGLE_NATIVE_INSTALL_RECEIPT.json"
P6_RECEIPT_SHA = "2ee4c313ad8f640aa72ba1665aa54f39df99891b6755773c9e824747f17f2cec"
P6_RECEIPT_BYTES = 9510550
P6_RECHECK_COUNT = 16622
P6_RECHECK_SHA = "f73bb5702c220d213ea3acd8823d13169a91d6e6c30e48f917e46939e2843726"
P6_STOCK_SHA = "22fe127049eabc1ee9f25009855d233c472a85497eb5b2d8f0bc5c9f9040bf69"
P6_SOURCE_SHA = "16fbf5f74a67a969fea728e69b7ddef3659acc566cd4ec15de60797120936146"
P6_OBJECT_SHA = "92f67d7cf5dbfe85f1de4255ea28872194ee554a1948da0026eaee7d5ec52950"
P6_FUNCTION = "MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction"
P6_BOUNDS = "MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds"
P6_SHADOW = "/workspace/blue-build-tools/runtime/p0-ci-shadow-toolchain"
P6_COMPILER_SHA = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
P6_RUNTIME_STATE = "/workspace/blue-build-tools/runtime-evidence/state.json"
P6_RUNTIME_STATE_SHA = "e474b9cb4b9e4d9cc4cc0c3ba58b29b0096f1bdec6f104d2e41a17f521ca232b"
P6_RUNTIME_LOG = "/workspace/blue-build-tools/runtime-evidence/compiler-commands.jsonl"
P6_RUNTIME_LOG_SHA = "a5a4a446dc0ce049cffb4afc518a1d2a5c308a966a9a31a4506d5c136bc1072b"
P6_SELECTION = "/workspace/blue-p6-selection.json"
P6_SELECTION_SHA = "5655b541f17120d3d535308478fe70f5d2b49739462a399675d4d88aeb277a62"
P6_SOURCE_CONTEXT = "/workspace/blue-p6-controller/zero/SOURCE_CONTEXT.json"
P6_SOURCE_CONTEXT_SHA = "7cea7c4f196b662a72fd84b00c99ede50dad0da971da57ba139a8868db2b2be2"
# These two original P6 producers are separate from the CP and Tail's source
# authority. The fixed Tail history supplies only their dependency/object SHAs.
P6_PREREQUISITES = {
    P6_FUNCTION: {
        "source": ("f3f113386eb0c3effb3269b824707b05e7a8588e633cff050f6f11249c5896e3", 5760),
        "pid": 20291, "line": 183, "native_dependencies": [],
        "map_sha256": "492f4c41a12370026e20d8afcbcda27b59b7002de32b59112d312e204d081baa",
        "import_modules": 3255, "import_facets": 16275,
        "facets": {
            ".olean": ("f78a815dea0aad0833aac831dc2233cdcd3fd5c7681d6220be3b253786b1b5ee", 313800),
            ".ilean": ("a6ec27eda5621f7b496641bcee12bf6063faa3ae9135e36727f6133b6730d829", 17104),
            ".trace": ("d84b7f373e1143fb218e12522041f3a4e7a4e8f159234ec1b4e3971d539f0777", 3278),
            ".setup.json": ("840ba7b2fc756630378c8dcfbbdde395ae8ae1b1897fa0df90da55d23214bd17", 2228484),
            ".c": ("0194057b46f3236a4920c7a059f15f2dcb254722910b295e88423602f3a1ebf3", 5622),
            ".olean.hash": ("4aae503d66d5b7e07a018a0773a06fc7168c9958681238d5a29e5da97b93114d", 16),
            ".ilean.hash": ("40db1cb3102f3421cfdbc760982185fd1243c81adbefd4866f4fc395a0ee1c45", 16),
            ".c.hash": ("ed22f60c35fe5bf19e212ffee31053f6e536fd56cefabbe90637767bb6dc0cfb", 16),
        },
    },
    P6_BOUNDS: {
        "source": ("a0dad36599799030975f7eb1ab08bdb9d827f07ed205308e40b0c03c60c92a24", 6145),
        "pid": 20310, "line": 186, "native_dependencies": [P6_FUNCTION],
        "map_sha256": "6bcd2f8ec2d50264d0dd2d55f027151bb12f04b1431de32de173f7f3bdfb3b53",
        "import_modules": 3325, "import_facets": 16621,
        "facets": {
            ".olean": ("40e6739d0928ae2c70deca8b80307dd87595f0076c851e4a2cf9e0098a749b75", 417864),
            ".ilean": ("c19e45f0b360194c0a890ab7e5f573de20c76185af9a95beb040f936db54b580", 23414),
            ".trace": ("110a39253b48b77e1dbefae355e85def269f2899eff6b4208c4034bf652b47ca", 3116),
            ".setup.json": ("f26d51db94674c4c4547b59d5dd88d43cc35d4dee8dc760491f310b1cae025ec", 2278118),
            ".c": ("e9f3bf8ae269f852e10d3668fcfcd042b87960d499f094b7e4e4654c5a745f20", 1764),
            ".olean.hash": ("99067b093d91d9335bd5396e204d886e16676ad8de9e6f75a20dca09f85bb9c4", 16),
            ".ilean.hash": ("9e1fcbc4a7e3df86990b537c830e92aa0eed4accc1df18885b406ccb50b0af47", 16),
            ".c.hash": ("bfccc1d596cc949cd5655b29c676ec1fc252c60eea4a2a15f5ef13eca8f0c9c0", 16),
        },
    },
}


def write_new(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def module_path(name: str) -> str:
    require(isinstance(name, str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", name),
            "Unsafe module name")
    return name.replace(".", "/")


def source_row(path: Path, package: str, hashes: PhysicalHashes) -> dict:
    raw = path.read_bytes()
    sha = hashlib.sha256(raw).hexdigest()
    require(hashes.digest(path) == sha, "Source changed during census")
    return {"package": package, "source": str(path.resolve()), "source_sha256": sha,
            "source_bytes": len(raw), "git_blob_sha1": carrier.blob_sha(raw),
            "direct_imports": source_imports(raw.decode())}


def project_census(project: Path, hashes: PhysicalHashes) -> tuple[dict, list[str]]:
    nodes, order, active = {}, [], set()

    def visit(name: str) -> None:
        require(name not in active, "Project import cycle: " + name)
        if name in nodes:
            return
        nodes[name] = source_row(project / (module_path(name) + ".lean"), "project", hashes)
        active.add(name)
        for dep in nodes[name]["direct_imports"]:
            if dep.startswith("ImbalancedChen."):
                visit(dep)
        active.remove(name)
        order.append(name)

    visit(ROOT)
    return nodes, order


def ordered_import_map(setup: dict, cwd: str, receipts: dict, expected: str | None = None) -> dict:
    result = {}
    items = setup["importArts"].items() if isinstance(setup["importArts"], dict) else setup["importArts"]
    require(Path(cwd).is_absolute(), "Original command cwd is not absolute")
    for name, groups in items:
        module_path(name)
        require(name not in result and isinstance(groups, list) and groups, "Duplicate or empty original import group")
        result[name] = []
        for group in groups:
            require(isinstance(group, list) and group, "Empty original import subgroup")
            for text in group:
                path = Path(text)
                require(".." not in path.parts, "Unsafe original import path")
                absolute = str(path if path.is_absolute() else Path(cwd) / path)
                require(absolute in receipts, "Original import lacks SHA receipt: " + absolute)
                result[name].append([absolute, receipts[absolute]["sha256"]])
    require(expected is None or signature(result) == expected, "Original actual-import-map SHA differs")
    return result


def p6_recheck_table(rows: list, count: int, expected_signature: str) -> dict:
    require(isinstance(rows, list) and len(rows) == count, "P6 full import recheck count differs")
    require(signature(rows) == expected_signature, "P6 import recheck canonical SHA differs")
    result = {}
    for row in rows:
        module_path(row["module"])
        path = row["P6_path"]
        require(Path(path).is_absolute() and ".." not in Path(path).parts, "Unsafe original P6 import path")
        require(path not in result, "Duplicate P6 physical import")
        require(row["same_actual_object_bytes_reconfirmed"] is True, "Original P6 input was not reconfirmed")
        require(re.fullmatch("[0-9a-f]{64}", row["sha256"]), "Malformed P6 input SHA")
        result[path] = row
    return result


def p6_setup_map(setup: dict, cwd: str, rows: dict) -> dict:
    original = ordered_import_map(setup, cwd, rows)
    flattened = [(n, p) for n, parts in original.items() for p, _ in parts]
    require(len(flattened) == len(rows) and len({p for _, p in flattened}) == len(rows)
            and {p for _, p in flattened} == set(rows)
            and all(rows[p]["module"] == n for n, p in flattened),
            "P6 setup differs from complete original import checks")
    return original


def p6_prerequisite_event(name: str, event: dict) -> dict:
    require(name in P6_PREREQUISITES, "P6 prerequisite source authority is scoped to Function/Bounds")
    spec = P6_PREREQUISITES[name]
    package = P6_ROOT + "/.lake/packages/goldbach"
    relative = module_path(name)
    source, lib, ir = (package + "/" + relative + ".lean",
                       package + "/.lake/build/lib/lean/" + relative,
                       package + "/.lake/build/ir/" + relative)
    arguments = [source, "-o", lib + ".olean", "-i", lib + ".ilean", "-c", ir + ".c",
                 "--setup", ir + ".setup.json", "--json"]
    require(event["pid"] == spec["pid"] and event["slot_owner"] == str(spec["pid"])
            and event["tool"] == "lean" and event["cwd"] == P6_ROOT and event["sysroot"] == P6_SHADOW
            and event["input_args"] == arguments
            and event["command"] == [P6_SHADOW + "/bin/lean-runtime", "-t0", "-j2", "-M12288"] + arguments,
            "Original prerequisite source/output/guard event differs")
    return event


def p6_subset_map(setup: dict, cwd: str, rows: dict, expected: str,
                  modules: int, facets: int, native_dependencies: list[str]) -> dict:
    original = ordered_import_map(setup, cwd, rows, expected)
    flattened = [(n, p) for n, parts in original.items() for p, _ in parts]
    require(len(original) == modules and len(flattened) == facets
            and len({p for _, p in flattened}) == facets
            and all(rows[p]["module"] == n for n, p in flattened)
            and {n for n in original if native(n)} == set(native_dependencies),
            "Original prerequisite import subset/module ownership differs")
    return original


def p6_completed_outputs(trace: dict, outputs: dict[str, Path]) -> bool:
    # The original collector's completed-output rule does not infer an exit
    # code from a source invocation. Preserve that boundary explicitly.
    require(trace.get("schemaVersion") == "2025-09-10" and trace.get("synthetic") is False
            and isinstance(trace.get("depHash"), str) and bool(trace["depHash"])
            and isinstance(trace.get("outputs"), dict)
            and all(trace["outputs"].get(key) for key in ("o", "i", "c"))
            and all(suffix in outputs and outputs[suffix].is_file() and outputs[suffix].stat().st_size > 0
                    for suffix in (".olean", ".ilean", ".c")),
            "Original prerequisite lacks completed bound outputs")
    return True


class NativeTransfer:
    """A byte locator. Every get requires an independently authenticated SHA."""
    def __init__(self, root: Path, hashes: PhysicalHashes) -> None:
        self.root = root.resolve(strict=True)
        self.hashes = hashes
        self.manifest_path = self.root / "MANIFEST.json"
        require(not self.manifest_path.is_symlink(), "Transport manifest is a symlink")
        self.manifest_sha = hashes.digest(self.manifest_path)
        value = json.loads(self.manifest_path.read_text())
        require(value.get("schema") == "p27-native-byte-transfer-v1"
                and value.get("compile_credit") is False and value.get("kernel_credit") is False,
                "Transport must not grant qualification or proof credit")
        self.files = value["files"]
        for original, row in self.files.items():
            require(Path(original).is_absolute() and ".." not in Path(original).parts, "Unsafe original transport path")
            relative = PurePosixPath(row["relative_path"])
            require(not relative.is_absolute() and ".." not in relative.parts
                    and str(relative) == row["relative_path"]
                    and relative.parts == ("objects", row["sha256"])
                    and re.fullmatch("[0-9a-f]{64}", row["sha256"]), "Unsafe content-addressed transport path")
            path = self.root / relative
            require(not path.is_symlink() and not path.parent.is_symlink(), "Transport payload contains a symlink")
            require(path.is_file() and path.resolve().is_relative_to(self.root), "Missing transport payload")
            require(isinstance(row["bytes"], int) and row["bytes"] >= 0, "Malformed transport length")

    def get(self, original: str, expected: str, size: int | None = None) -> Path:
        require(self.hashes.digest(self.manifest_path) == self.manifest_sha, "Transport manifest changed")
        require(original in self.files, "Missing original byte supplier: " + original)
        row = self.files[original]
        require(row["sha256"] == expected and (size is None or row["bytes"] == size),
                "Transport differs from independently bound original SHA/length: " + original)
        path = self.root / row["relative_path"]
        require(not path.is_symlink() and not path.parent.is_symlink()
                and path.stat().st_size == row["bytes"] and self.hashes.digest(path) == expected,
                "Current transport bytes differ: " + original)
        return path


class InputBindings:
    def __init__(self, hashes: PhysicalHashes) -> None:
        self.hashes, self.bound = hashes, {}

    def bind(self, path: Path, role: str, expected: str | None = None, size: int | None = None) -> dict:
        path = path.resolve(strict=True)
        require(path.is_file(), "Physical input is not a file")
        row = {"sha256": self.hashes.digest(path), "bytes": path.stat().st_size, "role": role}
        require(expected is None or row["sha256"] == expected, "Physical SHA differs: " + str(path))
        require(size is None or row["bytes"] == size, "Physical length differs: " + str(path))
        previous = self.bound.get(str(path))
        require(previous is None or all(previous[k] == row[k] for k in ("sha256", "bytes")),
                "Previously bound input changed: " + str(path))
        self.bound[str(path)] = previous or row
        return row

    def recheck(self) -> None:
        for path, row in list(self.bound.items()):
            self.bind(Path(path), row["role"], row["sha256"], row["bytes"])


def install_view_module(view: Path, name: str, facets: dict, *, copy: bool) -> dict:
    require(".olean" in facets and set(facets) <= set(LOAD_SUFFIXES), "Unexpected native loadable facet set")
    stem = view / module_path(name)
    destinations = {suffix: Path(str(stem) + suffix) for suffix in facets}
    require(all(not p.exists() and not p.is_symlink() for p in destinations.values()), "Refusing to overwrite namespace file")
    result = {}
    for suffix, target in destinations.items():
        source = facets[suffix].resolve(strict=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        if copy:
            with target.open("xb") as stream:
                stream.write(source.read_bytes())
        else:
            target.symlink_to(source)
        result[suffix] = target.resolve(strict=True)
    return result


def publish_snapshot(value: dict, out: Path, lean: str, mathlib_pin: str, project_lib: Path) -> Path:
    pending, target = out / "PENDING_EXTERNAL_SNAPSHOT.json", out / "EXTERNAL_SNAPSHOT.json"
    write_new(pending, value)
    ExternalSnapshot(pending, lean=lean, mathlib_pin=mathlib_pin, project_lib=project_lib).verify()
    require(not target.exists(), "Refusing to overwrite snapshot")
    pending.rename(target)
    try:
        ExternalSnapshot(target, lean=lean, mathlib_pin=mathlib_pin, project_lib=project_lib).verify()
    except Exception:
        target.rename(out / "REJECTED_EXTERNAL_SNAPSHOT.json")
        raise
    return target


class P27Qualification(InputBindings):
    def __init__(self, args) -> None:
        super().__init__(PhysicalHashes())
        self.project = args.project_root.resolve(strict=True)
        self.out = args.out.resolve()
        self.project_lib = self.project / ".lake/p2-private/lib"
        raw_base = json.loads(args.base_snapshot.read_text())
        self.lean = raw_base["runtime"]["lean"]
        self.base = ExternalSnapshot(args.base_snapshot, lean=self.lean, mathlib_pin=MATHLIB_PIN,
                                     project_lib=self.project_lib)
        require(not self.out.exists() and self.out.is_relative_to(self.project)
                and not self.out.is_relative_to(args.bundle.resolve())
                and not self.out.is_relative_to(self.base.path.parent)
                and not self.out.is_relative_to(self.project_lib.resolve())
                and all(not self.out.is_relative_to(Path(r["root"]).resolve())
                        for r in self.base.value["packages"].values()),
                "Use a new evidence directory outside all donor roots in the isolated P2.7 checkout")
        self.out.mkdir(parents=True)
        self.view = self.out / "lib/lean"
        self.bound = copy.deepcopy(self.base.files)
        self.bind(self.base.path, "immutable-base-snapshot", self.base.raw_sha256)
        self.bundle = NativeTransfer(args.bundle, self.hashes)
        self.bind(self.bundle.manifest_path, "transport-only-manifest", self.bundle.manifest_sha)
        self.packages = {name: Path(row["root"]) for name, row in self.base.value["packages"].items()}
        self.check_packages()
        checkpoint = args.checkpoint
        if checkpoint is None:
            choices = [Path(p) for p, r in self.base.files.items() if r["sha256"] == carrier.ARTIFACT["checkpoint_sha256"]]
            require(len(choices) == 1, "Supply the original coherent CHECKPOINT.json explicitly")
            checkpoint = choices[0]
        self.bind(checkpoint, "original-checkpoint", carrier.ARTIFACT["checkpoint_sha256"], carrier.ARTIFACT["checkpoint_bytes"])
        self.cp = json.loads(checkpoint.read_text())
        require(self.cp["schema"] == "t01-coherent-build-checkpoint-v3"
                and self.cp["source_commit"] == carrier.ARTIFACT["producer_commit"]
                and self.cp["runtime_audit_valid"] is True and self.cp["all_dependency_source_pins_valid"] is True,
                "Original checkpoint identity/audits differ")
        self.bind(PROTOCOL, "original-descriptor-validator", PROTOCOL_SHA256)
        spec = importlib.util.spec_from_file_location("p27_original_descriptor_protocol", PROTOCOL)
        require(spec is not None and spec.loader is not None, "Cannot load original descriptor validator")
        self.protocol = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.protocol)
        for path in (Path(__file__), Path(carrier.__file__), Path(sys.modules["winner9_external_snapshot"].__file__),
                     Path(sys.modules["qualify_winner9_native_cache"].__file__)):
            self.bind(path, "qualification-tool")
        self.bind(Path(sys.modules["inspect_winner9_owner_native"].__file__), "fixed-source-parser", carrier.CENSUS_SCRIPT_SHA)
        self.projects, self.project_order = project_census(self.project, self.hashes)
        self.nodes, self.order, active = {}, [], set()

        def visit(name: str) -> None:
            require(name not in active, "Native source import cycle: " + name)
            if name in self.nodes:
                return
            package = "LeanArchitect" if name.split(".")[0] == "Architect" else "goldbach"
            relative = module_path(name) + ".lean"
            path = self.packages[package] / relative
            row = source_row(path, package, self.hashes)
            require(readonly_git(self.packages[package], "show", "HEAD:" + relative) == path.read_bytes(),
                    "Native source differs from pinned Git bytes: " + name)
            self.nodes[name] = row
            self.bind(path, "current-native-source", row["source_sha256"], row["source_bytes"])
            active.add(name)
            for dep in row["direct_imports"]:
                if native(dep):
                    visit(dep)
            active.remove(name)
            self.order.append(name)

        self.entries = sorted({d for r in self.projects.values() for d in r["direct_imports"] if native(d)})
        for name in self.entries:
            visit(name)
        self.missing = {name: row for name, row in self.nodes.items() if name not in self.base.modules}
        cp_wanted = {name: row for name, row in self.missing.items() if name != TAIL}
        self.selected, self.omitted, _, _ = carrier.select_payloads(self.cp, {"requested": cp_wanted})
        self.qualified, self.objects, self.blocked, self.rebindings = {}, {}, {}, {}
        self.resolutions = {n: p for n, p in self.base.value["resolutions"].items() if not native(n)}
        self.base_by_sha = {}
        for path, row in self.base.files.items():
            self.base_by_sha.setdefault(row["sha256"], []).append(path)
        scope = {"schema": "p27-actual-source-native-scope-v1", "roots": [ROOT],
                 "project_root": str(self.project), "project_modules": self.projects,
                 "project_count": len(self.projects), "direct_native_entries": self.entries,
                 "native_modules": self.nodes, "native_count": len(self.nodes),
                 "missing_from_base": sorted(self.missing), "base_snapshot": self.base.binding(),
                 "adapted_census_binding_helpers_p24_sha256": P24_HELPER_SOURCE_SHA,
                 "compile_credit": False, "kernel_credit": False}
        write_new(self.out / "SOURCE_SCOPE.json", scope)
        self.bind(self.out / "SOURCE_SCOPE.json", "current-p27-scope")

    def check_packages(self) -> None:
        lock = {r["name"]: r["rev"] for r in json.loads((self.project / "lake-manifest.json").read_text())["packages"]}
        for name, pin in {**PINS, "mathlib": MATHLIB_PIN}.items():
            require(lock.get(name) == pin, "Current project package pin differs: " + name)
        for name, root in self.packages.items():
            require(readonly_git(root, "rev-parse", "HEAD").decode().strip() == PINS[name]
                    and not readonly_git(root, "diff", "HEAD", "--"), "Native source package changed: " + name)

    def transport(self, original: str, expected: str, size: int | None = None) -> Path:
        path = self.bundle.get(original, expected, size)
        self.bind(path, "original-portable-byte-supplier", expected, size)
        return path

    def metadata(self, name: str, facets: list, old_package: str) -> tuple[dict, dict, dict]:
        root = self.out / "original-metadata" / name
        loadable = {}
        for row in facets:
            original = row["original_path"]
            require(original.startswith(old_package + "/"), "Original facet is outside selected package")
            relative = original[len(old_package) + 1:]
            stems = [".lake/build/" + d + "/" + module_path(name) + "." for d in ("lib/lean", "ir")]
            require(".." not in PurePosixPath(relative).parts and any(relative.startswith(s) for s in stems)
                    and not relative.endswith(carrier.EXECUTABLE_SUFFIXES)
                    and relative.endswith(tuple(carrier.PORTABLE_SUFFIXES)), "Unreviewed original native facet")
            payload = self.transport(original, row["sha256"], row["bytes"])
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            require(not target.exists() and not target.is_symlink(), "Duplicate original metadata facet")
            target.symlink_to(payload)
            for suffix in LOAD_SUFFIXES:
                if relative == ".lake/build/lib/lean/" + module_path(name) + suffix:
                    loadable[suffix] = payload
        stem = root / ".lake/build/lib/lean" / module_path(name)
        ir = root / ".lake/build/ir" / module_path(name)
        setup_path, trace_path = Path(str(ir) + ".setup.json"), Path(str(stem) + ".trace")
        setup, trace = json.loads(setup_path.read_text()), json.loads(trace_path.read_text())
        require(setup["name"] == name and setup["package"] == self.nodes[name]["package"]
                and setup["options"] == {} and not setup["plugins"] and not setup["dynlibs"],
                "Original setup source/options/plugins differ")
        require(trace["schemaVersion"] == "2025-09-10" and trace["synthetic"] is False,
                "Original trace is incomplete/synthetic")
        checks = self.protocol.lake_descriptor_binding(trace["outputs"], stem, ir)
        require(checks and all(r["matched"] for r in checks), "Original trace/output descriptors do not bind")
        return setup, loadable, {"setup": str(setup_path.resolve()), "trace": str(trace_path.resolve()), "descriptor_checks": checks}

    def import_artifact(self, name: str, original: str, expected: str) -> Path:
        stem = name.rsplit(".", 1)[-1]
        filename = Path(original).name
        require(filename.startswith(stem + "."), "Imported artifact belongs to another module")
        suffix = filename[len(stem):]
        require(suffix in LOAD_SUFFIXES, "Unreviewed imported facet suffix")
        if native(name):
            require(name in self.nodes and name in self.qualified, "Actual native import lacks its own qualified provider: " + name)
            require(suffix in self.objects[name], "Native provider lacks an actual imported facet")
            path = self.objects[name][suffix]
        else:
            require(name in self.base.value["resolutions"], "Standard import absent from verified base: " + name)
            obj = self.base.value["resolutions"][name]
            require(obj.endswith(".olean"), "Malformed base public object")
            path = Path(obj[:-len(".olean")] + suffix).resolve(strict=True)
            require(str(path) in self.base.files and self.base.files[str(path)]["sha256"] == expected,
                    "Standard facet is not byte-exact in verified base: " + str(path))
        self.bind(path, "actual-imported-artifact", expected)
        if suffix == ".olean":
            previous = self.resolutions.setdefault(name, str(path))
            require(previous == str(path), "Conflicting actual object resolution")
        return path

    def rebind_map(self, original_map: dict, *, checkpoint_sources: bool) -> dict:
        current = {}
        for name, parts in original_map.items():
            if checkpoint_sources:
                origin = self.cp["actual_import_sources"].get(name)
                require(origin is not None and "source" in origin, "Missing original imported source: " + name)
                row = origin["source"]
                if native(name):
                    source = Path(self.nodes[name]["source"])
                else:
                    candidates = [Path(p) for p in self.base_by_sha.get(row["sha256"], [])
                                  if p.endswith("/" + module_path(name) + ".lean")]
                    require(len(candidates) == 1, "Original imported source absent/ambiguous in verified base: " + name)
                    source = candidates[0]
                self.bind(source, "actual-imported-source", row["sha256"], row["bytes"])
            current[name] = []
            for original, sha in parts:
                path = self.import_artifact(name, original, sha)
                current[name].append([str(path), sha])
                item = {"module": name, "current": str(path), "sha256": sha, "bytes": path.stat().st_size}
                previous = self.rebindings.setdefault(original, item)
                require(previous == item, "Conflicting original-to-current rebinding")
        return current

    def checkpoint_provider(self, name: str) -> tuple[dict, dict]:
        require(name in self.selected, self.omitted.get(name, "NO_ORIGINAL_PROVIDER") + ":" + name)
        selected = self.selected[name]
        require(selected["original_classification"] == carrier.CLASSIFIED,
                "ORIGINAL_QUARANTINE_RETAINED_REQUIRES_INDEPENDENT_RECEIPT:" + name)
        row = self.cp[selected["original_record_collection"]][selected["original_guarded_row_index"]]
        source = selected["source"]
        self.bind(Path(self.nodes[name]["source"]), "selected-native-source", source["sha256"], source["bytes"])
        commands = selected["original_guarded_commands"]
        require(commands and all(c["tool"] == "lean" and "-t0" in c["command"]
                and all(not t.startswith("-D") for t in c["input_args"]) for c in commands),
                "Original guarded native command differs")
        old_package = self.cp["runtime_state"]["root"] + "/.lake/packages/" + selected["package"]
        setup, facets, metadata = self.metadata(name, selected["facets"], old_package)
        original = ordered_import_map(setup, row["command"]["cwd"], self.cp["files"], row["actual_import_map_sha256"])
        current = self.rebind_map(original, checkpoint_sources=True)
        return facets, {"original_authority": "coherent-checkpoint", "checkpoint_sha256": carrier.ARTIFACT["checkpoint_sha256"],
                        "original_record_collection": selected["original_record_collection"],
                        "original_guarded_row_index": selected["original_guarded_row_index"],
                        "original_classification": selected["original_classification"],
                        "original_import_map_sha256": signature(original), "actual_import_map_sha256": signature(current), **metadata}

    def p6_runtime_bindings(self, state: dict) -> list[dict]:
        wrappers = {state["shadow"] + "/bin/" + tool for tool in state["tools"]}
        payloads = {p: sha for p, sha in state["runtime_sha256"].items() if p not in wrappers}
        require(len(payloads) == 11, "Original P6 prerequisite runtime payload census differs")
        sysroot = Path(self.base.value["runtime"]["sysroot"])
        result = []
        for original, sha in payloads.items():
            basename = Path(original).name
            current = (sysroot / "bin" / ("lean" if basename == "lean-runtime" else basename)).resolve(strict=True)
            require(str(current) in self.base.files and self.base.files[str(current)]["sha256"] == sha,
                    "Original P6 prerequisite payload is not the qualified current runtime")
            self.bind(current, "p6-prerequisite-runtime-rebound", sha)
            result.append({"original": original, "current": str(current), "sha256": sha})
        return result

    def p6_prerequisite_provider(self, name: str) -> tuple[dict, dict]:
        require(name in P6_PREREQUISITES, "P6 prerequisite authority is scoped to Function/Bounds")
        spec = P6_PREREQUISITES[name]
        old_package = P6_ROOT + "/.lake/packages/goldbach"
        relative = module_path(name)
        old_source = old_package + "/" + relative + ".lean"
        source_sha, source_bytes = spec["source"]
        current_source = Path(self.nodes[name]["source"])
        self.bind(current_source, "p6-prerequisite-current-source", source_sha, source_bytes)
        original_source = self.transport(old_source, source_sha, source_bytes)
        require(original_source.read_bytes() == current_source.read_bytes(), "P6 prerequisite source bytes differ")

        selection_path = self.transport(P6_SELECTION, P6_SELECTION_SHA, 1183673)
        context_path = self.transport(P6_SOURCE_CONTEXT, P6_SOURCE_CONTEXT_SHA, 457553)
        selection, context = json.loads(selection_path.read_text()), json.loads(context_path.read_text())
        pins = {**PINS, "mathlib": MATHLIB_PIN, "lean": "v4.33.0-rc1"}
        selected = selection["native_sources"][name]
        wanted_context = {"install_path": relative + ".lean", "source_path": relative + ".lean",
                          "source_commit": PINS["goldbach"], "sha256": source_sha}
        require(selection["pins"] == context["pins"] == pins
                and context["summary"]["all_native_sources_exact_selected_hashes"] is True
                and context["native_sources"][name] == wanted_context
                and all(selected[k] == v for k, v in wanted_context.items())
                and selected["module"] == name and selected["repository"] == "subfish-zhou/goldbach-lean"
                and selected["bytes"] == source_bytes and selected["blob_verified"] is True
                and selected["git_blob_sha1"] == carrier.blob_sha(current_source.read_bytes())
                and selected["imports"] == self.nodes[name]["direct_imports"],
                "Original P6 prerequisite source/pin context differs")

        state_path = self.transport(P6_RUNTIME_STATE, P6_RUNTIME_STATE_SHA, 4391)
        log_path = self.transport(P6_RUNTIME_LOG, P6_RUNTIME_LOG_SHA, 2058624)
        state = json.loads(state_path.read_text())
        require(state["schema"] == "p0-ci-runtime-v1" and state["shadow"] == P6_SHADOW
                and state["log"] == P6_RUNTIME_LOG
                and state["environment"]["LEAN_SYSROOT"] == P6_SHADOW
                and state["environment"]["P0_CI_GUARD_STATE"] == P6_RUNTIME_STATE
                and state["environment"]["LEAN_NUM_THREADS"] == "2"
                and state["environment"]["ELAN_TOOLCHAIN"] == "leanprover/lean4:v4.33.0-rc1"
                and state["runtime_sha256"][P6_SHADOW + "/bin/lean-runtime"] == P6_COMPILER_SHA
                and state["runtime_sha256"][state["realbin"] + "/lean"] == P6_COMPILER_SHA,
                "Original P6 prerequisite runtime binding differs")
        self.bind(Path(self.lean), "p6-prerequisite-current-compiler", P6_COMPILER_SHA)
        runtime_bindings = self.p6_runtime_bindings(state)
        events = [json.loads(line) for line in log_path.read_text().splitlines()]
        matches = [(i + 1, e) for i, e in enumerate(events) if old_source in e.get("input_args", [])]
        require(len(matches) == 1 and matches[0][0] == spec["line"], "Original P6 prerequisite source event absent/ambiguous")
        event = p6_prerequisite_event(name, matches[0][1])

        receipt_path = self.transport(P6_RECEIPT, P6_RECEIPT_SHA, P6_RECEIPT_BYTES)
        receipt = json.loads(receipt_path.read_text())
        require(receipt["module"] == TAIL
                and receipt["status"] == "PORTABLE_GROUP_REUSED_STOCK_UP_TO_DATE_ZERO_SOURCE_CALLS"
                and receipt["P6_files_modified"] is False and not receipt["blocked_imports"]
                and receipt["runtime_compiler_sha256"] == P6_COMPILER_SHA
                and receipt["runtime_policy"] == state["policy"], "Anchored P6 dependency history differs")
        rows = p6_recheck_table(receipt["actual_import_rechecks"], P6_RECHECK_COUNT, P6_RECHECK_SHA)
        public_object = old_package + "/.lake/build/lib/lean/" + relative + ".olean"
        require(public_object in rows and rows[public_object]["module"] == name
                and rows[public_object]["sha256"] == spec["facets"][".olean"][0],
                "Prerequisite object is not the independently anchored P6 object")

        facets, payloads = [], {}
        for suffix, (sha, size) in spec["facets"].items():
            directory = "ir" if suffix in (".c", ".c.hash", ".setup.json") else "lib/lean"
            original = old_package + "/.lake/build/" + directory + "/" + relative + suffix
            payloads[suffix] = self.transport(original, sha, size)
            facets.append({"original_path": original, "sha256": sha, "bytes": size})
        setup, objects, metadata = self.metadata(name, facets, old_package)
        trace = json.loads(payloads[".trace"].read_text())
        require(setup["isModule"] is False and set(objects) == {".olean"}
                and {r["part"] for r in metadata["descriptor_checks"]} == {"o", "i", "c"},
                "Original prerequisite output mode/descriptor scope differs")
        p6_completed_outputs(trace, payloads)
        trace_inputs = {row[0] for row in trace["inputs"]}
        require(old_source in trace_inputs and "Module.name: " + name in trace_inputs
                and "Package.id?: (some goldbach)" in trace_inputs and "Module.leanArgs: #[]" in trace_inputs,
                "Original prerequisite trace source/arguments differ")
        original = p6_subset_map(setup, event["cwd"], rows, spec["map_sha256"],
                                 spec["import_modules"], spec["import_facets"], spec["native_dependencies"])
        # No qualified Tail is consulted: Function has only standard imports;
        # Bounds imports the independently qualified Function object.
        current = self.rebind_map(original, checkpoint_sources=False)

        stock_path = self.transport(P6_EVIDENCE + "/P6_SINGLE_NATIVE_PRODUCER_STOCK.json", P6_STOCK_SHA, 749)
        stock = json.loads(stock_path.read_text())
        require(stock["exit_code"] == 0 and stock["cwd"] == P6_ROOT and stock["no_build_enforced"] is True
                and stock["stock_output_all_targets_up_to_date"] is True
                and stock["command"] == ["python3", "/workspace/blue-build-tools/run_guarded.py", "--state",
                                         P6_RUNTIME_STATE, "lake", "--no-build", "build", "@goldbach/+" + TAIL + ":olean"],
                "Original P6 dependency-context stock differs")
        stock_log = self.transport(stock["log"], stock["log_sha256"])
        return objects, {"original_authority": "p6-own-guarded-prerequisite-completed-outputs",
                         "source_selection": str(selection_path), "source_context": str(context_path),
                         "original_runtime_state": str(state_path), "original_runtime_log": str(log_path),
                         "source_runtime_event": event, "source_runtime_event_line": spec["line"],
                         "runtime_compiler_sha256": P6_COMPILER_SHA,
                         "runtime_bindings": runtime_bindings,
                         "completion_evidence": "guarded invocation and completed bound outputs; current imports rebound",
                         "source_exit_code_recorded": False, "lake_completed_trace": True, "output_bound_command": True,
                         "object_and_import_hash_authority": str(receipt_path),
                         "object_and_import_hash_authority_sha256": P6_RECEIPT_SHA,
                         "dependency_context_stock": {"module": TAIL, "receipt": str(stock_path), "log": str(stock_log),
                                                      "exit_code": 0, "direct_prerequisite_stock_credit": False},
                         "actual_import_facets_rechecked": spec["import_facets"],
                         "original_import_map_sha256": signature(original), "actual_import_map_sha256": signature(current),
                         **metadata}

    def missing_provider(self, name: str) -> tuple[dict, dict]:
        if name == TAIL:
            return self.p6_provider(name)
        if name in self.selected or name not in P6_PREREQUISITES:
            return self.checkpoint_provider(name)
        require(self.omitted.get(name) == "NO_SOURCE_MATCHING_ORIGINAL_GUARDED_ROW",
                "P6 prerequisite path cannot override another original refusal: " + name)
        return self.p6_prerequisite_provider(name)

    def p6_provider(self, name: str) -> tuple[dict, dict]:
        require(name == TAIL, "P6 receipt is scoped to TailPropagation only")
        receipt_path = self.transport(P6_RECEIPT, P6_RECEIPT_SHA, P6_RECEIPT_BYTES)
        receipt = json.loads(receipt_path.read_text())
        require(receipt["module"] == TAIL and receipt["status"] == "PORTABLE_GROUP_REUSED_STOCK_UP_TO_DATE_ZERO_SOURCE_CALLS"
                and receipt["source_sha256"] == P6_SOURCE_SHA and receipt["setup_options"] == {}
                and receipt["source_files_modified"] is False and receipt["P6_files_modified"] is False
                and receipt["native_executables_installed"] is False and receipt["no_clobber"] is True
                and not receipt["blocked_imports"] and receipt["import_facet_rechecks"] == P6_RECHECK_COUNT,
                "Original P6 receipt boundary differs")
        self.bind(Path(self.nodes[name]["source"]), "p6-selected-native-source", P6_SOURCE_SHA)
        self.bind(Path(self.lean), "p6-runtime-compiler", receipt["runtime_compiler_sha256"])
        event = receipt["source_runtime_event"]
        source = P6_ROOT + "/.lake/packages/goldbach/" + module_path(name) + ".lean"
        require(event["tool"] == "lean" and event["cwd"] == P6_ROOT
                and event["command"][1:4] == ["-t0", "-j2", "-M12288"]
                and event["command"][4:] == event["input_args"] and source in event["input_args"]
                and not any(t.startswith("-D") for t in event["input_args"]), "Original P6 trust-zero source event differs")
        rows = p6_recheck_table(receipt["actual_import_rechecks"], P6_RECHECK_COUNT, P6_RECHECK_SHA)
        qualification_original = P6_EVIDENCE + "/" + receipt["import_qualification_receipt"]
        require(qualification_original == P6_EVIDENCE + "/P6_SINGLE_NATIVE_IMPORT_QUALIFICATION.json", "P6 qualification pointer changed")
        # This companion record is checked against the anchored full receipt;
        # its transport hash alone is never an independent historical authority.
        qrow = self.bundle.files.get(qualification_original)
        require(qrow is not None, "Missing complete original P6 import qualification")
        qpath = self.transport(qualification_original, qrow["sha256"], qrow["bytes"])
        qual = json.loads(qpath.read_text())
        require(qual["unresolved_count"] == 0 and qual["all_checked_matches"] is True
                and len(qual["current_checks"]) == P6_RECHECK_COUNT, "Original P6 import qualification incomplete")
        qseen = set()
        for check in qual["current_checks"]:
            old = check["P6_path"]
            require(old in rows and old not in qseen and all(check[k] == rows[old][k]
                    for k in ("module", "P6_path", "Member_path", "sha256", "method")),
                    "P6 qualification does not match anchored full rechecks")
            qseen.add(old)
        require(qseen == set(rows), "P6 qualification is not the complete actual import set")
        stock_original = P6_EVIDENCE + "/" + receipt["producer_stock_receipt"]
        require(stock_original == P6_EVIDENCE + "/P6_SINGLE_NATIVE_PRODUCER_STOCK.json", "P6 producer pointer changed")
        stock_path = self.transport(stock_original, P6_STOCK_SHA, 749)
        stock = json.loads(stock_path.read_text())
        require(stock["exit_code"] == 0 and stock["no_build_enforced"] is True
                and stock["stock_output_all_targets_up_to_date"] is True, "Original P6 producer stock failed")
        self.transport(stock["log"], stock["log_sha256"])
        destination = receipt["destination_stock"]
        require(destination["exit_code"] == 0 and destination["no_build_enforced"] is True
                and destination["source_compiler_calls_for_target"] == 0
                and destination["copied_facet_hashes_unchanged"] is True, "Original P6 receiver boundary failed")
        self.transport(P6_EVIDENCE + "/" + destination["log"], destination["log_sha256"])
        old_package = P6_ROOT + "/.lake/packages/goldbach"
        facets = []
        for f in receipt["installed_files"]:
            original = old_package + "/" + f["relative_path"]
            facets.append({"original_path": original, "sha256": f["sha256"], "bytes": f["bytes"]})
        setup, objects, metadata = self.metadata(name, facets, old_package)
        require(setup["isModule"] is False, "Original P6 module mode differs")
        require(".olean" in objects and self.hashes.digest(objects[".olean"]) == P6_OBJECT_SHA,
                "Original P6 public object differs")
        original = p6_setup_map(setup, event["cwd"], rows)
        current = self.rebind_map(original, checkpoint_sources=False)
        return objects, {"original_authority": "p6-anchored-complete-install-receipt", "original_receipt": str(receipt_path),
                         "original_receipt_sha256": P6_RECEIPT_SHA, "original_import_qualification": str(qpath),
                         "original_producer_stock": str(stock_path), "source_runtime_event": event,
                         "runtime_policy": receipt["runtime_policy"], "runtime_compiler_sha256": receipt["runtime_compiler_sha256"],
                         "actual_import_facets_rechecked": len(rows), "original_rechecks_sha256": P6_RECHECK_SHA,
                         "original_import_map_sha256": signature(original), "actual_import_map_sha256": signature(current), **metadata}

    def base_provider(self, name: str) -> tuple[dict, dict]:
        row = self.base.modules[name]
        wanted = self.nodes[name]
        require(row["imports"] == wanted["direct_imports"] and row["git_blob_sha1"] == wanted["git_blob_sha1"]
                and self.base.files[row["source"]]["sha256"] == wanted["source_sha256"], "Base native source differs")
        facets = {}
        for suffix in LOAD_SUFFIXES:
            path = Path(row["object"][:-len(".olean")] + suffix)
            if path.is_file():
                physical = str(path.resolve(strict=True))
                require(physical in self.base.files, "Unbound extra base native facet")
                facets[suffix] = path
        return facets, copy.deepcopy(row["provider"])

    def run(self) -> int:
        for name in self.order:
            deps = [d for d in self.nodes[name]["direct_imports"] if native(d)]
            if any(d not in self.qualified for d in deps):
                self.blocked[name] = "UNQUALIFIED_NATIVE_DEPENDENCIES:" + ",".join(d for d in deps if d not in self.qualified)
                continue
            try:
                if name in self.base.modules:
                    facets, provider = self.base_provider(name)
                    objects = install_view_module(self.view, name, facets, copy=False)
                else:
                    facets, evidence = self.missing_provider(name)
                    objects = install_view_module(self.view, name, facets, copy=True)
                    record = {"schema": "p27-existing-native-provider-rebind-v1", "status": "EXACT_ORIGINAL_IMPORTS_REBOUND",
                              "module": name, "source": self.nodes[name]["source"], "source_sha256": self.nodes[name]["source_sha256"],
                              "objects": {str(p): self.bind(p, "qualified-native-artifact", self.hashes.digest(facets[s]))
                                          for s, p in objects.items()}, **evidence,
                              "new_source_compilation": False, "compile_credit": False, "kernel_credit": False,
                              "historical_classifications_modified": False}
                    path = self.out / "providers" / (name + ".json")
                    write_new(path, record)
                    self.bind(path, "native-provider-receipt")
                    provider = {"status": "EXACT_ORIGINAL_IMPORTS_REBOUND", "receipt": str(path)}
                self.objects[name], self.qualified[name] = objects, provider
                self.resolutions[name] = str(objects[".olean"])
            except (OSError, ValueError, KeyError, TypeError) as error:
                self.blocked[name] = str(error)
        table = self.out / "ORIGINAL_TO_CURRENT_IMPORTS.json"
        write_new(table, {"schema": "p27-original-to-current-physical-imports-v1", "paths": self.rebindings,
                          "reconstruction": "Preserve each original setup importArts group and order; resolve relative paths against its original cwd; substitute each path using this table."})
        self.bind(table, "actual-import-rebinding-table")
        self.base.verify()
        self.check_packages()
        for row in self.projects.values():
            self.bind(Path(row["source"]), "current-project-source", row["source_sha256"], row["source_bytes"])
        self.recheck()
        status = "NATIVE_QUALIFICATION_INCOMPLETE" if self.blocked else "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED"
        receipt = self.out / "QUALIFICATION.json"
        result = {"schema": "p27-native-input-qualification-v1", "status": status,
                  "roots": [ROOT], "project_count": len(self.projects), "native_count": len(self.nodes),
                  "qualified": self.qualified, "blocked": self.blocked, "base_snapshot": self.base.binding(),
                  "original_to_current_imports": {"path": str(table), "sha256": self.hashes.digest(table)},
                  "source_compiler_invocations": 0, "object_loader_invocations": 0,
                  "compile_credit": False, "kernel_credit": False, "historical_classifications_modified": False,
                  "old_snapshot_modified": False, "donor_files_modified": False}
        write_new(receipt, result)
        self.bind(receipt, "native-qualification-receipt")
        if self.blocked:
            print(json.dumps({"status": status, "blocked": self.blocked, "receipt": str(receipt)}), flush=True)
            return 2
        modules = {}
        for name in self.order:
            wanted = self.nodes[name]
            row = {"package": wanted["package"], "source": wanted["source"], "object": self.resolutions[name],
                   "imports": wanted["direct_imports"], "git_blob_sha1": wanted["git_blob_sha1"],
                   "dependency_signatures": {d: modules[d]["closure_signature"] for d in wanted["direct_imports"] if native(d)},
                   "provider": self.qualified[name]}
            bound = {k: row[k] for k in ("source", "object", "imports", "dependency_signatures", "provider")}
            bound.update(module=name, source_sha256=self.bound[row["source"]]["sha256"], object_sha256=self.bound[row["object"]]["sha256"])
            row["closure_signature"] = signature(bound)
            modules[name] = row
        runtime = copy.deepcopy(self.base.value["runtime"])
        runtime["lean_path"] = [str(self.view)] + runtime["lean_path"]
        value = {"schema": SCHEMA, "status": STATUS, "compile_credit": False, "kernel_credit": False,
                 "runtime": runtime, "packages": self.base.value["packages"],
                 "qualification": {"path": str(receipt), "sha256": self.hashes.digest(receipt), "status": status},
                 "modules": modules, "files": self.bound, "resolutions": self.resolutions,
                 "caller_scope": "P2.7 actual reachable native source closure; input qualification only"}
        value["context_signature"] = signature(value)
        target = publish_snapshot(value, self.out, self.lean, MATHLIB_PIN, self.project_lib)
        print(json.dumps({"status": status, "snapshot": str(target), "snapshot_sha256": self.hashes.digest(target),
                          "project_count": len(self.projects), "native_count": len(self.nodes),
                          "compile_credit": False, "kernel_credit": False}), flush=True)
        return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--base-snapshot", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    existed = args.out.exists()
    try:
        return P27Qualification(args).run()
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        failure = {"status": "NATIVE_QUALIFICATION_INCOMPLETE", "fatal_blocker": str(error),
                   "compile_credit": False, "kernel_credit": False}
        path = args.out.resolve() / "FAILURE.json"
        if not existed and path.parent.is_dir() and not path.exists():
            write_new(path, failure)
        print(json.dumps(failure), flush=True)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
