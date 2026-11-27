"""Read-only reuse survey and strict diagnostic compile of original analytic sources.

Authored locally, transferred verbatim. This is not a full acceptance driver.
It creates only fresh owned directories and preserves every diagnostic.
"""
from __future__ import annotations

import base64
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace
import zipfile

HEAD = "3193c2dfda0f05c334b918da3a4724907660311f"
TREE = "69b8009c630a2b033dd8c46f46da1e68c5c70a65"
ROOT = Path("/workspace/p34-primitive-original-3193c2df-20261127-r1")
OUT = Path("/workspace/p34-primitive-original-receipts-20261127-r1")
SOURCES = {
    "ImbalancedChen.Part3RealEisensteinSeedConvergence": "993cceaf94ae2a7801ac36079c89c7e39b116231fd1c65d396c9649b2b4a208a",
    "ImbalancedChen.Part3PrimitiveEisensteinParameterAnalytic": "1c943f9bbfc275a61b5f6b4c3647c006f2efb7463ba338f8a40e4746cee855aa",
    "ImbalancedChen.Part3PrimitiveEisensteinFourierParameterAnalytic": "1531f0d6a61eaf8ec8bf7fc81fba8b5912246e41b1ca803374793f6a25e35a33",
}
HELPERS = ["verification/verify_p34_classical_support.py",
           "verification/verify_p34_cusp_normalization.py",
           "verification/verify_variable_envelope_boxes.py"]
REQUIRED = [".gitignore", "lean-toolchain", "lake-manifest.json", "lakefile.toml",
            *HELPERS, *(m.replace(".", "/") + ".lean" for m in SOURCES)]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if ROOT.exists() or OUT.exists():
        raise RuntimeError("Fresh diagnostic directories already exist")
    OUT.mkdir()
    data = {"status": "DIAGNOSTIC_STARTING", "source": HEAD, "tree": TREE,
            "probe_sha256": digest(Path(__file__)), "acceptance_claimed": False}
    receipt = None
    exit_code = 1

    def command(label, argv, cwd=None, input_text=None):
        result = subprocess.run(argv, cwd=cwd, input=input_text, capture_output=True, text=True)
        (OUT / (label + ".log")).write_text("command=" + json.dumps(argv) + "\n" +
                                           result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(label + " exited " + str(result.returncode))
        return result.stdout.strip()

    try:
        candidates = []
        roots_checked = []
        # Only current conventional loose project caches, never archive archaeology.
        for root in sorted(Path("/workspace").iterdir()):
            if not root.is_dir() or root.name.startswith("."):
                continue
            objroot = root / ".lake/build/lib/lean"
            if not objroot.is_dir():
                continue
            roots_checked.append(str(objroot))
            for module, expected in SOURCES.items():
                relative = module.replace(".", "/")
                obj, source = objroot / (relative + ".olean"), root / (relative + ".lean")
                if obj.is_file():
                    candidates.append({"module": module, "object": str(obj),
                                       "object_sha256": digest(obj),
                                       "source": str(source),
                                       "source_matches": source.is_file() and digest(source) == expected})
        data["reuse_survey"] = {"roots_checked": roots_checked, "candidates": candidates,
                                "scope": "One-level conventional loose project object roots only"}
        print("P34_PRIMITIVE_REUSE_SURVEY " + json.dumps(data["reuse_survey"]), flush=True)
        if candidates:
            data["status"] = "REUSE_CANDIDATES_REQUIRE_REVIEW"
            exit_code = 0
        else:
            command("git-init", ["git", "init", str(ROOT)])
            command("git-remote", ["git", "remote", "add", "origin",
                    "https://github.com/UyNewNas/goldbach-formalization.git"], ROOT)
            command("git-fetch", ["git", "fetch", "--depth=8", "--filter=blob:none",
                    "--no-tags", "origin", HEAD], ROOT)
            tree = command("git-tree", ["git", "rev-parse", HEAD + "^{tree}"], ROOT)
            if tree != TREE:
                raise RuntimeError("Original source tree differs")
            command("git-sparse", ["git", "sparse-checkout", "set", "--no-cone", "--stdin"], ROOT,
                    "".join("/" + path + "\n" for path in REQUIRED))
            command("git-checkout", ["git", "checkout", "--detach", HEAD], ROOT)
            sys.dont_write_bytecode = True
            sys.path.insert(0, str(ROOT / "verification"))
            import verify_p34_classical_support as common

            class ProbeReceipt(common.Receipt):
                def __init__(self):
                    self.out = OUT
                    self.data = data
                    self.env = dict(os.environ)
                    self.data.update(status="DIAGNOSTIC_RUNNING", stages=[], baseline_commit=HEAD,
                                     expected_head=HEAD, targets=list(SOURCES))
                    self.save()

            receipt = ProbeReceipt()
            common.git_checkout(receipt, ROOT, "initial", HEAD)
            closure = common.project_closure(ROOT, tuple(SOURCES))
            if (closure["topological_order"] != list(SOURCES) or
                    any(row["sha256"] != SOURCES[row["module"]]
                        for row in closure["project_sources"])):
                raise RuntimeError("Original source closure differs")
            data["project_import_closure"] = closure
            hashes = data["source_sha256"] = {p: digest(ROOT / p) for p in REQUIRED}
            for relative, expected in common.CONFIG_SHA256.items():
                if hashes[relative] != expected:
                    raise RuntimeError("Pinned configuration differs")
            for module in SOURCES:
                text = (ROOT / common.module_file(module, ".lean")).read_text()
                if common.FORBIDDEN.search(common.lean_code(text)):
                    raise RuntimeError("Forbidden proof escape: " + module)
            objroot = ROOT / common.OBJECTS
            objroot.mkdir(parents=True)
            if common.checkout_object_parts():
                raise RuntimeError("Project object root is not empty")
            args = SimpleNamespace(toolchain_root=Path("/workspace/toolchains/lean-4.33.0-rc1-linux"),
                                   package_root=Path("/workspace/p34-classical-packages-20261127-v1"))
            tools, tool_hashes, packages, syslib = common.prepare_environment(receipt, args, objroot)
            if tool_hashes != common.TOOL_HASHES:
                raise RuntimeError("Pinned compiler binaries differ")
            data["external_scope"] = {"configured_packages": list(packages),
                                      "direct_source_imports": closure["external_imports"],
                                      "full_external_kernel_replay_claimed": False}
            fresh = set()
            bindings = data["project_object_bindings"] = {}
            parsed = data["parsed_dependencies"] = {}
            external = data["direct_external_object_bindings"] = {}
            for module in SOURCES:
                source = common.module_file(module, ".lean")
                stage = module.split(".")[-1]
                print("DIAGNOSTIC_COMPILE " + module, flush=True)
                log = receipt.run(stage + "-imports", tools["lean"], "--deps", source)
                parsed[module] = common.expected_deps(ROOT / source, log, fresh, objroot, packages, syslib)
                for name in parsed[module]:
                    if Path(name) not in fresh:
                        external[name] = common.external_object_parts(Path(name))
                obj = objroot / common.module_file(module, ".olean")
                obj.parent.mkdir(parents=True, exist_ok=True)
                receipt.run(stage + "-strict", tools["lean"], "-t0", "-j1", "-M12000",
                            "-DwarningAsError=true", "-o", obj, source)
                bindings[module] = common.bind_object(module, objroot, (*packages.values(), syslib))
                fresh.add(obj)
            if any(digest(ROOT / p) != h for p, h in hashes.items()):
                raise RuntimeError("Source changed during diagnostic compilation")
            common.git_checkout(receipt, ROOT, "final", HEAD)
            data["status"] = "DIAGNOSTIC_COMPILED_NO_ACCEPTANCE"
            exit_code = 0
    except BaseException as error:
        data.update(status="DIAGNOSTIC_FAILED", error=str(error))
        print("P34_PRIMITIVE_DIAGNOSTIC_ERROR " + str(error), flush=True)
        if receipt and data.get("stages"):
            log = OUT / (data["stages"][-1]["name"] + ".log")
            if log.is_file():
                print(log.read_text(errors="replace")[:24000], flush=True)
    finally:
        (OUT / "report.json").write_text(json.dumps(data, indent=2) + "\n")
        (OUT / "probe.py").write_bytes(Path(__file__).read_bytes())
        members = {p.name: p.read_bytes() for p in OUT.iterdir() if p.is_file()}
        manifest = {n: {"bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}
                    for n, b in members.items()}
        members["ARCHIVE_MEMBERS.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
        payload = io.BytesIO()
        with zipfile.ZipFile(payload, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for n, b in members.items():
                archive.writestr(n, b)
        raw = payload.getvalue()
        path = Path(str(OUT) + ".zip")
        if path.exists():
            raise RuntimeError("Diagnostic archive already exists")
        path.write_bytes(raw)
        print("P34_PRIMITIVE_DIAGNOSTIC_EVIDENCE " + json.dumps({"path": str(path),
              "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
              "base64": base64.b64encode(raw).decode()}), flush=True)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
