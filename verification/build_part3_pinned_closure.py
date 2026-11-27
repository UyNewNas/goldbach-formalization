"""Build reachable project, goldbach and LeanArchitect sources in the pinned Lake environment."""
from __future__ import annotations

import argparse
import fcntl
import functools
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from p31_family_scale_intake import validate_family_scale_intake
import verify_part3_continuation as gate


ROOT = gate.ROOT
CACHE = ROOT / ".lake/p31-direct-compile-v1"
FLAGS = ["-t0", "-j1"]
PARTS = (".olean", ".olean.server", ".olean.private", ".ir")


@functools.lru_cache(maxsize=None)
def file_hash(path: Path, identity: tuple) -> str:
    with path.open("rb") as handle:
        h = hashlib.sha256()
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(block)
        return h.hexdigest()


def digest(path: Path) -> str:
    st = path.stat()
    return file_hash(path, (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns))


def object_parts(obj: Path) -> dict[str, str]:
    if not obj.is_file():
        raise RuntimeError(f"Missing object: {obj}")
    result = {}
    for suffix in PARTS:
        part = obj.with_suffix(suffix)
        if part.exists() or part.is_symlink():
            if not part.is_file() or part.resolve(strict=True) != part:
                raise RuntimeError(f"Invalid object part: {part}")
            result[suffix] = digest(part)
    return result


def command(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def external_source_imports(data: str, source: str) -> tuple[str, ...]:
    """Normalize only the observed public/meta headers in the locked packages."""
    lines = gate.baseline.lean_code(data).splitlines()
    header = []
    seen = set()
    for i, line in enumerate(lines):
        words = line.split()
        if not words:
            continue
        if words == ["module"] and not header:
            continue
        if words[:3] == ["public", "meta", "import"]:
            words = words[2:]
        elif words[:2] in (["public", "import"], ["meta", "import"]):
            words = words[1:]
        if words[0] == "import" and len(words) > 1:
            # Pinned package sources can import the same module twice. Keep
            # the first edge in the build graph; Lean reads the original file.
            for name in words[1:]:
                if name not in seen:
                    header.append("import " + name)
                    seen.add(name)
            continue
        if any("import" in rest.split() for rest in lines[i:]):
            raise RuntimeError("Unsupported or misplaced import in " + source)
        if words in (["public", "meta", "section"], ["public", "section"], ["meta", "section"]):
            words = ["section"]
        header.append(" ".join(words))
        break
    return gate.source_imports("\n".join(header), source)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modules", nargs="+", required=True)
    parser.add_argument("--check-only", action="store_true",
                        help="Only check reachable sources and prebuilt external objects")
    args = parser.parse_args()
    modules, closure, _, _ = validate_family_scale_intake(
        ROOT, gate.FAMILY_SCALE_BUDGET_MODULES, gate.validate_project_closure)
    if len(set(args.modules)) != len(args.modules) or not set(args.modules) <= set(modules):
        parser.error("--modules must select distinct modules in the pinned project closure")
    projects = {row["module"]: row for row in closure["project_sources"]}

    manifest_path = ROOT / "lake-manifest.json"
    if digest(manifest_path) != gate.baseline.CONFIG_SHA256["lake-manifest.json"]:
        raise RuntimeError("Changed dependency manifest")
    manifest = json.loads(manifest_path.read_text())
    pkgs = {p["name"]: (ROOT / manifest["packagesDir"] / p["name"]).resolve()
            for p in manifest["packages"]}
    revisions = {p["name"]: p["rev"] for p in manifest["packages"]}
    # Determine namespace ownership from the pinned trees, even in a partially
    # missing checkout. A foreign .olean cannot substitute for a tracked source.
    owners: dict[str, list[str]] = {}
    for name, pkg in pkgs.items():
        if command("git", "rev-parse", "HEAD", cwd=pkgs[name]) != revisions[name]:
            raise RuntimeError(f"Incorrect package revision: {name}")
        tree = subprocess.check_output(
            ["git", "ls-tree", "-r", "-z", "--name-only", revisions[name]], cwd=pkg)
        for path in tree.decode().split("\0"):
            if path.endswith(".lean"):
                owners.setdefault(path, []).append(name)
    env = json.loads(command("lake", "env", sys.executable, "-c",
                             "import os,json; print(json.dumps(dict(os.environ)))"))
    sysroot = Path(env["LEAN_SYSROOT"]).resolve()
    lean = (sysroot / "bin/lean").resolve(strict=True)
    if Path(shutil.which("lean", path=env["PATH"]) or "/nonexistent").resolve() != lean:
        raise RuntimeError("Lake does not resolve Lean from the pinned sysroot")
    version = subprocess.check_output([lean, "--version"], env=env, text=True)
    if gate.LEAN_COMMIT not in version or "version 4.33.0-rc1" not in version:
        raise RuntimeError("Unexpected Lean version: " + version)
    search = [(ROOT / p).resolve() for p in env["LEAN_PATH"].split(os.pathsep) if p]
    syslib = sysroot / "lib/lean"
    # Lean subprocesses run from their owning package, not the root workspace.
    env["LEAN_PATH"] = os.pathsep.join(map(str, search))
    search.append(syslib)
    objdir = Path(".lake/build/lib/lean")
    source_packages = [pkgs["goldbach"], pkgs["LeanArchitect"]]
    owned = {}
    external = {}
    pending = set()

    def resolved(name: str) -> Path | None:
        relative = Path(*name.split(".")).with_suffix(".olean")
        return next((root / relative for root in search if (root / relative).is_file()), None)

    def visit(name: str) -> None:
        if name in owned or name in external:
            return
        if name in pending:
            raise RuntimeError("Import cycle: " + name)
        relative = Path(*name.split(".")).with_suffix(".lean")
        namespace = name.split(".", 1)[0]
        if name in projects:
            pkg = ROOT
        elif namespace in {"Init", "Lean", "Std", "Lake"}:
            pkg = None  # Only the pinned toolchain can own these modules.
        else:
            candidates = owners.get(relative.as_posix(), [])
            if len(candidates) != 1 or (namespace == "Mathlib" and candidates != ["mathlib"]):
                raise RuntimeError(f"Expected a unique pinned owner for {name}, found {candidates}")
            pkg = pkgs[candidates[0]]
            tracked_source = pkg / relative
            if not tracked_source.is_file() or tracked_source.resolve() != tracked_source:
                raise RuntimeError(f"Missing or redirected tracked package source: {tracked_source}")

        if pkg != ROOT and pkg not in source_packages:
            owner_root = syslib if pkg is None else (pkg / objdir).resolve()
            obj = owner_root / relative.with_suffix(".olean")
            if resolved(name) != obj:
                raise RuntimeError(f"Missing or shadowed pinned external object: {name}; expected {obj}")
            object_parts(obj)
            external[name] = obj
            return

        source = pkg / relative
        data = source.read_bytes()
        if source.resolve() != source:
            raise RuntimeError(f"Source escapes its checkout: {source}")
        if pkg in source_packages:
            tracked = subprocess.check_output(["git", "show", "HEAD:" + relative.as_posix()], cwd=pkg)
            if data != tracked:
                raise RuntimeError(f"Source differs from the pinned dependency revision: {name}")
        elif hashlib.sha256(data).hexdigest() != projects[name]["sha256"]:
            raise RuntimeError(f"Project source pin changed: {name}")
        read_imports = gate.source_imports if pkg == ROOT else external_source_imports
        imports = read_imports(data.decode(), str(source))
        if "Init" not in imports:
            imports += ("Init",)
        pending.add(name)
        for dep in imports:
            visit(dep)
        pending.remove(name)
        output_root = (pkg / objdir).resolve()
        if output_root not in search:
            raise RuntimeError(f"Object directory absent from LEAN_PATH: {output_root}")
        obj = output_root / relative.with_suffix(".olean")
        if (any(obj.with_suffix(ext).resolve() != obj.with_suffix(ext) for ext in PARTS)
                or resolved(name) not in (None, obj)):
            raise RuntimeError(f"Unexpected selected module resolution: {name}")
        owned[name] = (pkg, relative, imports, obj, hashlib.sha256(data).hexdigest())

    for name in args.modules:
        visit(name)
    # With no -o this asks the pinned Lean reader to load the complete import
    # environment of every boundary object, including its transitive imports.
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake", prefix="p31-preload-") as directory:
        probe = Path(directory) / "ExternalBoundary.lean"
        probe.write_text("".join(f"import {name}\n" for name in sorted(external)))
        subprocess.run([lean, *FLAGS, probe.name], env=env, cwd=directory, check=True)
    print(f"Checked {len(owned)} reachable source modules and {len(external)} external objects",
          flush=True)
    if args.check_only:
        return
    CACHE.mkdir(parents=True, exist_ok=True)
    # Only one direct builder can publish receipts into this checkout at once.
    with (CACHE / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        compiler = digest(lean)
        builder = digest(Path(__file__).resolve())
        objects = dict(external)
        for index, (name, (pkg, relative, imports, obj, source_sha)) in enumerate(owned.items(), 1):
            def inputs() -> dict:
                if digest(pkg / relative) != source_sha:
                    raise RuntimeError(f"Source changed during build: {name}")
                deps = {}
                for dep in imports:
                    if resolved(dep) != objects[dep]:
                        raise RuntimeError(f"Dependency resolution changed: {dep}")
                    deps[dep] = {"object_path": str(objects[dep]), "parts": object_parts(objects[dep])}
                return {"module": name, "source": source_sha, "compiler": compiler, "builder": builder,
                        "flags": FLAGS, "output": str(obj), "dependencies": deps}

            signature = inputs()
            stamp = CACHE / (name + ".json")
            try:
                record = json.loads(stamp.read_text())
            except (FileNotFoundError, UnicodeDecodeError, json.JSONDecodeError):
                record = {}
            if not isinstance(record, dict):
                record = {}
            if (record.get("inputs") == signature and obj.is_file()
                    and record.get("outputs") == object_parts(obj)):
                print(f"REUSE {index}/{len(owned)} {name}", flush=True)
            else:
                print(f"COMPILE {index}/{len(owned)} {name}", flush=True)
                stamp.unlink(missing_ok=True)
                obj.parent.mkdir(parents=True, exist_ok=True)
                for suffix in PARTS:
                    obj.with_suffix(suffix).unlink(missing_ok=True)
                subprocess.run([lean, *FLAGS, "-o", obj, relative], env=env, cwd=pkg, check=True)
                if resolved(name) != obj or inputs() != signature:
                    raise RuntimeError(f"Changed build identity: {name}")
                candidate = stamp.with_suffix(".tmp")
                candidate.write_text(json.dumps({"inputs": signature, "outputs": object_parts(obj)},
                                                sort_keys=True) + "\n")
                candidate.replace(stamp)
            objects[name] = obj


if __name__ == "__main__":
    main()
