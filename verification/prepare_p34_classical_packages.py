"""Create an owned view of already pinned P1 package caches.

The first classical-support attempt found a broken Git alternate in the old
goldbach cache. A bounded read-only survey found a healthy, same-pin P3.1
goldbach checkout with the required prebuilt objects. This script references
that checkout and the other healthy package caches without modifying them.

Cli has no built object directory and is not an actual direct proof import.
An independent local Git clone gives it an empty, ignored object directory;
the unchanged proof gate still rejects any unresolved object it really needs.
No external mathematical source is compiled or changed by this preparation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


PACKAGES = {
    "goldbach", "mathlib", "LeanArchitect", "plausible", "LeanSearchClient",
    "importGraph", "proofwidgets", "aesop", "Qq", "batteries", "Cli",
}
OBJECTS = Path(".lake/build/lib/lean")


def git(path: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(path), *args],
                            check=True, text=True, capture_output=True)
    return result.stdout.strip()


def clean_checkout(path: Path, pin: str) -> None:
    if (git(path, "rev-parse", "HEAD") != pin
            or git(path, "status", "--porcelain", "--untracked-files=all")
            or Path(git(path, "rev-parse", "--show-toplevel")).resolve() != path):
        raise RuntimeError("Package identity or clean status differs: " + str(path))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    if (not root.is_relative_to(Path("/workspace"))
            or not root.name.startswith("p34-classical-packages-") or root.exists()):
        raise RuntimeError("Expected a fresh owned package-view directory")
    raw = args.manifest.read_bytes()
    items = json.loads(raw)["packages"]
    pins = {item["name"]: item["rev"] for item in items}
    if set(pins) != PACKAGES or len(pins) != len(items):
        raise RuntimeError("Unexpected package manifest")
    ordinary = Path("/workspace/goldbach-formalization/.lake/packages")
    goldbach = Path("/workspace/p31-smooth-completion-20261127/.lake/packages/goldbach")
    donors = {name: (goldbach if name == "goldbach" else ordinary / name).resolve(strict=True)
              for name in pins}
    for name, donor in donors.items():
        clean_checkout(donor, pins[name])
        if name != "Cli" and not (donor / OBJECTS).is_dir():
            raise RuntimeError("Expected prebuilt object directory: " + str(donor))
    root.mkdir()
    report = {"manifest_sha256": hashlib.sha256(raw).hexdigest(),
              "external_sources_compiled": False, "donor_files_modified": False,
              "package_views": {}, "empty_object_roots": []}
    for name, donor in donors.items():
        target = root / name
        if name == "Cli" and not (donor / OBJECTS).is_dir():
            # --no-local copies reachable Git objects through the local transport;
            # the new repository does not inherit the donor's alternates/hardlinks.
            subprocess.run(["git", "clone", "--no-local", "--no-checkout",
                            str(donor), str(target)], check=True)
            git(target, "checkout", "--detach", pins[name])
            (target / OBJECTS).mkdir(parents=True)
            subprocess.run(["git", "-C", str(target), "check-ignore", "--quiet",
                            str(OBJECTS)], check=True)
            report["empty_object_roots"].append(name)
        else:
            target.symlink_to(donor, target_is_directory=True)
        resolved = target.resolve(strict=True)
        clean_checkout(resolved, pins[name])
        if (resolved / OBJECTS).resolve() != resolved / OBJECTS:
            raise RuntimeError("Redirected package object root")
        report["package_views"][name] = {
            "pin": pins[name], "donor": str(donor), "resolved": str(resolved),
            "object_root": str(resolved / OBJECTS),
            "independent_source_clone": name in report["empty_object_roots"],
        }
    for name, donor in donors.items():
        clean_checkout(donor, pins[name])
    report["status"] = "PREPARED_PINNED_PACKAGE_VIEW"
    output = root / "preparation.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
