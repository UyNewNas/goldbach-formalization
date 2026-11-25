#!/usr/bin/env python3
"""Union previously verified P2 exports, checking every owned declaration.

This consumes evidence; it does not compile Lean or grant new proof credit.
An exported module may recur only when its source, object, compile closure,
inventory, imports and complete owned declaration records are identical.
Receipt/driver differences remain explicit provenance. A changed source is
rejected for a separate current/superseded review, never silently replaced.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import lzma
from pathlib import Path
import re
import sys
import tarfile
import time


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROOF_META = (
    "source_sha256", "object_sha256", "compile_closure_signature",
    "project_modules", "declaration_count", "page_binding", "axiom_counts",
)
DEFAULT_ARCHIVES = [
    "docs/verification/20261124-p2-private/evidence-checkpoint-20261124.slim.tar.xz",
    "docs/verification/20261124-p2-private/evidence-wu-prefix-20261124.slim.tar.xz",
    "docs/verification/20261124-p2-private/evidence-numerical16-31-20261124.slim.tar.xz",
    "docs/verification/20261125-p2-resume/evidence-numerical32-63-20261125-canonical.slim.tar.xz",
    "docs/verification/20261125-p2-resume/evidence-resume-main-20261125.slim.tar.xz",
    "docs/verification/20261125-p2-resume/evidence-euler-word-20261125.slim.tar.xz",
    "docs/verification/20261125-p2-resume/evidence-numerical80-111-rank-20261125.slim.tar.xz",
]


class UnionError(ValueError):
    """A concrete evidence inconsistency; no accepted output may be written."""


def require(condition, message):
    if not condition:
        raise UnionError(message)


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def unique_strings(value, context):
    require(isinstance(value, list) and all(isinstance(x, str) for x in value),
            f"{context}: expected string list")
    require(len(set(value)) == len(value), f"{context}: duplicate entry")
    return sorted(value)


def validate_payload(module, meta, payload):
    """Validate all serialized owners, including private/generated constants."""
    declarations = payload["declarations"]
    require(isinstance(declarations, list), f"{module}: invalid declaration list")
    require(len(declarations) == payload["declaration_count"] == meta["declaration_count"],
            f"{module}: declaration count mismatch")
    owned = {}
    axiom_counts = collections.Counter()
    for declaration in declarations:
        name = declaration["name"]
        require(isinstance(name, str) and name, f"{module}: invalid owned name")
        require(name not in owned, f"{module}: duplicate owned name {name}")
        require(declaration["module"] == module, f"{name}: incorrect owner")
        for flag in ("unsafe", "partial", "axiom"):
            require(declaration[flag] is False, f"{name}: forbidden {flag}")
        require(isinstance(declaration["type"], str) and bool(declaration["type"]),
                f"{name}: missing full type")
        axioms = unique_strings(declaration["axioms"], f"{name} axioms")
        require(set(axioms) <= ALLOWED_AXIOMS, f"{name}: unexpected transitive axiom")
        axiom_counts.update(axioms)
        # Preserve and compare every field, not only the count/name/type/axioms.
        owned[name] = declaration
    expected_axioms = dict(sorted(axiom_counts.items()))
    require(expected_axioms == payload["axiom_counts"] == meta["axiom_counts"],
            f"{module}: axiom count mismatch")
    inventory = payload["inventory"]
    require(inventory["module"] == module, f"{module}: inventory owner mismatch")
    for key in ("environment", "serialized"):
        names = unique_strings(inventory[key], f"{module} inventory {key}")
        require(names == sorted(owned), f"{module}: incomplete {key} inventory")
    imports = unique_strings(payload["imports"], f"{module} imports")
    normalized_inventory = dict(inventory)
    normalized_inventory["environment"] = sorted(inventory["environment"])
    normalized_inventory["serialized"] = sorted(inventory["serialized"])
    return {
        "owned": dict(sorted(owned.items())),
        "inventory": normalized_inventory,
        "imports": imports,
        "axioms": set(axiom_counts),
    }


class OwnedUnion:
    def __init__(self):
        self.modules = {}
        self.owners = {}
        self.duplicates = {}
        self.axioms = set()
        self.raw_module_count = 0
        self.raw_owned_count = 0

    def add(self, module, meta, validated, occurrence):
        """Merge exactly equal proof records; reject all cross-owner clashes."""
        self.raw_module_count += 1
        self.raw_owned_count += len(validated["owned"])
        if module in self.modules:
            previous = self.modules[module]
            for field in PROOF_META:
                require(meta[field] == previous["meta"][field],
                        f"{module}: duplicate proof metadata differs: {field}")
            for field in ("owned", "inventory", "imports"):
                require(validated[field] == previous["validated"][field],
                        f"{module}: duplicate complete {field} differs")
            previous["occurrences"].append(occurrence)
            self.duplicates[module] = previous
            return False
        for name in validated["owned"]:
            require(name not in self.owners,
                    f"cross-module owned name collision: {name}: "
                    f"{self.owners.get(name)} versus {module}")
        for name in validated["owned"]:
            self.owners[name] = module
        self.axioms.update(validated["axioms"])
        self.modules[module] = {
            "meta": meta, "validated": validated, "occurrences": [occurrence],
        }
        return True

    def result(self, archives, expected_rows):
        rows = set()
        pages = {}
        modules = {}
        for module, item in sorted(self.modules.items()):
            meta, checked = item["meta"], item["validated"]
            binding = meta["page_binding"]
            if binding:
                first, count = binding["first_ordinal"], binding["row_count"]
                require(type(first) is int and first >= 0 and type(count) is int and count > 0,
                        f"{module}: invalid numeric page binding")
                new_rows = set(range(first, first + count))
                require(not rows & new_rows, f"{module}: overlapping numeric rows")
                rows |= new_rows
                pages[module] = binding
            modules[module] = {
                key: meta[key] for key in PROOF_META
            }
            modules[module].update({
                "archive": item["occurrences"][0]["archive"],
                "receipt_sha256": item["occurrences"][0]["receipt_sha256"],
                "owned_records_sha256": digest(checked["owned"]),
                "owned_names_sha256": digest(sorted(checked["owned"])),
                "inventory_sha256": digest(checked["inventory"]),
                "imports_sha256": digest(checked["imports"]),
                "occurrences": item["occurrences"],
            })
        require(rows == set(range(expected_rows)),
                f"numeric row set is not exactly 0..{expected_rows - 1}")
        duplicates = {}
        for module, item in sorted(self.duplicates.items()):
            occurrences = item["occurrences"]
            duplicates[module] = {
                "declaration_count": len(item["validated"]["owned"]),
                "occurrence_count": len(occurrences),
                "counted_once": True,
                "policy": "identical source/object/compile closure/project modules; exact complete owned records; equal imports and complete inventory",
                "proof_metadata_fields_compared": list(PROOF_META),
                "owned_records_sha256": digest(item["validated"]["owned"]),
                "owned_names": sorted(item["validated"]["owned"]),
                "provenance_differences": {
                    key: [occurrence[key] for occurrence in occurrences]
                    for key in occurrences[0]
                    if any(occurrence[key] != occurrences[0][key] for occurrence in occurrences)
                },
                "occurrences": occurrences,
            }
        duplicate_count = self.raw_owned_count - len(self.owners)
        require(duplicate_count == sum(
            len(item["validated"]["owned"]) * (len(item["occurrences"]) - 1)
            for item in self.duplicates.values()), "owned count accounting mismatch")
        return {
            "schema": 3,
            "status": "ACCEPTED_VERIFIED_DEDUPLICATED_EXPORT_UNION_NOT_FULL_P2",
            "archives": archives,
            "raw_export_module_occurrences": self.raw_module_count,
            "raw_export_owned_declaration_occurrences": self.raw_owned_count,
            "accepted_modules": len(self.modules),
            "owned_declarations": len(self.owners),
            "unique_owned_declarations": len(self.owners),
            "deduplicated_module_count": len(duplicates),
            "deduplicated_owned_declaration_occurrences": duplicate_count,
            "deduplicated_modules": duplicates,
            "duplicate_owned_declarations": {},
            "cross_module_owned_name_collisions": {},
            "superseded_records": [],
            "numeric_pages": len(pages),
            "numeric_block_aggregators": sum(bool(re.fullmatch(
                r"ImbalancedChen.P2Winner9NumericalCheck[0-9]{2}", module)) for module in modules),
            "numeric_row_count": len(rows),
            "numeric_ordinals": [min(rows), max(rows)] if rows else [],
            "numeric_ordinals_sha256": digest(sorted(rows)),
            "expected_numeric_rows": 11026,
            "remaining_numeric_rows": 11026 - len(rows),
            "expected_numeric_pages": 690,
            "remaining_numeric_pages": 690 - len(pages),
            "transitive_axiom_names": sorted(self.axioms),
            "owned_name_to_module_sha256": digest(dict(sorted(self.owners.items()))),
            "modules": modules,
            "numeric_page_bindings": pages,
            "full_winner9_family_claimed": False,
            "full_p2_complete": False,
            "boundary": (
                "Union of seven previously verified exports. Every serialized/environment owned "
                "declaration, including generated/private auxiliaries, is checked for ownership, "
                "complete type and allowed transitive axioms. Repeated modules are counted once "
                "only after exact proof metadata and full owned-record equality. Their distinct "
                "receipts remain recorded. Different modules may not own the same name. Every "
                "current module matches active source bytes. No Lean compilation, replay, new "
                "proof credit, full winner-9 or full P2 completion is claimed by this union."
            ),
        }


def scan_archive(path, repo, union, cache_dir=None, progress=None):
    """One sequential archive pass; selected declarations are hashed before use."""
    started = time.monotonic()
    manifest = None
    selected = {}
    extracted = {}
    manifest_sha = None
    relative = path.relative_to(repo).as_posix()
    # The main archive expands to 4.35 GB. A 1 MiB uncompressed stream buffer
    # avoids tarfile's default 10 KiB compressed-stream skip/copy overhead.
    with lzma.open(path, "rb") as decoded, tarfile.open(
        fileobj=decoded, mode="r|", bufsize=1024 * 1024
    ) as archive:
        for member in archive:
            if member.name == "ORIGINAL_EXPORT_MANIFEST.json":
                require(manifest is None and member.isfile(), f"{path}: duplicate/invalid manifest")
                raw = archive.extractfile(member).read()
                manifest_sha = hashlib.sha256(raw).hexdigest()
                manifest = json.loads(raw)
                require(len(manifest["accepted_modules"]) == manifest["accepted_module_count"],
                        f"{path}: accepted module count mismatch")
                for module, meta in manifest["accepted_modules"].items():
                    candidates = [x for x in meta["artifact_paths"] if x.endswith("/declarations.json")]
                    require(len(candidates) == 1, f"{module}: not one selected owned payload")
                    declaration_path = candidates[0]
                    require(declaration_path not in selected, f"{path}: shared owned payload path")
                    selected[declaration_path] = module
                if cache_dir:
                    target = cache_dir / path.name
                    target.mkdir(parents=True, exist_ok=True)
                    (target / "ORIGINAL_EXPORT_MANIFEST.json").write_bytes(raw)
            elif member.name.startswith("packages/"):
                require(manifest is not None, f"{path}: packages precede manifest")
                pieces = member.name.split("/", 2)
                if len(pieces) != 3 or pieces[2] not in selected:
                    continue
                artifact_path = pieces[2]
                module = selected[artifact_path]
                require(module not in extracted and member.isfile(), f"{module}: duplicate/invalid owned payload")
                raw = archive.extractfile(member).read()
                artifact_sha = hashlib.sha256(raw).hexdigest()
                expected = manifest["files"][artifact_path]
                require(len(raw) == member.size == expected["bytes"] and artifact_sha == expected["sha256"],
                        f"{module}: owned payload hash/size mismatch")
                meta = manifest["accepted_modules"][module]
                payload = json.loads(raw)
                checked = validate_payload(module, meta, payload)
                source = repo.joinpath(*module.split(".")).with_suffix(".lean")
                require(source.is_file(), f"{module}: missing active source")
                require(hashlib.sha256(source.read_bytes()).hexdigest() == meta["source_sha256"],
                        f"{module}: active source mismatch; explicit superseded review required")
                occurrence = {
                    "archive": relative,
                    "source_sha256": meta["source_sha256"],
                    "object_sha256": meta["object_sha256"],
                    "compile_closure_signature": meta["compile_closure_signature"],
                    "receipt_sha256": meta["receipt_sha256"],
                    "driver_sha256": meta["driver_sha256"],
                    "declarations_path": artifact_path,
                    "declarations_sha256": artifact_sha,
                }
                union.add(module, meta, checked, occurrence)
                extracted[module] = len(checked["owned"])
                if cache_dir:
                    (cache_dir / path.name / (module + ".declarations.json")).write_bytes(raw)
                if progress and len(extracted) % 25 == 0:
                    progress({"archive": relative, "selected_modules_read": len(extracted),
                              "elapsed_seconds": round(time.monotonic() - started, 2)})
    require(manifest is not None and len(extracted) == manifest["accepted_module_count"],
            f"{path}: missing selected owned payload")
    count = sum(extracted.values())
    require(count == manifest["owned_declaration_count"] == manifest["unique_owned_declaration_count"],
            f"{path}: owned declaration total mismatch")
    require(not manifest["duplicate_owned_declarations"], f"{path}: internal duplicate owned declarations")
    with path.open("rb") as stream:
        archive_sha = hashlib.file_digest(stream, "sha256").hexdigest()
    record = {
        "archive": relative, "bytes": path.stat().st_size, "sha256": archive_sha,
        "manifest_sha256": manifest_sha, "accepted_modules": len(extracted),
        "owned_declarations": count,
    }
    if progress:
        progress({**record, "stage": "archive_verified", "elapsed_seconds": round(time.monotonic() - started, 2)})
    return record


def write_new_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--archive", action="append", help="Repository-relative archive; repeat in desired provenance order")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-row-count", type=int, default=1792)
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--owners-output", type=Path)
    parser.add_argument("--progress-log", type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    require(not args.output.exists(), f"Refuse to overwrite output: {args.output}")
    if args.owners_output:
        require(not args.owners_output.exists(), f"Refuse to overwrite owner map: {args.owners_output}")
    require(args.expected_row_count >= 0, "Invalid expected row count")

    def progress(value):
        line = json.dumps(value, ensure_ascii=False, sort_keys=True)
        print(line, file=sys.stderr, flush=True)
        if args.progress_log:
            args.progress_log.parent.mkdir(parents=True, exist_ok=True)
            with args.progress_log.open("a") as stream:
                stream.write(line + "\n")

    union = OwnedUnion()
    paths = [repo / name for name in (args.archive or DEFAULT_ARCHIVES)]
    require(len(set(paths)) == len(paths), "Repeated archive argument")
    records = [scan_archive(path, repo, union, args.cache_dir, progress) for path in paths]
    result = union.result(records, args.expected_row_count)
    result["verifier"] = {
        "path": "verification/part2/build_p2_accepted_union.py",
        "sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    if args.owners_output:
        write_new_json(args.owners_output, dict(sorted(union.owners.items())))
    write_new_json(args.output, result)
    print(json.dumps({key: value for key, value in result.items() if key not in
                     {"archives", "modules", "numeric_page_bindings", "deduplicated_modules"}},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (UnionError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        raise SystemExit(1)
