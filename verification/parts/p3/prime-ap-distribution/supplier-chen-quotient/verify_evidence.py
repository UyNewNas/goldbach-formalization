#!/usr/bin/env python3
"""Offline consistency checks for the archived supplier evidence."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import re
import tarfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(value: bool, message: str) -> None:
    if not value:
        raise AssertionError(message)


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def main() -> None:
    receipt = json.loads((HERE / "receipt.json").read_text())
    require(receipt["status"] == "PASS", "receipt status")
    production = receipt["production"]
    audit = receipt["audit"]
    evidence = receipt["evidence"]
    require(digest(ROOT / production["source"]) == production["source_sha256"], "production source")
    require(digest(ROOT / audit["source"]) == audit["source_sha256"], "audit source")
    require(digest(HERE / "evidence.tar.xz") == evidence["bundle_sha256"], "evidence archive")

    with tarfile.open(HERE / "evidence.tar.xz", "r:xz") as archive:
        members = {member.name.removeprefix("./"): member for member in archive.getmembers() if member.isfile()}

        def read(name: str) -> bytes:
            require(name in members, f"missing evidence member {name}")
            stream = archive.extractfile(members[name])
            require(stream is not None, f"unreadable evidence member {name}")
            return stream.read()

        declarations_data = read("compiler-declarations.json")
        imports_data = read("import-objects.tsv")
        require(digest_bytes(declarations_data) == evidence["compiler_declarations_sha256"],
                "compiler declaration file")
        require(digest_bytes(imports_data) == evidence["import_objects_sha256"], "import inventory")
        declarations = json.loads(declarations_data)
        imports = imports_data.decode().splitlines()

        objects_archive = read("verified-objects.tar.xz")
        require(digest_bytes(objects_archive) == evidence["verified_objects_archive_sha256"],
                "verified object archive")
        with tarfile.open(fileobj=io.BytesIO(objects_archive), mode="r:xz") as objects:
            object_members = {
                member.name.removeprefix("./"): member for member in objects.getmembers() if member.isfile()
            }
            expected_objects = {
                "ImbalancedChen/ChenQuotientSieveRemainders.olean":
                    evidence["production_object_member_sha256"],
                "verification/parts/p3/ChenQuotientSieveRemaindersAudit.olean":
                    evidence["audit_object_member_sha256"],
            }
            require(set(object_members) == set(expected_objects), "verified object members")
            for name, wanted in expected_objects.items():
                stream = objects.extractfile(object_members[name])
                require(stream is not None, f"unreadable object {name}")
                require(digest_bytes(stream.read()) == wanted, f"verified object hash {name}")

        strict_log = read("raw/strict-compile.log").decode()
        replay_log = read("raw/production-replay.log").decode()
        audit_log = read("raw/audit-compile.log").decode()
        audit_replay = read("raw/audit-replay.log").decode()
        for timing in ("strict-compile.timing", "production-replay.timing",
                       "audit-compile.timing", "audit-replay.timing"):
            require(read("raw/" + timing).decode().strip().endswith("exit=0"), f"successful {timing}")

    require(len(declarations) == audit["owned_declaration_count"] == 34, "declaration count")
    require(len({row["name"] for row in declarations}) == 34, "unique declarations")
    require({row["module"] for row in declarations} == {production["module"]}, "defining module")
    require({axiom for row in declarations for axiom in row["axioms"]} == ALLOWED, "axiom union")
    require(all(row["kind"] != "axiom" for row in declarations), "no axiom declaration")
    require(all("⋯" not in row["type"] and "⋯" not in row["readable_type"] for row in declarations),
            "complete compiler types")
    require(sum(row["kind"] == "theorem" for row in declarations) == 30, "theorem count")
    require(sum(row["kind"] == "definition" for row in declarations) == 4, "definition count")

    require(len(imports) == audit["actual_import_object_count"] == 4237, "import count")
    parsed = [line.split("\t") for line in imports]
    require(all(len(row) == 4 and row[2].isdigit() and re.fullmatch(r"[0-9a-f]{64}", row[3]) for row in parsed),
            "import inventory format")
    require(len({row[0] for row in parsed}) == len(parsed), "unique import modules")

    require("FRONTEND_OK module=ImbalancedChen.ChenQuotientSieveRemainders trustLevel=0" in strict_log,
            "strict frontend marker")
    require(replay_log.strip() == "replaying ImbalancedChen.ChenQuotientSieveRemainders", "production replay")
    require("FRONTEND_OK module=verification.parts.p3.ChenQuotientSieveRemaindersAudit trustLevel=0" in audit_log,
            "audit frontend marker")
    require("PART3_SUPPLIER_MODULE {\"count\":34" in audit_log, "audit count marker")
    require(audit_replay.strip() == "replaying verification.parts.p3.ChenQuotientSieveRemaindersAudit",
            "audit replay")

    print(json.dumps({
        "status": "PASS",
        "production_module": production["module"],
        "owned_declarations": len(declarations),
        "actual_import_objects": len(imports),
        "transitive_axioms": sorted(ALLOWED),
        "prime_ap_distribution_compiled": False,
    }, indent=2))


if __name__ == "__main__":
    main()
