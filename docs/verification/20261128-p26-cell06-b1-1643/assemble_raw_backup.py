"""Preserve explicitly selected original bytes; no subprocesses or proof credit."""
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys
import tarfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def regular_bytes(pin):
    assert set(pin) == {"path", "bytes", "sha256"}
    path = Path(pin["path"])
    assert path.is_absolute() and ".." not in path.parts
    assert path.is_relative_to("/workspace")
    for parent in [*reversed(path.parents), path]:
        assert not parent.is_symlink(), str(parent)
    st = path.stat()
    assert stat.S_ISREG(st.st_mode) and st.st_nlink == 1, str(path)
    data = path.read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], str(path)
    return data


def emit(path, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    return {"path": str(path), "bytes": len(raw), "sha256": digest(raw)}


def main():
    assert len(sys.argv) == 3
    ipath = Path(sys.argv[1])
    raw = ipath.read_bytes()
    assert digest(raw) == sys.argv[2]
    contract = json.loads(raw)
    assert contract["schema"] == "p26_b1_raw_backup_actual1643_input_v1"
    assert regular_bytes(contract["assembler"]) == Path(__file__).read_bytes()
    inventory_raw = regular_bytes(contract["inventory"])
    inventory = json.loads(inventory_raw)
    assert inventory["schema"] == "p26_B1_original_evidence_backup_plan_v1"
    assert inventory["producer_recorded_endpoint_union"] == 1643
    members = inventory["members"]
    assert len(members) == inventory["selected_member_count"]
    assert sum(m["source"]["bytes"] for m in members) == inventory["selected_raw_bytes"]
    qa = json.loads(regular_bytes(contract["actual_review"]))
    assert qa["schema"] == "p26_b1_actual_run_independent_acceptance_review_v1"
    assert qa["status"] == "ACCEPTED_B1_CONTEXT_1643"
    assert qa["counts"] == {"Critical": 0, "Important": 0, "Minor": 0}
    assert qa["B1_formal_acceptance_verified"] and qa["new_context_usable_as_accepted_parent"]
    assert qa["context"] == contract["accepted_context"]
    assert qa["seal"] == contract["accepted_seal"]
    assert not any(qa[k] for k in ["Cell06_integral_complete", "P2_6_complete", "original_full_snapshot_verified"])
    regular_bytes(contract["accepted_context"])
    regular_bytes(contract["accepted_seal"])
    selected = [dict(m) for m in members]
    selected += [
        {"archive_name": "backup-controls/INVENTORY.json", "source": contract["inventory"], "roles": ["frozen_original_inventory"]},
        {"archive_name": "backup-controls/PLAN.md", "source": contract["plan"], "roles": ["frozen_backup_plan"]},
        {"archive_name": "backup-controls/assemble_raw_backup.py", "source": contract["assembler"], "roles": ["one_shot_stdlib_assembler"]},
    ]
    names = set()
    for member in selected:
        name = member["archive_name"]
        pure = PurePosixPath(name)
        assert not pure.is_absolute() and pure.parts and all(p not in (".", "..") for p in pure.parts)
        assert name == pure.as_posix() and "\\" not in name and "\0" not in name
        assert name not in names and name != "MANIFEST.json"
        names.add(name)
    assert any(m["source"] == contract["actual_review"] for m in selected)
    manifest = {
        "schema": "p26_b1_raw_evidence_backup_manifest_v1",
        "input_contract": {"path": str(ipath), "bytes": len(raw), "sha256": digest(raw)},
        "members": sorted(selected, key=lambda m: m["archive_name"]),
        "original_member_count": len(members),
        "new_mathematical_credit": 0,
        "proof_process_calls": 0,
        "G_payload_scans": 0,
        "accepted_endpoint_previously_verified": 1643,
        "inherited_bulk_bodies_reference_only": True,
        "canonical_alias_body_not_duplicated": inventory["canonical_object_expected_alias"],
    }
    out = Path(__file__).parent / "output"
    out.mkdir(exist_ok=False)
    mpin = emit(out / "MANIFEST.json", manifest)
    archive = out / "evidence.tar.xz"
    with tarfile.open(archive, mode="x:xz", format=tarfile.PAX_FORMAT, preset=6) as tar:
        for member in manifest["members"]:
            body = regular_bytes(member["source"])
            info = tarfile.TarInfo(member["archive_name"])
            info.size = len(body)
            info.mode = 0o644
            info.mtime = 0
            tar.addfile(info, io.BytesIO(body))
        body = regular_bytes(mpin)
        info = tarfile.TarInfo("MANIFEST.json")
        info.size = len(body)
        info.mode = 0o644
        info.mtime = 0
        tar.addfile(info, io.BytesIO(body))
    size = archive.stat().st_size
    assert size < 90 * 1024 * 1024, "Measured archive exceeds publication cap; preserve and use planned volumes."
    apin = {"path": str(archive), "bytes": size, "sha256": digest(archive.read_bytes())}
    capsule = {
        "schema": "p26_b1_original_byte_backup_capsule_v1",
        "manifest": mpin,
        "archive": apin,
        "payload_member_count": len(manifest["members"]),
        "archive_regular_member_count": len(manifest["members"]) + 1,
        "payload_raw_bytes": sum(m["source"]["bytes"] for m in manifest["members"]),
        "accepted_context": contract["accepted_context"],
        "accepted_seal": contract["accepted_seal"],
        "actual_acceptance_review": contract["actual_review"],
        "previous_published_commit": contract["previous_published_commit"],
        "operation_formal_acceptance": False,
        "accepted_endpoint_previously_verified": 1643,
        "new_mathematical_credit": 0,
        "proof_process_calls": 0,
        "G_payload_scans": 0,
        "source_minor_M1_deferred": True,
        "Cell06_integral_complete": False,
        "P2_6_complete": False,
        "original_full_snapshot_verified": False,
        "independent_archive_review_pending": True,
    }
    cpin = emit(out / "CAPSULE.json", capsule)
    print(json.dumps({"capsule": cpin, "archive": apin, "manifest": mpin}, sort_keys=True))


if __name__ == "__main__":
    main()
