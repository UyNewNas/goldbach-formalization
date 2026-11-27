#!/usr/bin/env python3
"""Reconcile 275 modules and stage 273 old parents. No Lean or old receipts."""
from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager
import hashlib
import importlib
import json
import lzma
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import uuid
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RESUMED = "docs/verification/20261127-p2-5-resumed/"
TARGET = "ImbalancedChen.P4AOriginalCell0HalfOpenPrimeCarrier"
CHRONOLOGY = "ImbalancedChen.P4AOriginalCell0AffineChronology"
TARGET_SHA = "c629a82f73a6ccd83286745cbbe235def6ed00d752e83e11f5854e1033bab9b0"
SNAPSHOT_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
CREDIT = dict(compile_credit=False, kernel_credit=False, owned_audit_credit=False,
              historical_counts_modified=False, old_records_reconstructed=False,
              original_external_snapshot_verified=False, R19_accepted=False, P2_5_proved=False)
INPUTS = {
    "r18_closure": ("inputs/R18_SOURCE_CLOSURE.json", "331428a5cfb5a8bcdd15e12dc74522d0aa998dd35c83ff275bd88110fd4eed7a"),
    "r18_result": ("inputs/R18_RUN_RESULT.json", "8d8cadde46c9f56af4cc3f269a8c16b8a84abcac976da4f55539a0ab54df31dc"),
    "r18_objects": ("inputs/R18_NEW_NORMAL_OBJECT_INDEX.json", "87c63a19763b86b127c7405f04cb7f6b96b9f3af435ab545641cd07b562654b7"),
    "local_objects": ("inputs/EXACT_PARENT_OBJECTS.json", "201f401dae4400905efd0286acf784671a84c4a72095bdc7c5dfe2302dc5cb9e"),
    "exact54": ("inputs/P1_EXACT54_REQUEST.json", "93f504571d61e257073edaa3750feca2512d6a0dd5e102d950a951ce4d88436b"),
    "r14_inventory": (RESUMED + "p2-round14-context/CELL1_AFFINE_294_NORMAL_INVENTORY.json", "5e2f0856b5f2df8c4e455cb5320075b743255a441b3d19262a63ec7a50ce3a4c"),
    "r16_objects": (RESUMED + "p2-round16/NEW_NORMAL_OBJECT_INDEX.json", "383a873e113023297b9637171403908f246903615af8a472804c5a5022a22582"),
    "r17_objects": (RESUMED + "p2-round17/NEW_NORMAL_OBJECT_INDEX.json", "fde18d78d7ce514d9db72d2e61adf648ae26c59120be88c5a66f52b35c08170a"),
}
HELPERS = {
    "run_winner9_private_checks.py": "f7816db16309f99b6f3babbe128425c06818b3da1dec556dffffe5e8132a6314",
    "run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "inspect_winner9_owner_native.py": "28fbce08aa1adcc379ee592eda3760d2465b27e784cc735497d35b3658c9e464",
    "winner9_external_snapshot.py": "a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
    "winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
}
FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(body):
    return hashlib.sha256(body).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def stamp(info):
    return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def read_regular(path, expected_sha=None, expected_size=None):
    with os.fdopen(os.open(path, FLAGS), "rb") as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode), "Not a regular file: " + str(path))
        if expected_size is not None:
            require(before.st_size == expected_size, "Wrong file size: " + str(path))
        body = stream.read()
        require(stamp(os.fstat(stream.fileno())) == stamp(before), "File changed during read: " + str(path))
    if expected_sha is not None:
        require(sha(body) == expected_sha, "Wrong SHA256: " + str(path))
    return body


@contextmanager
def parent_fd(path):
    """Create/traverse real directories; never follow a destination symlink."""
    require(path.is_absolute() and ".." not in path.parts, "Expected normalized absolute path")
    descriptor = os.open("/", FLAGS | os.O_DIRECTORY)
    try:
        for component in path.parent.parts[1:]:
            try:
                child = os.open(component, FLAGS | os.O_DIRECTORY, dir_fd=descriptor)
            except FileNotFoundError:
                try:
                    os.mkdir(component, 0o755, dir_fd=descriptor)
                except FileExistsError:
                    pass
                child = os.open(component, FLAGS | os.O_DIRECTORY, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        yield descriptor
    finally:
        os.close(descriptor)


def publish_new(path, body):
    """Atomically create one new file, without replacing anything already there."""
    with parent_fd(path) as directory:
        temporary = ".halfopen-" + uuid.uuid4().hex
        descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                             0o644, dir_fd=directory)
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(body)
                stream.flush()
                os.fsync(stream.fileno())
            os.link(temporary, path.name, src_dir_fd=directory, dst_dir_fd=directory,
                    follow_symlinks=False)
            os.fsync(directory)
        finally:
            os.unlink(temporary, dir_fd=directory)


def existing_exact(path, digest, size):
    for parent in reversed(path.parents):
        if parent.exists() or parent.is_symlink():
            require(stat.S_ISDIR(parent.lstat().st_mode), "Non-directory/symlink ancestor: " + str(parent))
    if path.exists() or path.is_symlink():
        read_regular(path, digest, size)
        return True
    return False


def original_helpers(root):
    directory = root / "verification/part2"
    for name, digest in HELPERS.items():
        read_regular(directory / name, digest)
    sys.path.insert(0, str(directory))
    return (importlib.import_module("run_winner9_private_checks"),
            importlib.import_module("run_winner9_private_audit"))


def build_manifest(root=ROOT):
    """Recompute every join; an inventory projection is never records.json."""
    root = root.resolve(strict=True)
    checks, _ = original_helpers(root)
    data, provenance = {}, {}
    for key, (relative, digest) in INPUTS.items():
        path = HERE / relative if relative.startswith("inputs/") else root / relative
        raw = read_regular(path, digest)
        data[key] = json.loads(raw)
        provenance[key] = dict(path=str(path.relative_to(root)), bytes=len(raw), sha256=digest)
    graph = data["r18_closure"]["modules"]
    require(not data["r18_closure"]["cycles"] and not data["r18_closure"]["missing_imports"],
            "R18 source closure was incomplete")
    order, active = [], set()

    def visit(module):
        require(module not in active, "Project import cycle: " + module)
        if module in order:
            return
        active.add(module)
        for dep in graph[module]["imports"]:
            visit(dep)
        active.remove(module)
        order.append(module)

    visit(TARGET)
    require(len(order) == 275 and order[-1] == TARGET and CHRONOLOGY in order,
            "Unexpected HalfOpen source closure")
    parent_names = order[:-1]
    r14 = data["r14_inventory"]
    require(r14["project_count"] == 294, "Unexpected R14 inventory scope")
    result = data["r18_result"]
    external = result["external_after"]
    require(external == result["external_before"] and result["external_after_matches"] is True
            and external["snapshot_sha256"] == SNAPSHOT_SHA, "R18 external binding differs")
    bindings = {m: dict(r14["module_records"][m], provenance="r14_inventory") for m in parent_names}
    overlays = {"r16_objects": "ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7",
                "r17_objects": "ImbalancedChen.P4AOriginalAscendingCell0Literal96",
                "r18_objects": CHRONOLOGY}
    for key, module in overlays.items():
        require(set(data[key]["modules"]) == {module}, "Unexpected overlay scope: " + key)
        bindings[module] = dict(data[key]["modules"][module], provenance=key)
    require(data["r18_objects"]["all_postflights"] is True
            and bindings[CHRONOLOGY]["owned_accepted"] is True, "R18 Chronology was not accepted")
    local = data["local_objects"]
    exact54 = data["exact54"]["modules"]
    standalone = {r["module"]: r for r in local["standalone_original_objects"]}
    modules, counts, schema_counts = {}, Counter(), Counter()
    for module in order:
        source = graph[module]["source"]
        require(source == module.replace(".", "/") + ".lean", "Unexpected source path: " + module)
        wanted_sha = TARGET_SHA if module == TARGET else graph[module]["sha256"]
        physical_source = (root / source).resolve(strict=True)
        require(physical_source.is_relative_to(root), "Project source link escapes repository: " + module)
        raw = read_regular(physical_source, wanted_sha)
        require(checks.imports(physical_source) == graph[module]["imports"], "Project imports changed: " + module)
        item = dict(source=source, source_bytes=len(raw), source_sha256=wanted_sha,
                    source_resolved=str(physical_source.relative_to(root)),
                    direct_project_imports=graph[module]["imports"])
        if module == TARGET:
            item.update(action="fresh_compile_replay_owned", original_source_sha256=graph[module]["sha256"],
                        source_change="Previously reviewed proof-body-only candidate; no theorem statement change")
            modules[module] = item
            continue
        row = bindings[module]
        require(row["source_sha256"] == wanted_sha, "Historical source binding differs: " + module)
        deps = {d: bindings[d]["object_sha256"] for d in graph[module]["imports"]}
        signatures = {d: bindings[d]["closure_signature"] for d in graph[module]["imports"]}
        require(row["deps"] == deps and row["dependency_signatures"] == signatures,
                "Historical direct dependency binding differs: " + module)
        schemas = [s for s in (2, 3) if checks.closure_signature(dict(
            module=module, source_sha256=wanted_sha, object_sha256=row["object_sha256"],
            toolchain=r14["toolchain"], dependency_signatures=signatures, cache_schema=s,
            external_snapshot=external)) == row["closure_signature"]]
        require(len(schemas) == 1 and row.get("cache_schema", schemas[0]) == schemas[0],
                "Historical closure signature differs: " + module)
        schema_counts[schemas[0]] += 1
        if row["provenance"] == "r14_inventory":
            require(row["status"] == "ROUND14_NORMAL_SUCCESS_OBJECT_AND_DEPENDENCIES_VERIFIED",
                    "R14 failed/blocked row is not reusable: " + module)
        historical = {k: row[k] for k in ("source_sha256", "object_sha256", "object_bytes",
                                          "closure_signature", "deps", "dependency_signatures", "provenance")}
        historical["cache_schema"] = schemas[0]
        item["historical_binding"] = historical
        item["object_relative"] = module.replace(".", "/") + ".olean"
        if module == CHRONOLOGY:
            item.update(action="fresh_compile_replay_owned", supplier="fresh_chronology",
                        reason="Original R18 object bytes lost; compile the exact unchanged f7a source and record new evidence")
        elif module in exact54:
            supplier = exact54[module]
            require(all(supplier[k] == row[k] for k in ("source_sha256", "object_sha256", "object_bytes"))
                    and supplier["r14_closure_signature"] == row["closure_signature"]
                    and supplier["r14_dependency_object_sha256"] == deps
                    and supplier["r14_dependency_signatures"] == signatures,
                    "P1 exact54 request differs: " + module)
            item.update(action="restore_existing_bytes", supplier="ci_exact54", packet_member="objects/" + row["object_sha256"])
        else:
            supplier = local["known_current_source_matched_archived_modules"][module]
            require(all(supplier[k] == row[k] for k in ("source_sha256", "object_sha256")),
                    "Local supplier inventory differs: " + module)
            if module in standalone:
                archive = standalone[module]
                require(all(archive[k] == row[k] for k in ("source_sha256", "object_sha256", "object_bytes")),
                        "Standalone archive binding differs: " + module)
                archive_path = RESUMED + f"p2-round{archive['round']}/new-owned/{module}/{module.split('.')[-1]}.olean.xz"
                read_regular(root / archive_path, archive["compressed_sha256"], archive["compressed_bytes"])
                item.update(action="restore_existing_bytes", supplier="standalone_xz", archive=archive_path,
                            archive_sha256=archive["compressed_sha256"], archive_bytes=archive["compressed_bytes"])
            else:
                require(supplier["basis"] == "R14 exact archived231 + original qualified inventory",
                        "Unexpected local archive basis: " + module)
                item.update(action="restore_existing_bytes", supplier="r14_ltar")
        counts[item["supplier"]] += 1
        modules[module] = item
    require(counts == {"r14_ltar": 214, "standalone_xz": 5, "ci_exact54": 54, "fresh_chronology": 1},
            "Supplier partition differs: " + str(counts))
    require(set(exact54) <= set(parent_names) and len(exact54) == 54, "Exact54 request scope differs")
    require(schema_counts == {2: 92, 3: 182}, "Historical schema partition differs")
    archive = local["r14_archive"]
    return dict(schema="p25-halfopen-minimal-input-plan-v1", status="INPUT_PLAN_ONLY_NO_EXECUTION_CREDIT",
                **CREDIT, target=TARGET, source_closure_count=275, strict_parent_count=274,
                existing_parent_object_count=273, new_compilation_targets=[CHRONOLOGY, TARGET],
                historical_reference_counts=dict(normal_success=362, normal_scope=377, owned_success=54, owned_scope=69,
                                                 current_revalidated=False),
                supplier_counts=dict(counts), historical_schema_counts=dict(schema_counts),
                input_files=provenance, original_helper_sha256=HELPERS, toolchain=r14["toolchain"],
                original_external_binding=external, modules=modules, topological_order=order,
                r14_archive={k: archive[k] for k in ("bytes", "sha256", "leantar_sha256", "selected_modules")})


def stage_project_objects(plan, root, out, r14_archive, leantar, packet_dir):
    require(not out.exists() and not out.is_symlink(), "Stage output directory must be new")
    lib = root / ".lake/p2-private/lib"
    rows = {m: r for m, r in plan["modules"].items() if r["action"] == "restore_existing_bytes"}
    require(len(rows) == 273, "Unexpected staging scope")
    present, needed = {}, {}
    for module, row in rows.items():
        old = row["historical_binding"]
        target = lib / row["object_relative"]
        if existing_exact(target, old["object_sha256"], old["object_bytes"]):
            present[module] = dict(status="already_exact", destination=str(target), sha256=old["object_sha256"])
        else:
            needed[module] = row
    # Verify all missing donors before the first project write.
    payloads, origins = {}, {}
    with tempfile.TemporaryDirectory(prefix="halfopen-r14-") as temporary:
        extracted = Path(temporary)
        if any(r["supplier"] == "r14_ltar" for r in needed.values()):
            require(r14_archive is not None and leantar is not None, "R14 archive and leantar required")
            read_regular(r14_archive, plan["r14_archive"]["sha256"], plan["r14_archive"]["bytes"])
            read_regular(leantar, plan["r14_archive"]["leantar_sha256"])
            subprocess.run([str(leantar), "-C", str(extracted), "-x", "--jobs", "1", str(r14_archive)], check=True)
        ci_need = {r["packet_member"]: m for m, r in needed.items() if r["supplier"] == "ci_exact54"}
        if ci_need:
            require(packet_dir is not None, "CI inner-packet directory required for exact54 objects")
            for number in range(1, 7):
                path = packet_dir / f"part-{number:03d}.zip"
                if not path.exists():
                    continue
                with os.fdopen(os.open(path, FLAGS), "rb") as stream, zipfile.ZipFile(stream) as archive:
                    require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), "Nonregular packet")
                    names = archive.namelist()
                    require(len(names) == len(set(names)), "Duplicate packet members")
                    for member in set(names) & set(ci_need):
                        module = ci_need[member]
                        row = needed[module]["historical_binding"]
                        info = archive.getinfo(member)
                        require(not info.flag_bits & 1 and not stat.S_ISLNK(info.external_attr >> 16)
                                and info.file_size == row["object_bytes"], "Invalid object packet member")
                        body = archive.read(member)
                        require(len(body) == row["object_bytes"] and sha(body) == row["object_sha256"],
                                "CI payload bytes differ: " + module)
                        require(module not in payloads, "Duplicate exact54 supplier: " + module)
                        payloads[module] = body
                        origins[module] = dict(kind="ci_inner_packet", archive=str(path), member=member,
                                               whole_packet_rehashed=False, member_sha256_verified=True)
        for module, row in needed.items():
            old = row["historical_binding"]
            if row["supplier"] == "r14_ltar":
                path = extracted / row["object_relative"]
                payloads[module] = read_regular(path, old["object_sha256"], old["object_bytes"])
                origins[module] = dict(kind="r14_ltar", archive=str(r14_archive), member=row["object_relative"],
                                       archive_sha256=plan["r14_archive"]["sha256"])
            elif row["supplier"] == "standalone_xz":
                compressed = read_regular(root / row["archive"], row["archive_sha256"], row["archive_bytes"])
                body = lzma.decompress(compressed)
                require(len(body) == old["object_bytes"] and sha(body) == old["object_sha256"],
                        "Standalone object bytes differ: " + module)
                payloads[module] = body
                origins[module] = dict(kind="standalone_xz", archive=row["archive"], archive_sha256=row["archive_sha256"])
        require(set(payloads) == set(needed), "Missing exact project donors: " + str(sorted(set(needed) - set(payloads))))
        require(build_manifest(root) == plan, "Source/input bindings changed during donor preparation")
        report = dict(schema="p25-halfopen-project-byte-restoration-v1", **CREDIT,
                      project_root=str(root), manifest_sha256=sha(encoded(plan)), modules=present,
                      old_parent_objects=273, chronology_recompiled=False, halfopen_compiled=False)
        publish_new(out / "INPUT_PLAN.json", encoded(plan))
        try:
            for module in plan["topological_order"]:
                if module not in needed:
                    continue
                row, body = needed[module], payloads[module]
                target = lib / row["object_relative"]
                old = row["historical_binding"]
                if existing_exact(target, old["object_sha256"], old["object_bytes"]):
                    status = "already_exact_at_publish"
                else:
                    publish_new(target, body)
                    status = "restored_exact_bytes"
                read_regular(target, old["object_sha256"], old["object_bytes"])
                report["modules"][module] = dict(status=status, destination=str(target), source=origins[module],
                                                   bytes=len(body), sha256=old["object_sha256"])
            require(build_manifest(root) == plan, "Source/input bindings changed during staging")
            for module, row in rows.items():
                old = row["historical_binding"]
                require(existing_exact(lib / row["object_relative"], old["object_sha256"], old["object_bytes"]),
                        "Staged parent disappeared: " + module)
            report.update(status="ALL_273_PARENT_OBJECT_BYTES_EXACT", source_and_dependency_bindings_rechecked=True)
        except Exception as error:
            report.update(status="STAGING_INCOMPLETE", error=str(error))
            raise
        finally:
            publish_new(out / "PROJECT_STAGE_RESULT.json", encoded(report))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--manifest-out", type=Path)
    parser.add_argument("--stage-project-objects", action="store_true")
    parser.add_argument("--out-dir", type=Path)
    parser.add_argument("--r14-archive", type=Path)
    parser.add_argument("--leantar", type=Path)
    parser.add_argument("--ci-packets-dir", type=Path)
    args = parser.parse_args()
    root = args.root.resolve(strict=True)
    plan = build_manifest(root)
    if args.manifest_out:
        target = args.manifest_out.absolute()
        body = encoded(plan)
        if not existing_exact(target, sha(body), len(body)):
            publish_new(target, body)
    if args.stage_project_objects:
        require(args.out_dir is not None, "--out-dir required for project staging")
        report = stage_project_objects(plan, root, args.out_dir.absolute(), args.r14_archive,
                                       args.leantar, args.ci_packets_dir)
        print(json.dumps(dict(status=report["status"], object_count=len(report["modules"]), **CREDIT)))
    else:
        print(json.dumps(dict(status=plan["status"], closure=275, existing_objects=273,
                              fresh_targets=plan["new_compilation_targets"], manifest_sha256=sha(encoded(plan)), **CREDIT)))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile, lzma.LZMAError, subprocess.CalledProcessError) as error:
        print("HALFOPEN_PREPARATION_REFUSED " + str(error), file=sys.stderr)
        sys.exit(2)
