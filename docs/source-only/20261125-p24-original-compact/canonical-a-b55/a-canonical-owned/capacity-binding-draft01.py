# This diagnostic binds space estimates only. The original audit CLI must still
# perform independent replay and create all three complete plaintext artifacts.
capacity_directory = root / ".lake/p24-owned-capacity/b55-A-attempt-001"
capacity_receipt_path = capacity_directory / "capacity-diagnostic.json"
capacity_receipt_sha256 = "47734ae76baf0a59f4f381e491ff4fc2ed62669a2fd81131af24635bb94d20a9"
assert re.fullmatch(r"[0-9a-f]{64}", capacity_receipt_sha256), \
    "Freeze the completed actual capacity receipt before submission"
minimum_free_reserve = 32 * 1024 * 1024
replay_allocation_allowance = 1 * 1024 * 1024
wrapper_allocation_allowance = 4 * 1024 * 1024
capacity_binding = None
capacity_sizes = None


def bound_capacity_file(binding, expected_name):
    path = Path(binding["path"])
    assert path == capacity_directory / expected_name
    assert path.is_file() and not path.is_symlink()
    assert path.resolve().is_relative_to(capacity_directory.resolve())
    assert file_info(path) == binding
    return path


def bind_capacity_and_check_original_audit_space():
    global capacity_binding, capacity_sizes
    assert capacity_receipt_path.is_file() and not capacity_receipt_path.is_symlink()
    assert digest(capacity_receipt_path) == capacity_receipt_sha256
    measured = json.loads(capacity_receipt_path.read_text())
    assert measured["diagnostic_passed"] is True and measured["wrapper_exit_code"] == 0
    assert measured["source_pin"] == pin and measured["target"] == A
    assert measured["target_project_scope"] == 102 and measured["full_source_scope"] == 324
    assert measured["ordered_fingerprint"] == ordered_expected
    assert measured["pinned_file_sha256"] == expected
    assert measured["runtime_sha256"] == runtime_expected
    assert measured["native_binding"] == native_before
    assert measured["postchecks"] and all(value is True for value in measured["postchecks"].values())
    assert not measured["errors"]
    assert measured["registry_before"] == measured["registry_after"]
    assert measured["original_runner_main_called"] is False
    assert measured["independent_replay_performed"] is False
    assert measured["canonical_audit_credit"] is False and measured["full324_credit"] is False
    assert measured["lean_memory_mb"] == 11264 and measured["lean_threads"] == 1
    assert measured["outer_timeout_seconds"] == 3600 and measured["job_memory_mb"] == 13107
    assert measured["command"][:-1] == [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
        "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
    frozen_path = bound_capacity_file(measured["full324_before"], "full324-before-snapshot.json")
    measured_frozen = json.loads(frozen_path.read_text())
    # B or W may have gained a current object after the diagnostic. Only A's
    # exact 102-source/object closure determines its complete owned type output.
    assert {name: measured_frozen["project"][name] for name in a_nodes} == \
        {name: pre_frozen["project"][name] for name in a_nodes}
    for key in ("toolchain", "lean_binary_sha256", "leanchecker_sha256", "template_sha256",
                "driver_sha256", "external_snapshot"):
        assert measured_frozen[key] == pre_frozen[key]
    sizes_path = bound_capacity_file(measured["capacity_sizes"], "capacity-sizes.json")
    capacity_sizes = json.loads(sizes_path.read_text())
    assert capacity_sizes == measured["original_format_sizes"]
    assert capacity_sizes["original_parser_passed_full_owned_rules"] is True
    assert capacity_sizes["complete_inventory_and_fulltypes_preserved"] is True
    assert capacity_sizes["gzip_roundtrip_verified"] is True
    assert capacity_sizes["canonical_audit_credit"] is False
    capture = measured["capture"]
    assert capture["complete_successful_template_stdout"] is True
    assert capture["lean_exit_code"] == 0 and capture["read_to_eof"] is True
    assert capture["stopped_for_reserve"] is False and not capture["errors"]
    compressed = {"path": capture["gzip_path"], "bytes": capture["gzip_bytes"],
                  "sha256": capture["gzip_sha256"]}
    gzip_path = bound_capacity_file(compressed, "audit.stdout.log.gz")
    restored_hash, restored_bytes = hashlib.sha256(), 0
    with gzip.open(gzip_path, "rb") as stream:
        while chunk := stream.read(65536):
            restored_hash.update(chunk)
            restored_bytes += len(chunk)
    assert {"bytes": restored_bytes, "sha256": restored_hash.hexdigest()} == capacity_sizes["audit.log"]
    assert restored_bytes == capture["stdout_bytes"] and restored_hash.hexdigest() == capture["stdout_sha256"]
    raw_names = ("audit.log", "declarations.json", "types.txt")
    for name in raw_names:
        assert isinstance(capacity_sizes[name]["bytes"], int) and capacity_sizes[name]["bytes"] > 0
        assert re.fullmatch(r"[0-9a-f]{64}", capacity_sizes[name]["sha256"])
    assert capacity_sizes["raw_three_files_bytes"] == sum(capacity_sizes[name]["bytes"] for name in raw_names)
    assert capacity_sizes["raw_three_files_bytes"] == 485251971
    disk = os.statvfs(root)
    block = disk.f_frsize
    allocated = lambda count: ((count + block - 1) // block) * block
    original_raw_allocation = sum(allocated(capacity_sizes[name]["bytes"]) for name in raw_names)
    # The before-registry copy already exists; reserve the exact same lossless
    # after-registry payload plus its small index, never another plaintext copy.
    future_registry_bytes = len(gzip.compress(registry.read_bytes(), compresslevel=9, mtime=0))
    future_registry_allocation = allocated(future_registry_bytes) + 65536
    required = (original_raw_allocation + future_registry_allocation + replay_allocation_allowance
                + wrapper_allocation_allowance + minimum_free_reserve)
    capacity_binding = {
        "receipt": file_info(capacity_receipt_path), "sizes": file_info(sizes_path),
        "full324_reference": file_info(frozen_path), "complete_stdout_gzip": file_info(gzip_path),
        "exact_A_102_input_binding_unchanged": True,
        "raw_three_files_bytes": capacity_sizes["raw_three_files_bytes"],
        "raw_three_files_block_allocation": original_raw_allocation,
        "future_registry_allocation": future_registry_allocation,
        "replay_allocation_allowance": replay_allocation_allowance,
        "wrapper_allocation_allowance": wrapper_allocation_allowance,
        "minimum_free_reserve": minimum_free_reserve,
        "required_available_bytes_before_original_CLI": required,
        "actual_available_bytes": disk.f_bavail * block,
        "diagnostic_credit_transferred": False,
        "shape_checker_run_in_separate_bound_wrapper": True,
    }
    write_evidence("capacity-binding-and-space-guard.json", capacity_binding)
    assert capacity_binding["actual_available_bytes"] >= required, \
        "Insufficient space for the original complete three files and preserved reserve"


def verify_original_plaintext_sizes():
    row = captured_modules[A]
    receipt = json.loads(Path(row["captured_latest"]["path"]).read_text())
    assert receipt["accepted"] is True
    measured = {}
    for name in ("audit.log", "declarations.json", "types.txt"):
        candidates = [root / path for path in receipt["artifacts"] if Path(path).name == name]
        assert len(candidates) == 1
        info = file_info(candidates[0])
        assert info["sha256"] == receipt["artifacts"][str(candidates[0].relative_to(root))]
        assert {key: info[key] for key in ("bytes", "sha256")} == \
            {key: capacity_sizes[name][key] for key in ("bytes", "sha256")}
        measured[name] = info
    assert receipt["audit"]["declaration_count"] == capacity_sizes["declaration_count"]
    assert receipt["audit"]["axiom_counts"] == capacity_sizes["axiom_counts"]
    write_evidence("original-plaintext-artifacts-match-capacity.json", {
        "original_plaintext_files": measured,
        "all_original_files_retained": True,
        "capacity_diagnostic_credit_transferred": False,
    })
