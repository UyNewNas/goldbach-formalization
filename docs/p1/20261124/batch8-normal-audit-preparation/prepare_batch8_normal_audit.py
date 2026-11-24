#!/usr/bin/env python3
"""Prepare an e9 audit plan from completed Batch8 original evidence; never compile.

The only subprocess operations are read-only Git object reads. No runner, guard,
Lean, Lake, remote API, source installer, or environment setup is invoked.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
from types import SimpleNamespace


NORMAL_COMMIT = "15fbbdd842d11df0ca4db340cae2eddfa7ed39d7"
PREFIX = "docs/p1/20261124/"
EXECUTION_PLAN_PATH = PREFIX + "batch8-parallel/EXECUTION_PLAN.json"
DRIVER_PATH = PREFIX + "batch8-parallel/run_batch8_parallel.py"
HELPER_PATH = PREFIX + "batch5-parallel/run_batch5_parallel.py"
HELPER_SHA = "1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5"
OPS_PATH = PREFIX + "batch6-parallel/run_batch6_parallel.py"
OPS_SHA = "e1338ef756fba98b126bb089413f2c489ed4de8682a61c11dfb8e61c8e518d11"
RUNNER_PATH = PREFIX + "normal-supplement-audit/run_parallel_acceptance_multibatch.py"
RUNNER_SHA = "e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1"
CLOUD_ROOT = Path("/workspace/p1-complete-proof/20261124-resume/batch8-repairs-probes-next17")
PROJECT = "/workspace/blue-member-build"
DEFAULT_RECEIPT_ROOT = (
    "/workspace/p1-complete-proof/20261124-resume/"
    "batch8-completed-normal-supplement-acceptance"
)
COMPLETE_STATUS = "PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS"


class EvidenceError(ValueError):
    pass


def require(ok, reason, detail=None):
    if not ok:
        raise EvidenceError(json.dumps({"reason": reason, "detail": detail}, ensure_ascii=False))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest_file(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def file_info(path):
    p = Path(path)
    return {"local_path": str(p.resolve()), "bytes": p.stat().st_size, "sha256": digest_file(p)}


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


class GitTree:
    """Read immutable objects, never checkout, update, or write a Git worktree."""
    def __init__(self, repo, commit):
        self.repo = Path(repo)
        require(re.fullmatch(r"[0-9a-f]{40}", commit), "full_git_commit_required", commit)
        self.commit = commit
        self.tree = subprocess.check_output(
            ["git", "rev-parse", commit + "^{tree}"], cwd=self.repo, text=True
        ).strip()
        raw = subprocess.check_output(["git", "ls-tree", "-rz", commit], cwd=self.repo)
        self.blobs = {}
        for item in raw.split(b"\0"):
            if item:
                meta, name = item.split(b"\t", 1)
                mode, kind, blob = meta.decode().split()
                if kind == "blob":
                    self.blobs[name.decode()] = blob
        self.child = subprocess.Popen(
            ["git", "cat-file", "--batch"], cwd=self.repo,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE
        )
        self.cache = {}

    def read(self, path):
        require(path in self.blobs, "missing_git_source", [self.commit, path])
        if path not in self.cache:
            blob = self.blobs[path]
            self.child.stdin.write((blob + "\n").encode())
            self.child.stdin.flush()
            header = self.child.stdout.readline().decode().split()
            require(header[:2] == [blob, "blob"], "bad_git_object_reply", path)
            data = self.child.stdout.read(int(header[2]))
            require(self.child.stdout.read(1) == b"\n", "bad_git_object_separator", path)
            require(len(data) == int(header[2]), "short_git_object", path)
            self.cache[path] = data
        return self.cache[path]

    def metadata(self, path):
        data = self.read(path)
        return {
            "source_commit": self.commit, "repository_path": path,
            "git_blob_sha1": self.blobs[path], "bytes": len(data), "sha256": sha(data)
        }

    def close(self):
        self.child.stdin.close()
        require(self.child.wait() == 0, "git_cat_file_failed")


class ArchiveEvidence:
    def __init__(self, root, index_path, index_sha256):
        self.root = Path(root).resolve()
        self.index_path = Path(index_path).resolve()
        require(digest_file(self.index_path) == index_sha256, "archive_index_sha256_mismatch")
        index = json.loads(self.index_path.read_bytes())
        rows = index.get("files", index)
        if isinstance(rows, list):
            require(len({r["path"] for r in rows}) == len(rows), "duplicate_archive_index_paths")
            self.index = {r["path"]: r for r in rows}
        else:
            require(isinstance(rows, dict), "unrecognized_archive_index")
            self.index = rows
        self.used = {}

    def read(self, path):
        p = Path(path).resolve()
        require(p.is_relative_to(self.root), "evidence_path_outside_archive", str(p))
        relative = p.relative_to(self.root).as_posix()
        require(relative in self.index, "file_not_in_original_archive_index", relative)
        data = p.read_bytes()
        row = self.index[relative]
        require(sha(data) == row["sha256"] and len(data) == row["bytes"],
                "original_archive_member_mismatch", relative)
        self.used[str(p)] = {
            "local_path": str(p), "archive_member": relative,
            "bytes": len(data), "sha256": sha(data)
        }
        return data

    def jread(self, path):
        return json.loads(self.read(path))


def load_read_only_helpers(data, expected_sha, name):
    require(sha(data) == expected_sha, "existing_helper_sha256_mismatch", name)
    namespace = {"__name__": name, "__file__": "<verified Git object: " + name + ">"}
    exec(compile(data, namespace["__file__"], "exec"), namespace)
    return SimpleNamespace(**namespace)


def checked_headers(raw, command, targets, helper, ops):
    """Only genuine complete Built headers qualify; an exit 1 may contain them."""
    require(sha(raw) == command["log_sha256"] and len(raw) == command["log_bytes"],
            "normal_log_bytes_not_bound_to_command")
    require(isinstance(command.get("exit_code"), int) and command.get("finished_utc"),
            "normal_command_not_finished")
    started = datetime.fromisoformat(command["started_utc"])
    finished = datetime.fromisoformat(command["finished_utc"])
    require(finished >= started, "normal_command_time_order")
    text = helper.ANSI.sub("", raw.decode())
    built = helper.BUILT.findall(text)
    failed = ops.FAILED.findall(text)
    require(len(built) == len(set(built)), "duplicate_actual_built_headers")
    require(len(failed) == len(set(failed)), "duplicate_actual_failed_headers")
    require(built == command["actual_built_modules"], "command_built_list_disagrees_with_log")
    require(failed == command["actual_failed_modules"], "command_failed_list_disagrees_with_log")
    require(not set(built) & set(failed), "same_module_built_and_failed")
    require(not set(built + failed) - set(targets), "unexpected_normal_module_scope",
            sorted(set(built + failed) - set(targets)))
    for m in built:
        leaf = m.replace(".", "/") + ".lean"
        require(not re.search(r"^error:\s+" + re.escape(leaf) + r":", text, re.M),
                "built_module_has_leaf_error", m)
    headers = [
        {"line": n, "text": line, "module": match.group(1)}
        for n, line in enumerate(text.splitlines(), 1)
        if (match := helper.BUILT.match(line))
    ]
    return built, failed, headers


def prepare(args):
    evidence = ArchiveEvidence(args.archive_root, args.archive_index, args.archive_index_sha256)
    root = args.evidence_root.resolve()
    require(root.is_relative_to(evidence.root), "batch8_evidence_root_not_under_archive")
    normal = GitTree(args.repo, NORMAL_COMMIT)
    review = normal if args.review_commit == NORMAL_COMMIT else GitTree(args.repo, args.review_commit)
    try:
        config = evidence.jread(root / "RUN_CONFIG.json")
        result = evidence.jread(root / "BATCH8_RESULT.json")
        context = evidence.jread(root / "PROJECT_SOURCE_CONTEXT.json")
        reads = evidence.jread(root / "GIT_SHOW_READS.json")
        installation = evidence.jread(root / "SOURCE_INSTALL.json")
        execution_raw = evidence.read(root / "inputs/EXECUTION_PLAN.json")
        execution = json.loads(execution_raw)
        require(config["commit"] == result["commit"] == installation["commit"] == NORMAL_COMMIT,
                "not_original_batch8_commit")
        require(execution_raw == normal.read(EXECUTION_PLAN_PATH), "execution_plan_not_published_bytes")
        require(config["plan_sha256"] == sha(execution_raw), "run_config_plan_sha256_mismatch")
        require(result.get("all_context_sources_unchanged_during_execution") is True,
                "no_final_complete_context_unchanged_receipt")
        require(result.get("higher_canonical_source_unchanged") is True and
                result.get("higher_full_module_candidate_installed") is False,
                "unexpected_batch8_higher_install")
        require(result.get("original_dirty_git_worktree_unchanged") is True,
                "original_worktree_final_gate_missing")

        helper_raw = evidence.read(root / "inputs/batch5_helpers.py")
        ops_raw = evidence.read(root / "inputs/batch6_operations.py")
        helper = load_read_only_helpers(helper_raw, HELPER_SHA, "batch8_audit_readonly_helper")
        ops = load_read_only_helpers(ops_raw, OPS_SHA, "batch8_audit_readonly_ops")
        require(helper_raw == normal.read(HELPER_PATH) and ops_raw == normal.read(OPS_PATH),
                "helper_not_published_original")
        runner_raw = evidence.read(root / "inputs/run_parallel_acceptance_multibatch.py")
        require(sha(runner_raw) == RUNNER_SHA and runner_raw == normal.read(RUNNER_PATH),
                "exact_e9_runner_mismatch")
        require(review.read(RUNNER_PATH) == runner_raw, "review_commit_changes_exact_runner")
        driver = evidence.read(root / "executed-driver.py")
        require(driver == normal.read(DRIVER_PATH) and sha(driver) == config["driver_sha256"],
                "executed_batch8_driver_mismatch")
        require(result["protected_roots"] == installation["protected_roots"] == helper.FOUR_ROOTS,
                "protected_root_receipts_disagree")
        for m, digest in helper.FOUR_ROOTS.items():
            require(sha(review.read(helper.module_path(m))) == digest,
                    "review_changes_protected_root", m)

        prior_raw = evidence.read(root / "inputs/AUDIT_PLAN.json")
        prior = json.loads(prior_raw)
        require(sha(prior_raw) == execution["audit_plan_sha256"] and
                prior_raw == normal.read(execution["audit_plan_path"]),
                "prior17_plan_not_exact_published_original")
        update_raw = evidence.read(root / "inputs/SOURCE_UPDATE.json")
        update = json.loads(update_raw)
        require(sha(update_raw) == execution["source_update_sha256"] and
                update_raw == normal.read(execution["source_update_path"]),
                "source_update_not_exact_published_original")
        candidates = [m for group in execution["normal_groups"] for m in group["targets"]]
        require(len(candidates) == len(set(candidates)) == execution["normal_module_count"],
                "candidate_normal_universe_disagrees")
        require(set(config["normal_sources"]) == set(candidates), "config_normal_universe_disagrees")
        mutable = {r["module"] for r in update["updates"] if r["cloud_source_mutation_required"]}
        require(mutable == set(candidates), "source_update_normal_universe_disagrees")
        installed = {r["module"]: r for r in installation["sources"]}
        require(set(installed) == {r["module"] for r in update["updates"]},
                "source_install_universe_disagrees")
        read_index = {r["path"]: r for r in reads}
        require(len(read_index) == len(reads), "duplicate_git_show_read_destinations")
        for row in update["updates"]:
            m, rel = row["module"], row["path"]
            raw = evidence.read(root / "inputs/sources" / rel)
            require(raw == normal.read(rel) and sha(raw) == row["after_sha256"],
                    "installed_source_not_exact_published_bytes", m)
            require(installed[m]["actual_after_sha256"] == context[m]["sha256"] == sha(raw),
                    "actual_cloud_source_context_mismatch", m)
            read = read_index[str(CLOUD_ROOT / "inputs/sources" / rel)]
            require(read["argv"] == ["git", "show", NORMAL_COMMIT + ":" + rel] and
                    read["exit_code"] == 0 and read["sha256"] == sha(raw) and
                    read["bytes"] == len(raw), "source_git_show_read_mismatch", m)
            if m in mutable:
                require(config["normal_sources"][m] == sha(raw), "normal_source_config_mismatch", m)
            else:
                require(installed[m]["mutated"] is False, "preserved_source_was_rewritten", m)

        lane_root = root / "execution/lane-1"
        lane = evidence.jread(lane_root / "LANE_RESULT.json")
        stages = {r.get("log"): r for r in lane["stages"] if r.get("log")}
        require(len(stages) == sum(bool(r.get("log")) for r in lane["stages"]),
                "duplicate_lane_stage_logs")
        require(lane.get("audit_failure_does_not_suppress_independent_normal") is True,
                "lane_result_semantics_changed")

        def command(stage, expected_argv):
            cmd_path = lane_root / (stage + "-command.json")
            log_path = lane_root / (stage + ".log")
            cmd = evidence.jread(cmd_path)
            raw = evidence.read(log_path)
            cloud_log = str(CLOUD_ROOT / "execution/lane-1" / (stage + ".log"))
            require(cmd["argv"] == expected_argv and cmd["cwd"] == PROJECT and cmd["log"] == cloud_log,
                    "actual_command_contract_mismatch", stage)
            require(cmd["log_sha256"] == sha(raw) and cmd["log_bytes"] == len(raw),
                    "actual_command_log_binding_mismatch", stage)
            require(cmd.get("finished_utc") and isinstance(cmd.get("exit_code"), int),
                    "unfinished_command", stage)
            require(cloud_log in stages and all(stages[cloud_log].get(k) == v for k, v in cmd.items()),
                    "lane_result_does_not_bind_command", stage)
            return cmd, raw

        guard = ["python3", helper.GUARD, "--state", str(helper.STATES[1])]
        groups, normal_logs, records, selected, selection = {}, {}, {}, [], []
        for group in execution["normal_groups"]:
            name, targets = group["name"], group["targets"]
            deps = sorted({d for m in targets for d in config["graph"][m]})
            ready, _ = command(name + "-directdeps",
                               guard + ["lake", "--no-build", "build"] + ["+" + d + ":olean" for d in deps])
            if ready["exit_code"] != 0:
                require(not (lane_root / (name + "-command.json")).exists() and
                        not (lane_root / (name + ".log")).exists(),
                        "normal_exists_after_failed_readiness", name)
                selection.append({"group": name, "status": "SKIPPED_DIRECT_DEPS_NOT_READY",
                                  "requested": targets, "built": [], "readiness": ready})
                continue
            cmd, raw = command(name, guard + ["lake", "build"] + ["+" + m + ":olean" for m in targets])
            built, failed, headers = checked_headers(raw, cmd, targets, helper, ops)
            scope = evidence.jread(lane_root / (name + "-BUILD_SCOPE.json"))
            require(scope["requested"] == targets and scope["built"] == built and
                    scope["failed"] == failed and scope["unexpected"] == [],
                    "build_scope_receipt_disagrees", name)
            key = "batch8_" + name
            groups[key] = built
            if built:
                normal_logs[key] = {"path": cmd["log"], "sha256": sha(raw),
                                    "source_commit": NORMAL_COMMIT, "expected_built_modules": built,
                                    "expected_failed_modules": failed}
                records[key] = {"original_log": file_info(lane_root / (name + ".log")),
                                "original_command_record": file_info(lane_root / (name + "-command.json")),
                                "actual_command": cmd, "complete_built_headers": headers,
                                "complete_built_modules": built, "complete_failed_modules": failed,
                                "whole_normal_command_exit_code": cmd["exit_code"],
                                "whole_command_exit_zero_required_for_individual_built_credit": False}
                selected.extend(built)
            selection.append({"group": name, "status": "FINISHED_NORMAL",
                              "requested": targets, "built": built, "failed": failed,
                              "without_new_built_or_failed_header": sorted(set(targets) - set(built + failed)),
                              "whole_command_exit_code": cmd["exit_code"]})
        require(len(selected) == len(set(selected)), "same_normal_credited_twice")
        excluded13 = list(prior["excluded_prior13"])
        reused = list(prior["reused_complete_modules"])
        prior_targets = list(prior["modules"])
        require(not set(selected) & set(excluded13 + reused + prior_targets),
                "selected_normal_overlaps_prior_audit_or_accepted_modules")
        prior_result = None
        prior_receipt = args.prior_audit_receipt or (
            evidence.root / Path(prior["receipt_root"]).name / "lane-1/VALIDATION_RESULTS.json"
        )
        require(not args.prior_audit_receipt or prior_receipt.is_file(),
                "explicit_prior_audit_receipt_missing", str(prior_receipt))
        if prior_receipt.exists():
            receipt = evidence.jread(prior_receipt)
            require(receipt["status"] == COMPLETE_STATUS and receipt["plan_sha256"] == sha(prior_raw),
                    "prior17_acceptance_not_bound_to_exact_plan")
            require(receipt["modules"] == {m: v["source_sha256"] for m, v in prior["modules"].items()},
                    "prior17_accepted_module_sources_mismatch")
            require(receipt["project_dependency_sources"] == prior["expected_project_sources"],
                    "prior17_full_dependency_context_mismatch")
            require(receipt["source_plus_five_outputs_unchanged_across_kernel_and_audit"] is True,
                    "prior17_output_gate_missing")
            reused += prior_targets
            prior_result = {"receipt": file_info(prior_receipt), "status": receipt["status"],
                            "module_count": len(receipt["modules"]),
                            "owned_count": receipt["total_owned_exports"],
                            "repeated_by_this_plan": False}

        graph, sources = {}, {}
        def visit(m):
            if m in graph:
                return
            rel = helper.module_path(m)
            raw = normal.read(rel)
            deps = [d for d in helper.imports(raw) if d.startswith("ImbalancedChen.")]
            require(m in context and sha(raw) == context[m]["sha256"] and len(raw) == context[m]["bytes"],
                    "normal_project_ancestor_source_not_bound_to_actual_context", m)
            require(deps == context[m]["imports"] == config["graph"][m],
                    "normal_project_import_graph_disagrees", m)
            require(review.read(rel) == raw, "project_ancestor_changed_since_normal",
                    {"module": m, "normal_sha256": sha(raw), "review_sha256": sha(review.read(rel))})
            graph[m] = deps
            sources[m] = {**review.metadata(rel), "imports": deps,
                          "normal_source_commit": NORMAL_COMMIT,
                          "normal_source_git_blob_sha1": normal.blobs[rel]}
            for d in deps:
                visit(d)
        for m in selected:
            visit(m)
        closures = {m: sorted(helper.closure(graph, [m])) for m in selected}
        require(set(sources) == set().union(*(set(c) for c in closures.values())),
                "audit_source_closure_not_exact")
        concurrent = list(dict.fromkeys(args.concurrent_module))
        for m in concurrent:
            helper.module_path(m)
        overlap = sorted(set(concurrent) & set(sources))
        require(not overlap, "concurrent_write_target_in_audit_dependency_closure", overlap)
        modules = {}
        for key, built in groups.items():
            for m in built:
                s = sources[m]
                modules[m] = {
                    "source_sha256": s["sha256"], "normal_log": key,
                    "normal_source_commit": NORMAL_COMMIT,
                    "normal_source_git_blob_sha1": s["normal_source_git_blob_sha1"],
                    "normal_source_repository_path": s["repository_path"], "source_bytes": s["bytes"],
                    "current_source_commit": review.commit, "current_source_git_blob_sha1": s["git_blob_sha1"],
                    "project_closure": closures[m], "project_closure_count": len(closures[m]),
                    "original_normal_source_context_complete": True,
                    "original_normal_all_project_sources_match_current_expected_context": True,
                    "original_normal_source_context_binding": file_info(root / "PROJECT_SOURCE_CONTEXT.json"),
                    "historical_full_receipt_reused": False,
                    "audit_status": "NORMAL_REUSED_NEW_NAMED_KERNEL_AND_FULL_OWNED_PENDING"
                }
        require(set(modules) == set(selected), "audit_selection_mismatch")
        plan = {
            "schema": "p1_completed_normal_multibatch_audit_plan_v1",
            "status": "PLAN_ONLY_NORMAL_REUSE_KERNEL_FULL_OWNED_PENDING",
            "source_review_head": review.commit, "project": PROJECT, "receipt_root": args.receipt_root,
            "runtime_states": [str(s) for s in helper.STATES], "audit_template": prior["audit_template"],
            "normal_logs": normal_logs, "modules": modules, "groups": groups,
            "lanes": [{"id": 0, "modules": []}, {"id": 1, "modules": selected}],
            "expected_project_sources": {m: s["sha256"] for m, s in sorted(sources.items())},
            "excluded_prior13": excluded13, "reused_complete_modules": reused,
            "excluded_prior_audit_targets_without_new_acceptance_claim":
                [] if prior_result else prior_targets,
            "successful_normal_not_to_be_repeated": True,
            "whole_P1_complete": False, "full_selected_11026_accepted": False,
            "source_context_binding": {
                "kind": "COMPLETE_ORIGINAL_BATCH8_SOURCE_CONTEXT_MATCHES_REVIEW_GIT_TREE",
                "normal_commit": NORMAL_COMMIT, "review_commit": review.commit,
                "review_tree": review.tree, "project_module_count": len(sources),
                "actual_cloud_source_gate_required": True, "current_cloud_readiness_claimed": False
            },
            "runner_binding": {
                "repository_path": RUNNER_PATH, "reviewed_commit": review.commit, "sha256": RUNNER_SHA,
                "unchanged_existing_runner": True,
                "required_invocation": "--prepare-only, then explicit --lane 1 inside existing state1 serializer; runner supplies its own guards.",
                "default_dual_lane_invocation_forbidden": True, "lane0_must_not_be_launched": True
            },
            "execution_constraints": {
                "active_lane": 1, "active_lane_modules": len(selected),
                "normal_compilation_not_to_be_repeated": True,
                "new_kernel_or_owned_acceptance_not_claimed_by_plan": True,
                "source_plus_five_outputs_gate_unchanged": True,
                "named_leanchecker_gate_unchanged": True,
                "all_environment_owned_types_and_axioms_gate_unchanged": True,
                "no_build_before_and_after_unchanged": True,
                "check_all_project_source_hashes_before_kernel": True
            },
            "dependency_review": {
                "project_closure_count": len(sources),
                "concurrent_write_modules": concurrent,
                "concurrent_write_modules_in_audit_closure": [],
                "concurrent_write_set_supplied": bool(concurrent),
                "protected_original_four_roots": helper.FOUR_ROOTS,
                "source_or_artifact_mutations_allowed_by_audit": False
            }
        }
        provenance = {
            "schema": "p1_batch8_actual_normal_supplement_provenance_v1",
            "status": "ORIGINAL_FINISHED_EVIDENCE_VERIFIED_NEW_AUDIT_PENDING",
            "normal_commit": NORMAL_COMMIT, "review_commit": review.commit, "review_tree": review.tree,
            "original_archive_index": file_info(args.archive_index),
            "original_run_config": file_info(root / "RUN_CONFIG.json"),
            "original_final_batch_result": file_info(root / "BATCH8_RESULT.json"),
            "original_source_context": file_info(root / "PROJECT_SOURCE_CONTEXT.json"),
            "original_source_install": file_info(root / "SOURCE_INSTALL.json"),
            "original_git_reads": file_info(root / "GIT_SHOW_READS.json"),
            "actual_group_selection": selection, "normal_groups": records,
            "target_count": len(selected), "project_source_count": len(sources),
            "current_project_import_graph": graph, "current_expected_source_metadata": sources,
            "prior17_actual_acceptance": prior_result,
            "prior_exclusions_basis": {
                "original_prior17_plan": file_info(root / "inputs/AUDIT_PLAN.json"),
                "excluded_prior13": excluded13, "previous_complete_modules": prior["reused_complete_modules"]
            },
            "raw_evidence_files": evidence.used,
            "runner": review.metadata(RUNNER_PATH),
            "all_normal_source_snapshots_exact": True,
            "all_project_ancestors_match_actual_normal_context_and_review_tree": True,
            "normal_success_is_not_kernel_or_full_owned_acceptance": True,
            "no_lean_or_lake_invoked": True, "cloud_tasks_started": 0,
            "main_repo_modified": False, "whole_P1_complete": False
        }
        selection_result = {
            "status": "READY_FOR_PLAN_FREEZE" if selected else "NO_NEW_BUILT_TARGETS_NOTHING_TO_AUDIT",
            "normal_commit": NORMAL_COMMIT, "review_commit": review.commit,
            "candidate_universe": candidates, "groups": selection,
            "actual_built_targets": selected, "actual_built_count": len(selected),
            "project_source_count": len(sources), "proof_acceptance_claimed": False
        }
        return plan, provenance, selection_result, evidence
    finally:
        if review is not normal:
            review.close()
        normal.close()


def write_result(args, plan, provenance, selection, evidence):
    require(not args.out.exists(), "output_directory_already_exists", str(args.out))
    args.out.mkdir(parents=True)
    (args.out / "SELECTION.json").write_bytes(json_bytes(selection))
    bundle = args.out / "NORMAL_EVIDENCE.tar.xz"
    with tarfile.open(bundle, "x:xz", format=tarfile.PAX_FORMAT) as archive:
        archive.add(evidence.index_path, arcname="ORIGINAL_ARCHIVE_FILES.json", recursive=False)
        for p, meta in sorted(evidence.used.items()):
            require(digest_file(p) == meta["sha256"], "evidence_changed_during_preparation", p)
            archive.add(p, arcname=meta["archive_member"], recursive=False)
    if selection["actual_built_targets"]:
        (args.out / "AUDIT_PLAN.json").write_bytes(json_bytes(plan))
        provenance["audit_plan_sha256"] = digest_file(args.out / "AUDIT_PLAN.json")
    provenance["raw_evidence_bundle"] = file_info(bundle)
    (args.out / "PROVENANCE.json").write_bytes(json_bytes(provenance))
    (args.out / "SOURCE_GRAPH.json").write_bytes(json_bytes({
        "source_commit": plan["source_review_head"],
        "graph": provenance["current_project_import_graph"],
        "sources": provenance["current_expected_source_metadata"],
        "closures": {m: row["project_closure"] for m, row in plan["modules"].items()}
    }))
    manifest = {
        "schema": "p1_batch8_actual_normal_audit_package_v1",
        "generator": file_info(Path(__file__)), "status": selection["status"],
        "new_acceptance_claimed": False,
        "files": {p.name: file_info(p) for p in sorted(args.out.iterdir()) if p.is_file()}
    }
    (args.out / "MANIFEST.json").write_bytes(json_bytes(manifest))
    return {"status": selection["status"], "out": str(args.out), "targets": selection["actual_built_count"],
            "project_sources": selection["project_source_count"],
            "audit_plan_sha256": provenance.get("audit_plan_sha256")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--evidence-root", required=True, type=Path,
                        help="Extracted Batch8 directory containing RUN_CONFIG.json and execution/.")
    parser.add_argument("--archive-root", required=True, type=Path,
                        help="Directory against which original ARCHIVE_FILES.json member paths resolve.")
    parser.add_argument("--archive-index", required=True, type=Path)
    parser.add_argument("--archive-index-sha256", required=True,
                        help="The independently bound original archive-index SHA; never inferred by this script.")
    parser.add_argument("--review-commit", required=True,
                        help="Full published source commit for the proposed subsequent audit run.")
    parser.add_argument("--prior-audit-receipt", type=Path,
                        help="Optional explicit exported prior audit17 VALIDATION_RESULTS.json path.")
    parser.add_argument("--out", required=True, type=Path,
                        help="New exclusive output directory; existing paths are never overwritten.")
    parser.add_argument("--receipt-root", default=DEFAULT_RECEIPT_ROOT)
    parser.add_argument("--concurrent-module", action="append", default=[],
                        help="One next-round write target; reject if it occurs in any selected audit closure.")
    parser.add_argument("--check-only", action="store_true",
                        help="Verify all available evidence and print selection without writing any artifact.")
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{64}", args.archive_index_sha256), "full_archive_index_sha_required")
    require(Path(args.receipt_root).is_absolute(), "absolute_cloud_receipt_root_required")
    plan, provenance, selection, evidence = prepare(args)
    if args.check_only:
        print(json.dumps(selection, ensure_ascii=False, indent=2))
    else:
        print(json.dumps(write_result(args, plan, provenance, selection, evidence), ensure_ascii=False, indent=2))
    return 0 if selection["actual_built_targets"] else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (EvidenceError, KeyError, FileNotFoundError) as error:
        print(json.dumps({"status": "EVIDENCE_NOT_READY_OR_MISMATCH_NO_PLAN_FROZEN",
                          "error": str(error)}, ensure_ascii=False), file=sys.stderr)
        raise SystemExit(3)
