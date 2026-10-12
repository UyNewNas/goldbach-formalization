#!/usr/bin/env python3
"""Offline consumer for the exact d0366ce Part 0 core-verification artifact.

This program only reads Git objects and supplied evidence. It never invokes Lean,
Lake, Elan, a kernel checker, the network, or Actions. Missing evidence is PENDING.
The five inherited Buchstab records retain their complete default Meta.ppExpr
format; only actual Round3/4 compiler records acquire the PP_ALL_COMPLETE label.
"""

from __future__ import annotations

import argparse
from collections import Counter
import copy
import csv
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import zipfile


EXPECTED_SHA = "d0366ce64272e81faf6166a8a90050f56b328d38"
EXPECTED_TREE = "e2ab22b96f76c8969386296558c626c62a581700"
PREVIOUS_SHA = "28fd630ef7cc38eba86beb6c0ba123336b5d05f2"
EXPECTED_RUN = 38289734671
EXPECTED_JOB = 114946653833
EXPECTED_ATTEMPT = 1
EXPECTED_REPOSITORY = "UyNewNas/goldbach-formalization"
EXPECTED_BRANCH = "chatgpt/chen-p0-integration"
TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
LEAN_COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
LEAN_ACTION_COMMIT = "f061402b660e0c34644504b324e830f2991d4865"
AXIOM_AUDIT_COMMIT = "46024e005996495c65ef609368e11ab39c4222e3"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FINAL_BRIDGE = "ImbalancedChen.current_theorem_1_1_of_manuscript_bounds"
FINAL_MODULE = "ImbalancedChen.CurrentMainTheorem"
LEDGER_BASE = "verification/parts/p0/round4/ledger"
FROZEN = {
    "lean-toolchain": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254",
    "lake-manifest.json": "35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849",
}
ROUND_MODULES = {
    3: {
        "ImbalancedChen.ActualSelectedPrefixLowerCellSum": 9,
        "ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral": 8,
        "ImbalancedChen.HistoricalPrefixCertificate": 96,
        "ImbalancedChen.OrdinaryLowerFourFrontier": 27,
        "ImbalancedChen.Certificates.PairedV2Geometry": 10,
        "ImbalancedChen.Certificates.PairedV2Prefix4Data": 11,
        "ImbalancedChen.Certificates.PairedV2Prefix4": 35,
        "ImbalancedChen.Part3LongSlotNormalization": 2,
    },
    4: {
        "ImbalancedChen.StoredHistoricalBoxPermit": 14,
        "ImbalancedChen.Certificates.PairedV2Batch4To64Data": 72,
        "ImbalancedChen.Certificates.PairedV2Batch4To64": 207,
        "ImbalancedChen.Certificates.PairedV2Prefix64": 121,
    },
}
STAGE_NAMES = {
    "build": "Build the full project",
    "round4-targets": "Check the four explicit round 4 production targets",
    "leanchecker": "Recheck ImbalancedChen with bundled Lean 4.33.0-rc1 leanchecker",
    "axiom-audit": "Audit ImbalancedChen root declarations and transitive axioms",
    "round3-types": "Export complete round 3 types and the existing conditional main bridge",
    "round4-types": "Export complete round 4 types and the existing conditional main bridge",
}
SHA256_RE = re.compile(r"[0-9a-f]{64}")
DIAGNOSTIC_RE = re.compile(r"(?:^.+:\d+:\d+: error(?:\([^)]+\))?:|^error(?:\([^)]+\))?:)")


class EvidenceFailure(RuntimeError):
    pass


class EvidencePending(RuntimeError):
    pass


class KnownCIFailure(RuntimeError):
    """A bound supplied run/job/required-step metadata record is non-successful."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def parse_time(value: str) -> datetime:
    result = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if result.tzinfo is None:
        raise EvidenceFailure("An evidence timestamp has no timezone: " + value)
    return result


def first_diagnostic(value: str) -> dict | None:
    lines = value.splitlines()
    for index, line in enumerate(lines):
        if DIAGNOSTIC_RE.search(line):
            end = next((i for i in range(index + 1, len(lines))
                        if DIAGNOSTIC_RE.search(lines[i])), len(lines))
            return {"line": index + 1, "text": "\n".join(lines[index:end])}
    return None


def lean_code(value: str) -> str:
    """Local reviewed copy of the fixed comment/string masking rule; no eval."""
    out = []
    pos = depth = 0
    while pos < len(value):
        if value.startswith("/-", pos):
            depth += 1
            pos += 2
        elif depth and value.startswith("-/", pos):
            depth -= 1
            pos += 2
            out.append(" ")
        elif depth:
            out.append("\n" if value[pos] == "\n" else " ")
            pos += 1
        elif value.startswith("--", pos):
            end = value.find("\n", pos)
            pos = len(value) if end == -1 else end
        elif value[pos] == '"':
            pos += 1
            while pos < len(value):
                if value[pos] == "\\":
                    pos += 2
                elif value[pos] == '"':
                    pos += 1
                    break
                else:
                    pos += 1
            out.append(" ")
        else:
            out.append(value[pos])
            pos += 1
    if depth:
        raise EvidenceFailure("Unterminated comment in a fixed Lean source")
    return "".join(out)


class Consumer:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.output = args.output.resolve()
        self.checks: list[dict] = []
        self.diagnostics: list[dict] = []
        self.git_cache: dict[tuple[str, str], bytes] = {}
        self.archive: zipfile.ZipFile | None = None
        self.members: list[str] = []
        self.stage_logs: dict[str, str] = {}
        self.stage_receipts: dict[str, dict] = {}
        self.export_receipts: dict[int, dict] = {}
        self.pending_metadata_reasons: list[str] = []
        self.report = {
            "schema": "chen-p0-round4-exact-core-consumer-v1",
            "status": "PENDING",
            "started_utc": utc_now(),
            "expected_source_commit": EXPECTED_SHA,
            "expected_tree": EXPECTED_TREE,
            "expected_run_id": EXPECTED_RUN,
            "expected_job_id": EXPECTED_JOB,
            "expected_attempt": EXPECTED_ATTEMPT,
            "verification_mode": "OFFLINE_CONSUMPTION_OF_SUPPLIED_ORIGINAL_CI_ARTIFACT",
            "consumer_executes_lean_or_ci": False,
            "ci_metadata_status": "NOT_OBSERVED",
            "known_ci_failures": [],
            "evidence_status": "NOT_CONSUMED",
            "pending_evidence_reasons": [],
            "expected_on_actual_success": {
                "required_stages": list(STAGE_NAMES),
                "accepted_modules": 23,
                "pending_components": 14,
                "inherited_types": 393,
                "actual_round3_types": 198,
                "actual_round4_types": 414,
                "complete_merged_types": 1005,
                "pp_all_complete": 1000,
                "default_meta_ppexpr_complete": 5,
            },
            "observed": {},
            "main_theorem_is_conditional": True,
            "hLower_hUpper_discharged": False,
            "K_c_analytic_suppliers_closed_by_this_consumer": False,
            "unclosed_inputs": [
                "Actual full-history construction and uncompiled fixed fifth-layer candidates",
                "Full same-mask-v2 E0/E1 numerical certificate and error ledger beyond the accepted slice",
                "Actual arithmetic distribution interfaces still listed open by their owners",
                "K density proof for the same actual rho (Part 4-A)",
                "Actual hUpper supplier (Part 4-B)",
                "Full Chen mean, analytic c and actual hLower supplier (Part 5; depends on Part 4-A)",
            ],
            "limitations": [
                "This consumer is not a local Lean compilation or kernel replay.",
                "Production object hashes are captured before/after by the actual CI type exporters; the archive need not contain every production object.",
                "The bundled root checker prints replay markers, not per-marker object digests. The production object bindings here were captured by the subsequent Round3/4 exporters; this consumer does not invent hashes at the earlier replay timestamp.",
                "The inherited 393 type strings retain prior compiler provenance. The current root replay validates their unchanged source closure, not a fresh type print for those 393.",
                "The eight upstream S1LowerRosser declarations are excluded from the 23 modules and 1005 types.",
            ],
        }

    def require(self, condition: bool, label: str, detail: object = None) -> None:
        item = {"check": label, "pass": bool(condition)}
        if detail is not None:
            item["detail"] = detail
        self.checks.append(item)
        if not condition:
            raise EvidenceFailure(label)

    def fixed(self, relative: str, commit: str = EXPECTED_SHA) -> bytes:
        key = (commit, relative)
        if key not in self.git_cache:
            result = subprocess.run(
                ["git", "show", commit + ":" + relative], cwd=self.args.repo,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            )
            if result.returncode != 0:
                raise EvidencePending("Fixed Git object unavailable: " + commit + ":" + relative)
            self.git_cache[key] = result.stdout
        return self.git_cache[key]

    def fixed_json(self, relative: str) -> object:
        return json.loads(self.fixed(relative))

    def member(self, relative: str) -> bytes:
        self.require(relative in self.members, "Archive contains required member " + relative)
        assert self.archive is not None
        return self.archive.read(relative)

    def unique_suffix(self, suffix: str) -> str:
        matches = [name for name in self.members if name == suffix or name.endswith("/" + suffix)]
        self.require(len(matches) == 1, "Unique archive suffix " + suffix, matches)
        return matches[0]

    def save_member(self, member: str, relative: str) -> None:
        path = self.output / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(self.member(member))

    def prepare(self) -> None:
        self.require(not self.output.exists() or not any(self.output.iterdir()),
                     "Output directory is new or empty; no stale successful payload can survive")
        repo = self.args.repo.resolve()
        self.require(self.output != repo and repo not in self.output.parents,
                     "Consumer output is outside the integration repository")
        self.output.mkdir(parents=True, exist_ok=True)
        paths = {
            "repo": self.args.repo,
            "artifact_zip": self.args.artifact_zip,
            "run_json": self.args.run_json,
            "jobs_json": self.args.jobs_json,
            "artifacts_json": self.args.artifacts_json,
        }
        missing = [key for key, path in paths.items()
                   if path is None or not path.exists() or (key != "repo" and not path.is_file())]
        self.report["supplied_input_paths"] = {key: str(path) if path else None for key, path in paths.items()}
        self.report["missing_inputs"] = missing
        for key in missing:
            self.note_missing_evidence("Required input is not supplied: " + key)
        # Do not fail on a missing archive or local Git object before reading
        # available run/job/step metadata: a known CI failure must survive.

    def check_fixed_commit(self) -> None:
        if not self.args.repo.is_dir():
            raise EvidencePending("The local fixed-source Git repository is not supplied")
        revision = subprocess.run(["git", "rev-parse", EXPECTED_SHA + "^{tree}"], cwd=self.args.repo,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
        if revision.returncode:
            raise EvidencePending("The published fixed Git commit is not readable locally")
        self.require(revision.stdout.strip() == EXPECTED_TREE, "Published commit has the exact expected tree")

    def note_missing_evidence(self, reason: str) -> None:
        self.report["evidence_status"] = "INCOMPLETE"
        if reason not in self.report["pending_evidence_reasons"]:
            self.report["pending_evidence_reasons"].append(reason)

    def read_supplied_metadata(self, key: str, path: Path | None) -> object | None:
        if path is None or not path.is_file():
            self.note_missing_evidence("Missing supplied metadata: " + key)
            return None
        raw = path.read_bytes()
        target = self.output / "original-metadata" / (key + ".json")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        self.report.setdefault("metadata_files", {})[key] = {
            "input_path": str(path), "retained_path": str(target.relative_to(self.output)),
            "bytes": len(raw), "sha256": sha256(raw),
        }
        return json.loads(raw)

    def observe_ci_entity(self, scope: str, identity: object, record: dict) -> None:
        """Called only after binding the supplied entity to the fixed run/job."""
        status, conclusion = record.get("status"), record.get("conclusion")
        if status == "completed" and isinstance(conclusion, str) and bool(conclusion) and conclusion != "success":
            self.report["known_ci_failures"].append({
                "scope": scope, "identity": identity, "status": status, "conclusion": conclusion,
                "evidence_kind": "SUPPLIED_BOUND_CI_METADATA_NOT_A_LEAN_DIAGNOSTIC",
            })
            self.report["ci_metadata_status"] = "KNOWN_FAILURE_FROM_SUPPLIED_METADATA"
        elif status != "completed" or conclusion != "success":
            reason = f"Supplied {scope} metadata is not completed with a conclusion: {identity}"
            self.pending_metadata_reasons.append(reason)
            self.note_missing_evidence(reason)
            if not self.report["known_ci_failures"]:
                self.report["ci_metadata_status"] = "NONFINAL_OR_INCOMPLETE_METADATA"

    def read_metadata(self) -> None:
        run = self.read_supplied_metadata("run", self.args.run_json)
        if run is None:
            self.pending_metadata_reasons.append("The raw run metadata is missing")
        else:
            self.require(isinstance(run, dict), "Run metadata is a raw GitHub run object")
            self.require(run.get("id") == EXPECTED_RUN and run.get("head_sha") == EXPECTED_SHA,
                         "Run metadata binds the expected run and exact source SHA")
            self.require(run.get("run_attempt") == EXPECTED_ATTEMPT, "Run attempt is fixed to 1")
            self.require(run.get("repository", {}).get("full_name") == EXPECTED_REPOSITORY,
                         "Run repository identity is exact")
            self.require(run.get("head_branch") == EXPECTED_BRANCH and run.get("path") == ".github/workflows/lean.yml",
                         "Run uses the published integration branch and core workflow")
            self.report["observed"].update(
                run_id=run["id"], source_commit=run["head_sha"], run_url=run.get("html_url"),
                run_status=run.get("status"), run_conclusion=run.get("conclusion"),
            )
            self.observe_ci_entity("run", run["id"], run)

        jobs_value = self.read_supplied_metadata("jobs", self.args.jobs_json)
        job = None
        if jobs_value is None:
            self.pending_metadata_reasons.append("The raw job metadata is missing")
        else:
            jobs = jobs_value.get("jobs", []) if isinstance(jobs_value, dict) else jobs_value
            if isinstance(jobs_value, dict) and jobs_value.get("id") == EXPECTED_JOB:
                jobs = [jobs_value]
            self.require(isinstance(jobs, list), "Job metadata contains raw job records")
            selected = [j for j in jobs if isinstance(j, dict) and j.get("id") == EXPECTED_JOB]
            self.require(len(selected) <= 1, "At most one expected actual core job is present")
            if not selected:
                reason = "The expected core job is not listed in the supplied job metadata"
                self.pending_metadata_reasons.append(reason)
                self.note_missing_evidence(reason)
            else:
                job = selected[0]
                self.require(job.get("run_id") == EXPECTED_RUN, "Core job belongs to the expected run")
                for key, expected in [("head_sha", EXPECTED_SHA), ("run_attempt", EXPECTED_ATTEMPT)]:
                    if key in job:
                        self.require(job[key] == expected, "Actual job metadata matches " + key)
                self.report["observed"].update(
                    job_id=job["id"], job_url=job.get("html_url"),
                    job_status=job.get("status"), job_conclusion=job.get("conclusion"),
                )
                self.observe_ci_entity("job", job["id"], job)
                self.job = job
        steps = job.get("steps", []) if job is not None else []
        self.require(isinstance(steps, list), "Available job execution steps form a list")
        self.report["observed"]["required_job_steps"] = []
        for stage, name in STAGE_NAMES.items():
            matches = [step for step in steps if isinstance(step, dict) and step.get("name") == name]
            self.require(len(matches) <= 1, "At most one actual step exists for " + stage)
            if not matches:
                reason = "The actual required step is not present in supplied metadata: " + stage
                self.pending_metadata_reasons.append(reason)
                self.note_missing_evidence(reason)
                continue
            step = matches[0]
            self.report["observed"]["required_job_steps"].append({"stage": stage, **step})
            self.observe_ci_entity("required_step", stage, step)
            if not step.get("started_at") or not step.get("completed_at"):
                reason = "The required step lacks complete execution timestamps: " + stage
                self.pending_metadata_reasons.append(reason)
                self.note_missing_evidence(reason)
        self.report["observed"]["optional_cache_steps"] = [
            step for step in steps if isinstance(step, dict)
            and ("optional Lake cache" in step.get("name", "") or step.get("name") == "Save the existing Lake cache")
        ]
        if self.report["known_ci_failures"]:
            self.report["ci_metadata_status"] = "KNOWN_FAILURE_FROM_SUPPLIED_METADATA"
        elif self.pending_metadata_reasons:
            self.report["ci_metadata_status"] = "NONFINAL_OR_INCOMPLETE_METADATA"
        else:
            self.report["ci_metadata_status"] = "COMPLETED_SUCCESS_METADATA_ONLY"

        # Artifact availability is a separate axis. It must never erase the
        # source-bound run/job/step observations already retained above.
        artifact_value = self.read_supplied_metadata("artifacts", self.args.artifacts_json)
        if artifact_value is None:
            raise EvidencePending("The raw artifact metadata is missing")
        artifacts = artifact_value.get("artifacts", []) if isinstance(artifact_value, dict) else artifact_value
        if isinstance(artifact_value, dict) and "workflow_run" in artifact_value:
            artifacts = [artifact_value]
        self.require(isinstance(artifacts, list), "Artifact metadata contains raw artifact records")
        artifact_name = f"lean-verification-{EXPECTED_RUN}-{EXPECTED_ATTEMPT}"
        selected = [a for a in artifacts if a.get("name") == artifact_name]
        if not selected:
            raise EvidencePending("The expected core artifact is not listed in the supplied metadata")
        self.require(len(selected) == 1, "The expected core artifact identity is unique")
        artifact = selected[0]
        binding = artifact.get("workflow_run", {})
        self.require(binding.get("id") == EXPECTED_RUN and binding.get("head_sha") == EXPECTED_SHA,
                     "Artifact metadata binds the exact run and source SHA")
        self.report["observed"]["artifact_metadata"] = {
            "id": artifact.get("id"), "name": artifact.get("name"),
            "digest": artifact.get("digest"), "size_in_bytes": artifact.get("size_in_bytes"),
            "workflow_run": binding,
        }
        digest = artifact.get("digest")
        if not isinstance(digest, str) or not digest.startswith("sha256:"):
            raise EvidencePending("GitHub artifact SHA-256 metadata is missing")
        if self.args.artifact_zip is None or not self.args.artifact_zip.is_file():
            raise EvidencePending("The actual core artifact ZIP has not been supplied")
        archive_bytes = self.args.artifact_zip.read_bytes()
        archive_digest = sha256(archive_bytes)
        self.require(digest == "sha256:" + archive_digest, "Downloaded archive matches GitHub's artifact digest")
        self.require(artifact.get("size_in_bytes") == len(archive_bytes), "Downloaded archive byte count matches artifact metadata")
        self.report["observed"].update(
            artifact_id=artifact.get("id"), artifact_name=artifact_name,
            artifact_sha256=archive_digest, artifact_bytes=len(archive_bytes),
        )
        self.archive = zipfile.ZipFile(io.BytesIO(archive_bytes))
        names = [info.filename for info in self.archive.infolist() if not info.is_dir()]
        self.require(len(names) == len(set(names)), "Archive contains no duplicate file member names")
        self.require(all(not PurePosixPath(name).is_absolute() and ".." not in PurePosixPath(name).parts
                         and "\\" not in name for name in names), "Archive member paths are unambiguous")
        self.require(self.archive.testzip() is None, "All archive member CRCs validate")
        self.members = names
        self.report["observed"]["artifact_file_members"] = len(names)
        (self.output / "original-metadata" / "core-artifact.zip").write_bytes(archive_bytes)
        write_json(self.output / "ARTIFACT_MEMBERS.json", [
            {"member": name, "bytes": len(self.archive.read(name)), "sha256": sha256(self.archive.read(name))}
            for name in names
        ])

        # Retain available real diagnostics even if this completed run failed a
        # required gate. A consumer metadata failure is not a Lean diagnostic.
        for stage in STAGE_NAMES:
            matches = [name for name in self.members if name.endswith("/lean-verification-logs/" + stage + ".log")
                       or name == "lean-verification-logs/" + stage + ".log"]
            if len(matches) == 1:
                member = matches[0]
                raw = self.member(member).decode("utf-8", errors="replace")
                self.save_member(member, "actual-logs/" + stage + ".log")
                diagnostic = first_diagnostic(raw)
                if diagnostic:
                    self.diagnostics.append({"stream": "combined actual stage log", "stage": stage,
                                             "artifact_member": member, **diagnostic})
        for number in [3, 4]:
            for member in self.members:
                if f"/.lake/part0-round{number}-types/" not in "/" + member or not member.endswith("/receipt.json"):
                    continue
                receipt = json.loads(self.member(member))
                if receipt.get("source_commit") != EXPECTED_SHA:
                    continue
                parent = str(PurePosixPath(member).parent)
                for stream in ["stdout", "stderr"]:
                    stream_member = parent + "/" + stream + ".log"
                    if stream_member not in self.members:
                        continue
                    raw = self.member(stream_member)
                    diagnostic = first_diagnostic(raw.decode("utf-8", errors="replace"))
                    if diagnostic:
                        self.diagnostics.append({"stream": stream, "stage": f"round{number}-types",
                                                 "artifact_member": stream_member, **diagnostic})
                        self.save_member(stream_member, f"diagnostic-evidence/round{number}-" + PurePosixPath(parent).name + "-" + stream + ".log")
        self.report["evidence_status"] = "ARCHIVE_IDENTITY_VALIDATED_AVAILABLE_LOGS_RETAINED"
        if self.report["known_ci_failures"]:
            raise KnownCIFailure("A bound supplied run/job/required-step metadata record is completed without success")
        if self.pending_metadata_reasons:
            for reason in self.pending_metadata_reasons:
                self.note_missing_evidence(reason)
            raise EvidencePending("Required run/job/step metadata is incomplete or not final")
        self.require(run is not None and job is not None and len(self.report["observed"]["required_job_steps"]) == 6,
                     "All complete successful run/job and six required-step metadata records are present")
        self.require(run.get("status") == "completed" and run.get("conclusion") == "success"
                     and job.get("status") == "completed" and job.get("conclusion") == "success",
                     "Actual complete run and job metadata both record success")
        for step in self.report["observed"]["required_job_steps"]:
            self.require(step.get("status") == "completed" and step.get("conclusion") == "success"
                         and bool(step.get("started_at")) and bool(step.get("completed_at")),
                         "Actual required-step metadata records executed success for " + step["stage"])

    def read_logs(self) -> None:
        provenance_member = self.unique_suffix("lean-verification-logs/provenance.log")
        provenance = self.member(provenance_member).decode("utf-8")
        for literal in ["project_commit=" + EXPECTED_SHA,
                        "lean_action_commit=" + LEAN_ACTION_COMMIT,
                        "toolchain=" + TOOLCHAIN,
                        f"run={EXPECTED_RUN} attempt={EXPECTED_ATTEMPT}"]:
            self.require(literal in provenance.splitlines(), "Actual provenance contains " + literal)
        self.save_member(provenance_member, "actual-logs/provenance.log")
        outcomes_member = self.unique_suffix("lean-verification-logs/outcomes.log")
        outcome_lines = self.member(outcomes_member).decode("utf-8").splitlines()
        outcomes = dict(line.split("=", 1) for line in outcome_lines if "=" in line)
        self.require(len(outcome_lines) == len(outcomes) == 6 and set(outcomes) == set(STAGE_NAMES),
                     "Required outcomes log lists all six gates exactly once")
        self.report["observed"]["outcomes"] = outcomes
        self.save_member(outcomes_member, "actual-logs/outcomes.log")

        # Preserve real stage diagnostics before requiring successful gate exits.
        for stage in STAGE_NAMES:
            member = self.unique_suffix("lean-verification-logs/" + stage + ".log")
            raw = self.member(member).decode("utf-8", errors="replace")
            self.stage_logs[stage] = raw
            self.save_member(member, "actual-logs/" + stage + ".log")
            diagnostic = first_diagnostic(raw)
            if diagnostic and not any(item.get("artifact_member") == member for item in self.diagnostics):
                self.diagnostics.append({"stream": "combined actual stage log", "stage": stage,
                                         "artifact_member": member, **diagnostic})

        job_start = parse_time(self.job["started_at"])
        job_end = parse_time(self.job["completed_at"])
        previous_end = None
        for stage in STAGE_NAMES:
            self.require(outcomes[stage] == "success", "Required outcome is success for " + stage)
            member = self.unique_suffix("lean-verification-logs/" + stage + ".timing.tsv")
            rows = list(csv.DictReader(io.StringIO(self.member(member).decode("utf-8")), delimiter="\t"))
            self.require(len(rows) == 1 and rows[0].get("stage") == stage, "One timing row matches " + stage)
            row = rows[0]
            elapsed, exit_code = int(row["elapsed_seconds"]), int(row["exit_code"])
            started, finished = parse_time(row["started_utc"]), parse_time(row["finished_utc"])
            self.require(exit_code == 0 and elapsed >= 0 and finished >= started,
                         "Timing row records a successful actual gate for " + stage)
            self.require(abs((finished - started).total_seconds() - elapsed) <= 1,
                         "Timing duration agrees with its timestamps for " + stage)
            self.require((started - job_start).total_seconds() >= -1 and (job_end - finished).total_seconds() >= -1,
                         "Gate timestamps lie within the actual job for " + stage)
            if previous_end is not None:
                self.require((started - previous_end).total_seconds() >= -1, "Sequential required gates do not overlap at " + stage)
            previous_end = finished
            raw_lines = self.stage_logs[stage].splitlines()
            self.require(f"stage={stage} started={row['started_utc']}" in raw_lines,
                         "Stage log preserves matching start marker for " + stage)
            final_line = (f"stage={stage} finished={row['finished_utc']} "
                          f"elapsed_seconds={elapsed} exit_code={exit_code}")
            self.require(final_line in raw_lines, "Stage log preserves matching successful exit marker for " + stage)
            diagnostic = first_diagnostic(self.stage_logs[stage])
            self.require(diagnostic is None, "Successful stage has no real Lean error diagnostic for " + stage, diagnostic)
            self.stage_receipts[stage] = {
                **row, "elapsed_seconds": elapsed, "exit_code": exit_code,
                "outcome": outcomes[stage], "log_sha256": sha256(self.stage_logs[stage].encode("utf-8")),
                "timing_archive_member": member,
            }
            self.save_member(member, "actual-logs/" + stage + ".timing.tsv")
        self.report["observed"]["stages"] = list(self.stage_receipts.values())

    def check_root_and_fixed_inputs(self) -> tuple[dict, list[dict]]:
        ledger = self.fixed_json(LEDGER_BASE + "/MODULE_LEDGER_CANDIDATE.json")
        inherited = self.fixed_json(LEDGER_BASE + "/INHERITED_TYPES_591.json")
        accepted = [row for row in ledger["modules"] if row["component_evidence_accepted"]]
        self.require(len(ledger["modules"]) == 37 and len(accepted) == 23, "Published ledger has 37 fixed components and 23 accepted components")
        self.require(len(inherited) == 591, "Published inherited type ledger has 591 complete records")
        self.require(sum(row["declarations"]["owned_audited"] for row in accepted) == 1005,
                     "Accepted module declaration counts sum to 1005")
        workflow = self.fixed(".github/workflows/lean.yml").decode("utf-8")
        root_code = lean_code(self.fixed("ImbalancedChen.lean").decode("utf-8"))
        root_imports = {name for line in root_code.splitlines() if line.strip().startswith("import ")
                        for name in line.strip().split()[1:]}
        for row in accepted:
            module = row["module"]
            source_digest = sha256(self.fixed(row["repository_path"]))
            self.require(source_digest == row["source"]["sha256"], "Accepted source matches published producer-bound bytes for " + module)
            self.require(module in root_imports, "Accepted production module is explicitly imported by the root: " + module)
        for relative, digest in FROZEN.items():
            self.require(sha256(self.fixed(relative)) == digest, "Frozen toolchain/dependency file remains exact: " + relative)
        self.require(self.fixed("lean-toolchain").decode().strip() == TOOLCHAIN, "Toolchain pin is unchanged")
        for relative in ["ImbalancedChen/CurrentMainTheorem.lean", "ImbalancedChen/CurrentNumericalTransfer.lean"]:
            self.require(self.fixed(relative) == self.fixed(relative, PREVIOUS_SHA),
                         "Existing conditional bridge and numerical transfer remain byte-identical: " + relative)
        for module in ROUND_MODULES[4]:
            self.require(module in workflow, "Fixed workflow explicitly names the new target " + module)
        for number in [3, 4]:
            audit = self.fixed(f"verification/parts/p0/Round{number}Audit.lean").decode("utf-8")
            self.require(re.search(r"(?m)^\s*set_option\s+pp\.all\s+true\s*$", audit) is not None,
                         f"Fixed Round{number} audit actually enables pp.all")
            for option in ["pp.proofs true", "pp.deepTerms true", "pp.maxSteps 1000000"]:
                self.require("set_option " + option in audit, f"Fixed Round{number} audit enables " + option)

        build_matches = re.findall(r"(?m)^Build completed successfully \((\d+) jobs\)\.$", self.stage_logs["build"])
        self.require(len(build_matches) == 1, "Full build has one actual successful build footer")
        target_matches = re.findall(r"(?m)^Build completed successfully \((\d+) jobs\)\.$", self.stage_logs["round4-targets"])
        self.require(len(target_matches) == 1, "Explicit four-target build has one actual successful build footer")
        replay_lines = self.stage_logs["leanchecker"].splitlines()
        self.require(any(line.startswith("Bundled leanchecker: ") and "v4.33.0-rc1/bin/leanchecker" in line
                         for line in replay_lines), "Kernel replay uses the bundled pinned checker path")
        self.require(any("Lean (version 4.33.0-rc1," in line and "commit " + LEAN_COMMIT in line
                         for line in replay_lines), "Kernel replay records the exact Lean version and commit")
        self.require("replaying ImbalancedChen" in replay_lines, "Actual bundled kernel replay includes the root")
        replayed = []
        for row in accepted:
            module = row["module"]
            self.require("replaying " + module in replay_lines, "Actual root kernel replay marker exists for " + module)
            replayed.append(module)
        axiom_log = self.stage_logs["axiom-audit"]
        self.require("axiom-audit @ v0.1.2 (" + AXIOM_AUDIT_COMMIT + ")" in axiom_log,
                     "Root axiom audit records the fixed upstream v0.1.2 commit")
        matches = re.findall(
            r"(?m)^axiom-audit: audited (\d+) declaration\(s\) under 'ImbalancedChen'; all within the allowlist \[([^\]]+)\]\.$",
            axiom_log,
        )
        self.require(len(matches) == 1, "Actual root axiom audit has one complete success footer")
        count, allowed = matches[0]
        self.require(set(s.strip() for s in allowed.split(",")) == ALLOWED_AXIOMS,
                     "Root axiom audit used exactly the three standard allowed axioms")
        self.require(int(count) >= 1005 and "axiom-audit completed successfully" in axiom_log.splitlines(),
                     "Root axiom audit has a positive full-root census and completion marker")
        self.report["observed"].update(
            full_build_jobs=int(build_matches[0]), explicit_target_build_jobs=int(target_matches[0]),
            explicit_target_modules=list(ROUND_MODULES[4]), accepted_module_replay_markers=sorted(replayed),
            accepted_module_replay_count=len(replayed), root_owned_declarations_audited=int(count),
            axiom_audit_version="v0.1.2", axiom_audit_commit=AXIOM_AUDIT_COMMIT,
            allowed_axioms=sorted(ALLOWED_AXIOMS),
        )
        self.ledger = ledger
        self.accepted = accepted
        return ledger, inherited

    def expected_snapshot(self, number: int) -> tuple[set[str], dict[str, str]]:
        modules = set(ROUND_MODULES[number]) | {"ImbalancedChen", FINAL_MODULE}
        for module in sorted(modules.copy()):
            code = lean_code(self.fixed(module.replace(".", "/") + ".lean").decode("utf-8"))
            for line in code.splitlines():
                if line.strip().startswith("import "):
                    modules.update(name for name in line.strip().split()[1:]
                                   if name == "ImbalancedChen" or name.startswith("ImbalancedChen."))
        sources = {module.replace(".", "/") + ".lean" for module in modules} | set(FROZEN)
        sources.update({f"verification/parts/p0/Round{number}Audit.lean",
                        f"verification/parts/p0/check_round{number}_types.py",
                        "verification/parts/p0/check_pins.py", "verification/verify_variable_envelope_boxes.py"})
        return modules, {relative: sha256(self.fixed(relative)) for relative in sorted(sources)}

    def check_record(self, record: dict, require_readable: bool = True) -> None:
        self.require(record.get("kind") != "axiom" and isinstance(record.get("axioms"), list)
                     and set(record["axioms"]) <= ALLOWED_AXIOMS,
                     "Declaration has only allowed transitive axioms: " + record.get("name", "<missing>"))
        for key in (["type", "readable_type"] if require_readable else ["type"]):
            value = record.get(key)
            self.require(isinstance(value, str) and bool(value.strip())
                         and not any(marker in value for marker in ["⋯", "…", "<proof>"]),
                         "Complete non-elided " + key + " exists: " + record.get("name", "<missing>"))

    def read_export(self, number: int) -> tuple[list[dict], dict, dict]:
        candidates = []
        ignored = []
        for member in self.members:
            if f"/.lake/part0-round{number}-types/" not in "/" + member or not member.endswith("/receipt.json"):
                continue
            receipt = json.loads(self.member(member))
            if receipt.get("source_commit") == EXPECTED_SHA:
                candidates.append((member, receipt))
            else:
                ignored.append({"member": member, "source_commit": receipt.get("source_commit"), "status": receipt.get("status")})
        self.report["observed"][f"ignored_other_source_round{number}_receipts"] = ignored
        self.require(len(candidates) == 1, f"Exactly one actual Round{number} receipt is bound to the expected SHA",
                     [member for member, _ in candidates])
        member, receipt = candidates[0]
        parent = str(PurePosixPath(member).parent)
        stage = f"round{number}-types"
        expected = ROUND_MODULES[number]
        total = sum(expected.values())
        self.require(receipt.get("schema") == f"p0-round{number}-types-export-v1" and receipt.get("status") == "PASS",
                     f"Actual Round{number} receipt has the expected schema and PASS status")
        self.require(receipt.get("source_commit_after") == EXPECTED_SHA, f"Round{number} export source SHA is unchanged after execution")
        self.require(receipt.get("expected_defining_module_counts") == expected and receipt.get("expected_owned_declarations") == total,
                     f"Round{number} receipt uses the fixed defining-module census")
        self.require(receipt.get("lean_invocation_started") is True and receipt.get("lean_exit_code") == 0
                     and receipt.get("pin_check_exit_code") == 0 and receipt.get("failures") == [],
                     f"Round{number} actual compiler and pin check completed successfully")
        for key in ["production_modules_recompiled", "production_modules_replayed", "dependencies_built", "toolchain_bootstrapped"]:
            self.require(receipt.get(key) is False, f"Round{number} supplemental exporter scope is honest for " + key)
        self.require(receipt.get("final_bridge_name") == FINAL_BRIDGE and receipt.get("final_bridge_is_conditional") is True
                     and receipt.get("hLower_hUpper_discharged") is False,
                     f"Round{number} receipt keeps the final bridge conditional")
        self.require(receipt.get("full_types_untruncated") is True and receipt.get("unsafe_and_new_axiom_checks") == "PASS_IN_LEAN",
                     f"Round{number} actual export reports complete types and Lean-side full declaration checks")
        self.require(receipt.get("inherited_lean_search_paths_cleared") is True and receipt.get("audit_object_before") == {},
                     f"Round{number} audit output began fresh and inherited Lean search paths were cleared")
        command = receipt.get("command", [])
        self.require(len(command) == 7 and PurePosixPath(command[0]).name == "lake"
                     and command[1:5] == ["env", "lean", "-DwarningAsError=true", "-o"]
                     and command[5].endswith(f"/Round{number}Audit.olean")
                     and command[6] == f"verification/parts/p0/Round{number}Audit.lean",
                     f"Round{number} actual command is the strict intended audit compilation")
        self.require(receipt.get("timeout_seconds") == {3: 540, 4: 1440}[number], f"Round{number} actual timeout matches fixed workflow")
        self.require(receipt.get("inputs_before") == receipt.get("inputs_after"),
                     f"Round{number} before/after source and production object snapshots are identical")
        modules, sources = self.expected_snapshot(number)
        snapshot = receipt["inputs_before"]
        self.require(snapshot.get("source_sha256") == sources, f"Round{number} complete source snapshot equals the exact published Git bytes")
        objects = snapshot.get("production_olean_parts", {})
        self.require(set(objects) == modules, f"Round{number} production object module set equals fixed import-derived scope")
        for module in sorted(modules):
            main = ".lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
            parts = objects[module]
            self.require(isinstance(parts, dict) and main in parts and bool(parts)
                         and all((path == main or path.startswith(main + "."))
                                 and isinstance(digest, str) and SHA256_RE.fullmatch(digest)
                                 for path, digest in parts.items()),
                         f"Round{number} captured valid object parts for " + module)

        output_relative = receipt.get("output_directory", "")
        self.require(output_relative.startswith(f".lake/part0-round{number}-types/")
                     and (parent == output_relative or parent.endswith("/" + output_relative)),
                     f"Round{number} receipt names its actual archive directory")
        self.require(command[5].endswith("/" + output_relative + f"/Round{number}Audit.olean"),
                     f"Round{number} actual output command is bound to this receipt directory")
        for stream in ["stdout", "stderr"]:
            stream_member = parent + "/" + stream + ".log"
            raw = self.member(stream_member)
            self.require(sha256(raw) == receipt.get(stream + "_sha256"), f"Round{number} original {stream} hash matches its receipt")
            self.require(receipt.get(stream + "_path") == output_relative + "/" + stream + ".log",
                         f"Round{number} original {stream} path is bound to this receipt directory")
            diagnostic = first_diagnostic(raw.decode("utf-8", errors="replace"))
            if diagnostic:
                self.diagnostics.append({"stream": stream, "stage": stage, "artifact_member": stream_member, **diagnostic})
            self.require(diagnostic is None and receipt.get(stream + "_first_lean_diagnostic") is None,
                         f"Round{number} actual {stream} has no Lean error diagnostic", diagnostic)
        output_hashes = receipt.get("compiler_output_files_sha256", {})
        self.require(set(output_hashes) == {"declarations.json", "final-bridge.json", "final-bridge-type.txt"},
                     f"Round{number} receipt covers all three compiler-derived payloads")
        for filename, digest in output_hashes.items():
            self.require(sha256(self.member(parent + "/" + filename)) == digest,
                         f"Round{number} exact compiler payload hash matches for " + filename)
        audit_parts = receipt.get("audit_object_after", {})
        audit_main = output_relative + f"/Round{number}Audit.olean"
        self.require(audit_main in audit_parts and bool(audit_parts), f"Round{number} audit produced a nonempty captured object set")
        for path, digest in audit_parts.items():
            self.require(path == audit_main or path.startswith(audit_main + "."), f"Round{number} audit object part is scoped to its output")
            object_member = parent + "/" + PurePosixPath(path).name
            raw = self.member(object_member)
            self.require(bool(raw) and sha256(raw) == digest, f"Round{number} archived audit object part matches its actual receipt")

        stdout = self.member(parent + "/stdout.log").decode("utf-8")
        lines = stdout.splitlines()
        prefix = f"P0_ROUND{number}_"
        def records(suffix: str) -> list:
            marker = prefix + suffix + " "
            return [json.loads(line[len(marker):]) for line in lines if line.startswith(marker)]
        declarations = json.loads(self.member(parent + "/declarations.json"))
        bridge = json.loads(self.member(parent + "/final-bridge.json"))
        module_records = records("MODULE")
        totals = [int(line[len(prefix + "COUNT "):]) for line in lines if line.startswith(prefix + "COUNT ")]
        self.require(records("DECL") == declarations, f"Round{number} saved declarations equal the original raw compiler marker records")
        self.require(records("FINAL_BRIDGE") == [bridge], f"Round{number} saved final bridge equals the original raw compiler marker record")
        self.require(totals == [total] and len(declarations) == total and len({d["name"] for d in declarations}) == total,
                     f"Round{number} raw total and unique full declaration count match")
        self.require(Counter(d["module"] for d in declarations) == Counter(expected), f"Round{number} actual defining-module counts match")
        self.require(len(module_records) == len(expected)
                     and {d["module"]: d["count"] for d in module_records} == expected,
                     f"Round{number} original per-module census markers match exactly")
        self.require(receipt.get("declaration_count") == total and receipt.get("bridge_count") == 1,
                     f"Round{number} receipt's observed counts agree with original output")
        self.require(bridge.get("name") == FINAL_BRIDGE and bridge.get("module") == FINAL_MODULE
                     and bridge.get("kind") == "theorem", f"Round{number} prints the exact existing final bridge")
        self.require(FINAL_BRIDGE not in {d["name"] for d in declarations}, f"Round{number} separate final bridge is not counted in production declarations")
        for record in declarations + [bridge]:
            self.check_record(record)
        self.require("hLower" in bridge["type"] and "hUpper" in bridge["type"],
                     f"Round{number} actual pp.all final type still visibly requires hLower and hUpper")
        union = sorted({axiom for record in declarations + [bridge] for axiom in record["axioms"]})
        self.require(receipt.get("transitive_axiom_union") == union, f"Round{number} declared axiom union matches all actual records")
        start, end = parse_time(receipt["started_utc"]), parse_time(receipt["finished_utc"])
        stage_row = self.stage_receipts[stage]
        self.require((start - parse_time(stage_row["started_utc"])).total_seconds() >= -1
                     and (parse_time(stage_row["finished_utc"]) - end).total_seconds() >= -1,
                     f"Round{number} actual export timestamps are inside its own gate")
        self.require(0 <= receipt.get("elapsed_seconds", -1) <= stage_row["elapsed_seconds"] + 2,
                     f"Round{number} actual compiler duration fits its gate duration")
        self.require(stdout in self.stage_logs[stage], f"Round{number} stage log contains the exact actual raw compiler stream")
        invocation_receipts = []
        for line in self.stage_logs[stage].splitlines():
            if line.startswith('{"status":'):
                try:
                    value = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(value, dict) and "receipt" in value:
                    invocation_receipts.append(value)
        self.require(len(invocation_receipts) == 1 and invocation_receipts[0].get("status") == "PASS"
                     and invocation_receipts[0].get("failures") == []
                     and invocation_receipts[0]["receipt"].endswith("/" + output_relative + "/receipt.json"),
                     f"Round{number} actual stage's final marker identifies exactly this successful receipt")
        for name in self.members:
            if name.startswith(parent + "/"):
                self.save_member(name, f"actual-round{number}/" + name[len(parent) + 1:])
        summary = {
            "receipt_archive_member": member, "receipt_sha256": sha256(self.member(member)),
            "source_commit": receipt["source_commit"], "actual_type_format": "PP_ALL_COMPLETE",
            "declaration_count": total, "separate_final_bridge_count": 1,
            "source_inputs": len(sources), "production_object_modules": len(objects),
            "input_snapshots_equal": True, "production_objects_replayed_by_exporter": False,
            "production_objects_replayed_by_separate_root_gate": True,
            "type_payload_sha256": output_hashes["declarations.json"],
            "actual_compiler_seconds": receipt["elapsed_seconds"],
            "allowed_transitive_axiom_union": union,
        }
        self.report["observed"][f"round{number}_export"] = summary
        self.export_receipts[number] = receipt
        return declarations, bridge, summary

    def merge_and_write(self, inherited: list[dict], r3: list[dict], r4: list[dict], bridge3: dict, bridge4: dict) -> None:
        self.require(bridge3 == bridge4, "Both actual exports print identical complete final-bridge records")
        for key in ["production_olean_parts"]:
            self.require(self.export_receipts[3]["inputs_before"][key] == self.export_receipts[4]["inputs_before"][key],
                         "Production object bindings remain identical across Round3 and Round4 actual exports")
        objects = self.export_receipts[4]["inputs_before"]["production_olean_parts"]
        inherited393 = [record for record in inherited if record["module"] not in ROUND_MODULES[3]]
        previous198 = [record for record in inherited if record["module"] in ROUND_MODULES[3]]
        self.require(len(inherited393) == 393 and len(previous198) == 198, "Inherited 591 splits into old393 and previous Round3 198 without duplication")
        self.require({record["name"] for record in previous198} == {record["name"] for record in r3},
                     "Actual current Round3 declaration names replace exactly the prior 198 names")
        inherited_formats = Counter(record.get("actual_type_format") for record in inherited393)
        self.require(inherited_formats == {"PP_ALL_COMPLETE": 388, "DEFAULT_META_PPEXPR_COMPLETE": 5},
                     "Old393 preserve 388 actual pp.all and five complete default records")
        defaults = [record for record in inherited393 if record["actual_type_format"] == "DEFAULT_META_PPEXPR_COMPLETE"]
        self.require(len(defaults) == 5 and all(record["module"] == "ImbalancedChen.CurrentChenBuchstabRefinement" for record in defaults),
                     "Only the five historical Buchstab types retain the default Meta.ppExpr format")
        inherited_member = LEDGER_BASE + "/INHERITED_TYPES_591.json"
        inherited_ref = {"commit": EXPECTED_SHA, "path": inherited_member, "sha256": sha256(self.fixed(inherited_member)),
                         "relative_refs_resolve_under": LEDGER_BASE,
                         "nested_historical_ref_resolution": LEDGER_BASE + "/REF_RESOLUTION.md"}
        merged = []
        accepted_by_module = {row["module"]: row for row in self.accepted}
        for old in inherited393:
            self.check_record(old, require_readable=False)
            self.require(old["production_source_sha256"] == sha256(self.fixed(old["module"].replace(".", "/") + ".lean")),
                         "Inherited compiler record is bound to unchanged current source: " + old["name"])
            record = copy.deepcopy(old)
            record["inherited_provenance"] = record.get("provenance")
            record["provenance"] = {
                "kind": "REUSED_OLD393_COMPLETE_COMPILER_RECORD_WITH_CURRENT_ROOT_REPLAY",
                "inherited_record_container": inherited_ref,
                "original_record_provenance": old.get("provenance"),
                "current_type_print_rerun": False,
                "current_source_bytes_match_inherited_compiler_record": True,
            }
            record["integration_source_commit"] = EXPECTED_SHA
            record["current_root_verification"] = {"run_id": EXPECTED_RUN, "job_id": EXPECTED_JOB,
                                                    "kernel_replay_marker": "replaying " + record["module"],
                                                    "production_olean_parts": objects[record["module"]],
                                                    "object_capture_scope": "Subsequent Round3/4 exporter snapshots; the root replay marker itself has no object digest"}
            merged.append(record)
        for number, records in [(3, r3), (4, r4)]:
            for raw in records:
                record = copy.deepcopy(raw)
                module = record["module"]
                record.update(
                    actual_type_format="PP_ALL_COMPLETE", primary_type_complete=True,
                    contains_omission_marker=False, source_fixed_commit=EXPECTED_SHA,
                    integration_source_commit=EXPECTED_SHA,
                    production_source_sha256=sha256(self.fixed(module.replace(".", "/") + ".lean")),
                    provenance={
                        "kind": f"ACTUAL_CURRENT_P0_ROUND{number}_COMPILER_EXPORT",
                        "run_id": EXPECTED_RUN, "job_id": EXPECTED_JOB,
                        "artifact_id": self.report["observed"]["artifact_id"],
                        "artifact_sha256": self.report["observed"]["artifact_sha256"],
                        "receipt_archive_member": self.report["observed"][f"round{number}_export"]["receipt_archive_member"],
                        "type_payload_sha256": self.report["observed"][f"round{number}_export"]["type_payload_sha256"],
                        "actual_record_reexecuted_this_run": True,
                        "producer_source_identity_from_published_ledger": accepted_by_module[module]["source"],
                        "producer_source_identity_record_scope": {"commit": EXPECTED_SHA, "base_path": LEDGER_BASE},
                    },
                    current_root_verification={
                        "run_id": EXPECTED_RUN, "job_id": EXPECTED_JOB,
                        "kernel_replay_marker": "replaying " + module,
                        "production_olean_parts": objects[module],
                        "object_capture_scope": "Subsequent Round3/4 exporter snapshots; the root replay marker itself has no object digest",
                    },
                )
                merged.append(record)
        merged.sort(key=lambda record: (record["module"], record["name"]))
        self.require(len(merged) == len({record["name"] for record in merged}) == 1005, "Final merged census is exactly 1005 unique complete production types")
        self.require(Counter(record["module"] for record in merged) ==
                     Counter({row["module"]: row["declarations"]["owned_audited"] for row in self.accepted}),
                     "Final1005 exactly cover all 23 accepted defining-module inventories")
        formats = Counter(record["actual_type_format"] for record in merged)
        self.require(formats == {"PP_ALL_COMPLETE": 1000, "DEFAULT_META_PPEXPR_COMPLETE": 5},
                     "Actual successful merged formats are exactly 1000 pp.all and five default complete")
        self.require(FINAL_BRIDGE not in {record["name"] for record in merged}, "Final bridge remains a separate type, outside the 1005 census")
        self.report["observed"].update(
            accepted_modules=23, pending_components=14, inherited_complete_types=393,
            actual_round3_complete_types=198, actual_round4_complete_types=414,
            complete_merged_types=1005, actual_merged_type_formats=dict(formats),
            actual_pp_all_final_bridge_separate=True,
        )
        ledger = copy.deepcopy(self.ledger)
        ledger["schema"] = "chen-p0-round4-actual-core-verified-ledger-v1"
        ledger["generated_utc"] = utc_now()
        ledger["historical_candidate_counts"] = copy.deepcopy(ledger["counts"])
        ledger["new_integration"] = {
            "commit": EXPECTED_SHA, "tree": EXPECTED_TREE, "status": "PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE",
            "run_id": EXPECTED_RUN, "job_id": EXPECTED_JOB,
            "full_build": "PASS", "root_stock_kernel_replay": "PASS", "root_axiom_audit": "PASS",
            "explicit_four_targets": "PASS", "actual_round3_type_export": "PASS", "actual_round4_type_export": "PASS",
            "main_theorem_is_still_conditional": True, "hLower_hUpper_discharged": False,
        }
        ledger["counts"].update(
            new_integration_root_validated_modules=23, new_integration_root_gates_status="PASS",
            current_received_complete_types=1005, current_received_pp_all_types=1000,
            current_received_default_complete_types=5,
            new_received_complete_types=414, new_received_pp_all_types=414, new_received_default_complete_types=0,
            actual_current_run_type_exports=612, current_inherited_type_records=393,
        )
        for row in ledger["modules"]:
            if row["component_evidence_accepted"]:
                module = row["module"]
                row["new_integration_sha"] = EXPECTED_SHA
                row["new_integration_gates"] = "PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE"
                row["current_integration_production_olean_parts"] = objects[module]
                row["current_integration_kernel_replay_marker"] = "replaying " + module
                row["current_integration_source_sha256"] = sha256(self.fixed(row["repository_path"]))
                row["current_type_formats"] = dict(Counter(record["actual_type_format"] for record in merged if record["module"] == module))
                row["previous_received_declarations"] = copy.deepcopy(row["declarations"])
                row["declarations"]["actual_type_formats"] = row["current_type_formats"]
                row["current_type_records"] = "COMPLETE_TYPES_1005.json"
                row["current_type_print_this_run"] = module in ROUND_MODULES[3] or module in ROUND_MODULES[4]
        write_json(self.output / "COMPLETE_TYPES_1005.json", merged)
        write_json(self.output / "TYPE_FORMATS_1005.json", [
            {"name": record["name"], "module": record["module"], "actual_type_format": record["actual_type_format"],
             "primary_type_complete": True, "compiler_record_origin": record["provenance"]["kind"],
             "integration_source_commit": EXPECTED_SHA, "production_source_sha256": record["production_source_sha256"]}
            for record in merged
        ])
        write_json(self.output / "MODULE_LEDGER_VERIFIED.json", ledger)
        write_json(self.output / "ACTUAL_FINAL_BRIDGE.json", bridge4)
        (self.output / "ACTUAL_FINAL_BRIDGE_TYPE.txt").write_text(
            "source_commit=" + EXPECTED_SHA + "\nrun_id=" + str(EXPECTED_RUN) + "\n\n" + FINAL_BRIDGE
            + "\n\nActual complete pp.all type:\n" + bridge4["type"]
            + "\n\nActual complete readable type:\n" + bridge4["readable_type"]
            + "\n\nThis existing theorem still requires hLower and hUpper. The full theorem is not closed.\n",
            encoding="utf-8",
        )
        write_json(self.output / "SOURCE_OBJECT_BINDINGS.json", {
            "source_commit": EXPECTED_SHA,
            "round3_inputs_before_and_after": self.export_receipts[3]["inputs_before"],
            "round4_inputs_before_and_after": self.export_receipts[4]["inputs_before"],
            "equality_checked_within_and_between_exports": True,
            "production_object_bytes_all_embedded": False,
            "object_scope": "Original runner-captured production object part hashes; audit output objects are in the supplied archive.",
        })
        self.report["status"] = "PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE"
        self.report["evidence_status"] = "FULLY_CONSUMED_ALL_REQUIRED_GATES_AND_TYPES_PASS"

    def run(self) -> int:
        exit_code = 1
        try:
            self.prepare()
            self.read_metadata()
            self.check_fixed_commit()
            self.read_logs()
            _, inherited = self.check_root_and_fixed_inputs()
            r3, bridge3, _ = self.read_export(3)
            r4, bridge4, _ = self.read_export(4)
            self.merge_and_write(inherited, r3, r4, bridge3, bridge4)
            exit_code = 0
        except KnownCIFailure as error:
            self.report.update(status="FAILED_CI_FROM_SUPPLIED_METADATA", ci_failure_reason=str(error))
            exit_code = 1
        except EvidencePending as error:
            self.note_missing_evidence(str(error))
            self.report["pending_reason"] = str(error)
            if self.report["known_ci_failures"]:
                self.report.update(status="FAILED_CI_WITH_INCOMPLETE_EVIDENCE",
                                   ci_failure_reason="Known bound CI metadata failure is retained despite missing or incomplete evidence")
                exit_code = 1
            else:
                self.report["status"] = "PENDING"
                exit_code = 2
        except Exception as error:
            self.report.update(status="FAILED_EVIDENCE_CONSUMPTION", evidence_status="INVALID_OR_CONSUMER_BLOCKED",
                               error=f"{type(error).__name__}: {error}")
            exit_code = 1
        finally:
            if self.archive is not None:
                self.archive.close()
            # If prepare rejected an occupied or in-repository output, do not touch it.
            forbidden = (self.output == self.args.repo.resolve() or self.args.repo.resolve() in self.output.parents)
            occupied_rejection = any(not item["pass"] and item["check"].startswith("Output directory is new") for item in self.checks)
            if not forbidden and not occupied_rejection:
                self.output.mkdir(parents=True, exist_ok=True)
                self.report.update(finished_utc=utc_now(), consumer_exit_code=exit_code,
                                   checks_passed=sum(item["pass"] for item in self.checks),
                                   checks_failed=sum(not item["pass"] for item in self.checks),
                                   first_real_lean_diagnostics_preserved=len(self.diagnostics))
                write_json(self.output / "CORE_RECEIPT.json", self.report)
                write_json(self.output / "CHECKS.json", self.checks)
                write_json(self.output / "FIRST_REAL_LEAN_DIAGNOSTICS.json", {
                    "order_claim": "First actual Lean error retained separately for each available raw stream; no cross-stream ordering is asserted.",
                    "diagnostics": self.diagnostics,
                })
                self.write_markdown()
                write_json(self.output / "OUTPUT_MANIFEST.json", [
                    {"path": str(path.relative_to(self.output)), "bytes": path.stat().st_size, "sha256": sha256(path.read_bytes())}
                    for path in sorted(self.output.rglob("*")) if path.is_file() and path.name != "OUTPUT_MANIFEST.json"
                ])
        print(json.dumps({"status": self.report["status"], "consumer_exit_code": exit_code,
                          "expected_source_commit": EXPECTED_SHA,
                          "ci_metadata_status": self.report["ci_metadata_status"],
                          "known_ci_failure_count": len(self.report["known_ci_failures"]),
                          "evidence_status": self.report["evidence_status"],
                          "receipt": str(self.output / "CORE_RECEIPT.json"),
                          "pending_reason": self.report.get("pending_reason"), "error": self.report.get("error")}, ensure_ascii=False))
        return exit_code

    def write_markdown(self) -> None:
        observed = self.report["observed"]
        lines = ["# Part 0 exact core evidence receipt", "", "Status: **" + self.report["status"] + "**", "",
                 "Expected source: " + EXPECTED_SHA, "", "Expected tree: " + EXPECTED_TREE, "",
                 f"Actual requested run/job: {EXPECTED_RUN} / {EXPECTED_JOB} (attempt {EXPECTED_ATTEMPT}).", "",
                 "This is an offline evidence consumer. It does not execute Lean, a kernel checker, or Actions.", ""]
        lines += ["CI metadata status: " + self.report["ci_metadata_status"] + ". Evidence status: " + self.report["evidence_status"] + ".", ""]
        if self.report["known_ci_failures"]:
            lines += ["## Known CI metadata failure", "",
                      "The following source/run/job-bound supplied metadata was already non-successful. Missing evidence does not replace these observations with a pending CI result.", "",
                      "| Scope | Identity | Status | Conclusion |", "|---|---|---|---|"]
            for item in self.report["known_ci_failures"]:
                lines.append(f"| {item['scope']} | {item['identity']} | {item['status']} | {item['conclusion']} |")
            lines += ["", "These metadata conclusions are not Lean error diagnostics. Available actual raw Lean diagnostics are recorded separately.", ""]
        if self.report.get("pending_reason"):
            lines += ["## Pending evidence", "", self.report["pending_reason"], "",
                      "No verified 1005-type payload or successful integrated module ledger has been produced.", ""]
        if self.report["pending_evidence_reasons"]:
            lines += ["## Missing or incomplete evidence", ""]
            lines += ["- " + reason for reason in self.report["pending_evidence_reasons"]]
            lines.append("")
        if self.report.get("error"):
            lines += ["## First consumer failure", "", self.report["error"], "",
                      "Raw supplied evidence and any retained real Lean diagnostics remain distinguishable from this consumer failure.", ""]
        if "stages" in observed:
            lines += ["## Actual required gates", "", "| Gate | Outcome | Seconds | Exit |", "|---|---|---:|---:|"]
            for row in observed["stages"]:
                lines.append(f"| {row['stage']} | {row['outcome']} | {row['elapsed_seconds']} | {row['exit_code']} |")
            lines.append("")
        if self.report["status"] == "PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE":
            lines += ["## Actual accepted scope", "",
                      f"Artifact {observed['artifact_id']}: {observed['artifact_bytes']} bytes; SHA-256 {observed['artifact_sha256']}.", "",
                      f"Full root build: {observed['full_build_jobs']} jobs. Actual root replay includes all 23 accepted module markers. "
                      f"The root axiom audit reports {observed['root_owned_declarations_audited']} declarations with only the three standard allowed axioms.", "",
                      "The final type census is 393 inherited complete records + 198 actual Round3 records + 414 actual Round4 records = 1005. "
                      "Exactly 1000 are complete pp.all records; the five inherited Buchstab records remain complete default Meta.ppExpr records. "
                      "The separate final bridge is excluded from this production census.", "",
                      "The 37-component ledger contains 23 components accepted at this exact integration SHA and 14 pending components. "
                      "The eight upstream S1LowerRosser declarations remain separate.", ""]
        lines += ["## Unclosed theorem inputs", "",
                  "The existing final bridge remains conditional on hLower and hUpper. The analytic K and c suppliers are still required. "
                  "Successful component integration does not discharge these hypotheses.", "",
                  "## Provenance and limits", ""]
        lines += ["- " + value for value in self.report["limitations"]]
        lines += ["", "Relative references inside the inherited ledger retain their published fixed-source scope. "
                  "Resolve them using " + EXPECTED_SHA + ":" + LEDGER_BASE + "/REF_RESOLUTION.md; this output does not claim to duplicate every historical payload.", ""]
        (self.output / "RECEIPT.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path("/workspace/scratch/535d89efd063/goldbach-formalization"))
    parser.add_argument("--artifact-zip", type=Path, help="Actual downloaded core artifact ZIP; read directly without extraction")
    parser.add_argument("--run-json", type=Path, help="Raw completed GitHub run metadata")
    parser.add_argument("--jobs-json", type=Path, help="Raw GitHub jobs response or the raw expected job object")
    parser.add_argument("--artifacts-json", type=Path, help="Raw GitHub artifacts response or raw expected artifact metadata")
    parser.add_argument("--output", type=Path, required=True, help="New/empty output directory outside the repository")
    args = parser.parse_args()
    return Consumer(args).run()


if __name__ == "__main__":
    raise SystemExit(main())
