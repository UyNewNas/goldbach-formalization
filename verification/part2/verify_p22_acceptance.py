#!/usr/bin/env python3
"""Verify the archived Lean acceptance of the 20261106 P2.2 first integral."""

import argparse
from fractions import Fraction
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys


REPO = Path(__file__).resolve().parents[2]
ACCEPTANCE = REPO / "docs/verification/20261125-p2.2-acceptance/acceptance.json"
EVIDENCE_COMMIT = "99c1f8ba1dc453b21f47e30b667db0de93d73387"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_FIELDS = (
    "name", "module", "kind", "type", "type_expression",
    "universe_parameters", "axioms", "is_private",
)
ENDPOINT_THEOREMS = {
    "polynomial_upper_le_selected",
    "originalFirstIntegral_literal_selected_bound",
    "originalFirstIntegral_le_budget_base_one",
}


class VerificationError(Exception):
    """An archived evidence or source consistency check failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def git(*args):
    result = subprocess.run(
        ["git", *args], cwd=REPO, capture_output=True, check=False,
        env={**os.environ, "GIT_NO_REPLACE_OBJECTS": "1", "GIT_NO_LAZY_FETCH": "1"},
    )
    require(result.returncode == 0, f"git {' '.join(args)}: {result.stderr.decode(errors='replace').strip()}")
    return result.stdout


def archive(path):
    return git("show", f"{EVIDENCE_COMMIT}:{path}")


def file_record(raw):
    return {"bytes": len(raw), "sha256": sha256(raw).hexdigest()}


def by_key(records, key):
    indexed = {record[key]: record for record in records}
    require(len(indexed) == len(records), f"Duplicate evidence records for {key}")
    return indexed


def verify_source(module, expected_sha):
    path = module.replace(".", "/") + ".lean"
    source = archive(path)
    require(sha256(source).hexdigest() == expected_sha, f"Archived source SHA-256 mismatch: {path}")
    require(git("show", f"HEAD:{path}") == source, f"HEAD source differs from accepted source: {path}")
    require(git("show", f":{path}") == source, f"Indexed source differs from accepted source: {path}")
    working_file = REPO / path
    if working_file.exists():
        require(working_file.read_bytes() == source, f"Working-tree source differs from accepted source: {path}")
    else:
        sparse = git("ls-files", "-t", "--", path).startswith(b"S ")
        require(sparse, f"Working-tree source is missing: {path}")
    return source


def verify_module(spec, source):
    name = spec["name"]
    module = f"ImbalancedChen.{name}"
    batch = spec["batch"]
    directory = f"docs/verification/20261123-blue-compilation/member-repair-batch{batch}"

    release = json.loads(archive(f"{directory}/FINAL_RELEASE.json"))
    require(release["status"] == "FINAL_RELEASE", f"Batch {batch}: final release missing")
    statuses = (
        "full_owned_including_private_generated", "normal_kernel_audit_all_exit0",
        "source_plus_five_outputs_still_equal_recorded_stage_hashes", "raw_logs_bytes_unchanged",
    )
    require(all(release[flag] is True for flag in statuses), f"Batch {batch}: release checks incomplete")

    validation_raw = archive(f"{directory}/VALIDATION_RESULTS.json")
    publication_raw = archive(f"{directory}/PUBLICATION_FILES.json")
    for key, raw in (("validation_results", validation_raw), ("publication_files", publication_raw)):
        require(sha256(raw).hexdigest() == release[f"{key}_sha256"], f"Batch {batch}: {key} SHA-256 mismatch")
    validation = json.loads(validation_raw)
    require(
        validation["status"] == "PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS",
        f"Batch {batch}: archived validation did not pass",
    )
    statuses = (
        "full_owned_including_private_generated", "only_standard_axioms",
        "pp_all_true_no_elisions", "source_plus_five_outputs_unchanged_across_kernel_and_audit",
    )
    require(all(validation[flag] is True for flag in statuses), f"Batch {batch}: validation checks incomplete")
    publication = by_key(json.loads(publication_raw)["files"], "path")

    def published(path):
        raw = archive(f"{directory}/{path}")
        require(
            publication[path] == {"path": path, **file_record(raw)},
            f"Batch {batch}: published bytes or SHA-256 mismatch for {path}",
        )
        return raw

    source_sha = spec["sha256"]
    expected_source = json.loads(published("EXPECTED_SOURCES.json"))[module]
    require(expected_source == source_sha, f"{module}: expected source SHA-256 mismatch")
    selection = json.loads(published("SOURCE_SELECTION.json"))[module]
    require(selection["postimage_sha256"] == source_sha, f"{module}: selected source SHA-256 mismatch")
    readback = release["actual_source_readback"][module]
    require(
        readback["main_exists"] is True
        and readback["Member_source_sha256"] == readback["main_source_sha256"] == source_sha,
        f"{module}: released source readback mismatch",
    )
    after_normal = json.loads(published(f"{name}-AFTER_NORMAL.json"))
    after_kernel = json.loads(published(f"{name}-AFTER_KERNEL.json"))
    require(
        len(after_normal) == 6 and after_normal == after_kernel == validation["source_plus_five_outputs"][module],
        f"{module}: source and five output records differ across stages",
    )
    require(
        after_normal[f"ImbalancedChen/{name}.lean"] == file_record(source),
        f"{module}: validated source bytes differ",
    )

    logs = {}
    log_bytes = {}
    commands = {
        "normal": f"{name}-normal",
        "kernel": f"{name}-kernel",
        "audit": "all-public-types-axioms",
    }
    tails = {
        "normal": ["lake", "build", f"{module}:olean"],
        "kernel": ["lake", "env", "leanchecker", "--verbose", module],
    }
    for stage, command_name in commands.items():
        command = json.loads(published(f"{command_name}-command.json"))
        require(
            command["name"] == command_name and command["exit_code"] == 0,
            f"{module}: failed {stage} command",
        )
        if stage == "audit":
            require(command == validation["audit_command"], f"{module}: audit command disagrees with validation")
            require(Path(command["argv"][-1]).name == "PublicAudit.lean", f"{module}: unexpected audit target")
        else:
            tail = tails[stage]
            require(
                command in validation[f"{stage}_commands"],
                f"{module}: {stage} command disagrees with validation",
            )
            require(command["argv"][-len(tail):] == tail, f"{module}: unexpected {stage} target")
        log_bytes[stage] = published(command["log"])
        log_sha = sha256(log_bytes[stage]).hexdigest()
        require(command["log_sha256"] == log_sha, f"{module}: {stage} log SHA-256 mismatch")
        logs[stage] = {
            "path": f"{directory}/{command['log']}",
            "sha256": log_sha,
            "exit_code": command["exit_code"],
        }

    prefix = b"AUDIT_RECORD "
    records = [
        json.loads(line[len(prefix):])
        for line in log_bytes["audit"].splitlines() if line.startswith(prefix)
    ]
    audited = by_key([record for record in records if record["module"] == module], "name")
    all_owned = json.loads(published("OWNED_EXPORTS.json"))
    owned = by_key([record for record in all_owned if record["module"] == module], "name")
    require(audited.keys() == owned.keys(), f"{module}: audit and owned declaration inventories differ")
    axioms = set()
    for declaration, record in owned.items():
        require(
            all(record[field] == audited[declaration][field] for field in AUDIT_FIELDS),
            f"{module}: type or audit fields differ for {declaration}",
        )
        require(record["is_axiom_declaration"] is False, f"{module}: new axiom declaration {declaration}")
        axioms.update(record["axioms"])
        require(record["axioms"] == record["transitive_axioms"], f"{module}: transitive axiom mismatch for {declaration}")
    require(axioms <= STANDARD_AXIOMS, f"{module}: nonstandard axioms: {sorted(axioms - STANDARD_AXIOMS)}")
    public = sum(not record["is_private"] for record in owned.values())
    for count_kind, count in (("owned", len(owned)), ("public", public)):
        count_key = f"{count_kind}_export_counts"
        require(
            count == spec[count_kind] == validation[count_key][module] == release[f"environment_{count_key}"][module],
            f"{module}: {count_kind} declaration count mismatch",
        )
    for theorem in spec.get("key_theorems", []):
        record = owned[f"{module}SourceOnly.{theorem}"]
        require(record["kind"] == "theorem" and not record["is_private"], f"{module}: missing public theorem {theorem}")
    return {
        "module": module, "batch": batch, "source_sha256": source_sha,
        "owned": len(owned), "public": public, "private": len(owned) - public,
        "axioms": sorted(axioms), "commands": logs,
    }


def check_fraction(selected_upper):
    """Repeat the finite rational comparison as a supplementary arithmetic check."""
    order = 16
    theta = Fraction(299, 500)
    rho = Fraction(19, 96)
    width = theta / rho - 3
    center = Fraction(0)
    for i in range(order):
        log_coefficient = Fraction((-1) ** i, i + 1)
        for j in range(order):
            reciprocal_coefficient = Fraction((-1) ** j, 2 ** (j + 1))
            power = i + j + 2
            center += log_coefficient * reciprocal_coefficient * width ** power / power
    center *= 4 / theta
    log_error = width ** (order + 1) / (1 - width)
    reciprocal_error = (width / 2) ** order / 2
    radius = (4 / theta) * width * (log_error / 2 + (width + log_error) * reciprocal_error)
    require(0 < radius <= Fraction(1, 2 ** 80), "Auxiliary Fraction check: radius bound failed")
    require(center + radius <= Fraction(selected_upper), "Auxiliary Fraction check: selected endpoint comparison failed")
    printed_upper = Fraction(76020940667, 10 ** 14)
    require(Fraction(selected_upper) < printed_upper, "Auxiliary Fraction check: printed upward bound failed")
    return {
        "order": order, "terms": order ** 2,
        "center_plus_radius_le_selected": True, "radius_le_two_pow_neg_80": True,
        "printed_upper": str(printed_upper), "selected_lt_printed_upper": True,
    }


def verify(manifest):
    require(
        manifest["node"] == "P2.2" and manifest["evidence_commit"] == EVIDENCE_COMMIT,
        "Wrong node or pinned evidence commit",
    )
    selection = json.loads(archive("docs/p1/20261124/SOURCE_SELECTION.json"))
    require(
        manifest["manuscript_release"] == "20261106"
        and manifest["manuscript_commit"] == selection["manuscript_commit"]
        and selection["manuscript_path"] == "paper/release-20261106/en",
        "Manuscript provenance mismatch",
    )
    catalog = json.loads(archive("docs/part2/adopted-evidence-catalog.json"))
    require(
        manifest["selected_upper"] == catalog["A_upper"]["base_components"]["first_integral"],
        "Selected upper endpoint differs from the archived catalog",
    )

    modules = by_key(manifest["modules"], "name")
    expected_modules = {
        "P2FirstIntegralSeries": 54,
        "P2FirstIntegralPolynomialEnclosure": 65,
        "P2OriginalFirstIntegralEndpoint": 86,
    }
    require(
        {name: spec["batch"] for name, spec in modules.items()} == expected_modules,
        "Unexpected P2.2 module or batch selection",
    )
    require(
        set(modules["P2OriginalFirstIntegralEndpoint"]["key_theorems"]) == ENDPOINT_THEOREMS,
        "Unexpected P2.2 endpoint theorem selection",
    )
    source_files = {
        f"ImbalancedChen.{name}": verify_source(f"ImbalancedChen.{name}", spec["sha256"])
        for name, spec in modules.items()
    }
    imports = {
        module.decode() for raw in source_files.values()
        for module in re.findall(rb"^import (ImbalancedChen\.[\w.]+)", raw, re.MULTILINE)
    }
    dependencies = manifest["direct_dependencies"]
    require(imports - source_files.keys() == dependencies.keys(), "P2.2 direct dependency set differs from source imports")
    p1_evidence = "docs/p1/20261124"
    dependency_receipts = json.loads(archive(f"{p1_evidence}/batch5-verified-evidence/AUDIT24_VALIDATION_RESULTS.json"))
    source_graph = json.loads(archive(f"{p1_evidence}/batch8-normal-supplement-audit/SOURCE_GRAPH.json"))["sources"]
    require(
        dependency_receipts["status"] == "PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS",
        "Dependency validation did not pass",
    )
    selected_sources = by_key(selection["sources"], "module")
    for module, expected_sha in dependencies.items():
        verify_source(module, expected_sha)
        graph_entry = source_graph[module]
        path = module.replace(".", "/") + ".lean"
        blob_id = git("rev-parse", f"{EVIDENCE_COMMIT}:{path}").decode().strip()
        require(
            graph_entry["sha256"] == dependency_receipts["project_dependency_sources"][module] == expected_sha
            and selected_sources[module]["sha256"] == expected_sha
            and blob_id == graph_entry["git_blob_sha1"] == graph_entry["normal_source_git_blob_sha1"]
            and graph_entry["source_binding_basis"] == "EXACT_NORMAL15_SOURCE_MATCHES_ACTUAL_CONTEXT_AND_REVIEW",
            f"{module}: source disagrees with the archived dependency provenance",
        )

    results = [verify_module(spec, source_files[f"ImbalancedChen.{name}"]) for name, spec in modules.items()]
    totals = {key: sum(result[key] for result in results) for key in ("owned", "public", "private")}
    require(totals == {"owned": 124, "public": 123, "private": 1}, "Unexpected P2.2 declaration totals")
    return {
        "status": "PASS_EXISTING_LEAN_EVIDENCE", "node": manifest["node"],
        "evidence_commit": EVIDENCE_COMMIT, "manuscript_commit": manifest["manuscript_commit"],
        "selected_upper": manifest["selected_upper"], "declarations": totals,
        "current_sources_match": True, "modules": results, "direct_dependencies": dependencies,
        "auxiliary_fraction_check": check_fraction(manifest["selected_upper"]),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=ACCEPTANCE)
    parser.add_argument("--output", type=Path, help="Write the verification result as JSON")
    args = parser.parse_args()
    try:
        result = verify(json.loads(args.manifest.read_bytes()))
        if args.output is not None:
            args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    except (OSError, ValueError, TypeError, KeyError, VerificationError) as error:
        print(f"P2.2 acceptance failed: {error}", file=sys.stderr)
        return 1
    print(f"{result['status']}: 3 modules, 9 logs, {result['declarations']['owned']} owned declarations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
