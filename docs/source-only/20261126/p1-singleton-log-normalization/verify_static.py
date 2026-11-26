#!/usr/bin/env python3
"""Bounded source/provenance checks only. Never invokes Lean, Lake or a cloud API."""

import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
MANIFEST = HERE / "SOURCE_REVIEW.json"
RECEIPT = HERE / "STATIC_VERIFICATION.json"
ENV = dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0",
           GIT_TERMINAL_PROMPT="0")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()


def fingerprint(data, row, label):
    require(len(data) == row["bytes"], f"{label}: byte count")
    require(sha(data) == row["sha256"], f"{label}: SHA256")
    require(blob(data) == row["git_blob"], f"{label}: Git blob")


def git_bytes(commit, path):
    return subprocess.run(
        ["git", "--no-lazy-fetch", "show", f"{commit}:{path}"],
        cwd=REPO, env=ENV, check=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE).stdout


def code_without_comments(text):
    """Keep newlines/positions while removing nested Lean comments and strings."""
    result = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            result[i] = " "
            i += 1
            while i < len(text):
                char = text[i]
                result[i] = " " if char != "\n" else "\n"
                i += 1
                if char == "\\" and i < len(text):
                    result[i] = " "
                    i += 1
                elif char == '"':
                    break
        else:
            i += 1
    require(depth == 0, "unclosed block comment")
    return "".join(result)


def main():
    manifest_bytes = MANIFEST.read_bytes()
    review = json.loads(manifest_bytes)
    require(review["status"] == "SOURCE_ONLY_NOT_ELABORATED_NO_FORMAL_ACCEPTANCE",
            "source-only status")
    candidate = review["candidate"]
    source = (REPO / candidate["path"]).read_bytes()
    fingerprint(source, candidate, "candidate")
    code = code_without_comments(source.decode())
    imports = re.findall(r"^import\s+(\S+)\s*$", code, re.MULTILINE)
    require(imports == candidate["literal_imports"], "two exact direct imports")
    names = re.findall(r"^theorem\s+(\S+)", code, re.MULTILINE)
    require(names == [r["name"] for r in review["declarations"]],
            "exactly the two recorded theorem declarations")
    require(not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code),
            "forbidden proof token")
    require(not re.search(r"\b(?:def|abbrev|instance|opaque)\s+", code),
            "no replacement definitions")
    require("field_simp" not in code, "no denominator cancellation at log n = 0")
    statements = []
    for declaration in review["declarations"]:
        start = declaration["byte_start_inclusive"]
        end = declaration["byte_end_exclusive"]
        block = source[start:end]
        statement, proof = block.split(b":= by", 1)
        require(sha(block) == declaration["sha256"], "declaration hash")
        require(sha(statement) == declaration["statement_sha256"], "statement hash")
        require(sha(b":= by" + proof) == declaration["proof_sha256"], "proof hash")
        require(source[:start].count(b"\n") + 1 == declaration["line_start"],
                "declaration start line")
        require(source[:end].count(b"\n") + 1 == declaration["line_end"],
                "declaration end line")
        statements.append(statement.decode())
    first, second = statements
    require("(n : ℕ) :" in first and "→" not in first, "unconditional all-n identity")
    require(second.index("∀ᶠ N") < second.index("∀ (kap : ℝ)"),
            "uniform threshold precedes kap and the actual indices")
    require("fs ∈ factorTuples (2*(j+1)) n" in second, "actual ordered tuple")
    require("assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs ≠ 0" in second,
            "actual assigned tuple weight")
    require(second.count("wordKernel Q rho N") == 2, "same Q/rho/N kernel twice")
    require("wordKernel Q rho N [completeProduct ns]" in second and
            "wordKernel Q rho N [n]" in second, "same complete-product kernel arguments")
    require(not re.search(r"\b(?:Prime|blockCoefficient|herror)\b", first + second),
            "no prime/aggregate/error premise text")

    checked = {}
    rows = review["source_bindings"] + review["bounded_deduplication"]["relevant_reference_files"]
    for row in rows:
        key = (row["commit"], row["path"])
        if key not in checked:
            published = git_bytes(*key)
            current = (REPO / row["path"]).read_bytes()
            require(current == published, f"pinned/current source mismatch: {row['path']}")
            fingerprint(current, row, row["path"])
            checked[key] = sha(current)
        else:
            require(checked[key] == row["sha256"], "repeated binding conflict")
    manuscript = review["manuscript"]
    fingerprint(Path(manuscript["local_cache"]).read_bytes(), manuscript, "fixed 1106 cache")
    require(all(not review["build_boundary"][key] for key in [
        "lean_run", "kernel_audit_run", "owned_inventory_run",
        "full_recursive_source_closure_checked", "native_dependency_readiness_checked",
        "formal_acceptance_added"]), "build/acceptance boundary")
    receipt = {
        "schema": "p1_actual_singleton_log_normalization_static_verification_v1",
        "status": "PASS_SOURCE_STATIC_ONLY",
        "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "manifest_sha256": sha(manifest_bytes),
        "verifier_sha256": sha(Path(__file__).read_bytes()),
        "candidate_sha256": sha(source),
        "candidate_declarations": names,
        "source_binding_rows": len(review["source_bindings"]),
        "dedup_reference_rows": len(review["bounded_deduplication"]["relevant_reference_files"]),
        "distinct_published_current_file_pairs_verified": len(checked),
        "fixed_1106_cache_verified": True,
        "declaration_statement_proof_ranges_verified": True,
        "fixed_imports_verified": True,
        "forbidden_proof_tokens_absent": True,
        "contract_text_checks_only": True,
        "independent_review": review["independent_review"],
        "lean_run": False,
        "kernel_audit_run": False,
        "complete_source_or_native_closure_verified": False,
        "formal_acceptance_added": False,
    }
    RECEIPT.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(receipt, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
