#!/usr/bin/env python3
"""Receive the archived Part 2 rows [4,64) and cumulative-prefix acceptance.

Run this file from any working directory. It reads repository files and runs
only the unchanged, hash-bound Python P0 receiving check; it never invokes Lean,
Lake, leanchecker, a generator, or a network service, and writes no files.

The Python Fraction calculations below bind the frozen seven-field row stream,
the emitted exact data, and the bookkeeping. They are not integral proofs. The
actual integral claims require the separately archived strict trust-zero Lean
compilations, stock kernel replays, and complete owned-declaration audit. Nine
old production modules are reused with identical source bytes and identical
compiler records; only three new production modules are compiled and replayed.

The original prefix4 validator is intentionally unchanged: its nine-module
inventory is historical. This receiver checks its complete frozen evidence and
the recorded successful run before the append, then checks the twelve-module
inventory. Only four explicitly named parent tool files may have changed.
"""

from collections import Counter
from datetime import datetime, timedelta
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
OLD_REL = "verification/part2/round2/prefix4/receipt.json"
OLD_BASE = ROOT / "verification/part2/round2/prefix4"
UPSTREAM_BASE = ROOT / "verification/part2/round2/upstream"
SOURCE_REL = "verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json"
SOURCE_ORIGINAL = "verification/data/corpus-renewal-paired-certificate-v2-20261010.json"
SOURCE_COMMIT = "ba6ec11d800eccc54406490631895e174de85766"
PARENT_COMMIT = "076473720210ee602e6e9735902e16bb6c5f1398"
PARENT_TREE = "d09f102dd62aa91a93107bd8885435370f8e924e"
BASELINE = "1a80c1bcce67886f699d097fc37fd245cd3620bf"
STATUS = "PASS_STRICT_TRUST0_STOCK_REPLAY_OWNED_AUDIT"
PRODUCTION_PREFIX = "ImbalancedChen.Certificates."
NEW_MODULES = {
    PRODUCTION_PREFIX + "PairedV2Batch4To64Data",
    PRODUCTION_PREFIX + "PairedV2Batch4To64",
    PRODUCTION_PREFIX + "PairedV2Prefix64",
}
ALLOWED_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
ALLOWED_PARENT_CHANGES = {
    ".github/workflows/part2-certificates.yml",
    "verification/part2/CertificateAudit.lean",
    "verification/part2/check.sh",
    "verification/part2/generate_paired_prefix.py",
}
OLD_IDENTITY = {
    "bytes": 20623,
    "sha256": "a7eda6ca5d823aaa31e5ebce320f0fca802ab123cdd99a21ef0d7d692c677ca1",
    "git_blob_sha1": "c11ce176846530953f2a968e30e9da3b3f24dfa8",
}
FROZEN_RECEIVING_INPUTS = {
    "parent-source-identities.json": {
        "bytes": 101543,
        "sha256": "be33820d88143a0f2bcfc6b92e458eda7977b5c5bfc42bb254d6d3f7f95ddce0",
        "git_blob_sha1": "7ad803fadd96b5cf72cecf3aecd533e6509f8783",
    },
    "prefix4-before-mutation.json": {
        "bytes": 6207,
        "sha256": "6cdff3ee8a92f79ad68913241c2834bdd4b744e160bc4e67ccd7e2401210d9ef",
        "git_blob_sha1": "ec7ad85f1d74ef162866830421ce773c1729633d",
    },
    "prefix4-before-mutation.log": {
        "bytes": 273,
        "sha256": "bc4177ec5d8ba592adf23d5fe59b920d55f3733df7e987a8f0c68b01978ac578",
        "git_blob_sha1": "c48dff513f7c4e6c992be727721c008dc8b3d3e1",
    },
}
SOURCE_IDENTITY = {
    "bytes": 3604398,
    "sha256": "f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7",
    "git_blob_sha1": "49499697cca96de5f7b779e95077874ce5f9d119",
}
STREAM_IDENTITIES = {
    (0, 4): (457, "96df956686f3617d69cb0f72e510258991e7f21d10c36c635915f8cc0a573235"),
    (4, 64): (6930, "86c9f08228f08e98a9f1467fc353f1f01bdb5878e0d01e8a678debc664c661ab"),
    (0, 64): (7387, "f89caa496a9672c1dc9285a22f1e010008a0d6ea6e9ff850fb09747586afaaf9"),
}
FULL_STREAM_SHA256 = "027212a3415cd41c32b669318ef2eb313d240b59eb8260cde202365b1454cab0"
ROW_COLUMNS = ["group", "t_index", "u_index", "exact_Z", "discarded_floor_Q80",
               "extra_lower_Q160", "extra_upper_Q160"]
A, H, D, MU, K = Q(417, 5000), Q(19, 125), Q(59, 250), Q(25, 128), Q(8452171, 1250000)
DT, DU = (D - MU) / 512, (H - A) / 512
LOG_SCALE, CELL_SCALE = 10 ** 15, 10 ** 20


def require(condition, message):
    if not condition:
        raise ValueError(message)


def identity(path):
    raw = path.read_bytes()
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
            "git_blob_sha1": hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_object)


def local_path(base, relative):
    path = Path(relative)
    require(isinstance(relative, str) and not path.is_absolute()
            and relative != "" and ".." not in path.parts,
            "Invalid repository-relative path: " + str(relative))
    result = base / path
    require(result.resolve().is_relative_to(base.resolve()),
            "Path escapes its evidence directory: " + relative)
    return result


def identities(base, entries, required=()):
    require(isinstance(entries, dict) and set(required) <= set(entries),
            "Identity manifest omits required files: " + str(sorted(set(required) - set(entries))))
    for relative, expected in entries.items():
        require(identity(local_path(base, relative)) == expected,
                "File identity changed: " + str(base / relative))


def source_path(module):
    return module.replace(".", "/") + ".lean"


def load_source_scanner():
    # This repository helper is itself protected by the parent snapshot below.
    # Disable bytecode creation so a receiving check is a read-only operation.
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(ROOT))
    from verification.verify_variable_envelope_boxes import lean_code
    return lean_code


def direct_production_imports(module, lean_code):
    names = set()
    for line in lean_code((ROOT / source_path(module)).read_text()).splitlines():
        match = re.fullmatch(r"\s*import\s+(.+?)\s*", line)
        if match:
            names.update(x for x in match[1].split() if x.startswith(PRODUCTION_PREFIX))
    return names


def production_dependencies(module, entries, lean_code):
    result = set()
    pending = list(direct_production_imports(module, lean_code))
    while pending:
        name = pending.pop()
        require(name in entries and name != module, "Unknown or circular production import: " + name)
        if name not in result:
            result.add(name)
            pending.extend(direct_production_imports(name, lean_code))
    return result


def imported_bindings(receipt, entries, required_modules, target_module):
    local = receipt["local_producer_sha256_before"]
    require(isinstance(local, dict), "Missing local producer identities")
    for module in required_modules:
        suffix = "/" + module.replace(".", "/") + ".olean"
        found = [value for path, value in local.items() if path.endswith(suffix)]
        require(found == [entries[module]["object_sha256"]],
                "Gate imported an unaccepted producer: " + module)
    for key in ["local_producer_sha256_before", "shared_sha256_before"]:
        for path, value in receipt[key].items():
            for module, entry in entries.items():
                if module == target_module:
                    continue  # A pre-existing output is not an import of itself.
                if path.endswith("/" + entry["source"]):
                    require(value == entry["source_identity"]["sha256"],
                            "Gate shared source differs: " + module)
                if path.endswith("/" + module.replace(".", "/") + ".olean"):
                    require(value == entry["object_sha256"], "Gate producer object differs: " + module)


def gate(base, archive, entry, action, entries, required_imports, tool_hashes=None):
    item = entry[action]
    require(item["receipt"] in archive and item["log"] in archive,
            "Raw gate files are not hash-bound: " + entry["module"])
    receipt = read(local_path(base, item["receipt"]))
    lines = local_path(base, item["log"]).read_text().splitlines()
    require(lines and receipt["action"] == action and receipt["module"] == entry["module"],
            "Gate action/module mismatch")
    require(item["exit_code"] == receipt["returncode"] == 0
            and receipt["verification_passed"] is True and receipt["failures"] == [],
            "Unsuccessful execution receipt: " + item["receipt"])
    require(receipt["metadata_adapter"] is False, "Unexpected metadata adapter")
    require(receipt["environment"]["LEAN_NUM_THREADS"] == "1", "Thread setting changed")
    require(receipt["object_sha256_after"] == entry["object_sha256"], "Output object mismatch")
    require(Path(receipt["log"]).name == Path(item["log"]).name, "Wrong raw gate log")
    preamble = json.loads(lines[0], object_pairs_hook=unique_object)
    require(isinstance(preamble, dict) and preamble, "Missing raw gate preamble")
    for key, value in preamble.items():
        require(key in receipt and receipt[key] == value, "Log/receipt preamble mismatch: " + key)
    for key in ["source_sha256", "shared_sha256", "local_producer_sha256"]:
        require(receipt[key + "_before"] == receipt[key + "_after"],
                "Changed gate input: " + key)
    command = receipt["command"]
    if action == "compile":
        require(type(receipt["trustLevel"]) is int and receipt["trustLevel"] == 0
                and receipt["warningAsError"] is True, "Compile was not strict/trust-zero")
        require(receipt["source"].endswith("/" + entry["source"])
                and receipt["source_sha256_after"] == entry["source_identity"]["sha256"],
                "Compiled source does not match the accepted source")
        require("FRONTEND_OK module=" + entry["module"] + " trustLevel=0" in lines,
                "Missing successful stock frontend marker")
        require(Path(command[0]).name == "lake" and len(command) >= 8
                and command[-5] == "compileOne" and command[-4] == receipt["source"]
                and command[-3] == entry["module"] and command[-1] == "strict"
                and command[-2].endswith("/" + entry["module"].replace(".", "/") + ".olean"),
                "Unexpected strict frontend command")
    else:
        require(receipt["object_sha256_before"] == receipt["object_sha256_after"],
                "Replayed object changed")
        require(len(command) == 3 and Path(command[0]).name == "leanchecker"
                and command[1:] == ["--verbose", entry["module"]],
                "Unexpected stock kernel replay command")
        require("replaying " + entry["module"] in lines, "Missing selected-module kernel replay")
    imported_bindings(receipt, entries, required_imports, entry["module"])
    if tool_hashes is not None:
        shared = receipt["shared_sha256_before"]
        for executable, expected in tool_hashes.items():
            found = [value for path, value in shared.items() if path.endswith("/bin/" + executable)]
            require(found == [expected], "Pinned executable differs: " + executable)
    return receipt


def audit_records(base, report, entries, audit_gate):
    audit = report["audit"]
    lines = local_path(base, audit["compile"]["log"]).read_text().splitlines()
    records = [json.loads(line.removeprefix("P2_AUDIT_DECL "), object_pairs_hook=unique_object)
               for line in lines if line.startswith("P2_AUDIT_DECL ")]
    counts = [json.loads(line.removeprefix("P2_AUDIT_MODULE "), object_pairs_hook=unique_object)
              for line in lines if line.startswith("P2_AUDIT_MODULE ")]
    totals = [int(line.removeprefix("P2_AUDIT_COUNT "))
              for line in lines if line.startswith("P2_AUDIT_COUNT ")]
    require(records == read(base / "compiler-types.json"), "Compiler records differ from the raw audit")
    require(counts == audit["module_counts"] and totals == [len(records)], "Audit census mismatch")
    require(len(records) == audit["declaration_count"] == report["audit_all_owned_declaration_count"],
            "Incorrect owned-declaration total")
    require(len({r["name"] for r in records}) == len(records), "Duplicate audited declaration")
    require(len(counts) == len(entries) and {x["module"] for x in counts} == set(entries),
            "Audit module inventory is incomplete")
    counter = Counter(r["module"] for r in records)
    require(set(counter) == set(entries), "Audit contains an unexpected declaring module")
    for item in counts:
        require(counter[item["module"]] == item["count"] > 0, "Incorrect per-module declaration count")
    require(audit["declaring_module_inventory"] is True and audit["includes_private_and_generated"] is True
            and audit["unsafe_or_new_axiom_declarations"] == 0, "Owned-declaration audit scope changed")
    union = set()
    text = (base / "compiler-readable-types.txt").read_text()
    require("⋯" not in text, "Truncated readable-type artifact")
    for record in records:
        require(record["kind"] != "axiom" and set(record["axioms"]) <= ALLOWED_AXIOMS,
                "Forbidden axiom dependency: " + record["name"])
        union.update(record["axioms"])
        for field in ["type", "readable_type"]:
            require(isinstance(record[field], str) and record[field] and "⋯" not in record[field],
                    "Missing or truncated compiler type: " + record["name"])
        block = f"[{record['module']}]\n{record['name']} :\n{record['readable_type']}\n"
        require(block in text, "Readable artifact omits a complete compiler type: " + record["name"])
    require(union == set(audit["transitive_axiom_union"]) == ALLOWED_AXIOMS,
            "Incorrect transitive axiom union")
    imported_bindings(audit_gate, entries, set(entries), audit["module"])
    return records


def history(report, lean_code):
    identities(BASE, FROZEN_RECEIVING_INPUTS)
    require(identity(ROOT / OLD_REL) == OLD_IDENTITY, "Frozen prefix4 receipt changed")
    require(report["previous_acceptance"] == OLD_REL
            and report["previous_acceptance_identity"] == OLD_IDENTITY, "Wrong previous acceptance")
    scope = report["historical_scope"]
    require(scope["parent_commit"] == PARENT_COMMIT
            and scope["parent_sources"] == "parent-source-identities.json"
            and scope["pre_mutation_receipt"] == "prefix4-before-mutation.json"
            and scope["pre_mutation_log"] == "prefix4-before-mutation.log"
            and len(scope["allowed_changed_parent_paths"]) == 4
            and set(scope["allowed_changed_parent_paths"]) == ALLOWED_PARENT_CHANGES,
            "Historical source-scope declaration changed")
    snapshot = read(BASE / "parent-source-identities.json")
    require(snapshot["parent_commit"] == PARENT_COMMIT and snapshot["tree"] == PARENT_TREE
            and len(snapshot["files"]) == 424, "Incorrect parent source snapshot")
    changed = []
    for relative, expected in snapshot["files"].items():
        current = identity(local_path(ROOT, relative))
        if current != expected:
            require(relative in ALLOWED_PARENT_CHANGES, "Parent file was modified: " + relative)
            changed.append(relative)
    old_tree = {p for p in snapshot["files"] if p.startswith("verification/part2/round2/")}
    current_tree = {p.relative_to(ROOT).as_posix()
                    for p in (ROOT / "verification/part2/round2").rglob("*") if p.is_file()}
    require(current_tree == old_tree, "Historical round2 path inventory changed")
    previous = read(ROOT / OLD_REL)
    require(previous["status"] == STATUS and previous["fixed_proof_source_commit"]
            == "6acf61cc28f227a9154363f2347c386ec01dffb0", "Wrong historical proof acceptance")
    for relative, expected in previous["source_inputs"].items():
        require(snapshot["files"][relative] == expected, "Old source manifest differs from the parent snapshot")
    identities(OLD_BASE, previous["archive_files"])
    pre = read(BASE / "prefix4-before-mutation.json")
    require(pre["returncode"] == 0 and pre["new_lean_execution"] is False
            and pre["command"] == ["python3", "verification/part2/round2/prefix4/verify_acceptance.py"]
            and pre["parent_commit"] == PARENT_COMMIT and pre["parent_blob_count"] == 424
            and pre["old_receipt_identity"] == OLD_IDENTITY
            and pre["old_source_inputs"] == previous["source_inputs"], "Invalid pre-mutation acceptance")
    require(read(BASE / "prefix4-before-mutation.log") == {
        "status": "PASS_ARCHIVED_PREFIX4_ACCEPTANCE", "new_modules": 3,
        "reused_modules": 6, "all_owned_declarations": 309, "new_owned_declarations": 56,
        "actual_rows": [0, 1, 2, 3], "new_lean_compile_or_replay_in_this_receiving_check": False,
    }, "Pre-mutation receiving output changed")

    # This unchanged Python receiver checks every archived P0 raw log, gate
    # preamble, source/import hash, ledger entry and full compiler-type record.
    # It does not invoke Lean. Its file and every P0 artifact were just checked
    # against the fixed 424-file parent snapshot, independently of this call.
    result = subprocess.run(
        [sys.executable, "-B", str(UPSTREAM_BASE / "verify_upstream_acceptance.py"),
         "--repo-root", str(ROOT)], capture_output=True, text=True, check=False)
    require(result.returncode == 0, "Historical P0 receiving check failed: " + result.stderr.strip())
    upstream_status = json.loads(result.stdout, object_pairs_hook=unique_object)
    require(upstream_status["status"] == "PASS_EXACT_SOURCE_UPSTREAM_REUSE"
            and upstream_status["modules"] == 6 and upstream_status["declarations"] == 253
            and upstream_status["new_lean_compile_or_replay"] is False, "Unexpected P0 receiving result")
    upstream = read(UPSTREAM_BASE / "UPSTREAM_ACCEPTANCE.json")
    require(upstream["proof_source_commit"] == "278f949444748a30b5165ff47bfa283ab0bad0d8"
            and upstream["evidence_source_commit"] == "cce2334906f068fda2f58c400646366f2aa2d417",
            "Wrong P0 source/evidence commits")
    entries = {}
    for entry in upstream["modules"]:
        entries[entry["module"]] = {
            "module": entry["module"], "source": entry["path"],
            "source_identity": {"bytes": entry["bytes"], "sha256": entry["accepted_source_sha256"],
                                "git_blob_sha1": entry["accepted_git_blob_sha1"]},
            "object_sha256": entry["olean_sha256"],
        }
    for entry in previous["new_modules"]:
        require(entry["module"] not in entries, "Repeated historical module")
        entries[entry["module"]] = {k: entry[k] for k in
                                    ["module", "source", "source_identity", "object_sha256"]}
    require(len(entries) == 9 and set(entries) == set(previous["all_production_modules"]),
            "Expected exactly nine historical production modules")
    for entry in entries.values():
        require(entry["source"] == source_path(entry["module"])
                and identity(ROOT / entry["source"]) == entry["source_identity"],
                "Historical production source changed: " + entry["module"])
    for entry in previous["new_modules"]:
        dependencies = production_dependencies(entry["module"], entries, lean_code)
        gate(OLD_BASE, previous["archive_files"], entry, "compile", entries, dependencies)
        gate(OLD_BASE, previous["archive_files"], entry, "replay", entries, dependencies)
    old_audit = gate(OLD_BASE, previous["archive_files"], previous["audit"], "compile", entries, set(entries))
    records = audit_records(OLD_BASE, previous, entries, old_audit)
    require(len(records) == 309, "Historical 309-declaration coverage changed")
    by_name = {r["name"]: r for r in records}
    for batch in ["p2-first", "p2-coarse"]:
        require(all(by_name.get(r["name"]) == r
                    for r in read(UPSTREAM_BASE / batch / "compiler-types.json")),
                "Historical P0 compiler records differ from prefix4 audit")
    tool_hashes = {}
    for executable in ["lean", "lake", "leanchecker"]:
        values = [value for path, value in old_audit["shared_sha256_before"].items()
                  if path.endswith("/bin/" + executable)]
        require(len(values) == 1, "Historical pinned executable identity is ambiguous")
        tool_hashes[executable] = values[0]
    return previous, entries, records, tool_hashes, changed


def floor(q):
    return q.numerator // q.denominator


def ceil(q):
    return -((-q.numerator) // q.denominator)


def log_candidates(q, terms):
    require(q >= 1 and terms > 0, "Invalid rational log input")
    x = (q - 1) / (q + 1)
    lo = 2 * sum((x ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), Q(0))
    hi = lo + 2 * x ** (2 * terms + 1) / (1 - x * x)
    return Q(floor(lo * LOG_SCALE), LOG_SCALE), Q(ceil(hi * LOG_SCALE), LOG_SCALE)


def row_stream(rows):
    # Preserve all seven original fields, including the unused Q160 text.
    # The global source ordinal is not an eighth field in this stream.
    return "".join(",".join(map(str, row)) + "\n" for row in rows).encode("ascii")


def decode_row(ordinal, row):
    require(isinstance(row, list) and len(row) == 7, "Wrong row arity")
    group, i, j, ztext, lost, _stored_lo, _stored_hi = row
    require(group == "E0" and lost == "0", "Row is outside the adopted E0/floor-zero slice")
    require(type(i) is int and type(j) is int and 0 <= i < 512 and 0 <= j < 512,
            "Invalid integer grid index")
    tl, tr, ul, ur = MU + DT * i, MU + DT * (i + 1), A + DU * j, A + DU * (j + 1)
    z = Q(ztext)
    require(z == min(ul, 3 * (1 - tr - ur) / 13), "Exact cutoff differs from the frozen row")
    require(0 < A < z <= ul < ur <= H < tl < tr <= D, "E0 endpoint geometry failed")
    residual = Q(57, 64) - Q(5, 2) * tl - ul
    require(residual <= 2 * A, "E0 residual condition failed")
    log_t, log_u, log_z = log_candidates(tr / tl, 1), log_candidates(ur / ul, 1), log_candidates(z / A, 6)
    bracket_lo, bracket_hi = 1 / A - (1 + log_z[1]) / z, 1 / A - (1 + log_z[0]) / z
    require(0 <= log_t[0] <= log_t[1] and 0 <= log_u[0] <= log_u[1]
            and 0 <= bracket_lo <= bracket_hi, "Candidate product sign/order failed")
    raw_lo, raw_hi = K / 80 * log_t[0] * log_u[0] * bracket_lo, K / 80 * log_t[1] * log_u[1] * bracket_hi
    lo, hi = Q(floor(raw_lo * CELL_SCALE), CELL_SCALE), Q(ceil(raw_hi * CELL_SCALE), CELL_SCALE)
    decoded = {
        "original_ordinal": ordinal, "original_row": row, "group": "E0", "discarded_floor_Q80": 0,
        "t_index": i, "u_index": j, "tl": str(tl), "tr": str(tr), "ul": str(ul), "ur": str(ur), "Z": str(z),
        "cutoff": "min(ul,3*(1-tr-ur)/13)", "E0_residual": str(residual),
        "E0_residual_upper": str(2 * A), "geometry_check": True,
        "log_t": list(map(str, log_t)), "log_u": list(map(str, log_u)), "log_z": list(map(str, log_z)),
        "lower": str(lo), "upper": str(hi),
    }
    return decoded, raw_lo, raw_hi


def lean_rat(value):
    q = Q(value)
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator} / {q.denominator}"


def emitted_data(decoded, lower, upper, lean_code):
    """Independently bind every emitted rational definition to decoded rows.

    This is a complete token comparison for the data module, not an execution
    of the emitter. Lean's separate checks remain responsible for correctness
    of each certificate and its relation to the real integral.
    """
    namespace = "ImbalancedChen.Certificates.PairedV2.Batch4To64"
    lines = ["import ImbalancedChen.Certificates.PairedV2Data", "namespace " + namespace]

    def lookup(name, typ, values):
        lines.extend([f"def {name} (i : Fin 60) : {typ} :=", "match i.val with"])
        lines.extend(f"| {i} => {value}" for i, value in enumerate(values[:-1]))
        lines.append("| _ => " + values[-1])

    lookup("rowIndices", "ℕ × ℕ", [f"({r['t_index']}, {r['u_index']})" for r in decoded])
    lookup("rowZ", "ℚ", [lean_rat(r["Z"]) for r in decoded])
    lines.extend(["def rowOrdinal (i : Fin 60) : ℕ := 4 + i.val", "def start : ℕ := 4",
                  "def count : ℕ := 60", "def endOrdinal : ℕ := 64",
                  'def rowGroup (_ : Fin 60) : String := "E0"',
                  "def rowDiscardedFloorQ80 (_ : Fin 60) : ℕ := 0"])
    for row in decoded:
        n, i, j = row["original_ordinal"], row["t_index"], row["u_index"]
        lines.extend([f"def certificate{n:04d} : PairedIntegralCertificate where", "K := K", "a := a",
                      f"tl := tLower {i}", f"tr := tUpper {i}", f"ul := uLower {j}",
                      f"ur := uUpper {j}", "Z := " + lean_rat(row["Z"])])
        for label, q, terms, bounds in [
            ("T", Q(row["tr"]) / Q(row["tl"]), 1, row["log_t"]),
            ("U", Q(row["ur"]) / Q(row["ul"]), 1, row["log_u"]),
            ("Z", Q(row["Z"]) / A, 6, row["log_z"]),
        ]:
            lines.extend(["log" + label + " :=", "{ argument := " + lean_rat(q),
                          f"terms := {terms}", "lower := " + lean_rat(bounds[0]),
                          "upper := " + lean_rat(bounds[1]) + " }"])
        lines.extend(["lower := " + lean_rat(row["lower"]), "upper := " + lean_rat(row["upper"])])
    lookup("certificates", "PairedIntegralCertificate",
           [f"certificate{r['original_ordinal']:04d}" for r in decoded])
    lines.extend(["def lowerBound : ℚ := " + lean_rat(lower), "def upperBound : ℚ := " + lean_rat(upper),
                  "end " + namespace])
    text = (ROOT / "ImbalancedChen/Certificates/PairedV2Batch4To64Data.lean").read_text()
    require(lean_code(text).split() == lean_code("\n".join(lines)).split(),
            "Emitted data tokens do not match the sixty decoded source rows")
    # lean_code removes strings as well as comments; bind the one data string
    # separately so even a changed group label cannot hide in that removal.
    require(re.findall(r'def\s+rowGroup\s*\(_\s*:\s*Fin\s+60\)\s*:\s*String\s*:=\s*"([^"]*)"', text)
            == ["E0"], "Emitted row group differs from E0")


def data_and_ledger(previous, lean_code):
    require(identity(ROOT / SOURCE_REL) == SOURCE_IDENTITY, "Frozen raw CRLF certificate changed")
    raw = (ROOT / SOURCE_REL).read_bytes()
    require(raw.count(b"\r\n") == 158321 and b"\n" not in raw.replace(b"\r\n", b"")
            and b"\r" not in raw.replace(b"\r\n", b""), "Source newline protocol changed")
    source = read(ROOT / SOURCE_REL)
    require(source["row_columns"] == ROW_COLUMNS and len(source["rows"]) == 17572
            and source["omega_argument_threshold"] == "7/3" and source["omega_lower"] == "11/20"
            and Q(source["K"]) == K, "Frozen certificate field semantics changed")
    rows = source["rows"]
    require(hashlib.sha256(row_stream(rows)).hexdigest() == source["row_stream_sha256"] == FULL_STREAM_SHA256,
            "Full original seven-field LF stream differs")
    streams = {}
    for bounds, expected in STREAM_IDENTITIES.items():
        stream = row_stream(rows[bounds[0]:bounds[1]])
        require((len(stream), hashlib.sha256(stream).hexdigest()) == expected,
                "Original range LF stream differs: " + str(bounds))
        streams[bounds] = stream
    require(streams[(0, 4)] + streams[(4, 64)] == streams[(0, 64)], "Append stream is not an exact concatenation")
    prefix_indices = {(r[1], r[2]) for r in rows[:4]}
    batch_indices = {(r[1], r[2]) for r in rows[4:64]}
    total_indices = {(r[1], r[2]) for r in rows[:64]}
    require(len(prefix_indices) == 4 and len(batch_indices) == 60 and len(total_indices) == 64
            and not prefix_indices & batch_indices and prefix_indices | batch_indices == total_indices,
            "Old/new actual grid indices overlap or are duplicated")
    decoded_all = [decode_row(n, rows[n]) for n in range(64)]
    decoded = [x[0] for x in decoded_all[4:64]]
    generated = read(BASE / "generated-report.json")
    require(generated["source_commit"] == SOURCE_COMMIT and generated["source_path"] == SOURCE_ORIGINAL
            and generated["source_sha256"] == SOURCE_IDENTITY["sha256"]
            and generated["source_git_blob"] == SOURCE_IDENTITY["git_blob_sha1"], "Wrong generated source identity")
    require(generated["start"] == 4 and generated["count"] == 60 and generated["end"] == 64
            and generated["original_ordinals"] == list(range(4, 64))
            and generated["original_rows"] == rows[4:64] and generated["decoded_rows"] == decoded,
            "Generated range, original ordinals, fields or exact decoded coordinates differ")
    require(generated["prefix_row_stream_sha256"] == generated["row_stream_sha256"] == STREAM_IDENTITIES[(4, 64)][1]
            and generated["source_file_newlines"] == "CRLF" and generated["row_stream_newlines"] == "LF"
            and generated["coordinate_order"] == ["t", "u", "z", "w"]
            and generated["group"] == "E0" and generated["discarded_Q80_sum"] == 0,
            "Generated row-stream/coordinate/group semantics differ")
    require(generated["log_scale"] == LOG_SCALE and generated["cell_scale"] == CELL_SCALE
            and generated["candidate_lean_status"] == "REQUIRES_SEPARATE_STRICT_COMPILE_KERNEL_REPLAY_AND_AUDIT",
            "Generator candidate status or rounding scales were changed")
    require(set(generated["generated_sha256"]) == {"PairedV2Batch4To64Data.lean", "PairedV2Batch4To64.lean"},
            "Wrong generated module inventory")
    for filename, expected in generated["generated_sha256"].items():
        require(identity(ROOT / "ImbalancedChen/Certificates" / filename)["sha256"] == expected,
                "Generated source hash mismatch: " + filename)
    lower = sum((Q(row["lower"]) for row in decoded), Q(0))
    upper = sum((Q(row["upper"]) for row in decoded), Q(0))
    require(Q(generated["candidate_lower"]) == lower and Q(generated["candidate_upper"]) == upper,
            "Generated range candidate sum differs")
    emitted_data(decoded, lower, upper, lean_code)
    old_generated = read(OLD_BASE / "generated-report.json")
    require(old_generated["original_ordinals"] == list(range(4)) and old_generated["original_rows"] == rows[:4]
            and old_generated["prefix_row_stream_sha256"] == STREAM_IDENTITIES[(0, 4)][1],
            "Accepted first-four source slice differs")
    old_lower = sum((Q(x[0]["lower"]) for x in decoded_all[:4]), Q(0))
    old_upper = sum((Q(x[0]["upper"]) for x in decoded_all[:4]), Q(0))
    require(old_lower == Q(previous["scope"]["lower"]) == Q(old_generated["candidate_lower"])
            and old_upper == Q(previous["scope"]["upper"]) == Q(old_generated["candidate_upper"]),
            "Previously accepted four-row endpoints changed")
    ledger = read(BASE / "append-ledger.json")
    require(ledger["source_commit"] == SOURCE_COMMIT and ledger["source_sha256"] == SOURCE_IDENTITY["sha256"]
            and ledger["source_git_blob"] == SOURCE_IDENTITY["git_blob_sha1"]
            and ledger["source_bytes"] == SOURCE_IDENTITY["bytes"], "Append ledger source identity differs")
    ranges = [{"start": start, "count": end - start, "end": end,
               "row_stream_sha256": digest, "row_stream_bytes": size}
              for (start, end), (size, digest) in STREAM_IDENTITIES.items()]
    require(ledger["ranges"] == ranges and ledger["original_indices"] == [[n, r[1], r[2]] for n, r in enumerate(rows[:64])]
            and ledger["indices_no_duplicates"] is True and ledger["ranges_disjoint"] is True
            and ledger["concatenated_stream_equals_prefix64"] is True, "Append ledger range/index coverage differs")
    for key, lo, hi in [("prefix4", old_lower, old_upper), ("new_batch", lower, upper),
                        ("prefix64", old_lower + lower, old_upper + upper)]:
        require({name: Q(value) for name, value in ledger[key].items()}
                == {"lower": lo, "upper": hi, "width": hi - lo}, "Append ledger bound differs: " + key)
    prefix_source = lean_code((ROOT / "ImbalancedChen/Certificates/PairedV2Prefix64.lean").read_text())
    for name, expected in [("lowerBound", old_lower + lower), ("upperBound", old_upper + upper)]:
        literals = re.findall(r"(?m)^def\s+" + name + r"\s*:\s*ℚ\s*:=\s*([0-9]+)\s*/\s*([0-9]+)\s*$",
                              prefix_source)
        require(len(literals) == 1 and Q(int(literals[0][0]), int(literals[0][1])) == expected,
                "Cumulative Lean bound does not equal the exact accepted append: " + name)
    raw_width = sum((hi - lo for _, lo, hi in decoded_all[4:64]), Q(0))
    lower_rounding = sum((lo - Q(row["lower"]) for row, lo, _ in decoded_all[4:64]), Q(0))
    upper_rounding = sum((Q(row["upper"]) - hi for row, _, hi in decoded_all[4:64]), Q(0))
    errors = ledger["new_batch_error_accounting"]
    for key, expected in [("unrounded_enclosure_width", raw_width),
                          ("lower_outward_rounding_total", lower_rounding),
                          ("upper_outward_rounding_total", upper_rounding),
                          ("total_width", upper - lower),
                          ("per_side_rounding_total_strict_upper", Q(60, CELL_SCALE))]:
        require(Q(errors[key]) == expected, "New-batch rational error accounting differs: " + key)
    require(0 <= lower_rounding < Q(60, CELL_SCALE) and 0 <= upper_rounding < Q(60, CELL_SCALE)
            and raw_width + lower_rounding + upper_rounding == upper - lower,
            "Outward rounding/error identity failed")
    require(ledger["stored_Q160_endpoints_used_as_proof_hypotheses"] is False
            and ledger["geometric_union_disjointness_claimed"] is False
            and ledger["default_prefix4_regenerated_as_new_proof"] is False
            and ledger["log_terms"] == {"t": 1, "u": 1, "Z_over_a": 6}
            and ledger["outward_log_scale"] == LOG_SCALE and ledger["outward_cell_scale"] == CELL_SCALE,
            "Append ledger proof/rounding scope changed")
    return lower, upper, old_lower + lower, old_upper + upper


def serial_execution_receipts(report):
    """Check that only the final, serial production runs enter acceptance."""
    require("scheduling-rejections.json" in report["archive_files"],
            "Missing the preserved scheduling-rejection record")
    excluded = set(read(BASE / "scheduling-rejections.json")["excluded_receipt_stems"])
    runs = []
    for entry in report["new_modules"] + [report["audit"]]:
        actions = ["compile", "replay"] if entry in report["new_modules"] else ["compile"]
        for action in actions:
            relative = entry[action]["receipt"]
            require(Path(relative).stem not in excluded, "A rejected scheduling attempt was accepted")
            receipt = read(BASE / relative)
            start = datetime.strptime(receipt["started_utc"], "%Y%m%dT%H%M%S%fZ")
            end = start + timedelta(seconds=receipt["elapsed_seconds"])
            runs.append((start, end, entry["module"], action))
    runs.sort()
    require(len(runs) == 7, "Wrong final serial execution count")
    require(all(left[1] <= right[0] for left, right in zip(runs, runs[1:])),
            "Accepted execution time intervals overlap")
    require(runs[-1][2:] == ("verification.part2.CertificateAudit", "compile"),
            "The complete declaration audit must follow the production gates")


def main():
    report = read(BASE / "receipt.json")
    require(report["status"] == STATUS, "Acceptance is not complete")
    require(report["parent_branch_commit"] == PARENT_COMMIT
            and report["proof_common_baseline"] == BASELINE and report["manuscript_commit"] == SOURCE_COMMIT,
            "Wrong fixed parent/baseline/manuscript")
    # Protect the source scanner before importing it. The complete snapshot is
    # checked again by history(), including all frozen runtime/checker files.
    identities(BASE, FROZEN_RECEIVING_INPUTS)
    snapshot = read(BASE / "parent-source-identities.json")
    scanner = "verification/verify_variable_envelope_boxes.py"
    require(identity(ROOT / scanner) == snapshot["files"][scanner], "Source scanner changed")
    lean_code = load_source_scanner()
    previous, old_entries, old_records, tool_hashes, changed = history(report, lean_code)
    required_sources = set(previous["source_inputs"]) | {source_path(m) for m in NEW_MODULES} | {
        scanner, str(Path(__file__).resolve().relative_to(ROOT)),
    }
    runtime = ROOT / "verification/part2/round3/runtime"
    require(runtime.is_dir(), "The new runtime evidence has not been archived")
    runtime_files = {p.relative_to(ROOT).as_posix() for p in runtime.rglob("*") if p.is_file()}
    require(runtime_files, "The new runtime archive is empty")
    identities(ROOT, report["source_inputs"], required_sources | runtime_files)
    required_archive = set(FROZEN_RECEIVING_INPUTS) | {
        "generated-report.json", "append-ledger.json", "compiler-types.json", "compiler-readable-types.txt",
    }
    identities(BASE, report["archive_files"], required_archive)
    modules = report["all_production_modules"]
    actual_sources = {p.with_suffix("").relative_to(ROOT).as_posix().replace("/", ".")
                      for p in (ROOT / "ImbalancedChen/Certificates").rglob("*.lean")}
    require(len(modules) == 12 and set(modules) == actual_sources == set(old_entries) | NEW_MODULES,
            "Production inventory is not exactly the old nine plus the new three")
    for module in modules:
        code = lean_code((ROOT / source_path(module)).read_text())
        require(not re.search(r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide)\b|\bdebug\.skipKernelTC\b", code),
                "Forbidden proof escape: " + module)
    reused = report["reused_modules"]
    require(len(reused) == 9 and {x["module"] for x in reused} == set(old_entries), "Incorrect reused-module inventory")
    for entry in reused:
        require({key: entry[key] for key in ["module", "source", "source_identity", "object_sha256"]}
                == old_entries[entry["module"]], "Reused source/object binding changed: " + entry["module"])
    require(len(report["new_modules"]) == 3
            and {x["module"] for x in report["new_modules"]} == NEW_MODULES, "Incorrect new-module inventory")
    entries = dict(old_entries)
    for entry in report["new_modules"]:
        require(entry["source"] == source_path(entry["module"])
                and identity(ROOT / entry["source"]) == entry["source_identity"], "New source identity mismatch")
        require(re.fullmatch(r"[0-9a-f]{64}", entry["object_sha256"]), "Missing new object digest")
        entries[entry["module"]] = entry
    for entry in report["new_modules"]:
        dependencies = production_dependencies(entry["module"], entries, lean_code)
        gate(BASE, report["archive_files"], entry, "compile", entries, dependencies, tool_hashes)
        gate(BASE, report["archive_files"], entry, "replay", entries, dependencies, tool_hashes)
    audit = report["audit"]
    require(audit["source"] == "verification/part2/CertificateAudit.lean"
            and identity(ROOT / audit["source"]) == audit["source_identity"], "New audit source identity mismatch")
    new_audit_gate = gate(BASE, report["archive_files"], audit, "compile", entries, set(entries), tool_hashes)
    serial_execution_receipts(report)
    records = audit_records(BASE, report, entries, new_audit_gate)
    by_name = {record["name"]: record for record in records}
    old_names = {record["name"] for record in old_records}
    require({r["name"] for r in records if r["module"] in old_entries} == old_names
            and all(by_name.get(record["name"]) == record for record in old_records),
            "One of the historical 309 complete compiler records changed")
    new_count = sum(r["module"] in NEW_MODULES for r in records)
    require(len(records) == 309 + new_count and report["new_owned_declaration_count"] == new_count
            and report["new_strict_compile_count"] == report["new_stock_kernel_replay_count"] == 3
            and report["reused_module_count"] == 9, "Wrong new/reused gate or declaration counts")
    theorem_names = {
        "Batch4To64": ["certificates_checked", "geometry_checked", "certificate_inputs",
                       "rowIntegral_eq_certificate", "rowIntegral_bounds", "integral_semantics", "integral_bounds"],
        "Prefix64": ["source_ranges_disjoint", "source_ordinal_coverage", "rowIndices_injective",
                     "prefix_batch_indices_disjoint", "geometry_checked", "integral_eq_parts",
                     "integral_semantics", "lowerBound_eq_sum", "upperBound_eq_sum", "integral_bounds"],
    }
    for namespace, names in theorem_names.items():
        for name in names:
            full = "ImbalancedChen.Certificates.PairedV2." + namespace + "." + name
            require(full in by_name and by_name[full]["kind"] == "theorem", "Missing actual-object theorem: " + full)
    bounds = data_and_ledger(previous, lean_code)
    scope = report["scope"]
    require(scope["previous_zero_based_ordinals"] == list(range(4))
            and scope["original_zero_based_ordinals"] == list(range(4, 64))
            and scope["cumulative_zero_based_ordinals"] == list(range(64)) and scope["group"] == "E0"
            and (scope["start"], scope["count"], scope["end"]) == (4, 60, 64),
            "Acceptance scope is not the exact appended original ranges")
    require(tuple(Q(scope[key]) for key in ["lower", "upper", "cumulative_lower", "cumulative_upper"]) == bounds,
            "Accepted numerical bounds differ from the bound source data and exact append ledger")
    require(scope["global_union_integral_identity"] is False and scope["arithmetic_parent_license"] is False
            and scope["original_Q160_enclosures_used_as_proof_premises"] is False
            and scope["first_cell_added_again"] is False,
            "Acceptance exceeds the actual finite-integral-sum scope")
    for key in ["metadata_adapter", "full_lake_build", "full_historical_mask_certified", "hLower_supplier", "hUpper_supplier"]:
        require(report[key] is False, "Unsupported stronger validation/semantic claim: " + key)
    # Re-read every current source after the gate/type/data checks, catching a
    # concurrent change instead of reporting an acceptance for mixed revisions.
    identities(ROOT, report["source_inputs"], required_sources | runtime_files)
    print(json.dumps({
        "status": "PASS_ARCHIVED_BATCH4_TO64_ACCEPTANCE", "new_modules": 3, "reused_modules": 9,
        "all_owned_declarations": len(records), "new_owned_declarations": new_count,
        "unchanged_historical_compiler_records": 309, "previous_rows": [0, 4],
        "new_rows": [4, 64], "cumulative_rows": [0, 64], "range_convention": "half-open original ordinals",
        "actual_unique_grid_indices": {"previous": 4, "new": 60, "cumulative": 64},
        "changed_parent_tool_paths": sorted(changed),
        "python_data_and_error_accounting_is_not_an_integral_proof": True,
        "new_lean_compile_or_replay_in_this_receiving_check": False,
    }, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        raise SystemExit("FAIL_ARCHIVED_BATCH4_TO64_ACCEPTANCE: " + str(error)) from error
