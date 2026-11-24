#!/usr/bin/env python3
"""Factor the exact original Full87 integral definition closure for Winner9.

This is source movement, not a new interpretation of the 87-cell alphabet.
Every selected declaration is copied from a pinned Git blob, retaining its
namespace, type and body.  CRLF is normalized to LF.  The generated refactor
patch removes those declarations from their former modules and imports the
new core, so the same names must never be loaded from both locations.

Default output is explicitly source-only.  --check checks reproducibility;
neither operation invokes Lean or grants any formal verification credit.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = "8fdeb981e9cd29d336adb811f9558081e2ae9be8"
ARCHIVE = "docs/source-only/20261124-p2-winner9-original-full87"
DEFAULT_OUT = ROOT / ARCHIVE
HISTORY = "docs/source-only/20261102-resume-30r/full87_source_history/"
GAIN = "docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/"
REFERENCE_BLOBS = {
    "P4AOriginalFull87StrictActionTrim": {
        "blob": "c815fd9a9adf51ba1e84bcf38354126084690f56",
        "commit": "be2efd01c561080672e6c0ad0ba21638837afe4c",
        "path": "docs/source-only/20261103-full87-finite-eighth/P4AOriginalFull87StrictActionTrim.lean",
    },
    "P4AOriginalFull87EighthKernelControl": {
        "blob": "9c463af5937bd4c15ea95239d10470de5089b380",
        "commit": "be2efd01c561080672e6c0ad0ba21638837afe4c",
        "path": "docs/source-only/20261104-full87-eighth-kernel/P4AOriginalFull87EighthKernelControl.lean",
    },
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def source_path(name: str) -> str:
    if name in REFERENCE_BLOBS:
        return REFERENCE_BLOBS[name]["path"]
    if name in {
        "P4AOriginalAscendingFourteenAffineSource", "P4AOriginalSeed7Unequal15Literal",
        "P4AOriginalFirstFailureH5H7Literal", "P4AOriginalRemainingEighthSources",
        "P4AOriginalFull87SourceDictionary",
    }:
        return HISTORY + name + ".lean"
    if name == "P4AOriginalFirstFailureH3Literal":
        return "docs/source-only/20261102-resume-30p/adopted87_policy/" + name + ".lean"
    if name == "P4AOriginalFull87SourcePrimeTests":
        return GAIN + name + ".lean"
    return "ImbalancedChen/" + name + ".lean"


def source_bytes(name: str) -> bytes:
    if name in REFERENCE_BLOBS:
        raw = (DEFAULT_OUT / "reference-blobs" / (name + ".lean.txt")).read_bytes()
        assert blob_sha(raw) == REFERENCE_BLOBS[name]["blob"], name
        return raw
    return subprocess.check_output(["git", "show", BASE + ":" + source_path(name)], cwd=ROOT)


def extract(text: str, name: str) -> tuple[str, int, int]:
    """Selected declarations have column-zero commands and indented bodies."""
    pattern = re.compile(r"^(?:def|abbrev|inductive) " + re.escape(name) + r"(?=[\s:(])", re.M)
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise ValueError(f"expected exactly one declaration {name}, found {len(matches)}")
    start = matches[0].start()
    next_command = re.search(
        r"\n(?=(?:def |abbrev |inductive |structure |theorem |private |instance |"
        r"set_option |namespace |end(?:\s|$)|/--|/-!|--|@\[))", text[matches[0].end():]
    )
    stop = matches[0].end() + next_command.start() if next_command else len(text)
    return text[start:stop].rstrip() + "\n", start, stop


# (new module, imports, [(old namespace/module, names, required open commands)])
SPECS = [
    ("OriginalDescendingFifteenRowDefinitions", ["Mathlib.Data.Fin.VecNotation", "Mathlib.Tactic"], [
        ("OriginalDescendingFifteenLiteralAffineRows",
         ["evaluateCoefficients", "literalPool", "literalIndex", "exportedCoefficients", "StrictExportedRows"], []),
    ]),
    ("OriginalAscendingThirteenRowDefinitions", ["ImbalancedChen.OriginalDescendingFifteenRowDefinitions"], [
        ("OriginalAscendingThirteenLiteralAffineRows",
         ["literalPool", "literalIndex", "exportedCoefficients", "StrictExportedRows"],
         ["open OriginalDescendingFifteenLiteralAffineRows"]),
    ]),
    ("P2OriginalDescendingEighthCapDefinitions", ["ImbalancedChen.VariableEnvelope", "Mathlib.Data.Fin.VecNotation"], [
        ("P2OriginalDescendingEighthLogSemantics",
         ["Point", "eta", "d", "selectedSum", "oldRaw", "newCap"], ["open VariableEnvelope"]),
    ]),
    ("P2OriginalThirdMinorantCapDefinitions", ["ImbalancedChen.VariableEnvelope", "Mathlib.Data.Fin.VecNotation"], [
        ("P2OriginalThirdMinorantLogDictionary",
         ["Point", "eta", "comparisonCap", "selectedSum", "newCap"], ["open VariableEnvelope"]),
    ]),
    ("P4AOriginalAscendingFourteenSourceDefinitions", ["Mathlib.Data.Fin.VecNotation", "Mathlib.Tactic"], [
        ("P4AOriginalAscendingFourteenAffineSource", ["literalPool", "literalIndex", "rows"], []),
    ]),
    ("P4AOriginalSeed7Unequal15SourceDefinitions", ["Mathlib.Data.Fin.VecNotation", "Mathlib.Tactic"], [
        ("P4AOriginalSeed7Unequal15Literal", ["seed7Rows", "nineRows", "fiftyAscRows", "fiftyDescRows"], []),
    ]),
    ("P4AOriginalH5H7SourceDefinitions", ["Mathlib.Data.Fin.VecNotation", "Mathlib.Tactic"], [
        ("P4AOriginalFirstFailureH5H7Literal", ["h5AffineRows", "h7AffineRows"], []),
    ]),
    ("P4AOriginalH3SourceDefinitions", ["Mathlib.Data.Fin.VecNotation", "Mathlib.Tactic"], [
        ("P4AOriginalFirstFailureH3Literal",
         ["Point", "eta", "A", "R6", "M8", "sourceAffineRows", "evalAffine", "sourceAffineGuard"], []),
    ]),
    ("P4AOriginalRemainingEighthSourceDefinitions", [
        "ImbalancedChen.VariableEnvelope",
        "ImbalancedChen.P4AOriginalAscendingFourteenSourceDefinitions",
        "ImbalancedChen.P4AOriginalSeed7Unequal15SourceDefinitions",
        "ImbalancedChen.P4AOriginalH5H7SourceDefinitions",
    ], [
        ("P4AOriginalRemainingEighthSources",
         ["Point", "Cell", "rowCount", "row", "evalRow", "Source", "selected", "selectedSum",
          "eta", "comparison", "descendingNew", "newCap"], ["open VariableEnvelope"]),
    ]),
    ("P4AOriginalFull87SourceDefinitions", [
        "ImbalancedChen.P4AOriginalRemainingEighthSourceDefinitions",
        "ImbalancedChen.OriginalDescendingFifteenRowDefinitions",
        "ImbalancedChen.OriginalAscendingThirteenRowDefinitions",
        "ImbalancedChen.P2OriginalDescendingEighthCapDefinitions",
        "ImbalancedChen.P2OriginalThirdMinorantCapDefinitions",
        "ImbalancedChen.P4AOriginalH3SourceDefinitions",
    ], [
        ("P4AOriginalFull87SourceDictionary", ["Point", "Cell", "Source", "newCap", "comparison"], []),
        ("P4AOriginalFull87StrictActionTrim", ["rowCount", "rowValue", "sourceSet"],
         ["open P4AOriginalFull87SourceDictionary"]),
    ]),
    ("P4AOriginalFull87IntegralDefinitions", [
        "ImbalancedChen.P4AOriginalFull87SourceDefinitions",
        "Mathlib.MeasureTheory.Integral.Bochner.Set",
        "Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar",
    ], [
        ("P4AOriginalFull87EighthKernelControl", ["total", "product", "residual", "kernel"],
         ["open P4AOriginalFull87SourceDictionary"]),
        ("P4AOriginalFull87SourcePrimeTests", ["cellIntegral"],
         ["open Set MeasureTheory P4AOriginalFull87SourceDictionary",
          "open P4AOriginalFull87StrictActionTrim P4AOriginalFull87EighthKernelControl"]),
    ]),
]


def namespace(name: str) -> str:
    if name == "P2OriginalThirdMinorantLogDictionary":
        return "ImbalancedChen.P2OriginalThirdMinorantLogDictionarySourceOnly"
    return "ImbalancedChen." + name


def render() -> dict[str, str]:
    files: dict[str, str] = {}
    sources: dict[str, tuple[bytes, str]] = {}
    removals: dict[str, list[tuple[int, int, str, str]]] = {}
    receipt: dict = {
        "baseline": BASE,
        "status": "SOURCE_ONLY_NOT_COMPILED",
        "purpose": "exact original Full87 definition closure, preserving all 87 cell families",
        "normalization": "CRLF to LF; trailing blank lines removed from extracted declarations; no Lean token changes",
        "same_names_must_have_one_owner": True,
        "declarations": [],
        "modules": [],
    }
    for module, imports, groups in SPECS:
        out = "".join("import " + x + "\n" for x in imports)
        out += ("\n/-! SOURCE ONLY / NOT COMPILED. Mechanical extraction of existing declarations.\n"
                "See ../docs/source-only/20261124-p2-winner9-original-full87/DEFINITION_RECEIPT.json.\n"
                "Names, types and bodies are retained. Original modules must import this core\n"
                "and remove these declarations using the accompanying refactor patch. -/\n")
        for old, names, opens in groups:
            if old not in sources:
                raw = source_bytes(old)
                sources[old] = raw, raw.decode().replace("\r\n", "\n")
            raw, text = sources[old]
            ns = namespace(old)
            out += f"\nnamespace {ns}\nnoncomputable section\nopen scoped Classical BigOperators\n"
            out += "".join(x + "\n" for x in opens) + "\n"
            for name in names:
                decl, start, stop = extract(text, name)
                assert decl.strip() == text[start:stop].strip()
                out += decl + "\n"
                separator = ("where" if decl.startswith("inductive ") else
                             ":=" if ":=" in decl else "\n  |")
                declaration_head, declaration_body = decl.split(separator, 1)
                record = {
                    "name": ns + "." + name,
                    "namespace": ns,
                    "open_commands": opens,
                    "scopes": ["Classical", "BigOperators"],
                    "source_path": source_path(old),
                    "source_commit": REFERENCE_BLOBS.get(old, {}).get("commit", BASE),
                    "source_blob": blob_sha(raw),
                    "source_sha256": sha256(raw),
                    "source_first_line": text[:start].count("\n") + 1,
                    "source_last_line": text[:start + len(decl.rstrip())].count("\n") + 1,
                    "normalized_declaration_sha256": sha256(decl.encode()),
                    "declaration_head": declaration_head.rstrip(),
                    "declaration_head_sha256": sha256(declaration_head.encode()),
                    "declaration_body_sha256": sha256(declaration_body.encode()),
                    "body_separator": separator,
                    "target_module": "ImbalancedChen." + module,
                    "type_and_body_copied_verbatim": True,
                }
                receipt["declarations"].append(record)
                removals.setdefault(old, []).append((start, stop, module, name))
            out += f"end\nend {ns}\n"
        path = "ImbalancedChen/" + module + ".lean"
        files[path] = out
        receipt["modules"].append({"path": path, "sha256": sha256(out.encode()), "imports": imports})

    patch: list[str] = []
    refactors: list[dict] = []
    for old, chunks in sorted(removals.items()):
        raw, original = sources[old]
        modified = original
        for start, stop, _, _ in sorted(chunks, reverse=True):
            modified = modified[:start] + modified[stop:]
        imports = sorted({"import ImbalancedChen." + chunk[2] for chunk in chunks})
        modified = "\n".join(imports) + "\n" + modified
        path = source_path(old)
        patch.extend(difflib.unified_diff(original.splitlines(True), modified.splitlines(True),
                     fromfile="a/" + path, tofile="b/" + path))
        refactors.append({"path": path, "source_blob": blob_sha(raw),
                          "normalized_refactored_sha256": sha256(modified.encode()),
                          "removed_declarations": [namespace(old) + "." + c[3] for c in chunks],
                          "new_imports": imports,
                          "active_at_baseline": path.startswith("ImbalancedChen/")})
        if path.startswith("ImbalancedChen/"):
            files["refactored/" + path] = modified

    receipt["refactors"] = refactors
    receipt["declaration_count"] = len(receipt["declarations"])
    files["DEFINITION_RECEIPT.json"] = json.dumps(receipt, ensure_ascii=False, indent=2) + "\n"
    files["original-modules-refactor.patch"] = "".join(patch)
    return files


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    files = render()
    for relative, contents in files.items():
        path = args.output_dir / relative
        if args.check:
            if not path.is_file() or path.read_bytes() != contents.encode():
                raise SystemExit("different or missing generated source: " + str(path))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents.encode())
    print(json.dumps({"mode": "checked" if args.check else "wrote", "files": len(files),
                      "declarations": len(json.loads(files["DEFINITION_RECEIPT.json"])["declarations"]),
                      "formal_credit": False}))


if __name__ == "__main__":
    main()
