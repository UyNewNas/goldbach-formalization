"""Instantiate existing field proofs at the immutable Cell01 typed candidate.

This generator supplies ordinary Lean source, never a correctness certificate.
It reads the already published Lean candidate, preserving its exact raw nodes.
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
import re

PACKAGE = Path(__file__).resolve().parent
REPO = PACKAGE.parents[2]
BASE = Path("docs/source-only/20261126-p2-5-cell01-parser-typed")
INPUT_PINS = {
    str(BASE / "ImbalancedChen/P2Saving16Cell01TypedPayload.lean"):
        "1ddf5f99c579ef2fedcf197c7b7a5f642262e905a1ad9bdec2b6f44229cc9d99",
    str(BASE / "TYPED_PAYLOAD_MANIFEST.json"):
        "d125e382cfe99b1cb8359e6ed556fa695b3e800894b1a796bcd69c4448239d48",
    "ImbalancedChen/P2Saving16Cell00FieldBase.lean":
        "d25a0ddf04a1f56729160274a4bcd8bb306a66018e27d7574b0817df3120f50c",
    "docs/source-only/20261126-p2-5-cell00-field-symbolic/ImbalancedChen/P2Saving16Cell00FieldDecode.lean":
        "ad5e8f4f534dd8d23ea6e181e2323b5d11c935affdd76c4d8b64a937aaf0d224",
}
KEYS = [
    "simplex_id", "vertex_ids", "physical_volume", "mean_gap", "factor_maxima",
    "gap_weighted_means", "max_bound", "jensen_bound", "max_floor_Q96",
    "jensen_floor_Q96",
]
NOTICE = """/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell01 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
"""


def descriptor(path: Path) -> dict:
    data = path.read_bytes()
    return {"path": str(path.relative_to(REPO)), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def read_pinned_inputs() -> dict[str, str]:
    result = {}
    for name, digest in INPUT_PINS.items():
        data = (REPO / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f"Changed immutable input: {name}")
        result[name] = data.decode("utf-8")
    return result


def split_top(text: str) -> list[str]:
    """Split generated Lean tuples/lists without altering their node text."""
    parts, stack = [], []
    quote = None
    escaped = False
    start = 0
    for i, char in enumerate(text):
        if quote is not None:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in "\"'":
            quote = char
        elif char in "([{":
            stack.append(char)
        elif char in ")]}":
            if not stack or "([{"[")]}".index(char)] != stack.pop():
                raise ValueError("Unbalanced generated Lean expression")
        elif char == "," and not stack:
            parts.append(text[start:i].strip())
            start = i + 1
    if stack or quote:
        raise ValueError("Unclosed generated Lean expression")
    parts.append(text[start:].strip())
    return parts


def definitions(source: str) -> dict[str, str]:
    pairs = re.findall(r"^def (\w+)\s*:[^\n]*:=\n(.*?)(?=^def |^end |\Z)",
                       source, re.M | re.S)
    result = {name: body.strip() for name, body in pairs}
    if len(result) != len(pairs):
        raise ValueError("Duplicate typed candidate declaration")
    return result


def row_fields(body: str) -> list[tuple[str, str]]:
    if not (body.startswith(".obj [") and body.endswith("]")):
        raise ValueError("Expected original raw simplex object")
    result = []
    for pair in split_top(body[len(".obj ["):-1]):
        if not (pair.startswith("(") and pair.endswith(")")):
            raise ValueError("Expected original field pair")
        members = split_top(pair[1:-1])
        if len(members) != 2:
            raise ValueError("Wrong raw field arity")
        key_expr, value = members
        match = re.fullmatch(r"String\.ofList (\[.*\])", key_expr)
        if match is None:
            raise ValueError("Unexpected raw field key")
        chars = ast.literal_eval(match.group(1))
        if not all(isinstance(c, str) and len(c) == 1 for c in chars):
            raise ValueError("Invalid character list")
        result.append(("".join(chars), value))
    if [key for key, _ in result] != KEYS:
        raise ValueError("Missing, duplicated, or reordered original simplex field")
    return result


def immutable_write(path: Path, source: str) -> None:
    data = source.encode("utf-8")
    if path.exists():
        if path.read_bytes() != data:
            raise ValueError(f"Refusing to overwrite a different generated output: {path}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def header(imports: list[str], namespace: str) -> str:
    return ("".join(f"import ImbalancedChen.{name}\n" for name in imports)
            + "\n" + NOTICE + f"namespace ImbalancedChen.{namespace}\n"
            + "open P2OriginalSaving19Archive (SourceJson)\n"
            + "open P2OriginalSaving16OriginalArchive\n")


def main() -> None:
    sources = read_pinned_inputs()
    typed_source = sources[str(BASE / "ImbalancedChen/P2Saving16Cell01TypedPayload.lean")]
    typed_manifest = json.loads(sources[str(BASE / "TYPED_PAYLOAD_MANIFEST.json")])
    if typed_manifest["input"]["sha256"] != "d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f":
        raise ValueError("Wrong original Cell01 provenance")
    defs = definitions(typed_source)
    raw_rows = [f"rawSimplex{i:02d}" for i in range(81)]
    actual_rows = sorted(n for n in defs if re.fullmatch(r"rawSimplex\d+", n))
    if actual_rows != raw_rows:
        raise ValueError("Wrong original ordered row inventory")
    if defs["rawSimplicesItems"] != "[" + ", ".join(raw_rows) + "]":
        raise ValueError("Original raw row array reordered")
    if defs["simplices"] != "#[" + ", ".join(f"simplex{i:02d}" for i in range(81)) + "]":
        raise ValueError("Original typed row array reordered")
    all_fields = [row_fields(defs[name]) for name in raw_rows]
    module_sources = {}
    ns = "P2Saving16Cell01FieldDecode"
    common = ("open P2Saving16Cell01TypedPayload\n"
              "open P2Saving16Cell01ScalarDecode\n"
              "open scoped ImbalancedChen.P2Saving16Cell01FieldDecode\n\n")

    base_donor = sources["ImbalancedChen/P2Saving16Cell00FieldBase.lean"]
    body = base_donor[base_donor.index("theorem lookup_dimension"):]
    before = body[:body.index("theorem vertex00_decoded")]
    after = body[body.index("theorem vertices_mapped"):]
    vertices = "".join(
        f"theorem vertex{i:02d}_decoded : rationalArray rawVertex{i:02d} = .ok vertex{i:02d} := by\n"
        f"  unfold rawVertex{i:02d} vertex{i:02d}\n  simp\n\n"
        f"attribute [local simp] vertex{i:02d}_decoded\n\n" for i in range(35))
    base_body = (before + vertices + after).replace("Cell00", "Cell01")
    module_sources["P2Saving16Cell01FieldBase"] = header(
        ["P2Saving16Cell01FieldSimp"], ns) + common + base_body

    for i, fields in enumerate(all_fields):
        parts = [header(["P2Saving16Cell01FieldSimp"], ns), common]
        for key, value in fields:
            name = f"simplex{i:02d}_lookup_{key}"
            parts.append(
                f"theorem {name} :\n"
                f"    rawSimplex{i:02d}.getObjVal? {json.dumps(key)} = .ok ({value}) := by\n"
                f"  rfl\n\nattribute [local simp] {name}\n\n")
        parts.append(
            f"theorem simplex{i:02d}_decoded : decodeSimplex rawSimplex{i:02d} = .ok simplex{i:02d} := by\n"
            f"  unfold decodeSimplex simplex{i:02d}\n"
            f"  simp [rationalField, rationalArrayField]\n\n"
            f"end ImbalancedChen.{ns}\n")
        module_sources[f"P2Saving16Cell01Simplex{i:02d}Decode"] = "".join(parts)

    final_donor_path = "docs/source-only/20261126-p2-5-cell00-field-symbolic/ImbalancedChen/P2Saving16Cell00FieldDecode.lean"
    final_donor = sources[final_donor_path]
    generic = final_donor[final_donor.index("private theorem decodeCell_of_field_successes"):
                          final_donor.index("theorem rawRoot_decoded")]
    generic = generic.replace("private theorem", "theorem", 1)
    module_sources["P2OriginalSaving16DecoderRecordCompose"] = (
        header(["P2OriginalSaving16DecoderCompose"], "P2OriginalSaving16OriginalArchive")
        + "\n/- Public extraction of the existing Cell00 symbolic composition proof. -/\n"
        + generic + "end ImbalancedChen.P2OriginalSaving16OriginalArchive\n")
    base_names = re.findall(r"^theorem (\w+)\s*:", base_body, re.M)
    simplex_names = [f"simplex{i:02d}_decoded" for i in range(81)]
    middle = final_donor[final_donor.index("theorem simplices_mapped"):
                         final_donor.index("/- The symbolic root")]
    final_body = final_donor[final_donor.index("theorem rawRoot_decoded"):]
    final_body = final_body.replace("Cell00", "Cell01").replace("cell00", "cell01")
    module_sources[ns] = (
        header(["P2OriginalSaving16DecoderRecordCompose", "P2Saving16Cell01FieldBase"]
               + [f"P2Saving16Cell01Simplex{i:02d}Decode" for i in range(81)], ns)
        + common + "attribute [local simp] " + " ".join(base_names + simplex_names)
        + "\n\n" + middle + final_body)

    output_rows = []
    for module, text in module_sources.items():
        path = PACKAGE / "ImbalancedChen" / (module + ".lean")
        immutable_write(path, text)
        row = descriptor(path)
        row["module"] = "ImbalancedChen." + module
        row["public_theorems_in_source"] = re.findall(r"^theorem (\w+)", text, re.M)
        output_rows.append(row)
    manifest = {
        "schema": "p25-cell01-field-source-package-v1",
        "status": "SOURCE_ONLY_UNCOMPILED",
        "Lean_executed": False, "P2_5_proved": False,
        "input_witness_sha256": typed_manifest["input"]["sha256"],
        "inputs": [descriptor(REPO / name) for name in INPUT_PINS],
        "outputs": output_rows,
        "counts": {"root_fields": 17, "vertices": 35, "simplices": 81,
                   "fields_per_simplex": 10, "modules": len(output_rows),
                   "public_theorems_in_source": sum(len(r["public_theorems_in_source"]) for r in output_rows)},
        "reused_symbolic_proof": {
            "source": final_donor_path,
            "old_visibility": "private", "new_visibility": "public",
            "statement_and_proof_expression_unchanged": True,
        },
    }
    immutable_write(PACKAGE / "FIELD_MANIFEST.json", json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
