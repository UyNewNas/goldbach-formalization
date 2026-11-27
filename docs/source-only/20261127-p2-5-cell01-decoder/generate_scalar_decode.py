#!/usr/bin/env python3
"""Generate Cell01 scalar proof candidates using the published payload and Cell00 proofs."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re


PACKAGE = Path(__file__).resolve().parent
SOURCE_ONLY = PACKAGE.parent
CELL01 = SOURCE_ONLY / "20261126-p2-5-cell01-parser-typed"
CELL00 = SOURCE_ONLY / "20261126-p2-5-cell00-decoded"
FIELD_SPLIT = SOURCE_ONLY / "20261126-p2-5-cell00-field-split"
PROJECT = "ImbalancedChen"
PREFIX = "P2Saving16Cell01"
SCALAR = PREFIX + "ScalarDecode"
FIELD_NS = PREFIX + "FieldDecode"
BATCH_SIZE = 128
HEADER = "/-! Cell01 decoder proof candidates. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/"
INPUTS = {
    CELL01 / "TYPED_PAYLOAD_MANIFEST.json": "d125e382cfe99b1cb8359e6ed556fa695b3e800894b1a796bcd69c4448239d48",
    CELL01 / PROJECT / (PREFIX + "TypedPayload.lean"): "1ddf5f99c579ef2fedcf197c7b7a5f642262e905a1ad9bdec2b6f44229cc9d99",
    CELL00 / PROJECT / "P2Saving16Cell00ScalarDecode.lean": "ba4424e7db6a4efdcd88278b80c129e15cb9049e193adbf7f0e95825964bb9f3",
    CELL00 / PROJECT / "P2Saving16Cell00TypedPayload.lean": "e92848bd075bf82fe7325bd46e3ddcde937cba277387d46a3579560c27aa287b",
    FIELD_SPLIT / PROJECT / "P2Saving16Cell00FieldSimp.lean": "1e43f44c0cbc858d505ef968499390bf85c25426d7307d69c833e2f89c455aa4",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def chars(spelling):
    # All callers use a validated alphabet of decimal digits, '/' and '-'.
    return "[" + ", ".join(repr(ch) for ch in spelling) + "]"


def checked_inputs():
    documents = {}
    for path, expected in INPUTS.items():
        data = path.read_bytes()
        if sha(data) != expected:
            raise ValueError(f"Input hash mismatch: {path}")
        documents[path.name] = data.decode()
    return documents


def scalar_definitions(typed_source):
    return dict(re.findall(r"^def ((?:rational|integer)\d+) : [ℚℤ] :=\n  ([^\n]+)$",
                           typed_source, re.MULTILINE))


def existing_proofs(source):
    pattern = (r"^theorem ((?:rational|integer)\d+)_decoded :\n"
               r"    (parseRational|parseInteger) \(String.ofList (\[[^\]]*\])\) = \.ok \1 :=")
    results = {}
    for name, parser, literal in re.findall(pattern, source, re.MULTILINE):
        spelling = "".join(ast.literal_eval(literal))
        results[parser, spelling] = name
    if len(results) != 227:
        raise ValueError("Incomplete Cell00 scalar inventory")
    return results


def scalar_specs(manifest, typed_source, donor_source, donor_typed):
    donors = existing_proofs(donor_source)
    definitions = scalar_definitions(typed_source)
    old_definitions = scalar_definitions(donor_typed)
    specs = []
    for kind, parser in (("rational", "parseRational"), ("integer", "parseInteger")):
        for row in manifest[kind + "_candidates"]:
            name, spelling = row["name"], row["original_string"]
            if not (re.fullmatch(kind + r"\d{3,}", name) and
                    re.fullmatch(r"-?[0-9]+(?:/[0-9]+)?" if kind == "rational" else r"-?[0-9]+", spelling)):
                raise ValueError(f"Invalid {kind} entry: {name}")
            donor = donors.get((parser, spelling))
            if donor and definitions[name] != old_definitions[donor]:
                raise ValueError(f"Cell00 proof result differs for {name}")
            specs.append((name, parser, spelling, donor))
    if len(specs) != len(definitions) or {r[0] for r in specs} != set(definitions):
        raise ValueError("Scalar names differ from Cell01 payload definitions")
    return specs


def nat_keys(typed_source):
    encoded = re.findall(r"\.number \(String.ofList (\[[^\]]*\])\)", typed_source)
    if len(encoded) != typed_source.count(".number"):
        raise ValueError("A raw numeric literal was not read")
    keys = {"".join(ast.literal_eval(literal)) for literal in encoded}
    if not all(re.fullmatch(r"0|[1-9][0-9]*", k) for k in keys):
        raise ValueError("Expected canonical natural-number literals in raw fields")
    return sorted(keys, key=int), len(encoded)


def scalar_block(rows):
    imports = ["P2OriginalSaving16DecoderChars", PREFIX + "TypedPayload"]
    if any(donor for _, _, _, donor in rows):
        imports.append("P2Saving16Cell00ScalarDecode")
    lines = [*(f"import {PROJECT}.{mod}" for mod in imports), "", HEADER,
             f"namespace {PROJECT}.{SCALAR}", "open P2OriginalSaving16OriginalArchive",
             f"open {PREFIX}TypedPayload", ""]
    for name, parser, spelling, donor in rows:
        lines.extend([f"theorem {name}_decoded :",
                      f"    {parser} (String.ofList {chars(spelling)}) = .ok {name} := by"])
        if donor:
            lines.append(f"  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.{donor}_decoded")
        else:
            lines.extend([f"  rw [{parser}_ofList]", "  rfl"])
        lines.append("")
    lines.append(f"end {PROJECT}.{SCALAR}")
    return "\n".join(lines) + "\n"


def register(lines, names):
    for start in range(0, len(names), 12):
        lines.append("attribute [scoped simp] " + " ".join(names[start:start + 12]))


def field_simp(specs, naturals, donor):
    common = donor[donor.index("private theorem except_ok_bind"):
                   donor.index("private theorem nat000_literal_decoded")]
    lines = [f"import {PROJECT}.P2OriginalSaving16DecoderCompose",
             f"import {PROJECT}.{SCALAR}", "", HEADER, f"namespace {PROJECT}.{FIELD_NS}",
             "open P2OriginalSaving19Archive (SourceJson)", "open P2OriginalSaving16OriginalArchive",
             f"open {PREFIX}TypedPayload", f"open {SCALAR}", "", common.rstrip(), ""]
    aliases = []
    for number in naturals:
        name = f"nat{int(number):03d}_literal_decoded"
        lines.extend([f"private theorem {name} :",
                      f'    (SourceJson.Decode.read (.number "{number}") : Except String Nat) = .ok {number} :=',
                      f"  decodeNat_number_ofList {chars(number)}", ""])
        aliases.append(name)
    for name, parser, spelling, _ in specs:
        alias = name + "_literal_decoded"
        lines.extend([f"private theorem {alias} :", f'    {parser} "{spelling}" = .ok {name} :=',
                      f"  {name}_decoded", ""])
        aliases.append(alias)
    register(lines, aliases)
    lines.append("")
    lines.extend(line for line in donor.splitlines()
                 if line.startswith(("attribute [scoped simp] decodeString_str",
                                     "attribute [scoped simp] SourceJson.")))
    register(lines, [name + "_decoded" for name, *_ in specs])
    lines.extend(["", f"end {PROJECT}.{FIELD_NS}"])
    return "\n".join(lines) + "\n"


def render():
    docs = checked_inputs()
    manifest = json.loads(docs["TYPED_PAYLOAD_MANIFEST.json"])
    typed = docs[PREFIX + "TypedPayload.lean"]
    specs = scalar_specs(manifest, typed, docs["P2Saving16Cell00ScalarDecode.lean"],
                         docs["P2Saving16Cell00TypedPayload.lean"])
    naturals, occurrences = nat_keys(typed)
    outputs = {}
    chunks = []
    for offset in range(0, len(specs), BATCH_SIZE):
        module = f"{SCALAR}Part{offset // BATCH_SIZE:02d}"
        chunks.append(module)
        outputs[f"{PROJECT}/{module}.lean"] = scalar_block(specs[offset:offset + BATCH_SIZE])
    outputs[f"{PROJECT}/{SCALAR}.lean"] = "".join(f"import {PROJECT}.{m}\n" for m in chunks) + "\n" + HEADER + "\n"
    outputs[f"{PROJECT}/{PREFIX}FieldSimp.lean"] = field_simp(specs, naturals, docs["P2Saving16Cell00FieldSimp.lean"])
    reused = {name: donor for name, _, _, donor in specs if donor}
    receipt = {
        "schema": "p25-cell01-scalar-decoder-source-v1",
        "status": "SOURCE_ONLY_UNCOMPILED", "new_formal_credit": False, "P2_5_proved": False,
        "input_witness": manifest["input"], "generator_sha256": sha(Path(__file__).read_bytes()),
        "pinned_sources": {str(p.relative_to(SOURCE_ONLY.parent.parent)): h for p, h in INPUTS.items()},
        "rational_count": len(manifest["rational_candidates"]), "integer_count": len(manifest["integer_candidates"]),
        "typed_raw_number_occurrences": occurrences, "distinct_raw_natural_spellings": naturals,
        "scalar_theorems": len(specs), "new_scalar_reductions": len(specs) - len(reused),
        "accepted_cell00_theorem_references": reused,
        "scalar_theorems_per_module_max": BATCH_SIZE, "proof_modules": chunks,
        "field_simp_private_theorems": 3 + len(naturals) + len(specs),
        "files": {p: {"sha256": sha(s.encode()), "bytes": len(s.encode())} for p, s in outputs.items()},
    }
    outputs["SCALAR_MANIFEST.json"] = json.dumps(receipt, indent=2, ensure_ascii=False) + "\n"
    return outputs


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--check", action="store_true", help="check existing generated bytes")
    args = cli.parse_args()
    outputs = render()
    # Validate the whole write set before creating any file. An independently
    # edited candidate is retained, rather than silently regenerated over it.
    for path, content in outputs.items():
        dest = PACKAGE / path
        if args.check:
            if not dest.is_file() or dest.read_bytes() != content.encode():
                raise SystemExit(f"Missing or changed generated file: {dest}")
        elif dest.exists() and (not dest.is_file() or dest.read_bytes() != content.encode()):
            raise SystemExit(f"Refusing to overwrite a different generated file: {dest}")
    if not args.check:
        for path, content in outputs.items():
            dest = PACKAGE / path
            if dest.exists():
                continue
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(content.encode())


if __name__ == "__main__":
    main()
