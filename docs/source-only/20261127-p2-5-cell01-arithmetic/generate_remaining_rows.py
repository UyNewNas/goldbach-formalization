"""Generate the remaining Cell01 row owners and their composition from pinned sources."""

import argparse
import hashlib
import json
from pathlib import Path


PACKAGE = Path(__file__).resolve().parent
REPO = PACKAGE.parents[2]
OWNERS = PACKAGE / "ImbalancedChen"
PILOT = OWNERS / "P2Saving16Cell01Row00Arithmetic.lean"
FLOORS = OWNERS / "P2Saving16Cell01StoredFloors.lean"
CELL00 = (PACKAGE.parent / "20261126-p2-5-cell00-remaining-arithmetic" / "ImbalancedChen"
          / "P2Saving16Cell00AllRowsArithmetic.lean")
PINS = {
    PILOT: "9e0d5ff429c6c91d517a216bdaa1b7ab6f6fd7677209621fa94d61deaced4a6c",
    FLOORS: "a912ccaefc1119ae08460ab85cb1932d6909881d148a262049cfcd9ef5f542ba",
    CELL00: "39d76f5edf839aea803ee3b8e2e11497740cdc5854deca60bd7f5875eaecedd8",
}
NEW_SUM = "292535084187454643081"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def replace_exact(text, old, new, count):
    if text.count(old) != count:
        raise ValueError(f"Expected {count} occurrences of {old!r}")
    return text.replace(old, new)


def row_source(pilot, index):
    tag = f"{index:02d}"
    edits = [
        ("Row00Arithmetic", f"Row{tag}Arithmetic", 2),
        ("simplex00", f"simplex{tag}", 3),
        ("(0 : Fin 81)", f"({index} : Fin 81)", 3),
        ("row.simplexId = 0", f"row.simplexId = {index}", 2),
        ("the first original saving16 cell01 simplex", f"original saving16 cell01 simplex {tag}", 1),
        ("operation guard for row00", f"operation guard for row{tag}", 1),
    ]
    result = pilot
    for old, new, count in edits:
        result = replace_exact(result, old, new, count)
    restored = result
    for old, new, count in reversed(edits):
        restored = replace_exact(restored, new, old, count)
    if restored != pilot:
        raise ValueError(f"Row {tag} failed reverse substitution")
    return result


def all_rows_source(cell00):
    result = cell00.replace("Cell00", "Cell01").replace("cell00", "cell01")
    result = replace_exact(result, "13236428172062120", NEW_SUM, 2)
    result = replace_exact(result, "eight", "81", 3)
    result = replace_exact(result, "archive 0", "archive 1", 1)
    for template in ("import ImbalancedChen.P2Saving16Cell01Row{:02d}Arithmetic\n",
                     "  · exact P2Saving16Cell01Row{:02d}Arithmetic.simplex_valid\n"):
        first_eight = "".join(template.format(i) for i in range(8))
        all_rows = "".join(template.format(i) for i in range(81))
        result = replace_exact(result, first_eight, all_rows, 1)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check generated files without writing")
    args = parser.parse_args()
    for path, expected in PINS.items():
        if digest(path.read_bytes()) != expected:
            raise ValueError(f"Source pin mismatch: {path}")
    pilot = PILOT.read_bytes().decode()
    floors = FLOORS.read_text()
    for i in range(81):
        if floors.count(f"theorem simplex{i:02d}_stored_jensen_floor ") != 1:
            raise ValueError(f"Missing stored floor theorem {i}")
    if f").jensenFloor) = {NEW_SUM} := by decide +kernel" not in floors:
        raise ValueError("Stored floor sum does not match its supplying theorem")
    outputs = {OWNERS / f"P2Saving16Cell01Row{i:02d}Arithmetic.lean": row_source(pilot, i).encode()
               for i in range(1, 81)}
    outputs[OWNERS / "P2Saving16Cell01AllRowsArithmetic.lean"] = all_rows_source(CELL00.read_text()).encode()
    manifest = {
        "schema": "p25-cell01-remaining-row-arithmetic-source-v1",
        "status_at_generation": "SOURCE_ONLY_NOT_COMPILED",
        "generator_sha256": digest(Path(__file__).read_bytes()),
        "source_pins": {str(p.relative_to(REPO)): h for p, h in PINS.items()},
        "row00_accepted_object_sha256": "a1f49bbf4e9a7f15089c8b10b43a5986efef3ecedd003eca21aead5596320eae",
        "stored_floors_accepted_object_sha256": "013bf22594f3f84c7da405acd28d7b2dd9c25dbe9fd0ae31d4043f8cfdd03115",
        "input": {"file": "eighth-prefix-family-20261009-cell-01.witness.json",
                  "sha256": "d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f"},
        "new_rows_reverse_substitution_exact": 80,
        "composition_row_indices": list(range(81)),
        "termwise_geometric_floor_sum": NEW_SUM,
        "outputs": [{"path": str(p.relative_to(PACKAGE)), "bytes": len(data), "sha256": digest(data)}
                    for p, data in outputs.items()],
    }
    outputs[PACKAGE / "REMAINING_ROWS_MANIFEST.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    for path, data in outputs.items():
        if path.exists() and path.read_bytes() != data:
            raise ValueError(f"Preserve differing existing output: {path}")
        if args.check and not path.exists():
            raise ValueError(f"Missing existing output: {path}")
    if not args.check:
        for path, data in outputs.items():
            if not path.exists():
                with path.open("xb") as output:
                    output.write(data)


if __name__ == "__main__":
    main()
