"""Render the integer inputs for the Winner9 pulling checker."""

import argparse
from fractions import Fraction
from functools import cache
from math import gcd, lcm
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "docs/source-only/20261028-resume-30g/certificate_rows"
VERTICES = ROOT / "ImbalancedChen/P2Winner9CompleteSeedVertices.lean"
LEAN = ROOT / "ImbalancedChen/P2Winner9OriginalPullingFlags.lean"
BEGIN = "-- Begin generated pulling data."
END = "-- End generated pulling data."
ROW_COUNT = 11026
BLOCK_SIZE = 256
PAGE_SIZE = 16


def vertex_table():
    pattern = r"\(\(\s*(-?\d+) : ℚ\) / (\d+)\)"
    points = [
        [Fraction(int(num), int(den)) for num, den in re.findall(pattern, line)]
        for line in VERTICES.read_text().splitlines()
        if line.strip().startswith("![")
    ]
    assert len(points) == 201 and all(len(point) == 8 for point in points)
    return points


def row_table():
    pattern = r"parentId := (\d+),\s*vertexIds := !\[([^\]]+)\]"
    rows = []
    for block in sorted(ARCHIVE.glob("P2Winner9CompleteSeedBlock*.lean")):
        for ordinal, ids in re.findall(pattern, block.read_text()):
            assert int(ordinal) == len(rows)
            rows.append(tuple(map(int, ids.split(","))))
    assert len(rows) == ROW_COUNT
    assert len(set(rows)) == len(rows)
    assert all(len(ids) == 9 and list(ids) == sorted(set(ids), reverse=True) for ids in rows)
    return rows


def mask_sum(point, mask):
    return sum(value for i, value in enumerate(point) if (mask >> i) & 1)


def ascending(value):
    return Fraction(1, 2) + value / 2


def descending(value):
    return Fraction(57, 64) - 3 * value / 2


def gate_values(point):
    navigation = [
        Fraction(num, 10**12)
        for num in [
            115365267465, 104500235252, 97721136227, 68922122738,
            55525244864, 46801972101, 28296601588, 21808164892,
        ]
    ]
    old_cap = ascending(point[0] + point[3])
    third_cap = descending(point[1] + point[2])
    new_cap = ascending(mask_sum(point, 138)) - Fraction(1, 10**6)
    values = [Fraction(25, 128) - point[0], point[2] - Fraction(1, 100),
              point[7] - Fraction(53, 13824)]
    values.extend(point[i] - point[i + 1] for i in range(7))
    values.extend(third_cap - (sum(point[:k]) + 3 * point[k]) for k in range(0, 8, 2))
    values.extend([
        old_cap - third_cap,
        descending(point[0] + point[3]) - old_cap,
        ascending(point[1] + point[2]) - third_cap,
        old_cap - (Fraction(153, 256) - 3 * point[2] / 8),
    ])
    for mask in range(1, 64):
        if mask == 9:
            continue
        y = mask_sum(navigation, mask)
        z = mask_sum(point, mask)
        values.append(old_cap - (descending(z) if descending(y) < ascending(y) else ascending(z)))
    values.extend([new_cap - old_cap, descending(mask_sum(point, 138)) - Fraction(1, 10**6) - new_cap])
    values.extend(new_cap - (sum(point[:j]) + 2 * point[j]) for j in range(8))
    values.extend(
        new_cap - (mask_sum(point, 138) + sum(
            point[k] for k in range(j) if not ((138 >> k) & 1)
        ) + 2 * point[j])
        for j in range(8) if not ((138 >> j) & 1)
    )
    values.extend([old_cap - sum(point) - point[7], sum(point) + 3 * point[7] - new_cap])
    assert len(values) == 97
    return values


def vertex_mask(ids):
    return sum(1 << vertex for vertex in ids)


def all_flags(points, rows):
    # Coordinates and all comparisons are exact rationals.
    evaluations = list(zip(*(gate_values(point) for point in points)))
    assert min(min(values) for values in evaluations) >= 0
    zero_masks = [vertex_mask(i for i, value in enumerate(values) if value == 0)
                  for values in evaluations]

    @cache
    def find_flag(face, ids):
        apex, *tail = ids
        if face.bit_length() - 1 != apex:
            return None
        if not tail:
            return ()
        lower = vertex_mask(tail)
        for gate, zeros in enumerate(zero_masks):
            if ((1 << apex) & zeros) or (lower & ~zeros):
                continue
            rest = find_flag(face & zeros, tuple(tail))
            if rest is not None:
                return (gate, *rest)
        return None

    flags = [find_flag((1 << len(points)) - 1, ids) for ids in rows]
    assert all(flag is not None and len(flag) == 8 for flag in flags)
    used_gates = sorted({gate for flag in flags for gate in flag})
    assert len(used_gates) == 21
    gate_number = {gate: i for i, gate in enumerate(used_gates)}
    packed = [
        sum(gate_number[gate] << (5 * step) for step, gate in enumerate(flag))
        for flag in flags
    ]
    return used_gates, [zero_masks[gate] for gate in used_gates], packed


def integer_point(point):
    denominator = lcm(*(value.denominator for value in point))
    numerator = [int(value * denominator) for value in point]
    return denominator, numerator


def integer_planes(gates):
    zero = [Fraction(0)] * 8
    offset = gate_values(zero)
    basis = [gate_values([Fraction(i == j) for i in range(8)]) for j in range(8)]
    result = []
    for gate in gates:
        coeffs = [offset[gate], *(values[gate] - offset[gate] for values in basis)]
        _, numerators = integer_point(coeffs)
        content = gcd(*numerators)
        assert content > 0
        result.append([value // content for value in numerators])
    return result


def lean_array(lines, name, type_name, entries):
    lines.append(f"private def {name} : Array ({type_name}) := #[")
    lines.extend(f"  {entry}{',' if i + 1 < len(entries) else ''}"
                 for i, entry in enumerate(entries))
    lines.extend(["]", ""])


def lean_pages(lines, prefix, name, type_name, entries):
    names = []
    for page, start in enumerate(range(0, len(entries), PAGE_SIZE)):
        page_name = f"{prefix}{page:03}"
        lean_array(lines, page_name, type_name, entries[start : start + PAGE_SIZE])
        names.append(page_name)
    lean_array(lines, name, f"Array ({type_name})", names)


def render(count):
    points = vertex_table()
    rows = row_table()
    gate_ids, masks, packed = all_flags(points, rows)
    lines = [BEGIN, "-- Produced by verification/part2/render_winner9_pulling_flags.py."]
    lean_pages(lines, "pointPage", "pointPages", "ℕ × (Fin 8 → ℤ)", [
        f"({denominator}, ![{', '.join(map(str, numerator))}])"
        for denominator, numerator in map(integer_point, points)
    ])
    lean_array(lines, "planeData", "ℤ × (Fin 8 → ℤ)", [
        f"({offset}, ![{', '.join(map(str, coeffs))}])"
        for offset, *coeffs in integer_planes(gate_ids)
    ])
    lean_array(lines, "maskData", "ℕ", list(map(str, masks)))
    keys = [vertex_mask(ids) for ids in rows[:count]]
    ordering = sorted(range(count), key=keys.__getitem__)
    ranks = [0] * count
    for rank, ordinal in enumerate(ordering):
        ranks[ordinal] = rank
    lean_pages(lines, "geometry", "geometryPages", "ℕ",
               [str((code << 14) + rank) for code, rank in zip(packed[:count], ranks)])
    lean_pages(lines, "ordered", "orderedPages", "ℕ",
               [str((keys[ordinal] << 14) + ordinal) for ordinal in ordering])
    return "\n".join([*lines, END])


def render_block_check(block):
    first = BLOCK_SIZE * block
    count = min(BLOCK_SIZE, ROW_COUNT - first)
    page_offsets = range(0, count, PAGE_SIZE)
    archive = f"P2Winner9CompleteSeedBlock{block:02}"
    module = f"P2Winner9OriginalPullingCheck{block:02}"
    pred = "(fun ordinal row => checkedRow ordinal row = true)"
    lines = [
        f"import ImbalancedChen.{archive}",
        "import ImbalancedChen.P2Winner9OriginalPullingFlags",
        "",
        f"namespace ImbalancedChen.{module}",
        "open P2Winner9OriginalPullingFlags (checkedRow)",
        "open P2Winner9SeedArchiveChecks",
        "",
        "set_option maxRecDepth 20000",
        "set_option maxHeartbeats 0",
        "",
    ]
    pages = []
    for page, offset in enumerate(page_offsets):
        pages.append(f"{archive}.pages[{page}]!")
        page_count = min(PAGE_SIZE, count - offset)
        lines.extend([
            f"private theorem page{page:02} :",
            f"    Checked {pred} {first + offset} {page_count} ({pages[-1]}) := by",
            "  decide +kernel",
            "",
        ])
    lines.extend([
        f"theorem checked : Checked {pred} {first} {count} {archive}.rows := by",
        f"  change Checked {pred} {first} {count} ([",
        ",\n".join(f"    {page}" for page in pages),
        "  ].toArray.flatten)",
    ])
    result = f"Checked.flatten_single page{len(pages) - 1:02}"
    for page in reversed(range(len(pages) - 1)):
        result = f"Checked.flatten_cons page{page:02} ({result})"
    lines.extend([f"  exact {result}", "", f"end ImbalancedChen.{module}"])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    outputs = parser.add_mutually_exclusive_group()
    outputs.add_argument("--check", action="store_true", help="compare with the installed Lean payload")
    outputs.add_argument("--block-check", type=int, help="render the Lean checker for one archive block")
    outputs.add_argument("--full-payload", action="store_true",
                         help="render candidate data for the complete archive")
    args = parser.parse_args()
    if args.block_check is not None:
        if not 0 <= args.block_check <= (ROW_COUNT - 1) // BLOCK_SIZE:
            parser.error("block index is outside the original archive")
        print(render_block_check(args.block_check))
        return
    payload = render(ROW_COUNT if args.full_payload else BLOCK_SIZE)
    if args.check:
        current = LEAN.read_text()
        start = current.index(BEGIN)
        stop = current.index(END) + len(END)
        if current[start:stop] != payload:
            parser.exit(1, "Winner9 pulling data differs from the archive renderer.\n")
    else:
        print(payload)


if __name__ == "__main__":
    main()
