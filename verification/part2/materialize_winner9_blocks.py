#!/usr/bin/env python3
"""Render the original Winner9 records in declarations of at most 16 rows."""

import argparse
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "docs/source-only/20261028-resume-30g/certificate_rows"
BLOCK_SIZE = 256
PAGE_SIZE = 16
ROW_COUNT = 11026
RECORD = re.compile(r"^  \{ parentId := (\d+),.*?\n    mixedSelected := \d+ \}", re.M | re.S)


def render_block(block: int) -> str:
    name = f"P2Winner9CompleteSeedBlock{block:02}"
    lower = block * BLOCK_SIZE
    upper = min(lower + BLOCK_SIZE, ROW_COUNT)
    archive = (ARCHIVE / f"{name}.lean").read_text(encoding="utf-8")
    start = "def rows : Array RawRow := #[\n"
    end = f"\n]\n\nend ImbalancedChen.{name}"
    body = archive.split(start, 1)[1].split(end, 1)[0]
    matches = list(RECORD.finditer(body))
    records = [match[0] for match in matches]
    if [int(match[1]) for match in matches] != list(range(lower, upper)):
        raise ValueError(f"Unexpected source ordinals in {name}")
    if body != ",\n".join(records):
        raise ValueError(f"Unrecognized record layout in {name}")

    sections = [
        "import ImbalancedChen.P2Winner9CompleteSeedTypes",
        "/-!\n"
        f"Original archive rows {lower} through {upper - 1} with their fields and order preserved.\n"
        "Pages of at most sixteen records bound elaboration depth.\n-/",
        f"namespace ImbalancedChen.{name}\nopen P2Winner9CompleteSeedTypes",
        "set_option maxRecDepth 20000\nset_option maxHeartbeats 8000000",
    ]
    pages = []
    for offset in range(0, len(records), PAGE_SIZE):
        page = f"rows{offset:03}"
        pages.append(page)
        page_body = ",\n".join(records[offset : offset + PAGE_SIZE])
        sections.append(f"private def {page} : Array RawRow := #[\n{page_body}\n]")
    sections.append("def pages : Array (Array RawRow) := #[\n  " + ", ".join(pages) + "\n]")
    sections.append("def rows : Array RawRow := pages.flatten")
    sections.append(f"end ImbalancedChen.{name}")
    return "\n\n".join(sections) + "\n"


def render_checks(block: int) -> str:
    data = f"P2Winner9CompleteSeedBlock{block:02}"
    name = f"P2Winner9SeedArchiveCheck{block:02}"
    start = block * BLOCK_SIZE
    count = min(BLOCK_SIZE, ROW_COUNT - start)
    sections = [
        f"import ImbalancedChen.{data}\nimport ImbalancedChen.P2Winner9SeedArchiveChecks",
        f"namespace ImbalancedChen.{name}\nopen P2Winner9SeedArchiveChecks",
        "set_option maxRecDepth 20000\nset_option maxHeartbeats 8000000",
    ]
    page_refs = []
    proofs = []
    for page, offset in enumerate(range(0, count, PAGE_SIZE)):
        ref = f"{data}.pages[{page}]!"
        proof = f"page{page:02}"
        page_refs.append(ref)
        proofs.append(proof)
        sections.append(
            f"private theorem {proof} :\n"
            f"    Checked ArchiveRowCheck {start + offset} {min(PAGE_SIZE, count - offset)} ({ref}) := by\n"
            "  decide +kernel"
        )
    proof_lines = [f"    {p}.flatten_cons <|" for p in proofs[:-1]]
    proof_lines.append(f"    {proofs[-1]}.flatten_single")
    sections.append(
        f"theorem checked : Checked ArchiveRowCheck {start} {count} {data}.rows := by\n"
        f"  change Checked ArchiveRowCheck {start} {count} ([\n    "
        + ",\n    ".join(page_refs)
        + "]).toArray.flatten\n  exact\n"
        + "\n".join(proof_lines)
    )
    sections.append(f"end ImbalancedChen.{name}")
    return "\n\n".join(sections) + "\n"


def render_complete_seed(count: int) -> str:
    checks = [f"P2Winner9SeedArchiveCheck{block:02}" for block in range(count)]
    blocks = [f"P2Winner9CompleteSeedBlock{block:02}.rows" for block in range(count)]
    block_list = ",\n  ".join(blocks)
    proof = "\n".join(f"    {name}.checked.flatten_cons <|" for name in checks[:-1])
    proof += f"\n    {checks[-1]}.checked.flatten_single"
    imports = "\n".join(f"import ImbalancedChen.{name}" for name in checks)
    return f"""import ImbalancedChen.P2Winner9CompleteSeedVertices
{imports}

/-! The complete original Winner9 family with kernel-checked archive ordinals and selected maxima. -/

namespace ImbalancedChen.P2Winner9CompleteSeedData

open P2Winner9CompleteSeedTypes
open P2Winner9SeedArchiveChecks

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

abbrev RowIndex := Fin {ROW_COUNT}

def blocks : Array (Array RawRow) := [
  {block_list}
].toArray

def allRows : Array RawRow := blocks.flatten

theorem archive_checked : Checked ArchiveRowCheck 0 {ROW_COUNT} allRows := by
  unfold allRows blocks
  exact
{proof}

attribute [local irreducible] allRows

private def certifiedLookup {{P : ℕ → RawRow → Prop}} {{n : ℕ}} {{rows : Array RawRow}}
    (h : Checked P 0 n rows) (i : Fin n) : {{r : RawRow // P i.val r ∧ r = rows[i.val]!}} :=
  ⟨rows[i.val]!, by simpa only [Nat.zero_add] using h.2 i, rfl⟩

-- Keep ordinal lookup abstract during use of its proof fields. The exact
-- equality below gives access to the original flattened array when needed.
private opaque certifiedEntry (i : RowIndex) :
    {{r : RawRow // ArchiveRowCheck i.val r ∧ r = allRows[i.val]!}} :=
  @certifiedLookup ArchiveRowCheck {ROW_COUNT} allRows archive_checked i

def entry (i : RowIndex) : RawRow := (certifiedEntry i).val

def physicalVertices (i : RowIndex) (k : Fin 9) : Fin 8 → ℚ :=
  P2Winner9CompleteSeedVertices.coordinates[(entry i).vertexIds k]!

theorem archive_row_check (i : RowIndex) : ArchiveRowCheck i.val (entry i) :=
  (certifiedEntry i).property.1

theorem entry_eq_allRows (i : RowIndex) : entry i = allRows[i.val]! :=
  (certifiedEntry i).property.2

theorem full_source_shapes_and_chronology :
    allRows.size = {ROW_COUNT} ∧ P2Winner9CompleteSeedVertices.coordinates.size = 201 ∧
      ∀ i : RowIndex, RowShape i.val (entry i) :=
  ⟨archive_checked.1, by decide +kernel, fun i => (archive_row_check i).1⟩

private theorem selected_of_check {{i : ℕ}} {{r : RawRow}} (h : ArchiveRowCheck i r) :
    r.mixedSelected = max r.logSelected r.mixedRaw := by
  rcases h with ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, hcur, _, hmix⟩, hle⟩
  rw [hmix, hcur, max_assoc, max_eq_right hle]

theorem selected_eq_max_log_mixed (i : RowIndex) :
    (entry i).mixedSelected = max (entry i).logSelected (entry i).mixedRaw :=
  selected_of_check (archive_row_check i)

end ImbalancedChen.P2Winner9CompleteSeedData
"""


def write_or_check(name: str, source: str, check: bool) -> None:
    path = ROOT / "ImbalancedChen" / f"{name}.lean"
    current = path.read_text(encoding="utf-8") if path.is_file() else None
    if current == source:
        return
    if check:
        raise SystemExit(f"Archive-derived source differs: {path.relative_to(ROOT)}")
    path.write_text(source, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify generated sources without writing.")
    args = parser.parse_args()
    count = (ROW_COUNT + BLOCK_SIZE - 1) // BLOCK_SIZE
    for block in range(count):
        write_or_check(f"P2Winner9CompleteSeedBlock{block:02}", render_block(block), args.check)
        write_or_check(f"P2Winner9SeedArchiveCheck{block:02}", render_checks(block), args.check)
    write_or_check("P2Winner9CompleteSeedData", render_complete_seed(count), args.check)
    print(f"{ROW_COUNT} original records in {count} blocks")


if __name__ == "__main__":
    main()
