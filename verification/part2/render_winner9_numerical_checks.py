#!/usr/bin/env python3
"""Render kernel proofs of the original selected Winner9 row checks.

The renderer supplies no numerical answers.  Every generated leaf evaluates
the existing sound checker on a record from the original paged archive.
Small leaves permit interrupted runs to retain already checked objects.
"""

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ROW_COUNT = 11026
BLOCK_SIZE = 256
PAGE_SIZE = 16
BLOCK_COUNT = (ROW_COUNT + BLOCK_SIZE - 1) // BLOCK_SIZE
PAGE_COUNT = (ROW_COUNT + PAGE_SIZE - 1) // PAGE_SIZE


def page_name(page: int) -> str:
    return f"P2Winner9NumericalPage{page:04}"


def block_name(block: int) -> str:
    return f"P2Winner9NumericalCheck{block:02}"


def render_page(page: int) -> str:
    first = page * PAGE_SIZE
    count = min(PAGE_SIZE, ROW_COUNT - first)
    block, offset = divmod(first, BLOCK_SIZE)
    ref = f"P2Winner9CompleteSeedBlock{block:02}.pages[{offset // PAGE_SIZE}]!"
    name = page_name(page)
    parts = [
        f"import ImbalancedChen.P2Winner9CompleteSeedBlock{block:02}\n"
        "import ImbalancedChen.P2Winner9SelectedArchiveChecker\n"
        "import ImbalancedChen.P2Winner9SeedArchiveChecks",
        f"/-! Original selected numerical certificates for ordinals {first}–{first + count - 1}. -/",
        f"namespace ImbalancedChen.{name}\n"
        "open P2Winner9SelectedArchiveChecker (checkSelected)\n"
        "open P2Winner9SeedArchiveChecks (Checked)",
        "set_option maxRecDepth 50000\nset_option maxHeartbeats 40000000\n"
        "set_option Elab.async true",
    ]
    for index in range(count):
        parts.append(
            f"private theorem row{index:02} : checkSelected ({ref})[{index}]! = true := by\n"
            "  decide +kernel"
        )
    branches = "\n".join(f"  · exact row{index:02}" for index in range(count))
    parts.append(
        f"theorem checked : Checked (fun _ r => checkSelected r = true) {first} {count}\n"
        f"    ({ref}) := by\n"
        "  refine ⟨by decide +kernel, fun i => ?_⟩\n"
        f"  fin_cases i\n{branches}"
    )
    parts.append(f"end ImbalancedChen.{name}")
    return "\n\n".join(parts) + "\n"


def render_block(block: int) -> str:
    first = block * BLOCK_SIZE
    count = min(BLOCK_SIZE, ROW_COUNT - first)
    pages = list(range(first // PAGE_SIZE, (first + count + PAGE_SIZE - 1) // PAGE_SIZE))
    imports = "\n".join(f"import ImbalancedChen.{page_name(p)}" for p in pages)
    refs = ",\n    ".join(
        f"P2Winner9CompleteSeedBlock{block:02}.pages[{offset}]!" for offset in range(len(pages))
    )
    proof = "\n".join(f"    {page_name(p)}.checked.flatten_cons <|" for p in pages[:-1])
    proof += f"\n    {page_name(pages[-1])}.checked.flatten_single"
    return f"""{imports}

namespace ImbalancedChen.{block_name(block)}
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) {first} {count}
    P2Winner9CompleteSeedBlock{block:02}.rows := by
  change Checked (fun _ r => checkSelected r = true) {first} {count} ([
    {refs}]).toArray.flatten
  exact
{proof}

end ImbalancedChen.{block_name(block)}
"""


def render_complete() -> str:
    imports = "\n".join(f"import ImbalancedChen.{block_name(b)}" for b in range(BLOCK_COUNT))
    proof = "\n".join(
        f"    {block_name(b)}.checked.flatten_cons <|" for b in range(BLOCK_COUNT - 1)
    )
    proof += f"\n    {block_name(BLOCK_COUNT - 1)}.checked.flatten_single"
    return f"""{imports}
import ImbalancedChen.P2Winner9CompleteSeedData

/-! Every original Winner9 row supplies its own selected numerical certificate. -/

namespace ImbalancedChen.P2Winner9CompleteNumericalChecks
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)
open P2Winner9CompleteSeedData (RowIndex entry allRows entry_eq_allRows)

set_option maxRecDepth 20000

theorem archive_checked : Checked (fun _ r => checkSelected r = true) 0 {ROW_COUNT} allRows := by
  unfold allRows P2Winner9CompleteSeedData.blocks
  exact
{proof}

attribute [local irreducible] allRows

theorem selected_checked (i : RowIndex) : checkSelected (entry i) = true := by
  rw [entry_eq_allRows]
  exact archive_checked.2 i

end ImbalancedChen.P2Winner9CompleteNumericalChecks
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "ImbalancedChen",
                        help="Module directory; use a source-only directory before verification.")
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--page", type=int, choices=range(PAGE_COUNT))
    choice.add_argument("--block", type=int, choices=range(BLOCK_COUNT))
    choice.add_argument("--all", action="store_true")
    args = parser.parse_args()
    if args.page is not None:
        outputs = {page_name(args.page): render_page(args.page)}
    else:
        blocks = list(range(BLOCK_COUNT)) if args.all else [args.block]
        outputs = {}
        for block in blocks:
            first = block * BLOCK_SIZE // PAGE_SIZE
            last = min(first + BLOCK_SIZE // PAGE_SIZE, PAGE_COUNT)
            outputs.update({page_name(page): render_page(page) for page in range(first, last)})
            outputs[block_name(block)] = render_block(block)
        if args.all:
            outputs["P2Winner9CompleteNumericalChecks"] = render_complete()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = args.output_dir / f"{name}.lean"
        current = path.read_text() if path.exists() else None
        if current == source:
            continue
        if args.check:
            raise SystemExit(f"Generated source differs: {path}")
        path.write_text(source)
    print(f"{len(outputs)} numerical-check modules {'match' if args.check else 'rendered'}")


if __name__ == "__main__":
    main()
