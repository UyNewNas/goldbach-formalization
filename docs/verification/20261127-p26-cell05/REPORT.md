# P2.6 Cell05 finite certificate and original RowNumerics join

Base: `b9fe4eff619ed611dd87643790acfad4d3fcdaa6`, from
`work/p2-6-source-closure-20261125`. This is a continuation of the current
source closure, not the older formal-proof staging branch.

## Proved in this execution

`P2OriginalSaving19Cell05GeometryCertificate` connects the original packed
JSON parse and decoded GeometryShape to the previously accepted 56-row
ten-clause arithmetic certificate. Its new closed kernel proof checks all
28 original vertices: physical inequalities, saved gap and factor values,
gap nonnegativity, and the original `53/13824` denominator lower bound.
Each row's vertices are proved to come from the original vertex array.
Positive volume, mean gap, mass, all ten weighted means and maxima, and
Jensen values follow from these same decoded rows.

The original integer division is proved equal to rational floor. Every
geometry Jensen Q96 floor lies below its rational Jensen bound, with error
strictly less than `1/2^96`; the sum over Cell05 loses strictly less than
`56/2^96`. These are geometry Jensen fields, not the different moment new
Q96 floors and not assertions about the real cell integral.

`P2OriginalSaving19RowNumericsPureBridge` now compiles in a freshly checked
dependency context. `P2OriginalSaving19Cell05OriginalRowChecks` uses that
definitional equivalence to prove all 56 rows in the original RowNumerics
interface. A uniqueness lemma transports these checks to any consumer
decoding the identical original text; no `.getD` fallback or hash equality
is a mathematical premise. The primary parse/shape/row theorem is closed.

## Verification

`RUN.json` records eight successful normal compilations with `--trust=0`
and warnings treated as errors, eight successful stock `leanchecker`
replays, and one successful full inventory/type/transitive-axiom audit.
All 151 owned declarations, including generated/private declarations,
were inventoried against the actual serialized module inventories.
Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms.
The complete project import closure has 139 modules. All source and reused
object hashes are checked before and after this run.

Lean is `leanprover/lean4:v4.33.0-rc1`. Mathlib is
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. No `lake update` was run.
One missing Mathlib cache object, `Mathlib.Tactic.Push.Attr`, was rebuilt
from that pinned tree with `lake build Mathlib.Tactic.Push.Attr`.

The analytic suppliers `P2PositiveAffineSimplexLogJensen`,
`P2DegreeSixLogGapSoundness`, and `P2OriginalLogMomentQ96Checker` were
recompiled and replayed here. Their changes only replace proposition-valued
`letI` by `let`, remove redundant tactic sequencing, and retain an original
unused measurable-space parameter under a local linter setting. Mathematical
declaration statements and constants are unchanged. This fresh acceptance
does not claim byte-identical reuse of the earlier differing analytic
objects or transfer their historical receipts into this context.

Owned counts: 19 + 28 + 39 + 13 + 20 + 1 + 23 + 8 = 151.
The final results are in `RUN.json`, `*-normal.log`, `*-kernel.log`,
`joined-owned.log`, and `owned-declarations.json`. Earlier exploratory logs
are retained separately under `diagnostics/` and are not final receipts.

## Reproduction

From this repository root, with the pinned Mathlib and Lean installed and
the dependency objects in `.lake/build/lib/lean`:

```sh
python3 tools/p26/cell05-geometry-certificate/verify.py
```

The companion `project-objects.tar.xz` contains exactly the project objects
listed in `RUN.json`, including the 131 predecessor objects. It can be
extracted at `.lake/build/lib/lean` before replay. The original predecessor
acceptance remains in the prior Cell05 arithmetic evidence; this run freshly
validates the eight listed targets, not all 131 predecessor source commands.

## Remaining P2.6 scope and observed blocker

`P2_6_complete` remains **false**. This work closes the original RowNumerics
join for Cell05. It does not complete the 13-cell Archive, all 28,918 moment
rows, pulling ownership/coverage, owned integral, or ActualEndpoint.

For the next Cell05 moment-floor step, the original file
`eighth-third-moment-refinement-20261009-a23-low-05.witness.json` is missing
from the current `/workspace/goldbach-research`. The retained input ledger
pins 28,973 bytes and SHA-256
`9a85e92f79b24c2b2361717d3a29ecb6167059e5509211c2f3fb290b5284fe2c`.
The known P1 MCP was probed read-only for this file and returned
`Session terminated` (JSON-RPC 32600); no P1 task ID was returned. Direct GitHub
lookups of the known filename in the research/manuscript repositories also
returned 404. This records those bounded observations, not a claim that
no other copy exists. Recover the exact original bytes from the P1 source
environment or original input archive before certifying its new floors.
