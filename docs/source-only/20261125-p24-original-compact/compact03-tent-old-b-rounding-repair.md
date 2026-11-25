# Compact03: six-tent, OLD weight and below-mu B proof-expression repair

Date: 2026-11-25. Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

## Actual failing run

The input is P1 diagnostic job `job_a07d78e98e4e4a999137ad2e7ad046cc`,
source commit `5a91b30f`, with a 128-module diagnostic closure. The recorded log
is `p1-compact-03.log`, 32,153 bytes, SHA-256
`dea260febb4dcd042829b24c3dd3d2b50ae3405b70e187cd0b5aa5f002b5b494`.
The failures listed below were read directly from that log. This repair did
not run Lean, Lake, a numerical generator, a cloud job, or a new CI audit.

## Frozen manuscript and source correspondence

The local frozen 1106 manuscript comes from publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/numerical-appendix.tex`, SHA-256
  `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
  Its Directed arithmetic subsection specifies lower floors, upper ceilings,
  and positive denominators for division.
- `verification/data/certify_extended_prefix.py`, SHA-256
  `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.
  `affine_cap_lower` enumerates the six tent sums and the B plane
  `(153,0,0,-96,256)`. `jensen_difference_upper` retains the positive residual
  gate, OLD endpoint extremes, the symmetric maximum moment, the ordinary
  affine OLD mean, and the weight `(old_mean-old_lo)/(old_hi-old_lo)`.

In normalized coordinates, the symmetric branch uses
`(57/64-EX-EY-(3/2)*EMax)*EZInv-1`. For the B plane, the ordinary coefficients
are `-1`, `-1`, and `(-96-256)/256 = -11/8`, yielding
`(153/256-EX-EY)*EZInv-11/8`. These are the formulas already present in the
affected Lean files. Their interval operations and their positive-divisor
guards were not changed.

The separately named `numerical-w2-affine-series-independent-20261010.py`
was not locally available in the narrow lookup. As directed by the root
agent, no wider historical retrieval was attempted. This note does not claim
a new full replay-source equivalence review for that script.

## Minimal changes and classification

Locations refer to the pre-repair files.

| File and location | Change | Classification |
|---|---|---|
| `ActualThirdOriginalSixTentCandidates.lean:197` | Replace the unnecessary `<;> ring` continuation by sequential `ring`. | Strict-linter expression repair. |
| Same file, 221, 223, 239 | Add `add_comm` to the existing explicit simp sets, matching the quotient-plus-constant form of `affineArgument` with the translated inequalities. | Equal algebraic expressions had different addition order; no new mathematical premise or estimate. |
| `ActualThirdOriginalRoundedOldWeight.lean:31` | Restrict simplification after `neg_le_neg` to `up`, `value`, `Int.cast_neg`, `neg_div`, and `neg_neg`. | Preserve the intended floor-to-ceiling inequality reversal. |
| Same file, 123 | Bind `c` and `d` explicitly in `symmetricOld_encloses`. | Elaboration parameters absent from the logarithm premises; no new hypothesis. |
| `ActualThirdOriginalBelowMuBRounded.lean:31` | Apply the same explicit floor-to-ceiling simp set. | Same signed-rounding expression repair. |
| Same file, 61, 66 | Replace unnecessary `<;> ring` continuations by sequential `ring`. | Strict-linter expression repair. |
| Same file, 118 | Change the anonymous proposition-valued local instance from `letI` to `let`. | Follow the actual strict-linter diagnostic; retain the same probability proof. |

For the signed-rounding step, the existing lower-bound lemma applied to
`-n` gives `value ((-n)/d) <= (-n : Real)/d/P160`. Negating both sides yields
`(n : Real)/d/P160 <= -value ((-n)/d) = value (up n d)`.
The unrestricted `simp` was undoing the order reversal through general
negative-inequality simplification. The replacement uses the same explicit
simp pattern already present in
`ActualThirdOriginalPositive256Log.rounded_div_upper` and
`ActualThirdOriginalRoundedNewOperations.le_value_up`.

No mathematical gap was identified in these reported failures. The missing
steps are algebraic expression normalization and parameter elaboration using
existing hypotheses, together with strict-linter cleanup. This classification
does not assert completion of any other manuscript or finite-check obligation.

## Source bindings

| File | Before SHA-256 | After SHA-256 |
|---|---|---|
| `ImbalancedChen/ActualThirdOriginalSixTentCandidates.lean` | `a5a5a69ba0b41cb9effa19eb72bea9b405f4ff9be651712c4be2fd9c04ab7e5c` | `0922838c33552ee19bc35d0b5b4508db972b437be1dbcc7b57944a635c6b4003` |
| `ImbalancedChen/ActualThirdOriginalRoundedOldWeight.lean` | `e2fec9345e3b5d688c1be907aadd587e8f695f55217a8d37e79f89528a9520de` | `3519720a65e6dbc8447cc41e52437b38e623cb9c0f7cd134b24ccc01083baf13` |
| `ImbalancedChen/ActualThirdOriginalBelowMuBRounded.lean` | `e74fffa458fe2f2ee71f26c10be65391f224119b2d5d5ccb713e0b4528f7780e` | `3ad45e46e42eff0447345298d5ac06f22843d08e5b93e1da7f81273a32b3d80f` |

## Static verification and remaining gate

All 38 theorem headers, including private helpers, are byte-identical.
All 36 `def` declarations and both inductive declarations are byte-identical.
The earlier grouping-based count of 33 unchanged computational text blocks
includes adjacent declarations in the same block; the declaration count is 38.
Imports, theorem assumptions, conclusions, interval operation order and
computation bodies are unchanged. The diff has 11 insertions and 10 deletions,
and `git diff --check` passes. No `sorry`, `admit`, axiom, `native_decide`,
`unsafe`, or linter-disabling option was added.

Root owns the next actual Lean diagnostic. The modified proofs are not yet
claimed to compile, and this source repair grants no compilation, kernel,
finite-evaluation, or P2.4 completion credit.
