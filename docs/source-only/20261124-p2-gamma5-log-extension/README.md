# Actual finite marked Γ5 logarithmic extension

**Status: source-only; not compiled or kernel-replayed. No new formal or
endpoint credit.** Both files passed an independent source-level review by
`/root/p2_numerical`. Root owns dependency resolution and strict validation.

## What this candidate actually supplies

`P2FiniteMarkedGamma5LogExtension` constructs an explicit smooth profile in
physical logarithmic coordinates. Its arguments are the old prefix log,
the two fresh ordered slots, and every slot of the rough residual. The tail
rank is arbitrary. The integer evaluation uses the same formula on all
natural-number tuples, including composite slots; it has no primality,
coprimality, coefficient-ρ, or additive-output branch.

`actual_source_one` derives every gate from the existing, independent
`badLabels` and `roughNumbers` source. Its essential type is:

```lean
0 < N → 0 < d → 1 < Q / d → 0 < width →
qs ∈ badLabels N Q d →
m ∈ roughNumbers ((N:ℝ)/(d*qs.prod:ℕ)) (cutoff Q d (227/50)) →
integerExtension N Q width d (sourcePair qs) (canonicalTail m) = 1
```

The original geometric upper endpoints and pair ordering remain strict;
the lower endpoints, bad wall `Q ≤ d*q₁²*q₂`, roughness, canonical tail
ordering, and ordinary product cap remain closed. There is no assertion
that the smooth profile equals the sharp indicator off the actual source.

`source_fullProduct` proves

```lean
fullProduct d (sourcePair qs) (canonicalTail m) = d * qs.prod * m
```

from actual pair membership and `m > 0`. The canonical list is the complete
`primeFactorsList`, preserving repeated factors. The `m = 1` length-zero
case and its exact product are explicit theorems; no lower bound on tail
rank excludes it.

`marked_source_test_unchanged` inserts this one-valued geometric factor
inside the original sum indexed by marks, pair lists, and rough integers.
It preserves arbitrary original weights σ and arbitrary tests F. Thus the
same additive-prime, congruence, or coprimality test can remain literally
outside the profile. Equal-product marks are never merged by a product
image. This is a source-preserving equality, not a PP estimate.

## Actual enhanced-U4 caller

`P2FiniteMarkedGamma5SeedPlateau` applies that theorem to the real
`LevelIndex N n .U4 t p dep`, `wordProduct`, `levelMark`, and
`rootQ N n .U4 t p`.

`enhanced_position_source_one` obtains positivity and `1 < Q/d` from
`Part5OriginalH430SeedHistoryMass.scale_and_alpha`. It obtains the original
book's old-prime and Γ5 cutoff lower bounds from
`Part5OriginalH430HistoryQuotientCounts.history_integer_roughness` at the
same `levelOccurrence`. Its conclusion retains all of:

```lean
0 < frozenLeafCutoffFloor
∀ q ∈ (wordProduct l).primeFactors,
  (N:ℝ)^frozenLeafCutoffFloor ≤ (q:ℝ)
(N:ℝ)^frozenLeafCutoffFloor ≤ cutoff Q (wordProduct l) (227/50)
integerExtension N Q width (wordProduct l)
  (sourcePair qs) (canonicalTail m) = 1
```

No `1/90` cutoff or rank-200 ceiling is substituted. The caller removes the
geometry module's explicit `hd` and `hR` premises by using existing actual
book theorems. It does not replace them with a new admission assumption.
`enhanced_marked_source_test_unchanged` then uses the same finite selected
`B : Finset (LevelIndex ... .U4 ...)` and literal `levelMark`.

The U4 caller keeps the original restrictions `N ≥ 2`, `0 ≤ t ≤ 1/12`,
`1/(n+1) ≤ 11/384`, and `p ∈ originalBand N .U4`. These are the inputs
of the reused source geometry. This pointwise identity does not demand
a distribution theorem uniform over arbitrary moving families.

## Scale and remaining admission work

The full-product gate is

```text
log N − (log d + log q₁ + log q₂ + Σ log tail)
```

Consequently `integerExtension_product_lt` proves, for positive integer
slots, that nonzero weight implies
`fullProduct < exp(width) * N`. The width is in physical log scale. It is
not a fixed-width gate on `1 − Σ normalized_log_coordinates`, which would
give the unsuitable bound `N^(1+width)`.

The profile is globally smooth in its **log-coordinate** variables. A
complete physical `Licence`/`Family` still needs the original-prefix slot
pullback, compatible global physical zero extension, the family's lower
support and mixed-Euler budgets, and its actual source/smooth collar
payment. Those facts are not fields assumed by this module. The remaining
VM distribution supply and the other terms in `switchedPPBalance` remain
unpaid. Native H/h definitions and the PP coefficient have not changed.

## Exact bytes and executable validation roots

| New validation target | Source SHA256 |
|---|---|
| `ImbalancedChen.P2FiniteMarkedGamma5LogExtension` | `3ecc727198a6efcd45fe9205883e3397b46d487af974f7aca55306ca464089f6` |
| `ImbalancedChen.P2FiniteMarkedGamma5SeedPlateau` | `bd8cd06d0993b9006a699161631afac713013d7db589c8f1c32ffed2b38aae10` |

`SOURCE_MANIFEST.json` fixes the two new files and all four direct old
project-source choices. In particular the geometry import is the original
`20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5ArithmeticGeometry.lean`,
and the U4 imports are the original `20261110-yellow-closure-10t` source
locations used by the final dependency audit. There is no implicit
same-basename source overlay.

Root can validate the geometry target first, then the short U4 caller,
using its existing strict compiler, independent leanchecker, and owned
declaration audit. First resolve their complete project import closures
against the current qualified project/native records and these direct
source bindings. The candidate manifest deliberately does **not** claim
that the transitive graph is already resolved or accepted. Missing or
conflicting old bytes must be identified before that target is promoted.

The existing `P4BSmoothGateUpperStep` byte hash is also bound by the earlier
Wu source manifest. The other three old project imports are not covered
by that smaller Wu manifest; their transitive availability is a separate
root check. No reliable old module needs to be re-proved merely to add
this new geometry component.

## Manuscript locator

Fixed manuscript commit:
`a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/sieve-appendix.tex`.

- Lines 607–620, `sv:complete-fifth-region`: full Γ5 mother region and
  equality-inclusive bad slice `v+2u ≥ 1`.
- Lines 634–660: original marked prefix, the additive-prime quotient,
  ordered pair labels, and cutoff `R^a0`.
- Lines 1090–1101: a fixed finite set of queries with a positive original
  cutoff is chosen before sending `N` to infinity.

The arithmetic endpoint convention is taken from the existing exact
`pairLabels`/`badPair` definitions, not changed during this construction.
