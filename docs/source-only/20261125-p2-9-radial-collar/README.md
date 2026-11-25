# P2.9: actual frozen-cutoff radial ordinary collar

**SOURCE_ONLY_UNCOMPILED. Formal credit = 0; kernel credit = 0; endpoint credit = 0.**

This package extends the existing physical radial-shell argument to the actual
Gamma5 frozen-history cutoff and source-rank constants. It is a single-ambient
ordinary collar payment. It neither asserts completion of P2.9 nor identifies
the whole marked-history ordinary mass with the manuscript's J.

## Fixed quantities and conclusions

The original fully qualified constants are reused unchanged:

- `Part5OriginalH430FrozenRootRefinement.frozenLeafCutoffFloor` is
  a = ((11/384) / 101^440) / 6.
- `P2FiniteMarkedGamma5ActualRank.frozenSourceRankBound` is K = floor(a^(-1)).
- The auxiliary rough cutoff is `cut N = N^(a/2)`. Write beta = a/2.

The new rough endpoint and shell conclusions are

```text
(log N / N) * roughCount(c*N, N^beta)
  --> beta^(-1) * c * buchstab(beta^(-1))             (c > 0)

(log N / N) * card(roughNumbers(c*N, N^beta)
                    \\ roughNumbers(b*N, N^beta))
  --> beta^(-1) * (c-b) * buchstab(beta^(-1))         (0 < b <= c).
```

A symbolic fixed band index ceil(beta^(-1)) + 1 is chosen before N.
The proof applies the already supplied unrestricted finite-band error theorem.
It does not prove another Buchstab or PNT estimate, and it does not truncate
this actual cutoff to the old band 100.

For ordered prime tuples at each rank k <= K, the existing product-fibre
bound k^k gives

```text
card(bandTuples N k b c) <= k^k * card(shell N b c).
```

The rank sum includes k = 0, with the empty product 1 and 0^0 = 1.
Repeated prime coordinates are retained. There is no extra mark or colour
factor: the multiplier is one, whereas the reused older example had 20.

The main payment is

```text
for every epsilon > 0,
there exists fixed 0 < h <= 1/8,
eventually in N,
  (log N / N) * boundaryCount N (1-2*h) (1+2*h) <= epsilon.
```

K, the finite sum over Fin(K+1), and the fibre powers remain symbolic.
No finite enumeration or numerical evaluation of the enormous rank occurs.

## Original profile support and physical width

The profile consumer fixes `radialWidth h = log(1+h)`. It proves
`0 < radialWidth h <= 1` and `exp(radialWidth h) = 1+h < 2`.
The existing nonzero-support theorem therefore gives the strict complete
product cap M < (1+h)N < 2N. Every positive natural coordinate divides M,
so every slot is at most 2N. The resulting Fin(2N+1) enumeration preserves
all original coordinates and their order; empty old or rough blocks,
repeated factors and a unit rough tail are not excluded.

The actual lower floor on nonzero profile support is N^a/2. The package
derives `N^(a/2) <= N^a/2` eventually, using
`(N^(a/2))^2 = N^a` and `N^(a/2) --> infinity`.
No stronger cutoff is introduced as a caller hypothesis.

`profileOuterMass` is explicitly the original `finPhysicalProfile`
weighted sum on its bounded prime-tuple enumerator with M > N.
The existing `physicalProfile_bounds` supplies its weights in [0,1];
a weight bound is not admitted as a new premise. The fixed h is chosen
before N, k, r and logQ, and the same ordinary payment bounds this sum
whenever k+2+r <= K.

The proved dictionary at this stage is bounded enumeration plus exact
coordinate coverage of every nonzero natural prime tuple. This package
does **not** yet prove a sum equality with a separately defined full
natural-support sum or with the old actual-history mass/J expression.
Pointwise coverage is not reported as that missing aggregate equality.
The original actual-rank supplier derives the bound for actual sources;
this package does not repeat or requalify that supplier.

## Reused proofs and thin extraction

The old radial modules are retained as reference sources, not imported
through their heavy fixed-clamp seed/J chain:

| Reused source | Change in this package |
| --- | --- |
| `Part5OriginalH430ClassicalRadialRoughMass` | Replace 1/96 by the actual beta and band 100 by a fixed symbolic adequate band. |
| `Part5OriginalH430ClassicalRadialTupleCount.rank_bound` | Reuse its arbitrary-rank product-fibre argument at the new cutoff. |
| Its `absolute_radial_payment` | Replace Fin 201 by Fin(K+1), 96 by beta^(-1), and mark multiplier 20 by one. |
| `p5z_marked_prime_product_fibre_card_le` | Import the existing generic ordered-tuple fibre bound; do not re-prove it. |
| `finPhysicalProfile_nonzero_support`, integer positivity/product bounds, and `physicalProfile_bounds` | Reuse the unchanged actual physical profile and its accepted support/weight facts. |

The earlier radial package was source-only and concerned twenty
Gamma9--21 occurrences. Its existence is not counted as a Gamma5
payment or as new kernel evidence here. The already present
`original_badGamma5_cost_theta`,
`SeedConvertedMass.original_inclusive_converted_mass` and `seed_split`
are not re-proved.

Three original owner files have recorded preimages and postimages:

1. FrozenRootRefinement: move the two frozen-floor definitions and their
   positivity theorem, with exact declaration bytes and FQNs, to the
   lightweight constants module.
2. ActualRank: move its original rank definition, with exact bytes and FQN,
   into that same module. Its rank proof is untouched.
3. ClassicalFixedClampGeometry: move the existing `prime_divisor_floor`
   statement under the same FQN to a lightweight core. The two list
   membership proof terms are expressed using simp; **this theorem body
   is not byte-identical to the recorded original**. No new mathematical
   argument is introduced. A separately reported historical membership
   overlay was not available by an exact selected path during this edit.

Each postimage differs only by its core import and removal of the moved
declarations. Static reverse reconstruction of all three owner preimages
passed. When original owners are loaded with these cores, select these
postimages to avoid duplicate declarations. No old owner is needed for
the new thin endpoint/tuple proof itself.

## Native supplier selection

The only new native import used by the rough module is

```text
MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformFixedCompat
source SHA256:
282ede7340f0069dc12479db826b6a4346ed458a1d37ed1ea926740183e07900
```

The dependency audit supplied its exact existing interface
`LiLiuPrereqBuchstab.roughCount_buchstab_band_error_unrestricted`,
with arbitrary natural k and no k <= 100 condition.
The existing compatibility module imports the legacy Uniform module and
was reported as separately source-compiled and audited on P1.
This report is dependency provenance, not a compilation result for the
new package.

The three full 9d4 research provider overlays were inspected as alternatives
but are **not selected**. Their SHA256s and the actually observed legacy
provider SHA256s are registered separately. The previous 1526-source
metadata comparison against `records[].sha256` does not establish that
those three production overlay sources were loaded. No such qualification
or kernel credit is claimed.

## Manuscript scope and remaining work

The manuscript anchor is release-20261106/en/argument.tex, lines 400--407,
at chen-imbalanced-semiprimes commit
a988cba584d803ae2856a0de50efb582f4f3dd6a: positive outer approximation,
N tending to infinity before approximation error tends to zero, and the
same approximation within one precision. The explicit radial shell
formula is a formal implementation of that omitted deduction. It is not
quoted as a separately stated manuscript lemma. The historical
prime-product-radial-boundary-repair note is not substituted for the 1106
release.

The package preserves the order “fixed width, then N to infinity”.
The layer N < M < exp(width)N is paid in ordinary N/log N mass, rather
than discarded using its shrinking exponent-coordinate width.

Compilation and owned-declaration/axiom review for all new modules remain
to be performed by the root task. Further manuscript work includes the
ordinary mass sum dictionaries, all history/mark multiplicities,
nonradial approximation errors, the same-family source/J identification,
and the prime-product/distribution application. This one-ambient radial
increment does not establish those conclusions.

The 29 H247/native-Wu endpoints belong to the existing native Binder's
still-open sufficient-condition/compatibility branch. It has not been
proved that all 29 are necessary obligations for the manuscript's actual
enhanced finite-family conclusion. That semantic identification remains
open and is not inserted into the manuscript-mainline obligation list.

No cloud job, local Lean build, commit or ref update is performed by this
package's source author. Only source text and immutable Git blobs are
prepared for the root task's review and controlled compilation.
