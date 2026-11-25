# P2.9: actual frozen-cutoff radial ordinary collar

**THREE MODULES ACCEPTED. FrozenConstants, PrimeDivisorFloorCore and RadialRoughMass have passed normal compilation, stock leanchecker, named kernel replay and the complete owned-declaration/transitive-axiom audit: 42 owned declarations in total. Tuple, profile and natural-mass consumers remain source-only. Full P2.9 remains open.**

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

The natural-support dictionary is supplied by
`P2FiniteMarkedGamma5RadialNaturalMass`. Its finite `naturalOuterTuples`
carrier is the coordinatewise Nat.val image of `profileOuterTuples`.
For N > 0 and 0 < h <= 1/8, `mem_naturalOuterTuples` proves membership
if and only if every natural slot is prime, the unchanged original
profile is nonzero, and the complete natural product exceeds N.
The reverse implication directly reuses the proved integer enumeration;
there is no new support or rank hypothesis in this membership dictionary.

The coordinate-value map is injective by function extensionality and
Fin.ext. Consequently `Finset.sum_image` proves
`naturalOuterMass_eq_profileOuterMass`, preserving the exact original
profile weight, order and repeated coordinates. The full finite natural
prime-support sum therefore receives the same payment through
`absolute_natural_outer_payment`, with the unchanged quantifier order
“exists fixed h, eventually N, for all k, r and logQ”.

This resolves the natural-support sum dictionary at source level.
It does **not** identify that one-ambient sum with the old actual-history
mass/J expression or aggregate all history marks. The original
actual-rank supplier derives the bound for actual sources; this package
does not repeat or requalify that supplier.

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
   argument is introduced. The root subsequently located the historical membership overlay at
   `docs/source-only/20261112-resume/t07/list-membership-overlay/Part5OriginalH430ClassicalFixedClampGeometry.lean`
   (blob `68061ecf2efb284938d824e5240431916dbfcdb6`). It already repairs the
   original `mem_cons_self` application; the new core's two simp terms
   remain explicitly recorded as body changes.

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

The three thin modules have now passed the complete validation gates. The following paragraph preserves the failed-attempt history; it is superseded by the acceptance record below.
The initial three-module normal build compiled FrozenConstants and
PrimeDivisorFloorCore, then failed at four local expression/API sites in
RadialRoughMass. The second controlled normal build eliminated the first
three error sites; its only remaining error was the distinction between
a Real exponent 2 and a natural exponent 2 in the floor-square identity.
The current revision adds the existing pinned Mathlib lemma
`Real.rpow_two` at that exact rewrite.

API_REPAIRS.json retains both failed source versions and both complete
task stdout records. All 11 theorem statements are byte-for-byte unchanged.
The explicit numeral-conversion revision subsequently passed normal compilation and all post-compilation gates. The unchanged tuple, profile and natural consumers still have no compilation credit.

Further manuscript work includes the
old actual-history ordinary sum dictionaries, all history/mark multiplicities,
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

## Current three-module acceptance

Task `job_252a9d6dd37a40aba7f4d7dfda0b372a` normally compiled the repaired
RoughMass and reused the two previously successful core objects. Its later
controller stopped because its import classifier omitted the already accepted
FixedCompat module's own object. That was an evidence-classification error,
with no Lean source failure.

Task `job_316abd9abba34afe85edf8354c31637b` corrected the receiving
classification and completed all remaining gates with exit 0 in 26.56 seconds,
without recompiling any source. The 19,262 monitored borrowed cache parts
were unchanged, and all 19,202 actual imported facets were bound.

| Accepted module | All owned declarations |
|---|---:|
| `P2FiniteMarkedGamma5FrozenConstants` | 8 |
| `P2FiniteMarkedGamma5RadialRoughMass` | 32 |
| `P2MarkedPrimeDivisorFloorCore` | 2 |

The inventory includes private and generated declarations. It is not a count
of 42 newly proved mathematical theorems. The only observed axioms are
`Classical.choice`, `Quot.sound` and `propext`.

See `docs/verification/20261125-p2-9-radial/ACCEPTANCE.json` and
`postnormal/TASK_OUTPUT.txt` in that verification directory for exact
source and receipt hashes. The accepted RoughMass source SHA256 is
`7766fbca185e25e7380aee84e805cd3c35b94daaa8e6f7f98740ee3533fb67eb`.

The source comments and API_REPAIRS record preserve the historical
source-only preparation state. Current acceptance is determined by exact
source hashes and the later receipt. The tuple/profile/natural modules,
owner postimages and actual-history integration are not promoted by this
three-module result.

## Exact existing fibre proof relocation

The current TupleCount candidate imports `P2MarkedPrimeProductFibreCore`.
Its previous P5z import pulled in a 9,572-module receiving setup, including
24,504 facets outside the current qualified context. The new core copies
the two original Part3 tuple definitions, private helper and public fibre
proof byte-for-byte. No estimate is re-proved and no hypothesis is added.
The public FQNs are unchanged; the helper receives its new private module
owner. Only that one import in TupleCount changes.

The exact sources, reversible owner postimages and independent review are
in `docs/source-only/20261125-p2-9-prime-product-fibre-core/`.
The first core/consumer validation task
`job_f761e0d8b28e47369e915aa7d21f3347` compiled the thin core normally,
then stopped at an unused Wu2008DoubleSieve namespace in TupleCount's open
header. No kernel or full-owned credit was granted to that pair. The
minimal header repair is being revalidated under unchanged gates.
The three previously accepted sources and outputs remain unchanged.

The complete three-module textual receipt set is now published in
`docs/verification/20261125-p2-9-radial/qualified/`.
The 119-member frozen archive has SHA256
`4e6e5ecb0af9ddba5d42719b11440e1c14fc8ed408245f8f005eef02b40f718c`;
its complete binary body is published as `qualified/p29-radial-three-qualified-20261125.tar.xz` with transport receipt `qualified/ARCHIVE_TRANSPORT.json`. No additional compilation or mathematical credit is created by the export.


## Current two-consumer header repair

The exact current ProfileCollar source is `33196c7c3fc1c4aeac651871482bb142e55deca8` (SHA256 `64959b49ba41fc30534bcbd7d31d97ba8dd803ff7361ef97b69ec24f3297f93d`); NaturalMass is `5a22a4e7aeb47b39b7052e9a184703d577e5c112` (SHA256 `4cb852104310b03c4c1941d997558d9997de9ba8fe4cd3f503f00308a9d2affc`). Each deletes only the unused `Wu2008DoubleSieve` token from the combined `open` header. Imports and every declaration/proof remain byte-identical; root independently reconstructed both preimages. This addresses the same already-observed TupleCount header cause before the first compile of these two consumers. Source selection overrides earlier header snapshots; it does not add acceptance. Full receiving input binding and the original normal/kernel/full-owned gates remain pending.
