# Actual seed atlas ordinary excess

**SOURCE_ONLY_UNCOMPILED.** Formal, kernel, endpoint and new-native credit are all **0**. This packet contains no compiler run, cloud job, active-tree edit or branch update. The exact source blob was read back and matched byte for byte. Independent full-source mathematical review found no blocking issue; Lean elaboration and all acceptance gates remain outstanding.

## Delivered source

| Module | Git blob | SHA256 | Bytes | Lines |
|---|---|---|---:|---:|
| `ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasOrdinaryExcess` | `5b7090a10e0ac1a707a4119acae3f02ea170c109` | `902b62d0b1f1dfb3c67a124f7bb8398a29fdd437e6f661807fc5b651e3ddee69` | 17338 | 328 |

Repository path: `docs/source-only/20261125-p2-9-seed-atlas-ordinary-excess/ImbalancedChen/P2FiniteMarkedGamma5SeedAtlasOrdinaryExcess.lean`.

The public conclusion is `atlas_mass_le_exact_cell_plus_epsilon`. For fixed original root precision `n` and root tag, with `1/(n+1) ≤ 11/384`, each positive epsilon gives a fixed mesh function `m : Index 430 → Nat` such that, eventually in `N`, simultaneously for every `tau∈[0,1/12]` and `h∈(0,1/8]`,

`norm N * Σ v : Entry n, fixedWeight v.shape * Σ u∈originalPrimeTuples, actualFamilyWeight(v,u)`

`≤ norm N * Σ v : Entry n, fixedWeight v.shape * Σ u∈originalPrimeTuples, 1_exactCell(v,u) * originalPhysicalProfile(v,u) + epsilon.`

The left side is the existing `SeedAtlasFinitePP.weight` using the actual `planAt` and `acceptAt`. The main term retains coefficient **one**, the same entries, the same complete ordered prime tuples, the same marks, and the same `cellQ`.

## Exact source mask

The comparison uses `SeedCellFibre.exactCell` directly, from blob `6c30b9072c5c95dead4020b33303d1223ee3caaf`. This is the original root-prime cell, every old coordinate coprime to the target, and the literal selected predicate. Its native dictionary retains the complete original root code.

No complete-product coprime condition is imposed on this main term. In particular, fresh and tail factors may divide `N`. There is also no such arithmetic filter in the smooth Family weight on the left.

For root `U4`, the right-hand finite sum is definitionally the separate `SeedOrdinaryReindex.literalMass`. The already supplied `literalMass_eq_seedMass`, blob `189a61645dd730f8a6297e54b9e66f24334b5c9d`, identifies it with the original `seedMass ... completeProfile`. That dictionary is not reimplemented here.

## How the two errors are paid

The proof first expands the existing Family weight using `SeedCellReadout.actual_weight` at the original large-scale gate. The original profile gives `0≤profile≤1`. On its nonzero support, the original floor and product gate give every coordinate at least `cut N` and complete product at most `2*N`. The previous two-prime coordinate bound places the old logarithmic coordinates in the atlas cube. The original finite atom partition then bounds the readout by one.

There are three positive pointwise terms:

1. The original profile on `exactCell`.
2. A unit allowance for the original `noncoprimeTuples` carrier.
3. A unit allowance for the same `cellOuterTuples` proper-wall carrier.

Only the third branch assumes that the complete product is coprime to `N`. In that branch, divisibility gives the old-coordinate coprimality required by `exactCell`. A failed exact cell therefore belongs to the already constructed geometric spill carrier. The full-tuple `wallTuple` map is proved injective coordinate by coordinate and preserves its complete product. No injectivity of the product map is used.

The noncoprime branch uses `TargetExclusion.absolute_noncoprime_payment` at the original actual floor and rank ceiling. The total rank bound comes from **`Entry.v.property`**, not from a bound on the tail alone. No divisor-count, logarithmic-decay, product-fibre or prime-box proof is repeated.

For the proper branch, `SelectedCellWallPayment.exists_all_cells_outer_payment` already pays all root codes and all tails with one mesh per fixed shape/read index. Its reserved fresh position includes `r=0`. Repeated primes remain labelled throughout.

## Uniformity and fixed weights

Let `A` be the sum of the original nonnegative fixed marks over the finite `Entry n` type, and `C=A+1`. Both errors receive `eta=epsilon/(2*C)`. The final finite weighted error is at most `A*(2*eta)≤epsilon`. This also works for an empty family, when `A=0`.

All entries, their marks, the mesh function, the floor and the rank ceiling are fixed before the target threshold. The threshold is uniform in `tau`, in `h∈(0,1/8]`, and in every later prime tuple. No epsilon is allocated separately to a moving prime or history position. Each fixed entry may use its own Plan, as allowed by the existing Family receiver.

## Exact dependencies and owner selection

Direct imports are `SeedCellFibre` **6c30b9072c5c95dead4020b33303d1223ee3caaf** and `TargetExclusion` **68641a9d05fdd4ceafb60a22656d310e63ee2083**. The actual readout supplier is **e14cb3ff13229e0ead0789734be2359c131fa139**, and the original finite Entry/weight supplier is **26b5b5adeb17598892a01462180ff578c896d4b0**.

The complete registry inherits the current selection at baseline **12dd8b011185ef351a80bae40cd240993ad6f288**, then the exact selected-wall packet **656fb16b6015a522adfb038ca400bc5ccc7f35aa**. Select RootStrips **521b485f8167c760d816aa2e01ec137bad8a9bac**, CellAtlasStrips **9a0a6ad021f3ae1c455c2731d0451bf9011b7cee**, and the new readout-core owner postimages. Retain the current Tuple **56572a3ad02bb9c35c535d87800b164542cd3d2f**, ProfileCollar **33196c7c3fc1c4aeac651871482bb142e55deca8**, and NaturalMass **5a22a4e7aeb47b39b7052e9a184703d577e5c112** selections.

The historical and finite-fallback import closure is still a separate receiving-object qualification problem. Acceptance of individual thin suppliers does not qualify this new consumer.

## Manuscript and scope

The frozen [1106 argument, 359–407](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L359-L407) requires finite nonnegative families and fixed-precision positive smooth outer approximations. The [1106 sieve appendix, 1090–1101](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L1090-L1101) fixes the finite queries and positive floors before the target limit. This source fills the finite positive-sum and arithmetic-support transport between the already proved components.

It supplies an actual ordinary mass comparison with the exact seed-cell mask. It does not introduce a new `J`, invoke PP or distribution, qualify the full historical closure, or assert completion of W1/W2, P2.9, or a native H247 compatibility branch.
