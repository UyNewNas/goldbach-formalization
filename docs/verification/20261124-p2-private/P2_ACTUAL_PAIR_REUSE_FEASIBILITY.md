# P2 actual-pair reuse feasibility — 2026-11-24

## Decision

The accepted P3 actual-pair family uses exactly the smooth weight already written in the outer-pair receiver. The weight/profile and prime-product pushforward identities already exist. No new identity lemma or renamed wrapper is needed.

That outer-pair weight is not the native P2 Ω3 `indexedWeight`, nor does the manuscript identify it with the fixed marked pair family. No new Lean source, compilation, replay, or acceptance credit was produced by this review. The actual VM discrepancy and full PP remain unpaid by the P3 proper-power theorem.

## Frozen P3 source and existing literal receiver

P3 head: `ef1479c272bdd6b24800fa10409d793f0a2fe95c`.

- `ImbalancedChen/Part3ProperPowerActualPairFamily.lean`, accepted at `d23f13b1d55423ede87153a147f77bbd227fa916`, SHA-256 `d663cf07c61ac7f2844faf7303aea42e502b305f7a47b56b725a9edbcf8c4ca0`.
- Acceptance provenance and exact theorem types are retained in `docs/source-only/20261124-p2-wu-uniform/UPSTREAM_REUSE_REVIEW_P3_INCREMENT_20261124.json` (SHA-256 `8cca75c33ee162c2c24e7f8acfb982529ffacd6b9b0010f79c30997387b2ee53`). This review reuses that published evidence without rerunning it.

The actual weight is

```lean
P4B.smoothPhysicalPairOuterRamp b N
  (manuscriptHalfProductCutoff kappa N) width
```

with `manuscriptHalfProductCutoff kappa N = 2 * N^(1-kappa)` and integer tuple domain `Fin 2 → Fin (N+1)`.

This is already the literal weight in:

1. `ImbalancedChen/P4BActualSmoothPhysicalPPA3.lean`, definition `ActualSmoothPhysicalPPA3`.
2. `docs/source-only/20261123-yellow-node-owners/y07_uniform_upper/ImbalancedChen/P4BOriginalFineAttachedUpper.lean`, `Selection.upper_of_attached_PP`.

Both retain the actual `attachedUpperModuli` and `attachedUpperCoefficient`. Their full PP premise is not proved by a prime-minus-VM estimate.

Existing exact identities to reuse:

- `P4B.smoothPhysicalPairOuterRamp_eq_profile`.
- `P4B.smoothPhysicalPairOuterRamp_eq_primeVariableProfile`.
- `P4BActualSmoothFamilyWitness.selected_weight_eq_prime_profile` (`rfl`, no weight-equality hypothesis).
- `P4BLabelledOuterPushforward.signed_productWeight_eq_primeProductSignedError`, preserving the actual complete product image and one signed sum in the same rho. `productCarrier N` is the image of all labelled prime pairs, not an imposed `m ≤ N` truncation.

The three local profile/margin modules have different whole-file hashes from the accepted P3 import selection. Nine relevant definitions were compared individually and are **exactly equal as text**: `smoothPhysicalPairOuterRamp`, `smoothPhysicalProfileMargin`, `smoothPhysicalProfile`, `physicalProductWallScale`, `physicalPairMargins`, `positivePrimeOrthant`, `primeVariableLogPoint`, `smoothPrimeVariableProfile`, and `primeTuplePoint`. The entire local Gate, LogGeometry, PairDictionary and cutoff modules match their P3 accepted import hashes. This establishes the source-level object match; it does not transfer acceptance to different local whole-file bytes.

## Existing proper-power payment already present

The repository already contains:

`docs/source-only/20261123-yellow-node-owners/y06_same_rho_pp/ImbalancedChen/P4BOriginalAllWidthProperPowers.lean`

Its `eventually_all_width_properPower_sum_norm` pays the sum of norms of `properPowerReserve` over the original rank-two chart bank. It retains the actual attached signed coefficient, all permitted widths, the exact coprime mean and full-product diagonal. Its genuine remaining range premise is

```lean
(actualActiveUpperCap nu r beta f cap N : ℝ) ≤ (N : ℝ)^theta
```

with `0 ≤ theta < 1`. It does not assume the desired proper-power conclusion or PP.

The adjacent `P4BOriginalFineRetainedCalibration.eventually_proper_removed` already applies that payment to the selected fine retention. `P4BOriginalFineAttachedRetained.attached_support` proves the actual selected nonzero coefficient support is below `N^(599/1000)`; its private `active_cap` provides the required cap. Therefore an additional copy of this mathematical payment is unnecessary. These existing source-only files receive no new compile/replay credit here.

The full displayed `attachedUpperModuli` must not be confused with the nonzero active support. Existing `P5Z.ProperPowerPhysicalPolynomialPayment.physical_signedRow_eq_active` removes zero-coefficient rows and the cancelling q=1 row; `physicalRho_norm_le_one` and `physicalQ_subset_activeCap` keep the same coefficient and prove the necessary bounds. Passing the full displayed modulus set to the new P3 theorem without its required cap would be invalid.

## Rank two is not the sieve-scale parameter `nu`

P3's two original prime/integer slots are represented by the literal natural number `2`. The real parameter `nu` in the attached coefficient controls powers `N^(nu*r)`, `N^(nu*epsilon)` and `N^(nu*epsilon^2)`. It must not be set to 2 merely because the source has two slots. Likewise the P3 theorem's modulus-support multiplier `K` is not the sieve constant `681/100`.

## Why the native/fixed marked P2 source is different

`P2NativeOmega3RankTupleReceiver.indexedWeight` is

```lean
p5z_markedPhysicalWeight (indexedFamily k delta r N b) (fun _ => 1)
```

where `p5z_markedPhysicalWeight S W t = if t ∈ S then W t else 0`, and `indexedFamily_prime` proves the family contains only prime tuples. The underlying complete word is

```lean
List.ofFn a.1 ++ [a.2.2.2.1,a.2.2.1,a.2.1] ++ a.2.2.2.2.primeFactorsList
```

It has the old prefix slots, three distinguished primes, and the canonical tail. Its length is at least three, so the rank-two branch is empty by these definitions. This observation is source reasoning, not a newly compiled theorem. The actual outer ramp is a geometric smooth function on integer tuples, including effective VM tuples containing proper prime powers. Replacing it by a prime-only family indicator changes that integer extension.

The fixed marked pair in the manuscript retains `sigma(B)`, the prefix B, the residual quotient `(N-p)/B`, and the roughness condition on the remaining quotient. These are not the outer bad-semiprime four-wall object. Existing pair source receivers also retain their own root/descendant ceilings and masks. A prime-only identity on a subset would not establish the needed identity on effective VM integer support.

## Exact manuscript locators

Repository `UyNewNas/chen-imbalanced-semiprimes`, fixed commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`, directory `paper/release-20261106/en`.

- `argument.tex`, `sec:current-transfer`, lines 1124–1167: the final `B_b(N)` outer-pair passage. Its original conditions are `r ≤ q`, `q^b < r`, `2 N^(1-kappa0) ≤ rq < N`. The log-coordinate substitution at 1144–1148 gives the four walls. Lines 100–120, 304–306 and 400–407 preserve the allowed family, actual rho bounds, outside mass and precision order.
- `coefficient-appendix.tex`, lines 323–331: the geometric weighted discrepancy has no extra prime filter inserted into its integer extension. Lines 513–524: prime to Lambda/log replacement, proper-power reciprocal saving and the separate complete-product=N diagonal payment.
- `sieve-appendix.tex`, `sv:finite-feedback`, lines 494–531 and 634–660: fixed `sigma(B)`, `R=Q/B`, and `Q_d(y;n)=1_(d|n) 1_(P^-(n/d)≥y)` with `n=(N-p)/B`. Lines 763–792 retain bad Gamma5 and the switched unit-face mass. Lines 1090–1101 fix the finite query family before N tends to infinity; they do not identify it with the bad-semiprime four-wall source.

The sharp manuscript upper wall is strict, the geometric indicator uses a closed wall, and the smooth outer support can exceed N. Existing majorization/outside-mass and diagonal handling must be retained; this review does not claim literal equality of the original sharp count and the smooth weight. When an outer receiver uses target `N=2n`, that is the complete even target and is not the marked prefix B or residual quotient.

## Source fingerprints

All paths below are relative to `goldbach-p2`, except the three manuscript paths relative to the fixed manuscript version directory.

| Source | SHA-256 |
| --- | --- |
| `ImbalancedChen/P4BActualSmoothPhysicalPPA3.lean` | `9fb3d84c56fb047f57d10f73092df7b135c37ed3e2ca57be16a984579b08d573` |
| `ImbalancedChen/P4BActualSmoothFamilyWitness.lean` | `d4b57ae26030d218abc51f1cbced22a65d22da2b67e9e58ae6e6d38c59fa0208` |
| `ImbalancedChen/P4BLabelledOuterPushforward.lean` | `e7bc4867d454032921170f1ffdbe484d86d29bd13ea52795cc6cd5625dcd4074` |
| `y07_uniform_upper/ImbalancedChen/P4BOriginalFineAttachedUpper.lean` | `df408b9aa888b3f09dff72db76221faa004c33dba029a5c69e2e297b9f15dc61` |
| `y07_uniform_upper/ImbalancedChen/P4BOriginalFineAttachedRetained.lean` | `39c9fb0d6ac0b1cd06755fdc69bf0c4a1c20a920bf782aa38ae498fe2dee2c66` |
| `y06_same_rho_pp/ImbalancedChen/P4BOriginalAllWidthProperPowers.lean` | `aa0e9f821dab0f33d88104fd62454ace546b27ab8bced94d466f3608857f9da3` |
| `y06_same_rho_pp/ImbalancedChen/P4BOriginalFineRetainedCalibration.lean` | `7c0a1f4f44723b05f0a61314fff5304f7ad068040fb133201b408303af7916e1` |
| `20261028-resume-30c/transfer_power/P5ProperPowerPhysicalPolynomialPayment.lean` | `36caa118411cb8ce26ec9d7c5eef64c3e8dc3f608eed8e02c537a753e1091eee` |
| `P2NativeOmega3RankTupleReceiver.lean` in the 20261121 receiver directory | `6ec68a0008464374fdc6e3810ea31d2216d095a291afa45aa1b575b1a544c6b3` |
| `P2NativeOmega3ExpandedPrimeWords.lean` in the same directory | `49b1d17c55aefccc3fe769cd41e37acc734f59028a74b0e656687752935aa07d` |
| `argument.tex` | `87f5b5f2e25082e00b2b04d8ecc684630d64846912457dc0adade1a36fd67182` |
| `coefficient-appendix.tex` | `267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440` |
| `sieve-appendix.tex` | `15c9f561b870edb43ec1de3a8adf88b0b4561982f0617b58b26b1de966f9f9d8` |

The y06/y07 shorthand is under `docs/source-only/20261123-yellow-node-owners/`; the 20261028 shorthand is under `docs/source-only/`. The receiver directory is `docs/source-only/20261121-resume/manuscript-distribution-and-receivers/ImbalancedChen/`.

The remaining analytic term is the actual VM discrepancy. The result `|E_prime-E_VM| = o(N/log^A N)` does not by itself bound `|E_prime|`, supply actual auxiliary SW, or close the finite marked P2 terminal. No new assumption or axiom was introduced for any of these inputs.
