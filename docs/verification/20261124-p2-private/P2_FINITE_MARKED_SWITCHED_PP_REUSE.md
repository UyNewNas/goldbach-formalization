# P2 finite marked switched-PP reuse check

Date: 2026-11-24. This is a source-level dependency check. No Lean source,
compiler, audit driver, or accepted object was changed; no compilation or
replay credit is added.

## Chosen unpaid substep and result

The chosen substep is the **bad Γ5 summand at the actual enhanced seed**
inside
`Part5OriginalH430SeedSameCarrierPP.switchedPPBalance`.
The source fixes `S := seedPositions N n .U4 t p` and
`Q := rootQ N n .U4 t p`; each occurrence retains its own
`d := wordProduct l` and `levelMark l`.

The existing exact definition, valid for both root constructors, is:

```lean
def switchedPPBalance {N n p dep : ℕ} {r : Root} {t : ℝ}
    (B : Finset (LevelIndex N n r t p dep)) : ℝ :=
  let Q := rootQ N n r t p
  ∑ l∈B,levelMark l*(switchedFibre true N Q (wordProduct l)-
    (K/4)*thetaConversion N (wordProduct l)*switchedFibre false N Q (wordProduct l))
```

All immediate finite identities needed to expose this debt already exist.
I found no additional small unconditional identity whose proof would pay
the actual enhanced Γ5 term. I therefore did not create a new Lean wrapper.
The remaining step needs admission and a distribution estimate for the
actual marked family; it is not resolved by reassociating a finite sum.

## Exact existing work to reuse

In `Part5OriginalH430SeedPurifiedPrimeFibres`, write
`M := roughNumbers ((N:ℝ)/(d*qs.prod)) (cutoff Q d (227/50))`.
Then `badFibre` sums over the original `qs ∈ badLabels N Q d`:

| Existing symbol | Exact work already present |
|---|---|
| `fibre` | The tested mass is `p5z_labelledPrimeMass M (fun m => (d*qs.prod)*m) (fun _ => 1) N`; the untested mass is the same labelled integer carrier. |
| `rough_receiver_eq_prime_fibre` | The actual quotient/source bijection restores the additive prime, under the original `N ≥ 4`, evenness, and positive marked product hypotheses. |
| `raw_fibre`, `raw_bad` | The untested mass equals the original inclusive rough-integer cardinality and `ordinaryBad`, respectively. |
| `prime_bad_purified`, `restricted_prime_purified` | Actual repeated-prefix and target-divisor-center errors are preserved and explicitly separated. |
| `SeedSameCarrierPP.converted_eq_untested` | The original Γ5 and Γ9–21 prices equal the sum of the same untested fibres, retaining list occurrences, same `Q`, same `d`, and same mark. |
| `SeedSameCarrierPP.purify_on_original_marks` | Those errors are paid at the actual selected marks; the resulting upper bound still contains `switchedPPBalance`. |
| `SeedSameCarrierPP.actual_seed_and_four_rounds_at_common_prime_restriction` | The original seed and four rounds are already assembled with `ordinaryAP S + switchedPPBalance S` on the right. Neither term is asserted to be paid. |

`P2EnhancedBadGamma5ArithmeticGeometry.original_unit_partition` already
proves the inclusive unit/nonunit split. It uses the original ordered prime
lists and does not replace list multiplicity by an assumed injective product.
`P2EnhancedBadGamma5CostTheta.original_badGamma5_cost_theta` already bounds
the **ordinary** converted Γ5 mass. This bound supplies the priced ordinary
cost; it does not upper-bound the tested-minus-priced difference. In
particular, an upper bound on the subtracted ordinary term cannot supply
an upper bound on `switchedPPBalance`.

The normalizer is also already exact:

```lean
thetaConversion N d =
  4 * logarithmicIntegral N * (d:ℝ) * wuSingularSeries (d*N) /
    ((N:ℝ) * (Nat.totient d:ℝ))
```

It must not be replaced definitionally by a constant independent of `d`.
The coefficient in the real debt remains the manuscript's `K/4`.

## Why the nearby suppliers do not close this chosen case

`Part5OriginalH430ClassicalBadPairPayment.actual_Gamma5_at_common_mass`
already supplies a real classical Γ5 payment. Its statement uses
`rootQ N n .U3 τ p`, `p ∈ clampPrimes N`, and `B ⊆ clampPrimes N`.
Its proof goes through the actual classical signed-AP pool. This is
valuable existing work; replacing `.U3` and the single external prime
by `.U4` and an inherited marked product is not a definitional substitution.
No new acceptance of this source-only module is claimed here.

`Part5OriginalH430ClassicalSmoothNativeFamily.family` is a genuine
`Family 200` construction, with `aStar := 1/90`, `lower := 1/2`,
`upper := 2`, and an integer extension. However its ambient occurrence
set comes from
`ClassicalSmoothAllOccurrences.words j := secondFunctionalMotherGammaWords (9+j.val)`
for `j : Fin 13`. It does not supply the chosen bad Γ5 family by itself.
Its existing `original_hb_pullback` and `original_lambda_atlas` should be
reused for their own ambient family, not assigned to a different carrier.

The newly accepted Part3 proper-power pair theorem pays
`Eprime − EVM` for the existing bare four-wall outer-pair profile. As
documented in `P2_ACTUAL_PAIR_REUSE_FEASIBILITY.md`, its rank two is not
the real sieve-scale parameter ν. The marked Γ5 source retains an old
prefix, two fresh ordered primes, a rough residual integer including 1,
and the selected history's mark. Neither its carrier nor its arithmetic
mask is the outer-pair ramp. Its `EVM` distribution remains unpaid even
for the matching outer-pair application.

## Minimum remaining input, with quantifiers kept at the manuscript strength

For this substep, the unresolved source-level connection is an actual
admissible integer extension/smoothing of the selected finite marked Γ5
family, with its original prefix and rough residual decomposition, tied
back to the literal tested and untested fibres above. It must preserve:

1. the complete product `d * qs.prod * m` and the additive prime at `N`;
2. the original ordered/list labels, multiplicities, marks, and `Q`;
3. the cutoff `cutoff Q d (227/50)`, including the unit residual case;
4. the same physical moduli and attached coefficient ρ in every resulting
   coprime, prime-to-VM, and VM distribution term;
5. the literal `thetaConversion N d` and original `K/4` price.

An actual P3 supply for this admitted family must then bound the remaining
VM distribution term. Assuming `hWeightEq`, a family-admission conclusion,
or the desired PP estimate as a new argument does not close this gap.
This does **not** demand a theorem uniform over every moving history:
the manuscript first fixes the finite marked query family and its outside
parameters, then takes `N` sufficiently large. The present review proves
neither that the manuscript statement is false nor that its estimates
can be filled by a finite algebraic identity. It identifies the unpaid
actual-family admission/distribution step.

The root agent separately checked `ordinaryAP`; this report does not
change or attempt to replace that route. The two genuine error terms
remain distinct at the same selected σ and same `Q`.

## Manuscript and reviewed source provenance

Manuscript commit: `a988cba584d803ae2856a0de50efb582f4f3dd6a` in
`chen-imbalanced-semiprimes`, release `paper/release-20261106/en`.
`sieve-appendix.tex` 494–531 fixes σ(B), `R = Q/B`, and the feedback
family; 634–660 defines the pair's rough quotient and the actual additive
prime source; 763–792 retains the bad Γ5 term and inclusive switched
mass; 1090–1101 fixes the finite query family before `N → ∞`.
The file SHA256 is
`15c9f561b870edb43ec1de3a8adf88b0b4561982f0617b58b26b1de966f9f9d8`.

The following locators are relative to the goldbach-formalization root.

| Source file | SHA256 |
|---|---|
| `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/seed_pair_closure/Part5OriginalH430SeedSameCarrierPP.lean` | `689ea0aa4a88049843a7ef80ea1ec14c9256053ac614c15e41ee9abf14b3a4c7` |
| `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/seed_pair_closure/Part5OriginalH430SeedPurifiedPrimeFibres.lean` | `8943b9224c032da8b9653d572d9835e7472b3e7d7c66c7ba2b32adff334d0a81` |
| `docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5ArithmeticGeometry.lean` | `53f0e246929d51ee338b56880d4ae773dcf0bacda0e2f251357cbe9e940d0019` |
| `docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5CostTheta.lean` | `fa051e0e42d1488bde226d89f3794c4653fb4f1bb34750dcf63a9f5209fee041` |
| `docs/source-only/20261102-resume-30o/enhanced_switch_mass/P2EnhancedSwitchedTrueNormalization.lean` | `1082e7e6ed3b23a9828aeb68cf2a2072a0b13e377799988825fb4fd8ebb1a11d` |
| `docs/source-only/20261112-resume/t07/switched-next/Part5OriginalH430ClassicalBadPairPayment.lean` | `3c9a2ecfe4171f29dedd02ee80aaf13d18904077c6322ca416d5f9274c22daf0` |
| `docs/source-only/20261112-resume/t07/classical-fixed-box/smooth-word/hb-licence/Part5OriginalH430ClassicalSmoothAllOccurrences.lean` | `7230baed47233c158b53cccc76b53fc24230572bb00cf36d6d9b382b29456500` |
| `docs/source-only/20261112-resume/t07/classical-fixed-box/smooth-word/hb-licence/Part5OriginalH430ClassicalSmoothNativeFamily.lean` | `1714887be342346487eec3594a791499f63b0fa02d70ca64d4182801c2c7c393` |

Search scope: the existing final dependency and upstream-reuse reviews,
followed by exact symbol searches in active `ImbalancedChen/` and all
`docs/source-only/` Lean sources for `switchedPPBalance`, `badFibre`, and
their actual receivers. Absence statements above are confined to these
reviewed source paths; this was not a new whole-site search.
