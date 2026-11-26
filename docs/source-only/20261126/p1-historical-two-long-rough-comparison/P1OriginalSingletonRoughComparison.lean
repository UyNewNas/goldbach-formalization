import ImbalancedChen.P1OriginalHistoricalTwoLongRoughComparison
import ImbalancedChen.P1OriginalSingletonActualBrunDensity

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

This caller supplies the finite historical rough comparison with the actual
singleton block scale, original rough cutoff and growing Brun order. The
finite scalar gates are consequences of the existing scale and density
theorems, rather than assumptions about the desired discrepancy.

The original shortSequence, ordered short positions, historical Q/rho and
single exact coprime mean are unchanged. The conclusion compares smooth
long profiles with their upper/upper Brun core. It does not identify these
profiles with a sharp block, restore Fourier tails or close the Atlas sum.
All inherited missing-source and unique-owner adoption boundaries remain.
-/

namespace ImbalancedChen.P1OriginalSingletonRoughComparison
noncomputable section
open Classical Filter
open scoped BigOperators SchwartzMap
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile rowRoles)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open P5Z.ActualHBRoughBrunFinite (gapDensity chartPrimes)
open OriginalOneLongE5FiniteBudget (brunEpsilon)
open Part3.RoughSlotCharacterLift20261026b (smallPrimes)
open Part3.TwoLongActualHBShortMass
  (ShortPositions shortScale shortSupport shortSequence)
open Part3.TwoLongHBMellinBrunProfiles (leftMellin rightMellin)
open P4BOriginalPositiveLongEnvelope (envelopeSchwartz meanPrice)
open P4BOriginalEnvelopePolynomialPayment (p2Price)
open P4BOriginalPairMeanNorm (densityLog)
open P1OriginalHistoricalTwoLongP2
  (historicalModuli historicalRowCore momentBudget)
open P1OriginalHistoricalTwoLongRoughComparison
  (historicalRoughSum reciprocalMoment historical_shortSequence_rough_comparison)
open P1OriginalSingletonFixedScaleTransport
  (eventually_actual_singleton_fixed_scale_transport)
open P1OriginalSingletonFixedRectangleScale
  (eventually_actual_singleton_fixed_rectangle_level)
open P1OriginalSingletonActualBrunDensity
  (eventually_actual_singleton_twoLong_density_payment)

/-- All finite Brun/E1 gates at the SAME actual singleton scale. In
particular the factorial gap is proved at most one by cancelling the
positive full scale from the existing actual-cutoff density payment.
No threshold depends on the chart, original profile order, HB row,
selected positions, historical policies, modulus or Mellin frequencies. -/
theorem eventually_actual_singleton_rough_comparison_gates (cutoffOrder : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (Bprofile cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap Bprofile N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      let X0 : ℝ := shortScale bs
      let Z := beforeHBCutoff cutoffOrder [cj]
      let D : ℕ := Nat.floor (X0^(1199/2000 : ℝ))
      1 < X0 ∧ 1 ≤ Z ∧
        Z^(2*halfOrder X0+1) ≤ X0 ∧
        brunEpsilon (halfOrder X0) (smallPrimes Z) ≤ 1 ∧
        (∀ a : ShortPositions i k, 2*(lower (bs a.val) : ℝ) ≤ X0) ∧
        ∀ (levelB : ℝ) (old fresh : List ℕ → Bool)
          (cap : ℕ) (w z : ℝ) (q : ℕ),
          q ∈ historicalModuli levelB old fresh N cap w z → q ≤ D := by
  filter_upwards [eventually_actual_singleton_fixed_scale_transport cutoffOrder
      1 (by norm_num) hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_density_payment cutoffOrder 0 0
      1 1 (by norm_num) (by norm_num) hkappa hsmall hzeta htrim]
    with N htransport hrectangle hdensity
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  let X0 : ℝ := shortScale bs
  let Z := beforeHBCutoff cutoffOrder [cj]
  obtain ⟨hx, _, _, _, _, hcap, _, _, hZ, hY⟩ :=
    htransport kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlevel⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  obtain ⟨hscale, _, hpaid⟩ :=
    hdensity kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  have hgap : gapDensity Z (halfOrder X0) ≤ 1 := by
    have hmul : X0 * gapDensity Z (halfOrder X0) ≤ X0 * 1 := by
      simpa only [one_mul, pow_zero, mul_one, div_one, ← hscale] using hpaid
    exact (mul_le_mul_left (zero_lt_one.trans hx)).mp hmul
  refine ⟨hx, hZ, ?_, ?_, hcap, ?_⟩
  · simpa only [Real.rpow_one] using hY
  · simpa only [gapDensity, chartPrimes, smallPrimes] using hgap
  · intro levelB old fresh cap w z q hq
    exact (hlevel levelB old fresh cap w z q hq).2

/-- The finite rough comparison on an actual singleton rectangle, with
all scalar gates supplied. The original signed short pushforward is
inserted, its mass is obtained from shortSequence_mass, and the original
physical history supplies the modulus class and .5995 local endpoint.

The profile label/log flags can subsequently be specialized by the
existing two-long dictionary. No sharp-profile or Fourier identity is
asserted here. The physical threshold is uniform in delta, both real
frequencies, the short frequencies and all historical parameters. -/
theorem eventually_actual_singleton_rough_comparison (cutoffOrder : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (Bprofile cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap Bprofile N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ)
        (w z L delta t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
        (xi : Fin (2*(j+1)) → ℝ),
      ∀ (hd : 0 < delta) (hs : delta ≤ 1/4),
      let X0 : ℝ := shortScale bs
      let U : ℝ := lower (bs i)
      let V : ℝ := lower (bs k)
      let Z := beforeHBCutoff cutoffOrder [cj]
      let J := halfOrder X0
      let Y := Z^(2*J+1)
      let D : ℕ := Nat.floor (X0^(1199/2000 : ℝ))
      let shortBlocks := fun a : ShortPositions i k => bs a.val
      let shortCutoffs := fun _ : ShortPositions i k => hbCutoff cj
      let shortFrequencies := fun a : ShortPositions i k => xi a.val
      let shortRoles := fun a : ShortPositions i k => rowRoles j a.val
      let alpha := shortSequence shortBlocks Z shortCutoffs shortFrequencies shortRoles
      let muBound := (shortScale shortBlocks : ℝ) *
        (1+Real.log X0)^Fintype.card (ShortPositions i k)
      let E := envelopeSchwartz hd hs U
      let F := envelopeSchwartz hd hs V
      ‖historicalRoughSum levelB old fresh N cap w z L
          (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
          U V Z (shortSupport shortBlocks) alpha -
        historicalRowCore levelB old fresh N cap w z L Z J false false
          delta U V t₁ t₂ label log₁ log₂
          shortBlocks shortCutoffs shortFrequencies shortRoles‖ ≤
        2*p2Price E F*Y^2*muBound*momentBudget D +
          2*muBound*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
            (2*U*V*brunEpsilon J (smallPrimes Z)*densityLog X0 +
              2*densityLog X0*(U+V)*Y + 2*Y^2) := by
  filter_upwards [eventually_actual_singleton_rough_comparison_gates
    cutoffOrder hkappa hsmall hzeta htrim] with N hgates
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
    levelB old fresh cap w z L delta t₁ t₂ label log₁ log₂ xi hd hs
  obtain ⟨hx, hZ, hY, hgap, hcap, hlevel⟩ :=
    hgates kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  have hU : (0 : ℝ) < lower (bs i) := by exact_mod_cast lower_pos (bs i)
  have hV : (0 : ℝ) < lower (bs k) := by exact_mod_cast lower_pos (bs k)
  exact historical_shortSequence_rough_comparison levelB old fresh N cap
    (Nat.floor ((shortScale bs : ℝ)^(1199/2000 : ℝ))) w z L
    (fun q hq => hlevel levelB old fresh cap w z q hq)
    hZ hd hs hU hV hx.le (halfOrder (shortScale bs : ℝ)) hgap hY
    t₁ t₂ label log₁ log₂ hx.le (fun a : ShortPositions i k => bs a.val)
    (fun _ => hbCutoff cj) (fun a => xi a.val) (fun a => rowRoles j a.val) hcap

end
end ImbalancedChen.P1OriginalSingletonRoughComparison
