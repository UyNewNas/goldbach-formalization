import ImbalancedChen.P1OriginalSingletonFixedScaleTransport

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The cutoff in this file is the actual Z, not roughZ X0. The finite alphabet
is chartPrimes Z and the order remains 2*halfOrder X0+1. The existing
gap_is_superlog and eventually_gap_budget pay the factorial and logarithmic
estimates. Only a uniform harmonic-envelope comparison and the actual
singleton scale/threshold dictionary are added here.

No discrepancy bound, aggregate activity, rough restoration or new Brun
estimate is an assumption. All constants, logarithmic orders and cutoff
orders precede the physical-N threshold. The inherited source-only supply
and its remaining import boundaries are unchanged.
-/

namespace ImbalancedChen.P1OriginalSingletonActualBrunDensity
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.ActualHBRoughBrunFinite
open P5Z.ActualHBRoughBrunRates (halfOrder)
open OriginalOneLongE5FiniteBudget Part3.BrunFactorialRecurrenceE1
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale)
open P1OriginalSingletonFixedScaleTransport
  (eventually_actual_singleton_fixed_scale_transport)
open P1OriginalSingletonFixedRectangleScale
  (eventually_actual_singleton_fixed_rectangle_level)

/-- One natural-scale threshold works for every actual prime alphabet with
1 <= Z <= n. The comparison uses the common envelope Hbar(n)=2*loglog(n),
not the smaller alphabet belonging to roughZ(n). The old scalar gap budget
is used with its original growing order. -/
theorem eventually_uniform_actual_cutoff_gap_budget
    (C : ℝ) (hC : 0 ≤ C) (logOrder accuracy : ℕ)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) ∧
      ∀ Z : ℝ, 1 ≤ Z → Z ≤ (n : ℝ) →
        C*(n : ℝ)*gapDensity Z (halfOrder (n : ℝ))*
          (Real.log (n : ℝ))^logOrder ≤
            eta*(n : ℝ)/(Real.log (n : ℝ))^accuracy := by
  let Hbar : ℕ → ℝ := fun n => 2*OriginalOneLongExplicitBrunRates.L2 n
  have hHbar : ∀ᶠ n : ℕ in atTop,
      0 ≤ Hbar n ∧ Hbar n ≤ 2*OriginalOneLongExplicitBrunRates.L2 n := by
    filter_upwards [OriginalOneLongExplicitBrunRates.tendsto_L2.eventually
      (eventually_ge_atTop (0 : ℝ))] with n hL
    refine ⟨?_, le_rfl⟩
    dsimp [Hbar]
    positivity
  have hsuper := OriginalOneLongExplicitBrunRates.gap_is_superlog Hbar hHbar
  have hbudget := OriginalOneLongSupportAbsorption.eventually_gap_budget
    (OriginalOneLongExplicitBrunRates.gap Hbar) C hC hsuper
    logOrder accuracy eta heta
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hbudget,
    hcast.eventually P5Z.ActualHBRoughBrunRates.eventually_real_chart_harmonic,
    eventually_one_le_nat_log] with n hpaid hH hlog
  refine ⟨hlog, ?_⟩
  intro Z hZ hZn
  have hHZ0 : 0 ≤ chartHarmonic (chartPrimes Z) := by
    unfold chartHarmonic
    positivity
  have hHZ : chartHarmonic (chartPrimes Z) ≤ Hbar n := by
    have hh := hH (chartPrimes Z) (chartPrimes_prime Z) (by
      intro p hp
      exact ((mem_chartPrimes (zero_le_one.trans hZ) p).mp hp).2.trans hZn)
    simpa only [Hbar, OriginalOneLongExplicitBrunRates.L2,
      P5Z.ActualHBRoughBrunRates.loglog] using hh
  have hpow : chartHarmonic (chartPrimes Z) ^
        OriginalOneLongExplicitBrunRates.order n ≤
      (Hbar n)^OriginalOneLongExplicitBrunRates.order n :=
    pow_le_pow_left₀ hHZ0 hHZ _
  have hgap : gapDensity Z (halfOrder (n : ℝ)) ≤
      OriginalOneLongExplicitBrunRates.gap Hbar n := by
    have hh := div_le_div_of_nonneg_right hpow
      (show (0 : ℝ) ≤ (Nat.factorial (OriginalOneLongExplicitBrunRates.order n) : ℝ)
        from Nat.cast_nonneg _)
    simpa only [gapDensity, brunEpsilon, halfOrder,
      P5Z.ActualHBRoughBrunRates.loglog, OriginalOneLongExplicitBrunRates.gap,
      OriginalOneLongExplicitBrunRates.order, OriginalOneLongExplicitBrunRates.L2] using hh
  calc
    _ ≤ C*(n : ℝ)*(OriginalOneLongExplicitBrunRates.gap Hbar n)*
        (Real.log (n : ℝ))^logOrder :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap (mul_nonneg hC (Nat.cast_nonneg n)))
        (pow_nonneg (zero_le_one.trans hlog) _)
    _ ≤ _ := hpaid

/-- The literal singleton two-long density term uses the original full
block scale M*U*V=X0, actual cutoff and prime alphabet, and halfOrder X0.
The physical threshold precedes every profile order, chart, row, tuple and
the two already-selected positions. Only one actual scalar profile value
is required nonzero. This is a scalar payment, not a finite-error bound. -/
theorem eventually_actual_singleton_twoLong_density_payment
    (cutoffOrder logOrder accuracy : ℕ) (C eta : ℝ)
    (hC : 0 ≤ C) (heta : 0 < eta)
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
      let M : ℝ := shortScale (fun a : ShortPositions i k => bs a.val)
      let U : ℝ := lower (bs i)
      let V : ℝ := lower (bs k)
      let Z := beforeHBCutoff cutoffOrder [cj]
      X0 = M*U*V ∧ 1 ≤ Real.log X0 ∧
        C*(M*U*V)*gapDensity Z (halfOrder X0)*(Real.log X0)^logOrder ≤
          eta*X0/(Real.log X0)^accuracy := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_uniform_actual_cutoff_gap_budget C hC logOrder accuracy eta heta)
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_fixed_scale_transport cutoffOrder
      1 (by norm_num) hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*(T : ℝ)))]
    with N htransport hrectangle hlarge
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  let X0 : ℝ := shortScale bs
  let M : ℝ := shortScale (fun a : ShortPositions i k => bs a.val)
  let U : ℝ := lower (bs i)
  let V : ℝ := lower (bs k)
  let Z := beforeHBCutoff cutoffOrder [cj]
  obtain ⟨_, hscale, _, _, _, _, _, _, hZ, hY⟩ :=
    htransport kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, _, _, htrimX, _, _, _, _, _, _, _⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  have hTX : (T : ℝ) ≤ X0 := by linarith only [hlarge, htrimX]
  have hTn : T ≤ shortScale bs := by
    change (T : ℝ) ≤ (shortScale bs : ℝ) at hTX
    exact_mod_cast hTX
  have hYx : Z^(2*halfOrder X0+1) ≤ X0 := by
    simpa only [Real.rpow_one] using hY
  have hZx : Z ≤ X0 := by
    calc
      Z = 1*Z := (one_mul Z).symm
      _ ≤ Z^(2*halfOrder X0)*Z :=
        mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ Z^(2*halfOrder X0) from one_le_pow₀ hZ)
          (zero_le_one.trans hZ)
      _ = Z^(2*halfOrder X0+1) := (pow_succ Z (2*halfOrder X0)).symm
      _ ≤ X0 := hYx
  have hpaid := hT (shortScale bs) hTn
  have hscale' : X0 = M*U*V := hscale
  refine ⟨hscale', hpaid.1, ?_⟩
  change C*(M*U*V)*gapDensity Z (halfOrder X0)*(Real.log X0)^logOrder ≤
    eta*X0/(Real.log X0)^accuracy
  rw [← hscale']
  exact hpaid.2 Z hZ hZx

end
end ImbalancedChen.P1OriginalSingletonActualBrunDensity
