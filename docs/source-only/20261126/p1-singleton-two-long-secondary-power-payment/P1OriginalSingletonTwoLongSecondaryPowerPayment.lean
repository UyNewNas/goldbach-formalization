import ImbalancedChen.P1OriginalSingletonTwoLongPowerPayment
import ImbalancedChen.P1OriginalSingletonTwoLongLowerScale

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

This leaf pays the two secondary power terms M*(U+V)*Y and M*Y^2 in
coefficient-appendix.tex (1106), lines 797--821. It keeps the original
complete block scale X0=M*U*V, occurrence indices i,k, cutoff Z,
halfOrder X0, and historical modulus filter.

The original dictionary's exact longPositions equality supplies the
actual long-block hypothesis. The separate actual lower-scale owner
pays its X0^(1/4) consequence; no lower bound or target error is assumed.
The existing pairCost power-payment theorem absorbs the cross term.
The square term follows monotonically from the already supplied dominant
M*Y^2*D^(3/2) payment, since its original D is at least one.
The two bare fixed-log terms are also paid: the original fixed-log
supplier absorbs the cross term, and Y <= U+V bounds the bare square
term by that cross term. No lower bound for pairCost is used.

All fixed orders and small parameters precede the physical-N threshold.
Only one actual tuple's scalarProfile is required nonzero. This file
does not prove a rough discrepancy identity, a density bound, or any
whole-rectangle activity statement. The inherited source-only and
unique-owner adoption boundaries remain unchanged.
-/

namespace ImbalancedChen.P1OriginalSingletonTwoLongSecondaryPowerPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale)
open Part3.TwoLongHBMellinBrunProfiles (pairCost pairCost_nonneg)
open Part3.TwoLongMellinLogBudget
  (eventually_pairCost_power_payment eventually_fixed_log_le_power)
open P4BOriginalNoMediumPairRows (longPositions)
open P1OriginalSingletonFixedScaleTransport
  (eventually_actual_singleton_fixed_scale_transport)
open P1OriginalSingletonFixedRectangleScale
  (eventually_actual_singleton_fixed_rectangle_level)
open P1OriginalSingletonTwoLongPowerPayment
  (eventually_actual_singleton_twoLong_power_payment)
open P1OriginalSingletonTwoLongLowerScale
  (eventually_actual_singleton_twoLong_lower_scale)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open P1Full87TrueDPolicyDelta (trueDDeltaSupport)

/-- The two secondary power terms on the original singleton rectangle.
The same two occurrence positions remain fixed throughout the proof;
units and repeated factor values are retained. The attached level is
the unchanged historical remainingModuli/trueDDeltaSupport expression. -/
theorem eventually_actual_singleton_twoLong_secondary_power_payment
    (accuracy smoothOrder frequencyOrder extraLog cutoffOrder : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4 * (1 + kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (Bprofile cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap Bprofile N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      longPositions (originalMediumHigh zeta [cj]) bs = {i,k} →
      let X0 : ℝ := shortScale bs
      let M : ℝ := shortScale (fun a : ShortPositions i k => bs a.val)
      let U : ℝ := lower (bs i)
      let V : ℝ := lower (bs k)
      let Z := beforeHBCutoff cutoffOrder [cj]
      let Y := Z^(2*halfOrder X0+1)
      let D : ℕ := Nat.floor (X0^(1199/2000 : ℝ))
      1 ≤ Real.log X0 ∧ 1 ≤ D ∧
        (∀ (levelB : ℝ) (old fresh : List ℕ → Bool)
          (cap : ℕ) (w z : ℝ) (q : ℕ),
          q ∈ remainingModuli levelB N (trueDDeltaSupport old fresh N cap w z) → q ≤ D) ∧
        (pairCost ((Real.log X0)^smoothOrder)⁻¹ U V ((Real.log X0)^frequencyOrder) *
          (M*(U+V)*Y)*(Real.log X0)^extraLog ≤ X0/(Real.log X0)^accuracy) ∧
        (pairCost ((Real.log X0)^smoothOrder)⁻¹ U V ((Real.log X0)^frequencyOrder) *
          (M*Y^2)*(Real.log X0)^extraLog ≤ X0/(Real.log X0)^accuracy) ∧
        ((M*(U+V)*Y)*(Real.log X0)^extraLog ≤ X0/(Real.log X0)^accuracy) ∧
        (M*Y^2)*(Real.log X0)^extraLog ≤ X0/(Real.log X0)^accuracy := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_pairCost_power_payment smoothOrder frequencyOrder extraLog accuracy
      1 (by norm_num) (eta := 1/8) (by norm_num)).and
      ((eventually_fixed_log_le_power 2 (by norm_num) 0 (eta := 1/16) (by norm_num)).and
        (eventually_fixed_log_le_power 1 (by norm_num) (extraLog+accuracy)
          (eta := 1/8) (by norm_num))))
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_twoLong_power_payment
      accuracy smoothOrder frequencyOrder extraLog cutoffOrder hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_scale_transport cutoffOrder
      (1/16000) (by norm_num) hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_lower_scale hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*T))]
      with N hpower htransport hrectangle hlong hlarge
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
  let X0 : ℝ := shortScale bs
  let M : ℝ := shortScale (fun a : ShortPositions i k => bs a.val)
  let U : ℝ := lower (bs i)
  let V : ℝ := lower (bs k)
  let Z := beforeHBCutoff cutoffOrder [cj]
  let Y := Z^(2*halfOrder X0+1)
  let D : ℕ := Nat.floor (X0^(1199/2000 : ℝ))
  obtain ⟨hlog, hD1, hlevel, hdominant⟩ :=
    hpower kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨hx, hscale, _, _, _, _, _, _, hZ, hY⟩ :=
    htransport kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, _, _, htrimX, _, _, _, _, _, _, _⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  obtain ⟨hUlong, hVlong⟩ :=
    hlong kap hkap Bprofile cj j bs ns i k hj hik hns hactive hpair
  have hTX : T ≤ X0 := by linarith only [hlarge, htrimX]
  obtain ⟨hbudget, htwoRaw, hrawLogRaw⟩ := hT X0 hTX
  have htwo : (2 : ℝ) ≤ X0^(1/16 : ℝ) := by
    simpa only [pow_zero, mul_one] using htwoRaw
  have hrawLog : (Real.log X0)^(extraLog+accuracy) ≤ X0^(1/8 : ℝ) := by
    simpa only [one_mul] using hrawLogRaw
  have hx0 : 0 < X0 := zero_lt_one.trans hx
  have hMnat : 0 < shortScale (fun a : ShortPositions i k => bs a.val) :=
    Finset.prod_pos (fun a _ => lower_pos (bs a.val))
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (Nat.succ_le_of_lt hMnat)
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast (Nat.succ_le_of_lt (lower_pos (bs i)))
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast (Nat.succ_le_of_lt (lower_pos (bs k)))
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hU0 : 0 ≤ U := zero_le_one.trans hU1
  have hV0 : 0 ≤ V := zero_le_one.trans hV1
  have hMU1 : (1 : ℝ) ≤ M*U := by
    simpa only [one_mul] using mul_le_mul hM1 hU1 (by norm_num : (0 : ℝ) ≤ 1) hM0
  have hMV1 : (1 : ℝ) ≤ M*V := by
    simpa only [one_mul] using mul_le_mul hM1 hV1 (by norm_num : (0 : ℝ) ≤ 1) hM0
  have hUx : U ≤ X0 := by
    calc
      U ≤ U*(M*V) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hMV1 hU0
      _ = X0 := by rw [hscale]; ring
  have hVx : V ≤ X0 := by
    calc
      V ≤ (M*U)*V := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMU1 hV0
      _ = X0 := hscale.symm
  have hMU : M*U ≤ X0^(3/4 : ℝ) := by
    apply le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hx0 (1/4 : ℝ))
    calc
      (M*U)*X0^(1/4 : ℝ) ≤ (M*U)*V :=
        mul_le_mul_of_nonneg_left hVlong (mul_nonneg hM0 hU0)
      _ = X0 := hscale.symm
      _ = X0^(3/4 : ℝ)*X0^(1/4 : ℝ) := by
        rw [← Real.rpow_add hx0]
        norm_num
  have hMV : M*V ≤ X0^(3/4 : ℝ) := by
    apply le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hx0 (1/4 : ℝ))
    calc
      (M*V)*X0^(1/4 : ℝ) ≤ (M*V)*U :=
        mul_le_mul_of_nonneg_left hUlong (mul_nonneg hM0 hV0)
      _ = X0 := by rw [hscale]; ring
      _ = X0^(3/4 : ℝ)*X0^(1/4 : ℝ) := by
        rw [← Real.rpow_add hx0]
        norm_num
  have hsum : M*(U+V) ≤ 2*X0^(3/4 : ℝ) := by
    calc
      M*(U+V) = M*U+M*V := by ring
      _ ≤ X0^(3/4 : ℝ)+X0^(3/4 : ℝ) := add_le_add hMU hMV
      _ = 2*X0^(3/4 : ℝ) := by ring
  have hY0 : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hcross : M*(U+V)*Y ≤ X0^(1-(1/8 : ℝ)) := by
    calc
      M*(U+V)*Y ≤ (2*X0^(3/4 : ℝ))*X0^(1/16000 : ℝ) :=
        mul_le_mul hsum hY hY0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hx0.le _))
      _ = 2*X0^((3/4 : ℝ)+1/16000) := by
        rw [mul_assoc, ← Real.rpow_add hx0]
      _ ≤ X0^(1/16 : ℝ)*X0^((3/4 : ℝ)+1/16000) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hx0.le _)
      _ = X0^((1/16 : ℝ)+3/4+1/16000) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      _ ≤ X0^(1-(1/8 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hcost0 := pairCost_nonneg ((Real.log X0)^smoothOrder)⁻¹ U V
    ((Real.log X0)^frequencyOrder)
  have hlog0 : 0 ≤ (Real.log X0)^extraLog :=
    pow_nonneg (zero_le_one.trans hlog) _
  have hDcast : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hDpow : (1 : ℝ) ≤ (D : ℝ)^(3/2 : ℝ) :=
    Real.one_le_rpow hDcast (by norm_num)
  have hsquare : M*Y^2 ≤ M*Y^2*(D : ℝ)^(3/2 : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hDpow (mul_nonneg hM0 (sq_nonneg Y))
  have hYU : Y ≤ U := hY.trans
    ((Real.rpow_le_rpow_of_exponent_le hx.le
      (by norm_num : (1/16000 : ℝ) ≤ 1/4)).trans hUlong)
  have hYsum : Y ≤ U+V := hYU.trans (le_add_of_nonneg_right hV0)
  have hsquareCross : M*Y^2 ≤ M*(U+V)*Y := by
    calc
      M*Y^2 = (M*Y)*Y := by ring
      _ ≤ (M*(U+V))*Y := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hYsum hM0) hY0
  have hraw (term : ℝ) (hterm : term ≤ X0^(1-(1/8 : ℝ))) :
      term*(Real.log X0)^extraLog ≤ X0/(Real.log X0)^accuracy := by
    apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hlog) accuracy)).2
    calc
      term*(Real.log X0)^extraLog*(Real.log X0)^accuracy =
          term*(Real.log X0)^(extraLog+accuracy) := by rw [pow_add, mul_assoc]
      _ ≤ X0^(1-(1/8 : ℝ))*X0^(1/8 : ℝ) := mul_le_mul hterm hrawLog
        (pow_nonneg (zero_le_one.trans hlog) _) (Real.rpow_nonneg hx0.le _)
      _ = X0 := by
        rw [← Real.rpow_add hx0]
        norm_num
  refine ⟨hlog, hD1, hlevel, ?_, ?_, hraw _ hcross, hraw _ (hsquareCross.trans hcross)⟩
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcross hcost0) hlog0).trans
        (hbudget.2.2 U V hU1 hV1
          (by simpa only [one_mul] using hUx)
          (by simpa only [one_mul] using hVx))
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare hcost0) hlog0).trans hdominant

end
end ImbalancedChen.P1OriginalSingletonTwoLongSecondaryPowerPayment
