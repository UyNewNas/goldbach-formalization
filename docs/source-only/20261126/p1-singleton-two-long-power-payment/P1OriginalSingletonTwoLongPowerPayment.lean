import ImbalancedChen.P1OriginalSingletonFixedScaleTransport
import ImbalancedChen.Part3TwoLongMellinLogBudget
import ImbalancedChen.P4BOriginalTwoLongActualScales

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

This is only the actual singleton specialization of the existing E4
monomial payment. The complete block scale X0, selected occurrence indices,
original cutoff Z and halfOrder X0 remain unchanged. No finite discrepancy
bound or rough restoration is assumed or proved here.

The old fixed_margin supplies epsilon = 1/16000 and theta = 1199/2000.
The old eventually_twoLong_E4_monomial supplies the entire power/log
payment. Actual geometry pays its M,Y,D,U,V premises. All fixed profile,
frequency, logarithmic and cutoff orders precede the physical-N threshold.

The P4 ActualScales import is used only for its existing numerical lemma.
If adopted, use the already recorded complementary NoMediumPairRows
postimage with the shared singleton finite geometry; do not compile the
unmigrated original provider alongside that shared owner. The inherited
source-only/Mellin/FixedM source boundary is not resolved by this leaf.
-/

namespace ImbalancedChen.P1OriginalSingletonTwoLongPowerPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale)
open Part3.TwoLongHBMellinBrunProfiles (pairCost)
open Part3.TwoLongMellinLogBudget (eventually_twoLong_E4_monomial)
open P1OriginalSingletonFixedScaleTransport
  (eventually_actual_singleton_fixed_scale_transport)
open P1OriginalSingletonFixedRectangleScale
  (eventually_actual_singleton_fixed_rectangle_level)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open P1Full87TrueDPolicyDelta (trueDDeltaSupport)

/-- The original actual rectangle pays the dominant two-long power term.
The physical threshold precedes kap, the original profile order, charts,
HB rows, tuples, occurrence positions and all historical modulus data.
Only one actual profile value is required nonzero. No aggregate or whole
rectangle activity is required, and i,k are never selected again.

The scalar estimate does not change any signed coefficient: the attached
level statement uses exactly the historical remainingModuli expression.
The two other power remainders and the factorial density term are outside
this conclusion. -/
theorem eventually_actual_singleton_twoLong_power_payment
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
        pairCost ((Real.log X0)^smoothOrder)⁻¹ U V ((Real.log X0)^frequencyOrder) *
          (M*Y^2*(D : ℝ)^(3/2 : ℝ))*(Real.log X0)^extraLog ≤
            X0/(Real.log X0)^accuracy := by
  have hfixed := P4BOriginalTwoLongActualScales.fixed_margin hzeta
  have heps : (0 : ℝ) < 1/16000 := by
    simpa only [P4BOriginalTwoLongActualScales.brunEpsilon] using hfixed.1
  have hmargin : 40*zeta+2*(1/16000 : ℝ)+3*(1199/2000 : ℝ)/2 < 1 := by
    simpa only [P4BOriginalTwoLongActualScales.brunEpsilon,
      P4BOriginalHighRankLocalLevel.theta] using hfixed.2.2.2
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_twoLong_E4_monomial smoothOrder frequencyOrder extraLog accuracy
      1 (by norm_num) zeta (1199/2000) (1/16000) heps hmargin)
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_fixed_scale_transport cutoffOrder
      (1/16000) heps hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*T))] with N htransport hrectangle hlarge
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  let X0 : ℝ := shortScale bs
  let M : ℝ := shortScale (fun a : ShortPositions i k => bs a.val)
  let U : ℝ := lower (bs i)
  let V : ℝ := lower (bs k)
  let Z := beforeHBCutoff cutoffOrder [cj]
  let Y := Z^(2*halfOrder X0+1)
  let D : ℕ := Nat.floor (X0^(1199/2000 : ℝ))
  obtain ⟨hx, hscale, _, _, hMpay, _, _, _, hZ, hY⟩ :=
    htransport kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, _, _, htrimX, _, _, _, _, _, _, hlevel⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  have hTX : T ≤ X0 := by linarith only [hlarge, htrimX]
  have hx0 : 0 < X0 := zero_lt_one.trans hx
  have hMnat : 0 < shortScale (fun a : ShortPositions i k => bs a.val) :=
    Finset.prod_pos (fun a _ => lower_pos (bs a.val))
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (Nat.succ_le_of_lt hMnat)
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast (Nat.succ_le_of_lt (lower_pos (bs i)))
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast (Nat.succ_le_of_lt (lower_pos (bs k)))
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hU0 : 0 ≤ U := zero_le_one.trans hU1
  have hV0 : 0 ≤ V := zero_le_one.trans hV1
  have hMU : (1 : ℝ) ≤ M*U := by
    simpa only [one_mul] using mul_le_mul hM1 hU1 (by norm_num : (0 : ℝ) ≤ 1) hM0
  have hMV : (1 : ℝ) ≤ M*V := by
    simpa only [one_mul] using mul_le_mul hM1 hV1 (by norm_num : (0 : ℝ) ≤ 1) hM0
  have hUx : U ≤ X0 := by
    calc
      U ≤ U*(M*V) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hMV hU0
      _ = X0 := by rw [hscale]; ring
  have hVx : V ≤ X0 := by
    calc
      V ≤ (M*U)*V := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMU hV0
      _ = X0 := hscale.symm
  have hY0 : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hD1 : 1 ≤ D := Nat.le_floor (Real.one_le_rpow hx.le (by norm_num))
  have hDpay : (D : ℝ) ≤ X0^(1199/2000 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hpay := hT X0 hTX
  refine ⟨hpay.2.1, hD1, ?_, ?_⟩
  · intro levelB old fresh cap w z q hq
    exact (hlevel levelB old fresh cap w z q hq).2
  · exact hpay.2.2 M Y D U V hM0 hY0 (Nat.cast_nonneg D) hMpay hY hDpay hU1 hV1
      (by simpa only [one_mul] using hUx) (by simpa only [one_mul] using hVx)

end
end ImbalancedChen.P1OriginalSingletonTwoLongPowerPayment
