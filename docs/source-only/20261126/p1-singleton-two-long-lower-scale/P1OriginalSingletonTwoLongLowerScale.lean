import ImbalancedChen.P1OriginalSingletonFixedScaleTransport

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original singleton dictionary supplies the SAME two long occurrence
positions.  Its strict originalMediumHigh condition, together with the
actual scalar-profile chart window, gives a uniform fixed power lower
bound at X0 = the product of ALL original block lower endpoints.

The only constant transport is X0 <= 2 * R cj.  The fixed exponent gap
1/3 - 1/4 = 1/12 absorbs 2^(1/3) before the physical-N threshold.  No
new selection of the pair, aggregate activity, or desired error estimate
is assumed.  No Brun, P2, Fourier, or factorial estimate is reproved here.
-/

namespace ImbalancedChen.P1OriginalSingletonTwoLongLowerScale
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumHigh)
open P5Z.ExactOriginalSmoothDyadicPartition (scales)
open Part3.TwoLongActualHBShortMass (shortScale)
open P4BOriginalNoMediumPairRows (longPositions)
open P1OriginalSingletonFixedRectangleScale
  (eventually_actual_singleton_fixed_rectangle_level)
open P1OriginalSingletonFixedScaleTransport (scalarProfile_chart_window)

/-- The fixed 1/12 exponent gap pays the factor from x <= 2*R.
The threshold precedes R and the particular long lower endpoint U. -/
theorem eventually_chart_long_lower_scale {zeta : ℝ} (hzeta : 0 ≤ zeta) :
    ∀ᶠ x : ℝ in atTop, ∀ R U : ℝ,
      1 ≤ R → x ≤ 2*R → R^((1/3 : ℝ)+zeta/4) ≤ U →
      x^(1/4 : ℝ) ≤ U := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (_root_.tendsto_rpow_atTop (by norm_num : 0 < (1/12 : ℝ))).eventually
      (eventually_ge_atTop ((2 : ℝ)^(1/3 : ℝ)))]
    with x hx hconstant
  intro R U hR hxR hU
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hC : 0 < (2 : ℝ)^(1/3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hmult : (2 : ℝ)^(1/3 : ℝ) * x^(1/4 : ℝ) ≤
      (2 : ℝ)^(1/3 : ℝ) * R^(1/3 : ℝ) := by
    calc
      (2 : ℝ)^(1/3 : ℝ) * x^(1/4 : ℝ) ≤
          x^(1/12 : ℝ) * x^(1/4 : ℝ) :=
        mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hxp.le _)
      _ = x^(1/3 : ℝ) := by rw [← Real.rpow_add hxp]; norm_num
      _ ≤ (2*R)^(1/3 : ℝ) :=
        Real.rpow_le_rpow hxp.le hxR (by norm_num)
      _ = (2 : ℝ)^(1/3 : ℝ) * R^(1/3 : ℝ) :=
        Real.mul_rpow (by norm_num) (zero_le_one.trans hR)
  have hsmall : x^(1/4 : ℝ) ≤ R^(1/3 : ℝ) :=
    le_of_mul_le_mul_left hmult hC
  exact hsmall.trans ((Real.rpow_le_rpow_of_exponent_le hR (by linarith)).trans hU)

/-- The actual dictionary pair has two long lower endpoints at the SAME
fixed rectangle scale.  The physical threshold precedes kap, B, the chart,
HB row, rectangle, active tuple, and both supplied occurrence indices.

The pair condition is exactly the already supplied longPositions equality.
It does not assume the power lower bounds being proved, whole-rectangle
activity, or any final distribution-error estimate. -/
theorem eventually_actual_singleton_twoLong_lower_scale
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap B N cj kap0 (completeProduct ns) ≠ 0 →
      longPositions (originalMediumHigh zeta [cj]) bs = {i,k} →
      let X0 : ℝ := shortScale bs
      X0^(1/4 : ℝ) ≤ (lower (bs i) : ℝ) ∧
        X0^(1/4 : ℝ) ≤ (lower (bs k) : ℝ) := by
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_chart_long_lower_scale hzeta0.le)
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_fixed_rectangle_level
    hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*T))] with N hlevel hlarge
  intro kap hkap B cj j bs ns i k hj hik hns hactive hpair
  let X0 : ℝ := shortScale bs
  obtain ⟨_, _, _, htrimX, _, _, _, _, hwindow, _, _⟩ :=
    hlevel kap hkap B cj j bs ns i k hj hik hns hactive
  have hTX : T ≤ X0 := by linarith only [hlarge, htrimX]
  have hxR : X0 ≤ 2 * P5Z.ExactOriginalSmoothDyadicPartition.R cj :=
    (hwindow ns hns).1.trans
      (scalarProfile_chart_window kap kap0 B N cj (completeProduct ns) hactive).2
  have hR : (1 : ℝ) ≤ P5Z.ExactOriginalSmoothDyadicPartition.R cj :=
    one_le_pow₀ (by norm_num)
  have hlong (a : Fin (2*(j+1))) (ha : a ∈ ({i,k} : Finset (Fin (2*(j+1))))) :
      (P5Z.ExactOriginalSmoothDyadicPartition.R cj)^((1/3 : ℝ)+zeta/4) ≤
        (lower (bs a) : ℝ) := by
    have hm : a ∈ longPositions (originalMediumHigh zeta [cj]) bs := by
      rw [hpair]
      exact ha
    have hhigh := (Finset.mem_filter.mp hm).2
    simpa only [originalMediumHigh, scales, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] using hhigh.le
  exact ⟨hT X0 hTX _ _ hR hxR (hlong i (by simp)),
    hT X0 hTX _ _ hR hxR (hlong k (by simp))⟩

end
end ImbalancedChen.P1OriginalSingletonTwoLongLowerScale
