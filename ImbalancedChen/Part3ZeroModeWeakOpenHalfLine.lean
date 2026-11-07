import ImbalancedChen.Part3ZeroModeWeakHalfLineTrace

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Interior-only local L2 weak data on (Y,infinity) have a single continuous
locally absolutely continuous representative. The proof uses countably
many nested intervals with left endpoints decreasing to Y. No endpoint
integrability, trace at Y, graph approximation, or Hardy estimate is assumed.
-/

namespace ImbalancedChen.Part3.ZeroModeWeakOpenHalfLine20261026b
noncomputable section
open MeasureTheory Set Filter
open ZeroModeRealPrimitiveWeak20261026b ZeroModeComplexPrimitiveWeak20261026b
open ZeroModeWeakIntervalTrace20261026b ZeroModeWeakHalfLineTrace20261026b

structure OpenHalfLineSobolevRepresentative (Y : ℝ) (f g : ℝ → ℂ) where
  function : ℝ → ℂ
  continuous : ContinuousOn function (Ioi Y)
  re_ac : ∀ a b, Y < a → a ≤ b →
    AbsolutelyContinuousOnInterval (fun x => (function x).re) a b
  im_ac : ∀ a b, Y < a → a ≤ b →
    AbsolutelyContinuousOnInterval (fun x => (function x).im) a b
  value_ae : ∀ᵐ x, x ∈ Ioi Y → f x = function x
  derivative_ae : ∀ᵐ x, x ∈ Ioi Y → HasDerivAt function (g x) x
  derivative_integrable : ∀ a b, Y < a → a ≤ b → IntervalIntegrable g volume a b
  fundamental : ∀ x y, Y < x → Y < y →
    function y - function x = ∫ t in x..y, g t

theorem nonempty_openHalfLineSobolevRepresentative {Y : ℝ} {f g : ℝ → ℂ}
    (hloc : ∀ a b, Y < a → a < b →
      MemLp f 2 (volume.restrict (Ioo a b)) ∧ MemLp g 2 (volume.restrict (Ioo a b)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi Y →
      (∫ x, deriv ψ x • f x) = -(∫ x, ψ x • g x)) :
    Nonempty (OpenHalfLineSobolevRepresentative Y f g) := by
  let A : ℕ → ℝ := fun n => Y + 1 / ((n : ℝ) + 2)
  let B : ℕ → ℝ := fun n => Y + (n : ℝ) + 2
  let z : ℝ := Y + 1
  have hden (n : ℕ) : 0 < (n : ℝ) + 2 := by positivity
  have hAY (n : ℕ) : Y < A n := by
    dsimp [A]
    exact lt_add_of_pos_right Y (div_pos zero_lt_one (hden n))
  have hA0 (n : ℕ) : A n ≤ A 0 := by
    have hi : 1 / ((n : ℝ) + 2) ≤ 1 / (2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [A]
    norm_num only [Nat.cast_zero, zero_add]
    linarith
  have hB0 (n : ℕ) : B 0 ≤ B n := by
    dsimp [B]
    norm_num only [Nat.cast_zero]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hAz (n : ℕ) : A n < z := by
    have ha : A 0 < z := by norm_num [A, z]
    exact (hA0 n).trans_lt ha
  have hzB (n : ℕ) : z < B n := by
    have hb : z < B 0 := by norm_num [B, z]
    exact hb.trans_le (hB0 n)
  have hAB (n : ℕ) : A n < B n := (hAz n).trans (hzB n)
  have hGn (n : ℕ) : IntervalIntegrable g volume (A n) (B n) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hAB n).le).mpr
      (MemLp.integrable (by norm_num) (hloc (A n) (B n) (hAY n) (hAB n)).2)
  let U (n : ℕ) : IntervalSobolevRepresentative (A n) (B n) f g :=
    Classical.choice (nonempty_intervalSobolevRepresentative_of_memLp (hAB n)
      (hloc (A n) (B n) (hAY n) (hAB n)).1
      (hloc (A n) (B n) (hAY n) (hAB n)).2
      (fun ψ hψ hψc hψs => hweak ψ hψ hψc (fun x hx =>
        (hAY n).trans (hψs hx).1)))
  let c : ℂ := (U 0).function z
  let F : ℝ → ℂ := coordinatePrimitive z g c
  have htrace (n : ℕ) : (U n).function z = c := by
    have hae : (U n).function =ᵐ[volume.restrict (Ioo (A 0) (B 0))] (U 0).function := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [(U n).value_ae, (U 0).value_ae] with x hn hzero hx
      have hxn : x ∈ Ioo (A n) (B n) :=
        ⟨(hA0 n).trans_lt hx.1, hx.2.trans_le (hB0 n)⟩
      exact (hn hxn).symm.trans (hzero hx)
    rw [restrict_Ioo_eq_restrict_Icc] at hae
    have hcontn : ContinuousOn (U n).function (Icc (A 0) (B 0)) :=
      (U n).continuous.mono (Icc_subset_Icc (hA0 n) (hB0 n))
    exact (Measure.eqOn_Icc_of_ae_eq (hAB 0).ne hae hcontn (U 0).continuous)
      ⟨(hAz 0).le, (hzB 0).le⟩
  have hFpoint (n : ℕ) {x : ℝ} (hx : x ∈ Icc (A n) (B n)) :
      F x = c + complexPrimitive z g x := by
    have hzu : z ∈ uIcc (A n) (B n) := by
      rw [uIcc_of_le (hAB n).le]
      exact ⟨(hAz n).le, (hzB n).le⟩
    have hxu : x ∈ uIcc (A n) (B n) := by simpa only [uIcc_of_le (hAB n).le] using hx
    exact coordinatePrimitive_eq_native ((hGn n).mono_set (uIcc_subset_uIcc hzu hxu)) c
      right_mem_uIcc
  have hFn (n : ℕ) : EqOn (U n).function F (Icc (A n) (B n)) := by
    intro x hx
    have hzu : z ∈ uIcc (A n) (B n) := by
      rw [uIcc_of_le (hAB n).le]
      exact ⟨(hAz n).le, (hzB n).le⟩
    have hxu : x ∈ uIcc (A n) (B n) := by simpa only [uIcc_of_le (hAB n).le] using hx
    have hAzint := (hGn n).mono_set (uIcc_subset_uIcc_left hzu)
    have hzxint := (hGn n).mono_set (uIcc_subset_uIcc hzu hxu)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hAzint hzxint
    have hzval := (U n).fundamental z ⟨(hAz n).le, (hzB n).le⟩
    rw [htrace n] at hzval
    rw [(U n).fundamental x hx, hFpoint n hx]
    unfold complexPrimitive
    linear_combination -hadd - hzval
  have hcover (a b : ℝ) (ha : Y < a) : ∃ n, A n < a ∧ b < B n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / (a - Y)) (b - Y))
    have hnA : 1 / (a - Y) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hnB : b - Y < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hmul : 1 < (n : ℝ) * (a - Y) :=
      (div_lt_iff₀ (sub_pos.mpr ha)).mp hnA
    refine ⟨n, ?_, ?_⟩
    · dsimp [A]
      have hinv : 1 / ((n : ℝ) + 2) < a - Y := by
        apply (div_lt_iff₀ (hden n)).mpr
        nlinarith
      linarith
    · dsimp [B]
      linarith
  have hFcontn (n : ℕ) : ContinuousOn F (Icc (A n) (B n)) := by
    have hzu : z ∈ uIcc (A n) (B n) := by
      rw [uIcc_of_le (hAB n).le]
      exact ⟨(hAz n).le, (hzB n).le⟩
    have hn : ContinuousOn (fun x => c + complexPrimitive z g x) (uIcc (A n) (B n)) :=
      continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval' (hGn n) hzu)
    have heq : EqOn F (fun x => c + complexPrimitive z g x) (Icc (A n) (B n)) :=
      fun x hx => hFpoint n hx
    have hn' : ContinuousOn (fun x => c + complexPrimitive z g x) (Icc (A n) (B n)) := by
      simpa only [uIcc_of_le (hAB n).le] using hn
    exact hn'.congr heq
  have hvalue : ∀ᵐ x, x ∈ Ioi Y → f x = F x := by
    have hall : ∀ᵐ x, ∀ n : ℕ, x ∈ Ioo (A n) (B n) → f x = (U n).function x :=
      ae_all_iff.mpr (fun n => (U n).value_ae)
    filter_upwards [hall] with x hx hxy
    obtain ⟨n, hAn, hnB⟩ := hcover x x hxy
    exact (hx n ⟨hAn, hnB⟩).trans (hFn n ⟨hAn.le, hnB.le⟩)
  have hgint (a b : ℝ) (ha : Y < a) (hab : a ≤ b) : IntervalIntegrable g volume a b := by
    rcases hab.eq_or_lt with rfl | hab
    · exact IntervalIntegrable.refl
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr
        (MemLp.integrable (by norm_num) (hloc a b ha hab).2)
  refine ⟨{
    function := F
    continuous := ?_
    re_ac := ?_
    im_ac := ?_
    value_ae := hvalue
    derivative_ae := ?_
    derivative_integrable := hgint
    fundamental := ?_ }⟩
  · intro x hx
    obtain ⟨n, hAn, hnB⟩ := hcover x x hx
    exact ((hFcontn n x ⟨hAn.le, hnB.le⟩).continuousAt
      (Icc_mem_nhds hAn hnB)).continuousWithinAt
  · intro a b ha hab
    obtain ⟨n, hAn, hnB⟩ := hcover a b ha
    have hzu : z ∈ uIcc (A n) (B n) := by
      rw [uIcc_of_le (hAB n).le]
      exact ⟨(hAz n).le, (hzB n).le⟩
    have hreal : IntervalIntegrable (fun t => (g t).re) volume (A n) (B n) :=
      ⟨(hGn n).1.re, (hGn n).2.re⟩
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c.re) (A n) (B n) :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c.re)).contDiffOn.absolutelyContinuousOnInterval
    have hac := hconst.add
      (hreal.absolutelyContinuousOnInterval_intervalIntegral (c := z) hzu)
    apply hac.mono
    rw [uIcc_of_le hab, uIcc_of_le (hAB n).le]
    exact Icc_subset_Icc hAn.le hnB.le
  · intro a b ha hab
    obtain ⟨n, hAn, hnB⟩ := hcover a b ha
    have hzu : z ∈ uIcc (A n) (B n) := by
      rw [uIcc_of_le (hAB n).le]
      exact ⟨(hAz n).le, (hzB n).le⟩
    have himag : IntervalIntegrable (fun t => (g t).im) volume (A n) (B n) :=
      ⟨(hGn n).1.im, (hGn n).2.im⟩
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c.im) (A n) (B n) :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c.im)).contDiffOn.absolutelyContinuousOnInterval
    have hac := hconst.add
      (himag.absolutelyContinuousOnInterval_intervalIntegral (c := z) hzu)
    apply hac.mono
    rw [uIcc_of_le hab, uIcc_of_le (hAB n).le]
    exact Icc_subset_Icc hAn.le hnB.le
  · have hall : ∀ᵐ x, ∀ n : ℕ, x ∈ Ioo (A n) (B n) → HasDerivAt F (g x) x := by
      apply ae_all_iff.mpr
      intro n
      filter_upwards [(hGn n).ae_hasDerivAt_integral] with x hx hxi
      have hxu : x ∈ uIcc (A n) (B n) := by
        rw [uIcc_of_le (hAB n).le]
        exact ⟨hxi.1.le, hxi.2.le⟩
      have hzu : z ∈ uIcc (A n) (B n) := by
        rw [uIcc_of_le (hAB n).le]
        exact ⟨(hAz n).le, (hzB n).le⟩
      have hn : HasDerivAt (fun t => c + complexPrimitive z g t) (g x) x := by
        simpa only [zero_add] using (hasDerivAt_const x c).add (hx hxu z hzu)
      apply hn.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with t ht
      exact hFpoint n ⟨ht.1.le, ht.2.le⟩
    filter_upwards [hall] with x hx hxy
    obtain ⟨n, hAn, hnB⟩ := hcover x x hxy
    exact hx n ⟨hAn, hnB⟩
  · intro x y hx hy
    obtain ⟨n, hAn, hnB⟩ := hcover (min x y) (max x y) (lt_min hx hy)
    have hxx : x ∈ Icc (A n) (B n) :=
      ⟨(hAn.trans_le (min_le_left x y)).le, (le_max_left x y).trans hnB.le⟩
    have hyy : y ∈ Icc (A n) (B n) :=
      ⟨(hAn.trans_le (min_le_right x y)).le, (le_max_right x y).trans hnB.le⟩
    have hxu : x ∈ uIcc (A n) (B n) := by simpa only [uIcc_of_le (hAB n).le] using hxx
    have hyu : y ∈ uIcc (A n) (B n) := by simpa only [uIcc_of_le (hAB n).le] using hyy
    have hAx := (hGn n).mono_set (uIcc_subset_uIcc_left hxu)
    have hxy := (hGn n).mono_set (uIcc_subset_uIcc hxu hyu)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hAx hxy
    rw [← hFn n hyy, ← hFn n hxx, (U n).fundamental y hyy, (U n).fundamental x hxx]
    linear_combination -hadd

/-- The representative is determined by the original value a.e. on the open
half-line; this statement intentionally supplies no trace at Y. -/
theorem OpenHalfLineSobolevRepresentative.unique_of_value_ae {Y : ℝ}
    {f g f' g' : ℝ → ℂ} (u : OpenHalfLineSobolevRepresentative Y f g)
    (v : OpenHalfLineSobolevRepresentative Y f' g')
    (hvalue : ∀ᵐ x, x ∈ Ioi Y → f x = f' x) :
    EqOn u.function v.function (Ioi Y) := by
  have hae : u.function =ᵐ[volume.restrict (Ioi Y)] v.function := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [u.value_ae, v.value_ae, hvalue] with x hu hv hff hx
    exact (hu hx).symm.trans ((hff hx).trans (hv hx))
  exact Measure.eqOn_open_of_ae_eq hae isOpen_Ioi u.continuous v.continuous

end
end ImbalancedChen.Part3.ZeroModeWeakOpenHalfLine20261026b
