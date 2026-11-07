import ImbalancedChen.Part3ZeroModeWeakIntervalTrace

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Countable patching of genuine finite-interval weak representatives on [Y,infinity).
The local L2 assumptions explicitly reach the lower endpoint: for every b>Y,
both weak coordinates belong to L2(Y,b). This is the endpoint extension
hypothesis, not merely local integrability strictly inside (Y,infinity).
The lower trace is derived by overlap uniqueness. No graph closure or held
Hardy inequality is used.
-/

namespace ImbalancedChen.Part3.ZeroModeWeakHalfLineTrace20261026b
noncomputable section
open MeasureTheory Set Filter
open ZeroModeRealPrimitiveWeak20261026b ZeroModeComplexPrimitiveWeak20261026b
open ZeroModeWeakIntervalTrace20261026b

def coordinatePrimitive (Y : ℝ) (g : ℝ → ℂ) (c : ℂ) (x : ℝ) : ℂ :=
  ⟨c.re + realPrimitive Y (fun t => (g t).re) x,
    c.im + realPrimitive Y (fun t => (g t).im) x⟩

theorem coordinatePrimitive_eq_native {Y b : ℝ} {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume Y b) (c : ℂ) {x : ℝ} (hx : x ∈ uIcc Y b) :
    coordinatePrimitive Y g c x = c + complexPrimitive Y g x := by
  apply Complex.ext
  · simp only [coordinatePrimitive, Complex.add_re, complexPrimitive_re hg hx]
  · simp only [coordinatePrimitive, Complex.add_im, complexPrimitive_im hg hx]

structure HalfLineSobolevRepresentative (Y : ℝ) (f g : ℝ → ℂ) where
  function : ℝ → ℂ
  continuous : ContinuousOn function (Ici Y)
  re_ac : ∀ b, Y < b → AbsolutelyContinuousOnInterval (fun x => (function x).re) Y b
  im_ac : ∀ b, Y < b → AbsolutelyContinuousOnInterval (fun x => (function x).im) Y b
  value_ae : ∀ᵐ x, x ∈ Ioi Y → f x = function x
  derivative_ae : ∀ᵐ x, x ∈ Ioi Y → HasDerivAt function (g x) x
  derivative_integrable : ∀ b, Y < b → IntervalIntegrable g volume Y b
  fundamental : ∀ x ∈ Ici Y, function x = function Y + ∫ t in Y..x, g t

/-- Local L2 weak data extending up to Y give one continuous locally absolutely
continuous representative, including an honest lower endpoint trace. -/
theorem nonempty_halfLineSobolevRepresentative {Y : ℝ} {f g : ℝ → ℂ}
    (hloc : ∀ b, Y < b → MemLp f 2 (volume.restrict (Ioo Y b)) ∧
      MemLp g 2 (volume.restrict (Ioo Y b)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi Y →
      (∫ x, deriv ψ x • f x) = -(∫ x, ψ x • g x)) :
    Nonempty (HalfLineSobolevRepresentative Y f g) := by
  let B : ℕ → ℝ := fun n => Y + (n : ℝ) + 1
  have hB (n : ℕ) : Y < B n := by
    dsimp [B]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hGn (n : ℕ) : IntervalIntegrable g volume Y (B n) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hB n).le).mpr
      (MemLp.integrable (by norm_num) (hloc (B n) (hB n)).2)
  let U (n : ℕ) : IntervalSobolevRepresentative Y (B n) f g :=
    Classical.choice (nonempty_intervalSobolevRepresentative_of_memLp (hB n)
      (hloc (B n) (hB n)).1 (hloc (B n) (hB n)).2
      (fun ψ hψ hψc hψs => hweak ψ hψ hψc (hψs.trans Ioo_subset_Ioi_self)))
  let c : ℂ := (U 0).function Y
  let F : ℝ → ℂ := coordinatePrimitive Y g c
  have hB0 (n : ℕ) : B 0 ≤ B n := by
    dsimp [B]
    norm_num only [Nat.cast_zero]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have htrace (n : ℕ) : (U n).function Y = c := by
    have hae : (U n).function =ᵐ[volume.restrict (Ioo Y (B 0))] (U 0).function := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [(U n).value_ae, (U 0).value_ae] with x hn hz hx
      exact (hn ⟨hx.1, hx.2.trans_le (hB0 n)⟩).symm.trans (hz hx)
    rw [restrict_Ioo_eq_restrict_Icc] at hae
    have hcontn : ContinuousOn (U n).function (Icc Y (B 0)) :=
      (U n).continuous.mono (Icc_subset_Icc le_rfl (hB0 n))
    exact (Measure.eqOn_Icc_of_ae_eq (hB 0).ne hae hcontn (U 0).continuous)
      ⟨le_rfl, (hB 0).le⟩
  have hFn (n : ℕ) : EqOn (U n).function F (Icc Y (B n)) := by
    intro x hx
    rw [(U n).fundamental x hx, htrace n]
    exact (coordinatePrimitive_eq_native (hGn n) c
      (by simpa only [uIcc_of_le (hB n).le] using hx)).symm
  have hvalue : ∀ᵐ x, x ∈ Ioi Y → f x = F x := by
    have hall : ∀ᵐ x, ∀ n : ℕ, x ∈ Ioo Y (B n) → f x = (U n).function x :=
      ae_all_iff.mpr (fun n => (U n).value_ae)
    filter_upwards [hall] with x hx hxy
    obtain ⟨n, hn⟩ := exists_nat_gt (x - Y)
    have hxBn : x < B n := by dsimp [B]; linarith
    exact (hx n ⟨hxy, hxBn⟩).trans (hFn n ⟨hxy.le, hxBn.le⟩)
  have hG (b : ℝ) (hb : Y < b) : IntervalIntegrable g volume Y b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mpr
      (MemLp.integrable (by norm_num) (hloc b hb).2)
  have hFcont (b : ℝ) (hb : Y < b) : ContinuousOn F (Icc Y b) := by
    have hn : ContinuousOn (fun x => c + complexPrimitive Y g x) (uIcc Y b) :=
      continuousOn_const.add (complexPrimitive_continuousOn (hG b hb))
    have heq : EqOn F (fun x => c + complexPrimitive Y g x) (uIcc Y b) :=
      fun x hx => coordinatePrimitive_eq_native (hG b hb) c hx
    simpa only [uIcc_of_le hb.le] using hn.congr heq
  have hFY : F Y = c := by
    apply Complex.ext <;> simp [F, coordinatePrimitive, realPrimitive]
  refine ⟨{
    function := F
    continuous := ?_
    re_ac := ?_
    im_ac := ?_
    value_ae := hvalue
    derivative_ae := ?_
    derivative_integrable := hG
    fundamental := ?_ }⟩
  · intro x hx
    have hb : Y < x + 1 := by linarith
    have hc := hFcont (x + 1) hb x ⟨hx, by linarith⟩
    apply hc.mono_of_mem_nhdsWithin
    have hi : Iio (x + 1) ∈ 𝓝[Ici Y] x :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
    apply mem_of_superset (inter_mem self_mem_nhdsWithin hi)
    intro z hz
    exact ⟨hz.1, hz.2.le⟩
  · intro b hb
    have hi : IntervalIntegrable (fun t => (g t).re) volume Y b :=
      ⟨(hG b hb).1.re, (hG b hb).2.re⟩
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c.re) Y b :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c.re)).contDiffOn.absolutelyContinuousOnInterval
    exact hconst.add (hi.absolutelyContinuousOnInterval_intervalIntegral (c := Y) (by simp))
  · intro b hb
    have hi : IntervalIntegrable (fun t => (g t).im) volume Y b :=
      ⟨(hG b hb).1.im, (hG b hb).2.im⟩
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c.im) Y b :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c.im)).contDiffOn.absolutelyContinuousOnInterval
    exact hconst.add (hi.absolutelyContinuousOnInterval_intervalIntegral (c := Y) (by simp))
  · have hall : ∀ᵐ x, ∀ n : ℕ, x ∈ Ioo Y (B n) → HasDerivAt F (g x) x := by
      apply ae_all_iff.mpr
      intro n
      filter_upwards [(hGn n).ae_hasDerivAt_integral] with x hx hxi
      have hxu : x ∈ uIcc Y (B n) := by
        rw [uIcc_of_le (hB n).le]
        exact ⟨hxi.1.le, hxi.2.le⟩
      have hn : HasDerivAt (fun t => c + complexPrimitive Y g t) (g x) x := by
        simpa only [zero_add] using
          (hasDerivAt_const x c).add (hx hxu Y (by simp))
      apply hn.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with t ht
      exact coordinatePrimitive_eq_native (hGn n) c
        (by rw [uIcc_of_le (hB n).le]; exact ⟨ht.1.le, ht.2.le⟩)
    filter_upwards [hall] with x hx hxy
    obtain ⟨n, hn⟩ := exists_nat_gt (x - Y)
    exact hx n ⟨hxy, by dsimp [B]; linarith⟩
  · intro x hx
    rw [hFY]
    have hb : Y < x + 1 := by linarith
    exact coordinatePrimitive_eq_native (hG (x + 1) hb) c
      (by rw [uIcc_of_le hb.le]; exact ⟨hx, by linarith⟩)

/-- FTC on any two finite heights, in either order, with the genuine weak
derivative and no smooth approximation hypothesis. -/
theorem HalfLineSobolevRepresentative.fundamental_subinterval {Y : ℝ}
    {f g : ℝ → ℂ} (u : HalfLineSobolevRepresentative Y f g)
    {x y : ℝ} (hx : Y ≤ x) (hy : Y ≤ y) :
    u.function y - u.function x = ∫ t in x..y, g t := by
  let b : ℝ := max x y + 1
  have hb : Y < b := by
    dsimp [b]
    linarith [le_max_left x y]
  have hxu : x ∈ uIcc Y b := by
    rw [uIcc_of_le hb.le]
    exact ⟨hx, by dsimp [b]; linarith [le_max_left x y]⟩
  have hyu : y ∈ uIcc Y b := by
    rw [uIcc_of_le hb.le]
    exact ⟨hy, by dsimp [b]; linarith [le_max_right x y]⟩
  have hG := u.derivative_integrable b hb
  have hYx := hG.mono_set (uIcc_subset_uIcc_left hxu)
  have hxy := hG.mono_set (uIcc_subset_uIcc hxu hyu)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hYx hxy
  rw [u.fundamental y hy, u.fundamental x hx]
  linear_combination -hadd

/-- Lower traces depend only on the a.e. value, not on the chosen weak
derivative or on any finite-interval representatives used in patching. -/
theorem HalfLineSobolevRepresentative.trace_unique {Y : ℝ}
    {f g f' g' : ℝ → ℂ} (u : HalfLineSobolevRepresentative Y f g)
    (v : HalfLineSobolevRepresentative Y f' g')
    (hvalue : ∀ᵐ x, x ∈ Ioi Y → f x = f' x) : u.function Y = v.function Y := by
  have hae : u.function =ᵐ[volume.restrict (Ioo Y (Y + 1))] v.function := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [u.value_ae, v.value_ae, hvalue] with x hu hv hf hx
    exact (hu hx.1).symm.trans ((hf hx.1).trans (hv hx.1))
  rw [restrict_Ioo_eq_restrict_Icc] at hae
  have hu : ContinuousOn u.function (Icc Y (Y + 1)) :=
    u.continuous.mono (fun _ hx => hx.1)
  have hv : ContinuousOn v.function (Icc Y (Y + 1)) :=
    v.continuous.mono (fun _ hx => hx.1)
  exact (Measure.eqOn_Icc_of_ae_eq (by linarith : Y ≠ Y + 1) hae hu hv)
    ⟨le_rfl, by linarith⟩

end
end ImbalancedChen.Part3.ZeroModeWeakHalfLineTrace20261026b
