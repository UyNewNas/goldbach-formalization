import ImbalancedChen.P5U7OriginalOmegaIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Source-only successor to P5U7OriginalOmegaIntegral.lean in this draft.
Its proposed import path requires installing that predecessor at the
corresponding ImbalancedChen path; neither candidate has been compiled.

This file supplies the missing outer moving-row integrability and actual
product-triangle Fubini theorem, without assuming integrability.  A
globally continuous positive-coordinate extension proves continuity of
the moving row, including its zero value at t=1/3.  An explicit finite
bound is obtained from the actual first two Buchstab formulas.
-/

namespace ImbalancedChen

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab
open scoped Topology

def p5U7OmegaTriangle : Set (ℝ × ℝ) := {x | p5U7OmegaClosedSupport x.1 x.2}

def p5U7OmegaRow (K t : ℝ) : ℝ :=
  ∫ u in t..((1 - t) / 2), p5U7OmegaKernel K t u

/-- A continuous extension, used only to prove moving-row regularity. -/
def p5U7OmegaPositiveExtension (K t u : ℝ) : ℝ :=
  p5U7OmegaKernel K (max (59 / 250) t) (max (59 / 250) u)

theorem p5U7Omega_extension_continuous (K : ℝ) :
    Continuous (fun x : ℝ × ℝ => p5U7OmegaPositiveExtension K x.1 x.2) := by
  exact (p5U7Omega_kernel_continuousOn_positive K).comp_continuous
    ((continuous_const.max continuous_fst).prodMk (continuous_const.max continuous_snd))
    (fun x => ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250) (le_max_left _ _),
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250) (le_max_left _ _)⟩)

theorem p5U7Omega_extension_eq {K t u : ℝ} (ht : (59 / 250 : ℝ) ≤ t)
    (hu : (59 / 250 : ℝ) ≤ u) :
    p5U7OmegaPositiveExtension K t u = p5U7OmegaKernel K t u := by
  rw [p5U7OmegaPositiveExtension, max_eq_right ht, max_eq_right hu]

theorem p5U7Omega_extension_row_continuous (K : ℝ) :
    Continuous (fun t : ℝ =>
      ∫ u in t..((1 - t) / 2), p5U7OmegaPositiveExtension K t u) := by
  have hf := p5U7Omega_extension_continuous K
  have hupper : Continuous (fun t : ℝ =>
      ∫ u in (0 : ℝ)..((1 - t) / 2), p5U7OmegaPositiveExtension K t u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf
      ((continuous_const.sub continuous_id).div_const 2)
  have hlower : Continuous (fun t : ℝ =>
      ∫ u in (0 : ℝ)..t, p5U7OmegaPositiveExtension K t u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_id
  have heq : (fun t : ℝ => ∫ u in t..((1 - t) / 2), p5U7OmegaPositiveExtension K t u) =
      fun t : ℝ =>
        (∫ u in (0 : ℝ)..((1 - t) / 2), p5U7OmegaPositiveExtension K t u) -
        ∫ u in (0 : ℝ)..t, p5U7OmegaPositiveExtension K t u := by
    funext t
    exact (intervalIntegral.integral_interval_sub_left
      ((hf.uncurry_left t).intervalIntegrable 0 ((1 - t) / 2))
      ((hf.uncurry_left t).intervalIntegrable 0 t)).symm
  rw [heq]
  exact hupper.sub hlower

theorem p5U7Omega_extension_row_eq (K : ℝ) {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 3)) :
    (∫ u in t..((1 - t) / 2), p5U7OmegaPositiveExtension K t u) = p5U7OmegaRow K t := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith [ht.2] : t ≤ (1 - t) / 2)] at hu
  exact p5U7Omega_extension_eq ht.1 (ht.1.trans hu.1)

/-- The moving original row is continuous on the full closed outer interval. -/
theorem p5U7Omega_row_continuousOn (K : ℝ) :
    ContinuousOn (p5U7OmegaRow K) (Icc (59 / 250 : ℝ) (1 / 3)) := by
  apply (p5U7Omega_extension_row_continuous K).continuousOn.congr
  intro t ht
  exact (p5U7Omega_extension_row_eq K ht).symm

theorem p5U7Omega_row_at_third (K : ℝ) : p5U7OmegaRow K (1 / 3) = 0 := by
  norm_num [p5U7OmegaRow]

/-- Outer integrability is proved, not a premise of the integral dictionary. -/
theorem p5U7Omega_outer_intervalIntegrable (K : ℝ) :
    IntervalIntegrable (p5U7OmegaRow K) volume (59 / 250 : ℝ) (1 / 3) := by
  exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    (p5U7Omega_row_continuousOn K)

private theorem p5U7Omega_triangle_closed : IsClosed p5U7OmegaTriangle := by
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd ((continuous_const.sub continuous_fst).div_const 2)))

private theorem p5U7Omega_triangle_subset_box :
    p5U7OmegaTriangle ⊆ Icc (59 / 250 : ℝ) (1 / 3) ×ˢ Icc (59 / 250 : ℝ) 1 := by
  intro x hx
  have hg := p5U7Omega_closed_geometry hx
  exact ⟨⟨hx.1, hg.2.2.2.1⟩, ⟨hx.1.trans hx.2.1, by linarith [hx.1, hx.2.2]⟩⟩

theorem p5U7Omega_triangle_compact : IsCompact p5U7OmegaTriangle := by
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    p5U7Omega_triangle_closed p5U7Omega_triangle_subset_box

theorem p5U7Omega_triangle_integrable (K : ℝ) :
    IntegrableOn (fun x : ℝ × ℝ => p5U7OmegaKernel K x.1 x.2) p5U7OmegaTriangle := by
  exact (p5U7Omega_kernel_continuousOn_closed K).integrableOn_compact
    p5U7Omega_triangle_compact

/-- Product-space Fubini over the actual compact triangle. -/
theorem p5U7Omega_triangle_integral_eq_nested (K : ℝ) :
    (∫ x in p5U7OmegaTriangle, p5U7OmegaKernel K x.1 x.2) =
      p5U7OriginalOmegaIntegral K := by
  let B : Set (ℝ × ℝ) := Icc (59 / 250 : ℝ) (1 / 3) ×ˢ Icc (59 / 250 : ℝ) 1
  let O : Set (ℝ × ℝ) := {x | x.1 ≤ x.2 ∧ x.2 ≤ (1 - x.1) / 2}
  let g : ℝ × ℝ → ℝ := fun x => p5U7OmegaKernel K x.1 x.2
  have hO : MeasurableSet O :=
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd ((continuous_const.sub continuous_fst).div_const 2))).measurableSet
  have hset : B ∩ O = p5U7OmegaTriangle := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1.1, hx.2⟩
    · intro hx
      exact ⟨p5U7Omega_triangle_subset_box hx, hx.2⟩
  have hgB : ContinuousOn g B :=
    (p5U7Omega_kernel_continuousOn_positive K).mono (fun x hx =>
      ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250) hx.1.1,
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250) hx.2.1⟩)
  have hiB : IntegrableOn g B := hgB.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfubini : (∫ x in p5U7OmegaTriangle, g x) =
      ∫ t in Icc (59 / 250 : ℝ) (1 / 3),
        ∫ u in Icc (59 / 250 : ℝ) 1, O.indicator g (t,u) := by
    calc
      _ = ∫ x in B, O.indicator g x := by rw [setIntegral_indicator hO, hset]
      _ = _ := by
        rw [B, Measure.volume_eq_prod]
        exact setIntegral_prod _ (by
          simpa only [B, Measure.volume_eq_prod] using hiB.indicator hO)
  rw [hfubini]
  have hinner : ∀ t ∈ Icc (59 / 250 : ℝ) (1 / 3),
      (∫ u in Icc (59 / 250 : ℝ) 1, O.indicator g (t,u)) = p5U7OmegaRow K t := by
    intro t ht
    have heq : (fun u => O.indicator g (t,u)) =
        (Icc t ((1 - t) / 2)).indicator (fun u => g (t,u)) := by
      funext u
      by_cases h : t ≤ u ∧ u ≤ (1 - t) / 2 <;> simp [O, h]
    rw [heq, setIntegral_indicator measurableSet_Icc]
    have hsub : Icc (59 / 250 : ℝ) 1 ∩ Icc t ((1 - t) / 2) = Icc t ((1 - t) / 2) := by
      apply inter_eq_right.mpr
      intro u hu
      exact ⟨ht.1.trans hu.1, by linarith [hu.2, ht.1]⟩
    rw [hsub, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [ht.2] : t ≤ (1 - t) / 2)]
    rfl
  calc
    _ = ∫ t in Icc (59 / 250 : ℝ) (1 / 3), p5U7OmegaRow K t :=
      setIntegral_congr_fun measurableSet_Icc hinner
    _ = p5U7OriginalOmegaIntegral K := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (59 / 250 : ℝ) ≤ 1 / 3)]
      rfl

/-- The actual first two Buchstab pieces stay between zero and one. -/
theorem p5U7Omega_buchstab_zero_one {t u : ℝ} (h : p5U7OmegaClosedSupport t u) :
    0 ≤ buchstab (p5U7OmegaArgument t u) ∧ buchstab (p5U7OmegaArgument t u) ≤ 1 := by
  have hg := p5U7Omega_closed_geometry h
  have hs1 := hg.2.2.2.2.1
  have hspos : 0 < p5U7OmegaArgument t u := lt_of_lt_of_le zero_lt_one hs1
  refine ⟨(by norm_num : (0 : ℝ) ≤ 1 / 2).trans (one_half_le_buchstab hs1), ?_⟩
  by_cases hs2 : p5U7OmegaArgument t u ≤ 2
  · rw [buchstab_eq_one_div hs1 hs2]
    exact (div_le_one hspos).mpr hs1
  · have hs2' : 2 < p5U7OmegaArgument t u := lt_of_not_ge hs2
    rw [buchstab_eq_log_div hs2'.le (hg.2.2.2.2.2.trans (by norm_num))]
    apply (div_le_one hspos).mpr
    have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < p5U7OmegaArgument t u - 1)
    linarith

def p5U7OmegaFiniteBound (K : ℝ) : ℝ := |K| / (59 / 250 : ℝ) ^ 3

theorem p5U7Omega_kernel_norm_le_explicit (K : ℝ) {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) :
    ‖p5U7OmegaKernel K t u‖ ≤ p5U7OmegaFiniteBound K := by
  have hg := p5U7Omega_closed_geometry h
  have hb := p5U7Omega_buchstab_zero_one h
  have hu : (59 / 250 : ℝ) ≤ u := h.1.trans h.2.1
  have hu2 : (59 / 250 : ℝ) ^ 2 ≤ u ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hu 2
  have hd : (59 / 250 : ℝ) ^ 3 ≤ t * u ^ 2 := by
    calc
      _ = (59 / 250 : ℝ) * (59 / 250 : ℝ) ^ 2 := by ring
      _ ≤ t * u ^ 2 := mul_le_mul h.1 hu2 (by positivity) hg.1.le
  have hden : 0 < t * u ^ 2 := mul_pos hg.1 (sq_pos_of_pos hg.2.1)
  rw [p5U7OmegaKernel, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg hb.1, abs_of_pos hden]
  calc
    _ ≤ |K| / (t * u ^ 2) :=
      div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2 (abs_nonneg K)) hden.le
    _ ≤ p5U7OmegaFiniteBound K :=
      div_le_div_of_nonneg_left (abs_nonneg K) (by norm_num) hd

theorem p5U7Omega_row_norm_le_explicit (K : ℝ) {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 3)) :
    ‖p5U7OmegaRow K t‖ ≤ p5U7OmegaFiniteBound K := by
  have hle : t ≤ (1 - t) / 2 := by linarith [ht.2]
  have hB : 0 ≤ p5U7OmegaFiniteBound K := by unfold p5U7OmegaFiniteBound; positivity
  have hi : ‖p5U7OmegaRow K t‖ ≤ p5U7OmegaFiniteBound K * |(1 - t) / 2 - t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le hle] at hu
    exact p5U7Omega_kernel_norm_le_explicit K ⟨ht.1, hu.1.le, hu.2⟩
  refine hi.trans ?_
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  calc
    _ ≤ p5U7OmegaFiniteBound K * 1 := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hB
    _ = _ := mul_one _

theorem p5U7OriginalOmegaIntegral_norm_le_explicit (K : ℝ) :
    ‖p5U7OriginalOmegaIntegral K‖ ≤ p5U7OmegaFiniteBound K * (73 / 750 : ℝ) := by
  have hi : ‖p5U7OriginalOmegaIntegral K‖ ≤
      p5U7OmegaFiniteBound K * |(1 / 3 : ℝ) - 59 / 250| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le (by norm_num : (59 / 250 : ℝ) ≤ 1 / 3)] at ht
    exact p5U7Omega_row_norm_le_explicit K ⟨ht.1.le, ht.2⟩
  norm_num at hi ⊢
  exact hi

theorem p5U7OriginalOmegaIntegral_nonneg {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ p5U7OriginalOmegaIntegral K := by
  apply intervalIntegral.integral_nonneg (by norm_num : (59 / 250 : ℝ) ≤ 1 / 3)
  intro t ht
  apply intervalIntegral.integral_nonneg (by linarith [ht.2] : t ≤ (1 - t) / 2)
  intro u hu
  exact p5U7Omega_kernel_nonneg hK ⟨ht.1, hu.1, hu.2⟩

theorem p5U7CurrentOriginalOmegaIntegral_nonneg : 0 ≤ p5U7CurrentOriginalOmegaIntegral := by
  exact p5U7OriginalOmegaIntegral_nonneg (by norm_num [currentK])

theorem p5U7Omega_triangle_integral_nonneg {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ ∫ x in p5U7OmegaTriangle, p5U7OmegaKernel K x.1 x.2 := by
  rw [p5U7Omega_triangle_integral_eq_nested]
  exact p5U7OriginalOmegaIntegral_nonneg hK

end

end ImbalancedChen
