import ImbalancedChen.Part3ActualGeneralJBessel
import ImbalancedChen.Part3ComplexBetaHalfLineGamma
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

Actual Poisson weight integrability and all even moments for Re(nu)>-1/2.
The map t->t^2, its image, derivative and literal cpow Jacobian are proved,
then the existing concrete compact complex Beta theorem evaluates them.
This is the analytic integral primitive for the actual generalJ series;
the final termwise cosine series identification is separate.
-/

namespace ImbalancedChen.Part3.JBesselPoissonEvenMoments20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3ComplexBetaHalfLineGamma (compactKernel
  integrableOn_compactKernel integral_compactKernel_eq_gamma)

def poissonWeight (ν : ℂ) (t : ℝ) : ℂ :=
  ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)

def evenMomentIntegrand (ν : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (2 * n) * poissonWeight ν t

private theorem square_image : (fun t : ℝ => t ^ 2) '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨sq_pos_of_pos ht.1, ?_⟩
    have hprod := mul_pos (sub_pos.mpr ht.2) (show 0 < 1 + t by linarith [ht.1])
    nlinarith
  · intro hu
    refine ⟨Real.sqrt u, ⟨Real.sqrt_pos.mpr hu.1, ?_⟩, Real.sq_sqrt hu.1.le⟩
    apply (sq_lt_sq₀ (Real.sqrt_nonneg u) zero_le_one).mp
    simpa only [Real.sq_sqrt hu.1.le, one_pow] using hu.2

private theorem square_derivative (t : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
  simpa using (hasDerivAt_id t).pow 2

private theorem square_injective : Set.InjOn (fun t : ℝ => t ^ 2) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact (sq_eq_sq₀ hx.1.le hy.1.le).mp hxy

theorem poisson_square_jacobian (ν : ℂ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    |2 * t| • compactKernel ((n : ℂ) + 1 / 2) (ν + 1 / 2) (t ^ 2) =
      (2 : ℂ) * evenMomentIntegrand ν n t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpower : (((t ^ 2 : ℝ) : ℂ)) ^ ((n : ℂ) + 1 / 2 - 1) =
      (t : ℂ) ^ (((2 * n : ℕ) : ℂ) - 1) := by
    rw [← Real.rpow_two t, ← Complex.cpow_mul_ofReal_nonneg ht.le (2 : ℝ)]
    congr 1
    push_cast
    ring
  have hcancel : (t : ℂ) * (((t ^ 2 : ℝ) : ℂ)) ^ ((n : ℂ) + 1 / 2 - 1) =
      (t : ℂ) ^ (2 * n) := by
    rw [hpower, Complex.cpow_sub _ _ htC, Complex.cpow_one, Complex.cpow_natCast]
    field_simp [htC] <;> ring
  have hexp : (ν + 1 / 2) - 1 = ν - 1 / 2 := by ring
  rw [Complex.real_smul, abs_of_pos (mul_pos (by norm_num) ht)]
  dsimp only [compactKernel, evenMomentIntegrand, poissonWeight]
  rw [hexp]
  push_cast
  calc
    _ = (2 : ℂ) * ((t : ℂ) * ((t : ℂ) ^ 2) ^ ((n : ℂ) + 1 / 2 - 1)) *
        (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) := by ring
    _ = _ := by
      have hc := hcancel
      push_cast at hc
      rw [hc]

theorem evenMoment_half_integrable {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    IntegrableOn (evenMomentIntegrand ν n) (Ioo (0 : ℝ) 1) := by
  have ha : 0 < ((n : ℂ) + 1 / 2).re := by
    have hre : ((n : ℂ) + 1 / 2).re = (n : ℝ) + 1 / 2 := by simp
    rw [hre]
    positivity
  have hb : 0 < (ν + 1 / 2).re := by
    have hre : (ν + 1 / 2).re = ν.re + 1 / 2 := by norm_num
    rw [hre]
    linarith
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (square_derivative t).hasDerivWithinAt) square_injective
    (compactKernel ((n : ℂ) + 1 / 2) (ν + 1 / 2))
  rw [square_image] at hchange
  have h := hchange.mp (integrableOn_compactKernel ha hb)
  apply (h.div_const (2 : ℂ)).congr_fun _ measurableSet_Ioo
  intro t ht
  rw [poisson_square_jacobian ν n ht.1]
  ring

theorem evenMoment_half_integral {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    (2 : ℂ) * (∫ t in Ioo (0 : ℝ) 1, evenMomentIntegrand ν n t) =
      Complex.Gamma ((n : ℂ) + 1 / 2) * Complex.Gamma (ν + 1 / 2) /
        Complex.Gamma ((n : ℂ) + ν + 1) := by
  have ha : 0 < ((n : ℂ) + 1 / 2).re := by
    have hre : ((n : ℂ) + 1 / 2).re = (n : ℝ) + 1 / 2 := by simp
    rw [hre]
    positivity
  have hb : 0 < (ν + 1 / 2).re := by
    have hre : (ν + 1 / 2).re = ν.re + 1 / 2 := by norm_num
    rw [hre]
    linarith
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (square_derivative t).hasDerivWithinAt) square_injective
    (compactKernel ((n : ℂ) + 1 / 2) (ν + 1 / 2))
  rw [square_image] at hchange
  calc
    (2 : ℂ) * (∫ t in Ioo (0 : ℝ) 1, evenMomentIntegrand ν n t) =
        ∫ t in Ioo (0 : ℝ) 1, (2 : ℂ) * evenMomentIntegrand ν n t :=
      (integral_const_mul _ _).symm
    _ = ∫ t in Ioo (0 : ℝ) 1,
        |2 * t| • compactKernel ((n : ℂ) + 1 / 2) (ν + 1 / 2) (t ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact (poisson_square_jacobian ν n ht.1).symm
    _ = ∫ u in Ioo (0 : ℝ) 1, compactKernel ((n : ℂ) + 1 / 2) (ν + 1 / 2) u := hchange.symm
    _ = _ := by
      have hsum : ((n : ℂ) + 1 / 2) + (ν + 1 / 2) = (n : ℂ) + ν + 1 := by ring
      simpa only [hsum] using integral_compactKernel_eq_gamma ha hb

theorem evenMoment_neg (ν : ℂ) (n : ℕ) (t : ℝ) :
    evenMomentIntegrand ν n (-t) = evenMomentIntegrand ν n t := by
  simp [evenMomentIntegrand, poissonWeight, Complex.ofReal_neg, neg_pow, pow_mul]

private theorem evenMoment_interval_integrable {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    IntervalIntegrable (evenMomentIntegrand ν n) volume (-1) 1 := by
  have hp : IntervalIntegrable (evenMomentIntegrand ν n) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
      (evenMoment_half_integrable hν n)
  have hn : IntervalIntegrable (evenMomentIntegrand ν n) volume (-1) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hp
    simpa only [neg_zero, neg_one, evenMoment_neg] using h.symm
  exact hn.trans hp

theorem evenMoment_integrable {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    IntegrableOn (evenMomentIntegrand ν n) (Ioo (-1 : ℝ) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).1
    (evenMoment_interval_integrable hν n)

/-- Full actual even moment on (-1,1), including the exact Beta/Gamma factors. -/
theorem evenMoment_integral {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    (∫ t in Ioo (-1 : ℝ) 1, evenMomentIntegrand ν n t) =
      Complex.Gamma ((n : ℂ) + 1 / 2) * Complex.Gamma (ν + 1 / 2) /
        Complex.Gamma ((n : ℂ) + ν + 1) := by
  have hp : IntervalIntegrable (evenMomentIntegrand ν n) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
      (evenMoment_half_integrable hν n)
  have hn : IntervalIntegrable (evenMomentIntegrand ν n) volume (-1) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hp
    simpa only [neg_zero, neg_one, evenMoment_neg] using h.symm
  have he : (∫ t in (-1 : ℝ)..0, evenMomentIntegrand ν n t) =
      ∫ t in (0 : ℝ)..1, evenMomentIntegrand ν n t := by
    simpa only [evenMoment_neg, neg_zero, neg_one] using
      (intervalIntegral.integral_comp_neg (evenMomentIntegrand ν n) (a := (0 : ℝ)) (b := 1)).symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hn hp
  rw [he] at hsplit
  have hhalf := evenMoment_half_integral hν n
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hhalf
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← hsplit]
  linear_combination hhalf

theorem poissonWeight_integrable {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) :
    IntegrableOn (poissonWeight ν) (Ioo (-1 : ℝ) 1) := by
  simpa only [evenMomentIntegrand, mul_zero, pow_zero, one_mul] using evenMoment_integrable hν 0

end
end ImbalancedChen.Part3.JBesselPoissonEvenMoments20261025a
