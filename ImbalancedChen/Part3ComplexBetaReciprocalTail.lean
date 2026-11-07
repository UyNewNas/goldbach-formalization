import ImbalancedChen.Part3ComplexBetaHalfLineGamma
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

The actual complex Euler kernel is transformed by t->1/t. The resulting
paired tail on (1,infinity) is evaluated by the concrete complex half-line
Beta/Gamma supplier, with no identity or integrability premise. This is
the complex counterpart needed by the literal K_{2it} Mellin transform;
its two parameters will be s/2+I*t and s/2-I*t.
-/

namespace ImbalancedChen.Part3.ComplexBetaReciprocalTail20261025a

noncomputable section
open Set MeasureTheory Filter
open ImbalancedChen.Part3ComplexBetaHalfLineGamma

/-- Exact complex Euler reciprocal pullback with its real Jacobian. -/
theorem halflineKernel_reciprocal (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    (t ^ 2)⁻¹ • halflineKernel a b t⁻¹ = halflineKernel b a t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp : 0 < 1 + t := by linarith
  have hpC : ((1 + t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hinv : 1 + t⁻¹ = (1 + t) / t := by field_simp [ht.ne'] <;> ring
  have hpow : (t : ℂ) ^ (a + b) =
      (t : ℂ) ^ (a - 1) * (t : ℂ) ^ (b - 1) * (t : ℂ) ^ 2 := by
    calc
      (t : ℂ) ^ (a + b) = (t : ℂ) ^ ((a - 1) + (b - 1) + (2 : ℂ)) := by
        congr 1
        ring
      _ = _ := by
        rw [Complex.cpow_add _ _ htC, Complex.cpow_add _ _ htC, Complex.cpow_two]
  have hpa : (t : ℂ) ^ (a - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl htC)
  have hpb : (t : ℂ) ^ (b - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl htC)
  have hpab : ((1 + t : ℝ) : ℂ) ^ (a + b) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  rw [Complex.real_smul]
  dsimp only [halflineKernel]
  rw [hinv, Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.inv_cpow_ofReal_nonneg ht.le,
    Complex.div_cpow_ofReal_nonneg hp.le ht.le, add_comm b a, hpow]
  field_simp [htC, hpa, hpb, hpab] <;> ring

/-- The small complex Euler interval equals the opposite-order tail. -/
theorem halflineKernel_small_eq_swapped_tail (a b : ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, halflineKernel a b t) =
      ∫ t in Ioi (1 : ℝ), halflineKernel b a t := by
  have himage : (fun t : ℝ => t⁻¹) '' Ioi (1 : ℝ) = Ioo (0 : ℝ) 1 := by
    rw [image_inv_eq_inv, inv_Ioi₀ (by norm_num : (0 : ℝ) < 1), inv_one]
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => t⁻¹) (f' := fun t : ℝ => -(t ^ 2)⁻¹)
    measurableSet_Ioi
    (fun t ht =>
      (hasDerivAt_inv (lt_trans (by norm_num : (0 : ℝ) < 1) ht).ne').hasDerivWithinAt)
    (fun x _ y _ hxy => inv_injective hxy) (halflineKernel a b)
  rw [himage] at h
  refine h.trans ?_
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  exact halflineKernel_reciprocal a b (lt_trans (by norm_num : (0 : ℝ) < 1) ht)

/-- The paired tails reconstruct the whole positive Euler integral. -/
theorem halflineKernel_paired_tail_eq_full {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t in Ioi (1 : ℝ), halflineKernel a b t + halflineKernel b a t) =
      ∫ t in Ioi (0 : ℝ), halflineKernel a b t := by
  have hfull := integrableOn_halflineKernel ha hb
  have htail : IntegrableOn (halflineKernel a b) (Ioi (1 : ℝ)) :=
    hfull.mono_set (Ioi_subset_Ioi (by norm_num))
  have htailSwap : IntegrableOn (halflineKernel b a) (Ioi (1 : ℝ)) :=
    (integrableOn_halflineKernel hb ha).mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit : (∫ t in Ioi (0 : ℝ), halflineKernel a b t) =
      (∫ t in Ioo (0 : ℝ) 1, halflineKernel a b t) +
        ∫ t in Ioi (1 : ℝ), halflineKernel a b t := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hfull.mono_set Ioc_subset_Ioi_self) htail,
      integral_Ioc_eq_integral_Ioo]
  rw [integral_add htail htailSwap,
    ← halflineKernel_small_eq_swapped_tail a b, add_comm]
  exact hsplit.symm

/-- Actual complex paired Euler-tail Gamma evaluation, without a supplier
premise in the statement. -/
theorem halflineKernel_paired_tail_eq_gamma {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t in Ioi (1 : ℝ), halflineKernel a b t + halflineKernel b a t) =
      Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  rw [halflineKernel_paired_tail_eq_full ha hb, integral_halflineKernel_eq_gamma ha hb]

end
end ImbalancedChen.Part3.ComplexBetaReciprocalTail20261025a
