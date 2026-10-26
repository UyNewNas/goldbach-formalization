import ImbalancedChen.Part3GeneralIRealPositiveEndpoint
import ImbalancedChen.Part3GeneralKRightEndpoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The actual I series at real order nu >= 0 has a quadratic lower bound
at infinity. Consequently its logarithmic pullback is not square
integrable on any right half-line. A square-integrable linear combination
of the actual I and K solutions has zero I coefficient.

This covers the real-order parameter for lambda = 1/4 - nu^2, including
nu = 0. It does not assert a Fourier-coefficient ODE, a basis theorem,
or the analogous imaginary-order growth theorem. In particular it does
not presume that an arbitrary cusp coefficient already has this form.
-/

namespace ImbalancedChen.Part3.RealOrderIGrowthExclusion20261026a

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open GeneralComplexISeriesSourceOnly GeneralIRealPositiveEndpoint20261025a
open ComplexOrderKRadialRegularitySourceOnly GeneralKRightEndpoint20261025a

private def positiveCoefficient (nu : ℝ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ) * Real.Gamma ((n : ℝ) + nu + 1))⁻¹

private theorem coefficient_ofReal (nu : ℝ) (n : ℕ) :
    generalICoeff (nu : ℂ) n = (positiveCoefficient nu n : ℂ) := by
  have harg : (n : ℂ) + (nu : ℂ) + 1 = (((n : ℝ) + nu + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [generalICoeff, harg, Complex.Gamma_ofReal]
  simp only [positiveCoefficient, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast]

private theorem coefficient_pos {nu : ℝ} (hnu : 0 ≤ nu) (n : ℕ) :
    0 < positiveCoefficient nu n := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact inv_pos.mpr (mul_pos hf (Real.Gamma_pos_of_pos (by linarith)))

/-- A specified nonnegative term of the actual convergent I core is a
lower bound. This is a series inequality, not an asymptotic assumption. -/
theorem generalICore_term_le {nu x : ℝ} (hnu : 0 ≤ nu) (hx : 0 ≤ x) (n : ℕ) :
    positiveCoefficient nu n * x ^ n ≤
      (generalICore (nu : ℂ) (x : ℂ)).re := by
  have hlegal : -1 < (nu : ℂ).re := by simp only [Complex.ofReal_re]; linarith
  have hterm (k : ℕ) : generalICoeff (nu : ℂ) k * (x : ℂ) ^ k =
      ((positiveCoefficient nu k * x ^ k : ℝ) : ℂ) := by
    rw [coefficient_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  have hs : HasSum (fun k : ℕ => positiveCoefficient nu k * x ^ k)
      (generalICore (nu : ℂ) (x : ℂ)).re := by
    simpa only [hterm, Complex.ofReal_re] using
      Complex.hasSum_re (generalICore_hasSum hlegal (x : ℂ))
  simpa only [Finset.sum_singleton] using
    sum_le_hasSum ({n} : Finset ℕ)
      (fun k _ => mul_nonneg (coefficient_pos hnu k).le (pow_nonneg hx k)) hs

/-- Genuine quadratic growth of the actual real-order I solution. -/
theorem generalI_quadratic_lower_bound {nu q : ℝ} (hnu : 0 ≤ nu) (hq : 2 ≤ q) :
    (Real.Gamma (nu + 2))⁻¹ * (q / 2) ^ 2 ≤ (generalI (nu : ℂ) q).re := by
  have hhalf : 1 ≤ q / 2 := by linarith
  have hpos : 0 < q / 2 := by linarith
  have hcore := generalICore_term_le hnu (sq_nonneg (q / 2)) 1
  have harg : (1 : ℝ) + nu + 1 = nu + 2 := by ring
  simp only [positiveCoefficient, Nat.factorial_one, Nat.cast_one, one_mul,
    pow_one, harg] at hcore
  have hnonneg : 0 ≤ (generalICore (nu : ℂ) (((q / 2) ^ 2 : ℝ) : ℂ)).re :=
    (mul_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith)).le)
      (sq_nonneg (q / 2))).trans hcore
  have hpower : (((q / 2 : ℝ) : ℂ) ^ (nu : ℂ)) = ((q / 2) ^ nu : ℝ) :=
    (Complex.ofReal_cpow hpos.le nu).symm
  rw [generalI, hpower, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact hcore.trans (le_mul_of_one_le_left hnonneg (Real.one_le_rpow hhalf hnu))

/-- A positive constant lower bound, including the threshold order zero. -/
theorem generalI_norm_lower_bound {nu q : ℝ} (hnu : 0 ≤ nu) (hq : 2 ≤ q) :
    (Real.Gamma (nu + 2))⁻¹ ≤ ‖generalI (nu : ℂ) q‖ := by
  have hc : 0 ≤ (Real.Gamma (nu + 2))⁻¹ :=
    (inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))).le
  have hs : 1 ≤ (q / 2) ^ 2 := by nlinarith
  calc
    _ ≤ (Real.Gamma (nu + 2))⁻¹ * (q / 2) ^ 2 := by nlinarith
    _ ≤ (generalI (nu : ℂ) q).re := generalI_quadratic_lower_bound hnu hq
    _ ≤ ‖generalI (nu : ℂ) q‖ := Complex.re_le_norm _

/-- No actual real-order I logarithmic mode is L2 at the right endpoint.
The tail starts at any real R, so finite changes of cusp height are harmless. -/
theorem realILogMode_not_memLp_two_Ioi {nu : ℝ} (hnu : 0 ≤ nu) (R : ℝ) :
    ¬ MemLp (realILogMode nu) 2 (volume.restrict (Ioi R)) := by
  intro hI
  let S : ℝ := max R (Real.log 2)
  let c : ℝ := (Real.Gamma (nu + 2))⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
  have hsub : Ioi S ⊆ Ioi R := fun _ hr => lt_of_le_of_lt (le_max_left _ _) hr
  have htail : MemLp (realILogMode nu) 2 (volume.restrict (Ioi S)) :=
    hI.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hconst : MemLp (fun _ : ℝ => c) 2 (volume.restrict (Ioi S)) := by
    apply htail.of_le aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrlog : Real.log 2 ≤ r := (le_max_right R (Real.log 2)).trans hr.le
    have hq : 2 ≤ Real.exp r := by
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
        Real.exp_le_exp.mpr hrlog
    simpa only [Real.norm_eq_abs, abs_of_pos hc, realILogMode, c] using
      generalI_norm_lower_bound hnu hq
  have hfinite := (memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp hconst
  rcases hfinite with hz | hfinite
  · exact hc.ne' hz
  · simpa only [Measure.restrict_apply_univ, Real.volume_Ioi, lt_self_iff_false] using hfinite

/-- Once an ODE basis representation has independently been proved, L2
forces its actual real-order I coefficient to vanish. No growth or K-L2
premise is required: both endpoint properties are actual theorems. -/
theorem real_IK_combination_L2_I_coefficient_zero {nu : ℝ} (hnu : 0 ≤ nu)
    (A B : ℂ) (R : ℝ)
    (hL2 : MemLp (fun r : ℝ => A * realILogMode nu r + B * radialK (nu : ℂ) r)
      2 (volume.restrict (Ioi R))) : A = 0 := by
  by_contra hA
  let S : ℝ := max R 0
  have hsubR : Ioi S ⊆ Ioi R := fun _ hr => lt_of_le_of_lt (le_max_left _ _) hr
  have hsub0 : Ioi S ⊆ Ioi (0 : ℝ) := fun _ hr => lt_of_le_of_lt (le_max_right _ _) hr
  have hsum := hL2.mono_measure (Measure.restrict_mono hsubR le_rfl)
  have hK := (radialK_memLp_two_Ioi (nu : ℂ)).mono_measure
    (Measure.restrict_mono hsub0 le_rfl)
  have hAI : MemLp (fun r : ℝ => A * realILogMode nu r) 2
      (volume.restrict (Ioi S)) := by
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right]
      using hsum.sub (hK.const_smul B)
  have hI : MemLp (realILogMode nu) 2 (volume.restrict (Ioi S)) := by
    simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]
      using hAI.const_smul A⁻¹
  exact realILogMode_not_memLp_two_Ioi hnu S hI

end
end ImbalancedChen.Part3.RealOrderIGrowthExclusion20261026a
