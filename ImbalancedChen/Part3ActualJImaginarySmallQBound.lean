import ImbalancedChen.Part3ActualGeneralJBessel
import Mathlib.Analysis.Normed.Group.Bounded

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Fixed imaginary-order J has a genuine bounded positive-q germ, from its
literal principal power and entire reciprocal-Gamma core. The core is
bounded on q in [0,1], and the positive-real imaginary power has norm one.
This is NOT the removable opposite-order critical quotient; no finite
bound for that logarithmic quotient at q=0 is asserted or bypassed.
-/

namespace ImbalancedChen.Part3.ActualJImaginarySmallQBound20261026b

noncomputable section
open Complex Set
open ActualGeneralJBesselSourceOnly GeneralComplexISeriesSourceOnly

theorem positive_imaginary_power_norm_one (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖(((q / 2 : ℝ) : ℂ) ^ (2 * I * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < q / 2)]
  simp

/-- The constant is extracted from the actual continuous entire core.
Only the power factor requires q>0; the core compactness includes q=0. -/
theorem exists_generalJ_imaginary_small_q_bound (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Ioc (0 : ℝ) 1,
      ‖generalJ (2 * I * (t : ℂ)) q‖ ≤ C := by
  have hnu : -1 < (2 * I * (t : ℂ)).re := by simp
  have hc : Continuous (fun q : ℝ =>
      generalICore (2 * I * (t : ℂ)) (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))) :=
    (continuous_generalICore hnu).comp (by fun_prop)
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
    .exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|A| + 1, by positivity, ?_⟩
  intro q hq
  rw [generalJ, norm_mul, positive_imaginary_power_norm_one t hq.1, one_mul]
  have hb := hA q ⟨hq.1.le, hq.2⟩
  have ha := le_abs_self A
  linarith

end
end ImbalancedChen.Part3.ActualJImaginarySmallQBound20261026b
