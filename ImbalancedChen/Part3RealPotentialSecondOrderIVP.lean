import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Native complex scalar initial-value uniqueness for f''=V*f on the
ORIGINAL half-line y>Y, for any continuous REAL potential V there.
The two-component field (z2,V(y)*z1) has a uniform Lipschitz constant
on every compact interval contained in that half-line. Its bound is
derived from compactness and continuity of V, rather than assumed.
Mathlib's native first-order ODE uniqueness then propagates equal jets
across the entire original domain, including all zeros of solutions.

Y may be arbitrary real, so positive-axis and Y>=0 cusp applications
are included. No L2, reference solution, special-function basis, fixed
spectral parameter, nonvanishing solution or IVP premise occurs.
-/

namespace ImbalancedChen.Part3.RealPotentialSecondOrderIVP20261026b
noncomputable section
open Set

/-- Actual first and second derivative jets of a scalar solution. -/
def CuspPotentialSolution (V : ℝ → ℝ) (Y : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ y : ℝ, Y < y → HasDerivAt f (deriv f y) y ∧
    HasDerivAt (deriv f) ((V y : ℂ) * f y) y

/-- C2 regularity and the literal native scalar equation supply the
solution jets; the caller need not present an extra jet hypothesis. -/
theorem cuspPotentialSolution_of_contDiffOn {V : ℝ → ℝ} {Y : ℝ} {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ 2 f (Ioi Y))
    (hODE : ∀ y : ℝ, Y < y → deriv (deriv f) y = (V y : ℂ) * f y) :
    CuspPotentialSolution V Y f := by
  have hdf : ContDiffOn ℝ 1 (deriv f) (Ioi Y) :=
    hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  intro y hy
  have hfirst := ((hf.differentiableOn (by norm_num) y hy).
    differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
  have hsecond := ((hdf.differentiableOn (by norm_num) y hy).
    differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
  exact ⟨hfirst, by simpa only [hODE y hy] using hsecond⟩

private def solutionJet (f : ℝ → ℂ) (y : ℝ) : ℂ × ℂ := (f y, deriv f y)

private def potentialField (V : ℝ → ℝ) (y : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (z.2, (V y : ℂ) * z.1)

/-- A bounded coefficient gives the actual state-field Lipschitz bound.
This estimate is independent of any zero or nonzero solution value. -/
private theorem potentialField_lipschitz {V : ℝ → ℝ} {y : ℝ} {K : ℝ≥0}
    (hK : 1 ≤ (K : ℝ)) (hV : ‖V y‖ ≤ (K : ℝ)) :
    LipschitzWith K (potentialField V y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  have hfirst : dist x.2 z.2 ≤ (K : ℝ) * dist x z := by
    have hpart : dist x.2 z.2 ≤ dist x z := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    nlinarith [dist_nonneg x z]
  have hsecond : dist ((V y : ℂ) * x.1) ((V y : ℂ) * z.1) ≤
      (K : ℝ) * dist x z := by
    rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real]
    apply mul_le_mul hV ?_ (norm_nonneg _) K.property
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  change max (dist x.2 z.2) (dist ((V y : ℂ) * x.1) ((V y : ℂ) * z.1)) ≤ _
  exact max_le hfirst hsecond

/-- Genuine scalar IVP uniqueness THROUGH ALL ZEROS on the original
open half-line. All needed coefficient bounds are proved from hV. -/
theorem cusp_initial_value_unique {V : ℝ → ℝ} {Y a : ℝ} {f g : ℝ → ℂ}
    (hV : ContinuousOn V (Ioi Y))
    (hf : CuspPotentialSolution V Y f) (hg : CuspPotentialSolution V Y g)
    (ha : Y < a) (hvalue : f a = g a) (hderiv : deriv f a = deriv g a) :
    EqOn f g (Ioi Y) := by
  intro q hq
  let A := (Y + min a q) / 2
  let B := max a q + 1
  have hmin : Y < min a q := lt_min ha hq
  have hYA : Y < A := by dsimp [A]; linarith
  have haA : A < a := by dsimp [A]; linarith [min_le_left a q]
  have hqA : A < q := by dsimp [A]; linarith [min_le_right a q]
  have haB : a < B := by dsimp [B]; linarith [le_max_left a q]
  have hqB : q < B := by dsimp [B]; linarith [le_max_right a q]
  have hVAB : ContinuousOn V (Icc A B) :=
    hV.mono (fun y hy => hYA.trans_le hy.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hVAB
  let K : ℝ≥0 := ⟨max 1 C, zero_le_one.trans (le_max_left _ _)⟩
  have hK : 1 ≤ (K : ℝ) := le_max_left _ _
  have hbound {y : ℝ} (hy : y ∈ Ioo A B) : ‖V y‖ ≤ (K : ℝ) :=
    (hC y ⟨hy.1.le, hy.2.le⟩).trans (le_max_right _ _)
  have hstate : EqOn (solutionJet f) (solutionJet g) (Ioo A B) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := potentialField V) (s := fun _ => univ) (K := K) (t₀ := a)
    · intro y hy
      exact (potentialField_lipschitz hK (hbound hy)).lipschitzOnWith
    · exact ⟨haA, haB⟩
    · intro y hy
      exact ⟨(hf y (hYA.trans hy.1)).1.prodMk (hf y (hYA.trans hy.1)).2, mem_univ _⟩
    · intro y hy
      exact ⟨(hg y (hYA.trans hy.1)).1.prodMk (hg y (hYA.trans hy.1)).2, mem_univ _⟩
    · exact Prod.ext hvalue hderiv
  exact congrArg Prod.fst (hstate ⟨hqA, hqB⟩)

/-- Direct C2 equation API, with no separately supplied native jets. -/
theorem cusp_C2_initial_value_unique {V : ℝ → ℝ} {Y a : ℝ} {f g : ℝ → ℂ}
    (hV : ContinuousOn V (Ioi Y))
    (hf : ContDiffOn ℝ 2 f (Ioi Y)) (hg : ContDiffOn ℝ 2 g (Ioi Y))
    (hfODE : ∀ y : ℝ, Y < y → deriv (deriv f) y = (V y : ℂ) * f y)
    (hgODE : ∀ y : ℝ, Y < y → deriv (deriv g) y = (V y : ℂ) * g y)
    (ha : Y < a) (hvalue : f a = g a) (hderiv : deriv f a = deriv g a) :
    EqOn f g (Ioi Y) :=
  cusp_initial_value_unique hV (cuspPotentialSolution_of_contDiffOn hf hfODE)
    (cuspPotentialSolution_of_contDiffOn hg hgODE) ha hvalue hderiv

end
end ImbalancedChen.Part3.RealPotentialSecondOrderIVP20261026b
