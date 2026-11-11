import ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
P3.6: ACTUAL first coordinate derivative of the complete original group-
occurrence product, rather than merely the combinatorial allocation mass.
The physical occurrence index j : Fin g distinguishes equal group subsets
and independent positive scales. This is one coordinate step only: repeated
higher mixed derivatives and U5/trim remain open.

Manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F). Lean v4.33.0-rc1,
Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
SOURCE_ONLY; compile and kernel NOT RUN.
-/

namespace ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBCanonicalGeometryDerivative

/-- The actual, occurrence-indexed product of all original smooth
psi(c_j exp(sum_{i in J_j} u_i)) factors; no surrogate factors. -/
def originalGroupProduct {g : ℕ} (chi : ℝ → ℂ)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) : ℂ :=
  ∏ j : Fin g, originalGroupDyadicFactor chi (c j) (J j) u

/-- Differentiability of a physical-scale original dyadic log profile
follows from the genuine C∞ cutoff, using only the smoothness premise. -/
theorem groupProfile_differentiable (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (c : ℝ) :
    Differentiable ℝ (groupDyadicLogProfile chi c) := by
  have hχ : Differentiable ℝ chi := hchi.differentiable (by norm_num)
  have he : Differentiable ℝ (fun t : ℝ => c * Real.exp t) :=
    Real.differentiable_exp.const_mul c
  have he2 : Differentiable ℝ (fun t : ℝ => 2 * (c * Real.exp t)) :=
    he.const_mul 2
  exact (hχ.comp he).sub (hχ.comp he2)

/-- The literal group sum, restricted to an actual updated coordinate,
is a differentiable affine map or a constant (depending on membership). -/
theorem groupSum_slice_differentiable (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    Differentiable ℝ (fun t : ℝ => originalGroupSum J (Function.update u i t)) := by
  classical
  by_cases hi : i ∈ J
  · have heq :
        (fun t : ℝ => originalGroupSum J (Function.update u i t)) =
          (fun t : ℝ => t + ∑ j ∈ J.erase i, u j) := by
      funext t
      exact originalGroupSum_update_mem J u i hi t
    rw [heq]
    fun_prop
  · have heq :
        (fun t : ℝ => originalGroupSum J (Function.update u i t)) =
          (fun _ : ℝ => originalGroupSum J u) := by
      funext t
      exact originalGroupSum_update_not_mem J u i hi t
    rw [heq]
    fun_prop

/-- Actual physical original group factors possess coordinate-slice
derivatives for EVERY real scale c (positivity is only needed later
for the uniform derivative budget). -/
theorem originalGroupFactor_slice_differentiable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : ℝ) (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ
      (fun t : ℝ => originalGroupDyadicFactor chi c J (Function.update u i t))
      (u i) := by
  have hprofile := groupProfile_differentiable chi hchi c
  have hsum := groupSum_slice_differentiable J u i
  exact (hprofile.comp hsum).differentiableAt

/-- Genuine one-axis Leibniz identity for the complete product of
original group OCCURRENCES. Unlike allocationMass, the left side is
an actual deriv on the literal group product. Empty g is included. -/
theorem originalGroupProduct_axisDeriv
    {g : ℕ} (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (originalGroupProduct chi c J) i u =
      ∑ j : Fin g,
        (∏ l ∈ (Finset.univ.erase j),
          originalGroupDyadicFactor chi (c l) (J l) u) *
          actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u := by
  classical
  have hupdate : Function.update u i (u i) = u := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_noteq h]
  have hd :=
    deriv_fun_finsetProd
      (u := (Finset.univ : Finset (Fin g)))
      (f := fun j t =>
        originalGroupDyadicFactor chi (c j) (J j) (Function.update u i t))
      (x := u i)
      (by
        intro j hj
        exact originalGroupFactor_slice_differentiable chi hchi
          (c j) (J j) u i)
  change deriv (fun t : ℝ => ∏ j : Fin g,
      originalGroupDyadicFactor chi (c j) (J j) (Function.update u i t))
    (u i) = _
  simpa only [hupdate, smul_eq_mul, actualAxisDeriv] using hd

/-- One-axis, complete-product nonnegative budget, with original group
occurrences and their multiplicities left untouched. -/
def originalGroupAxisMass {g : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (u : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  ∑ j : Fin g,
    (∏ l ∈ (Finset.univ.erase j),
      ‖originalGroupDyadicFactor chi (c l) (J l) u‖) *
      ‖actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖

/-- The actual derivative of the whole product is dominated by the
literal one-step occurrence mass, rather than by a separately assigned product jet. -/
theorem originalGroupProduct_axisDeriv_norm_le
    {g : ℕ} (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ ≤
      originalGroupAxisMass chi c J u i := by
  rw [originalGroupProduct_axisDeriv chi hchi c J u i]
  unfold originalGroupAxisMass
  calc
    ‖∑ j : Fin g,
       (∏ l ∈ (Finset.univ.erase j),
         originalGroupDyadicFactor chi (c l) (J l) u) *
         actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖
       ≤ ∑ j : Fin g,
         ‖(∏ l ∈ (Finset.univ.erase j),
           originalGroupDyadicFactor chi (c l) (J l) u) *
           actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖ :=
         norm_sum_le _ _
    _ = ∑ j : Fin g,
       (∏ l ∈ (Finset.univ.erase j),
         ‖originalGroupDyadicFactor chi (c l) (J l) u‖) *
         ‖actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖ := by
         apply Finset.sum_congr rfl
         intro j hj
         simp only [norm_mul, norm_prod]

/-- A FIRST-ORDER quantitative bound for the genuine group product.
The max(1,3C) enlargement is deliberate: erasing one factor should
not use the false inequality (3C)^(g-1) <= (3C)^g when 3C < 1.
The bound is not claimed polylogarithmic for growing group count g. -/
theorem originalGroupProduct_axisDeriv_uniform_finite_order
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : ℕ) (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) → ∀ (u : Fin 6 → ℝ) (i : Fin 6),
          ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ ≤
            (g : ℝ) * (max 1 (3 * C)) ^ g * (3 * C) := by
  obtain ⟨C, hC, hbound⟩ :=
    originalGroupOrderedDeriv_uniform_scale chi hchi hsmall hlarge 1
  refine ⟨C, hC, ?_⟩
  intro g c J hc u i
  let M : ℝ := max 1 (3 * C)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM1
  have hz : 0 ≤ (3 : ℝ) * C := mul_nonneg (by norm_num) hC
  have hzero (j : Fin g) :
      ‖originalGroupDyadicFactor chi (c j) (J j) u‖ ≤ 3 * C := by
    simpa only [originalOrderedAxisDeriv] using
      (hbound (c j) (hc j) (J j) [] (by simp) u)
  have hone (j : Fin g) :
      ‖actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖ ≤
        3 * C := by
    simpa only [originalOrderedAxisDeriv] using
      (hbound (c j) (hc j) (J j) [i] (by simp) u)
  calc
    ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖
      ≤ originalGroupAxisMass chi c J u i :=
        originalGroupProduct_axisDeriv_norm_le chi hchi c J u i
    _ ≤ ∑ _j : Fin g, M ^ g * (3 * C) := by
      unfold originalGroupAxisMass
      apply Finset.sum_le_sum
      intro j hj
      have hprod :
          (∏ l ∈ (Finset.univ.erase j),
            ‖originalGroupDyadicFactor chi (c l) (J l) u‖) ≤ M ^ g := by
        calc
          (∏ l ∈ (Finset.univ.erase j),
            ‖originalGroupDyadicFactor chi (c l) (J l) u‖)
            ≤ ∏ _l ∈ (Finset.univ.erase j), M := by
              apply Finset.prod_le_prod
              · intro l hl
                positivity
              · intro l hl
                exact (hzero l).trans (le_max_right _ _)
          _ = M ^ (Finset.univ.erase j).card := by simp
          _ ≤ M ^ g := by
            apply pow_le_pow_right₀ hM1
            simp
      exact mul_le_mul hprod (hone j)
        (norm_nonneg _) (pow_nonneg hM0 _)
    _ = (g : ℝ) * M ^ g * (3 * C) := by
      simp [mul_assoc, nsmul_eq_mul]

end
end ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
