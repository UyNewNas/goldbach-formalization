import ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
import Mathlib.Tactic

/-!
P3.6: incidence sparsification and EXACT translated support of the ACTUAL
original finite group-occurrence product and its first coordinate derivative.

The group index is an OCCURRENCE, never a quotient by repeated subsets.
The positive physical scales c_j are independent. The support is the
SHIFTED slanted strip sum_(i in J_j) u_i + log(c_j) in [-log 2,log 2],
not an unshifted global box and not a sharp artificial group cutoff.

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b, PP completion §4 (F).
Pinned toolchain: Lean v4.33.0-rc1;
Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Only FIRST actual product derivatives. Does NOT prove higher ordered
Leibniz, all U5/trim, Fourier tails, common T/m(N), or same-rho PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupIncidenceSupport
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBCanonicalGeometryDerivative

/-- Genuine group occurrences containing the requested original axis. -/
def incidentGroups {g : ℕ} (J : Fin g → Finset (Fin 6))
    (i : Fin 6) : Finset (Fin g) :=
  Finset.univ.filter (fun j => i ∈ J j)

/-- An original factor has zero actual axis derivative when that axis
is absent from its literal positional group, for every real scale. -/
theorem factor_axisDeriv_zero_of_not_mem
    (chi : ℝ → ℂ) (c : ℝ) (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) (hi : i ∉ J) :
    actualAxisDeriv (originalGroupDyadicFactor chi c J) i u = 0 := by
  change originalOrderedAxisDeriv [i]
    (originalGroupDyadicFactor chi c J) u = 0
  rw [originalGroupOrderedDeriv_exact chi c J [i] u]
  simp [axesWithinGroup, hi]

/-- Exact FIRST product derivative: only physically incident group
occurrences survive. Equal group subsets with distinct scales are kept. -/
theorem originalGroupProduct_axisDeriv_eq_incident
    {g : ℕ} (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (originalGroupProduct chi c J) i u =
      ∑ j ∈ incidentGroups J i,
        (∏ l ∈ (Finset.univ.erase j),
          originalGroupDyadicFactor chi (c l) (J l) u) *
          actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u := by
  classical
  rw [originalGroupProduct_axisDeriv chi hchi c J u i]
  unfold incidentGroups
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i ∈ J j
  · simp [hij]
  · have hz := factor_axisDeriv_zero_of_not_mem chi (c j) (J j) u i hij
    simp [hij, hz]

/-- If no genuine group occurrence contains a coordinate, the whole
physical grouped product is constant along that coordinate. -/
theorem originalGroupProduct_axisDeriv_zero_of_no_incident
    {g : ℕ} (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6)
    (hnone : ∀ j : Fin g, i ∉ J j) :
    actualAxisDeriv (originalGroupProduct chi c J) i u = 0 := by
  rw [originalGroupProduct_axisDeriv_eq_incident chi hchi c J u i]
  have hempty : incidentGroups J i = ∅ := by
    ext j
    simp [incidentGroups, hnone j]
  simp [hempty]

/-- Genuine incident-group L1-type pointwise MASS; unlike the previous
g-term envelope this contains only groups that actually see the axis. -/
theorem originalGroupProduct_axisDeriv_norm_le_incident
    {g : ℕ} (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ ≤
      ∑ j ∈ incidentGroups J i,
        (∏ l ∈ (Finset.univ.erase j),
          ‖originalGroupDyadicFactor chi (c l) (J l) u‖) *
          ‖actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖ := by
  rw [originalGroupProduct_axisDeriv_eq_incident chi hchi c J u i]
  calc
    ‖∑ j ∈ incidentGroups J i,
      (∏ l ∈ (Finset.univ.erase j),
        originalGroupDyadicFactor chi (c l) (J l) u) *
        actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖
      ≤ ∑ j ∈ incidentGroups J i,
        ‖(∏ l ∈ (Finset.univ.erase j),
          originalGroupDyadicFactor chi (c l) (J l) u) *
          actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u‖ :=
        norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [norm_mul, norm_prod]

/-- Literal dyadic factor vanishes outside its TRUE c-shifted strip.
This is not the original HB rectangular support statement. -/
theorem factor_zero_outside_shifted_group_strip
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : ℝ) (hc : 0 < c) (J : Finset (Fin 6))
    (u : Fin 6 → ℝ)
    (hout : originalGroupSum J u + Real.log c ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    originalGroupDyadicFactor chi c J u = 0 := by
  simpa only [originalOrderedAxisDeriv] using
    (originalGroupOrderedDeriv_zero_outside chi hchi hsmall hlarge
      c hc J ([] : List (Fin 6)) u hout)

/-- Its actual first coordinate derivative also vanishes outside that
same shifted strip, including when the coordinate belongs to J. -/
theorem factor_axisDeriv_zero_outside_shifted_group_strip
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : ℝ) (hc : 0 < c) (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6)
    (hout : originalGroupSum J u + Real.log c ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    actualAxisDeriv (originalGroupDyadicFactor chi c J) i u = 0 := by
  simpa only [originalOrderedAxisDeriv] using
    (originalGroupOrderedDeriv_zero_outside chi hchi hsmall hlarge
      c hc J [i] u hout)

/-- The TRUE complete original group-occurrence product vanishes as
soon as any ONE physical shifted group factor is outside support. -/
theorem originalGroupProduct_zero_outside_any_group
    {g : ℕ} (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6)) (u : Fin 6 → ℝ)
    (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    originalGroupProduct chi c J u = 0 := by
  unfold originalGroupProduct
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact factor_zero_outside_shifted_group_strip
    chi hchi hsmall hlarge (c j) (hc j) (J j) u hout

/-- The FIRST actual derivative of the entire product also vanishes
outside ANY one original group strip: differentiated term j has a zero
derivative, every other term has the zero j factor. The result retains
one integer physical scale per occurrence and does not introduce a wall. -/
theorem originalGroupProduct_axisDeriv_zero_outside_any_group
    {g : ℕ} (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6)) (u : Fin 6 → ℝ)
    (i : Fin 6) (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    actualAxisDeriv (originalGroupProduct chi c J) i u = 0 := by
  classical
  rw [originalGroupProduct_axisDeriv chi hchi c J u i]
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hlj : l = j
  · subst l
    have hz := factor_axisDeriv_zero_outside_shifted_group_strip
      chi hchi hsmall hlarge (c j) (hc j) (J j) u i hout
    simp [hz]
  · have hjmem : j ∈ (Finset.univ.erase l : Finset (Fin g)) :=
      Finset.mem_erase.mpr ⟨Ne.symm hlj, Finset.mem_univ j⟩
    have hprod :
        (∏ q ∈ (Finset.univ.erase l),
          originalGroupDyadicFactor chi (c q) (J q) u) = 0 := by
      apply Finset.prod_eq_zero hjmem
      exact factor_zero_outside_shifted_group_strip
        chi hchi hsmall hlarge (c j) (hc j) (J j) u hout
    simp [hprod]

end
end ImbalancedChen.P3HBOriginalGroupIncidenceSupport
