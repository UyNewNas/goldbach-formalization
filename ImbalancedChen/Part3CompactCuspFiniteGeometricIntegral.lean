import ImbalancedChen.Part3CompactCuspGeometricFubini

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The genuine actual compact-cusp Fourier coefficient, integrated against
an actual compact positive radial profile, has a finite geometric
Kloosterman double-integral expansion. A common cutoff is proved on the
outer support. Joint L1 of each actual Bruhat kernel supplies every
Fubini and finite-sum exchange. This is an integrated geometric Fourier
identity; the quotient-inner-product/chart identification remains separate.
-/

namespace ImbalancedChen.Part3.CompactCuspFiniteGeometricIntegral20261025a

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.ActualCompactBruhatAllModuli20261025a
open ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

/-- Outer mode m, inner seed mode n, with the canonical y^-2 weight. -/
def weightedActualPoincareFourier (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then
    radialWeight ψ y * actualCompactPoincareFourier N y hy n m φ
  else 0

/-- The common cutoff is valid wherever the OUTER radial seed is nonzero. -/
theorem weightedActualPoincareFourier_eq_finite (N : ℕ) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfloorφ : ∀ t, φ t ≠ 0 → a ≤ t) (hfloorψ : ∀ t, ψ t ≠ 0 → b ≤ t)
    (C : ℕ+) (hC : 1 / (a * b) < (C : ℝ)) (y : ℝ) :
    weightedActualPoincareFourier N m n ψ φ y =
      (if m = n then radialWeight ψ y * φ y else 0) +
      ∑ c ∈ Finset.Icc (1 : ℕ+) C,
        if N ∣ (c : ℕ) then
          kloosterman (c : ℕ) m n *
            (radialWeight ψ y * actualFourierSlice (c : ℝ)
              (by exact_mod_cast (Nat.ne_of_gt c.property)) m n φ y)
        else 0 := by
  classical
  by_cases hzero : ψ y = 0
  · simp [weightedActualPoincareFourier, radialWeight, hzero]
  · have hy : 0 < y := hposψ (subset_tsupport ψ hzero)
    have hby := hfloorψ y hzero
    have hcut : 1 / (a * y) < (C : ℝ) :=
      lt_of_le_of_lt (one_div_le_one_div_of_le (mul_pos ha hb) (mul_le_mul_of_nonneg_left hby ha.le)) hC
    rw [weightedActualPoincareFourier, dif_pos hy,
      actualCompactPoincareFourier_eq_finite_kloosterman N y hy n m φ hφ hcφ hposφ a ha hfloorφ C hcut]
    simp only [mul_add, Finset.mul_sum]
    congr 1
    · split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro c hc
      by_cases hNc : N ∣ (c : ℕ)
      · simp only [if_pos hNc, actualFourierSlice, dif_pos hy]
        ring
      · simp [hNc]

/-- The diagonal integrand is genuinely L1, even across y=0. -/
theorem radial_diagonal_integrable (ψ φ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) : Integrable (fun y => radialWeight ψ y * φ y) :=
  ((radialWeight_continuous ψ hψ hposψ).mul hφ).integrable_of_hasCompactSupport
    (radialWeight_hasCompactSupport ψ hcψ).mul_right

/-- Finite geometric expansion with actual derived L1 and actual Fubini.
The zero-c diagonal occurs once, with no center multiplicity factor. -/
theorem integrated_actualFourier_eq_finite_geometric (N : ℕ) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfloorφ : ∀ t, φ t ≠ 0 → a ≤ t) (hfloorψ : ∀ t, ψ t ≠ 0 → b ≤ t)
    (C : ℕ+) (hC : 1 / (a * b) < (C : ℝ)) :
    (∫ y : ℝ, weightedActualPoincareFourier N m n ψ φ y) =
      (if m = n then ∫ y : ℝ, radialWeight ψ y * φ y else 0) +
      ∑ c ∈ Finset.Icc (1 : ℕ+) C,
        if N ∣ (c : ℕ) then
          kloosterman (c : ℕ) m n *
            ∫ x : ℝ, ∫ y : ℝ, geometricPairKernel (c : ℝ) m n ψ φ (x, y)
        else 0 := by
  classical
  let S := Finset.Icc (1 : ℕ+) C
  let diag : ℝ → ℂ := fun y => if m = n then radialWeight ψ y * φ y else 0
  let term : ℕ+ → ℝ → ℂ := fun c y =>
    if N ∣ (c : ℕ) then kloosterman (c : ℕ) m n *
      (radialWeight ψ y * actualFourierSlice (c : ℝ)
        (by exact_mod_cast (Nat.ne_of_gt c.property)) m n φ y) else 0
  have hd : Integrable diag := by
    by_cases hmn : m = n
    · simpa only [diag, if_pos hmn] using radial_diagonal_integrable ψ φ hψ hcψ hposψ hφ
    · simp only [diag, if_neg hmn]
      exact integrable_zero _ _ _
  have ht (c : ℕ+) : Integrable (term c) := by
    by_cases hNc : N ∣ (c : ℕ)
    · simpa only [term, if_pos hNc] using
        (weighted_actualFourierSlice_integrable (c : ℝ)
          (by exact_mod_cast (Nat.ne_of_gt c.property)) m n ψ φ hψ hcψ hposψ hφ hcφ hposφ).const_mul
            (kloosterman (c : ℕ) m n)
    · simp only [term, if_neg hNc]
      exact integrable_zero _ _ _
  have heq : weightedActualPoincareFourier N m n ψ φ = fun y => diag y + ∑ c ∈ S, term c y := by
    funext y
    exact weightedActualPoincareFourier_eq_finite N m n ψ φ hposψ hφ hcφ hposφ
      a b ha hb hfloorφ hfloorψ C hC y
  rw [heq, integral_add hd (integrable_finsetSum S (fun c _ => ht c)),
    integral_finsetSum S (fun c _ => ht c)]
  congr 1
  · by_cases hmn : m = n <;> simp [diag, hmn]
  · apply Finset.sum_congr rfl
    intro c hc
    by_cases hNc : N ∣ (c : ℕ)
    · simp only [term, if_pos hNc, integral_const_mul]
      rw [fixed_modulus_geometric_double_integral (c : ℝ)
        (by exact_mod_cast (Nat.ne_of_gt c.property)) m n ψ φ hψ hcψ hposψ hφ hcφ hposφ]
    · simp [term, hNc]

/-- A finite geometric cutoff exists from the two actual compact positive
supports. No summability, absolute-integral, or cutoff supplier is needed. -/
theorem exists_integrated_actualFourier_finite_geometric (N : ℕ) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℕ+,
      (∫ y : ℝ, weightedActualPoincareFourier N m n ψ φ y) =
        (if m = n then ∫ y : ℝ, radialWeight ψ y * φ y else 0) +
        ∑ c ∈ Finset.Icc (1 : ℕ+) C,
          if N ∣ (c : ℕ) then
            kloosterman (c : ℕ) m n *
              ∫ x : ℝ, ∫ y : ℝ, geometricPairKernel (c : ℝ) m n ψ φ (x, y)
          else 0 := by
  obtain ⟨a, ha, hfloorφ⟩ := radial_support_positive_floor φ hcφ hposφ
  obtain ⟨b, hb, hfloorψ⟩ := radial_support_positive_floor ψ hcψ hposψ
  obtain ⟨C, hC⟩ := exists_positive_modulus_cutoff a b ha hb
  exact ⟨C, integrated_actualFourier_eq_finite_geometric N m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
    a b ha hb hfloorφ hfloorψ C hC⟩

end
end ImbalancedChen.Part3.CompactCuspFiniteGeometricIntegral20261025a
