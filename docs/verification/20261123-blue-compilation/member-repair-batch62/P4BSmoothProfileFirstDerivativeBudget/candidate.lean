import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# First derivative of the actual smooth physical profile

SOURCE-ONLY / YELLOW / UNCOMPILED, 2026-10-24.

The four actual affine wall rows and their offsets are defined explicitly.
The physical upper-product row is -log N times the sum of the coordinate
projections. The exact Fréchet derivative is a four-term Leibniz sum, not
an assumed smoothness certificate. The scalar C1/width supplier is proved
in P4BSmoothStepDerivativeBudget and instantiated at order one here.

This is quantitative first-order profile control only. It asserts no P3
geometric licence, higher-order licence, prime-variable pullback budget,
Siegel--Walfisz input, distribution estimate or spectral estimate.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped Classical BigOperators

/-- Linear parts of order, badness, lower product and physical upper product. -/
def smoothPhysicalWallRow (b : ℝ) (N : ℕ) (i : Fin 4) :
    (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ![(ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) - (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ),
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) - b • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ),
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) + (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ),
    (-Real.log (N : ℝ)) • ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) + (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ))] i

/-- Affine offsets, including log N at the physical upper-product wall. -/
def smoothPhysicalWallOffset (b : ℝ) (N : ℕ) (T : ℝ) : Fin 4 → ℝ :=
  ![0, 0, -Real.log T / Real.log (N : ℝ), Real.log (N : ℝ)]

/-- Exact dictionary from the defined actual profile margins to affine rows. -/
theorem smoothPhysicalProfileMargin_eq_offset_add_row
    (b : ℝ) (N : ℕ) (T : ℝ) (v : Fin 2 → ℝ) (i : Fin 4) :
    smoothPhysicalProfileMargin b N T v i =
      smoothPhysicalWallOffset b N T i + smoothPhysicalWallRow b N i v := by
  fin_cases i <;>
    simp [smoothPhysicalProfileMargin, physicalProductWallScale, actualPairMargins,
      smoothPhysicalWallOffset, smoothPhysicalWallRow] <;> ring

/-- Actual line slope, for consumers deriving higher directional derivatives. -/
theorem smoothPhysicalProfileMargin_line
    (b : ℝ) (N : ℕ) (T : ℝ) (x h : Fin 2 → ℝ) (t : ℝ) (i : Fin 4) :
    smoothPhysicalProfileMargin b N T (x + t • h) i =
      smoothPhysicalProfileMargin b N T x i + t * smoothPhysicalWallRow b N i h := by
  rw [smoothPhysicalProfileMargin_eq_offset_add_row,
    smoothPhysicalProfileMargin_eq_offset_add_row]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- Every row has the displayed uniform bound. The factor log N at wall 3
is retained; the constant 2+|b| is chosen before N and every profile point. -/
theorem smoothPhysicalWallRow_norm_le (b : ℝ) (N : ℕ) (hN : 2 ≤ N) (i : Fin 4) :
    ‖smoothPhysicalWallRow b N i‖ ≤ (2 + |b|) * (1 + Real.log (N : ℝ)) := by
  let p0 : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let p1 : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have hp (j : Fin 2) :
      ‖(ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v j
  have hp0 : ‖p0‖ ≤ 1 := hp 0
  have hp1 : ‖p1‖ ≤ 1 := hp 1
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have habs := abs_nonneg b
  have habslog := mul_nonneg habs hlog
  have hrow0 : ‖p1 - p0‖ ≤ 2 := by
    have ht := norm_sub_le p1 p0
    linarith only [ht, hp0, hp1]
  have hrow1 : ‖p0 - b • p1‖ ≤ 1 + |b| := by
    calc
      ‖p0 - b • p1‖ ≤ ‖p0‖ + ‖b • p1‖ := norm_sub_le _ _
      _ = ‖p0‖ + |b| * ‖p1‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 + |b| := by
        simpa only [mul_one] using
          add_le_add hp0 (mul_le_mul_of_nonneg_left hp1 habs)
  have hrow2 : ‖p0 + p1‖ ≤ 2 := by
    have ht := norm_add_le p0 p1
    linarith only [ht, hp0, hp1]
  have hrow3 : ‖(-Real.log (N : ℝ)) • (p0 + p1)‖ ≤ 2 * Real.log (N : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hlog]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hrow2 hlog
  have h0 : ‖p1 - p0‖ ≤ (2 + |b|) * (1 + Real.log (N : ℝ)) := by
    nlinarith only [hrow0, habs, hlog, habslog]
  have h1 : ‖p0 - b • p1‖ ≤ (2 + |b|) * (1 + Real.log (N : ℝ)) := by
    nlinarith only [hrow1, habs, hlog, habslog]
  have h2 : ‖p0 + p1‖ ≤ (2 + |b|) * (1 + Real.log (N : ℝ)) := by
    nlinarith only [hrow2, habs, hlog, habslog]
  have h3 : ‖(-Real.log (N : ℝ)) • (p0 + p1)‖ ≤
      (2 + |b|) * (1 + Real.log (N : ℝ)) := by
    nlinarith only [hrow3, habs, hlog, habslog]
  fin_cases i
  · simpa [smoothPhysicalWallRow, p0, p1] using h0
  · simpa [smoothPhysicalWallRow, p0, p1] using h1
  · simpa [smoothPhysicalWallRow, p0, p1] using h2
  · simpa [smoothPhysicalWallRow, p0, p1] using h3

/-- Uniform actual affine line-slope bound in the original Pi norm. -/
theorem smoothPhysicalWallRow_apply_abs_le
    (b : ℝ) (N : ℕ) (hN : 2 ≤ N) (i : Fin 4) (h : Fin 2 → ℝ) :
    |smoothPhysicalWallRow b N i h| ≤
      ((2 + |b|) * (1 + Real.log (N : ℝ))) * ‖h‖ := by
  have ht := (smoothPhysicalWallRow b N i).le_opNorm h
  exact (show |smoothPhysicalWallRow b N i h| ≤
      ‖smoothPhysicalWallRow b N i‖ * ‖h‖ by simpa only [Real.norm_eq_abs] using ht).trans
    (mul_le_mul_of_nonneg_right (smoothPhysicalWallRow_norm_le b N hN i) (norm_nonneg h))

/-- The actual affine margin has exactly its explicitly defined wall row. -/
theorem hasFDerivAt_smoothPhysicalProfileMargin
    (b : ℝ) (N : ℕ) (T : ℝ) (v : Fin 2 → ℝ) (i : Fin 4) :
    HasFDerivAt (fun x => smoothPhysicalProfileMargin b N T x i)
      (smoothPhysicalWallRow b N i) v := by
  have hr : HasFDerivAt
      (fun x : Fin 2 → ℝ => smoothPhysicalWallOffset b N T i + smoothPhysicalWallRow b N i x)
      (smoothPhysicalWallRow b N i) v :=
    (smoothPhysicalWallRow b N i).hasFDerivAt.const_add (smoothPhysicalWallOffset b N T i)
  simpa only [smoothPhysicalProfileMargin_eq_offset_add_row] using hr

/-- Real scalar chain rule for each actual smooth factor. -/
theorem hasFDerivAt_smoothPhysicalProfileFactor
    (b : ℝ) (N : ℕ) (T width : ℝ) (v : Fin 2 → ℝ) (i : Fin 4) :
    HasFDerivAt (fun x => smoothGateUpperStep width (smoothPhysicalProfileMargin b N T x i))
      (deriv (smoothGateUpperStep width) (smoothPhysicalProfileMargin b N T v i) •
        smoothPhysicalWallRow b N i) v := by
  have hs : HasDerivAt (smoothGateUpperStep width)
      (deriv (smoothGateUpperStep width) (smoothPhysicalProfileMargin b N T v i))
      (smoothPhysicalProfileMargin b N T v i) :=
    ((contDiff_smoothGateUpperStep width (n := 1)).differentiable_one _).hasDerivAt
  exact hs.comp_hasFDerivAt
    (h₂ := smoothGateUpperStep width)
    (f := fun x : Fin 2 → ℝ => smoothPhysicalProfileMargin b N T x i)
    v (hasFDerivAt_smoothPhysicalProfileMargin b N T v i)

/-- The genuine four-term Leibniz sum: the scalar derivative and wall CLM
are multiplied by precisely the other three genuine smooth factors. -/
theorem fderiv_smoothPhysicalProfile_eq_leibniz
    (b : ℝ) (N : ℕ) (T width : ℝ) (v : Fin 2 → ℝ) :
    fderiv ℝ (smoothPhysicalProfile b N T width) v =
      ∑ i : Fin 4,
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v j)) •
          (deriv (smoothGateUpperStep width) (smoothPhysicalProfileMargin b N T v i) •
            smoothPhysicalWallRow b N i) := by
  have hp := HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin 4)))
    (fun i _hi => hasFDerivAt_smoothPhysicalProfileFactor b N T width v i)
  exact hp.fderiv

/-- One genuine scalar constant is chosen before b, width, N, T and the
all-space point. No first-derivative budget is assumed by this theorem. -/
theorem exists_smoothPhysicalProfile_first_derivative_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ b width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ v : Fin 2 → ℝ,
        ‖fderiv ℝ (smoothPhysicalProfile b N T width) v‖ ≤
          (4 * C1 * (2 + |b|) / width) * (1 + Real.log (N : ℝ)) := by
  obtain ⟨C1, hC1, hscalar⟩ := exists_smoothGateUpperStep_derivative_budget 1
  refine ⟨C1, hC1, ?_⟩
  intro b width hwidth N hN T v
  have hC1nonneg : 0 ≤ C1 := zero_le_one.trans hC1
  have hderiv (i : Fin 4) :
      |deriv (smoothGateUpperStep width) (smoothPhysicalProfileMargin b N T v i)| ≤
        C1 / width := by
    simpa only [iteratedDeriv_one, pow_one] using
      hscalar width hwidth (smoothPhysicalProfileMargin b N T v i)
  have hterm (i : Fin 4) :
      ‖(∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v j)) •
          (deriv (smoothGateUpperStep width) (smoothPhysicalProfileMargin b N T v i) •
            smoothPhysicalWallRow b N i)‖ ≤
        (C1 / width) * ((2 + |b|) * (1 + Real.log (N : ℝ))) := by
    have hpnonneg : 0 ≤ ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
        smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v j) :=
      Finset.prod_nonneg (fun j _hj => (smoothGateUpperStep_bounds width _).1)
    have hple : (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
        smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v j)) ≤ 1 :=
      Finset.prod_le_one (fun j _hj => (smoothGateUpperStep_bounds width _).1)
        (fun j _hj => (smoothGateUpperStep_bounds width _).2)
    have hpnorm : ‖∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
        smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v j)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpnonneg]
      exact hple
    have hf :
        ‖deriv (smoothGateUpperStep width) (smoothPhysicalProfileMargin b N T v i) •
          smoothPhysicalWallRow b N i‖ ≤
        (C1 / width) * ((2 + |b|) * (1 + Real.log (N : ℝ))) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hderiv i) (smoothPhysicalWallRow_norm_le b N hN i)
        (norm_nonneg _) (div_nonneg hC1nonneg hwidth.le)
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right hpnorm (norm_nonneg _)).trans
      (by simpa only [one_mul] using hf)
  rw [fderiv_smoothPhysicalProfile_eq_leibniz]
  calc
    _ ≤ ∑ i : Fin 4,
        ‖(∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v j)) •
          (deriv (smoothGateUpperStep width) (smoothPhysicalProfileMargin b N T v i) •
            smoothPhysicalWallRow b N i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4,
        (C1 / width) * ((2 + |b|) * (1 + Real.log (N : ℝ))) :=
      Finset.sum_le_sum (fun i _hi => hterm i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring

end

end ImbalancedChen.P4B
