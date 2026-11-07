import ImbalancedChen.P0VariableProfileLipschitzIntegration
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative log-cutoff variation of the actual varying-prime profile

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

Exactly one of the four actual gates depends on T. The other three gates
form a common nonnegative multiplier bounded by one. The scalar step's
proved first-derivative budget therefore gives the exact log-cutoff cost
C1/(width * log N), with no derivative or integral bound as a premise.

The actual varying-prime weight is globally measurable and bounded.
Both cutoff profiles, their difference, and its absolute value are
integrable on every finite-measure region. Integrating the pointwise
bound proves a quantitative L1 cutoff-change budget, including every
positive compact prime box. The corresponding signed integral change is
bounded by the same L1 budget. No prime distribution or PP licence is
asserted.
-/

namespace ImbalancedChen.P0VariableProfileCutoffVariation

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P4B
open ImbalancedChen.P0VariableProfileLipschitzIntegration

/-- The three actual gates which do not move when the lower cutoff T moves. -/
def cutoffFreeProfileProduct (b : ℝ) (N : ℕ) (width : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  (smoothGateUpperStep width (v 1 - v 0) *
    smoothGateUpperStep width (v 0 - b * v 1)) *
    smoothGateUpperStep width (Real.log (N : ℝ) * (1 - v 0 - v 1))

/-- Exact separation of the original lower product wall, without changing
the order, badness, or physical upper-product gates. -/
theorem smoothPhysicalProfile_eq_cutoffFree_mul_gate
    (b : ℝ) (N : ℕ) (T width : ℝ) (v : Fin 2 → ℝ) :
    smoothPhysicalProfile b N T width v =
      cutoffFreeProfileProduct b N width v *
        smoothGateUpperStep width (v 0 + v 1 - Real.log T / Real.log (N : ℝ)) := by
  simp [smoothPhysicalProfile, Fin.prod_univ_four, smoothPhysicalProfileMargin,
    physicalProductWallScale, actualPairMargins, cutoffFreeProfileProduct] <;> ring

/-- The common multiplier contracts every change in the moving gate. -/
theorem cutoffFreeProfileProduct_bounds
    (b : ℝ) (N : ℕ) (width : ℝ) (v : Fin 2 → ℝ) :
    0 ≤ cutoffFreeProfileProduct b N width v ∧
      cutoffFreeProfileProduct b N width v ≤ 1 := by
  have h0 := smoothGateUpperStep_bounds width (v 1 - v 0)
  have h1 := smoothGateUpperStep_bounds width (v 0 - b * v 1)
  have h3 := smoothGateUpperStep_bounds width (Real.log (N : ℝ) * (1 - v 0 - v 1))
  have h01 : smoothGateUpperStep width (v 1 - v 0) *
      smoothGateUpperStep width (v 0 - b * v 1) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul h0.2 h1.2 h1.1 zero_le_one
  constructor
  · exact mul_nonneg (mul_nonneg h0.1 h1.1) h3.1
  · simpa only [cutoffFreeProfileProduct, one_mul] using
      mul_le_mul h01 h3.2 h3.1 zero_le_one

/-- The actual scalar transition is globally Lipschitz, with one constant
chosen before the positive width and the two real arguments. -/
theorem exists_smoothGateUpperStep_first_Lipschitz_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width → ∀ x y : ℝ,
      |smoothGateUpperStep width x - smoothGateUpperStep width y| ≤
        (C1 / width) * |x - y| := by
  obtain ⟨C1, hC1, hbudget⟩ := exists_smoothGateUpperStep_derivative_budget 1
  refine ⟨C1, hC1, ?_⟩
  intro width hwidth x y
  have hd : ∀ z ∈ (univ : Set ℝ), DifferentiableAt ℝ (smoothGateUpperStep width) z := by
    intro z _hz
    exact (contDiff_smoothGateUpperStep width (n := 1)).differentiable_one z
  have hb : ∀ z ∈ (univ : Set ℝ), ‖deriv (smoothGateUpperStep width) z‖ ≤ C1 / width := by
    intro z _hz
    simpa only [iteratedDeriv_one, pow_one, Real.norm_eq_abs] using hbudget width hwidth z
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    hd hb (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using h

/-- A genuine quantitative change-of-cutoff bound on the full physical
plane. The lower gate has exactly the normalized log-cutoff displacement. -/
theorem exists_smoothPhysicalProfile_log_cutoff_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width →
      ∀ b : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ T S : ℝ, ∀ v : Fin 2 → ℝ,
        |smoothPhysicalProfile b N T width v - smoothPhysicalProfile b N S width v| ≤
          (C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S| := by
  obtain ⟨C1, hC1, hstep⟩ := exists_smoothGateUpperStep_first_Lipschitz_budget
  refine ⟨C1, hC1, ?_⟩
  intro width hwidth b N hN T S v
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hfree := cutoffFreeProfileProduct_bounds b N width v
  rw [smoothPhysicalProfile_eq_cutoffFree_mul_gate b N T width v,
    smoothPhysicalProfile_eq_cutoffFree_mul_gate b N S width v,
    ← mul_sub, abs_mul, abs_of_nonneg hfree.1]
  calc
    _ ≤ 1 * |smoothGateUpperStep width (v 0 + v 1 - Real.log T / Real.log (N : ℝ)) -
        smoothGateUpperStep width (v 0 + v 1 - Real.log S / Real.log (N : ℝ))| :=
      mul_le_mul_of_nonneg_right hfree.2 (abs_nonneg _)
    _ = |smoothGateUpperStep width (v 0 + v 1 - Real.log T / Real.log (N : ℝ)) -
        smoothGateUpperStep width (v 0 + v 1 - Real.log S / Real.log (N : ℝ))| := one_mul _
    _ ≤ (C1 / width) * |(v 0 + v 1 - Real.log T / Real.log (N : ℝ)) -
        (v 0 + v 1 - Real.log S / Real.log (N : ℝ))| := hstep width hwidth _ _
    _ = (C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S| := by
      have hsub : (v 0 + v 1 - Real.log T / Real.log (N : ℝ)) -
          (v 0 + v 1 - Real.log S / Real.log (N : ℝ)) =
          -((Real.log T - Real.log S) / Real.log (N : ℝ)) := by ring
      rw [hsub, abs_neg, abs_div, abs_of_pos hlog]
      ring

/-- The same bound is valid for the actual varying-prime profile, uniformly
in the prime-variable point. Positivity of p is not needed for this bound. -/
theorem exists_smoothPrimeVariableProfile_log_cutoff_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width →
      ∀ b : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ T S : ℝ, ∀ p : Fin 2 → ℝ,
        |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N S width p| ≤
          (C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S| := by
  obtain ⟨C1, hC1, hphysical⟩ := exists_smoothPhysicalProfile_log_cutoff_budget
  exact ⟨C1, hC1, fun width hwidth b N hN T S p =>
    hphysical width hwidth b N hN T S (primeVariableLogPoint N p)⟩

/-- In the actual logarithmic cutoff coordinate tau, this is a globally
Lipschitz family with exact constant C1/(width * log N). -/
theorem exists_smoothPrimeVariableProfile_exp_cutoff_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width →
      ∀ b : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ tau sigma : ℝ, ∀ p : Fin 2 → ℝ,
        |smoothPrimeVariableProfile b N (Real.exp tau) width p -
          smoothPrimeVariableProfile b N (Real.exp sigma) width p| ≤
          (C1 / (width * Real.log (N : ℝ))) * |tau - sigma| := by
  obtain ⟨C1, hC1, hbudget⟩ := exists_smoothPrimeVariableProfile_log_cutoff_budget
  refine ⟨C1, hC1, ?_⟩
  intro width hwidth b N hN tau sigma p
  simpa only [Real.log_exp] using hbudget width hwidth b N hN (Real.exp tau) (Real.exp sigma) p

/-- The actual difference and its absolute value are integrable on every
finite-measure region, including prime boxes and measurable subregions. -/
theorem integrableOn_smoothPrimeVariableProfile_cutoff_difference
    (b : ℝ) (N : ℕ) (T S width : ℝ)
    (μ : Measure (Fin 2 → ℝ)) (s : Set (Fin 2 → ℝ)) (hs : μ s ≠ ∞) :
    IntegrableOn (fun p => smoothPrimeVariableProfile b N T width p -
      smoothPrimeVariableProfile b N S width p) s μ ∧
    IntegrableOn (fun p => |smoothPrimeVariableProfile b N T width p -
      smoothPrimeVariableProfile b N S width p|) s μ := by
  have hT := integrableOn_smoothPrimeVariableProfile_of_measure_ne_top b N T width μ s hs
  have hS := integrableOn_smoothPrimeVariableProfile_of_measure_ne_top b N S width μ s hs
  exact ⟨hT.sub hS, (hT.sub hS).abs⟩

/-- Finite-region L1 change-of-cutoff budget, proved by integrating the
actual pointwise gate estimate. Its constant precedes every region,
measure, prime variable, target, cutoff, and width. -/
theorem exists_smoothPrimeVariableProfile_log_cutoff_L1_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width →
      ∀ b : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ T S : ℝ,
      ∀ μ : Measure (Fin 2 → ℝ), ∀ s : Set (Fin 2 → ℝ), μ s ≠ ∞ →
        (∫ p in s, |smoothPrimeVariableProfile b N T width p -
          smoothPrimeVariableProfile b N S width p| ∂μ) ≤
          ((C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S|) * μ.real s := by
  obtain ⟨C1, hC1, hpointwise⟩ := exists_smoothPrimeVariableProfile_log_cutoff_budget
  refine ⟨C1, hC1, ?_⟩
  intro width hwidth b N hN T S μ s hs
  have habs := (integrableOn_smoothPrimeVariableProfile_cutoff_difference b N T S width μ s hs).2
  let D : ℝ := (C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S|
  have hconst : IntegrableOn (fun _ : Fin 2 → ℝ => D) s μ := integrableOn_const hs
  calc
    _ ≤ ∫ _ in s, D ∂μ :=
      integral_mono habs hconst (fun p => hpointwise width hwidth b N hN T S p)
    _ = D * μ.real s := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- The signed cutoff-integral change is paid by that same genuine L1
budget, with integrability derived from the actual bounded profiles. -/
theorem exists_smoothPrimeVariableProfile_log_cutoff_integral_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width →
      ∀ b : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ T S : ℝ,
      ∀ μ : Measure (Fin 2 → ℝ), ∀ s : Set (Fin 2 → ℝ), μ s ≠ ∞ →
        |(∫ p in s, smoothPrimeVariableProfile b N T width p ∂μ) -
          (∫ p in s, smoothPrimeVariableProfile b N S width p ∂μ)| ≤
          ((C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S|) * μ.real s := by
  obtain ⟨C1, hC1, hL1⟩ := exists_smoothPrimeVariableProfile_log_cutoff_L1_budget
  refine ⟨C1, hC1, ?_⟩
  intro width hwidth b N hN T S μ s hs
  have hT := integrableOn_smoothPrimeVariableProfile_of_measure_ne_top b N T width μ s hs
  have hS := integrableOn_smoothPrimeVariableProfile_of_measure_ne_top b N S width μ s hs
  rw [← integral_sub hT hS]
  calc
    _ ≤ ∫ p in s, |smoothPrimeVariableProfile b N T width p -
        smoothPrimeVariableProfile b N S width p| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := μ.restrict s)
          (fun p => smoothPrimeVariableProfile b N T width p -
            smoothPrimeVariableProfile b N S width p))
    _ ≤ _ := hL1 width hwidth b N hN T S μ s hs

/-- Actual positive-prime-box harmonic L1 cutoff variation. The density
is the literal product of 1/p_i, and its actual integral is retained in
the bound. Finiteness and integrability come from positive-box continuity,
not an assumed weighted norm or target integral estimate. -/
theorem exists_smoothPrimeVariableProfile_harmonic_log_cutoff_L1_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width →
      ∀ b : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ T S a u : ℝ, 0 < a →
      ∀ μ : Measure (Fin 2 → ℝ), μ (Icc (fun _ => a) (fun _ => u)) ≠ ∞ →
        IntegrableOn (fun p : Fin 2 → ℝ =>
          |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N S width p| *
            ∏ i : Fin 2, 1 / p i) (Icc (fun _ => a) (fun _ => u)) μ ∧
        (∫ p in Icc (fun _ : Fin 2 => a) (fun _ => u),
          |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N S width p| *
            ∏ i : Fin 2, 1 / p i ∂μ) ≤
          ((C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S|) *
            (∫ p in Icc (fun _ : Fin 2 => a) (fun _ => u), ∏ i : Fin 2, 1 / p i ∂μ) := by
  obtain ⟨C1, hC1, hpointwise⟩ := exists_smoothPrimeVariableProfile_log_cutoff_budget
  refine ⟨C1, hC1, ?_⟩
  intro width hwidth b N hN T S a u ha μ hμ
  let B : Set (Fin 2 → ℝ) := Icc (fun _ => a) (fun _ => u)
  let H : (Fin 2 → ℝ) → ℝ := fun p => ∏ i : Fin 2, 1 / p i
  let D : ℝ := (C1 / (width * Real.log (N : ℝ))) * |Real.log T - Real.log S|
  have hB : IsCompact B := isCompact_Icc
  have hpositive : ∀ p ∈ B, ∀ i : Fin 2, 0 < p i := by
    intro p hp i
    exact ha.trans_le (hp.1 i)
  have hprofile (R : ℝ) : ContinuousOn (smoothPrimeVariableProfile b N R width) B :=
    (contDiffOn_smoothPrimeVariableProfile (n := 0) b N R width).continuousOn.mono
      (fun p hp => hpositive p hp)
  have hcoord (i : Fin 2) : ContinuousOn (fun p : Fin 2 → ℝ => 1 / p i) B :=
    continuousOn_const.div
      (continuous_apply i : Continuous (fun p : Fin 2 → ℝ => p i)).continuousOn
      (fun p hp => (hpositive p hp i).ne')
  have hH : ContinuousOn H B := by
    simpa only [H, Fin.prod_univ_two] using (hcoord 0).mul (hcoord 1)
  have hHnonneg : ∀ p ∈ B, 0 ≤ H p := by
    intro p hp
    exact Finset.prod_nonneg (fun i _hi => div_nonneg zero_le_one (hpositive p hp i).le)
  have hleft : IntegrableOn (fun p =>
      |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N S width p| * H p)
      B μ :=
    (((hprofile T).sub (hprofile S)).abs.mul hH).integrableOn_of_subset_isCompact
      hB hB.measurableSet Subset.rfl hμ
  have hright : IntegrableOn (fun p => D * H p) B μ :=
    (hH.const_mul D).integrableOn_of_subset_isCompact hB hB.measurableSet Subset.rfl hμ
  refine ⟨hleft, ?_⟩
  calc
    _ ≤ ∫ p in B, D * H p ∂μ := by
      apply integral_mono_ae hleft hright
      filter_upwards [ae_restrict_mem hB.measurableSet] with p hp
      exact mul_le_mul_of_nonneg_right (hpointwise width hwidth b N hN T S p) (hHnonneg p hp)
    _ = D * ∫ p in B, H p ∂μ := integral_const_mul D H
end

end ImbalancedChen.P0VariableProfileCutoffVariation