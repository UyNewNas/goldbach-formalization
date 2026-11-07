import ImbalancedChen.P0VariableProfileCutoffVariation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Monoid

/-!
# Inverse-width stability of the actual varying-prime four-gate profile

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

The genuine step at width w is the width-one step evaluated at margin/w.
Its proved scalar Lipschitz budget gives the exact inverse-width change
C1 * |w^-1-v^-1| * |margin|. A finite-product contraction proof uses the
actual [0,1] gate bounds, and pays the sum of the four actual margins.

On every positive compact prime box the normalized logarithms, every
actual wall margin, and the literal prime harmonic density are continuous.
Their actual margin-envelope moment is therefore integrable for every
finite box measure. Integrating the proved pointwise estimate gives a
weighted L1 width-change budget with that actual moment on the right.
No target norm, derivative budget, or integral bound is a caller premise.
-/

namespace ImbalancedChen.P0VariableProfileWidthVariation

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P4B
open ImbalancedChen.P0VariableProfileCutoffVariation

/-- Products of real [0,1] factors contract the sum of their individual
changes. The proof is finite telescoping, including the empty family. -/
theorem abs_prod_sub_prod_le_sum_abs_of_unit_interval {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  revert hf hg
  induction s using Finset.induction_on with
  | empty =>
    intro hf hg
    simp
  | @insert a s ha ih =>
    intro hf hg
    have hfsmall : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgsmall : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1 :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hrec := ih hfsmall hgsmall
    have hfa := hf a (Finset.mem_insert_self a s)
    have hPg0 : 0 ≤ ∏ i ∈ s, g i :=
      Finset.prod_nonneg (fun i hi => (hgsmall i hi).1)
    have hPg1 : (∏ i ∈ s, g i) ≤ 1 :=
      Finset.prod_le_one (fun i hi => (hgsmall i hi).1) (fun i hi => (hgsmall i hi).2)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      |f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i| =
          |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
            (f a - g a) * ∏ i ∈ s, g i| := by congr 1; ring
      _ ≤ |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| +
          |(f a - g a) * ∏ i ∈ s, g i| := abs_add_le _ _
      _ = f a * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| +
          |f a - g a| * ∏ i ∈ s, g i := by
        rw [abs_mul, abs_mul, abs_of_nonneg hfa.1, abs_of_nonneg hPg0]
      _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 :=
        add_le_add (mul_le_mul hfa.2 hrec (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hPg1 (abs_nonneg _))
      _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

/-- Exact rescaling to the genuine width-one step, including totalized
zero widths. No surrogate smooth function is introduced. -/
theorem smoothGateUpperStep_eq_width_one (width x : ℝ) :
    smoothGateUpperStep width x = smoothGateUpperStep 1 (x / width) := by
  simp only [smoothGateUpperStep, div_one]

/-- One scalar constant controls inverse-width variation of the actual
step. Positive widths are not needed for this totalized identity. -/
theorem exists_smoothGateUpperStep_inverse_width_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width other x : ℝ,
      |smoothGateUpperStep width x - smoothGateUpperStep other x| ≤
        (C1 * |width⁻¹ - other⁻¹|) * |x| := by
  obtain ⟨C1, hC1, hstep⟩ := exists_smoothGateUpperStep_first_Lipschitz_budget
  refine ⟨C1, hC1, ?_⟩
  intro width other x
  rw [smoothGateUpperStep_eq_width_one width x, smoothGateUpperStep_eq_width_one other x]
  calc
    _ ≤ C1 * |x / width - x / other| := by
      simpa only [div_one] using hstep 1 zero_lt_one (x / width) (x / other)
    _ = (C1 * |width⁻¹ - other⁻¹|) * |x| := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul]
      ring

/-- The literal sum of the four actual margins after the varying-log
pullback. It retains b, N, T, and the physical upper wall's log N factor. -/
def primeMarginEnvelope (b : ℝ) (N : ℕ) (T : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 4, |smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) i|

/-- Width stability of the actual physical profile, with each gate's own
actual affine margin paid once. There is no margin-size hypothesis. -/
theorem exists_smoothPhysicalProfile_inverse_width_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ b : ℝ, ∀ N : ℕ, ∀ T width other : ℝ,
      ∀ v : Fin 2 → ℝ,
        |smoothPhysicalProfile b N T width v - smoothPhysicalProfile b N T other v| ≤
          (C1 * |width⁻¹ - other⁻¹|) *
            ∑ i : Fin 4, |smoothPhysicalProfileMargin b N T v i| := by
  obtain ⟨C1, hC1, hstep⟩ := exists_smoothGateUpperStep_inverse_width_budget
  refine ⟨C1, hC1, ?_⟩
  intro b N T width other v
  change |(∏ i : Fin 4, smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v i)) -
    ∏ i : Fin 4, smoothGateUpperStep other (smoothPhysicalProfileMargin b N T v i)| ≤ _
  calc
    _ ≤ ∑ i : Fin 4,
        |smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v i) -
          smoothGateUpperStep other (smoothPhysicalProfileMargin b N T v i)| :=
      abs_prod_sub_prod_le_sum_abs_of_unit_interval Finset.univ _ _
        (fun i _hi => smoothGateUpperStep_bounds width _)
        (fun i _hi => smoothGateUpperStep_bounds other _)
    _ ≤ ∑ i : Fin 4, (C1 * |width⁻¹ - other⁻¹|) *
        |smoothPhysicalProfileMargin b N T v i| :=
      Finset.sum_le_sum (fun i _hi => hstep width other _)
    _ = (C1 * |width⁻¹ - other⁻¹|) *
        ∑ i : Fin 4, |smoothPhysicalProfileMargin b N T v i| := by
      rw [Finset.mul_sum]

/-- The genuine prime-variable width change is bounded by its actual
four-margin envelope, uniformly in the point and both widths. -/
theorem exists_smoothPrimeVariableProfile_inverse_width_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ b : ℝ, ∀ N : ℕ, ∀ T width other : ℝ,
      ∀ p : Fin 2 → ℝ,
        |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N T other p| ≤
          (C1 * |width⁻¹ - other⁻¹|) * primeMarginEnvelope b N T p := by
  obtain ⟨C1, hC1, hphysical⟩ := exists_smoothPhysicalProfile_inverse_width_budget
  exact ⟨C1, hC1, fun b N T width other p =>
    hphysical b N T width other (primeVariableLogPoint N p)⟩

/-- Every actual margin and its absolute value are continuous on the
positive prime domain; the finite envelope inherits that continuity. -/
theorem continuousOn_primeMarginEnvelope_positive (b : ℝ) (N : ℕ) (T : ℝ) :
    ContinuousOn (primeMarginEnvelope b N T) positivePrimeOrthant := by
  unfold primeMarginEnvelope
  apply continuousOn_finsetSum Finset.univ
  intro i _hi
  have hc : ContDiffOn ℝ 0
      (fun p => smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) i)
      positivePrimeOrthant :=
    (contDiff_smoothPhysicalProfileMargin (n := 0) b N T i).comp_contDiffOn
      (contDiffOn_primeVariableLogPoint (n := 0) N)
  exact hc.continuousOn.abs

private theorem continuousOn_primeHarmonic_positive :
    ContinuousOn (fun p : Fin 2 → ℝ => ∏ i : Fin 2, 1 / p i) positivePrimeOrthant := by
  apply continuousOn_finsetProd Finset.univ
  intro i _hi
  exact continuousOn_const.div
    (continuous_apply i : Continuous (fun p : Fin 2 → ℝ => p i)).continuousOn
    (fun p hp => (hp i).ne')

/-- The actual four-margin harmonic moment is finite on every positive
compact prime box of finite measure. It is proved integrable here rather
than supplied as a target integral hypothesis. -/
theorem integrableOn_primeMarginEnvelope_harmonic_box
    (b : ℝ) (N : ℕ) (T a u : ℝ) (ha : 0 < a)
    (μ : Measure (Fin 2 → ℝ))
    (hμ : μ (Icc (fun _ => a) (fun _ => u)) ≠ ∞) :
    IntegrableOn (fun p : Fin 2 → ℝ => primeMarginEnvelope b N T p *
      ∏ i : Fin 2, 1 / p i) (Icc (fun _ => a) (fun _ => u)) μ := by
  have hpositive : Icc (fun _ : Fin 2 => a) (fun _ => u) ⊆ positivePrimeOrthant := by
    intro p hp i
    exact ha.trans_le (hp.1 i)
  have hc := ((continuousOn_primeMarginEnvelope_positive b N T).mul
    continuousOn_primeHarmonic_positive).mono hpositive
  exact hc.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Icc Subset.rfl hμ

/-- Genuine positive-prime-box harmonic L1 stability under width changes.
The right side retains the actual four-margin harmonic moment; no norm
or integral bound is assumed. Constants precede all widths and boxes. -/
theorem exists_smoothPrimeVariableProfile_harmonic_inverse_width_L1_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ b : ℝ, ∀ N : ℕ, ∀ T width other a u : ℝ,
      0 < a → ∀ μ : Measure (Fin 2 → ℝ),
      μ (Icc (fun _ => a) (fun _ => u)) ≠ ∞ →
        IntegrableOn (fun p : Fin 2 → ℝ =>
          |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N T other p| *
            ∏ i : Fin 2, 1 / p i) (Icc (fun _ => a) (fun _ => u)) μ ∧
        (∫ p in Icc (fun _ : Fin 2 => a) (fun _ => u),
          |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N T other p| *
            ∏ i : Fin 2, 1 / p i ∂μ) ≤
          (C1 * |width⁻¹ - other⁻¹|) *
            (∫ p in Icc (fun _ : Fin 2 => a) (fun _ => u),
              primeMarginEnvelope b N T p * ∏ i : Fin 2, 1 / p i ∂μ) := by
  obtain ⟨C1, hC1, hpointwise⟩ := exists_smoothPrimeVariableProfile_inverse_width_budget
  refine ⟨C1, hC1, ?_⟩
  intro b N T width other a u ha μ hμ
  let B : Set (Fin 2 → ℝ) := Icc (fun _ => a) (fun _ => u)
  let H : (Fin 2 → ℝ) → ℝ := fun p => ∏ i : Fin 2, 1 / p i
  let D : ℝ := C1 * |width⁻¹ - other⁻¹|
  have hB : IsCompact B := isCompact_Icc
  have hpositive : B ⊆ positivePrimeOrthant := by
    intro p hp i
    exact ha.trans_le (hp.1 i)
  have hprofile (w : ℝ) : ContinuousOn (smoothPrimeVariableProfile b N T w) B :=
    (contDiffOn_smoothPrimeVariableProfile (n := 0) b N T w).continuousOn.mono hpositive
  have hH : ContinuousOn H B := continuousOn_primeHarmonic_positive.mono hpositive
  have hHnonneg : ∀ p ∈ B, 0 ≤ H p := by
    intro p hp
    exact Finset.prod_nonneg (fun i _hi => div_nonneg zero_le_one (hpositive hp i).le)
  have hleft : IntegrableOn (fun p =>
      |smoothPrimeVariableProfile b N T width p - smoothPrimeVariableProfile b N T other p| * H p)
      B μ :=
    (((hprofile width).sub (hprofile other)).abs.mul hH).integrableOn_of_subset_isCompact
      hB hB.measurableSet Subset.rfl hμ
  have hmoment : IntegrableOn (fun p => primeMarginEnvelope b N T p * H p) B μ :=
    integrableOn_primeMarginEnvelope_harmonic_box b N T a u ha μ hμ
  have hright : IntegrableOn (fun p => D * (primeMarginEnvelope b N T p * H p)) B μ :=
    hmoment.const_mul D
  refine ⟨hleft, ?_⟩
  calc
    _ ≤ ∫ p in B, D * (primeMarginEnvelope b N T p * H p) ∂μ := by
      apply integral_mono_ae hleft hright
      filter_upwards [ae_restrict_mem hB.measurableSet] with p hp
      have h := mul_le_mul_of_nonneg_right (hpointwise b N T width other p) (hHnonneg p hp)
      simpa only [D, mul_assoc] using h
    _ = D * ∫ p in B, primeMarginEnvelope b N T p * H p ∂μ :=
      integral_const_mul D (fun p => primeMarginEnvelope b N T p * H p)

end

end ImbalancedChen.P0VariableProfileWidthVariation