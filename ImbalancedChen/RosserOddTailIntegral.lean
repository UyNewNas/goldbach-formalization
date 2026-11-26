import ImbalancedChen.RosserOddTailRegion
import ImbalancedChen.FinitePiIntegral
import MathlibNt.SieveTheory.LinearSieve.BoundaryMass

/-!
# Strict tail-region integrals equal the recursive Rosser boundary mass

For a positive terminal coordinate, the actual finite-dimensional tail
density is integrable on its compact positive ambient box. Fubini removes
the first two coordinates, and the strict region recursion identifies the
result with the provider's exact open-interval pair recursion. The empty
tail has unit volume and retains the provider's nonnegative residual test.
The equality is proved for every residual level and inherited upper cutoff.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MeasureTheory Set
open MathlibNt.SieveTheory.LinearSieve

def rosserOddTailDensity (k : ℕ) (v : Fin (2 * k) → ℝ) : ℝ := ∏ i, 1 / v i

def rosserOddTailIntegral (k : ℕ) (s q b : ℝ) : ℝ :=
  ∫ v in rosserOddTailRegion k s q b, rosserOddTailDensity k v

theorem continuousOn_rosserOddTailDensity_Icc (k : ℕ) {q b : ℝ} (hq : 0 < q) :
    ContinuousOn (rosserOddTailDensity k) (Set.univ.pi (fun _ => Set.Icc q b)) := by
  apply continuousOn_finsetProd
  intro i _
  apply continuousOn_const.div (continuous_apply i).continuousOn
  intro v hv
  exact (hq.trans_le (Set.mem_pi.mp hv i (Set.mem_univ i)).1).ne'

theorem integrableOn_rosserOddTailDensity (k : ℕ) (s q b : ℝ) (hq : 0 < q) :
    IntegrableOn (rosserOddTailDensity k) (rosserOddTailRegion k s q b) :=
  ((continuousOn_rosserOddTailDensity_Icc k hq).integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
      (rosserOddTailRegion_subset_Icc k s q b)

theorem integrable_rosserOddTailIndicator (k : ℕ) (s q b : ℝ) (hq : 0 < q) :
    Integrable ((rosserOddTailRegion k s q b).indicator (rosserOddTailDensity k)) :=
  (integrableOn_rosserOddTailDensity k s q b hq).integrable_indicator
    (measurableSet_rosserOddTailRegion k s q b)

theorem rosserOddTailDensity_cons_cons (k : ℕ) (x₀ x₁ : ℝ) (v : Fin (2 * k) → ℝ) :
    rosserOddTailDensity (k + 1) (Fin.cons x₀ (Fin.cons x₁ v)) =
      x₀⁻¹ * (x₁⁻¹ * rosserOddTailDensity k v) := by
  simp [rosserOddTailDensity, Nat.mul_succ, Fin.prod_univ_succ, one_div,
    mul_comm]

/-- The zero-dimensional tail has unit volume; its inherited upper cutoff
does not impose an extra condition. -/
theorem rosserOddTailIntegral_zero (s q b : ℝ) :
    rosserOddTailIntegral 0 s q b = if 0 ≤ s ∧ s < 3 * q then 1 else 0 := by
  unfold rosserOddTailIntegral
  rw [← integral_indicator (measurableSet_rosserOddTailRegion 0 s q b), integral_fin_zero]
  simp only [Set.indicator_apply, mem_rosserOddTailRegion_zero]
  simp [rosserOddTailDensity]

/-- The actual set integral satisfies the same strict pair-removal
recursion as the provider's boundary mass. -/
theorem rosserOddTailIntegral_succ (k : ℕ) (s q b : ℝ) (hq : 0 < q) :
    rosserOddTailIntegral (k + 1) s q b =
      ∫ x₀ in Set.Ioo q (min b (s / 3)),
        x₀⁻¹ * ∫ x₁ in Set.Ioo q x₀,
          x₁⁻¹ * rosserOddTailIntegral k (s - x₀ - x₁) q x₁ := by
  have hi := integrable_rosserOddTailIndicator (k + 1) s q b hq
  calc
    rosserOddTailIntegral (k + 1) s q b =
        ∫ x₀ : ℝ, ∫ x₁ : ℝ, ∫ v : Fin (2 * k) → ℝ,
          (rosserOddTailRegion (k + 1) s q b).indicator
            (rosserOddTailDensity (k + 1)) (Fin.cons x₀ (Fin.cons x₁ v)) := by
      change (∫ v in rosserOddTailRegion (k + 1) s q b, rosserOddTailDensity (k + 1) v) = _
      rw [← integral_indicator (measurableSet_rosserOddTailRegion (k + 1) s q b)]
      exact integral_fin_pair _ hi
    _ = ∫ x₀ in Set.Ioo q (min b (s / 3)), ∫ x₁ in Set.Ioo q x₀,
          x₀⁻¹ * (x₁⁻¹ * rosserOddTailIntegral k (s - x₀ - x₁) q x₁) := by
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards [] with x₀
      by_cases hx₀ : x₀ ∈ Set.Ioo q (min b (s / 3))
      · rw [indicator_of_mem hx₀, ← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        filter_upwards [] with x₁
        by_cases hx₁ : x₁ ∈ Set.Ioo q x₀
        · rw [indicator_of_mem hx₁]
          change (∫ v : Fin (2 * k) → ℝ, _) =
            x₀⁻¹ * (x₁⁻¹ * ∫ v in rosserOddTailRegion k (s - x₀ - x₁) q x₁,
              rosserOddTailDensity k v)
          rw [← integral_indicator (measurableSet_rosserOddTailRegion k (s - x₀ - x₁) q x₁),
            ← integral_const_mul, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with v
          by_cases hv : v ∈ rosserOddTailRegion k (s - x₀ - x₁) q x₁
          · have hm : Fin.cons x₀ (Fin.cons x₁ v) ∈ rosserOddTailRegion (k + 1) s q b :=
              (mem_rosserOddTailRegion_cons_cons hq).mpr ⟨hx₁.1, hx₁.2, hx₀.2, hv⟩
            rw [indicator_of_mem hm, indicator_of_mem hv, rosserOddTailDensity_cons_cons]
          · have hm : Fin.cons x₀ (Fin.cons x₁ v) ∉ rosserOddTailRegion (k + 1) s q b := by
              intro hm
              exact hv ((mem_rosserOddTailRegion_cons_cons hq).mp hm).2.2.2
            rw [indicator_of_notMem hm, indicator_of_notMem hv]
            simp
        · rw [indicator_of_notMem hx₁]
          apply integral_eq_zero_of_ae
          filter_upwards [] with v
          have hm : Fin.cons x₀ (Fin.cons x₁ v) ∉ rosserOddTailRegion (k + 1) s q b := by
            intro hm
            have hm' := (mem_rosserOddTailRegion_cons_cons hq).mp hm
            exact hx₁ ⟨hm'.1, hm'.2.1⟩
          exact indicator_of_notMem hm _
      · rw [indicator_of_notMem hx₀]
        apply integral_eq_zero_of_ae
        filter_upwards [] with x₁
        apply integral_eq_zero_of_ae
        filter_upwards [] with v
        have hm : Fin.cons x₀ (Fin.cons x₁ v) ∉ rosserOddTailRegion (k + 1) s q b := by
          intro hm
          have hm' := (mem_rosserOddTailRegion_cons_cons hq).mp hm
          exact hx₀ ⟨hm'.1.trans hm'.2.1, hm'.2.2.1⟩
        exact indicator_of_notMem hm _
    _ = _ := by simp_rw [integral_const_mul]

/-- The recursive boundary mass is exactly the genuine tail-region
Lebesgue integral, with no assumed integral identity or convergence input. -/
theorem rosserOddTailIntegral_eq_boundaryMassAux (k : ℕ) (s q b : ℝ) (hq : 0 < q) :
    rosserOddTailIntegral k s q b = upperRosserBoundaryMassAux k s q b := by
  induction k generalizing s b with
  | zero => rw [rosserOddTailIntegral_zero, upperRosserBoundaryMassAux_zero]
  | succ k ih =>
      rw [rosserOddTailIntegral_succ k s q b hq, upperRosserBoundaryMassAux_succ]
      simp_rw [ih]

end

end ImbalancedChen
