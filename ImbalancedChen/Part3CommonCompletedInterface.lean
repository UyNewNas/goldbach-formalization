import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.Part3ExceptionalWeightExtension

/-!
# Common interval and phase for the original transformed packet

The interval and phase belong to one completed variable shared by the entire
finite spectral sum. The full-block energy bound is an explicit input on the
same coefficients for every common phase.
-/

namespace ImbalancedChen.Part3.CommonCompletedInterface

noncomputable section

open scoped BigOperators
open ActualIntervalGeometricSumSourceOnly CommonIntervalFourier ExceptionalWeightExtension

/-- Multiplying by the original weight clips any finite carrier to its common
half-open interval and leaves the original phase on the intersection. -/
theorem sum_weight_mul_eq_sum_inter (c : CommonCompletedVariable) (S : Finset ℕ)
    (b : ℕ → ℂ) :
    (∑ m ∈ S, c.weight m * b m) =
      ∑ m ∈ S ∩ Finset.Ico c.intervalLo c.intervalHi, phaseAt c.additivePhase m * b m := by
  classical
  have hcarrier : S ∩ Finset.Ico c.intervalLo c.intervalHi =
      S.filter (fun m => m ∈ Finset.Ico c.intervalLo c.intervalHi) := by
    ext m
    simp only [Finset.mem_inter, Finset.mem_filter]
  rw [hcarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m ∈ Finset.Ico c.intervalLo c.intervalHi <;>
    simp [CommonCompletedVariable.weight, phaseAt, hm]

/-- Apply the common-interval bound to the literal weight on a full dyadic
block. The full-block hypothesis controls the same array at every phase. -/
theorem weight_weightedEnergy_le {ι : Type*} [Fintype ι]
    (c : CommonCompletedVariable) (j : ℕ) (bound : ℝ) {W T cap : ℝ}
    (hW : 0 < W) (hT : 0 < T) (exponent : ι → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ, weightedEnergy (fullBlock j) ρ T exponent a ≤ bound) :
    (∑ i, W ^ exponent i * ‖∑ m ∈ fullBlock j, c.weight m * a i m‖ ^ 2) ≤
      4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound) := by
  simp_rw [sum_weight_mul_eq_sum_inter]
  by_cases h : c.intervalLo ≤ c.intervalHi
  · exact commonIco_weightedEnergy_le h j c.additivePhase bound hW hT
      exponent hexponent hcap a full_uniform
  · have hempty : Finset.Ico c.intervalLo c.intervalHi = ∅ :=
      Finset.Ico_eq_empty_of_le (le_of_not_ge h)
    have hbound : 0 ≤ bound :=
      (weightedEnergy_nonneg (fullBlock j) 0 hT.le exponent a).trans (full_uniform 0)
    have hmax : 0 ≤ max 1 ((W / T) ^ cap) := zero_le_one.trans (le_max_left _ _)
    have hrhs : 0 ≤ 4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (sq_nonneg _) hmax) hbound)
    simpa [hempty] using hrhs

/-- Each spectral index projects to its packet label. The carrier and the
original coprime transformed coefficient depend only on that label, while
the kernel can depend on the full spectral index and both integer variables. -/
theorem packet_weightedEnergy_le {ι κ : Type*} [Fintype ι]
    (c : CommonCompletedVariable) (j : ℕ) (bound : ℝ) {W T cap : ℝ}
    (hW : 0 < W) (hT : 0 < T) (exponent : ι → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (label : ι → κ) (packet : κ → CoprimePacket) (carrier : κ → Finset ℕ)
    (kernel : ι → ℕ → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ, weightedEnergy (fullBlock j) ρ T exponent
      (fun i m => ∑ n ∈ carrier (label i),
        (packet (label i)).transformedCoefficient n * kernel i m n) ≤ bound) :
    (∑ i, W ^ exponent i * ‖∑ m ∈ fullBlock j, c.weight m *
      (∑ n ∈ carrier (label i),
        (packet (label i)).transformedCoefficient n * kernel i m n)‖ ^ 2) ≤
      4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound) := by
  exact weight_weightedEnergy_le c j bound hW hT exponent hexponent hcap
    (fun i m => ∑ n ∈ carrier (label i),
      (packet (label i)).transformedCoefficient n * kernel i m n) full_uniform

end

end ImbalancedChen.Part3.CommonCompletedInterface
