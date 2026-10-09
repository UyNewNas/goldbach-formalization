/-
SPDX-License-Identifier: Apache-2.0

HELD SOURCE CANDIDATE: source review only; no Lean/Lake or kernel check.
This file consumes the independently held continuous-rectangle theorem.
It retains the literal centre-masked half-open Y5/Y6 prime selectors.
The only analytic hypothesis on the fixed scalar test f is continuity on
[1,5]. There is no actual pair-limit, uniform mass, distribution, or sieve
lower-bound hypothesis. These harmonic sums are not the sifted Upsilon counts.
-/
import ImbalancedChen.ChenVariablePairKernel
import ImbalancedChen.ChenContinuousRectangleTransport

namespace ImbalancedChen.ChenVariablePairHarmonicLimit

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open ChenVariablePairKernel ChenContinuousRectangleTransport

def logCoordinate (N p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log (N : ℝ)

/-- The fifth literal totient main sum, with its symmetric extension K. -/
def y5HarmonicSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h),
    kernel f (logCoordinate N t.1) (logCoordinate N t.2) /
      (Nat.totient (t.1 * t.2) : ℝ)

/-- The full sixth literal totient main sum; its second band ends at N^d. -/
def y6HarmonicSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h) ((N : ℝ) ^ d),
    kernel f (logCoordinate N t.1) (logCoordinate N t.2) /
      (Nat.totient (t.1 * t.2) : ℝ)

/-- The same fifth numerator in the manuscript's larger-coordinate notation. -/
def orderedY5HarmonicSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h),
    f ((vLevel (logCoordinate N t.2) - logCoordinate N t.2 -
      logCoordinate N t.1) / a) / (Nat.totient (t.1 * t.2) : ℝ)

def orderedY6HarmonicSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h) ((N : ℝ) ^ d),
    f ((vLevel (logCoordinate N t.2) - logCoordinate N t.2 -
      logCoordinate N t.1) / a) / (Nat.totient (t.1 * t.2) : ℝ)

private theorem logCoordinate_mono {N p q : ℕ}
    (hN : 2 ≤ N) (hp : 0 < p) (hpq : p ≤ q) :
    logCoordinate N p ≤ logCoordinate N q := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpqR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  exact div_le_div_of_nonneg_right (Real.log_le_log hpR hpqR)
    (Real.log_nonneg hN1)

/-- Ordering is established on the actual finite fifth selector before
replacing max by the larger logarithmic coordinate. -/
theorem y5HarmonicSum_eq_ordered (f : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    y5HarmonicSum f N = orderedY5HarmonicSum f N := by
  unfold y5HarmonicSum orderedY5HarmonicSum
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_filter.mp ht
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp ht'.1).1).2.1
  rw [kernel_of_le f (logCoordinate_mono hN hp.pos ht'.2.2.1.le)]

/-- The full sixth bands force p<q. No argument-below-2 strip is removed. -/
theorem y6HarmonicSum_eq_ordered (f : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    y6HarmonicSum f N = orderedY6HarmonicSum f N := by
  unfold y6HarmonicSum orderedY6HarmonicSum
  apply Finset.sum_congr rfl
  intro t ht
  rw [chenY6PrimeSelector_eq_single_product] at ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp ht
  have hpprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
  rw [kernel_of_le f
    (logCoordinate_mono hN hpprime.pos (chenY6_single_product_lt hp hq).le)]

/-- A genuine fixed-variable-kernel Y5 limit. The imported theorem proves
the artificial prime diagonal tends to zero; it is not an extra assumption. -/
theorem tendsto_y5HarmonicSum {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (y5HarmonicSum f) atTop
      (𝓝 ((1 / 2 : ℝ) * (∫ u in a..h, ∫ v in a..h, weightedKernel f u v))) :=
  tendsto_chenY5_kernel_totient_sum a_pos a_lt_h h_le_one
    (continuousOn_kernel_R5 hf) (fun u _ v _ => kernel_symm f u v)

/-- A genuine fixed-variable-kernel Y6 limit on the entire mixed rectangle. -/
theorem tendsto_y6HarmonicSum {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (y6HarmonicSum f) atTop
      (𝓝 (∫ u in a..h, ∫ v in h..d, weightedKernel f u v)) :=
  tendsto_chenY6_kernel_totient_sum a_pos a_lt_h h_lt_d d_le_one
    (continuousOn_kernel_R6 hf)

/-- The fifth limit also holds for the literal manuscript numerator. -/
theorem tendsto_orderedY5HarmonicSum {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (orderedY5HarmonicSum f) atTop
      (𝓝 ((1 / 2 : ℝ) * (∫ u in a..h, ∫ v in a..h, weightedKernel f u v))) := by
  apply (tendsto_y5HarmonicSum hf).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact y5HarmonicSum_eq_ordered f hN

theorem tendsto_orderedY6HarmonicSum {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (orderedY6HarmonicSum f) atTop
      (𝓝 (∫ u in a..h, ∫ v in h..d, weightedKernel f u v)) := by
  apply (tendsto_y6HarmonicSum hf).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact y6HarmonicSum_eq_ordered f hN

end
end ImbalancedChen.ChenVariablePairHarmonicLimit
