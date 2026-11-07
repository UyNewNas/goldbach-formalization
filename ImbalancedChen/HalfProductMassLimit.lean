import ImbalancedChen.HalfProductMassError
import ImbalancedChen.MassLogIntegral
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Actual half-product mass, conditional on the two upstream analytic inputs

This module proves the mass limit for the original `halfProductSource`, at
its literal `logCutoff N`. The two explicit analytic inputs are the real-PNT
error-witness contract used in `UniformPrimeTail`, and the weighted-prime
Mertens limit for the fixed test `u ↦ 1 / (1 - u)` on the exact high-prime
window. Neither upstream theorem is imported or proved here.

The Mertens premise is a literal finite sum of reciprocal prime weights;
it contains no half-product cardinality or prime-prefix count. The proof
uses the uniform PNT simultaneously at all arguments `N / r ≥ sqrt N`,
proves the natural-division/floor equality, and sums errors with positive
weights. It then uses the proved negligible error for the actual cutoff
source. Squares and the strict lower endpoint are preserved throughout.

The coefficient is `log (1 / b)`, where `b = num / den`. The analytic
argument works for every fixed `0 < num < den`, without a parity condition.
-/

namespace ImbalancedChen

noncomputable section

open Filter Asymptotics Topology
open scoped BigOperators

/-- The literal fixed-test sum supplied by the upstream weighted-prime
Mertens theorem after specialization and the proved integral evaluation.
The lower endpoint is strict and the square-root endpoint is inclusive. -/
def halfProductMassWeightedPrimeSum (num den N : ℕ) : ℝ :=
  ∑ r ∈ halfProductHighPrimes N
      (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
    (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)

/-- Exact natural floor at the real division endpoint. No integer rounding
error needs to be estimated when applying the real-endpoint PNT. -/
theorem halfProduct_nat_floor_div {N r : ℕ} (hr : 0 < r) :
    Nat.floor ((N : ℝ) / (r : ℝ)) = N / r := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  apply Nat.le_antisymm
  · apply (Nat.le_div_iff_mul_le hr).mpr
    have hfloor := Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hrR.le)
    have hmul : (Nat.floor ((N : ℝ) / (r : ℝ)) : ℝ) * (r : ℝ) ≤ N :=
      (le_div_iff₀ hrR).mp hfloor
    exact_mod_cast hmul
  · apply Nat.le_floor
    apply (le_div_iff₀ hrR).mpr
    exact_mod_cast Nat.div_mul_le_self N r

/-- Every prime in the original high window is positive and below `N`, and
its real division endpoint lies in the single uniform square-root tail. -/
theorem halfProductHighPrimes_real_endpoint {N A r : ℕ}
    (hr : r ∈ halfProductHighPrimes N A) :
    0 < (r : ℝ) ∧ (r : ℝ) < N ∧
      Real.sqrt (N : ℝ) ≤ (N : ℝ) / (r : ℝ) := by
  classical
  obtain ⟨hrS, _⟩ := Finset.mem_filter.mp hr
  obtain ⟨hrsqrt, hrprime⟩ := Nat.mem_primesLE.mp hrS
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hrprime.pos
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hrprime.two_le
  have hrr : (r : ℝ) * (r : ℝ) ≤ N := by
    exact_mod_cast Nat.le_sqrt.mp hrsqrt
  have hrN : (r : ℝ) < N := by
    nlinarith [mul_le_mul_of_nonneg_left hr2 hrpos.le]
  have hrroot : (r : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  refine ⟨hrpos, hrN, (le_div_iff₀ hrpos).mpr ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hrroot (Real.sqrt_nonneg (N : ℝ))
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Exact identity converting each normalized real PNT main term to the
fixed Mertens test. All divisions have positive denominators in this range. -/
theorem halfProduct_normalized_prime_mainTerm {N r : ℕ}
    (hN : 2 ≤ N) (hr : 0 < (r : ℝ)) (hrN : (r : ℝ) < N) :
    (((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ))) /
        ((N : ℝ) / Real.log (N : ℝ)) =
      (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlogdiv : 0 < Real.log ((N : ℝ) / (r : ℝ)) :=
    Real.log_pos ((one_lt_div hr).mpr hrN)
  rw [← massLogKernel_identity hN1 hr hrN]
  field_simp [ne_of_gt hNpos, ne_of_gt hr, ne_of_gt hlog, ne_of_gt hlogdiv] <;> ring

/-- Every weight in the literal high-prime window is strictly positive.
This is the same fixed test as in the upstream Mertens input. -/
theorem halfProductHighPrimes_mass_weight_pos {N A r : ℕ}
    (hN : 2 ≤ N) (hr : r ∈ halfProductHighPrimes N A) :
    0 < (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ) := by
  obtain ⟨hrpos, hrN, _⟩ := halfProductHighPrimes_real_endpoint hr
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlogdiv : 0 < Real.log ((N : ℝ) / (r : ℝ)) :=
    Real.log_pos ((one_lt_div hrpos).mpr hrN)
  rw [← halfProduct_normalized_prime_mainTerm hN hrpos hrN]
  exact div_pos (div_pos (div_pos hNpos hrpos) hlogdiv) (div_pos hNpos hlog)

/-- The normalized literal prefix sum has relative error at most epsilon
times the positive fixed-test prime sum, simultaneously over the full
moving window. The only analytic input here is the explicit real PNT. -/
theorem eventually_halfProductMassApprox_weighted_error_of_real_pnt
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    (num den : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |(halfProductMassApprox num den N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) - halfProductMassWeightedPrimeSum num den N| ≤
        epsilon * halfProductMassWeightedPrimeSum num den N := by
  classical
  filter_upwards
    [eventually_primeCounting_uniform_sqrt_tail_of_real_pnt hPNT epsilon hepsilon,
      eventually_ge_atTop (2 : ℕ)] with N htail hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have hterm : ∀ r ∈ halfProductHighPrimes N
      (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
      |(Nat.primeCounting (N / r) : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
          (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)| ≤
        epsilon * ((1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)) := by
    intro r hr
    obtain ⟨hrpos, hrN, htailr⟩ := halfProductHighPrimes_real_endpoint hr
    have happrox := (htail ((N : ℝ) / (r : ℝ)) htailr).2.2
    rw [halfProduct_nat_floor_div (Nat.cast_pos.mp hrpos)] at happrox
    have hid := halfProduct_normalized_prime_mainTerm hN hrpos hrN
    calc
      |(Nat.primeCounting (N / r) : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
          (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)| =
          |(Nat.primeCounting (N / r) : ℝ) -
            ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ))| /
              ((N : ℝ) / Real.log (N : ℝ)) := by
        rw [← hid, ← sub_div, abs_div, abs_of_pos hscale]
      _ ≤ (epsilon * (((N : ℝ) / (r : ℝ)) /
          Real.log ((N : ℝ) / (r : ℝ)))) / ((N : ℝ) / Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right happrox hscale.le
      _ = epsilon * ((1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)) := by
        rw [mul_div_assoc, hid]
  rw [halfProductMassApprox, halfProductPrimePrefixMass, Nat.cast_sum,
    Finset.sum_div, halfProductMassWeightedPrimeSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ halfProductHighPrimes N
        (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
        |(Nat.primeCounting (N / r) : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
          (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ halfProductHighPrimes N
        (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
        epsilon * ((1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The upstream Mertens input is precisely the literal prime-weight sum
shown here. The prefix-count limit is a conclusion, not an analytic premise. -/
theorem tendsto_halfProductMassApprox_of_real_pnt_and_weighted_mertens
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    (num den : ℕ)
    (hMertens : Tendsto (fun N : ℕ =>
      ∑ r ∈ halfProductHighPrimes N
          (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
        (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ)))))) :
    Tendsto (fun N : ℕ => (halfProductMassApprox num den N : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ))))) := by
  let L : ℝ := Real.log (1 / ((num : ℝ) / (den : ℝ)))
  have hw : Tendsto (halfProductMassWeightedPrimeSum num den) atTop (𝓝 L) := hMertens
  have hC : 0 < |L| + 1 := by positivity
  have hbounded : ∀ᶠ N : ℕ in atTop,
      halfProductMassWeightedPrimeSum num den N < |L| + 1 :=
    hw.eventually (gt_mem_nhds (lt_of_le_of_lt (le_abs_self L) (lt_add_one _)))
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hsmall : 0 < (epsilon / 2) / (|L| + 1) :=
    div_pos (half_pos hepsilon) hC
  have hnear := (Metric.tendsto_nhds.mp hw) (epsilon / 2) (half_pos hepsilon)
  filter_upwards
    [eventually_halfProductMassApprox_weighted_error_of_real_pnt hPNT num den
      ((epsilon / 2) / (|L| + 1)) hsmall, hbounded, hnear]
    with N herr hbound hnearN
  rw [Real.dist_eq] at hnearN ⊢
  have herrsmall : |(halfProductMassApprox num den N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - halfProductMassWeightedPrimeSum num den N| <
      epsilon / 2 := by
    calc
      _ ≤ ((epsilon / 2) / (|L| + 1)) * halfProductMassWeightedPrimeSum num den N := herr
      _ < ((epsilon / 2) / (|L| + 1)) * (|L| + 1) :=
        mul_lt_mul_of_pos_left hbound hsmall
      _ = epsilon / 2 := div_mul_cancel₀ _ (ne_of_gt hC)
  have htriangle := abs_add_le
    ((halfProductMassApprox num den N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
      halfProductMassWeightedPrimeSum num den N)
    (halfProductMassWeightedPrimeSum num den N - L)
  dsimp [L] at htriangle hnearN
  have heq : (halfProductMassApprox num den N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - halfProductMassWeightedPrimeSum num den N +
        (halfProductMassWeightedPrimeSum num den N -
          Real.log (1 / ((num : ℝ) / (den : ℝ)))) =
      (halfProductMassApprox num den N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
        Real.log (1 / ((num : ℝ) / (den : ℝ))) := by ring
  rw [heq] at htriangle
  linarith

/-- Conditional MASS for the original finite source at the literal cutoff
`N / (log N)^10`. Only real PNT and the displayed fixed-test weighted-prime
Mertens limit are unproved upstream inputs. There is no target-mass premise. -/
theorem tendsto_halfProductSource_logCutoff_mass_of_real_pnt_and_weighted_mertens
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {num den : ℕ} (hnum : 0 < num) (hnumden : num < den)
    (hMertens : Tendsto (fun N : ℕ =>
      ∑ r ∈ halfProductHighPrimes N
          (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
        (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ)))))) :
    Tendsto (fun N : ℕ =>
      ((halfProductSource num den N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ))))) := by
  have hprefix := tendsto_halfProductMassApprox_of_real_pnt_and_weighted_mertens
    hPNT num den hMertens
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hnear := (Metric.tendsto_nhds.mp hprefix) (epsilon / 2) (half_pos hepsilon)
  filter_upwards
    [eventually_halfProductSource_massApprox_error_of_real_pnt hPNT hnum hnumden
      (epsilon / 2) (half_pos hepsilon), hnear, eventually_ge_atTop (2 : ℕ)]
    with N herr hnearN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have herrsmall : |((halfProductSource num den N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - (halfProductMassApprox num den N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ))| ≤ epsilon / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hscale]
    exact (div_le_iff₀ hscale).mpr herr
  rw [Real.dist_eq] at hnearN ⊢
  have htriangle := abs_add_le
    (((halfProductSource num den N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - (halfProductMassApprox num den N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)))
    ((halfProductMassApprox num den N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
      Real.log (1 / ((num : ℝ) / (den : ℝ))))
  have heq : ((halfProductSource num den N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - (halfProductMassApprox num den N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) +
        ((halfProductMassApprox num den N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
          Real.log (1 / ((num : ℝ) / (den : ℝ)))) =
      ((halfProductSource num den N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / ((num : ℝ) / (den : ℝ))) := by ring
  rw [heq] at htriangle
  linarith

end

end ImbalancedChen
