import ImbalancedChen.P5U7OriginalBoundaryElimination
import ImbalancedChen.P5U7OriginalFullIntegralDictionary

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Leading-one upper mean of the literal original marked U7 prime/semiprime
source. All analytic ingredients are proved in imported source modules:
actual PNT prime-box transport, denominator correction, finite rough-band
estimate, arithmetic thin-boundary payment, and the genuine Omega Fubini
dictionary. No source mean or desired integral inequality is a premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

theorem tendsto_p5U7MassBuchstabMain_normalized_original :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      p5U7MassBuchstabMain N) atTop (𝓝 (p5U7OriginalOmegaIntegral 1)) := by
  simpa only [p5U7InteriorOmegaIntegral_zero_eq_original] using
    tendsto_p5U7MassBuchstabMain_normalized

theorem p5U7Original_eventually_BuchstabMain_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      p5U7MassBuchstabMain N ≤ (p5U7OriginalOmegaIntegral 1 + epsilon) *
        ((N : ℝ) / Real.log (N : ℝ)) := by
  have hnorm := tendsto_p5U7MassBuchstabMain_normalized_original.eventually
    (gt_mem_nhds (show p5U7OriginalOmegaIntegral 1 <
      p5U7OriginalOmegaIntegral 1 + epsilon by linarith))
  filter_upwards [hnorm, eventually_ge_atTop (2 : ℕ)] with N hmain hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  calc
    p5U7MassBuchstabMain N =
        ((Real.log (N : ℝ) / (N : ℝ)) * p5U7MassBuchstabMain N) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
            field_simp [hNp.ne', hlog.ne']
    _ ≤ (p5U7OriginalOmegaIntegral 1 + epsilon) *
        ((N : ℝ) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hmain.le (by positivity)

/-- Original leading-one source mean, with arbitrary positive absolute
error. The fixed original cutoff d=59/250 and every repeated terminal
label remain in the finite source cardinalities. -/
theorem p5U7Original_eventually_arithmetic_mass_le_integral
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      ((p5U7ArithmeticThree N).card : ℝ) +
        ((p5U7ArithmeticFour N).card : ℝ) ≤
      (p5U7OriginalOmegaIntegral 1 + epsilon) *
        ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [p5U7Original_eventually_arithmetic_mass_le_main
      (epsilon / 2) (by positivity),
    p5U7Original_eventually_BuchstabMain_le (epsilon / 2) (by positivity)]
    with N hsource hmain
  linarith only [hsource, hmain]

/-- Same original mean on the literal weighted physical products. The
finite product-fibre identity preserves all marked-pair multiplicities. -/
theorem p5U7Original_eventually_product_weight_mass_le_integral
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m) ≤
      (p5U7OriginalOmegaIntegral 1 + epsilon) *
        ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [p5U7Original_eventually_arithmetic_mass_le_integral epsilon hepsilon]
    with N hN
  rw [p5U7Arithmetic_product_weight_mass]
  exact hN

end

end ImbalancedChen
