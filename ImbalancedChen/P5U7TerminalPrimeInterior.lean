import ImbalancedChen.P5U7TerminalPrimeUniform
import ImbalancedChen.P5U7OriginalInteriorCompatibility

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The old actual multiplicative gate supplies the terminal lower-wall decay.
One threshold precedes every marked pair. Both weak and strict selectors
remain actual finite arithmetic selectors; their walls are not deleted.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology LiLiuPrereqBuchstab
open scoped BigOperators

/-- The existing original row-boundary theorem gives the exact wall
required by the uniform terminal-prime PNT, with no new geometric premise. -/
theorem p5U7TerminalPrime_interior_wall {N : ℕ} (hN : 0 < N)
    {eta : ℝ} (heta : 0 ≤ eta) {t : ℕ × ℕ} (ht : t ∈ p5U7InteriorPairs N eta) :
    (t.2 : ℝ) ≤ ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) *
      (N : ℝ) ^ (-((59 / 250 : ℝ) * eta)) := by
  have hto := (Finset.mem_filter.mp ht).1
  have hc := (Finset.mem_filter.mp hto).1
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hl : 0 < Real.log (t.2 : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hh := p5U7Interior_boundary_row_le hN heta ht
  have hh' : (t.2 : ℝ) / Real.log (t.2 : ℝ) ≤
      (((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) *
        (N : ℝ) ^ (-((59 / 250 : ℝ) * eta))) / Real.log (t.2 : ℝ) := by
    rw [show -((59 / 250 : ℝ) * eta) = -(59 / 250 : ℝ) * eta by ring]
    exact hh.trans_eq (by ring)
  exact (div_le_div_iff_of_pos_right hl).mp hh'

/-- Actual terminal mass on every original marked pair of one fixed
positive eta band, with the quantifiers in their required uniform order. -/
theorem p5U7TerminalPrime_eventually_all_interior_pairs (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ p5U7InteriorPairs N eta,
      |((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ) -
        ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
          Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ))| ≤
      epsilon * (((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
        Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ))) := by
  filter_upwards [p5U7TerminalPrime_eventually_uniform_abs eta epsilon heta hepsilon,
    eventually_ge_atTop (2 : ℕ)] with N hN htwo
  intro t ht
  have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
  exact hN _ _ hg.1 (hg.2.1.trans hg.2.2.1.le)
    (p5U7TerminalPrime_interior_wall (by omega) heta.le ht)

/-- The same single threshold controls any finite subfamily of the
actual marked band, including the actual strict double-prime selector. -/
theorem p5U7TerminalPrime_eventually_subfamily_error (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ T : Finset (ℕ × ℕ), T ⊆ p5U7InteriorPairs N eta →
      |(∑ t ∈ T, ((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ)) -
        (∑ t ∈ T, ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
          Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)))| ≤
      epsilon * (∑ t ∈ T, ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
        Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ))) := by
  filter_upwards [p5U7TerminalPrime_eventually_all_interior_pairs eta epsilon heta hepsilon] with N hN
  intro T hT
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun t ht => hN t (hT ht)))

/-- Signed leading-one lower transport on the literal strict selector. -/
theorem p5U7TerminalPrime_eventually_strict_sum_lower (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      (1 - epsilon) * (∑ t ∈ p5U7InteriorSelector N eta,
        ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
          Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ))) ≤
      ∑ t ∈ p5U7InteriorSelector N eta,
        ((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ) := by
  filter_upwards [p5U7TerminalPrime_eventually_subfamily_error eta epsilon heta hepsilon,
    eventually_ge_atTop (2 : ℕ)] with N hN htwo
  have hh := (abs_le.mp (hN _ (p5U7InteriorSelector_subset_band htwo eta))).1
  nlinarith only [hh]
end
end ImbalancedChen

