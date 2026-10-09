import ImbalancedChen.ChenQuotientMovingWeight
import ImbalancedChen.ChenPrimeHarmonicAdapter

/-!
# Actual single-prime moving-factor limit

This separate consumer uses the genuine fixed-continuous-test harmonic
theorem in `ChenPrimeHarmonicAdapter`, which depends on the approved
ordinary270 Mertens supplier. Its endpoint, denominator, and centre-mask
corrections are reused unchanged. No foreign source is copied or edited.

The constant test proves bounded total harmonic mass; the affine-composed
test supplies the fixed-profile limit. The actual moving quotient-row
factor then has the displayed integral limit without either of those
analytic facts remaining as a premise.

This is a single-prime main-factor limit, not a sieve estimate or a
prime-pair theorem. The continuous test may have either sign.

Held source candidate: no compilation, kernel replay, or axiom audit yet.
-/

namespace ImbalancedChen.ChenQuotientMovingPrimeAdapter

noncomputable section
open Filter Topology
open scoped BigOperators

/-- The actual masked, half-open single-prime harmonic mass is bounded,
by applying the proved fixed-test harmonic limit to the constant one. -/
theorem exists_eventually_bounded_chenSinglePrimeTotientMass
    {l c : ℝ} (hl : 0 < l) (hlc : l < c) (hc : c ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ l) ((N : ℝ) ^ c),
        (Nat.totient p : ℝ)⁻¹) ≤ M := by
  have hmass : Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ l) ((N : ℝ) ^ c),
        (Nat.totient p : ℝ)⁻¹)
      atTop (𝓝 (∫ u in l..c, (1 : ℝ) / u)) := by
    simpa only [one_div] using
      ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeTotientLogSum
        hl hlc hc (f := fun _ : ℝ => (1 : ℝ)) continuousOn_const
  exact exists_eventually_bounded_mass_of_tendsto hmass

/-- The literal single-prime selector, genuine totient weight, actual
natural quotient-row level, and fixed padded continuity interval all
appear in the statement. No distribution, bounded-mass, or fixed-profile
limit premise remains. The integral itself is not numerically evaluated. -/
theorem tendsto_chenSinglePrime_moving_sieveFactor
    (B l c a rho : ℝ) (F : ℝ → ℝ)
    (hl : 0 < l) (hlc : l < c) (hc : c < 1 / 2)
    (ha : 0 < a) (hrho : 0 < rho)
    (hF : ContinuousOn F
      (Set.Icc (((1 / 2 : ℝ) - c) / a - rho) ((1 / 2 : ℝ) / a + rho))) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ l) ((N : ℝ) ^ c),
        F (chenQuotientRosserT B a N p) / (Nat.totient p : ℝ))
      atTop (𝓝 (∫ u in l..c, F (((1 / 2 : ℝ) - u) / a) / u)) := by
  let T : ℕ → Finset ℕ := fun N =>
    chenSinglePrimeSelector N ((N : ℝ) ^ l) ((N : ℝ) ^ c)
  have hc1 : c ≤ 1 := by linarith
  have hcomp : ContinuousOn (fun u : ℝ => F (((1 / 2 : ℝ) - u) / a))
      (Set.Icc l c) := by
    apply hF.comp ((continuousOn_const.sub continuousOn_id).div_const a)
    intro u hu
    have hu0 : 0 ≤ u := hl.le.trans hu.1
    have hlo : ((1 / 2 : ℝ) - c) / a ≤ ((1 / 2 : ℝ) - u) / a :=
      div_le_div_of_nonneg_right (by linarith [hu.2]) ha.le
    have hhi : ((1 / 2 : ℝ) - u) / a ≤ (1 / 2 : ℝ) / a :=
      div_le_div_of_nonneg_right (by linarith) ha.le
    exact ⟨by linarith, by linarith⟩
  obtain ⟨M, hM, hmass⟩ :=
    exists_eventually_bounded_chenSinglePrimeTotientMass hl hlc hc1
  have hb : ∀ᶠ N : ℕ in atTop, ∀ p ∈ T N,
      0 < p ∧ (p : ℝ) ≤ (N : ℝ) ^ c := by
    apply Filter.Eventually.of_forall
    intro N p hp
    have hdata := Finset.mem_filter.mp hp
    exact ⟨(mem_chenAdditivePrimeCarrier.mp hdata.1).2.1.pos, hdata.2.2.le⟩
  have hw : ∀ᶠ N : ℕ in atTop, ∀ p ∈ T N, 0 ≤ (Nat.totient p : ℝ)⁻¹ := by
    apply Filter.Eventually.of_forall
    intro N p _
    positivity
  have hfixed : Tendsto (fun N : ℕ =>
      ∑ p ∈ T N, (Nat.totient p : ℝ)⁻¹ *
        F (((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) / a))
      atTop (𝓝 (∫ u in l..c, F (((1 / 2 : ℝ) - u) / a) / u)) := by
    simpa only [T, div_eq_mul_inv, mul_comm] using
      ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeTotientLogSum hl hlc hc1 hcomp
  have hresult := tendsto_chenQuotientRosserT_weighted_of_profile T
    (fun _ p => p) (fun _ p => (Nat.totient p : ℝ)⁻¹) B c a rho M
    (∫ u in l..c, F (((1 / 2 : ℝ) - u) / a) / u) F
    hc ha hrho hM hF hb hw hmass hfixed
  simpa only [T, div_eq_mul_inv, mul_comm] using hresult

end

end ImbalancedChen.ChenQuotientMovingPrimeAdapter
