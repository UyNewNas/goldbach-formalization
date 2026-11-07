import ImbalancedChen.P5U8LiteralPrimeFibreMass
import ImbalancedChen.CurrentChenUpsilon8SharpKArithmeticSource

/-!
SOURCE_ONLY / UNCOMPILED. Unconditional mass for the literal original U8
sharpK arithmetic source, without an additive-prime gate. The original q>=p2
cutoff and centre-coprime product remain in arithmeticTriples. They are
relaxed only for an upper bound by the complete prime prefix. All triple
labels, including q=p2, are counted. SharpK distribution remains open.
-/

namespace ImbalancedChen.P5U8SharpKSourceMassSourceOnly

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open P5U8SharpKSource
open P5U8LiteralPrimeFibreMassSourceOnly

theorem arithmeticTriples_card_le_primeCountMass (N : ℕ) :
    ((arithmeticTriples N).card : ℝ) ≤ primeCountMass N := by
  rw [arithmeticTriples_card_eq_sum]
  apply rowCards_le_primeCountMass N (quotientPrimeWindow N)
  intro t _ht q hq
  unfold quotientPrimeWindow at hq
  have hdata := (Finset.mem_filter.mp hq).2
  exact ⟨hdata.1, hdata.2.1⟩

/-- Original U8 source labels have the literal double-integral coefficient,
unconditionally at the N/logN scale, before any sharpK distribution supplier. -/
theorem eventually_arithmeticTriples_mass_le_harmonicIntegral
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      ((arithmeticTriples N).card : ℝ) ≤
        (currentChenUpsilon8HarmonicIntegral + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [eventually_primeCountMass_le_harmonicIntegral eta heta] with N hN
  exact (arithmeticTriples_card_le_primeCountMass N).trans hN

/-- The genuine uniform PNT also supplies the exact intermediate true-li
bound on the original source. This is not a sharpK AP estimate. -/
theorem eventually_arithmeticTriples_card_le_trueLiMass
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      ((arithmeticTriples N).card : ℝ) ≤ (1 + delta) * currentChenUpsilon8LiMainMass N := by
  filter_upwards [eventually_primeCountMass_le_trueLiMass delta hdelta] with N hN
  exact (arithmeticTriples_card_le_primeCountMass N).trans hN

/-- The identical unconditional supplier on the literal product-fibre
weight used by the sharpK PP bridge. Multiplicity is preserved exactly. -/
theorem eventually_productWeight_mass_le_harmonicIntegral
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      p5z_labelledMass (Finset.range N) (productWeight N) ≤
        (currentChenUpsilon8HarmonicIntegral + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [eventually_arithmeticTriples_mass_le_harmonicIntegral eta heta] with N hN
  rw [productWeight_mass_eq_card]
  exact hN

end

end ImbalancedChen.P5U8SharpKSourceMassSourceOnly
