import ImbalancedChen.RealHalfProductMassSplit
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# Audited analytic suppliers for the arbitrary-real half-product mass

This module connects the repository-local PNT and weighted-prime Mertens
interfaces to the corresponding theorems in the pinned `goldbach-lean`
dependency.  The interval adapter is an exact equality: the supplier's
`rpowFloor` is the same natural floor of a real power used locally.

The resulting source-mass theorems no longer take PNT or Mertens conclusions
as premises.  They still concern the ordered half-product source before the
positive upper-sieve transfer, so they do not by themselves prove the final
bad-representation estimate or Theorem 1.1.
-/

namespace ImbalancedChen

noncomputable section

open Filter MeasureTheory Topology

/-- The local strict-left, inclusive-right reciprocal-prime interval is
definitionally the interval used by the pinned Mertens supplier. -/
theorem realPrimeReciprocalLogIntervalSum_eq_weightedPrimeReciprocalLogSum
    (f : ℝ → ℝ) (N : ℕ) (a c : ℝ) :
    realPrimeReciprocalLogIntervalSum f N a c =
      MathlibNt.SieveTheory.MertensTheorem.weightedPrimeReciprocalLogSum
        f N a c := by
  rfl

/-- The pinned prime-number theorem supplies exactly the real-variable
witness used by the finite half-product approximation. -/
theorem realHalfProduct_primeCounting_asymptotic_real :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x := by
  simpa using
    AnalyticNumberTheory.PrimeDistribution.primeCounting_asymptotic_real

/-- The manuscript kernel has no pole on its actual high-prime exponent
window, whose upper endpoint is `1/2`. -/
theorem realHalfProductMass_kernel_continuousOn {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) :
    ContinuousOn (fun u : ℝ => 1 / (1 - u))
      (Set.Icc (realHalfProductMassAlpha b) (1 / 2)) := by
  exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
    (fun u hu => by linarith [hu.2])

/-- The pinned weighted-prime Mertens theorem, specialized to the exact
arbitrary-real half-product window and expressed in the local spelling. -/
theorem tendsto_realPrimeReciprocalLogIntervalSum_halfProduct
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun N : ℕ =>
      realPrimeReciprocalLogIntervalSum (fun u => 1 / (1 - u)) N
        (realHalfProductMassAlpha b) (1 / 2)) atTop
      (nhds (∫ u in realHalfProductMassAlpha b..(1 / 2 : ℝ),
        (1 / (1 - u)) / u)) := by
  have hexp := realHalfProductMass_exponents hb hb1
  have h :=
    MathlibNt.SieveTheory.MertensTheorem.tendsto_weightedPrimeReciprocalLogSum
      hexp.1 hexp.2.1 (realHalfProductMass_kernel_continuousOn hb hb1)
  simpa only [realPrimeReciprocalLogIntervalSum_eq_weightedPrimeReciprocalLogSum]
    using h

/-- Unconditional arbitrary-real prefix-mass limit obtained from the pinned
PNT and weighted Mertens suppliers. -/
theorem tendsto_realHalfProductMassApprox_of_suppliers
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun N : ℕ => (realHalfProductMassApprox b N : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ)))
      atTop (nhds (Real.log (1 / b))) :=
  tendsto_realHalfProductMassApprox_of_real_pnt_and_weighted_mertens
    realHalfProduct_primeCounting_asymptotic_real hb hb1
    (tendsto_realPrimeReciprocalLogIntervalSum_halfProduct hb hb1)

/-- Unconditional mass limit at the historical logarithmic cutoff. -/
theorem tendsto_realHalfProductSource_logCutoff_mass_of_suppliers
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
      atTop (nhds (Real.log (1 / b))) :=
  tendsto_realHalfProductSource_logCutoff_mass_of_real_pnt_and_weighted_mertens
    realHalfProduct_primeCounting_asymptotic_real hb hb1
    (tendsto_realPrimeReciprocalLogIntervalSum_halfProduct hb hb1)

/-- Unconditional ordered half-product source mass at the literal cutoff used
by the current manuscript.  Strict badness, ordering and prime squares are
those of `realHalfProductSource`; this theorem introduces no multiplicity or
normalization change. -/
theorem tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers
    {b κ : ℝ} (hb : 0 < b) (hb1 : b < 1) (hκ : 0 < κ) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)))
      atTop (nhds (Real.log (1 / b))) :=
  tendsto_realHalfProductSource_manuscriptCutoff_mass_of_real_pnt_and_weighted_mertens
    realHalfProduct_primeCounting_asymptotic_real hb hb1 hκ
    (tendsto_realPrimeReciprocalLogIntervalSum_halfProduct hb hb1)

end

end ImbalancedChen
