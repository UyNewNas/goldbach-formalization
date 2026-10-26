import ImbalancedChen.Part3ActualJPoissonPrefactorMixed
import ImbalancedChen.Part3ActualJPoissonMixedMoments
import ImbalancedChen.Part3ActualJFirstOrderJet

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

First full actual-J mixed derivative. The q derivative of the literal
actual order derivative is proved to be the native order derivative of
the actual first q-jet. The calculation uses actual principal/Gamma
prefactor mixed derivatives and actual Poisson mixed moments; no Schwartz
commutation or mixed-jet identity is an assumption.
-/

namespace ImbalancedChen.Part3.ActualJFirstMixedDerivative20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open ActualJLocalOrderHolomorphic20261026a ActualJFirstOrderJet20261026b
open ActualJPoissonPrefactorMixed20261026b ActualJPoissonMixedMoments20261026b

def poissonJFirstJet (nu : ℂ) (q : ℝ) : ℂ :=
  (nu / (q : ℂ)) * poissonPrefactor nu q * poissonQMoment 0 nu q +
    poissonPrefactor nu q * poissonQMoment 1 nu q

def poissonJFirstOrderJet (nu : ℂ) (q : ℝ) : ℂ :=
  poissonPrefactorQOrder nu q * poissonQMoment 0 nu q +
    (nu / (q : ℂ)) * poissonPrefactor nu q * poissonQLogMoment 0 nu q +
      poissonPrefactorOrder nu q * poissonQMoment 1 nu q +
        poissonPrefactor nu q * poissonQLogMoment 1 nu q

theorem generalJ_eq_poissonPrefactor {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    generalJ nu q = poissonPrefactor nu q * poissonQMoment 0 nu q := by
  have hn : -(1 / 2 : ℝ) < nu.re := by change -(1 / 4 : ℝ) < nu.re at hnu; linarith
  change generalJ nu q = poissonPrefactor nu q * orderPoissonIntegral nu q
  rw [orderPoissonIntegral_eq]
  exact generalJ_eq_symmetric_poisson_integral hn hq

theorem actualJOrderDerivative_eq_poisson (nu : ℂ) (q : ℝ) :
    actualJOrderDerivative nu q =
      poissonPrefactorOrder nu q * poissonQMoment 0 nu q +
        poissonPrefactor nu q * poissonQLogMoment 0 nu q := by
  simp only [actualJOrderDerivative, poissonPrefactorOrder, poissonPrefactor,
    gammaDenominator, gammaDenominatorOrder, poissonQMoment, poissonQLogMoment,
    poissonQIntegrand, poissonQLogIntegrand, pow_zero, one_mul,
    orderPoissonIntegral, orderPoissonDeriv]

theorem generalJFirst_eq_poissonJet {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) : generalJFirst nu q = poissonJFirstJet nu q := by
  have he : generalJ nu =ᶠ[𝓝 q]
      (fun x => poissonPrefactor nu x * poissonQMoment 0 nu x) := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact generalJ_eq_poissonPrefactor hnu hx
  have hc := ((poissonPrefactor_q_hasDerivAt nu hq).mul
    (poissonQMoment_q_hasDerivAt 0 hnu q)).congr_of_eventuallyEq he
  have h : HasDerivAt (generalJ nu) (poissonJFirstJet nu q) q := by
    convert hc using 1
    unfold poissonJFirstJet
    ring
  have hn : -1 < nu.re := by change -(1 / 4 : ℝ) < nu.re at hnu; linarith
  exact (generalJ_hasDerivAt hn hq).unique h

theorem poissonJFirstJet_order_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => poissonJFirstJet z q) (poissonJFirstOrderJet nu q) nu := by
  have h := ((poissonPrefactorQ_order_hasDerivAt hnu hq).mul
    (poissonQMoment_order_hasDerivAt 0 hnu q)).add
      ((poissonPrefactor_order_hasDerivAt hnu hq).mul
        (poissonQMoment_order_hasDerivAt 1 hnu q))
  convert h using 1 <;> unfold poissonJFirstJet poissonJFirstOrderJet <;> ring

theorem actualJFirstOrderDerivative_eq_poisson {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) : actualJFirstOrderDerivative nu q = poissonJFirstOrderJet nu q := by
  have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have he : (fun z : ℂ => generalJFirst z q) =ᶠ[𝓝 nu] (fun z => poissonJFirstJet z q) := by
    filter_upwards [hopen.mem_nhds hnu] with z hz
    exact generalJFirst_eq_poissonJet hz hq
  exact (generalJFirst_order_hasDerivAt hnu hq).unique
    ((poissonJFirstJet_order_hasDerivAt hnu hq).congr_of_eventuallyEq he)

/-- Missing first mixed API supplied with actual native derivatives. -/
theorem actualJOrderDerivative_q_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (actualJOrderDerivative nu) (actualJFirstOrderDerivative nu q) q := by
  have h := ((poissonPrefactorOrder_q_hasDerivAt hnu hq).mul
    (poissonQMoment_q_hasDerivAt 0 hnu q)).add
      ((poissonPrefactor_q_hasDerivAt nu hq).mul (poissonQLogMoment_q_hasDerivAt 0 hnu q))
  have he : actualJOrderDerivative nu =ᶠ[𝓝 q]
      (fun x => poissonPrefactorOrder nu x * poissonQMoment 0 nu x +
        poissonPrefactor nu x * poissonQLogMoment 0 nu x) :=
    Eventually.of_forall (fun x => actualJOrderDerivative_eq_poisson nu x)
  have hc : HasDerivAt (actualJOrderDerivative nu) (poissonJFirstOrderJet nu q) q := by
    convert h.congr_of_eventuallyEq he using 1
    unfold poissonJFirstOrderJet
    ring
  rw [← actualJFirstOrderDerivative_eq_poisson hnu hq] at hc
  exact hc

theorem actualJOrderDerivative_native_q_deriv {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    deriv (actualJOrderDerivative nu) q = actualJFirstOrderDerivative nu q :=
  (actualJOrderDerivative_q_hasDerivAt hnu hq).deriv

end
end ImbalancedChen.Part3.ActualJFirstMixedDerivative20261026b
