import ImbalancedChen.Part3ActualJFirstMixedDerivative
import ImbalancedChen.Part3ActualJSecondOrderJet

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Second full actual-J mixed derivative, derived using the actual contiguous
q-jet relation, its genuine q and order derivatives, and uniqueness of
native derivatives. This supplies both missing mixed APIs and hence a
true inhomogeneous Bessel equation for the actual order derivative.
No hMixed, hODE, hEnergy, or critical-kernel supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualJSecondMixedDerivative20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualJLocalOrderHolomorphic20261026a
open ActualJFirstOrderJet20261026b ActualJSecondOrderJet20261026b
open ActualJFirstMixedDerivative20261026b

def secondMixedCandidate (nu : ℂ) (q : ℝ) : ℂ :=
  -generalJ nu q / (q : ℂ) ^ 2 - (nu / (q : ℂ) ^ 2) * actualJOrderDerivative nu q +
    generalJFirst nu q / (q : ℂ) + (nu / (q : ℂ)) * actualJFirstOrderDerivative nu q -
      actualJFirstOrderDerivative (nu + 1) q

private theorem shifted_order_mem {nu : ℂ} (hnu : nu ∈ orderHalfPlane) :
    nu + 1 ∈ orderHalfPlane := by
  change -(1 / 4 : ℝ) < nu.re at hnu
  change -(1 / 4 : ℝ) < (nu + 1).re
  simp only [Complex.add_re, Complex.one_re]
  linarith

private theorem quotient_q_hasDerivAt (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => nu / (x : ℂ)) (-nu / (q : ℂ) ^ 2) q := by
  convert (hasDerivAt_const q nu).div (hasDerivAt_id q).ofReal_comp
    (Complex.ofReal_ne_zero.mpr hq.ne') using 1 <;> ring

theorem generalJSecond_eq_contiguous_first {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    generalJSecond nu q = -(nu / (q : ℂ) ^ 2) * generalJ nu q +
      (nu / (q : ℂ)) * generalJFirst nu q - generalJFirst (nu + 1) q := by
  have hn : -1 < nu.re := by change -(1 / 4 : ℝ) < nu.re at hnu; linarith
  have hn' : -1 < (nu + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hc := ((quotient_q_hasDerivAt nu hq).mul (generalJ_hasDerivAt hn hq)).sub
    (generalJ_hasDerivAt hn' hq)
  have he : generalJFirst nu =ᶠ[𝓝 q]
      (fun x => (nu / (x : ℂ)) * generalJ nu x - generalJ (nu + 1) x) := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact generalJFirst_eq_contiguous nu hx
  have h : HasDerivAt (generalJFirst nu)
      (-(nu / (q : ℂ) ^ 2) * generalJ nu q +
        (nu / (q : ℂ)) * generalJFirst nu q - generalJFirst (nu + 1) q) q := by
    convert hc.congr_of_eventuallyEq he using 1 <;> ring
  exact (generalJFirst_hasDerivAt hn hq).unique h

private theorem secondCandidate_order_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => generalJSecond z q) (secondMixedCandidate nu q) nu := by
  have h0 := generalJ_order_hasDerivAt hnu hq
  have h1 := generalJFirst_order_hasDerivAt hnu hq
  have hshift := (generalJFirst_order_hasDerivAt (shifted_order_mem hnu) hq).comp nu
    ((hasDerivAt_id nu).add_const 1)
  have h := ((((hasDerivAt_id nu).div_const ((q : ℂ) ^ 2)).neg.mul h0).add
    (((hasDerivAt_id nu).div_const (q : ℂ)).mul h1)).sub hshift
  have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have he : (fun z : ℂ => generalJSecond z q) =ᶠ[𝓝 nu]
      (fun z => -(z / (q : ℂ) ^ 2) * generalJ z q +
        (z / (q : ℂ)) * generalJFirst z q - generalJFirst (z + 1) q) := by
    filter_upwards [hopen.mem_nhds hnu] with z hz
    exact generalJSecond_eq_contiguous_first hz hq
  convert h.congr_of_eventuallyEq he using 1
  unfold secondMixedCandidate
  ring

theorem actualJSecondOrderDerivative_eq_candidate {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) : actualJSecondOrderDerivative nu q = secondMixedCandidate nu q :=
  (generalJSecond_order_hasDerivAt hnu hq).unique (secondCandidate_order_hasDerivAt hnu hq)

/-- Missing second full mixed API, proved from actual native derivatives. -/
theorem actualJFirstOrderDerivative_q_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (actualJFirstOrderDerivative nu) (actualJSecondOrderDerivative nu q) q := by
  have hn : -1 < nu.re := by change -(1 / 4 : ℝ) < nu.re at hnu; linarith
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have h := (((generalJ_hasDerivAt hn hq).div (hasDerivAt_id q).ofReal_comp hqC).add
    ((quotient_q_hasDerivAt nu hq).mul (actualJOrderDerivative_q_hasDerivAt hnu hq))).sub
      (actualJOrderDerivative_q_hasDerivAt (shifted_order_mem hnu) hq)
  have hc : HasDerivAt (actualJFirstOrderDerivative nu) (secondMixedCandidate nu q) q := by
    convert h using 1
    · rfl
    · unfold secondMixedCandidate
      field_simp [hqC] <;> ring
  rw [← actualJSecondOrderDerivative_eq_candidate hnu hq] at hc
  exact hc

theorem actualJOrderDerivative_second_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (deriv (actualJOrderDerivative nu)) (actualJSecondOrderDerivative nu q) q := by
  have he : deriv (actualJOrderDerivative nu) =ᶠ[𝓝 q] actualJFirstOrderDerivative nu := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (actualJOrderDerivative_q_hasDerivAt hnu hx).deriv
  exact (actualJFirstOrderDerivative_q_hasDerivAt hnu hq).congr_of_eventuallyEq he

/-- True native q-ODE for the actual order derivative. Both mixed APIs
have now been proved, so the forcing is not merely a formal jet relation. -/
theorem actualJOrderDerivative_native_Bessel_forcing {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * deriv (deriv (actualJOrderDerivative nu)) q +
      (q : ℂ) * deriv (actualJOrderDerivative nu) q +
        ((q : ℂ) ^ 2 - nu ^ 2) * actualJOrderDerivative nu q = 2 * nu * generalJ nu q := by
  rw [(actualJOrderDerivative_second_hasDerivAt hnu hq).deriv,
    (actualJOrderDerivative_q_hasDerivAt hnu hq).deriv]
  exact generalJ_order_jet_equation nu hq

end
end ImbalancedChen.Part3.ActualJSecondMixedDerivative20261026b
