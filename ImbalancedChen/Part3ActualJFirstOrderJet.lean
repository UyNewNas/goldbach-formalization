import ImbalancedChen.Part3ActualJLocalOrderHolomorphic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual order derivative of the literal first q-jet of J. Its contiguous
identity is derived from the literal principal-power/core definition,
then differentiated using the proved genuine order derivative of actual J.
No interchange of q and order derivatives is assumed or concluded here.
This source imports no critical opposite-order kernel or held Mellin chain.
-/

namespace ImbalancedChen.Part3.ActualJFirstOrderJet20261026b

noncomputable section
open Complex Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralComplexISeriesSourceOnly
open ActualJLocalOrderHolomorphic20261026a

def actualJFirstOrderDerivative (nu : ℂ) (q : ℝ) : ℂ :=
  generalJ nu q / (q : ℂ) + (nu / (q : ℂ)) * actualJOrderDerivative nu q -
    actualJOrderDerivative (nu + 1) q

/-- Actual q-jet contiguous formula, proved from the native powers and
entire core rather than used as an additional Bessel supplier. -/
theorem generalJFirst_eq_contiguous (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    generalJFirst nu q = (nu / (q : ℂ)) * generalJ nu q - generalJ (nu + 1) q := by
  let b : ℂ := ((q / 2 : ℝ) : ℂ)
  let z : ℂ := -(b ^ (2 : ℕ))
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr (by dsimp [b]; positivity)
  have hp : b ^ (nu + 1) = b ^ nu * b := by
    rw [Complex.cpow_add nu 1 hb, Complex.cpow_one]
  change b ^ nu * ((nu / (q : ℂ)) * generalICore nu z - b * generalICore (nu + 1) z) =
    (nu / (q : ℂ)) * (b ^ nu * generalICore nu z) - b ^ (nu + 1) * generalICore (nu + 1) z
  rw [hp]
  ring

private theorem shifted_order_mem {nu : ℂ} (hnu : nu ∈ orderHalfPlane) :
    nu + 1 ∈ orderHalfPlane := by
  change -(1 / 4 : ℝ) < nu.re at hnu
  change -(1 / 4 : ℝ) < (nu + 1).re
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- Native order derivative of the actual first q-jet. This is a proved
scalar parameter derivative, not a mixed-derivative commutation premise. -/
theorem generalJFirst_order_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => generalJFirst z q) (actualJFirstOrderDerivative nu q) nu := by
  have h0 := generalJ_order_hasDerivAt hnu hq
  have h1 := (generalJ_order_hasDerivAt (shifted_order_mem hnu) hq).comp nu
    ((hasDerivAt_id nu).add_const 1)
  have h := (((hasDerivAt_id nu).div_const (q : ℂ)).mul h0).sub h1
  have he : (fun z : ℂ => generalJFirst z q) =ᶠ[𝓝 nu]
      (fun z : ℂ => (z / (q : ℂ)) * generalJ z q - generalJ (z + 1) q) :=
    Eventually.of_forall (fun z => generalJFirst_eq_contiguous z hq)
  convert h.congr_of_eventuallyEq he using 1
  unfold actualJFirstOrderDerivative
  ring

theorem generalJFirst_native_order_deriv {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    deriv (fun z : ℂ => generalJFirst z q) nu = actualJFirstOrderDerivative nu q :=
  (generalJFirst_order_hasDerivAt hnu hq).deriv

theorem generalJFirst_imaginary_order_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => generalJFirst (2 * I * (x : ℂ)) q)
      (2 * I * actualJFirstOrderDerivative (2 * I * (t : ℂ)) q) t := by
  have hnu : 2 * I * (t : ℂ) ∈ orderHalfPlane := by simp [orderHalfPlane]
  have hp : HasDerivAt (fun z : ℂ => 2 * I * z) (2 * I) (t : ℂ) :=
    (hasDerivAt_id (t : ℂ)).const_mul (2 * I)
  have h := ((generalJFirst_order_hasDerivAt hnu hq).comp (t : ℂ) hp).comp_ofReal
  convert h using 1 <;> ring

end
end ImbalancedChen.Part3.ActualJFirstOrderJet20261026b
