import ImbalancedChen.Part3ActualJFirstOrderJet

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual order derivative of the second native q-jet, and the differentiated
scalar jet identity. The latter has the exact imaginary-height forcing
-8*t*J_(2it). It is NOT asserted to be an ODE for the q-derivatives of the
order derivative: those two mixed-derivative commutation theorems remain
explicit missing APIs. No hODE or hforcing supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualJSecondOrderJet20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualJLocalOrderHolomorphic20261026a
open ActualJFirstOrderJet20261026b

def actualJSecondOrderDerivative (nu : ℂ) (q : ℝ) : ℂ :=
  -actualJFirstOrderDerivative nu q / (q : ℂ) +
    (2 * nu / (q : ℂ) ^ 2) * generalJ nu q -
      (1 - nu ^ 2 / (q : ℂ) ^ 2) * actualJOrderDerivative nu q

theorem generalJSecond_eq_jetFormula {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJSecond nu q = -generalJFirst nu q / (q : ℂ) -
      (1 - nu ^ 2 / (q : ℂ) ^ 2) * generalJ nu q := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have h := generalJ_jet_equation hnu hq
  have hsolve : generalJSecond nu q =
      (-(q : ℂ) * generalJFirst nu q - ((q : ℂ) ^ 2 - nu ^ 2) * generalJ nu q) /
        (q : ℂ) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hqC)).2
    linear_combination h
  rw [hsolve]
  field_simp [hqC] <;> ring

/-- Native complex-order derivative of the actual second q-jet. -/
theorem generalJSecond_order_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => generalJSecond z q) (actualJSecondOrderDerivative nu q) nu := by
  have h0 := generalJ_order_hasDerivAt hnu hq
  have h1 := generalJFirst_order_hasDerivAt hnu hq
  have hv : HasDerivAt (fun z : ℂ => 1 - z ^ 2 / (q : ℂ) ^ 2)
      (-(2 * nu / (q : ℂ) ^ 2)) nu := by
    convert (hasDerivAt_const nu (1 : ℂ)).sub (((hasDerivAt_id nu).pow 2).div_const
      ((q : ℂ) ^ 2)) using 1 <;> ring
  have h := ((h1.div_const (q : ℂ)).neg).sub (hv.mul h0)
  have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have he : (fun z : ℂ => generalJSecond z q) =ᶠ[𝓝 nu]
      (fun z : ℂ => -generalJFirst z q / (q : ℂ) -
        (1 - z ^ 2 / (q : ℂ) ^ 2) * generalJ z q) := by
    filter_upwards [hopen.mem_nhds hnu] with z hz
    have hz' : -1 < z.re := by change -(1 / 4 : ℝ) < z.re at hz; linarith
    exact generalJSecond_eq_jetFormula hz' hq
  convert h.congr_of_eventuallyEq he using 1
  unfold actualJSecondOrderDerivative
  ring

theorem generalJSecond_native_order_deriv {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    deriv (fun z : ℂ => generalJSecond z q) nu = actualJSecondOrderDerivative nu q :=
  (generalJSecond_order_hasDerivAt hnu hq).deriv

/-- Scalar parameter derivative of the actual Bessel jet relation. -/
theorem generalJ_order_jet_equation (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * actualJSecondOrderDerivative nu q +
      (q : ℂ) * actualJFirstOrderDerivative nu q +
        ((q : ℂ) ^ 2 - nu ^ 2) * actualJOrderDerivative nu q = 2 * nu * generalJ nu q := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold actualJSecondOrderDerivative
  field_simp [hqC] <;> ring

/-- Exact -8*t forcing in the imaginary-height scalar order jets. This
does not replace the still-required q/order commutation theorem. -/
theorem imaginary_height_order_jet_forcing (t : ℝ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * (2 * I * actualJSecondOrderDerivative (2 * I * (t : ℂ)) q) +
      (q : ℂ) * (2 * I * actualJFirstOrderDerivative (2 * I * (t : ℂ)) q) +
        ((q : ℂ) ^ 2 + 4 * (t : ℂ) ^ 2) *
          (2 * I * actualJOrderDerivative (2 * I * (t : ℂ)) q) =
      -8 * (t : ℂ) * generalJ (2 * I * (t : ℂ)) q := by
  have h := generalJ_order_jet_equation (2 * I * (t : ℂ)) hq
  have hi : (2 * I * (t : ℂ)) ^ 2 = -4 * (t : ℂ) ^ 2 := by
    calc
      _ = 4 * (I * I) * (t : ℂ) ^ 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hi] at h
  simp only [neg_mul, sub_neg_eq_add] at h
  calc
    _ = 2 * I * ((q : ℂ) ^ 2 * actualJSecondOrderDerivative (2 * I * (t : ℂ)) q +
        (q : ℂ) * actualJFirstOrderDerivative (2 * I * (t : ℂ)) q +
          ((q : ℂ) ^ 2 + 4 * (t : ℂ) ^ 2) *
            actualJOrderDerivative (2 * I * (t : ℂ)) q) := by ring
    _ = 2 * I * (2 * (2 * I * (t : ℂ)) * generalJ (2 * I * (t : ℂ)) q) := by
      rw [h]
    _ = _ := by
      calc
        _ = 8 * (I * I) * (t : ℂ) * generalJ (2 * I * (t : ℂ)) q := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring

end
end ImbalancedChen.Part3.ActualJSecondOrderJet20261026b
