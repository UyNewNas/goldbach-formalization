import ImbalancedChen.Part3ActualJComplexArgumentJets

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual complex-variable ordinary Bessel equation for literal J on the
principal slit, derived from the summed reciprocal-Gamma core recurrence.
The real positive-axis complex jets are identified with the existing
native q-jets by uniqueness of the real derivative, not by an assumed
identification of two ODE solutions.
-/

namespace ImbalancedChen.Part3.ActualJComplexArgumentODE20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open GeneralICoreDifferential20261025a ActualGeneralJBesselSourceOnly
open ActualGeneralJComplexArgument20261025a ActualJComplexArgumentJets20261026b

theorem generalJComplex_jet_equation {nu z : ℂ} (hnu : -1 < nu.re) (hz : z ≠ 0) :
    z ^ 2 * generalJComplexSecond nu z + z * generalJComplexFirst nu z +
      (z ^ 2 - nu ^ 2) * generalJComplex nu z = 0 := by
  have hcore := generalICore_contiguous hnu (-(complexJHalf z ^ 2))
  change complexJCore nu z = (nu + 1) * complexJCore (nu + 1) z +
    (-(complexJHalf z ^ 2)) * complexJCore (nu + 1 + 1) z at hcore
  change z ^ 2 * generalJComplexSecond nu z + z * generalJComplexFirst nu z +
    (z ^ 2 - nu ^ 2) * (complexJPower nu z * complexJCore nu z) = 0
  dsimp only [generalJComplexSecond, generalJComplexFirst]
  rw [hcore]
  dsimp only [complexJHalf]
  field_simp [hz]
  ring

/-- Native complex first and second derivatives solve the ordinary J
equation, with the positive z^2 potential sign. -/
theorem generalJComplex_bessel_equation {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) :
    z ^ 2 * deriv (deriv (generalJComplex nu)) z + z * deriv (generalJComplex nu) z +
      (z ^ 2 - nu ^ 2) * generalJComplex nu z = 0 := by
  rw [deriv_deriv_generalJComplex hnu hz, deriv_generalJComplex hnu hz]
  exact generalJComplex_jet_equation hnu (Complex.slitPlane_ne_zero hz)

theorem generalJComplexFirst_ofReal {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJComplexFirst nu (q : ℂ) = generalJFirst nu q := by
  have hz : (q : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hq
  have h : HasDerivAt (generalJ nu) (generalJComplexFirst nu (q : ℂ)) q := by
    simpa only [generalJComplex_ofReal] using (generalJComplex_hasDerivAt hnu hz).comp_ofReal
  exact h.unique (generalJ_hasDerivAt hnu hq)

theorem generalJComplexSecond_ofReal {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJComplexSecond nu (q : ℂ) = generalJSecond nu q := by
  have hz : (q : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hq
  have hcomp := (generalJComplexFirst_hasDerivAt hnu hz).comp_ofReal
  have h : HasDerivAt (generalJFirst nu) (generalJComplexSecond nu (q : ℂ)) q := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (generalJComplexFirst_ofReal hnu hx).symm
  exact h.unique (generalJFirst_hasDerivAt hnu hq)

end
end ImbalancedChen.Part3.ActualJComplexArgumentODE20261026b
