import ImbalancedChen.Part3ActualGeneralJComplexArgument
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Native complex-argument first and second jets of literal ordinary J on
the principal slit. Both derivatives are derived directly from the
principal power and the negative-quadratic entire reciprocal-Gamma core.
No complex Bessel equation or derivative supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualJComplexArgumentJets20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open GeneralComplexISeriesSourceOnly GeneralICoreDifferential20261025a
open ActualGeneralJComplexArgument20261025a

def complexJHalf (z : ℂ) : ℂ := z / 2
def complexJPower (nu z : ℂ) : ℂ := (complexJHalf z) ^ nu
def complexJCore (nu z : ℂ) : ℂ := generalICore nu (-(complexJHalf z ^ 2))

def generalJComplexFirst (nu z : ℂ) : ℂ :=
  complexJPower nu z * ((nu / z) * complexJCore nu z - complexJHalf z * complexJCore (nu + 1) z)

def generalJComplexSecond (nu z : ℂ) : ℂ :=
  complexJPower nu z * ((nu * (nu - 1) / z ^ 2) * complexJCore nu z -
    (nu + 1 / 2) * complexJCore (nu + 1) z + complexJHalf z ^ 2 * complexJCore (nu + 1 + 1) z)

theorem complexJHalf_mem_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    complexJHalf z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with hr | hi
  · left
    simpa only [complexJHalf, Complex.div_ofNat_re] using div_pos hr (by norm_num : (0 : ℝ) < 2)
  · right
    simpa only [complexJHalf, Complex.div_ofNat_im] using div_ne_zero hi (by norm_num : (2 : ℝ) ≠ 0)

theorem complexJHalf_hasDerivAt (z : ℂ) : HasDerivAt complexJHalf (1 / 2) z :=
  (hasDerivAt_id z).div_const 2

theorem complexJPower_hasDerivAt (nu : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (complexJPower nu) ((nu / z) * complexJPower nu z) z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have hh0 := Complex.slitPlane_ne_zero (complexJHalf_mem_slit hz)
  have h := (complexJHalf_hasDerivAt z).cpow_const (complexJHalf_mem_slit hz)
  convert h using 1
  · rfl
  · rw [Complex.cpow_sub _ _ hh0, Complex.cpow_one]
    unfold complexJPower complexJHalf
    field_simp [hz0]
    ring

theorem complexJCore_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    HasDerivAt (complexJCore nu) (-(complexJHalf z * complexJCore (nu + 1) z)) z := by
  have hz : HasDerivAt (fun w : ℂ => -(complexJHalf w ^ 2)) (-(complexJHalf z)) z := by
    convert ((complexJHalf_hasDerivAt z).pow 2).neg using 1 <;> ring
  have h := (generalICore_hasDerivAt hnu (-(complexJHalf z ^ 2))).comp z hz
  convert h using 1
  · rfl
  · unfold complexJCore
    ring

theorem generalJComplex_hasDerivAt {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (generalJComplex nu) (generalJComplexFirst nu z) z := by
  have h := (complexJPower_hasDerivAt nu hz).mul (complexJCore_hasDerivAt hnu z)
  convert h using 1
  · rfl
  · unfold generalJComplexFirst
    ring

theorem generalJComplexFirst_hasDerivAt {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (generalJComplexFirst nu) (generalJComplexSecond nu z) z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have hnu1 : -1 < (nu + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hquot : HasDerivAt (fun w : ℂ => nu / w) (-nu / z ^ 2) z := by
    simpa only [zero_mul, mul_one, zero_sub] using
      (hasDerivAt_const z nu).div (hasDerivAt_id z) hz0
  have hB := (hquot.mul (complexJCore_hasDerivAt hnu z)).sub
    ((complexJHalf_hasDerivAt z).mul (complexJCore_hasDerivAt hnu1 z))
  have h := (complexJPower_hasDerivAt nu hz).mul hB
  convert h using 1
  · rfl
  · unfold generalJComplexSecond complexJHalf
    field_simp [hz0]
    ring

theorem deriv_generalJComplex {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) :
    deriv (generalJComplex nu) z = generalJComplexFirst nu z :=
  (generalJComplex_hasDerivAt hnu hz).deriv

theorem deriv_generalJComplex_hasDerivAt {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (deriv (generalJComplex nu)) (generalJComplexSecond nu z) z := by
  apply (generalJComplexFirst_hasDerivAt hnu hz).congr_of_eventuallyEq
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
  exact deriv_generalJComplex hnu hw

theorem deriv_deriv_generalJComplex {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) :
    deriv (deriv (generalJComplex nu)) z = generalJComplexSecond nu z :=
  (deriv_generalJComplex_hasDerivAt hnu hz).deriv

end
end ImbalancedChen.Part3.ActualJComplexArgumentJets20261026b
