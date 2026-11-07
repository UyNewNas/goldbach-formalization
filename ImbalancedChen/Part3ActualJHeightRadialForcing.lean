import ImbalancedChen.Part3ActualJSecondMixedDerivative
import ImbalancedChen.Part3ActualJImaginaryRadialJet

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual real-height derivative w=d_t(sqrt(q)J_(2it)(q)) and its native q
jets satisfy w''+(1+(1/4+4t^2)/q^2)w=-(8t/q^2)u, u=sqrt(q)J_(2it)(q).
All mixed derivatives have been proved; this is a true native forced ODE.
No forcing/energy/critical-kernel supplier is an assumption.
-/

namespace ImbalancedChen.Part3.ActualJHeightRadialForcing20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualJLocalOrderHolomorphic20261026a
open ActualJFirstOrderJet20261026b ActualJSecondOrderJet20261026b
open ActualJFirstMixedDerivative20261026b ActualJSecondMixedDerivative20261026b
open ActualJImaginaryRadialJet20261026b

def heightOrderJ (t q : ℝ) : ℂ := 2 * I * actualJOrderDerivative (2 * I * (t : ℂ)) q
def heightOrderJFirst (t q : ℝ) : ℂ := 2 * I * actualJFirstOrderDerivative (2 * I * (t : ℂ)) q
def heightOrderJSecond (t q : ℝ) : ℂ := 2 * I * actualJSecondOrderDerivative (2 * I * (t : ℂ)) q

def radialW (t q : ℝ) : ℂ := (Real.sqrt q : ℂ) * heightOrderJ t q
def radialWFirst (t q : ℝ) : ℂ :=
  (Real.sqrt q : ℂ) * heightOrderJFirst t q +
    ((1 / (2 * Real.sqrt q) : ℝ) : ℂ) * heightOrderJ t q
def radialWForcing (t q : ℝ) : ℂ := (-8 * t / q ^ 2 : ℝ) • radialJ t q

private theorem imaginary_order_mem (t : ℝ) : 2 * I * (t : ℂ) ∈ orderHalfPlane := by
  simp [orderHalfPlane]

theorem heightOrderJ_q_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (heightOrderJ t) (heightOrderJFirst t q) q :=
  (actualJOrderDerivative_q_hasDerivAt (imaginary_order_mem t) hq).const_mul (2 * I)

theorem heightOrderJFirst_q_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (heightOrderJFirst t) (heightOrderJSecond t q) q :=
  (actualJFirstOrderDerivative_q_hasDerivAt (imaginary_order_mem t) hq).const_mul (2 * I)

theorem generalJ_height_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => generalJ (2 * I * (x : ℂ)) q) (heightOrderJ t q) t := by
  have hp : HasDerivAt (fun z : ℂ => 2 * I * z) (2 * I) (t : ℂ) :=
    (hasDerivAt_id (t : ℂ)).const_mul (2 * I)
  have h := ((generalJ_order_hasDerivAt (imaginary_order_mem t) hq).comp (t : ℂ) hp).comp_ofReal
  convert h using 1 <;> unfold heightOrderJ <;> ring

theorem radialJ_height_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => radialJ x q) (radialW t q) t :=
  (generalJ_height_hasDerivAt t hq).const_mul (Real.sqrt q : ℂ)

private theorem heightOrderJSecond_eq (t : ℝ) {q : ℝ} (hq : 0 < q) :
    heightOrderJSecond t q = -heightOrderJFirst t q / (q : ℂ) -
      (1 + 4 * (t : ℂ) ^ 2 / (q : ℂ) ^ 2) * heightOrderJ t q -
        (8 * (t : ℂ) / (q : ℂ) ^ 2) * generalJ (2 * I * (t : ℂ)) q := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have h := imaginary_height_order_jet_forcing t hq
  change (q : ℂ) ^ 2 * heightOrderJSecond t q + (q : ℂ) * heightOrderJFirst t q +
    ((q : ℂ) ^ 2 + 4 * (t : ℂ) ^ 2) * heightOrderJ t q =
      -8 * (t : ℂ) * generalJ (2 * I * (t : ℂ)) q at h
  have hsolve : heightOrderJSecond t q =
      (-(q : ℂ) * heightOrderJFirst t q - ((q : ℂ) ^ 2 + 4 * (t : ℂ) ^ 2) *
        heightOrderJ t q - 8 * (t : ℂ) * generalJ (2 * I * (t : ℂ)) q) / (q : ℂ) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hqC)).2
    linear_combination h
  rw [hsolve]
  field_simp [hqC] <;> ring

private theorem half_inverse_sqrt_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => 1 / (2 * Real.sqrt x)) (-(1 / (4 * (Real.sqrt q) ^ 3))) q := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have h := ((Real.hasDerivAt_sqrt hq.ne').const_mul 2).inv (mul_ne_zero (by norm_num) hs)
  convert h using 1
  · funext x
    exact one_div _
  · field_simp [hs] <;> ring

theorem radialW_q_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (radialW t) (radialWFirst t q) q := by
  have h := (Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul (heightOrderJ_q_hasDerivAt t hq)
  convert h using 1 <;> unfold radialW radialWFirst <;> ring

/-- Actual forced radial jet derivative, with the exact native forcing. -/
theorem radialWFirst_q_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (radialWFirst t) (-(radialPotential t q) • radialW t q + radialWForcing t q) q := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hsC : (Real.sqrt q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsq : (Real.sqrt q : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast Real.sq_sqrt hq.le
  have h := ((Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul (heightOrderJFirst_q_hasDerivAt t hq)).add
    ((half_inverse_sqrt_hasDerivAt hq).ofReal_comp.mul (heightOrderJ_q_hasDerivAt t hq))
  convert h using 1
  · rfl
  · rw [heightOrderJSecond_eq t hq]
    unfold radialPotential radialCoefficient radialW radialWForcing radialJ
    simp only [Complex.real_smul]
    push_cast
    rw [← hsq]
    field_simp [hsC] <;> ring

theorem radialW_native_forced_equation (t : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (deriv (radialW t)) q + (radialPotential t q) • radialW t q = radialWForcing t q := by
  have he : deriv (radialW t) =ᶠ[𝓝 q] radialWFirst t := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (radialW_q_hasDerivAt t hx).deriv
  have h := (radialWFirst_q_hasDerivAt t hq).congr_of_eventuallyEq he
  rw [h.deriv]
  simp only [neg_smul]
  abel

end
end ImbalancedChen.Part3.ActualJHeightRadialForcing20261026b
