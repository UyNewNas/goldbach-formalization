import ImbalancedChen.Part3ActualGeneralJBessel
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic

/-!
Actual complex-argument ordinary J from its literal reciprocal-Gamma core.
The principal slit supplies analyticity of the positive-base complex power.
The rotations at +/-i*q are derived from the actual principal logarithms
log(i)=i*pi/2 and log(-i)=-i*pi/2 and retain both branch phases.
No analytic continuation, rotation formula, or Bessel identification is assumed.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualGeneralJComplexArgument20261025a

noncomputable section
open Complex Set
open GeneralComplexISeriesSourceOnly ActualGeneralJBesselSourceOnly

/-- Literal principal-branch J at a complex argument. The entire core is
evaluated at the actual negative quadratic argument. -/
def generalJComplex (nu z : ℂ) : ℂ :=
  (z / 2) ^ nu * generalICore nu (-((z / 2) ^ (2 : ℕ)))

private theorem half_mem_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z / 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with hr | hi
  · left
    simpa only [Complex.div_ofNat_re] using div_pos hr (by norm_num : (0 : ℝ) < 2)
  · right
    simpa only [Complex.div_ofNat_im] using div_ne_zero hi (by norm_num : (2 : ℝ) ≠ 0)

/-- Holomorphy on the principal slit follows from the actual entire Gamma
core and the actual principal power, not an assumed Bessel regularity. -/
theorem analyticAt_generalJComplex {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) : AnalyticAt ℂ (generalJComplex nu) z := by
  have hh : AnalyticAt ℂ (fun w : ℂ => w / 2) z := analyticAt_id.div_const
  have hp : AnalyticAt ℂ (fun w : ℂ => (w / 2) ^ nu) z :=
    hh.cpow analyticAt_const (half_mem_slit hz)
  have hc : AnalyticAt ℂ (fun w : ℂ => -((w / 2) ^ (2 : ℕ))) z := (hh.pow 2).neg
  exact hp.mul ((analyticAt_generalICore hnu (-((z / 2) ^ (2 : ℕ)))).comp hc)

theorem analyticOnNhd_generalJComplex {nu : ℂ} (hnu : -1 < nu.re) :
    AnalyticOnNhd ℂ (generalJComplex nu) Complex.slitPlane :=
  fun _ hz => analyticAt_generalJComplex hnu hz

theorem differentiableOn_generalJComplex {nu : ℂ} (hnu : -1 < nu.re) :
    DifferentiableOn ℂ (generalJComplex nu) Complex.slitPlane :=
  (analyticOnNhd_generalJComplex hnu).differentiableOn

/-- Restriction to the actual positive real argument agrees exactly with
the previously defined literal ordinary J. The equality of definitions
also holds for real arguments outside the positive axis. -/
theorem generalJComplex_ofReal (nu : ℂ) (q : ℝ) :
    generalJComplex nu (q : ℂ) = generalJ nu q := by
  simp only [generalJComplex, generalJ, Complex.ofReal_div, Complex.ofReal_ofNat]

/-- The upper imaginary-axis phase is proved from the principal logarithm;
no unrestricted complex product-power rule is used. -/
theorem positive_mul_I_cpow (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) * I) ^ nu =
      Complex.exp (I * (Real.pi : ℂ) * nu / 2) * (x : ℂ) ^ nu := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hxC Complex.I_ne_zero),
    Complex.log_ofReal_mul hx Complex.I_ne_zero, Complex.log_I,
    add_mul, Complex.exp_add, Complex.cpow_def_of_ne_zero hxC,
    ← Complex.ofReal_log hx.le]
  have hphase : (((Real.pi : ℂ) / 2) * I) * nu = I * (Real.pi : ℂ) * nu / 2 := by ring
  rw [hphase]
  exact mul_comm _ _

/-- The lower imaginary-axis phase is separate, because its principal
logarithm is -i*pi/2. This is the actual negative rotation branch. -/
theorem positive_mul_neg_I_cpow (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) * (-I)) ^ nu =
      Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * (x : ℂ) ^ nu := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hi : -I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hxC hi),
    Complex.log_ofReal_mul hx hi, Complex.log_neg_I,
    add_mul, Complex.exp_add, Complex.cpow_def_of_ne_zero hxC,
    ← Complex.ofReal_log hx.le]
  have hphase : (-((Real.pi : ℂ) / 2) * I) * nu = (-I) * (Real.pi : ℂ) * nu / 2 := by ring
  rw [hphase]
  exact mul_comm _ _

/-- The exact positive q rotation dictionary J_nu(iq)=exp(i*pi*nu/2)I_nu(q).
The negative core becomes the positive I core by the literal square of i. -/
theorem generalJComplex_rotate_upper (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    generalJComplex nu (I * (q : ℂ)) =
      Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalI nu q := by
  have hh : 0 < q / 2 := div_pos hq (by norm_num)
  have hb : (I * (q : ℂ)) / 2 = ((q / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hc : -(((I * (q : ℂ)) / 2) ^ (2 : ℕ)) = (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
    rw [hb, mul_pow, Complex.I_sq]
    ring
  rw [generalJComplex, hc, hb, positive_mul_I_cpow nu hh, generalI]
  ring

/-- The lower branch has the conjugate phase exp(-i*pi*nu/2); its sign is
proved with log(-i), rather than inferred by an invalid product rule. -/
theorem generalJComplex_rotate_lower (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    generalJComplex nu ((-I) * (q : ℂ)) =
      Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalI nu q := by
  have hh : 0 < q / 2 := div_pos hq (by norm_num)
  have hb : ((-I) * (q : ℂ)) / 2 = ((q / 2 : ℝ) : ℂ) * (-I) := by
    push_cast
    ring
  have hc : -((((-I) * (q : ℂ)) / 2) ^ (2 : ℕ)) = (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
    rw [hb, mul_pow, neg_sq, Complex.I_sq]
    ring
  rw [generalJComplex, hc, hb, positive_mul_neg_I_cpow nu hh, generalI]
  ring

private theorem gamma_coefficient_conjugate (nu : ℂ) (n : ℕ) :
    conj (generalICoeff nu n) = generalICoeff (conj nu) n := by
  simp [generalICoeff, ← Complex.Gamma_conj]

private theorem gamma_core_conjugate (nu z : ℂ) :
    conj (generalICore nu z) = generalICore (conj nu) (conj z) := by
  simp only [generalICore, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [map_mul, gamma_coefficient_conjugate, map_pow]

/-- Principal-slit conjugation of the complex-argument J series, proved
from the actual Gamma coefficients and the valid conjugation of cpow. -/
theorem conj_generalJComplex (nu : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    conj (generalJComplex nu z) = generalJComplex (conj nu) (conj z) := by
  have hp := (Complex.conj_cpow (z / 2) (conj nu)
    (Complex.slitPlane_arg_ne_pi (half_mem_slit hz))).symm
  simp only [Complex.conj_conj, map_div, map_ofNat] at hp
  simp only [generalJComplex, map_mul, hp, gamma_core_conjugate,
    map_neg, map_pow, map_div, map_ofNat]

/-- In particular, the two imaginary-axis branches are actual conjugates
when the order is conjugated. This makes the branch convention explicit. -/
theorem upper_rotation_conjugate_lower (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    conj (generalJComplex nu (I * (q : ℂ))) =
      generalJComplex (conj nu) ((-I) * (q : ℂ)) := by
  have hz : I * (q : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using hq.ne'
  simpa only [map_mul, Complex.conj_I, Complex.conj_ofReal] using conj_generalJComplex nu hz

end
end ImbalancedChen.Part3.ActualGeneralJComplexArgument20261025a
