import ImbalancedChen.Part3GeneralComplexISeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Literal complex-argument I on the principal slit, built from the actual
entire reciprocal-Gamma core and the principal power (z/2)^nu. The core
argument is positive quadratic (z/2)^2, distinguishing it from the
already supplied ordinary-J complex model. Absolute convergence and
holomorphy are derived from the actual core source for -1<Re(nu), and
real-axis values agree exactly with the existing actual generalI.
No K/I connection or analytic continuation identity is an input here.
-/

namespace ImbalancedChen.Part3.ActualComplexArgumentISlit20261026b

noncomputable section
open Set
open GeneralComplexISeriesSourceOnly

def complexArgumentI (nu z : ℂ) : ℂ :=
  (z / 2) ^ nu * generalICore nu ((z / 2) ^ (2 : ℕ))

/-- Positive real scaling preserves the principal slit. -/
theorem halfArgument_mem_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z / 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with hr | hi
  · left
    simpa only [Complex.div_ofNat_re] using div_pos hr (by norm_num : (0 : ℝ) < 2)
  · right
    simpa only [Complex.div_ofNat_im] using div_ne_zero hi (by norm_num : (2 : ℝ) ≠ 0)

/-- The entire core provides actual absolute convergence at each complex
argument; no supplied convergence certificate is needed. -/
theorem complexArgumentI_summable_norm {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    Summable (fun n => ‖(z / 2) ^ nu *
      (generalICoeff nu n * ((z / 2) ^ (2 : ℕ)) ^ n)‖) := by
  simpa only [norm_mul] using
    (summable_norm_generalICore hnu ((z / 2) ^ (2 : ℕ))).mul_left ‖(z / 2) ^ nu‖

theorem complexArgumentI_hasSum {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    HasSum (fun n => (z / 2) ^ nu *
      (generalICoeff nu n * ((z / 2) ^ (2 : ℕ)) ^ n)) (complexArgumentI nu z) :=
  (generalICore_hasSum hnu ((z / 2) ^ (2 : ℕ))).mul_left _

/-- Actual principal-slit holomorphy, from the convergent Gamma core and
the analytic principal logarithm; no continuation premise is assumed. -/
theorem complexArgumentI_analyticAt {nu z : ℂ} (hnu : -1 < nu.re)
    (hz : z ∈ Complex.slitPlane) : AnalyticAt ℂ (complexArgumentI nu) z := by
  have hh : AnalyticAt ℂ (fun w : ℂ => w / 2) z := analyticAt_id.div_const
  have hp : AnalyticAt ℂ (fun w : ℂ => (w / 2) ^ nu) z :=
    hh.cpow analyticAt_const (halfArgument_mem_slit hz)
  have hc : AnalyticAt ℂ (fun w : ℂ => (w / 2) ^ (2 : ℕ)) z := hh.pow 2
  exact hp.mul ((analyticAt_generalICore hnu ((z / 2) ^ (2 : ℕ))).comp hc)

theorem complexArgumentI_analyticOnNhd {nu : ℂ} (hnu : -1 < nu.re) :
    AnalyticOnNhd ℂ (complexArgumentI nu) Complex.slitPlane :=
  fun _ hz => complexArgumentI_analyticAt hnu hz

/-- Equality to the existing actual I model follows from the literal
definitions and the complex coercion of the real half argument. -/
theorem complexArgumentI_real (nu : ℂ) (q : ℝ) :
    complexArgumentI nu (q : ℂ) = generalI nu q := by
  simp only [complexArgumentI, generalI, Complex.ofReal_div, Complex.ofReal_ofNat]

end
end ImbalancedChen.Part3.ActualComplexArgumentISlit20261026b
