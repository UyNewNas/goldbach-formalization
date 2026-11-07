import ImbalancedChen.Part3ActualJLocalOrderHolomorphic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual first mixed q/order derivatives of the principal-power/Gamma
Poisson prefactor. Both orders of differentiation are proved by native
calculus, with the actual Gamma derivative and a positive q branch.
No critical kernel or mixed-derivative supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualJPoissonPrefactorMixed20261026b

noncomputable section
open Complex Set
open ActualJLocalOrderHolomorphic20261026a

def gammaDenominator (nu : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Gamma (nu + 1 / 2)

def gammaDenominatorOrder (nu : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * deriv Gamma (nu + 1 / 2)

def poissonPrefactor (nu : ℂ) (q : ℝ) : ℂ :=
  (((q / 2 : ℝ) : ℂ) ^ nu) / gammaDenominator nu

def poissonPrefactorOrder (nu : ℂ) (q : ℝ) : ℂ :=
  ((((q / 2 : ℝ) : ℂ) ^ nu) * Complex.log (((q / 2 : ℝ) : ℂ)) * gammaDenominator nu -
    (((q / 2 : ℝ) : ℂ) ^ nu) * gammaDenominatorOrder nu) / gammaDenominator nu ^ 2

def poissonPrefactorQOrder (nu : ℂ) (q : ℝ) : ℂ :=
  poissonPrefactor nu q / (q : ℂ) + (nu / (q : ℂ)) * poissonPrefactorOrder nu q

theorem gammaDenominator_ne_zero {nu : ℂ} (hnu : nu ∈ orderHalfPlane) :
    gammaDenominator nu ≠ 0 := by
  have hp : 0 < (nu + 1 / 2).re := by
    change -(1 / 4 : ℝ) < nu.re at hnu
    simp only [Complex.add_re]
    norm_num
    linarith
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne')
    (Gamma_ne_zero_of_re_pos hp)

theorem gammaDenominator_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane) :
    HasDerivAt gammaDenominator (gammaDenominatorOrder nu) nu := by
  have hp : 0 < (nu + 1 / 2).re := by
    change -(1 / 4 : ℝ) < nu.re at hnu
    simp only [Complex.add_re]
    norm_num
    linarith
  have hg := ((Complex.differentiableAt_Gamma (nu + 1 / 2) (fun n hn => by
    have he := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).hasDerivAt.comp nu ((hasDerivAt_id nu).add_const (1 / 2)))
      .const_mul (Real.sqrt Real.pi : ℂ)
  convert hg using 1 <;> simp only [gammaDenominator, gammaDenominatorOrder, mul_one]

private theorem power_q_hasDerivAt (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => (((x / 2 : ℝ) : ℂ) ^ nu))
      ((nu / (q : ℂ)) * (((q / 2 : ℝ) : ℂ) ^ nu)) q := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hb : (((q / 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hs : (((q / 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := Or.inl (by simpa using (show 0 < q / 2 by positivity))
  have h := (Complex.hasStrictDerivAt_cpow_const (c := nu) hs).hasDerivAt.comp_ofReal.scomp
    q ((hasDerivAt_id q).div_const 2)
  convert h using 1
  · rfl
  · rw [Complex.cpow_sub _ _ hb, Complex.cpow_one]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hqC] <;> ring

private theorem log_q_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => Complex.log (((x / 2 : ℝ) : ℂ))) (1 / (q : ℂ)) q := by
  have hs : (((q / 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := Or.inl (by simpa using (show 0 < q / 2 by positivity))
  have h := (((hasDerivAt_id q).div_const 2).ofReal_comp).clog_real hs
  convert h using 1
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  push_cast
  field_simp [hqC] <;> ring

theorem poissonPrefactor_order_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => poissonPrefactor z q) (poissonPrefactorOrder nu q) nu := by
  have hp := (Complex.hasStrictDerivAt_const_cpow
    (x := (((q / 2 : ℝ) : ℂ))) (y := nu)
    (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity : (q / 2 : ℝ) ≠ 0)))).hasDerivAt
  exact hp.div (gammaDenominator_hasDerivAt hnu) (gammaDenominator_ne_zero hnu)

theorem poissonPrefactor_q_hasDerivAt (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (poissonPrefactor nu) ((nu / (q : ℂ)) * poissonPrefactor nu q) q := by
  convert (power_q_hasDerivAt nu hq).div_const (gammaDenominator nu) using 1 <;>
    unfold poissonPrefactor <;> ring

theorem poissonPrefactorOrder_q_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (poissonPrefactorOrder nu) (poissonPrefactorQOrder nu q) q := by
  have hp := power_q_hasDerivAt nu hq
  have hl := log_q_hasDerivAt hq
  have h := (((hp.mul hl).mul_const (gammaDenominator nu)).sub
    (hp.mul_const (gammaDenominatorOrder nu))).div_const (gammaDenominator nu ^ 2)
  convert h using 1
  · rfl
  · unfold poissonPrefactorQOrder poissonPrefactor poissonPrefactorOrder
    have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have hg := gammaDenominator_ne_zero hnu
    field_simp [hqC, hg] <;> ring

/-- The reverse mixed derivative gives the identical native value. -/
theorem poissonPrefactorQ_order_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => (z / (q : ℂ)) * poissonPrefactor z q)
      (poissonPrefactorQOrder nu q) nu := by
  have h := ((hasDerivAt_id nu).div_const (q : ℂ)).mul
    (poissonPrefactor_order_hasDerivAt hnu hq)
  convert h using 1
  unfold poissonPrefactorQOrder
  ring

end
end ImbalancedChen.Part3.ActualJPoissonPrefactorMixed20261026b
