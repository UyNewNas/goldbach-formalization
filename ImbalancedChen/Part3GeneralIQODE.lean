import ImbalancedChen.Part3GeneralICoreDifferential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Actual positive-q calculus and modified Bessel equation for the literal
complex-order Gamma-normalized I series. The order range -1<Re nu includes
the requested |Re nu|<1 strip. All derivative and ODE identities are proved
from the native core series theorem, not supplied as assumptions.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.GeneralIQODE20261025a

noncomputable section
open Set Filter
open GeneralComplexISeriesSourceOnly
open GeneralICoreDifferential20261025a

private theorem shifted_order {nu : ℂ} (hnu : -1 < nu.re) :
    -1 < (nu + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  linarith

private def halfQ (q : ℝ) : ℂ := ((q / 2 : ℝ) : ℂ)
private def coreQ (nu : ℂ) (q : ℝ) : ℂ := generalICore nu (halfQ q ^ 2)
private def powerQ (nu : ℂ) (q : ℝ) : ℂ := halfQ q ^ nu

private theorem halfQ_hasDerivAt (q : ℝ) :
    HasDerivAt halfQ (1 / 2 : ℂ) q := by
  simpa only [halfQ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    ((hasDerivAt_id q).div_const 2).ofReal_comp

private theorem coreQ_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re) (q : ℝ) :
    HasDerivAt (coreQ nu) (halfQ q * coreQ (nu + 1) q) q := by
  have hz : HasDerivAt (fun x : ℝ => (x / 2) ^ 2) (q / 2) q := by
    convert ((hasDerivAt_id q).div_const 2).pow 2 using 1 <;> ring
  have h := (generalICore_hasDerivAt hnu (((q / 2 : ℝ) ^ 2 : ℝ) : ℂ)).comp_ofReal.scomp q hz
  simpa only [coreQ, halfQ, Complex.ofReal_pow, Complex.real_smul] using h

private theorem powerQ_hasDerivAt (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (powerQ nu) ((nu / (q : ℂ)) * powerQ nu q) q := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hhalf : 0 < q / 2 := by positivity
  have hb : halfQ q ≠ 0 := by
    dsimp [halfQ]
    exact_mod_cast hhalf.ne'
  have hs : halfQ q ∈ Complex.slitPlane := by
    simp [halfQ, hhalf]
  have h := (Complex.hasStrictDerivAt_cpow_const (c := nu) hs).hasDerivAt.comp_ofReal.scomp
    q ((hasDerivAt_id q).div_const 2)
  convert h using 1
  · funext x
    rfl
  · rw [Complex.cpow_sub _ _ hb, Complex.cpow_one]
    simp only [Complex.real_smul, powerQ, halfQ, Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hqC]
    <;> ring

/-- The genuine first q jet, with the same principal positive-real power
and the same literal Gamma series core as generalI. -/
def generalIFirst (nu : ℂ) (q : ℝ) : ℂ :=
  powerQ nu q * ((nu / (q : ℂ)) * coreQ nu q + halfQ q * coreQ (nu + 1) q)

/-- The genuine second q jet. The core at nu+2 is an actual convergent
series, and the order remains complex throughout. -/
def generalISecond (nu : ℂ) (q : ℝ) : ℂ :=
  powerQ nu q *
    ((nu * (nu - 1) / (q : ℂ) ^ 2) * coreQ nu q +
      (nu + 1 / 2) * coreQ (nu + 1) q + halfQ q ^ 2 * coreQ (nu + 1 + 1) q)

theorem generalI_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) : HasDerivAt (generalI nu) (generalIFirst nu q) q := by
  have h := (powerQ_hasDerivAt nu hq).mul (coreQ_hasDerivAt hnu q)
  convert h using 1
  · funext x
    rfl
  · dsimp [generalIFirst]
    ring

theorem generalIFirst_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (generalIFirst nu) (generalISecond nu q) q := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hquot : HasDerivAt (fun x : ℝ => nu / (x : ℂ))
      (-nu / (q : ℂ) ^ 2) q := by
    simpa only [Pi.div_apply, zero_mul, mul_one, zero_sub] using
      (hasDerivAt_const q nu).div (hasDerivAt_id q).ofReal_comp hqC
  have hB := (hquot.mul (coreQ_hasDerivAt hnu q)).add
    ((halfQ_hasDerivAt q).mul (coreQ_hasDerivAt (shifted_order hnu) q))
  have h := (powerQ_hasDerivAt nu hq).mul hB
  convert h using 1
  · funext x
    rfl
  · dsimp [generalISecond, halfQ]
    push_cast
    field_simp [hqC]
    <;> ring

theorem deriv_generalI_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (deriv (generalI nu)) (generalISecond nu q) q := by
  apply (generalIFirst_hasDerivAt hnu hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  exact (generalI_hasDerivAt hnu hx).deriv

theorem generalI_differentiableAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) : DifferentiableAt ℝ (generalI nu) q :=
  (generalI_hasDerivAt hnu hq).differentiableAt

theorem generalI_deriv_differentiableAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) : DifferentiableAt ℝ (deriv (generalI nu)) q :=
  (deriv_generalI_hasDerivAt hnu hq).differentiableAt

private theorem continuous_coreQ {nu : ℂ} (hnu : -1 < nu.re) :
    Continuous (coreQ nu) := by
  exact (continuous_generalICore hnu).comp (by unfold halfQ; fun_prop)

private theorem powerQ_continuousOn (nu : ℂ) :
    ContinuousOn (powerQ nu) (Ioi (0 : ℝ)) := by
  intro q hq
  exact (powerQ_hasDerivAt nu hq).continuousAt.continuousWithinAt

/-- Continuity of the actual second jet is established from its three
convergent shifted-order cores, not inferred from mere formal algebra. -/
theorem generalISecond_continuousOn {nu : ℂ} (hnu : -1 < nu.re) :
    ContinuousOn (generalISecond nu) (Ioi (0 : ℝ)) := by
  have hnu1 := shifted_order hnu
  have hnu2 := shifted_order hnu1
  have hq : Continuous (fun q : ℝ => (q : ℂ)) := Complex.continuous_ofReal
  have hh : Continuous halfQ := by unfold halfQ; fun_prop
  have hcoeff : ContinuousOn (fun q : ℝ => nu * (nu - 1) / (q : ℂ) ^ 2)
      (Ioi (0 : ℝ)) :=
    continuousOn_const.div (hq.pow 2).continuousOn (fun q hq =>
      pow_ne_zero 2 (by exact_mod_cast hq.ne'))
  exact (powerQ_continuousOn nu).mul
    (((hcoeff.mul (continuous_coreQ hnu).continuousOn).add
      (continuousOn_const.mul (continuous_coreQ hnu1).continuousOn)).add
        ((hh.pow 2).continuousOn.mul (continuous_coreQ hnu2).continuousOn))

/-- The actual general complex I series is C2 on the entire positive
q-axis. This supplies the regularity needed by ordinary Abel/Green calculus. -/
theorem generalI_contDiffOn_two {nu : ℂ} (hnu : -1 < nu.re) :
    ContDiffOn ℝ 2 (generalI nu) (Ioi (0 : ℝ)) := by
  have hD : DifferentiableOn ℝ (deriv (generalI nu)) (Ioi (0 : ℝ)) := by
    intro q hq
    exact (generalI_deriv_differentiableAt hnu hq).differentiableWithinAt
  have hDD : ContinuousOn (deriv (deriv (generalI nu))) (Ioi (0 : ℝ)) :=
    (generalISecond_continuousOn hnu).congr
      (fun q hq => (deriv_generalI_hasDerivAt hnu hq).deriv)
  have hDone : ContDiffOn ℝ 1 (deriv (generalI nu)) (Ioi (0 : ℝ)) := by
    have hchar : ContDiffOn ℝ 1 (deriv (generalI nu)) (Ioi (0 : ℝ)) ↔
        DifferentiableOn ℝ (deriv (generalI nu)) (Ioi (0 : ℝ)) ∧
          ContinuousOn (deriv (deriv (generalI nu))) (Ioi (0 : ℝ)) := by
      rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      simp
    exact hchar.mpr ⟨hD, hDD⟩
  have hchar : ContDiffOn ℝ 2 (generalI nu) (Ioi (0 : ℝ)) ↔
      DifferentiableOn ℝ (generalI nu) (Ioi (0 : ℝ)) ∧
        ContDiffOn ℝ 1 (deriv (generalI nu)) (Ioi (0 : ℝ)) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    simp
  exact hchar.mpr ⟨(fun q hq =>
    (generalI_differentiableAt hnu hq).differentiableWithinAt), hDone⟩
/-- Exact positive-q modified Bessel equation for the computed jets. The
cancellation is the actual contiguous Gamma-core relation. -/
theorem generalI_jet_equation {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * generalISecond nu q + (q : ℂ) * generalIFirst nu q -
      ((q : ℂ) ^ 2 + nu ^ 2) * generalI nu q = 0 := by
  have hcore := generalICore_contiguous hnu (halfQ q ^ 2)
  change coreQ nu q = (nu + 1) * coreQ (nu + 1) q +
    halfQ q ^ 2 * coreQ (nu + 1 + 1) q at hcore
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  change (q : ℂ) ^ 2 * generalISecond nu q + (q : ℂ) * generalIFirst nu q -
    ((q : ℂ) ^ 2 + nu ^ 2) * (powerQ nu q * coreQ nu q) = 0
  dsimp only [generalISecond, generalIFirst]
  rw [hcore]
  dsimp only [halfQ]
  push_cast
  field_simp [hqC]
  <;> ring

/-- The ODE is stated with native first and second real q derivatives,
with no hODE or hDerivative supplier premise. -/
theorem generalI_modifiedBessel_equation {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * deriv (deriv (generalI nu)) q +
      (q : ℂ) * deriv (generalI nu) q -
        ((q : ℂ) ^ 2 + nu ^ 2) * generalI nu q = 0 := by
  rw [(deriv_generalI_hasDerivAt hnu hq).deriv, (generalI_hasDerivAt hnu hq).deriv]
  exact generalI_jet_equation hnu hq

/-- A normalized first derivative suitable for genuine small-q limits.
All powers and both series are the literal complex-order objects. -/
theorem generalI_normalized_first {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) * deriv (generalI nu) q =
      nu * generalICore nu (((q / 2 : ℝ) : ℂ) ^ 2) +
        2 * (((q / 2 : ℝ) : ℂ) ^ 2) * generalICore (nu + 1) (((q / 2 : ℝ) : ℂ) ^ 2) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hb : halfQ q ≠ 0 := by
    dsimp [halfQ]
    exact_mod_cast (show q / 2 ≠ 0 by positivity)
  have hp : powerQ nu q ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hb)
  rw [(generalI_hasDerivAt hnu hq).deriv]
  change (q : ℂ) * (halfQ q ^ (-nu)) * generalIFirst nu q = _
  rw [Complex.cpow_neg]
  dsimp only [generalIFirst, powerQ, coreQ, halfQ]
  push_cast
  field_simp [hqC, hp]
  <;> ring

end
end ImbalancedChen.Part3.GeneralIQODE20261025a