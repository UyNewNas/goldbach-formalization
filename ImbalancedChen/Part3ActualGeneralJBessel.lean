import ImbalancedChen.Part3GeneralICoreDifferential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Actual general complex-order ordinary Bessel J on the positive q-axis.
The explicit alternating Gamma series converges absolutely and locally
uniformly. Its first two q derivatives and ordinary Bessel equation are
derived from the proved entire Gamma core at the negative quadratic argument.
No J differential equation or special-function identification is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace ImbalancedChen.Part3.ActualGeneralJBesselSourceOnly

open GeneralComplexISeriesSourceOnly GeneralICoreDifferential20261025a

def generalJ (nu : ℂ) (q : ℝ) : ℂ :=
  (((q / 2 : ℝ) : ℂ) ^ nu) * generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))

/-- The literal alternating Gamma-series summand, retaining its complex
order and the principal positive-real power. -/
def generalJTerm (nu : ℂ) (q : ℝ) (n : ℕ) : ℂ :=
  (((q / 2 : ℝ) : ℂ) ^ nu) *
    ((-1 : ℂ) ^ n * generalICoeff nu n * (((q / 2 : ℝ) : ℂ) ^ (2 * n)))

theorem generalJTerm_eq_core_term (nu : ℂ) (q : ℝ) (n : ℕ) :
    generalJTerm nu q n = (((q / 2 : ℝ) : ℂ) ^ nu) *
      (generalICoeff nu n * (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) ^ n) := by
  simp only [generalJTerm, neg_pow, pow_mul]
  ring

theorem generalJ_hasSum {nu : ℂ} (hnu : -1 < nu.re) (q : ℝ) :
    HasSum (generalJTerm nu q) (generalJ nu q) := by
  have heq : generalJTerm nu q = fun n => (((q / 2 : ℝ) : ℂ) ^ nu) *
      (generalICoeff nu n * (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) ^ n) :=
    funext (generalJTerm_eq_core_term nu q)
  rw [heq]
  exact (generalICore_hasSum hnu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))).mul_left _

/-- Explicit ordinary Bessel power series with the actual factorial and
Gamma denominator, rather than a label for an assumed ODE solution. -/
theorem generalJ_eq_literal_series {nu : ℂ} (hnu : -1 < nu.re) (q : ℝ) :
    generalJ nu q = ∑' n : ℕ, (((q / 2 : ℝ) : ℂ) ^ nu) *
      ((-1 : ℂ) ^ n *
        (((n.factorial : ℂ) * Complex.Gamma ((n : ℂ) + nu + 1))⁻¹) *
          (((q / 2 : ℝ) : ℂ) ^ (2 * n))) :=
  (generalJ_hasSum hnu q).tsum_eq.symm

theorem summable_norm_generalJ {nu : ℂ} (hnu : -1 < nu.re) (q : ℝ) :
    Summable (fun n => ‖generalJTerm nu q n‖) := by
  have heq : (fun n => ‖generalJTerm nu q n‖) = fun n =>
      ‖(((q / 2 : ℝ) : ℂ) ^ nu)‖ *
        ‖generalICoeff nu n * (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) ^ n‖ := by
    funext n
    rw [generalJTerm_eq_core_term, norm_mul]
  rw [heq]
  exact (summable_norm_generalICore hnu
    (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))).mul_left _

theorem generalJ_tendstoUniformlyOn_compact {nu : ℂ} (hnu : -1 < nu.re)
    {K : Set ℝ} (hK : IsCompact K) (hpos : ∀ q ∈ K, 0 < q) :
    TendstoUniformlyOn (fun N q => ∑ n ∈ Finset.range N, generalJTerm nu q n)
      (generalJ nu) atTop K := by
  have hb : Continuous (fun q : ℝ => ((q / 2 : ℝ) : ℂ)) := by fun_prop
  have hp : ContinuousOn (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ nu)) K :=
    hb.continuousOn.cpow_const (fun q hq => Or.inl (by
      simpa using (div_pos (hpos q hq) (by norm_num : (0 : ℝ) < 2))))
  have hz : Continuous (fun q : ℝ => -(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) :=
    (hb.pow 2).neg
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hp
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn hz.continuousOn
  let C := max C₀ 0
  let R := max R₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hR : 0 ≤ R := le_max_right _ _
  have hmajor := (summable_norm_generalICoeff_mul_pow hnu R hR).mul_left C
  have hu := tendstoUniformlyOn_tsum_nat hmajor
    (s := K) (f := fun n q => generalJTerm nu q n) (fun n q hq => by
      rw [generalJTerm_eq_core_term, norm_mul, norm_mul, norm_pow]
      apply mul_le_mul ((hC₀ q hq).trans (le_max_left _ _))
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _)
            ((hR₀ q hq).trans (le_max_left _ _)) n) (norm_nonneg _)
      · exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      · exact hC)
  have heq : (fun q => ∑' n, generalJTerm nu q n) = generalJ nu :=
    funext fun q => (generalJ_hasSum hnu q).tsum_eq
  rw [heq] at hu
  exact hu

private theorem shifted_order {nu : ℂ} (hnu : -1 < nu.re) :
    -1 < (nu + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  linarith

private def halfJ (q : ℝ) : ℂ := ((q / 2 : ℝ) : ℂ)
private def coreJ (nu : ℂ) (q : ℝ) : ℂ := generalICore nu (-(halfJ q ^ 2))
private def powerJ (nu : ℂ) (q : ℝ) : ℂ := halfJ q ^ nu

private theorem halfJ_hasDerivAt (q : ℝ) :
    HasDerivAt halfJ (1 / 2 : ℂ) q := by
  simpa only [halfJ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    ((hasDerivAt_id q).div_const 2).ofReal_comp

private theorem coreJ_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re) (q : ℝ) :
    HasDerivAt (coreJ nu) (-(halfJ q * coreJ (nu + 1) q)) q := by
  have hz : HasDerivAt (fun x : ℝ => -((x / 2) ^ 2)) (-(q / 2)) q := by
    convert (((hasDerivAt_id q).div_const 2).pow 2).neg using 1 <;> ring
  have h := (generalICore_hasDerivAt hnu ((-((q / 2 : ℝ) ^ 2) : ℝ) : ℂ)).comp_ofReal.scomp q hz
  simpa only [coreJ, halfJ, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.real_smul, neg_mul] using h

private theorem powerJ_hasDerivAt (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (powerJ nu) ((nu / (q : ℂ)) * powerJ nu q) q := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hhalf : 0 < q / 2 := by positivity
  have hb : halfJ q ≠ 0 := by dsimp [halfJ]; exact_mod_cast hhalf.ne'
  have hs : halfJ q ∈ Complex.slitPlane := by simp [halfJ, hhalf]
  have h := (Complex.hasStrictDerivAt_cpow_const (c := nu) hs).hasDerivAt.comp_ofReal.scomp
    q ((hasDerivAt_id q).div_const 2)
  convert h using 1
  · funext x; rfl
  · rw [Complex.cpow_sub _ _ hb, Complex.cpow_one]
    simp only [Complex.real_smul, powerJ, halfJ, Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hqC]
    <;> ring

def generalJFirst (nu : ℂ) (q : ℝ) : ℂ :=
  powerJ nu q * ((nu / (q : ℂ)) * coreJ nu q - halfJ q * coreJ (nu + 1) q)

def generalJSecond (nu : ℂ) (q : ℝ) : ℂ :=
  powerJ nu q *
    ((nu * (nu - 1) / (q : ℂ) ^ 2) * coreJ nu q -
      (nu + 1 / 2) * coreJ (nu + 1) q + halfJ q ^ 2 * coreJ (nu + 1 + 1) q)

theorem generalJ_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) : HasDerivAt (generalJ nu) (generalJFirst nu q) q := by
  have h := (powerJ_hasDerivAt nu hq).mul (coreJ_hasDerivAt hnu q)
  convert h using 1
  · funext x; rfl
  · dsimp [generalJFirst]; ring

theorem generalJFirst_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) : HasDerivAt (generalJFirst nu) (generalJSecond nu q) q := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hquot : HasDerivAt (fun x : ℝ => nu / (x : ℂ)) (-nu / (q : ℂ) ^ 2) q := by
    simpa only [Pi.div_apply, zero_mul, mul_one, zero_sub] using
      (hasDerivAt_const q nu).div (hasDerivAt_id q).ofReal_comp hqC
  have hB := (hquot.mul (coreJ_hasDerivAt hnu q)).sub
    ((halfJ_hasDerivAt q).mul (coreJ_hasDerivAt (shifted_order hnu) q))
  have h := (powerJ_hasDerivAt nu hq).mul hB
  convert h using 1
  · funext x; rfl
  · dsimp [generalJSecond, halfJ]
    push_cast
    field_simp [hqC]
    <;> ring

theorem deriv_generalJ_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (deriv (generalJ nu)) (generalJSecond nu q) q := by
  apply (generalJFirst_hasDerivAt hnu hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  exact (generalJ_hasDerivAt hnu hx).deriv

theorem generalJ_differentiableAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) : DifferentiableAt ℝ (generalJ nu) q :=
  (generalJ_hasDerivAt hnu hq).differentiableAt

theorem generalJ_deriv_differentiableAt {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) : DifferentiableAt ℝ (deriv (generalJ nu)) q :=
  (deriv_generalJ_hasDerivAt hnu hq).differentiableAt

/-- The actual contiguous core identity at the negative argument yields
the ordinary Bessel equation, with the positive q² potential sign. -/
theorem generalJ_jet_equation {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * generalJSecond nu q + (q : ℂ) * generalJFirst nu q +
      ((q : ℂ) ^ 2 - nu ^ 2) * generalJ nu q = 0 := by
  have hcore := generalICore_contiguous hnu (-(halfJ q ^ 2))
  change coreJ nu q = (nu + 1) * coreJ (nu + 1) q +
    (-(halfJ q ^ 2)) * coreJ (nu + 1 + 1) q at hcore
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  change (q : ℂ) ^ 2 * generalJSecond nu q + (q : ℂ) * generalJFirst nu q +
    ((q : ℂ) ^ 2 - nu ^ 2) * (powerJ nu q * coreJ nu q) = 0
  dsimp only [generalJSecond, generalJFirst]
  rw [hcore]
  dsimp only [halfJ]
  push_cast
  field_simp [hqC]
  <;> ring

theorem generalJ_ordinaryBessel_equation {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * deriv (deriv (generalJ nu)) q +
      (q : ℂ) * deriv (generalJ nu) q +
        ((q : ℂ) ^ 2 - nu ^ 2) * generalJ nu q = 0 := by
  rw [(deriv_generalJ_hasDerivAt hnu hq).deriv, (generalJ_hasDerivAt hnu hq).deriv]
  exact generalJ_jet_equation hnu hq

end ImbalancedChen.Part3.ActualGeneralJBesselSourceOnly
