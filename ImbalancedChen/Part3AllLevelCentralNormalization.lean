import ImbalancedChen.Part3AllLevelContinuedMaass
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
New source only, 2026-10-26. UNCOMPILED / NOT ROOT ACCEPTED / ZERO CREDIT.

The ordinary level Eisenstein function at the central parameter cannot be
defined by substituting totalized values into division by Lambda(2s).
Instead the exact pole-removed Lambda identity constructs a holomorphic
reciprocal: A(s)/Q(s), where A=(2s)(2s-1) and Q=A Lambda_0(2s)+1.
Since Q(1/2)=1, that reciprocal has a genuine simple zero, derivative 2.
Multiplying the actual completed all-level family gives an analytic ordinary
extension. Its center is consequently zero, and its genuine derivative is
twice the completed central family. Neither conclusion is a hypothesis.

The precise open domain retains Q nonvanishing and the completed exception
s=1. No full scattering matrix or manuscript normalization is supplied.
-/

namespace ImbalancedChen.Part3.AllLevelCentralNormalization20261026a

noncomputable section

open Set Filter Topology Complex
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a

def polePolynomial (s : ℂ) : ℂ := (2 * s) * (2 * s - 1)

def reciprocalDenominator (s : ℂ) : ℂ :=
  polePolynomial s * completedRiemannZeta₀ (2 * s) + 1

/-- The analytic reciprocal, with its genuine removable central value. -/
def inverseCompletion (s : ℂ) : ℂ := polePolynomial s / reciprocalDenominator s

theorem polePolynomial_analyticAt (s : ℂ) : AnalyticAt ℂ polePolynomial s := by
  exact (analyticAt_id.const_mul (2 : ℂ)).mul
    ((analyticAt_id.const_mul (2 : ℂ)).sub_const 1)

theorem reciprocalDenominator_analyticAt (s : ℂ) :
    AnalyticAt ℂ reciprocalDenominator s := by
  have hZ : AnalyticAt ℂ (fun w : ℂ => completedRiemannZeta₀ (2 * w)) s :=
    (differentiable_completedZeta₀.analyticAt (2 * s)).comp
      (analyticAt_id.const_mul (2 : ℂ))
  exact ((polePolynomial_analyticAt s).mul hZ).add_const 1

@[simp] theorem polePolynomial_center : polePolynomial (1 / 2 : ℂ) = 0 := by
  norm_num [polePolynomial]

@[simp] theorem reciprocalDenominator_center : reciprocalDenominator (1 / 2 : ℂ) = 1 := by
  simp only [reciprocalDenominator, polePolynomial_center, zero_mul, zero_add]

@[simp] theorem inverseCompletion_center : inverseCompletion (1 / 2 : ℂ) = 0 := by
  simp only [inverseCompletion, polePolynomial_center, zero_div]

/-- Completion identity on the genuine positive-real-part domain; at the
central point both sides still have only their totalized original values. -/
theorem completionFactor_eq_completedZeta_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    completionFactor s = completedRiemannZeta (2 * s) := by
  have ht : 0 < (2 * s).re := by simp; linarith
  have ht0 : 2 * s ≠ 0 := by
    intro h
    rw [h] at ht
    simpa using ht
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos ht
  have he := (eq_div_iff hg).mp (riemannZeta_def_of_ne_zero ht0)
  have hΛ : completedRiemannZeta (2 * s) =
      (Real.pi : ℂ) ^ (-(2 * s) / 2) * Complex.Gamma ((2 * s) / 2) *
        riemannZeta (2 * s) := by
    simpa only [Complex.Gammaℝ_def, mul_comm, mul_left_comm, mul_assoc] using he.symm
  rw [hΛ, show -(2 * s) / 2 = -s by ring, show (2 * s) / 2 = s by ring]
  rfl

private theorem twice_ne_zero {s : ℂ} (hs : 0 < s.re) : 2 * s ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im,
    zero_mul, sub_zero, Complex.zero_re] at hr
  linarith

private theorem twice_sub_one_ne_zero {s : ℂ} (hs : s ≠ 1 / 2) : 2 * s - 1 ≠ 0 := by
  intro h
  apply hs
  linear_combination (1 / 2 : ℂ) * h

/-- Exact factorization of the actual completion factor away from its
central pole. The plus one records the true Lambda residue, not a supplier. -/
theorem reciprocalDenominator_eq_completion (s : ℂ) (hs : 0 < s.re)
    (hc : s ≠ 1 / 2) :
    reciprocalDenominator s = polePolynomial s * completionFactor s := by
  have h0 := twice_ne_zero hs
  have h1 := twice_sub_one_ne_zero hc
  have h1' : 1 - 2 * s ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h1))
  rw [completionFactor_eq_completedZeta_of_re_pos s hs, completedRiemannZeta_eq]
  unfold reciprocalDenominator polePolynomial
  field_simp [h0, h1']
  <;> ring

/-- A fixed open parameter neighborhood, independent of N and of the
spatial point. The finite level denominator is nonzero here by Re(s)>0. -/
def centralNormalizationDomain : Set ℂ :=
  {s | 0 < s.re ∧ s ≠ 1 ∧ reciprocalDenominator s ≠ 0}

theorem centralNormalizationDomain_isOpen : IsOpen centralNormalizationDomain := by
  have hQ : Continuous reciprocalDenominator :=
    continuous_iff_continuousAt.mpr (fun s =>
      (reciprocalDenominator_analyticAt s).continuousAt)
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun hQ continuous_const))

theorem center_mem_centralNormalizationDomain : (1 / 2 : ℂ) ∈ centralNormalizationDomain := by
  norm_num [centralNormalizationDomain]

theorem centralNormalizationDomain_mem_nhds :
    centralNormalizationDomain ∈ 𝓝 (1 / 2 : ℂ) :=
  centralNormalizationDomain_isOpen.mem_nhds center_mem_centralNormalizationDomain

theorem inverseCompletion_analyticOnNhd :
    AnalyticOnNhd ℂ inverseCompletion centralNormalizationDomain := by
  intro s hs
  exact (polePolynomial_analyticAt s).div (reciprocalDenominator_analyticAt s) hs.2.2

theorem inverseCompletion_hasDerivAt_center :
    HasDerivAt inverseCompletion 2 (1 / 2 : ℂ) := by
  have hlin : HasDerivAt (fun s : ℂ => 2 * s) 2 (1 / 2 : ℂ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (2 : ℂ)
  have hA : HasDerivAt polePolynomial 2 (1 / 2 : ℂ) := by
    convert hlin.mul (hlin.sub_const 1) using 1 <;> norm_num [polePolynomial]
  have hQ := (reciprocalDenominator_analyticAt (1 / 2 : ℂ)).differentiableAt.hasDerivAt
  simpa only [inverseCompletion, reciprocalDenominator_center, polePolynomial_center,
    mul_one, zero_mul, sub_zero, one_pow, div_one] using
      hA.div hQ (by simp)

theorem inverseCompletion_eq_actual_reciprocal (s : ℂ)
    (hs : s ∈ centralNormalizationDomain) (hc : s ≠ 1 / 2) :
    inverseCompletion s = (completionFactor s)⁻¹ := by
  have hA : polePolynomial s ≠ 0 :=
    mul_ne_zero (twice_ne_zero hs.1) (twice_sub_one_ne_zero hc)
  have he := reciprocalDenominator_eq_completion s hs.1 hc
  have hC : completionFactor s ≠ 0 := by
    intro h
    apply hs.2.2
    rw [he, h, mul_zero]
  rw [inverseCompletion, he]
  field_simp [hA, hC]

/-- The actual completion factor has residue 1/2 in the s-variable.
This is a punctured statement, so its totalized value at the pole is unused. -/
theorem completionFactor_center_residue :
    Tendsto (fun s : ℂ => (s - 1 / 2) * completionFactor s)
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (1 / 2 : ℂ)) := by
  have hQ : AnalyticAt ℂ (fun s : ℂ => reciprocalDenominator s / (4 * s)) (1 / 2 : ℂ) :=
    (reciprocalDenominator_analyticAt _).div (analyticAt_id.const_mul (4 : ℂ)) (by norm_num)
  have hlim : Tendsto (fun s : ℂ => reciprocalDenominator s / (4 * s))
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (1 / 2 : ℂ)) := by
    convert hQ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  have he : (fun s : ℂ => (s - 1 / 2) * completionFactor s)
      =ᶠ[𝓝[≠] (1 / 2 : ℂ)] (fun s => reciprocalDenominator s / (4 * s)) := by
    have hU : centralNormalizationDomain ∈ 𝓝[≠] (1 / 2 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds centralNormalizationDomain_mem_nhds
    filter_upwards [hU, self_mem_nhdsWithin] with s hs hc
    have hs0 : s ≠ 0 := by intro h; subst s; simpa using hs.1
    rw [reciprocalDenominator_eq_completion s hs.1 hc, polePolynomial]
    field_simp [hs0]
    <;> ring
  exact (tendsto_congr' he).2 hlim

theorem punctured_centralDomain_subset_physicalDomain (N : ℕ) {s : ℂ}
    (hs : s ∈ centralNormalizationDomain) (hc : s ≠ 1 / 2) :
    s ∈ physicalRegularDomain N := by
  have hs0 : s ≠ 0 := by intro h; subst s; simpa using hs.1
  have hnorm := ImbalancedChen.Part3.LevelOldformScattering20261026a.
    oldformNormalization_ne_zero_of_re_pos (canonicalPrimeList N) s hs.1
  refine ⟨⟨hs0, hs.2.1, hnorm⟩, ?_⟩
  intro h
  apply hs.2.2
  rw [reciprocalDenominator_eq_completion s hs.1 hc, h, mul_zero]

theorem initial_mem_centralNormalizationDomain (s : ℂ) (hs : 1 < s.re) :
    s ∈ centralNormalizationDomain := by
  have hspos : 0 < s.re := by linarith
  have hc : s ≠ 1 / 2 := by intro h; subst s; norm_num at hs
  refine ⟨hspos, ?_, ?_⟩
  · intro h
    subst s
    simpa using hs
  · rw [reciprocalDenominator_eq_completion s hspos hc]
    exact mul_ne_zero
      (mul_ne_zero (twice_ne_zero hspos) (twice_sub_one_ne_zero hc))
      (completionFactor_ne_zero_initial s hs)

/-- The actual ordinary analytic extension. Center is defined by the
holomorphic reciprocal zero, not by original totalized division. -/
def centralOrdinaryLevel (N : ℕ) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  inverseCompletion s * completedLevelOldform N s z

theorem centralOrdinaryLevel_analyticOnNhd (N : ℕ) (z : UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun s => centralOrdinaryLevel N s z) centralNormalizationDomain := by
  intro s hs
  have hs0 : s ≠ 0 := by intro h; subst s; simpa using hs.1
  have hnorm := ImbalancedChen.Part3.LevelOldformScattering20261026a.
    oldformNormalization_ne_zero_of_re_pos (canonicalPrimeList N) s hs.1
  exact (inverseCompletion_analyticOnNhd s hs).mul
    (completedLevelOldform_analyticOnNhd N z s ⟨hs0, hs.2.1, hnorm⟩)

theorem centralOrdinaryLevel_eq_continued (N : ℕ) (s : ℂ)
    (hs : s ∈ centralNormalizationDomain) (hc : s ≠ 1 / 2) (z : UpperHalfPlane) :
    centralOrdinaryLevel N s z = continuedLevelEisenstein N s z := by
  rw [centralOrdinaryLevel, inverseCompletion_eq_actual_reciprocal s hs hc]
  simp only [continuedLevelEisenstein, div_eq_mul_inv, mul_comm]

/-- Its equality with the actual native initial series fixes the normalization. -/
theorem centralOrdinaryLevel_eq_initial (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    centralOrdinaryLevel N s z = levelPrimitiveComplexEisenstein N s z := by
  have hc : s ≠ 1 / 2 := by intro h; subst s; norm_num at hs
  rw [centralOrdinaryLevel_eq_continued N s (initial_mem_centralNormalizationDomain s hs) hc z]
  exact continuedLevelEisenstein_eq_initial N hN s hs z

@[simp] theorem centralOrdinaryLevel_center (N : ℕ) (z : UpperHalfPlane) :
    centralOrdinaryLevel N (1 / 2) z = 0 := by
  simp only [centralOrdinaryLevel, inverseCompletion_center, zero_mul]

/-- The true first-order central object, without assuming that its value at
any spatial point is nonzero. -/
theorem centralOrdinaryLevel_hasDerivAt_center (N : ℕ) (z : UpperHalfPlane) :
    HasDerivAt (fun s => centralOrdinaryLevel N s z)
      (2 * completedLevelOldform N (1 / 2) z) (1 / 2 : ℂ) := by
  have hE := (completedLevelOldform_analyticOnNhd N z (1 / 2 : ℂ)
    (criticalStrip_subset_completedRegularDomain N (by norm_num))).differentiableAt.hasDerivAt
  simpa only [centralOrdinaryLevel, inverseCompletion_center, zero_mul, add_zero] using
    inverseCompletion_hasDerivAt_center.mul hE

theorem centralOrdinaryLevel_deriv_center (N : ℕ) (z : UpperHalfPlane) :
    deriv (fun s => centralOrdinaryLevel N s z) (1 / 2) =
      2 * completedLevelOldform N (1 / 2) z :=
  (centralOrdinaryLevel_hasDerivAt_center N z).deriv

private theorem ordinary_eventuallyEq_extension (N : ℕ) (z : UpperHalfPlane) :
    (fun s => continuedLevelEisenstein N s z) =ᶠ[𝓝[≠] (1 / 2 : ℂ)]
      (fun s => centralOrdinaryLevel N s z) := by
  have hU : centralNormalizationDomain ∈ 𝓝[≠] (1 / 2 : ℂ) :=
    mem_nhdsWithin_of_mem_nhds centralNormalizationDomain_mem_nhds
  filter_upwards [hU, self_mem_nhdsWithin] with s hs hc
  exact (centralOrdinaryLevel_eq_continued N s hs hc z).symm

/-- Genuine punctured limit of the original ordinary quotient. -/
theorem ordinary_center_limit (N : ℕ) (z : UpperHalfPlane) :
    Tendsto (fun s => continuedLevelEisenstein N s z) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 0) := by
  have h := (centralOrdinaryLevel_analyticOnNhd N z (1 / 2 : ℂ)
    center_mem_centralNormalizationDomain).continuousAt.tendsto
  have h' : Tendsto (fun s => centralOrdinaryLevel N s z)
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 0) := by
    simpa only [centralOrdinaryLevel_center] using h.mono_left nhdsWithin_le_nhds
  exact (tendsto_congr' (ordinary_eventuallyEq_extension N z)).2 h'

/-- The actual ordinary family's first nontrivial central normalization is
its first-order quotient limit, equal to twice the completed central family. -/
theorem ordinary_first_order_center_limit (N : ℕ) (z : UpperHalfPlane) :
    Tendsto (fun s => continuedLevelEisenstein N s z / (s - 1 / 2))
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (2 * completedLevelOldform N (1 / 2) z)) := by
  have h := (centralOrdinaryLevel_hasDerivAt_center N z).tendsto_slope
  have h' : Tendsto (fun s => centralOrdinaryLevel N s z / (s - 1 / 2))
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (2 * completedLevelOldform N (1 / 2) z)) := by
    simpa only [slope_def_field, centralOrdinaryLevel_center, sub_zero] using h
  have he' : (fun s => continuedLevelEisenstein N s z / (s - 1 / 2))
      =ᶠ[𝓝[≠] (1 / 2 : ℂ)] (fun s => centralOrdinaryLevel N s z / (s - 1 / 2)) := by
    filter_upwards [ordinary_eventuallyEq_extension N z] with s hs
    rw [hs]
  exact (tendsto_congr' he').2 h'

end

end ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
