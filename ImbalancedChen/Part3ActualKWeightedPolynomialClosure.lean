import ImbalancedChen.Part3EvenFourierHilbert
import ImbalancedChen.Part3ActualKComplexLaplaceConsequences
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Module.Basic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
Weighted Stone-Weierstrass approximation by actual positive-integer
exponential-cosh profiles. The weight makes uniform approximation valid
in full-axis L2 despite the infinite Lebesgue mass. This module does not
assert totality: the remaining continuous-even test-function density and
coordinate factorization are recorded separately in its checkpoint.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualKWeightedPolynomialClosureSourceOnly

open Set MeasureTheory
open scoped BigOperators
open KFullLineFourierBridgeSourceOnly P3ActualKProfileLpSourceOnly
open HalfCosinePlancherelSourceOnly EvenFourierHilbertSourceOnly
open ActualKComplexLaplaceConsequences20261024z

def coshCoordinate (u : ℝ) : ℝ := Real.exp (-Real.cosh u)

theorem coshCoordinate_continuous : Continuous coshCoordinate := by
  unfold coshCoordinate
  fun_prop

theorem coshCoordinate_pos (u : ℝ) : 0 < coshCoordinate u := Real.exp_pos _

theorem coshCoordinate_mem (u : ℝ) : coshCoordinate u ∈ Icc 0 (Real.exp (-1)) := by
  refine ⟨le_of_lt (coshCoordinate_pos u), ?_⟩
  exact Real.exp_le_exp.mpr (neg_le_neg (Real.one_le_cosh u))

theorem kEvenProfile_one (u : ℝ) : kEvenProfile 1 u = (coshCoordinate u : ℂ) := by
  simp [kEvenProfile, evenLaplaceProfile, coshCoordinate]

def integerProfile (n : ℕ) : ComplexL2 :=
  (evenKProfile ((n : ℝ) + 1) (by positivity) : ComplexL2)

theorem integerProfile_coe_ae (n : ℕ) :
    (integerProfile n : ℝ → ℂ) =ᵐ[volume]
      fun u => (coshCoordinate u : ℂ) ^ (n + 1) := by
  filter_upwards [(kEvenProfile_memLp_two (q := (n : ℝ) + 1) (by positivity)).coeFn_toLp]
    with u hu
  change ((kEvenProfile_memLp_two (q := (n : ℝ) + 1) (by positivity)).toLp _ u) = _
  rw [hu]
  change (Real.exp (-((n : ℝ) + 1) * Real.cosh u) : ℂ) = _
  have he : Real.exp (-((n : ℝ) + 1) * Real.cosh u) =
      (coshCoordinate u) ^ (n + 1) := by
    rw [coshCoordinate, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he, Complex.ofReal_pow]

def integerProfileSpan : Submodule ℂ ComplexL2 :=
  Submodule.span ℂ (Set.range integerProfile)

def weightedProfile (φ : ℝ → ℂ) (u : ℝ) : ℂ :=
  (coshCoordinate u : ℂ) * φ (coshCoordinate u)

theorem weightedProfile_continuous {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Icc 0 (Real.exp (-1)))) : Continuous (weightedProfile φ) := by
  exact (Complex.continuous_ofReal.comp coshCoordinate_continuous).mul
    (hφ.comp_continuous coshCoordinate_continuous coshCoordinate_mem)

theorem weightedProfile_memLp {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Icc 0 (Real.exp (-1)))) : MemLp (weightedProfile φ) 2 volume := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans
    (hM 0 ⟨le_rfl, le_of_lt (Real.exp_pos _)⟩)
  apply ((kEvenProfile_memLp_two (q := 1) (by norm_num)).const_mul (M : ℂ)).of_le
    (weightedProfile_continuous hφ).aestronglyMeasurable
  filter_upwards [] with u
  change ‖(coshCoordinate u : ℂ) * φ (coshCoordinate u)‖ ≤
    ‖(M : ℂ) * kEvenProfile 1 u‖
  rw [norm_mul, norm_mul, kEvenProfile_one]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0,
    abs_of_pos (coshCoordinate_pos u)]
  have hb := mul_le_mul_of_nonneg_left (hM _ (coshCoordinate_mem u))
    (le_of_lt (coshCoordinate_pos u))
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (coshCoordinate_pos u), mul_comm]
    using hb

def weightedProfileL2 (φ : ℝ → ℂ)
    (hφ : ContinuousOn φ (Icc 0 (Real.exp (-1)))) : ComplexL2 :=
  (weightedProfile_memLp hφ).toLp (weightedProfile φ)

def polynomialProfileL2 (p : ℂ[X]) : ComplexL2 :=
  ∑ n ∈ p.support, p.coeff n • integerProfile n

theorem polynomialProfileL2_mem (p : ℂ[X]) : polynomialProfileL2 p ∈ integerProfileSpan := by
  classical
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self n)

theorem polynomialProfileL2_coe_ae (p : ℂ[X]) :
    (polynomialProfileL2 p : ℝ → ℂ) =ᵐ[volume]
      fun u => (coshCoordinate u : ℂ) * p.eval (coshCoordinate u : ℂ) := by
  classical
  have hterm (n : ℕ) :
      ((p.coeff n • integerProfile n : ComplexL2) : ℝ → ℂ) =ᵐ[volume]
        fun u => p.coeff n * (coshCoordinate u : ℂ) ^ (n + 1) := by
    filter_upwards [Lp.coeFn_smul (p.coeff n) (integerProfile n), integerProfile_coe_ae n]
      with u hu hv
    simpa only [Pi.smul_apply, smul_eq_mul, hv] using hu
  filter_upwards [Lp.coeFn_fun_finsetSum p.support (fun n => p.coeff n • integerProfile n),
    ae_all_iff.2 hterm] with u hsum hall
  change (∑ n ∈ p.support, p.coeff n • integerProfile n : ComplexL2) u = _
  rw [hsum, Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hall n, pow_succ]
  ring

/-- Uniform error in the compact coordinate is converted to an actual
full-axis L2 error with the fixed integrable weight exp(-cosh u). -/
theorem weighted_polynomial_error {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Icc 0 (Real.exp (-1))))
    (p : ℂ[X]) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp : ∀ x ∈ Icc 0 (Real.exp (-1)), ‖p.eval (x : ℂ) - φ x‖ ≤ δ) :
    ‖polynomialProfileL2 p - weightedProfileL2 φ hφ‖ ≤ δ * ‖integerProfile 0‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (polynomialProfileL2 p) (weightedProfileL2 φ hφ),
    polynomialProfileL2_coe_ae p, (weightedProfile_memLp hφ).coeFn_toLp,
    integerProfile_coe_ae 0] with u hsub hpv hφv hbase
  rw [hsub, hpv, hφv, hbase]
  change ‖(coshCoordinate u : ℂ) * p.eval (coshCoordinate u : ℂ) -
    (coshCoordinate u : ℂ) * φ (coshCoordinate u)‖ ≤ _
  rw [← mul_sub, norm_mul]
  simp only [zero_add, pow_one]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (hp _ (coshCoordinate_mem u)) (norm_nonneg (coshCoordinate u : ℂ))

/-- An actual finite combination of positive-integer profiles approximates
every weighted continuous coordinate test in the genuine L2 norm. -/
theorem exists_polynomialProfileL2_near {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Icc 0 (Real.exp (-1)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ‖polynomialProfileL2 p - weightedProfileL2 φ hφ‖ < ε := by
  let δ : ℝ := ε / (‖integerProfile 0‖ + 1)
  have hd : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_complex_polynomial_near_of_continuousOn
    0 (Real.exp (-1)) φ hφ δ hd
  refine ⟨p, (weighted_polynomial_error hφ p (le_of_lt hd)
    (fun x hx => le_of_lt (hp x hx))).trans_lt ?_⟩
  have hden : 0 < ‖integerProfile 0‖ + 1 := by positivity
  have heq : δ * (‖integerProfile 0‖ + 1) = ε := by
    exact div_mul_cancel₀ ε (ne_of_gt hden)
  nlinarith

/-- The weighted continuous coordinate test lies in the closed span of
the actual profiles with parameters 1,2,3,... . -/
theorem weightedProfileL2_mem_closure {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Icc 0 (Real.exp (-1)))) :
    weightedProfileL2 φ hφ ∈ integerProfileSpan.topologicalClosure := by
  change weightedProfileL2 φ hφ ∈ closure (integerProfileSpan : Set ComplexL2)
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomialProfileL2_near hφ hε
  refine ⟨polynomialProfileL2 p, polynomialProfileL2_mem p, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hp

end ImbalancedChen.Part3.ActualKWeightedPolynomialClosureSourceOnly
