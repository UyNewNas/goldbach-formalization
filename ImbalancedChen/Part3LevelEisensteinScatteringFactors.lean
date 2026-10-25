import ImbalancedChen.Part3CriticalEisensteinScattering
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The explicit finite level factors of the infinity-to-infinity zero-mode
entry. Each local factor has no denominator zero on Re(s)>0 and is
holomorphic there. On s=1/2+it its numerator has norm 1-1/p and its
denominator has norm at least 1-1/p. Thus each factor, and the genuine
finite prime-divisor product, has norm at most one. Every local factor is
exactly one at the central parameter, regardless of the positive level
valuation. Multiplication by the previously constructed true full-level
critical scattering extension gives central value -1, continuity there,
and the scalar-entry bound <=1 for all real t.

The arithmetic identification with the original restricted Dirichlet
series and actual Fourier coefficient is a separate subsequent caller.
For multiple cusps this is one entry; no scalar unitarity or whole matrix
unitarity is asserted.
-/

namespace ImbalancedChen.Part3.LevelEisensteinScatteringFactors20261025a

noncomputable section

open Set Complex Filter Topology Finset
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a
open ImbalancedChen.Part3.ActualComplexEisensteinCanonicalFourier

/-- The literal local zero-mode correction at p^e, with the full complex
power and the prescribed denominator. The actual prime-factor product below
uses e=v_p(N); the elementary analytic/norm facts hold for every natural e. -/
def localScatteringFactor (p e : ℕ) (s : ℂ) : ℂ :=
  ((p : ℂ) - 1) * (p : ℂ) ^ ((e : ℂ) - 1 - 2 * (e : ℂ) * s) /
    (1 - (p : ℂ) ^ (-2 * s))

/-- The finite product is indexed by the literal prime divisors of N. -/
def levelFiniteFactor (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, localScatteringFactor p (padicValNat p N) s

/-- The actual full-level Gamma/zeta scattering factor with the explicit
finite level correction; its initial arithmetic caller is supplied separately. -/
def levelScattering (N : ℕ) (s : ℂ) : ℂ :=
  complexScattering s * levelFiniteFactor N s

/-- No local denominator zero on the entire right halfplane Re(s)>0. -/
theorem localScatteringFactor_denominator_ne_zero {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) : 1 - (p : ℂ) ^ (-2 * s) ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnorm : ‖(p : ℂ) ^ (-2 * s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    apply Real.rpow_lt_one_of_one_lt_of_neg hp1
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofNat_re,
      Complex.ofNat_im, neg_zero, zero_mul, sub_zero]
    linarith
  intro h
  have hz : (p : ℂ) ^ (-2 * s) = 1 := (sub_eq_zero.mp h).symm
  simpa only [hz, norm_one, lt_self_iff_false] using hnorm

theorem localScatteringFactor_differentiableAt {p : ℕ} (hp : p.Prime)
    (e : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (localScatteringFactor p e) s := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have he : Differentiable ℂ (fun z : ℂ => (e : ℂ) - 1 - 2 * (e : ℂ) * z) := by
    fun_prop
  have hn : Differentiable ℂ
      (fun z : ℂ => ((p : ℂ) - 1) * (p : ℂ) ^ ((e : ℂ) - 1 - 2 * (e : ℂ) * z)) :=
    differentiable_const.mul (he.const_cpow (.inl hpC))
  have hd : Differentiable ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-2 * z)) := by
    exact differentiable_const.sub
      ((differentiable_id.const_mul (-2 : ℂ)).const_cpow (.inl hpC))
  exact hn.differentiableAt.div hd.differentiableAt
    (localScatteringFactor_denominator_ne_zero hp hs)

theorem levelFiniteFactor_differentiableAt (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (levelFiniteFactor N) s := by
  unfold levelFiniteFactor
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  exact localScatteringFactor_differentiableAt (Nat.prime_of_mem_primeFactors hp) _ hs

/-- Genuine holomorphy of the explicit finite factor; no analytic supplier
or denominator nonvanishing hypothesis is passed by a caller. -/
theorem levelFiniteFactor_analyticOnNhd (N : ℕ) :
    AnalyticOnNhd ℂ (levelFiniteFactor N) {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (levelFiniteFactor_differentiableAt N hs).differentiableWithinAt

/-- The exact modulus of the prime ratio on the critical line. -/
theorem critical_primeRatio_norm {p : ℕ} (hp : p.Prime) (t : ℝ) :
    ‖(p : ℂ) ^ (-2 * criticalParameter t)‖ = 1 / (p : ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  have hre : (-2 * criticalParameter t).re = -1 := by
    simp [criticalParameter, Complex.mul_re, Complex.mul_im]
  rw [hre, Real.rpow_neg_one, one_div]

/-- Every valuation has the SAME critical numerator modulus. -/
theorem localScatteringFactor_critical_numerator_norm {p : ℕ} (hp : p.Prime)
    (e : ℕ) (t : ℝ) :
    ‖((p : ℂ) - 1) *
      (p : ℂ) ^ ((e : ℂ) - 1 - 2 * (e : ℂ) * criticalParameter t)‖ =
        1 - 1 / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hnorm : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
  have hre : ((e : ℂ) - 1 - 2 * (e : ℂ) * criticalParameter t).re = -1 := by
    simp only [criticalParameter, Complex.sub_re, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.natCast_re, Complex.natCast_im, Complex.ofNat_re,
      Complex.ofNat_im, Complex.one_re, Complex.one_im, Complex.div_re,
      Complex.div_im]
    norm_num
    ring
  rw [norm_mul, hnorm, Complex.norm_natCast_cpow_of_pos hp.pos, hre, Real.rpow_neg_one]
  field_simp [ne_of_gt hpR]
  ring

/-- A sharp elementary scalar bound: at criticality the denominator norm
is at least the exact numerator norm, by the reverse triangle inequality. -/
theorem localScatteringFactor_critical_norm_le_one {p : ℕ} (hp : p.Prime)
    (e : ℕ) (t : ℝ) : ‖localScatteringFactor p e (criticalParameter t)‖ ≤ 1 := by
  have hden : 1 - (p : ℂ) ^ (-2 * criticalParameter t) ≠ 0 :=
    localScatteringFactor_denominator_ne_zero hp (by rw [criticalParameter_re]; norm_num)
  have hbound : 1 - 1 / (p : ℝ) ≤ ‖1 - (p : ℂ) ^ (-2 * criticalParameter t)‖ := by
    simpa only [norm_one, critical_primeRatio_norm hp t] using
      norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-2 * criticalParameter t))
  rw [localScatteringFactor, norm_div, localScatteringFactor_critical_numerator_norm hp e t]
  exact (div_le_one (norm_pos_iff.mpr hden)).mpr hbound

/-- Exact central normalization of EVERY prime-power level factor. -/
theorem localScatteringFactor_half {p : ℕ} (hp : p.Prime) (e : ℕ) :
    localScatteringFactor p e (1 / 2) = 1 := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hden : 1 - (p : ℂ) ^ (-2 * (1 / 2 : ℂ)) ≠ 0 :=
    localScatteringFactor_denominator_ne_zero hp (by norm_num)
  unfold localScatteringFactor
  have he : (e : ℂ) - 1 - 2 * (e : ℂ) * (1 / 2) = -1 := by ring
  rw [he]
  apply (div_eq_one_iff_eq hden).mpr
  rw [show (-2 : ℂ) * (1 / 2) = -1 by norm_num, Complex.cpow_neg_one,
    Complex.cpow_neg_one]
  field_simp [hpC]
  ring

/-- The full finite product has central value one, including the empty
level-one product. The actual identification requires positive N later. -/
theorem levelFiniteFactor_half (N : ℕ) : levelFiniteFactor N (1 / 2) = 1 := by
  unfold levelFiniteFactor
  apply Finset.prod_eq_one
  intro p hp
  exact localScatteringFactor_half (Nat.prime_of_mem_primeFactors hp) _

/-- This finite level factor is a contraction on the critical line. -/
theorem levelFiniteFactor_critical_norm_le_one (N : ℕ) (t : ℝ) :
    ‖levelFiniteFactor N (criticalParameter t)‖ ≤ 1 := by
  rw [levelFiniteFactor, Complex.norm_prod]
  apply Finset.prod_le_one (fun p _hp => norm_nonneg _)
  intro p hp
  exact localScatteringFactor_critical_norm_le_one
    (Nat.prime_of_mem_primeFactors hp) _ t

/-- The infinity-to-infinity critical entry with its TRUE full-level
central scattering value, multiplied by the actual finite level factor. -/
def levelCriticalScattering (N : ℕ) (t : ℝ) : ℂ :=
  criticalScattering t * levelFiniteFactor N (criticalParameter t)

@[simp] theorem levelCriticalScattering_zero (N : ℕ) : levelCriticalScattering N 0 = -1 := by
  rw [levelCriticalScattering, criticalScattering_zero]
  simp only [criticalParameter, Complex.ofReal_zero, zero_mul, add_zero,
    levelFiniteFactor_half, mul_one]

theorem levelCriticalScattering_of_ne_zero (N : ℕ) (t : ℝ) (ht : t ≠ 0) :
    levelCriticalScattering N t = levelScattering N (criticalParameter t) := by
  rw [levelCriticalScattering, criticalScattering_of_ne_zero t ht]
  rfl

/-- True central continuity is inherited from the residue-based scalar
extension and actual holomorphy of the finite local product. -/
theorem levelCriticalScattering_continuousAt_zero (N : ℕ) :
    ContinuousAt (levelCriticalScattering N) 0 := by
  have hc : Continuous criticalParameter := by unfold criticalParameter; fun_prop
  have hF : ContinuousAt (fun t : ℝ => levelFiniteFactor N (criticalParameter t)) 0 :=
    (levelFiniteFactor_differentiableAt N
      (by rw [criticalParameter_re]; norm_num)).continuousAt.comp 0 hc.continuousAt
  exact criticalScattering_continuousAt_zero.mul hF

/-- One scalar matrix ENTRY is bounded by one. For levels with several
cusps this is deliberately not a scalar or matrix unitarity assertion. -/
theorem levelCriticalScattering_norm_le_one (N : ℕ) (t : ℝ) :
    ‖levelCriticalScattering N t‖ ≤ 1 := by
  rw [levelCriticalScattering, norm_mul, criticalScattering_norm, one_mul]
  exact levelFiniteFactor_critical_norm_le_one N t

end
end ImbalancedChen.Part3.LevelEisensteinScatteringFactors20261025a


