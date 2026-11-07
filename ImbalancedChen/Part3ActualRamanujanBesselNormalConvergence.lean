import ImbalancedChen.Part3ActualRamanujanDirichletSeries
import ImbalancedChen.Part3ComplexOrderKUniformStripDecay
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Normal convergence and entire spectral-parameter dependence of the literal
nonzero Fourier-Bessel kernel, before its meromorphic Gamma/zeta prefactor.
Every positive frequency is indexed once by n+1. The divisor factor is the
actual finite sigma_(1-2s) from the proved Ramanujan Dirichlet identity.
The K factor is the actual positive-axis integral, with its proved order
entireness and uniform strip exponential decay.

SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED. No numerical replay.
-/

namespace ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

noncomputable section

open Set Filter
open scoped Topology BigOperators
open Part3ActualRamanujanDirichletSeries
open Part3.ComplexOrderKBridgeSourceOnly Part3.ComplexOrderKEntire20261025a
open Part3.ComplexOrderKUniformStripDecay20261025a

/-- The literal positive-frequency horizontal Fourier phase. -/
def phase (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)

theorem norm_phase (n : ℕ) (x : ℝ) : ‖phase n x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

/-- The actual Fourier-Bessel term, without the Gamma/zeta prefactor. -/
def fourierBesselTerm (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) ^ (s - 1 / 2) * divisorFactor (n + 1) (2 * s) *
    complexOrderK (s - 1 / 2) (2 * Real.pi * (n + 1 : ℕ) * y) * phase (n + 1) x

/-- The finite divisor carrier gives a polynomial bound selected before s.
There is no divisor-count or Dirichlet-series estimate among the inputs. -/
theorem divisorFactor_polynomial_bound {N : ℕ} (hN : 0 < N)
    (M : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) :
    ‖divisorFactor N (2 * s)‖ ≤ (N : ℝ) ^ (2 * M + 2) := by
  have hpoint : ∀ d ∈ N.divisors,
      ‖(d : ℂ) ^ (1 - 2 * s)‖ ≤ (N : ℝ) ^ (2 * M + 1) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hdN : (d : ℝ) ≤ N := by
      exact_mod_cast Nat.le_of_dvd hN (Nat.dvd_of_mem_divisors hd)
    have he : (1 - 2 * s).re ≤ ((2 * M + 1 : ℕ) : ℝ) := by
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
        Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
      have hlow := (abs_le.mp hs).1
      push_cast
      linarith
    rw [Complex.norm_natCast_cpow_of_pos hdpos]
    calc
      _ ≤ (d : ℝ) ^ (((2 * M + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hd1 he
      _ = (d : ℝ) ^ (2 * M + 1) := Real.rpow_natCast _ _
      _ ≤ (N : ℝ) ^ (2 * M + 1) := by gcongr
  unfold divisorFactor
  calc
    _ ≤ ∑ d ∈ N.divisors, ‖(d : ℂ) ^ (1 - 2 * s)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ N.divisors, (N : ℝ) ^ (2 * M + 1) :=
      Finset.sum_le_sum hpoint
    _ = (N.divisors.card : ℝ) * (N : ℝ) ^ (2 * M + 1) := by simp
    _ ≤ (N : ℝ) * (N : ℝ) ^ (2 * M + 1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self N)
        (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (N : ℝ) ^ (2 * M + 2) := by
      rw [show 2 * M + 2 = (2 * M + 1) + 1 by omega, pow_succ']

theorem power_prefactor_bound {N : ℕ} (hN : 0 < N) (M : ℕ)
    {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) :
    ‖(N : ℂ) ^ (s - 1 / 2)‖ ≤ (N : ℝ) ^ M := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he : (s - 1 / 2).re ≤ (M : ℝ) := by
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofNat_re, Complex.ofNat_im]
    have h := (abs_le.mp hs).2
    norm_num
    linarith
  rw [Complex.norm_natCast_cpow_of_pos hN]
  exact (Real.rpow_le_rpow_of_exponent_le hN1 he).trans_eq (Real.rpow_natCast _ _)

/-- This positive constant is fixed before frequency, height, phase or s. -/
def decayConstant (M : ℕ) (a : ℝ) : ℝ :=
  stripDecayConstant 0 (2 * Real.pi * a) ((M : ℝ) + 1)

def majorant (M : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  decayConstant M a * ((n + 1 : ℕ) : ℝ) ^ (3 * M + 2) *
    Real.exp (-(Real.pi * a) * ((n + 1 : ℕ) : ℝ))

/-- Polynomial growth of actual divisor coefficients is absorbed by the
actual K exponential decay, uniformly in all horizontal x and y>=a. -/
theorem fourierBesselTerm_norm_bound (M : ℕ) {a : ℝ} (ha : 0 < a)
    (n : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ))
    {y : ℝ} (hy : a ≤ y) (x : ℝ) :
    ‖fourierBesselTerm n s y x‖ ≤ majorant M a n := by
  let N : ℕ := n + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hypos : 0 < y := ha.trans_le hy
  have hq0 : 0 < 2 * Real.pi * a := by positivity
  have hq : 2 * Real.pi * a ≤ 2 * Real.pi * (N : ℝ) * y := by
    have hNy : a ≤ (N : ℝ) * y :=
      hy.trans (le_mul_of_one_le_left hypos.le hN1)
    nlinarith [mul_le_mul_of_nonneg_left hNy (by positivity : 0 ≤ 2 * Real.pi)]
  have hnu : |(s - 1 / 2).re| ≤ (M : ℝ) + 1 := by
    have h := abs_sub_le s.re (1 / 2 : ℝ)
    norm_num at h
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hK := complexOrderK_uniform_exp_bound hq0 hq hnu
  have hexp : Real.exp (-(2 * Real.pi * (N : ℝ) * y / 2)) ≤
      Real.exp (-(Real.pi * a) * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ Real.pi * (N : ℝ))
    nlinarith
  have hK' : ‖complexOrderK (s - 1 / 2) (2 * Real.pi * (N : ℝ) * y)‖ ≤
      decayConstant M a * Real.exp (-(Real.pi * a) * (N : ℝ)) :=
    hK.trans (mul_le_mul_of_nonneg_left hexp (stripDecayConstant_pos _ _ _).le)
  have hc : ‖(N : ℂ) ^ (s - 1 / 2) * divisorFactor N (2 * s)‖ ≤
      (N : ℝ) ^ (3 * M + 2) := by
    rw [norm_mul]
    calc
      _ ≤ (N : ℝ) ^ M * (N : ℝ) ^ (2 * M + 2) :=
        mul_le_mul (power_prefactor_bound hN M hs) (divisorFactor_polynomial_bound hN M hs)
          (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  unfold fourierBesselTerm
  rw [norm_mul, norm_mul, norm_phase, mul_one]
  have h := mul_le_mul hc hK' (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  simpa only [majorant, N, mul_assoc, mul_left_comm, mul_comm] using h

/-- An explicit summable exponential-polynomial majorant, with no
normal-convergence assumption. -/
theorem majorant_summable (M : ℕ) {a : ℝ} (ha : 0 < a) : Summable (majorant M a) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul (3 * M + 2)
    (mul_pos Real.pi_pos ha)
  have hshift := (summable_nat_add_iff 1).mpr h
  simpa only [majorant, mul_assoc] using hshift.const_mul (decayConstant M a)

/-- Uniform convergence on an entire closed real-part strip, all heights
above a and all horizontal real x. Imaginary order is unrestricted. -/
theorem uniform_convergence_strip (M : ℕ) {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun H : ℕ => fun p : ℂ × ℝ × ℝ =>
        ∑ n ∈ Finset.range H, fourierBesselTerm n p.1 p.2.1 p.2.2)
      (fun p : ℂ × ℝ × ℝ => ∑' n, fourierBesselTerm n p.1 p.2.1 p.2.2)
      atTop {p | |p.1.re| ≤ (M : ℝ) ∧ a ≤ p.2.1} := by
  exact tendstoUniformlyOn_tsum_nat (majorant_summable M ha)
    (fun n p hp => fourierBesselTerm_norm_bound M ha n hp.1 hp.2 p.2.2)

/-- Every compact complex s-domain is contained in one proved strip. -/
theorem uniform_convergence_compact {K : Set ℂ} (hK : IsCompact K)
    {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun H : ℕ => fun p : ℂ × ℝ × ℝ =>
        ∑ n ∈ Finset.range H, fourierBesselTerm n p.1 p.2.1 p.2.2)
      (fun p : ℂ × ℝ × ℝ => ∑' n, fourierBesselTerm n p.1 p.2.1 p.2.2)
      atTop {p | p.1 ∈ K ∧ a ≤ p.2.1} := by
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  let M : ℕ := Nat.ceil B
  have hs : ∀ s ∈ K, |s.re| ≤ (M : ℝ) := by
    intro s hs
    exact (Complex.abs_re_le_norm s).trans ((hB s hs).trans (Nat.le_ceil B))
  exact tendstoUniformlyOn_tsum_nat (majorant_summable M ha)
    (fun n p hp => fourierBesselTerm_norm_bound M ha n (hs p.1 hp.1) hp.2 p.2.2)

/-- Actual absolute convergence at every complex parameter and positive y. -/
theorem fourierBessel_norm_summable (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖fourierBesselTerm n s y x‖) := by
  let M : ℕ := Nat.ceil |s.re|
  have hs : |s.re| ≤ (M : ℝ) := Nat.le_ceil _
  exact (majorant_summable M hy).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => fourierBesselTerm_norm_bound M hy n hs le_rfl x)

/-- Each actual term is entire in s: finite powers and divisor sums are
entire, and the K integral is entire in its complex order. -/
theorem fourierBesselTerm_differentiable (n : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => fourierBesselTerm n s y x) := by
  have hN : (n + 1 : ℕ) ≠ 0 := by omega
  have hNC : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hp : Differentiable ℂ (fun s : ℂ => ((n + 1 : ℕ) : ℂ) ^ (s - 1 / 2)) :=
    (differentiable_id.sub_const _).const_cpow (.inl hNC)
  have hd : Differentiable ℂ (fun s : ℂ => divisorFactor (n + 1) (2 * s)) := by
    unfold divisorFactor
    apply Differentiable.fun_sum
    intro d hd
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
    exact (differentiable_const.sub (differentiable_id.const_mul (2 : ℂ))).const_cpow (.inl hdC)
  have hq : 0 < 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y := by positivity
  have hK : Differentiable ℂ
      (fun s : ℂ => complexOrderK (s - 1 / 2) (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y)) :=
    (complexOrderK_differentiable_all hq).comp (differentiable_id.sub_const _)
  exact ((hp.mul hd).mul hK).mul (differentiable_const _)

/-- The sum is entire before the meromorphic Gamma/zeta factor is added. -/
theorem fourierBessel_sum_differentiable {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => ∑' n, fourierBesselTerm n s y x) := by
  intro s
  let M : ℕ := Nat.ceil |s.re| + 1
  let U : Set ℂ := {z | |z.re| < (M : ℝ)}
  have hs : s ∈ U := by
    have h := Nat.le_ceil |s.re|
    dsimp [U, M]
    push_cast
    linarith
  have hU : IsOpen U :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => ∑' n, fourierBesselTerm n z y x) U := by
    apply differentiableOn_tsum_of_summable_norm (majorant_summable M hy)
      (fun n => (fourierBesselTerm_differentiable n hy x).differentiableOn) hU
    intro n z hz
    exact fourierBesselTerm_norm_bound M hy n hz.le le_rfl x
  exact (hdiff s hs).differentiableAt (hU.mem_nhds hs)

/-- Both nonzero Fourier signs, each appearing exactly once. The radial
coefficient depends on abs(n), while the two horizontal phases are opposite. -/
def nonzeroFrequencyPair (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  fourierBesselTerm n s y x + fourierBesselTerm n s y (-x)

theorem nonzeroFrequencyPair_norm_bound (M : ℕ) {a : ℝ} (ha : 0 < a)
    (n : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ))
    {y : ℝ} (hy : a ≤ y) (x : ℝ) :
    ‖nonzeroFrequencyPair n s y x‖ ≤ 2 * majorant M a n := by
  unfold nonzeroFrequencyPair
  exact (norm_add_le _ _).trans (by
    have hp := fourierBesselTerm_norm_bound M ha n hs hy x
    have hn := fourierBesselTerm_norm_bound M ha n hs hy (-x)
    linarith)

theorem nonzeroFrequencyPair_uniform_compact {K : Set ℂ} (hK : IsCompact K)
    {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun H : ℕ => fun p : ℂ × ℝ × ℝ =>
        ∑ n ∈ Finset.range H, nonzeroFrequencyPair n p.1 p.2.1 p.2.2)
      (fun p : ℂ × ℝ × ℝ => ∑' n, nonzeroFrequencyPair n p.1 p.2.1 p.2.2)
      atTop {p | p.1 ∈ K ∧ a ≤ p.2.1} := by
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  let M : ℕ := Nat.ceil B
  have hs : ∀ s ∈ K, |s.re| ≤ (M : ℝ) := by
    intro s hs
    exact (Complex.abs_re_le_norm s).trans ((hB s hs).trans (Nat.le_ceil B))
  exact tendstoUniformlyOn_tsum_nat ((majorant_summable M ha).const_mul 2)
    (fun n p hp => nonzeroFrequencyPair_norm_bound M ha n (hs p.1 hp.1) hp.2 p.2.2)

theorem nonzeroFrequencyPair_norm_summable (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖nonzeroFrequencyPair n s y x‖) := by
  let M : ℕ := Nat.ceil |s.re|
  have hs : |s.re| ≤ (M : ℝ) := Nat.le_ceil _
  exact ((majorant_summable M hy).const_mul 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => nonzeroFrequencyPair_norm_bound M hy n hs le_rfl x)

/-- The entire bilateral nonzero Fourier kernel, prior to the common
meromorphic Gamma/zeta factor. -/
theorem nonzeroFrequencyPair_sum_differentiable {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => ∑' n, nonzeroFrequencyPair n s y x) := by
  have heq : (fun s : ℂ => ∑' n, nonzeroFrequencyPair n s y x) =
      (fun s : ℂ => (∑' n, fourierBesselTerm n s y x) +
        ∑' n, fourierBesselTerm n s y (-x)) := by
    funext s
    exact tsum_add (fourierBessel_norm_summable s hy x).of_norm
      (fourierBessel_norm_summable s hy (-x)).of_norm
  rw [heq]
  exact (fourierBessel_sum_differentiable hy x).add
    (fourierBessel_sum_differentiable hy (-x))
end

end ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

