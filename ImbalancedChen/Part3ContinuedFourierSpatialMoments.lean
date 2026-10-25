import ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
import ImbalancedChen.Part3ComplexOrderKQCalculus
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

Actual spatial derivative moments for the continued Fourier-Bessel kernel,
at arbitrary complex parameter. q derivatives require cosh(u)^k moments;
these differ from order derivatives, whose moments are powers of u. We prove
a new exponential bound uniform in all q>=q0 and |Re nu|<=R for the literal
qMoment k integral, using the actual tilted-cosh density at q0/2.

The spectral coefficient is exactly the one in fourierBesselTerm. Its
spatial moments have genuine x/y derivative recurrences and an explicit
summable exponential-polynomial majorant uniform on all y>=a>0 and bounded
real-part parameter strips. No spatial derivative or uniform bound of an
infinite series is an assumption, and no held coordinate-series module is
imported. The sqrt(y)-weighted completed expression is separate work.
-/

namespace ImbalancedChen.Part3.ContinuedFourierSpatialMoments

noncomputable section

open Set MeasureTheory Filter
open scoped Topology
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
open ImbalancedChen.Part3.ComplexOrderKQCalculus
open ImbalancedChen.Part3.RealOrderKPositiveLaplace

/-- This finite constant is selected before order and argument. -/
def qMomentDecayConstant (k : ℕ) (q0 R : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), tiltedCoshDensity ((k : ℝ) + R) (q0 / 2) u

theorem qMomentDecayConstant_nonneg (k : ℕ) (q0 R : ℝ) :
    0 ≤ qMomentDecayConstant k q0 R := by
  apply integral_nonneg
  intro u
  exact Real.exp_nonneg _

theorem qMoment_uniform_integrand_bound (k : ℕ)
    {q0 q R u : ℝ} {nu : ℂ} (hq0 : 0 < q0) (hq : q0 ≤ q)
    (hnu : |nu.re| ≤ R) (hu : 0 ≤ u) :
    ‖qMomentIntegrand k nu q u‖ ≤
      Real.exp (-(q / 2)) * tiltedCoshDensity ((k : ℝ) + R) (q0 / 2) u := by
  have hqpos : 0 < q := hq0.trans_le hq
  have hspl : qMomentIntegrand k nu q u =
      (Real.exp (-(q / 2) * Real.cosh u) : ℂ) * qMomentIntegrand k nu (q / 2) u := by
    unfold qMomentIntegrand
    rw [show -q * Real.cosh u = -(q / 2) * Real.cosh u +
      -(q / 2) * Real.cosh u by ring, Real.exp_add, Complex.ofReal_mul]
    ring
  have he : Real.exp (-(q / 2) * Real.cosh u) ≤ Real.exp (-(q / 2)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (Real.one_le_cosh u)
      (show 0 ≤ q / 2 by positivity)
    nlinarith
  have hm := qMomentIntegrand_norm_le k nu
    (show q0 / 2 ≤ q / 2 by linarith) hu
  have henv : tiltedCoshDensity ((k : ℝ) + |nu.re|) (q0 / 2) u ≤
      tiltedCoshDensity ((k : ℝ) + R) (q0 / 2) u := by
    unfold tiltedCoshDensity
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hnu hu
    nlinarith
  rw [hspl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul he (hm.trans henv) (norm_nonneg _) (Real.exp_pos _).le

/-- Uniform exponential decay of every actual q derivative moment. -/
theorem qMoment_uniform_exp_bound (k : ℕ) {q0 q R : ℝ} {nu : ℂ}
    (hq0 : 0 < q0) (hq : q0 ≤ q) (hnu : |nu.re| ≤ R) :
    ‖qMoment k nu q‖ ≤ qMomentDecayConstant k q0 R * Real.exp (-(q / 2)) := by
  have hb : IntegrableOn
      (fun u : ℝ => Real.exp (-(q / 2)) *
        tiltedCoshDensity ((k : ℝ) + R) (q0 / 2) u) (Ioi 0) :=
    (tiltedCoshDensity_integrable ((k : ℝ) + R) (half_pos hq0)).integrableOn.const_mul _
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ‖qMomentIntegrand k nu q u‖ ≤ Real.exp (-(q / 2)) *
        tiltedCoshDensity ((k : ℝ) + R) (q0 / 2) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact qMoment_uniform_integrand_bound k hq0 hq hnu hu.le
  have h := norm_integral_le_of_norm_le hb hbound
  rw [integral_const_mul] at h
  simpa only [qMoment, qMomentDecayConstant, mul_comm] using h

def frequency (N : ℕ) : ℝ := 2 * Real.pi * (N : ℝ)

def spectralCoefficient (n : ℕ) (s : ℂ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) ^ (s - 1 / 2) * divisorFactor (n + 1) (2 * s)

/-- j horizontal derivatives and k radial K derivatives of the actual
positive-frequency kernel, before the common sqrt(y) weight. -/
def spatialMomentTerm (j k n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  spectralCoefficient n s * (Complex.I * (frequency (n + 1) : ℂ)) ^ j *
    (frequency (n + 1) : ℂ) ^ k *
      qMoment k (s - 1 / 2) (frequency (n + 1) * y) * phase (n + 1) x

theorem spatialMomentTerm_zero_zero (n : ℕ) (s : ℂ) (y x : ℝ) :
    spatialMomentTerm 0 0 n s y x = fourierBesselTerm n s y x := by
  simp only [spatialMomentTerm, spectralCoefficient, pow_zero, mul_one, qMoment_zero,
    fourierBesselTerm, frequency]

theorem phase_hasDerivAt (N : ℕ) (x : ℝ) :
    HasDerivAt (phase N) ((Complex.I * (frequency N : ℂ)) * phase N x) x := by
  have heq : phase N = (fun t : ℝ =>
      Complex.exp ((frequency N : ℂ) * Complex.I * (t : ℂ))) := by
    funext t
    unfold phase frequency
    congr 1
    push_cast
    ring
  have h := (Complex.hasDerivAt_exp ((frequency N : ℂ) * Complex.I * (x : ℂ))).comp
    (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_mul ((frequency N : ℂ) * Complex.I))
  rw [heq]
  convert h.comp_ofReal using 1 <;> ring

/-- Genuine horizontal derivative recurrence for the literal moment family. -/
theorem spatialMomentTerm_hasDerivAt_x (j k n : ℕ) (s : ℂ) (y x : ℝ) :
    HasDerivAt (fun t : ℝ => spatialMomentTerm j k n s y t)
      (spatialMomentTerm (j + 1) k n s y x) x := by
  have h := (phase_hasDerivAt (n + 1) x).const_mul
    (spectralCoefficient n s * (Complex.I * (frequency (n + 1) : ℂ)) ^ j *
      (frequency (n + 1) : ℂ) ^ k *
        qMoment k (s - 1 / 2) (frequency (n + 1) * y))
  convert h using 1 <;> simp [spatialMomentTerm, pow_succ] <;> ring

/-- Genuine vertical derivative recurrence, using the actual qMoment derivative. -/
theorem spatialMomentTerm_hasDerivAt_y (j k n : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => spatialMomentTerm j k n s t x)
      (spatialMomentTerm j (k + 1) n s y x) y := by
  have hw : 0 < frequency (n + 1) := by unfold frequency; positivity
  have h := (qMoment_hasDerivAt k (s - 1 / 2) (mul_pos hw hy)).comp y
    ((hasDerivAt_id y).const_mul (frequency (n + 1)))
  have hc := (h.const_mul
    (spectralCoefficient n s * (Complex.I * (frequency (n + 1) : ℂ)) ^ j *
      (frequency (n + 1) : ℂ) ^ k)).mul_const (phase (n + 1) x)
  convert hc using 1 <;>
    simp [spatialMomentTerm, pow_succ, smul_eq_mul, Complex.ofReal_mul] <;> ring

theorem spectralCoefficient_norm_bound (M n : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) :
    ‖spectralCoefficient n s‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (3 * M + 2) := by
  unfold spectralCoefficient
  rw [norm_mul]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ M * ((n + 1 : ℕ) : ℝ) ^ (2 * M + 2) :=
      mul_le_mul (power_prefactor_bound (by omega) M hs)
        (divisorFactor_polynomial_bound (by omega) M hs)
        (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by rw [← pow_add]; congr 1; omega

def spatialMajorant (j k M : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  (qMomentDecayConstant k (2 * Real.pi * a) ((M : ℝ) + 1) *
    (2 * Real.pi) ^ (j + k)) * ((n + 1 : ℕ) : ℝ) ^ (3 * M + 2 + j + k) *
      Real.exp (-(Real.pi * a) * ((n + 1 : ℕ) : ℝ))

/-- A single summable bound for all spatial derivative orders selected in
advance, uniform over x, y>=a and the entire closed real-part strip. -/
theorem spatialMomentTerm_norm_bound (j k M : ℕ) {a : ℝ} (ha : 0 < a)
    (n : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : a ≤ y) (x : ℝ) :
    ‖spatialMomentTerm j k n s y x‖ ≤ spatialMajorant j k M a n := by
  let N : ℕ := n + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hypos : 0 < y := ha.trans_le hy
  have hw : 0 < frequency N := by unfold frequency; positivity
  have hq0 : 0 < 2 * Real.pi * a := by positivity
  have hq : 2 * Real.pi * a ≤ frequency N * y := by
    have hNy : a ≤ (N : ℝ) * y := hy.trans (le_mul_of_one_le_left hypos.le hN1)
    dsimp [frequency]
    nlinarith [mul_le_mul_of_nonneg_left hNy (by positivity : 0 ≤ 2 * Real.pi)]
  have hnu : |(s - 1 / 2).re| ≤ (M : ℝ) + 1 := by
    have h := abs_sub_le s.re (1 / 2 : ℝ)
    norm_num at h
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hK := qMoment_uniform_exp_bound k hq0 hq hnu
  have he : Real.exp (-(frequency N * y / 2)) ≤
      Real.exp (-(Real.pi * a) * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hy (show 0 ≤ Real.pi * (N : ℝ) by positivity)
    dsimp [frequency]
    nlinarith
  have hK' : ‖qMoment k (s - 1 / 2) (frequency N * y)‖ ≤
      qMomentDecayConstant k (2 * Real.pi * a) ((M : ℝ) + 1) *
        Real.exp (-(Real.pi * a) * (N : ℝ)) :=
    hK.trans (mul_le_mul_of_nonneg_left he (qMomentDecayConstant_nonneg _ _ _))
  have hcoef := spectralCoefficient_norm_bound M n hs
  calc
    _ = ‖spectralCoefficient n s‖ * frequency N ^ j * frequency N ^ k *
        ‖qMoment k (s - 1 / 2) (frequency N * y)‖ := by
      simp only [spatialMomentTerm, N, norm_mul, norm_pow, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, one_mul, norm_phase, mul_one]
    _ ≤ (N : ℝ) ^ (3 * M + 2) * frequency N ^ j * frequency N ^ k *
        (qMomentDecayConstant k (2 * Real.pi * a) ((M : ℝ) + 1) *
          Real.exp (-(Real.pi * a) * (N : ℝ))) := by
      gcongr
    _ = spatialMajorant j k M a n := by
      dsimp [spatialMajorant, frequency, N]
      simp only [mul_pow, pow_add]
      ring

theorem spatialMajorant_summable (j k M : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (spatialMajorant j k M a) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul (3 * M + 2 + j + k)
    (mul_pos Real.pi_pos ha)
  have hshift := (summable_nat_add_iff 1).mpr h
  simpa only [spatialMajorant, mul_assoc] using hshift.const_mul
    (qMomentDecayConstant k (2 * Real.pi * a) ((M : ℝ) + 1) * (2 * Real.pi) ^ (j + k))

/-- Genuine normal convergence of every spatial moment family. -/
theorem spatialMoment_uniform_convergence_strip (j k M : ℕ) {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun H : ℕ => fun p : ℂ × ℝ × ℝ =>
        ∑ n ∈ Finset.range H, spatialMomentTerm j k n p.1 p.2.1 p.2.2)
      (fun p : ℂ × ℝ × ℝ => ∑' n, spatialMomentTerm j k n p.1 p.2.1 p.2.2)
      atTop {p | |p.1.re| ≤ (M : ℝ) ∧ a ≤ p.2.1} :=
  tendstoUniformlyOn_tsum_nat (spatialMajorant_summable j k M ha)
    (fun n p hp => spatialMomentTerm_norm_bound j k M ha n hp.1 hp.2 p.2.2)

theorem spatialMoment_norm_summable (j k : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖spatialMomentTerm j k n s y x‖) := by
  let M : ℕ := Nat.ceil |s.re|
  exact (spatialMajorant_summable j k M hy).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => spatialMomentTerm_norm_bound j k M hy n (Nat.le_ceil _) le_rfl x)

end

end ImbalancedChen.Part3.ContinuedFourierSpatialMoments
