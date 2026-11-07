import ImbalancedChen.Part3PowerSeedPeriodization
import ImbalancedChen.Part3PrimitiveEisensteinParameterAnalytic
import ImbalancedChen.Part3ComplexOrderKEntire
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- The actual complex power-seed Fourier integral is evaluated for Re(s)>1.
-- The proof supplies full-line domination, parameter differentiation and
-- an independently analytic Gamma/K expression. The real restriction is
-- the existing real-order K integral theorem. No Fourier identity is an input.
-- Native row decomposition and infinite c-sum interchange remain separate.

namespace ImbalancedChen.Part3.NativeCuspComplexPowerFourier20261027

noncomputable section
open Set MeasureTheory Complex Metric Topology
open ImbalancedChen.Part3.PowerSeedGaussianLaplace
open ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini
open ImbalancedChen.Part3.PowerSeedNonzeroFourierK
open ImbalancedChen.Part3.PowerSeedPeriodization
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
open ImbalancedChen.Part3.ComplexOrderKEntire20261025a

def powerBase (y x : ℝ) : ℝ := y / (x ^ 2 + y ^ 2)

theorem powerBase_pos {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 < powerBase y x := by
  unfold powerBase
  positivity

theorem powerBase_rpow {y : ℝ} (hy : 0 < y) (t x : ℝ) :
    powerBase y x ^ t = powerSeed t y x := by
  unfold powerBase powerSeed
  rw [Real.div_rpow hy.le (by positivity : 0 ≤ x ^ 2 + y ^ 2)]

def complexPowerSeed (y : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (s * (Real.log (powerBase y x) : ℂ))

def complexPowerDerivative (y : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  (Real.log (powerBase y x) : ℂ) * complexPowerSeed y s x

theorem complexPowerSeed_ofReal {y : ℝ} (hy : 0 < y) (t x : ℝ) :
    complexPowerSeed y (t : ℂ) x = (powerSeed t y x : ℂ) := by
  rw [← powerBase_rpow hy, Real.rpow_def_of_pos (powerBase_pos hy x)]
  simp only [complexPowerSeed, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 2
  ring

theorem norm_complexPowerSeed {y : ℝ} (hy : 0 < y) (s : ℂ) (x : ℝ) :
    ‖complexPowerSeed y s x‖ = powerSeed s.re y x := by
  rw [complexPowerSeed, Complex.norm_exp, ← powerBase_rpow hy,
    Real.rpow_def_of_pos (powerBase_pos hy x)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

theorem complexPowerSeed_continuous {y : ℝ} (hy : 0 < y) (s : ℂ) :
    Continuous (complexPowerSeed y s) := by
  unfold complexPowerSeed powerBase
  fun_prop (disch := positivity)

theorem complexPowerDerivative_continuous {y : ℝ} (hy : 0 < y) (s : ℂ) :
    Continuous (complexPowerDerivative y s) := by
  unfold complexPowerDerivative complexPowerSeed powerBase
  fun_prop (disch := positivity)

theorem complexPowerSeed_hasDerivAt (y x : ℝ) (s : ℂ) :
    HasDerivAt (fun w => complexPowerSeed y w x) (complexPowerDerivative y s x) s := by
  have h := (Complex.hasDerivAt_exp (s * (Real.log (powerBase y x) : ℂ))).comp s
    ((hasDerivAt_id s).mul_const (Real.log (powerBase y x) : ℂ))
  convert h using 1 <;> simp [complexPowerSeed, complexPowerDerivative, mul_comm]

theorem complexPowerDerivative_norm_le {y epsilon a b : ℝ}
    (hy : 0 < y) (hepsilon : 0 < epsilon) (s : ℂ)
    (hsa : a ≤ s.re) (hsb : s.re ≤ b) (x : ℝ) :
    ‖complexPowerDerivative y s x‖ ≤
      (powerSeed (a - epsilon) y x + powerSeed (b + epsilon) y x) / epsilon := by
  calc
    _ = |Real.log (powerBase y x)| * powerBase y x ^ s.re := by
      simp only [complexPowerDerivative, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_complexPowerSeed hy, ← powerBase_rpow hy]
    _ ≤ _ := by
      simpa only [powerBase_rpow hy] using
        abs_log_mul_rpow_le_neighbors (powerBase_pos hy x) hepsilon hsa hsb

def oscillatoryKernel (y : ℝ) (n : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  fourierPhase n x * complexPowerSeed y s x

def oscillatoryDerivative (y : ℝ) (n : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  fourierPhase n x * complexPowerDerivative y s x

def actualPowerFourier (y : ℝ) (n : ℤ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, oscillatoryKernel y n s x

private theorem norm_phase (n : ℤ) (x : ℝ) : ‖fourierPhase n x‖ = 1 := by
  rw [fourierPhase, Complex.norm_exp]
  simp

theorem oscillatoryKernel_continuous {y : ℝ} (hy : 0 < y) (n : ℤ) (s : ℂ) :
    Continuous (oscillatoryKernel y n s) := by
  have hp : Continuous (fourierPhase n) := by unfold fourierPhase; fun_prop
  exact hp.mul (complexPowerSeed_continuous hy s)

theorem oscillatoryKernel_integrable {y : ℝ} (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) : Integrable (oscillatoryKernel y n s) := by
  apply (powerSeed_integrable (by linarith : (1 / 2 : ℝ) < s.re) hy).mono'
    (oscillatoryKernel_continuous hy n s).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simp only [oscillatoryKernel, norm_mul, norm_phase, one_mul, norm_complexPowerSeed hy]
    exact le_rfl)

theorem actualPowerFourier_hasDerivAt {y : ℝ} (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (actualPowerFourier y n)
      (∫ x : ℝ, oscillatoryDerivative y n s x) s := by
  let r : ℝ := (s.re - 1) / 4
  let a : ℝ := s.re - r
  let b : ℝ := s.re + r
  have hr : 0 < r := by dsimp [r]; linarith
  have ha : (1 / 2 : ℝ) < a - r := by dsimp [a, r]; linarith
  have hb : (1 / 2 : ℝ) < b + r := by dsimp [b, r]; linarith
  have hslab (w : ℂ) (hw : w ∈ ball s r) : a ≤ w.re ∧ w.re ≤ b := by
    have hnorm : ‖w - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    have hre : |w.re - s.re| ≤ r :=
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - s)).trans hnorm.le
    obtain ⟨hl, hu⟩ := abs_le.mp hre
    constructor <;> dsimp [a, b] <;> linarith
  have hm : Integrable (fun x : ℝ =>
      (powerSeed (a-r) y x + powerSeed (b+r) y x) / r) :=
    ((powerSeed_integrable ha hy).add (powerSeed_integrable hb hy)).div_const r
  have hp : Continuous (fourierPhase n) := by unfold fourierPhase; fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ))
    (F := oscillatoryKernel y n) (F' := oscillatoryDerivative y n)
    (bound := fun x => (powerSeed (a-r) y x + powerSeed (b+r) y x) / r)
    (s := ball s r) (ball_mem_nhds s hr)
    (Filter.Eventually.of_forall (fun w =>
      (oscillatoryKernel_continuous hy n w).aestronglyMeasurable))
    (oscillatoryKernel_integrable hy n s hs)
    ((hp.mul (complexPowerDerivative_continuous hy s)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x w hw => by
      simp only [oscillatoryDerivative, norm_mul, norm_phase, one_mul]
      exact complexPowerDerivative_norm_le hy hr w (hslab w hw).1 (hslab w hw).2 x))
    hm
    (Filter.Eventually.of_forall (fun x w _ =>
      (complexPowerSeed_hasDerivAt y x w).const_mul (fourierPhase n x)))
  exact h.2

theorem actualPowerFourier_analyticOnNhd {y : ℝ} (hy : 0 < y) (n : ℤ) :
    AnalyticOnNhd ℂ (actualPowerFourier y n) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (actualPowerFourier y n) {s : ℂ | 1 < s.re} := by
    intro s hs
    exact (actualPowerFourier_hasDerivAt hy n s hs).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)

def nonzeroKExpression (y : ℝ) (n : ℤ) (s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) ^ s / Complex.Gamma s) *
    ((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * (Real.sqrt y : ℂ) *
      complexOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y)

theorem nonzeroKExpression_analyticOnNhd {y : ℝ} (hy : 0 < y)
    {n : ℤ} (hn : n ≠ 0) :
    AnalyticOnNhd ℂ (nonzeroKExpression y n) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (nonzeroKExpression y n) {s : ℂ | 1 < s.re} := by
    intro s hs
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hg : DifferentiableAt ℂ Complex.Gamma s := by
      apply Complex.differentiableAt_Gamma s
      intro m hm
      have hre := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg m]
    have hgne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hp := differentiableAt_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hnp := (differentiableAt_id.sub_const (1 / 2 : ℂ)).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr (abs_pos.mpr hnR).ne'))
    have hq : 0 < 2 * Real.pi * |(n : ℝ)| * y := by positivity
    have hK := (complexOrderK_differentiable_all hq).differentiableAt.comp s
      (differentiableAt_id.sub_const (1 / 2 : ℂ))
    exact (((((differentiableAt_const.mul hp).div hg hgne).mul hnp)
      .mul_const (Real.sqrt y : ℂ)).mul hK).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)

theorem actualPowerFourier_ofReal {y : ℝ} (hy : 0 < y) {n : ℤ} (hn : n ≠ 0)
    (t : ℝ) (ht : 1 < t) :
    actualPowerFourier y n (t : ℂ) = nonzeroKExpression y n (t : ℂ) := by
  have hi : actualPowerFourier y n (t : ℂ) =
      ∫ x : ℝ, fourierPhase n x * (powerSeed t y x : ℂ) := by
    unfold actualPowerFourier oscillatoryKernel
    simp only [complexPowerSeed_ofReal hy]
  rw [hi, powerSeed_nonzero_fourier_actualK (by linarith : (1 / 2 : ℝ) < t) hy hn]
  unfold nonzeroKExpression
  rw [show (t : ℂ) - 1 / 2 = ((t - 1 / 2 : ℝ) : ℂ) by push_cast,
    Complex.Gamma_ofReal, complexOrderK_real,
    ← Complex.ofReal_cpow Real.pi_pos.le t,
    ← Complex.ofReal_cpow (abs_nonneg (n : ℝ)) (t - 1 / 2)]
  push_cast
  ring

-- This is an evaluated literal oscillatory integral on the complete half-plane.
theorem actualPowerFourier_nonzero {y : ℝ} (hy : 0 < y) {n : ℤ} (hn : n ≠ 0)
    (s : ℂ) (hs : 1 < s.re) :
    actualPowerFourier y n s = nonzeroKExpression y n s := by
  have hf := actualPowerFourier_analyticOnNhd hy n
  have hg := nonzeroKExpression_analyticOnNhd hy hn
  let U : Set ℂ := {z : ℂ | 1 < z.re}
  have hU : IsPreconnected U := (Complex.convex_halfSpace_re_gt (r := 1)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hclosure : (2 : ℂ) ∈ closure
      ({z : ℂ | actualPowerFourier y n z = nonzeroKExpression y n z} \ {2}) := by
    have himage : (2 : ℂ) ∈ closure (Complex.ofReal '' Ioi (2 : ℝ)) :=
      mem_closure_image Complex.continuous_ofReal.continuousAt (by simp)
    apply (closure_mono ?_) himage
    rintro z ⟨t, ht, rfl⟩
    refine ⟨actualPowerFourier_ofReal hy hn t (by linarith), ?_⟩
    simp only [mem_singleton_iff]
    intro h
    have ht2 : t = 2 := by exact_mod_cast h
    linarith
  exact (hf.eqOn_of_preconnected_of_mem_closure hg hU h2 hclosure) s hs

end
end ImbalancedChen.Part3.NativeCuspComplexPowerFourier20261027
