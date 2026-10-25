import ImbalancedChen.Part3PrimitiveEisensteinParameterAnalytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

Holomorphy in the complex parameter of the actual period-one primitive
Eisenstein Fourier integral. The spatial variable is restricted to [0,1],
and every seed and parameter derivative is bounded there by an explicit
summable lattice majorant. A logarithmic derivative is absorbed into two
neighboring real exponents using the existing positive-base calculation.
The parameter derivative is passed through the actual integral by the
pinned dominated derivative theorem. No uniform domination hypothesis is
supplied by the caller, and no held spatial-derivative module is imported.

This proves holomorphy of the actual left-hand Fourier integral. Extending
an evaluated Fourier-K right-hand series by an identity theorem additionally
requires the independently produced right-hand normal-convergence result.
-/

namespace ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

noncomputable section

open Set MeasureTheory Complex Metric Topology UpperHalfPlane EisensteinSeries
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic

def horizontalPoint (y : ℝ) (hy : 0 < y) (x : ℝ) : ℍ := ⟨⟨x, y⟩, hy⟩

def fourierPhase (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_fourierPhase (n : ℤ) (x : ℝ) : ‖fourierPhase n x‖ = 1 := by
  rw [fourierPhase, Complex.norm_exp]
  simp

theorem fourierPhase_measurable (n : ℤ) : Measurable (fourierPhase n) := by
  unfold fourierPhase
  fun_prop

/-- The genuine Fourier integrand, including the usual half-pair normalization. -/
def fourierIntegrand (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  fourierPhase n x * primitiveComplexEisenstein s (horizontalPoint y hy x)

/-- The actual parameter derivative of that integrand. -/
def fourierIntegrandDerivative (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  fourierPhase n x * ((1 / 2 : ℂ) * ∑' v : PrimitivePair,
    complexSeedDerivative (horizontalPoint y hy x) v s)

def actualPrimitiveFourier (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourierIntegrand y hy n s x

/-- Uniform-in-x real-seed lattice majorant on the actual Fourier interval. -/
def horizontalMajorant (t y : ℝ) (hy : 0 < y) (v : PrimitivePair) : ℝ :=
  (y ^ t * EisensteinSeries.r ⟨⟨1, y⟩, hy⟩ ^ (-(2 * t))) *
    ‖v.1‖ ^ (-(2 * t))

theorem horizontalMajorant_summable (t : ℝ) (ht : 1 < t)
    (y : ℝ) (hy : 0 < y) : Summable (horizontalMajorant t y hy) := by
  exact ((EisensteinSeries.summable_one_div_norm_rpow
    (by linarith : 2 < 2 * t)).subtype _).mul_left
      (y ^ t * EisensteinSeries.r ⟨⟨1, y⟩, hy⟩ ^ (-(2 * t)))

theorem horizontal_seed_bound (t : ℝ) (ht : 1 < t) (y : ℝ) (hy : 0 < y)
    (v : PrimitivePair) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    seed t (horizontalPoint y hy x) v.1 ≤ horizontalMajorant t y hy v := by
  have hz : horizontalPoint y hy x ∈ verticalStrip 1 y := by
    change |x| ≤ 1 ∧ y ≤ y
    exact ⟨by rw [abs_of_pos hx.1]; exact hx.2, le_rfl⟩
  exact seed_bound_on_boundedStrip t ht 1 y y hy v.1
    (horizontalPoint y hy x) hz le_rfl

theorem horizontal_complexSeed_bound (y : ℝ) (hy : 0 < y) (s : ℂ)
    (hs : 1 < s.re) (v : PrimitivePair) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖complexSeed (horizontalPoint y hy x) v s‖ ≤ horizontalMajorant s.re y hy v := by
  rw [norm_complexSeed, positiveBase_rpow_eq_seed]
  exact horizontal_seed_bound s.re hs y hy v hx

/-- A summable derivative majorant independent of both x in [0,1] and s
in the specified bounded real-part slab. -/
def horizontalDerivativeMajorant (a b epsilon y : ℝ) (hy : 0 < y)
    (v : PrimitivePair) : ℝ :=
  (horizontalMajorant (a - epsilon) y hy v +
    horizontalMajorant (b + epsilon) y hy v) / epsilon

theorem horizontalDerivativeMajorant_summable (a b epsilon y : ℝ) (hy : 0 < y)
    (ha : 1 < a - epsilon) (hb : 1 < b + epsilon) :
    Summable (horizontalDerivativeMajorant a b epsilon y hy) :=
  ((horizontalMajorant_summable (a - epsilon) ha y hy).add
    (horizontalMajorant_summable (b + epsilon) hb y hy)).div_const epsilon

theorem horizontal_complexSeedDerivative_bound (a b epsilon y : ℝ) (hy : 0 < y)
    (hepsilon : 0 < epsilon) (ha : 1 < a - epsilon) (hb : 1 < b + epsilon)
    (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) (v : PrimitivePair)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖complexSeedDerivative (horizontalPoint y hy x) v s‖ ≤
      horizontalDerivativeMajorant a b epsilon y hy v := by
  calc
    _ ≤ (seed (a - epsilon) (horizontalPoint y hy x) v.1 +
        seed (b + epsilon) (horizontalPoint y hy x) v.1) / epsilon :=
      complexSeedDerivative_norm_le (horizontalPoint y hy x) a b epsilon
        hepsilon v s hsa hsb
    _ ≤ _ := div_le_div_of_nonneg_right
      (add_le_add (horizontal_seed_bound (a - epsilon) ha y hy v hx)
        (horizontal_seed_bound (b + epsilon) hb y hy v hx)) hepsilon.le

theorem complexSeed_horizontal_measurable (y : ℝ) (hy : 0 < y)
    (v : PrimitivePair) (s : ℂ) :
    Measurable (fun x : ℝ => complexSeed (horizontalPoint y hy x) v s) := by
  unfold complexSeed positiveBase horizontalPoint
  fun_prop

theorem complexSeedDerivative_horizontal_measurable (y : ℝ) (hy : 0 < y)
    (v : PrimitivePair) (s : ℂ) :
    Measurable (fun x : ℝ => complexSeedDerivative (horizontalPoint y hy x) v s) := by
  unfold complexSeedDerivative complexSeed positiveBase horizontalPoint
  fun_prop

theorem fourierIntegrand_measurable (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) :
    Measurable (fourierIntegrand y hy n s) := by
  exact (fourierPhase_measurable n).mul
    (measurable_const.mul (Measurable.tsum (fun v => complexSeed_horizontal_measurable y hy v s)))

theorem fourierIntegrandDerivative_measurable (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) :
    Measurable (fourierIntegrandDerivative y hy n s) := by
  exact (fourierPhase_measurable n).mul
    (measurable_const.mul
      (Measurable.tsum (fun v => complexSeedDerivative_horizontal_measurable y hy v s)))

theorem fourierIntegrand_hasDerivAt (y : ℝ) (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    HasDerivAt (fun w : ℂ => fourierIntegrand y hy n w x)
      (fourierIntegrandDerivative y hy n s x) s :=
  (primitiveComplexEisenstein_hasDerivAt (horizontalPoint y hy x) s hs).const_mul
    (fourierPhase n x)

/-- A supplied spatial bound on the actual infinite integrand. -/
theorem fourierIntegrand_norm_le (y : ℝ) (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖fourierIntegrand y hy n s x‖ ≤
      (1 / 2 : ℝ) * ∑' v : PrimitivePair, horizontalMajorant s.re y hy v := by
  have hsum := tsum_of_norm_bounded (horizontalMajorant_summable s.re hs y hy).hasSum
    (fun v => horizontal_complexSeed_bound y hy s hs v hx)
  calc
    _ = (1 / 2 : ℝ) * ‖∑' v : PrimitivePair,
        complexSeed (horizontalPoint y hy x) v s‖ := by
      simp [fourierIntegrand, primitiveComplexEisenstein, norm_mul, norm_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- A supplied integrable constant dominates the actual derivative throughout
the spatial interval and the bounded parameter slab. -/
theorem fourierIntegrandDerivative_norm_le (a b epsilon y : ℝ) (hy : 0 < y)
    (hepsilon : 0 < epsilon) (ha : 1 < a - epsilon) (hb : 1 < b + epsilon)
    (n : ℤ) (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖fourierIntegrandDerivative y hy n s x‖ ≤
      (1 / 2 : ℝ) * ∑' v : PrimitivePair, horizontalDerivativeMajorant a b epsilon y hy v := by
  have hsum := tsum_of_norm_bounded
    (horizontalDerivativeMajorant_summable a b epsilon y hy ha hb).hasSum
    (fun v => horizontal_complexSeedDerivative_bound a b epsilon y hy hepsilon ha hb
      s hsa hsb v hx)
  calc
    _ = (1 / 2 : ℝ) * ‖∑' v : PrimitivePair,
        complexSeedDerivative (horizontalPoint y hy x) v s‖ := by
      simp [fourierIntegrandDerivative, norm_mul, norm_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

theorem fourierIntegrand_integrableOn (y : ℝ) (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fourierIntegrand y hy n s) (Ioc (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound (by simp)
    (fourierIntegrand_measurable y hy n s).aestronglyMeasurable.restrict
    ((1 / 2 : ℝ) * ∑' v : PrimitivePair, horizontalMajorant s.re y hy v)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact fourierIntegrand_norm_le y hy n s hs hx

/-- True parameter differentiation of the actual period-one Fourier integral,
with all required uniform domination proved above. -/
theorem actualPrimitiveFourier_hasDerivAt (y : ℝ) (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (actualPrimitiveFourier y hy n)
      (∫ x in (0 : ℝ)..1, fourierIntegrandDerivative y hy n s x) s := by
  let r : ℝ := (s.re - 1) / 4
  let a : ℝ := s.re - r
  let b : ℝ := s.re + r
  have hr : 0 < r := by dsimp [r]; linarith
  have ha : 1 < a - r := by dsimp [a, r]; linarith
  have hb : 1 < b + r := by dsimp [b, r]; linarith
  let M : ℝ := (1 / 2 : ℝ) * ∑' v : PrimitivePair,
    horizontalDerivativeMajorant a b r y hy v
  have hslab (w : ℂ) (hw : w ∈ ball s r) : a ≤ w.re ∧ w.re ≤ b := by
    have hnorm : ‖w - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    have hre0 : |w.re - s.re| ≤ ‖w - s‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - s)
    have hre : |w.re - s.re| ≤ r := hre0.trans hnorm.le
    obtain ⟨hl, hu⟩ := abs_le.mp hre
    constructor <;> dsimp [a, b] <;> linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))
    (F := fourierIntegrand y hy n) (F' := fourierIntegrandDerivative y hy n)
    (bound := fun _ : ℝ => M) (s := ball s r) (ball_mem_nhds s hr)
    (Filter.Eventually.of_forall (fun w =>
      (fourierIntegrand_measurable y hy n w).aestronglyMeasurable.restrict))
    (fourierIntegrand_integrableOn y hy n s hs)
    (fourierIntegrandDerivative_measurable y hy n s).aestronglyMeasurable.restrict
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      intro w hw
      exact fourierIntegrandDerivative_norm_le a b r y hy hr ha hb n w
        (hslab w hw).1 (hslab w hw).2 hx)
    (integrableOn_const (by simp))
    (Filter.Eventually.of_forall (fun x w hw =>
      fourierIntegrand_hasDerivAt y hy n w
        (by have hwRe := (hslab w hw).1; dsimp [a, r] at hwRe; linarith) x))
  simpa only [actualPrimitiveFourier,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h.2

/-- Holomorphy of the actual Fourier integral throughout Re(s)>1. -/
theorem actualPrimitiveFourier_differentiableOn (y : ℝ) (hy : 0 < y) (n : ℤ) :
    DifferentiableOn ℂ (actualPrimitiveFourier y hy n) {s : ℂ | 1 < s.re} := by
  intro s hs
  exact (actualPrimitiveFourier_hasDerivAt y hy n s hs).differentiableAt.differentiableWithinAt

theorem actualPrimitiveFourier_analyticOnNhd (y : ℝ) (hy : 0 < y) (n : ℤ) :
    AnalyticOnNhd ℂ (actualPrimitiveFourier y hy n) {s : ℂ | 1 < s.re} :=
  (actualPrimitiveFourier_differentiableOn y hy n).analyticOnNhd
    (isOpen_Ioi.preimage Complex.continuous_re)

end

end ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
