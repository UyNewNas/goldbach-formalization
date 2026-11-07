import ImbalancedChen.Part3LevelPrimitiveComplexEisensteinRegularity
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
Parameter analyticity of the literal level-N primitive Eisenstein Fourier
integral. All rows retain gcd(c,d)=1 and N|c. The parameter derivative is
passed through the actual interval integral using a proved summable level
subseries of the existing primitive lattice derivative majorant.
No analytic-integral, domination or level regularity premise is assumed.
SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.LevelEisensteinFourierParameterAnalytic

noncomputable section

open Set Filter MeasureTheory Complex Metric Topology
open scoped UpperHalfPlane
open Gamma0ParabolicCosetRows20261025a
open PrimitiveEisensteinParameterAnalytic PrimitiveEisensteinFourierParameterAnalytic
open LevelPrimitiveComplexEisenstein LevelPrimitiveComplexEisensteinRegularity

/-- The actual level-N scalar Fourier integrand and its actual derivative. -/
def levelFourierIntegrand (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  fourierPhase n x * levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x)

def levelFourierDerivative (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  fourierPhase n x * ((1 / 2 : ℂ) * ∑' v : LevelPrimitiveRow N,
    levelComplexSeedDerivative N (horizontalPoint y hy x) v s)

def actualLevelFourier (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, levelFourierIntegrand N y hy n s x

private theorem toPrimitiveRow_injective (N : ℕ) : Function.Injective (toPrimitiveRow N) := by
  intro v w h
  exact Subtype.ext (congrArg Subtype.val h)

def levelHorizontalDerivativeMajorant (N : ℕ) (a b epsilon y : ℝ) (hy : 0 < y)
    (v : LevelPrimitiveRow N) : ℝ :=
  horizontalDerivativeMajorant a b epsilon y hy (toPrimitiveRow N v)

theorem levelHorizontalDerivativeMajorant_summable (N : ℕ) (a b epsilon y : ℝ)
    (hy : 0 < y) (ha : 1 < a - epsilon) (hb : 1 < b + epsilon) :
    Summable (levelHorizontalDerivativeMajorant N a b epsilon y hy) :=
  (horizontalDerivativeMajorant_summable a b epsilon y hy ha hb).comp_injective
    (toPrimitiveRow_injective N)

theorem levelFourierIntegrand_measurable (N : ℕ) (y : ℝ) (hy : 0 < y)
    (n : ℤ) (s : ℂ) : Measurable (levelFourierIntegrand N y hy n s) := by
  exact (fourierPhase_measurable n).mul (measurable_const.mul
    (Measurable.tsum (fun v : LevelPrimitiveRow N =>
      complexSeed_horizontal_measurable y hy (toPrimitiveRow N v) s)))

theorem levelFourierDerivative_measurable (N : ℕ) (y : ℝ) (hy : 0 < y)
    (n : ℤ) (s : ℂ) : Measurable (levelFourierDerivative N y hy n s) := by
  exact (fourierPhase_measurable n).mul (measurable_const.mul
    (Measurable.tsum (fun v : LevelPrimitiveRow N =>
      complexSeedDerivative_horizontal_measurable y hy (toPrimitiveRow N v) s)))

theorem levelFourierIntegrand_hasDerivAt (N : ℕ) (y : ℝ) (hy : 0 < y)
    (n : ℤ) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    HasDerivAt (fun w : ℂ => levelFourierIntegrand N y hy n w x)
      (levelFourierDerivative N y hy n s x) s :=
  (levelPrimitiveComplexEisenstein_hasDerivAt N (horizontalPoint y hy x) s hs).const_mul
    (fourierPhase n x)

/-- The actual level derivative inherits a summable primitive lattice bound;
the level condition is never dropped from the function being differentiated. -/
theorem levelFourierDerivative_norm_le (N : ℕ) (a b epsilon y : ℝ) (hy : 0 < y)
    (hepsilon : 0 < epsilon) (ha : 1 < a - epsilon) (hb : 1 < b + epsilon)
    (n : ℤ) (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖levelFourierDerivative N y hy n s x‖ ≤
      (1 / 2 : ℝ) * ∑' v : LevelPrimitiveRow N,
        levelHorizontalDerivativeMajorant N a b epsilon y hy v := by
  have hsum := tsum_of_norm_bounded
    (levelHorizontalDerivativeMajorant_summable N a b epsilon y hy ha hb).hasSum
    (fun v : LevelPrimitiveRow N =>
      horizontal_complexSeedDerivative_bound a b epsilon y hy hepsilon ha hb s hsa hsb
        (toPrimitiveRow N v) hx)
  calc
    _ = (1 / 2 : ℝ) * ‖∑' v : LevelPrimitiveRow N,
        levelComplexSeedDerivative N (horizontalPoint y hy x) v s‖ := by
      simp [levelFourierDerivative, norm_mul, norm_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

theorem levelFourierIntegrand_integrableOn (N : ℕ) (y : ℝ) (hy : 0 < y)
    (n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (levelFourierIntegrand N y hy n s) (Ioc (0 : ℝ) 1) := by
  have hphase : Continuous (fourierPhase n) := by unfold fourierPhase; fun_prop
  have htrace := levelPrimitiveComplexEisenstein_horizontal_continuous N y hy s hs
  exact (hphase.mul htrace).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- True parameter differentiation of the literal all-level Fourier integral. -/
theorem actualLevelFourier_hasDerivAt (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (actualLevelFourier N y hy n)
      (∫ x in (0 : ℝ)..1, levelFourierDerivative N y hy n s x) s := by
  let r : ℝ := (s.re - 1) / 4
  let a : ℝ := s.re - r
  let b : ℝ := s.re + r
  have hr : 0 < r := by dsimp [r]; linarith
  have ha : 1 < a - r := by dsimp [a, r]; linarith
  have hb : 1 < b + r := by dsimp [b, r]; linarith
  let M : ℝ := (1 / 2 : ℝ) * ∑' v : LevelPrimitiveRow N,
    levelHorizontalDerivativeMajorant N a b r y hy v
  have hslab (w : ℂ) (hw : w ∈ ball s r) : a ≤ w.re ∧ w.re ≤ b := by
    have hnorm : ‖w - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    have hre0 : |w.re - s.re| ≤ ‖w - s‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - s)
    obtain ⟨hl, hu⟩ := abs_le.mp (hre0.trans hnorm.le)
    constructor <;> dsimp [a, b] <;> linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))
    (F := levelFourierIntegrand N y hy n) (F' := levelFourierDerivative N y hy n)
    (bound := fun _ : ℝ => M) (s := ball s r) (ball_mem_nhds s hr)
    (Filter.Eventually.of_forall (fun w =>
      (levelFourierIntegrand_measurable N y hy n w).aestronglyMeasurable.restrict))
    (levelFourierIntegrand_integrableOn N y hy n s hs)
    (levelFourierDerivative_measurable N y hy n s).aestronglyMeasurable.restrict
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      intro w hw
      exact levelFourierDerivative_norm_le N a b r y hy hr ha hb n w
        (hslab w hw).1 (hslab w hw).2 hx)
    (integrableOn_const (by simp))
    (Filter.Eventually.of_forall (fun x w hw =>
      levelFourierIntegrand_hasDerivAt N y hy n w
        (by have hwRe := (hslab w hw).1; dsimp [a, r] at hwRe; linarith) x))
  simpa only [actualLevelFourier,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h.2

theorem actualLevelFourier_analyticOnNhd (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    AnalyticOnNhd ℂ (actualLevelFourier N y hy n) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (actualLevelFourier N y hy n) {s : ℂ | 1 < s.re} := by
    intro s hs
    exact (actualLevelFourier_hasDerivAt N y hy n s hs).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)

end
end ImbalancedChen.Part3.LevelEisensteinFourierParameterAnalytic
