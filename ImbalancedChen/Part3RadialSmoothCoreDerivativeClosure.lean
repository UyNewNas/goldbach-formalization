import ImbalancedChen.Part3RadialExponentialMultiplierClosed
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual real-line compact smooth radial core is dense in L2(dr).
Its first derivative has the literal compact Green identity in that
Hilbert space. The weak derivative graph is proved closed and right
unique by that actual density; no domain-density or closedness premise
is supplied. This yields genuine first-derivative closability for the
radial Schrödinger energy coordinate.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory Filter Set

structure RadialTest where
  function : ℝ → ℂ
  smooth : ContDiff ℝ ∞ function
  compact : HasCompactSupport function

theorem RadialTest.function_memLp (T : RadialTest) : MemLp T.function 2 volume :=
  T.smooth.continuous.memLp_of_hasCompactSupport T.compact

theorem RadialTest.derivative_continuous (T : RadialTest) : Continuous (deriv T.function) :=
  (contDiff_infty_iff_deriv.mp T.smooth).2.continuous

theorem RadialTest.derivative_memLp (T : RadialTest) : MemLp (deriv T.function) 2 volume :=
  T.derivative_continuous.memLp_of_hasCompactSupport T.compact.deriv

theorem RadialTest.exponential_memLp (T : RadialTest) :
    MemLp (exponentialProduct T.function) 2 volume :=
  ((Complex.continuous_ofReal.comp Real.continuous_exp).mul T.smooth.continuous).
    memLp_of_hasCompactSupport T.compact.mul_left

def radialCoreL2 (T : RadialTest) : RadialL2 := T.function_memLp.toLp T.function
def radialDerivativeL2 (T : RadialTest) : RadialL2 :=
  T.derivative_memLp.toLp (deriv T.function)
def radialExponentialL2 (T : RadialTest) : RadialL2 :=
  T.exponential_memLp.toLp (exponentialProduct T.function)

/-- The density source is the pinned actual smooth compact Lp theorem;
every approximant becomes a literal RadialTest. -/
theorem radialCoreL2_range_dense : Dense (Set.range radialCoreL2) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hd := MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (F := ℂ) (E := ℝ) (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)) (by norm_num)
  apply hd.mono
  rintro F ⟨g, hFg, hgc, hgs⟩
  let T : RadialTest := ⟨g, hgs, hgc⟩
  refine ⟨T, ?_⟩
  apply Lp.ext
  exact T.function_memLp.coeFn_toLp.trans hFg.symm

private theorem radial_toLp_inner (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ r : ℝ, star (f r) * g r := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with r hrF hrG
  rw [hrF, hrG]
  simp only [RCLike.inner_apply', Complex.star_def]

/-- Boundary terms vanish for the actual compact functions; every
integrability fact is proved from those same functions and derivatives. -/
theorem radial_core_first_derivative_Green (T U : RadialTest) :
    inner ℂ (radialDerivativeL2 T) (radialCoreL2 U) =
      -inner ℂ (radialCoreL2 T) (radialDerivativeL2 U) := by
  have hfd : Differentiable ℝ T.function := (contDiff_infty_iff_deriv.mp T.smooth).1
  have hgd : Differentiable ℝ U.function := (contDiff_infty_iff_deriv.mp U.smooth).1
  have hi₁ : Integrable (fun r : ℝ => star (T.function r) * deriv U.function r) :=
    (T.smooth.continuous.star.mul U.derivative_continuous).
      integrable_of_hasCompactSupport U.compact.deriv.mul_left
  have hi₂ : Integrable (fun r : ℝ => star (deriv T.function r) * U.function r) :=
    (T.derivative_continuous.star.mul U.smooth.continuous).
      integrable_of_hasCompactSupport U.compact.mul_left
  have hi₀ : Integrable (fun r : ℝ => star (T.function r) * U.function r) :=
    (T.smooth.continuous.star.mul U.smooth.continuous).
      integrable_of_hasCompactSupport U.compact.mul_left
  have h := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun r : ℝ => star (T.function r)) (v := U.function)
    (u' := fun r : ℝ => star (deriv T.function r)) (v' := deriv U.function)
    (fun r _ => (hfd r).hasDerivAt.star)
    (fun r _ => (hgd r).hasDerivAt) hi₁ hi₂ hi₀
  unfold radialCoreL2 radialDerivativeL2
  rw [radial_toLp_inner, radial_toLp_inner]
  linear_combination -h

def radialWeakDerivativeGraph : Set (RadialL2 × RadialL2) :=
  {p | ∀ T : RadialTest,
    inner ℂ p.2 (radialCoreL2 T) = -inner ℂ p.1 (radialDerivativeL2 T)}

theorem isClosed_radialWeakDerivativeGraph : IsClosed radialWeakDerivativeGraph := by
  change IsClosed (⋂ T : RadialTest,
    {p : RadialL2 × RadialL2 |
      inner ℂ p.2 (radialCoreL2 T) = -inner ℂ p.1 (radialDerivativeL2 T)})
  apply isClosed_iInter
  intro T
  exact isClosed_eq (continuous_snd.inner continuous_const)
    (continuous_fst.inner continuous_const).neg

theorem radialWeakDerivativeGraph_core (T : RadialTest) :
    (radialCoreL2 T, radialDerivativeL2 T) ∈ radialWeakDerivativeGraph :=
  radial_core_first_derivative_Green T

theorem radialWeakDerivativeGraph_right_unique {F G H : RadialL2}
    (hG : (F, G) ∈ radialWeakDerivativeGraph)
    (hH : (F, H) ∈ radialWeakDerivativeGraph) : G = H := by
  have hz : G - H = 0 := by
    apply radialCoreL2_range_dense.eq_zero_of_inner_left ℂ
    rintro _ ⟨T, rfl⟩
    rw [inner_sub_left, hG T, hH T, sub_self]
  exact sub_eq_zero.mp hz

theorem radialWeakDerivativeGraph_zero_fiber {G : RadialL2}
    (hG : (0, G) ∈ radialWeakDerivativeGraph) : G = 0 := by
  apply radialCoreL2_range_dense.eq_zero_of_inner_left ℂ
  rintro _ ⟨T, rfl⟩
  simpa only [inner_zero_left, neg_zero] using hG T

/-- Real radial derivative closability, with no abstract hClosed input. -/
theorem radial_first_derivative_limit_zero (T : ℕ → RadialTest) (G : RadialL2)
    (hF : Tendsto (fun n => radialCoreL2 (T n)) atTop (nhds 0))
    (hD : Tendsto (fun n => radialDerivativeL2 (T n)) atTop (nhds G)) : G = 0 := by
  apply radialWeakDerivativeGraph_zero_fiber
  exact isClosed_radialWeakDerivativeGraph.mem_of_tendsto (hF.prodMk_nhds hD)
    (Filter.Eventually.of_forall (fun n => radialWeakDerivativeGraph_core (T n)))

theorem radial_core_exponential_relation (T : RadialTest) :
    (radialExponentialL2 T : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      exponentialProduct (radialCoreL2 T) := by
  filter_upwards [T.exponential_memLp.coeFn_toLp, T.function_memLp.coeFn_toLp]
    with r hrE hrF
  simp only [radialExponentialL2, radialCoreL2] at *
  rw [hrE]
  simp only [exponentialProduct, hrF]

/-- The two energy coordinates of the literal radial form vanish at a
zero physical limit. The potential coordinate uses the unbounded exp graph. -/
theorem radial_energy_coordinates_limit_zero (T : ℕ → RadialTest) (G H : RadialL2)
    (hF : Tendsto (fun n => radialCoreL2 (T n)) atTop (nhds 0))
    (hD : Tendsto (fun n => radialDerivativeL2 (T n)) atTop (nhds G))
    (hE : Tendsto (fun n => radialExponentialL2 (T n)) atTop (nhds H)) :
    G = 0 ∧ H = 0 :=
  ⟨radial_first_derivative_limit_zero T G hF hD,
    exponentialProduct_limit_zero _ _ H hF hE (fun n => radial_core_exponential_relation (T n))⟩

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
