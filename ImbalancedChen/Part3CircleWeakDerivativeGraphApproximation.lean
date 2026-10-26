import ImbalancedChen.Part3CuspZeroMeanSmoothApproximation
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Distributional horizontal differentiation on the actual unit circle, with
normalized Haar measure. Testing the weak equation against actual Fourier
characters identifies every derivative coefficient. The SAME frequency
cutoffs then approximate both components of the weak graph, with a literal
C-infinity, exactly zero-mean classical derivative pair at every cutoff.

This proves the circle weak-to-classical-closure inclusion. It does not
identify the cylinder weak graph: height localization, slice extraction,
and simultaneous approximation of its finitely many height coefficients
are separate obligations. No cylinder tail estimate is a hypothesis here.
-/

noncomputable section

namespace ImbalancedChen.Part3.CircleWeakDerivativeGraphApproximation20261026a

open Set MeasureTheory Filter
open scoped Topology
open CuspZeroMeanSmoothApproximationSourceOnly

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The ordinary bilinear distributional equation, tested against every
smooth periodic function. The derivative of the test is part of a genuine
`HasDerivAt` assertion, not a Fourier or graph-closure hypothesis. -/
def HasWeakCircleDerivative (f g : CircleL2) : Prop :=
  ∀ φ ψ : C(UnitAddCircle, ℂ),
    ContDiff ℝ ⊤ (fun t : ℝ => φ (t : UnitAddCircle)) →
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) →
    (∫ x : UnitAddCircle, φ x * g x ∂AddCircle.haarAddCircle) =
      -(∫ x : UnitAddCircle, ψ x * f x ∂AddCircle.haarAddCircle)

private theorem character_smooth (n : ℤ) :
    ContDiff ℝ ⊤ (fun t : ℝ => AddCircle.fourier n (t : UnitAddCircle)) := by
  simp only [AddCircle.fourier_coe_apply, Complex.ofReal_one, div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- All modes of the weak derivative are obtained by inserting the negative
character into the distributional equation. This includes the zero mode. -/
theorem weak_derivative_fourierCoeff {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g) (n : ℤ) :
    AddCircle.fourierCoeff g n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        AddCircle.fourierCoeff f n := by
  let a : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
  have hd (t : ℝ) :
      HasDerivAt (fun s : ℝ => AddCircle.fourier (-n) (s : UnitAddCircle))
        (((-a) • AddCircle.fourier (-n)) (t : UnitAddCircle)) t := by
    convert AddCircle.hasDerivAt_fourier_neg (1 : ℝ) n t using 1 <;>
      simp [a, smul_eq_mul] <;> ring
  have ht := hweak (AddCircle.fourier (-n))
    ((-a) • AddCircle.fourier (-n)) (character_smooth (-n)) hd
  change (∫ x : UnitAddCircle, AddCircle.fourier (-n) x * g x
      ∂AddCircle.haarAddCircle) =
    -(∫ x : UnitAddCircle, ((-a) * AddCircle.fourier (-n) x) * f x
      ∂AddCircle.haarAddCircle) at ht
  simp_rw [mul_assoc] at ht
  rw [integral_const_mul] at ht
  simpa only [AddCircle.fourierCoeff, smul_eq_mul, neg_mul, neg_neg, a] using ht

/-- A periodic weak derivative has zero normalized-Haar mean, without a
separate mean-zero assumption on the derivative. -/
theorem weak_derivative_zero_coefficient {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g) :
    AddCircle.fourierCoeff g 0 = 0 := by
  simpa using weak_derivative_fourierCoeff hweak 0

theorem weak_derivative_integral_zero {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g) :
    (∫ x : UnitAddCircle, g x ∂AddCircle.haarAddCircle) = 0 := by
  simpa [AddCircle.fourierCoeff, AddCircle.fourier_zero] using
    weak_derivative_zero_coefficient hweak

/-- Uniqueness of the weak derivative follows from completeness of the
actual Fourier basis, including the previously derived zero coefficient. -/
theorem weak_circle_derivative_unique {f g h : CircleL2}
    (hg : HasWeakCircleDerivative f g) (hh : HasWeakCircleDerivative f h) :
    g = h := by
  have hc (n : ℤ) : AddCircle.fourierCoeff g n = AddCircle.fourierCoeff h n := by
    rw [weak_derivative_fourierCoeff hg, weak_derivative_fourierCoeff hh]
  have hp (N : ℕ) : polynomialL2 g (window N) = polynomialL2 h (window N) := by
    simp only [polynomialL2, hc]
  apply tendsto_nhds_unique
    (window_polynomialL2_tendsto g (weak_derivative_zero_coefficient hg))
  simpa only [hp] using
    window_polynomialL2_tendsto h (weak_derivative_zero_coefficient hh)

/-- The derivative polynomial is literally the polynomial of the weak
derivative, rather than a second independently chosen approximant. -/
theorem weak_polynomial_derivative {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g) (s : Finset ℤ) (t : ℝ) :
    realDerivative f s t = realLift g s t := by
  rw [realDerivative, realLift, polynomial_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [weak_derivative_fourierCoeff hweak n]
  simp only [smul_eq_mul]
  ring

theorem weak_polynomial_hasDerivAt {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g) (s : Finset ℤ) (t : ℝ) :
    HasDerivAt (realLift f s) (realLift g s t) t := by
  rw [← weak_polynomial_derivative hweak s t]
  exact realLift_hasDerivAt f s t

/-- Both components converge in their actual L2 spaces under one common
sequence of finite Fourier projections. No derivative convergence is
assumed: it follows from the distributional coefficient computation. -/
theorem weak_fourier_graph_tendsto {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g)
    (hmean : AddCircle.fourierCoeff f 0 = 0) :
    Tendsto (fun N : ℕ =>
      (polynomialL2 f (window N), polynomialL2 g (window N)))
      atTop (𝓝 (f, g)) := by
  exact (window_polynomialL2_tendsto f hmean).prodMk_nhds
    (window_polynomialL2_tendsto g (weak_derivative_zero_coefficient hweak))

/-- Actual classical smooth mean-zero derivative pairs, before closure. -/
structure ClassicalCirclePair where
  function : C(UnitAddCircle, ℂ)
  derivative : C(UnitAddCircle, ℂ)
  smooth_function : ContDiff ℝ ⊤ (fun t : ℝ => function (t : UnitAddCircle))
  smooth_derivative : ContDiff ℝ ⊤ (fun t : ℝ => derivative (t : UnitAddCircle))
  hasDeriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => function (s : UnitAddCircle))
    (derivative (t : UnitAddCircle)) t
  mean_zero : (∫ x : UnitAddCircle, function x ∂AddCircle.haarAddCircle) = 0

def ClassicalCirclePair.coordinates (P : ClassicalCirclePair) : CircleL2 × CircleL2 :=
  (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ P.function,
   ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ P.derivative)

def classicalCircleGraph : Set (CircleL2 × CircleL2) :=
  Set.range ClassicalCirclePair.coordinates

def weakFourierPair {f g : CircleL2} (hweak : HasWeakCircleDerivative f g)
    (N : ℕ) : ClassicalCirclePair where
  function := polynomial f (window N)
  derivative := polynomial g (window N)
  smooth_function := realLift_contDiff f _
  smooth_derivative := realLift_contDiff g _
  hasDeriv := weak_polynomial_hasDerivAt hweak _
  mean_zero := polynomial_integral_zero f _

theorem weakFourierPair_coordinates {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g) (N : ℕ) :
    (weakFourierPair hweak N).coordinates =
      (polynomialL2 f (window N), polynomialL2 g (window N)) := by
  simp only [ClassicalCirclePair.coordinates, weakFourierPair, toLp_polynomial]

/-- The maximal distributional graph on the mean-zero circle is contained
in the closure of actual smooth classical pairs. This direction is the
density assertion and uses no closed-graph or approximation premise. -/
theorem weak_circle_pair_mem_classical_closure {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g)
    (hmean : AddCircle.fourierCoeff f 0 = 0) :
    (f, g) ∈ closure classicalCircleGraph := by
  have ht : Tendsto (fun N : ℕ => (weakFourierPair hweak N).coordinates)
      atTop (𝓝 (f, g)) := by
    simpa only [weakFourierPair_coordinates] using weak_fourier_graph_tendsto hweak hmean
  exact isClosed_closure.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun N => subset_closure ⟨weakFourierPair hweak N, rfl⟩)

/-- Quantitative simultaneous approximation in the two actual L2 norms. -/
theorem exists_classical_circle_pair_approximation {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g)
    (hmean : AddCircle.fourierCoeff f 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ClassicalCirclePair,
      ‖P.coordinates.1 - f‖ < ε ∧ ‖P.coordinates.2 - g‖ < ε := by
  have hf := (window_L2_error_tendsto_zero f hmean).eventually (gt_mem_nhds hε)
  have hg := (window_L2_error_tendsto_zero g
    (weak_derivative_zero_coefficient hweak)).eventually (gt_mem_nhds hε)
  obtain ⟨N, hNf, hNg⟩ := (hf.and hg).exists
  exact ⟨weakFourierPair hweak N, by simpa only [weakFourierPair_coordinates] using hNf,
    by simpa only [weakFourierPair_coordinates] using hNg⟩

theorem weak_circle_pair_mem_classical_closure_of_integral_zero {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g)
    (hmean : (∫ x : UnitAddCircle, f x ∂AddCircle.haarAddCircle) = 0) :
    (f, g) ∈ closure classicalCircleGraph := by
  apply weak_circle_pair_mem_classical_closure hweak
  simpa [AddCircle.fourierCoeff, AddCircle.fourier_zero] using hmean

end ImbalancedChen.Part3.CircleWeakDerivativeGraphApproximation20261026a
