import ImbalancedChen.Part3PhysicalHeightCommonSmoothing
import ImbalancedChen.Part3SeparatedWeakCuspGraphApproximation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite nonzero Fourier-mode reconstruction with arbitrary compact-height
L2 coefficients. The SAME smooth height sequence approximates the value
in Haar x dy/y^2 and its literal horizontal derivative in Haar x dy.
The limiting pair is proved to belong to the concrete classical graph
closure of 38ac, so that its sharp tail bound is an actual consequence.
No hApprox, weak-graph closure, Parseval, or onto theorem is assumed.
Extraction of the coefficient derivative equation from a distributional
weak pair is owned by CuspWeakCylinderFourierModes. Passage from finite
mode reconstructions to an arbitrary pair additionally uses the existing
actual Fourier projections and their convergence; it is not asserted here.
-/

namespace ImbalancedChen.Part3.FiniteHeightModeGraphClosure20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanSmoothApproximationSourceOnly
open CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a CircleWeakDerivativeGraphApproximation20261026a
open SeparatedWeakCuspGraphApproximation20261026a
open CommonHeightSmoothApproximation20261026b PhysicalHeightCommonSmoothing20261026b
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

def frequency (n : ℤ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)

theorem character_smooth (n : ℤ) :
    ContDiff ℝ ∞ (fun t : ℝ => AddCircle.fourier n (t : UnitAddCircle)) := by
  simp only [AddCircle.fourier_coe_apply, Complex.ofReal_one, div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

def modeCirclePair (n : ℤ) (hn : n ≠ 0) : ClassicalCirclePair where
  function := AddCircle.fourier n
  derivative := frequency n • AddCircle.fourier n
  smooth_function := character_smooth n
  smooth_derivative := (character_smooth n).const_smul _
  hasDeriv := fun t => by
    simpa only [frequency, ContinuousMap.smul_apply, smul_eq_mul,
      Complex.ofReal_one, div_one] using AddCircle.hasDerivAt_fourier (1 : ℝ) n t
  mean_zero := by
    have h := congrFun (AddCircle.fourierCoeff_fourier (T := (1 : ℝ)) n) 0
    simpa [AddCircle.fourierCoeff, AddCircle.fourier_zero, hn, Ne.symm hn] using h

theorem modeCirclePair_coordinates (n : ℤ) (hn : n ≠ 0) :
    (modeCirclePair n hn).coordinates =
      (AddCircle.fourierLp 2 n, frequency n • AddCircle.fourierLp 2 n) := by
  simp only [ClassicalCirclePair.coordinates, modeCirclePair,
    map_smul, AddCircle.fourierLp]

section TensorConvergence
variable (μ : Measure PositiveHeight) [SFinite μ]
variable (μC : Measure CuspCylinder)
variable (hμ : μC = (AddCircle.haarAddCircle (T := (1 : ℝ))).prod μ)

theorem tensorVector_sub_right (u : CircleL2) (v w : Lp ℂ 2 μ) :
    tensorVector μ μC hμ u (v - w) =
      tensorVector μ μC hμ u v - tensorVector μ μC hμ u w := by
  apply Lp.ext
  have hsub : ∀ᵐ z : CuspCylinder ∂μC, (v - w) z.2 = v z.2 - w z.2 := by
    rw [hμ]
    exact (quasiMeasurePreserving_snd).ae (Lp.coeFn_sub v w)
  filter_upwards [tensorVector_ae μ μC hμ u (v - w),
    tensorVector_ae μ μC hμ u v, tensorVector_ae μ μC hμ u w,
    Lp.coeFn_sub (tensorVector μ μC hμ u v) (tensorVector μ μC hμ u w), hsub]
    with z hz hv hw hsum hs
  simp only [Pi.sub_apply] at hsum
  rw [hz, hsum, hv, hw]
  simp only [tensorFunction, hs, mul_sub]

theorem tensorVector_tendsto_right (u : CircleL2) {v : Lp ℂ 2 μ}
    {q : ℕ → Lp ℂ 2 μ} (hq : Tendsto q atTop (𝓝 v)) :
    Tendsto (fun n => tensorVector μ μC hμ u (q n)) atTop
      (𝓝 (tensorVector μ μC hμ u v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖u‖) atTop (𝓝 ‖u‖)).mul
    (tendsto_iff_norm_sub_tendsto_zero.mp hq)
  simpa only [← tensorVector_sub_right, tensorVector_norm, mul_zero] using h

end TensorConvergence

def zeroClassicalPair (a : ℝ) : ClassicalPair 1 a where
  function := 0
  derivative := 0
  continuous_function := continuous_const
  continuous_derivative := continuous_const
  hasDeriv := fun y hy t => by simpa using hasDerivAt_const t (0 : ℂ)
  mean_zero := fun y hy => by simp
  function_memLp := MemLp.zero
  derivative_memLp := MemLp.zero

private theorem circle_integrable (f : UnitAddCircle → ℂ) (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle := by
  simpa only [integrableOn_univ] using
    (hf.continuousOn.integrableOn_compact isCompact_univ :
      IntegrableOn f Set.univ AddCircle.haarAddCircle)

def addClassicalPair {a : ℝ} (P Q : ClassicalPair 1 a) : ClassicalPair 1 a where
  function := P.function + Q.function
  derivative := P.derivative + Q.derivative
  continuous_function := P.continuous_function.add Q.continuous_function
  continuous_derivative := P.continuous_derivative.add Q.continuous_derivative
  hasDeriv := fun y hy t => by
    simpa only [Pi.add_apply, mul_add] using (P.hasDeriv y hy t).add (Q.hasDeriv y hy t)
  mean_zero := fun y hy => by
    rw [show (fun x : UnitAddCircle => (P.function + Q.function) (x, y)) =
      (fun x => P.function (x, y)) + (fun x => Q.function (x, y)) from rfl,
      integral_add
        (circle_integrable _ (P.continuous_function.comp
          (continuous_id.prodMk continuous_const)))
        (circle_integrable _ (Q.continuous_function.comp
          (continuous_id.prodMk continuous_const))), P.mean_zero y hy, Q.mean_zero y hy,
      add_zero]
  function_memLp := P.function_memLp.add Q.function_memLp
  derivative_memLp := P.derivative_memLp.add Q.derivative_memLp

@[simp] theorem zeroClassicalPair_coordinates (a : ℝ) :
    (zeroClassicalPair a).coordinates = 0 := rfl

@[simp] theorem addClassicalPair_coordinates {a : ℝ} (P Q : ClassicalPair 1 a) :
    (addClassicalPair P Q).coordinates = P.coordinates + Q.coordinates := rfl

/-- Every finite sum of actual classical graph pairs is again actual
classical graph data; no topological closure is used in this lemma. -/
theorem exists_classical_sum {ι : Type*} {a : ℝ} (s : Finset ι)
    (P : ι → ClassicalPair 1 a) :
    ∃ Q : ClassicalPair 1 a, Q.coordinates = ∑ i ∈ s, (P i).coordinates := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨zeroClassicalPair a, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨Q, hQ⟩ := ih
      exact ⟨addClassicalPair (P i) Q, by simp [hi, hQ]⟩

def coefficientPair (a : ℝ) (k : ℤ) (f : PositiveHeight → ℂ)
    (hw : MemLp f 2 heightMeasure) (hr : MemLp f 2 (volume : Measure PositiveHeight)) :
    FunctionL2 a × DerivativeL2 a :=
  (tensorVector (functionHeightMeasure a) (functionMeasure a) (functionMeasure_product a)
    (AddCircle.fourierLp 2 k)
    ((hw.mono_measure Measure.restrict_le_self).toLp f),
   tensorVector (derivativeHeightMeasure a) (derivativeMeasure a) (derivativeMeasure_product a)
    (frequency k • AddCircle.fourierLp 2 k)
    ((hr.mono_measure Measure.restrict_le_self).toLp f))

def finiteCoefficientPair (a : ℝ) (s : Finset ℤ) (f : ℤ → PositiveHeight → ℂ)
    (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight)) :
    FunctionL2 a × DerivativeL2 a := ∑ k ∈ s, coefficientPair a k (f k) (hw k) (hr k)

/-- An arbitrary compact-height finite nonzero-mode pair has an actual
classical approximating sequence in the two different physical norms. -/
theorem finite_modes_classical_sequence {a A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (s : Finset ℤ) (hzero : ∀ k ∈ s, k ≠ 0)
    (f : ℤ → PositiveHeight → ℂ)
    (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight))
    (hs : ∀ k, Function.support (f k) ⊆
      {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}) :
    ∃ P : ℕ → ClassicalPair 1 a,
      Tendsto (fun n => (P n).coordinates) atTop
        (𝓝 (finiteCoefficientPair a s f hw hr)) := by
  classical
  obtain ⟨g, hg⟩ := exists_physical_common_height_sequence hA hAB f hw hr hs
  let η (n : ℕ) (k : ℤ) : HeightProfile a :=
    { function := fun y => g n k (y : ℝ)
      continuous := ((hg n k).1.continuous.comp continuous_subtype_val)
      weighted_memLp := (hg n k).2.2.2.1.mono_measure Measure.restrict_le_self
      raw_memLp := (hg n k).2.2.2.2.1.mono_measure Measure.restrict_le_self }
  let P (n : ℕ) (k : ℤ) : ClassicalPair 1 a :=
    if hk : k ∈ s then liftedClassicalPair (η n k) (modeCirclePair k (hzero k hk))
    else zeroClassicalPair a
  have hconv (k : ℤ) (hk : k ∈ s) :
      Tendsto (fun n => (P n k).coordinates) atTop
        (𝓝 (coefficientPair a k (f k) (hw k) (hr k))) := by
    have hfw := toLp_tendsto_of_tolerance
      ((hw k).mono_measure (Measure.restrict_le_self (s := strictHeightTail a)))
      (fun n => (η n k).weighted_memLp)
      (fun n => (eLpNorm_restrict_le _ _ _ _).trans (hg n k).2.2.2.2.2.1)
    have hfr := toLp_tendsto_of_tolerance
      ((hr k).mono_measure (Measure.restrict_le_self (s := strictHeightTail a)))
      (fun n => (η n k).raw_memLp)
      (fun n => (eLpNorm_restrict_le _ _ _ _).trans (hg n k).2.2.2.2.2.2)
    have hv := tensorVector_tendsto_right (functionHeightMeasure a) (functionMeasure a)
      (functionMeasure_product a) (AddCircle.fourierLp 2 k) hfw
    have hd := tensorVector_tendsto_right (derivativeHeightMeasure a) (derivativeMeasure a)
      (derivativeMeasure_product a) (frequency k • AddCircle.fourierLp 2 k) hfr
    simpa only [P, dif_pos hk, liftedClassicalPair_coordinates,
      modeCirclePair_coordinates, liftValue, liftDerivative, circleHeightTensor,
      coefficientPair] using hv.prodMk_nhds hd
  have hsum : Tendsto (fun n => ∑ k ∈ s, (P n k).coordinates) atTop
      (𝓝 (finiteCoefficientPair a s f hw hr)) := by
    unfold finiteCoefficientPair
    exact tendsto_finset_sum s hconv
  have hQ (n : ℕ) := exists_classical_sum s (P n)
  choose Q hQ using hQ
  exact ⟨Q, by simpa only [hQ] using hsum⟩

/-- This is a genuine input to the sharp closed-graph tail theorem 38ac. -/
theorem finite_modes_mem_closed_graph {a A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (s : Finset ℤ) (hzero : ∀ k ∈ s, k ≠ 0)
    (f : ℤ → PositiveHeight → ℂ)
    (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight))
    (hs : ∀ k, Function.support (f k) ⊆ {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}) :
    finiteCoefficientPair a s f hw hr ∈ closedHorizontalGraph 1 a := by
  obtain ⟨P, hP⟩ := finite_modes_classical_sequence hA hAB s hzero f hw hr hs
  exact isClosed_closure.mem_of_tendsto hP (Eventually.of_forall fun n =>
    subset_closure ⟨P n, rfl⟩)

/-- Sharp normalized period-one cusp-tail bound for the reconstructed
finite weak graph pair, with no coercivity or closure premise. -/
theorem finite_modes_sharp_tail {a A B Y : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hY : 0 < Y) (haY : a ≤ Y)
    (s : Finset ℤ) (hzero : ∀ k ∈ s, k ≠ 0) (f : ℤ → PositiveHeight → ℂ)
    (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight))
    (hs : ∀ k, Function.support (f k) ⊆ {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}) :
    ‖tailRestriction a Y haY (finiteCoefficientPair a s f hw hr).1‖ ^ 2 ≤
      (4 * Real.pi ^ 2 * Y ^ 2)⁻¹ * ‖(finiteCoefficientPair a s f hw hr).2‖ ^ 2 := by
  simpa only [one_pow, one_div] using
    closed_horizontal_tail_bound (w := 1) (by norm_num) hY haY
      (finite_modes_mem_closed_graph hA hAB s hzero f hw hr hs)

end
end ImbalancedChen.Part3.FiniteHeightModeGraphClosure20261026b
