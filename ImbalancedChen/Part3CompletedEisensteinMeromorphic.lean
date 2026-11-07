import ImbalancedChen.Part3CompletedEisensteinReflection
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
The genuine completed Fourier expression is meromorphic on the complex plane.
Its nonzero Fourier terms are the actual complex-order K integrals. The apparent
constant-term pole at 1/2 has already been removed in the defining dslope.
Only 0 and 1 remain, with actual residues -1/2 and 1/2.

This is an analytic theorem about that explicit Fourier expression. It does not
assume or assert equality with the primitive Eisenstein series on Re(s)>1.
SOURCE ONLY: uncompiled, not ROOT accepted.
-/

noncomputable section

open Filter Set
open scoped Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

namespace ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a

theorem heightPower_differentiable {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ s) := by
  exact differentiable_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))

theorem reflectedHeightPower_differentiable {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ (1 - s)) := by
  exact (differentiable_const.sub differentiable_id).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))

theorem heightDifference_entire {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (heightDifference y) := by
  exact (heightPower_differentiable hy).sub (reflectedHeightPower_differentiable hy)

/-- The middle point uses the derivative value of dslope, not totalized division. -/
theorem reflectionHeightQuotient_entire {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (reflectionHeightQuotient y) := by
  have hd : Differentiable ℂ (dslope (heightDifference y) (1 / 2 : ℂ)) := by
    exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := (univ : Set ℂ))
        (c := (1 / 2 : ℂ)) Filter.univ_mem).mpr
          (heightDifference_entire hy).differentiableOn)
  exact hd.const_mul (1 / 2 : ℂ)

/-- All transcendental terms, with both rational polar terms omitted. -/
def completedFourierEntirePart (y x : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta₀ (2 * s) * (y : ℂ) ^ s +
    completedRiemannZeta₀ (2 * s - 1) * (y : ℂ) ^ (1 - s) +
    reflectionHeightQuotient y s +
    2 * (Real.sqrt y : ℂ) * ∑' n, nonzeroFrequencyPair n s y x

theorem completedFourierEntirePart_differentiable {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Differentiable ℂ (completedFourierEntirePart y x) := by
  have hZ₁ : Differentiable ℂ (fun s : ℂ => completedRiemannZeta₀ (2 * s)) :=
    differentiable_completedZeta₀.comp (differentiable_id.const_mul 2)
  have hZ₂ : Differentiable ℂ (fun s : ℂ => completedRiemannZeta₀ (2 * s - 1)) :=
    differentiable_completedZeta₀.comp ((differentiable_id.const_mul 2).sub_const 1)
  exact (((hZ₁.mul (heightPower_differentiable hy)).add
    (hZ₂.mul (reflectedHeightPower_differentiable hy))).add
      (reflectionHeightQuotient_entire hy)).add
        ((nonzeroFrequencyPair_sum_differentiable hy x).const_mul _)

theorem completedEisensteinFourier_polar_decomposition (s : ℂ) (y x : ℝ) :
    completedEisensteinFourier s y x = completedFourierEntirePart y x s -
      (y : ℂ) ^ s / (2 * s) - (y : ℂ) ^ (1 - s) / (2 * (1 - s)) := by
  unfold completedEisensteinFourier completedConstant completedFourierEntirePart
  ring

/-- Global meromorphy, including the actual removable value at s=1/2. -/
theorem completedEisensteinFourier_meromorphic {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Meromorphic (fun s : ℂ => completedEisensteinFourier s y x) := by
  intro s
  have hE := ((completedFourierEntirePart_differentiable hy x).analyticAt s).meromorphicAt
  have hA := ((heightPower_differentiable hy).analyticAt s).meromorphicAt
  have hB := ((reflectedHeightPower_differentiable hy).analyticAt s).meromorphicAt
  have hD₀ : MeromorphicAt (fun z : ℂ => 2 * z) s :=
    ((differentiable_id.const_mul (2 : ℂ)).analyticAt s).meromorphicAt
  have hD₁ : MeromorphicAt (fun z : ℂ => 2 * (1 - z)) s :=
    (((differentiable_const.sub differentiable_id).const_mul (2 : ℂ)).analyticAt s).meromorphicAt
  simpa only [completedEisensteinFourier_polar_decomposition] using
    (hE.sub (hA.div hD₀)).sub (hB.div hD₁)

/-- No possible poles outside {0,1}; in particular s=1/2 is analytic. -/
theorem completedEisensteinFourier_analyticAt {y : ℝ} (hy : 0 < y) (x : ℝ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => completedEisensteinFourier z y x) s := by
  have hD₀ : AnalyticAt ℂ (fun z : ℂ => 2 * z) s :=
    (differentiable_id.const_mul (2 : ℂ)).analyticAt s
  have hD₁ : AnalyticAt ℂ (fun z : ℂ => 2 * (1 - z)) s :=
    ((differentiable_const.sub differentiable_id).const_mul (2 : ℂ)).analyticAt s
  have hn₀ : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs₀
  have hn₁ : 2 * (1 - s) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hs₁.symm)
  simpa only [completedEisensteinFourier_polar_decomposition] using
    (((completedFourierEntirePart_differentiable hy x).analyticAt s).sub
      (((heightPower_differentiable hy).analyticAt s).div hD₀ hn₀)).sub
        (((reflectedHeightPower_differentiable hy).analyticAt s).div hD₁ hn₁)

theorem completedEisensteinFourier_analyticOnNhd {y : ℝ} (hy : 0 < y) (x : ℝ) :
    AnalyticOnNhd ℂ (fun s : ℂ => completedEisensteinFourier s y x)
      {s | s ≠ 0 ∧ s ≠ 1} := by
  intro s hs
  exact completedEisensteinFourier_analyticAt hy x hs.1 hs.2

/-- The actual residue at zero; the Fourier series contributes no polar part. -/
theorem completedEisensteinFourier_residue_zero {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Tendsto (fun s : ℂ => s * completedEisensteinFourier s y x)
      (𝓝[≠] 0) (𝓝 (-1 / 2 : ℂ)) := by
  let H : ℂ → ℂ := fun s => s * completedFourierEntirePart y x s -
    (y : ℂ) ^ s / 2 - s * (y : ℂ) ^ (1 - s) / (2 * (1 - s))
  have hH : ContinuousAt H 0 := by
    have hE := (completedFourierEntirePart_differentiable hy x).continuous.continuousAt
    have hA := (heightPower_differentiable hy).continuous.continuousAt
    have hB := (reflectedHeightPower_differentiable hy).continuous.continuousAt
    exact ((continuousAt_id.mul hE).sub (hA.div_const 2)).sub
      ((continuousAt_id.mul hB).div
        (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) (by norm_num))
  have hlim : Tendsto H (𝓝[≠] 0) (𝓝 (-1 / 2 : ℂ)) := by
    simpa [H] using hH.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin (zero_ne_one : (0 : ℂ) ≠ 1)]
    with s (hs₀ : s ≠ 0) hs₁
  rw [completedEisensteinFourier_polar_decomposition]
  dsimp [H]
  field_simp [hs₀, sub_ne_zero.mpr hs₁.symm]
  <;> ring

/-- The actual residue at one, independent of x and the positive height y. -/
theorem completedEisensteinFourier_residue_one {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Tendsto (fun s : ℂ => (s - 1) * completedEisensteinFourier s y x)
      (𝓝[≠] 1) (𝓝 (1 / 2 : ℂ)) := by
  let H : ℂ → ℂ := fun s => (s - 1) * completedFourierEntirePart y x s -
    (s - 1) * (y : ℂ) ^ s / (2 * s) + (y : ℂ) ^ (1 - s) / 2
  have hH : ContinuousAt H 1 := by
    have hE := (completedFourierEntirePart_differentiable hy x).continuous.continuousAt
    have hA := (heightPower_differentiable hy).continuous.continuousAt
    have hB := (reflectedHeightPower_differentiable hy).continuous.continuousAt
    exact (((continuousAt_id.sub continuousAt_const).mul hE).sub
      ((((continuousAt_id.sub continuousAt_const).mul hA).div
        (continuousAt_const.mul continuousAt_id) (by norm_num)))).add (hB.div_const 2)
  have hlim : Tendsto H (𝓝[≠] 1) (𝓝 (1 / 2 : ℂ)) := by
    simpa [H] using hH.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin (one_ne_zero : (1 : ℂ) ≠ 0)]
    with s (hs₁ : s ≠ 1) hs₀
  rw [completedEisensteinFourier_polar_decomposition]
  dsimp [H]
  field_simp [hs₀, sub_ne_zero.mpr hs₁.symm]
  <;> ring

/-- The nonzero residues rule out removable singularities at the two endpoints. -/
theorem completedEisensteinFourier_not_analyticAt_zero {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ¬ AnalyticAt ℂ (fun s : ℂ => completedEisensteinFourier s y x) 0 := by
  intro h
  have hlim : Tendsto (fun s : ℂ => s * completedEisensteinFourier s y x)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using (continuousAt_id.mul h.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have hbad := tendsto_nhds_unique hlim (completedEisensteinFourier_residue_zero hy x)
  norm_num at hbad

theorem completedEisensteinFourier_not_analyticAt_one {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ¬ AnalyticAt ℂ (fun s : ℂ => completedEisensteinFourier s y x) 1 := by
  intro h
  have hlim : Tendsto (fun s : ℂ => (s - 1) * completedEisensteinFourier s y x)
      (𝓝[≠] 1) (𝓝 0) := by
    simpa using ((continuousAt_id.sub continuousAt_const).mul h.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have hbad := tendsto_nhds_unique hlim (completedEisensteinFourier_residue_one hy x)
  norm_num at hbad

theorem completedEisensteinFourier_analyticAt_iff {y : ℝ} (hy : 0 < y) (x : ℝ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => completedEisensteinFourier z y x) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  constructor
  · intro h
    constructor
    · intro hs
      subst s
      exact completedEisensteinFourier_not_analyticAt_zero hy x h
    · intro hs
      subst s
      exact completedEisensteinFourier_not_analyticAt_one hy x h
  · rintro ⟨h₀, h₁⟩
    exact completedEisensteinFourier_analyticAt hy x h₀ h₁

end ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a
