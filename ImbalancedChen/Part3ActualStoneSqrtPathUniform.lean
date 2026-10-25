import ImbalancedChen.Part3ActualStoneSqrtPathAlgebra
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Instances.Complex

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual vertical Stone square-root paths: joint continuity, an explicit common
compact order rectangle, and quantitative uniform boundary convergence.
No kernel limit, spectral identity, or integrated Stone conclusion is assumed.
-/
namespace ImbalancedChen.Part3.ActualStoneSqrtPath20261025a

noncomputable section
open Set Filter
open scoped Topology

@[simp] theorem rootModulus_zero {x : ℝ} (hx : 0 ≤ x) : rootModulus x 0 = x := by
  simpa [rootModulus] using Real.sqrt_sq hx

@[simp] theorem imagMagnitude_zero {x : ℝ} (hx : 0 ≤ x) :
    imagMagnitude x 0 = Real.sqrt x := by
  unfold imagMagnitude
  rw [rootModulus_zero hx]
  congr 1
  ring

@[simp] theorem nuPlus_zero {x : ℝ} (hx : 0 < x) : nuPlus x 0 = boundaryPlus x := by
  simp [nuPlus, boundaryPlus, realMagnitude, imagMagnitude_zero hx.le]

@[simp] theorem nuMinus_zero {x : ℝ} (hx : 0 < x) : nuMinus x 0 = boundaryMinus x := by
  simp [nuMinus, boundaryMinus, realMagnitude, imagMagnitude_zero hx.le]

theorem continuous_rootModulus : Continuous (fun p : ℝ × ℝ => rootModulus p.1 p.2) := by
  unfold rootModulus
  fun_prop

theorem continuous_imagMagnitude : Continuous (fun p : ℝ × ℝ => imagMagnitude p.1 p.2) := by
  unfold imagMagnitude rootModulus
  fun_prop

theorem continuousAt_realMagnitude {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => realMagnitude q.1 q.2) p := by
  unfold realMagnitude
  exact continuous_snd.continuousAt.div
    (continuousAt_const.mul continuous_imagMagnitude.continuousAt)
    (mul_ne_zero (by norm_num) (imagMagnitude_pos hp p.2).ne')

theorem continuousAt_nuPlus {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => nuPlus q.1 q.2) p := by
  unfold nuPlus
  exact (Complex.continuous_ofReal.continuousAt.comp (continuousAt_realMagnitude hp)).sub
    ((Complex.continuous_ofReal.continuousAt.comp continuous_imagMagnitude.continuousAt).mul
      continuousAt_const)

theorem continuousAt_nuMinus {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => nuMinus q.1 q.2) p := by
  unfold nuMinus
  exact (Complex.continuous_ofReal.continuousAt.comp (continuousAt_realMagnitude hp)).add
    ((Complex.continuous_ofReal.continuousAt.comp continuous_imagMagnitude.continuousAt).mul
      continuousAt_const)

/-- One positive epsilon radius works simultaneously for every x>=A. -/
def pathRadius (A : ℝ) : ℝ := min 1 (Real.sqrt A / 4)

theorem pathRadius_pos {A : ℝ} (hA : 0 < A) : 0 < pathRadius A := by
  unfold pathRadius
  exact lt_min (by norm_num) (div_pos (Real.sqrt_pos.mpr hA) (by norm_num))

theorem realMagnitude_le_eighth {A x eps : ℝ} (hA : 0 < A) (hx : A ≤ x)
    (heps0 : 0 ≤ eps) (hepsR : eps ≤ pathRadius A) : realMagnitude x eps ≤ 1 / 8 := by
  have heps : eps ≤ Real.sqrt A / 4 := hepsR.trans (min_le_right _ _)
  refine (realMagnitude_le hA hx heps0).trans ?_
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt A)).2
  linarith only [heps]

/-- An actual compact subset of the complex order plane, including its boundary. -/
def orderRectangle (B : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Icc 0 (1 / 8) ×ˢ Icc (-Real.sqrt (B + 1)) (Real.sqrt (B + 1)))

theorem isCompact_orderRectangle (B : ℝ) : IsCompact (orderRectangle B) := by
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

theorem orderRectangle_coordinates {B : ℝ} {nu : ℂ} (hnu : nu ∈ orderRectangle B) :
    0 ≤ nu.re ∧ nu.re ≤ 1 / 8 ∧ |nu.im| ≤ Real.sqrt (B + 1) := by
  rcases hnu with ⟨p, hp, rfl⟩
  simpa using And.intro hp.1.1 (And.intro hp.1.2 (abs_le.mpr hp.2))

theorem orderRectangle_re_lt_one {B : ℝ} {nu : ℂ} (hnu : nu ∈ orderRectangle B) :
    nu.re < 1 := (orderRectangle_coordinates hnu).2.1.trans_lt (by norm_num)

theorem orderRectangle_abs_re_le_eighth {B : ℝ} {nu : ℂ}
    (hnu : nu ∈ orderRectangle B) : |nu.re| ≤ 1 / 8 := by
  rw [abs_of_nonneg (orderRectangle_coordinates hnu).1]
  exact (orderRectangle_coordinates hnu).2.1

theorem nuPlus_mem_orderRectangle {A B x eps : ℝ} (hA : 0 < A)
    (hxA : A ≤ x) (hxB : x ≤ B) (heps0 : 0 ≤ eps) (hepsR : eps ≤ pathRadius A) :
    nuPlus x eps ∈ orderRectangle B := by
  have hx0 : 0 < x := hA.trans_le hxA
  have hb0 := imagMagnitude_nonneg x eps
  have hb := imagMagnitude_le hx0.le hxB heps0 (hepsR.trans (min_le_left _ _))
  refine ⟨(realMagnitude x eps, -imagMagnitude x eps),
    ⟨⟨realMagnitude_nonneg hx0 heps0, realMagnitude_le_eighth hA hxA heps0 hepsR⟩,
      ⟨neg_le_neg hb, ?_⟩⟩, ?_⟩
  · exact (neg_nonpos.mpr hb0).trans (Real.sqrt_nonneg _)
  · simp [nuPlus, sub_eq_add_neg]

theorem nuMinus_mem_orderRectangle {A B x eps : ℝ} (hA : 0 < A)
    (hxA : A ≤ x) (hxB : x ≤ B) (heps0 : 0 ≤ eps) (hepsR : eps ≤ pathRadius A) :
    nuMinus x eps ∈ orderRectangle B := by
  have hx0 : 0 < x := hA.trans_le hxA
  have hb0 := imagMagnitude_nonneg x eps
  have hb := imagMagnitude_le hx0.le hxB heps0 (hepsR.trans (min_le_left _ _))
  refine ⟨(realMagnitude x eps, imagMagnitude x eps),
    ⟨⟨realMagnitude_nonneg hx0 heps0, realMagnitude_le_eighth hA hxA heps0 hepsR⟩,
      ⟨?_, hb⟩⟩, rfl⟩
  exact (neg_nonpos.mpr (Real.sqrt_nonneg _)).trans hb0

theorem continuousOn_nuPlus_rectangle {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (fun p : ℝ × ℝ => nuPlus p.1 p.2)
      (Icc A B ×ˢ Icc 0 (pathRadius A)) := by
  intro p hp
  exact (continuousAt_nuPlus (hA.trans_le hp.1.1)).continuousWithinAt

theorem continuousOn_nuMinus_rectangle {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (fun p : ℝ × ℝ => nuMinus p.1 p.2)
      (Icc A B ×ˢ Icc 0 (pathRadius A)) := by
  intro p hp
  exact (continuousAt_nuMinus (hA.trans_le hp.1.1)).continuousWithinAt

/-- The true vertical-path error tends to zero, with no x-dependent threshold. -/
theorem pathErrorBound_tendsto (A : ℝ) :
    Tendsto (pathErrorBound A) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous (pathErrorBound A) := by
    unfold pathErrorBound
    fun_prop
  simpa [pathErrorBound] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendstoUniformlyOn_nuPlus {A B : ℝ} (hA : 0 < A) :
    TendstoUniformlyOn (fun eps x => nuPlus x eps) boundaryPlus
      (𝓝[>] (0 : ℝ)) (Icc A B) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro tol htol
  have herr := (pathErrorBound_tendsto A).eventually (Iio_mem_nhds htol)
  have hpos : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
  filter_upwards [herr, hpos] with eps he hp
  intro x hx
  rw [dist_comm, dist_eq_norm]
  exact (nuPlus_sub_boundary_norm_le hA hx.1 hp.le).trans_lt he

theorem tendstoUniformlyOn_nuMinus {A B : ℝ} (hA : 0 < A) :
    TendstoUniformlyOn (fun eps x => nuMinus x eps) boundaryMinus
      (𝓝[>] (0 : ℝ)) (Icc A B) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro tol htol
  have herr := (pathErrorBound_tendsto A).eventually (Iio_mem_nhds htol)
  have hpos : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
  filter_upwards [herr, hpos] with eps he hp
  intro x hx
  rw [dist_comm, dist_eq_norm]
  exact (nuMinus_sub_boundary_norm_le hA hx.1 hp.le).trans_lt he

theorem tendsto_nuPlus {x : ℝ} (hx : 0 < x) :
    Tendsto (nuPlus x) (𝓝[>] (0 : ℝ)) (𝓝 (boundaryPlus x)) := by
  exact (tendstoUniformlyOn_nuPlus (B := x) hx).tendsto_at ⟨le_rfl, le_rfl⟩

theorem tendsto_nuMinus {x : ℝ} (hx : 0 < x) :
    Tendsto (nuMinus x) (𝓝[>] (0 : ℝ)) (𝓝 (boundaryMinus x)) := by
  exact (tendstoUniformlyOn_nuMinus (B := x) hx).tendsto_at ⟨le_rfl, le_rfl⟩

/-- A single eventual epsilon event gives the resolvent strip for all x in[A,B]. -/
theorem eventually_uniform_orderRange {A B : ℝ} (hA : 0 < A) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc A B,
      nuPlus x eps ∈ orderRectangle B ∧ nuMinus x eps ∈ orderRectangle B ∧
      0 < (nuPlus x eps).re ∧ (nuPlus x eps).re < 1 ∧
      0 < (nuMinus x eps).re ∧ (nuMinus x eps).re < 1 := by
  have hsmall : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), eps < pathRadius A :=
    (Iio_mem_nhds (pathRadius_pos hA)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
  filter_upwards [hsmall, hpos] with eps hs hp
  intro x hx
  have hplus := nuPlus_mem_orderRectangle hA hx.1 hx.2 hp.le hs.le
  have hminus := nuMinus_mem_orderRectangle hA hx.1 hx.2 hp.le hs.le
  exact ⟨hplus, hminus, nuPlus_re_pos (hA.trans_le hx.1) hp,
    orderRectangle_re_lt_one hplus, nuMinus_re_pos (hA.trans_le hx.1) hp,
    orderRectangle_re_lt_one hminus⟩

end
end ImbalancedChen.Part3.ActualStoneSqrtPath20261025a

