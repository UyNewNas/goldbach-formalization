import ImbalancedChen.Part3Gamma0LocalInteriorTensorApproximation

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The support-preserving local approximation now pays the actual positive
height weight: divide the target by y, approximate it by interior smooth
tensors, then multiply each approximating vertical factor by y. Both
operations are proved and keep compact positive support. The final error
is measured by the genuine y^-1 L2 seminorm, corresponding to canonical
hyperbolic spatial density y^-2. No unweighted estimate is silently treated
as a hyperbolic estimate. Global compact localization and quotient density
remain separate obligations.
-/

namespace ImbalancedChen.Part3.Gamma0LocalWeightedTensorApproximation20261025a

noncomputable section
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a
open ImbalancedChen.Part3.Gamma0LocalInteriorTensorApproximation20261025a

def divideByHeight (F : (ℝ×ℝ)→ℂ) (p : ℝ×ℝ) : ℂ := ((p.2⁻¹:ℝ):ℂ)*F p

def multiplyByHeight (F : (ℝ×ℝ)→ℂ) (p : ℝ×ℝ) : ℂ := (p.2:ℂ)*F p

theorem divideByHeight_continuous (F : (ℝ×ℝ)→ℂ) (hF : Continuous F)
    (hpos : ∀ p∈tsupport F,0<p.2) : Continuous (divideByHeight F) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p∈tsupport F
  · have hi : ContinuousAt (fun p : ℝ×ℝ => ((p.2⁻¹:ℝ):ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp p
        (continuous_snd.continuousAt.inv₀ (hpos p hp).ne')
    exact hi.mul hF.continuousAt
  · have hz : divideByHeight F =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [isClosed_tsupport.isOpen_compl.mem_nhds hp] with w hw
      simp only [divideByHeight,image_eq_zero_of_notMem_tsupport hw,mul_zero]
    exact continuousAt_const.congr_of_eventuallyEq hz

def heightLiftTensor (T : SmoothPositiveTensor) : SmoothPositiveTensor where
  horizontal := T.horizontal
  vertical y := y*T.vertical y
  horizontal_smooth := T.horizontal_smooth
  vertical_smooth := contDiff_id.mul T.vertical_smooth
  horizontal_compact := T.horizontal_compact
  vertical_compact := T.vertical_compact.mul_left
  vertical_positive := tsupport_mul_subset_right.trans T.vertical_positive

theorem multiplyByHeight_span_mem {G : (ℝ×ℝ)→ℂ} (hG : G∈planeTensorSpan) :
    multiplyByHeight G∈planeTensorSpan := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
      obtain ⟨T,rfl⟩ := hG
      apply Submodule.subset_span
      refine ⟨heightLiftTensor T,?_⟩
      funext p
      simp only [planeTensor,heightLiftTensor,multiplyByHeight]
      push_cast
      ring
  | zero =>
      simpa only [multiplyByHeight,Pi.zero_apply,mul_zero] using planeTensorSpan.zero_mem
  | add F G hF hG ihF ihG =>
      simpa only [multiplyByHeight,Pi.add_apply,mul_add] using planeTensorSpan.add_mem ihF ihG
  | smul c G hG ih =>
      simpa only [multiplyByHeight,Pi.smul_apply,smul_eq_mul,mul_left_comm] using
        planeTensorSpan.smul_mem c ih

/-- Genuine local approximation in the actual y^-1 weighted seminorm,
with the ENTIRE approximating support still confined to the actual carrier. -/
theorem exists_local_interior_weighted_tensor_L2_approx
    (N : ℕ) [NeZero N] (z : UpperHalfPlane) (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N)
    (F : (ℝ×ℝ)→ℂ) (hFcont : Continuous F) (hFc : HasCompactSupport F)
    (hFsupp : tsupport F⊆Metric.ball (z.re,z.im) (r/4))
    (epsilon : ℝ≥0∞) (hepsilon : 0<epsilon) :
    ∃ H∈planeTensorSpan,
      tsupport H⊆localSupportRectangle z r ∧
      (∀ p∈tsupport H,0<p.2 ∧ chartLift p∈reducedCarrier N) ∧
      eLpNorm (divideByHeight (F-H)) 2 volume<epsilon := by
  have hFpos : ∀ p∈tsupport F,0<p.2 := by
    intro p hp
    exact (hball p ((hFsupp hp).trans (by linarith))).1
  have hGcont : Continuous (divideByHeight F) := divideByHeight_continuous F hFcont hFpos
  have hGc : HasCompactSupport (divideByHeight F) := hFc.mul_left
  have hGsupp : tsupport (divideByHeight F)⊆Metric.ball (z.re,z.im) (r/4) :=
    tsupport_mul_subset_right.trans hFsupp
  obtain ⟨G,hG,hGrect,hGpos,herr⟩ := exists_local_interior_tensor_L2_approx
    N z r hr hball (divideByHeight F) hGcont hGc hGsupp epsilon hepsilon
  let H := multiplyByHeight G
  have hHrect : tsupport H⊆localSupportRectangle z r :=
    tsupport_mul_subset_right.trans hGrect
  refine ⟨H,multiplyByHeight_span_mem hG,hHrect,?_,?_⟩
  · intro p hp
    exact localSupportRectangle_inside N z r hr hball p (hHrect hp)
  · have heq : divideByHeight (F-H)=divideByHeight F-G := by
      funext p
      by_cases hy : p.2=0
      · have hgzero : G p=0 := by
          by_contra hg
          have hh := (hGpos p (subset_tsupport _ hg)).1
          simpa only [hy,lt_self_iff_false] using hh
        simp only [divideByHeight,Pi.sub_apply,hy,inv_zero,Complex.ofReal_zero,
          zero_mul,hgzero,sub_zero]
      · dsimp only [divideByHeight,multiplyByHeight,H,Pi.sub_apply]
        push_cast
        field_simp [hy]
        <;> ring
    rw [heq]
    exact herr

end
end ImbalancedChen.Part3.Gamma0LocalWeightedTensorApproximation20261025a
