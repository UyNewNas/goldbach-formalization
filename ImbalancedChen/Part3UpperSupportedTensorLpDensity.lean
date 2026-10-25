import ImbalancedChen.Part3UpperChartSmoothCutoffL2Convergence
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Every actual upper-supported planar L2 function is approximated in the
full-plane L2 seminorm by finite complex combinations of genuine compact
C-infinity separated tests with strictly positive vertical support.

First select an actual smooth compact upper-chart cutoff using the proved
L2 exhaustion. Approximate the original input by the pinned smooth compact
Lp approximation, and multiply that approximant by the SAME cutoff.
Its positive compact support is proved. The preceding full-plane compact
tensor approximation then applies. Three actual error terms are paid.
No compact approximation, density or support conclusion is a hypothesis.
-/

namespace ImbalancedChen.Part3.UpperSupportedTensorLpDensity20261025a

noncomputable section
open Set Filter MeasureTheory
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a
open ImbalancedChen.Part3.UpperChartSmoothCutoffL2Convergence20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a

theorem tsupport_planeTensor_subset_upperChart (T : SmoothPositiveTensor) :
    tsupport (planeTensor T) ⊆ upperChart := by
  have hs : Function.support (planeTensor T) ⊆
      tsupport T.horizontal ×ˢ tsupport T.vertical := by
    intro p hp
    constructor
    · by_contra hx
      exact hp (by simp [planeTensor, image_eq_zero_of_notMem_tsupport hx])
    · by_contra hy
      exact hp (by simp [planeTensor, image_eq_zero_of_notMem_tsupport hy])
  have ht : tsupport (planeTensor T) ⊆
      tsupport T.horizontal ×ˢ tsupport T.vertical :=
    closure_minimal hs (isClosed_tsupport.prod isClosed_tsupport)
  intro p hp
  exact T.vertical_positive (ht hp).2

theorem cutoff_multiplication_eLpNorm_le (n : ℕ) (F : (ℝ × ℝ) → ℂ) :
    eLpNorm (fun p => exhaustionCutoff n p * F p) 2 volume ≤ eLpNorm F 2 volume := by
  apply eLpNorm_mono
  intro p
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (exhaustionCutoff_norm_le_one n p)
    (norm_nonneg _)).trans_eq (one_mul _)

/-- The complete actual approximation, for arbitrary upper-supported
MemLp input. All comparison functions are constructed in the proof. -/
theorem exists_upper_supported_tensor_L2_approx (F : (ℝ × ℝ) → ℂ)
    (hF : MemLp F 2 (volume : Measure (ℝ × ℝ)))
    (hsupp : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ upperChart → F p = 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ H ∈ planeTensorSpan, eLpNorm (F - H) 2 volume < ENNReal.ofReal epsilon := by
  let eta := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hcut := tendsto_cutoff_eLpNorm F hF hsupp
  have hev : ∀ᶠ n : ℕ in atTop, eLpNorm
      (fun p => F p - exhaustionCutoff n p * F p) 2 volume < ENNReal.ofReal eta :=
    hcut.eventually (gt_mem_nhds (by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal eta))
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨g, hgc, hgs, hgerror⟩ := hF.exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 ≤ (2 : ℝ≥0∞)) heta
  let K : (ℝ × ℝ) → ℂ := fun p => exhaustionCutoff n p * g p
  have hKcont : Continuous K := (exhaustionCutoff_continuous n).mul hgs.continuous
  have hKcompact : HasCompactSupport K := (exhaustionCutoff_compact n).mul_right
  have hKpositive : tsupport K ⊆ upperChart :=
    tsupport_mul_subset_left.trans (tsupport_planeTensor_subset_upperChart (exhaustionTensor n))
  have hKg : eLpNorm (fun p => exhaustionCutoff n p * (F p - g p)) 2 volume ≤
      ENNReal.ofReal eta :=
    (cutoff_multiplication_eLpNorm_le n (F - g)).trans hgerror
  have hFK : eLpNorm (F - K) 2 volume ≤
      ENNReal.ofReal eta + ENNReal.ofReal eta := by
    have heq : F - K =
        (fun p => F p - exhaustionCutoff n p * F p) +
          (fun p => exhaustionCutoff n p * (F p - g p)) := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply, K]
      ring
    rw [heq]
    refine (eLpNorm_add_le
      (hF.aestronglyMeasurable.sub
        ((exhaustionCutoff_continuous n).aestronglyMeasurable.mul hF.aestronglyMeasurable))
      ((exhaustionCutoff_continuous n).aestronglyMeasurable.mul
        (hF.aestronglyMeasurable.sub hgs.continuous.aestronglyMeasurable))
      (by norm_num : 1 ≤ (2 : ℝ≥0∞))).trans ?_
    exact add_le_add hn.le hKg
  obtain ⟨H, hH, hKH⟩ := exists_plane_tensor_L2_approx K hKcont hKcompact
    hKpositive (ENNReal.ofReal eta) (by positivity)
  refine ⟨H, hH, ?_⟩
  have hHcont := (span_continuous_compact hH).1
  have hsum : ENNReal.ofReal eta + ENNReal.ofReal eta + ENNReal.ofReal eta <
      ENNReal.ofReal epsilon := by
    rw [← ENNReal.ofReal_add heta.le heta.le,
      ← ENNReal.ofReal_add (by positivity) heta.le]
    apply (ENNReal.ofReal_lt_ofReal_iff hepsilon).2
    dsimp only [eta]
    linarith
  have htri : eLpNorm (F - H) 2 volume ≤
      eLpNorm (F - K) 2 volume + eLpNorm (K - H) 2 volume := by
    have heq : F - H = (F - K) + (K - H) := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [heq]
    exact eLpNorm_add_le (hF.aestronglyMeasurable.sub hKcont.aestronglyMeasurable)
      (hKcont.aestronglyMeasurable.sub hHcont.aestronglyMeasurable)
      (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  exact (htri.trans (add_le_add hFK hKH.le)).trans_lt hsum

/-- Direct endpoint for the existing actual upper-supported Hilbert space. -/
theorem exists_tensor_L2_approx_of_upperSupported (F : PlaneL2)
    (hF : F ∈ upperSupportedSubmodule) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ H ∈ planeTensorSpan, eLpNorm ((F : (ℝ × ℝ) → ℂ) - H) 2 volume <
      ENNReal.ofReal epsilon :=
  exists_upper_supported_tensor_L2_approx F (Lp.memLp F) hF epsilon hepsilon

end
end ImbalancedChen.Part3.UpperSupportedTensorLpDensity20261025a
