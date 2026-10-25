import ImbalancedChen.Part3UpperSupportedTensorLpDensity
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual quotient-level density endpoint: the closed complex span of
the original `testL2` values of genuine compact smooth positive tensors
equals the actual previously constructed `upperSupportedSubmodule`.

The function-level tensor approximation is descended through `MemLp.toLp`.
Both the finite-span membership and the exact Lp metric are proved for
those actual quotient objects. No density premise or same-target
identification is assumed.
-/

namespace ImbalancedChen.Part3.UpperSupportedTensorL2Closure20261025a

noncomputable section
open MeasureTheory Set
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a
open ImbalancedChen.Part3.UpperSupportedTensorLpDensity20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a

def smoothTensorL2Span : Submodule ℂ PlaneL2 :=
  Submodule.span ℂ (Set.range (fun T : SmoothPositiveTensor => testL2 (toMaassTensor T)))

theorem span_memLp {H : (ℝ × ℝ) → ℂ} (hH : H ∈ planeTensorSpan) : MemLp H 2 volume :=
  (span_continuous_compact hH).1.memLp_of_hasCompactSupport (span_continuous_compact hH).2

theorem planeTensor_toLp_eq_actual_testL2 (T : SmoothPositiveTensor)
    (hT : MemLp (planeTensor T) 2 (volume : Measure (ℝ × ℝ))) :
    hT.toLp (planeTensor T) = testL2 (toMaassTensor T) := by
  unfold testL2
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun p => by
    simp [planeTensor, toMaassTensor, tensorFunction, Complex.ofReal_mul]

/-- The lift is an element of the original actual testL2 span, not an
unrelated L2 class with a proposed density property. -/
theorem span_toLp_mem_actual_test_span {H : (ℝ × ℝ) → ℂ}
    (hH : H ∈ planeTensorSpan) (hmem : MemLp H 2 (volume : Measure (ℝ × ℝ))) :
    hmem.toLp H ∈ smoothTensorL2Span := by
  revert hmem
  induction hH using Submodule.span_induction with
  | mem H hH =>
      intro hmem
      obtain ⟨T, rfl⟩ := hH
      rw [planeTensor_toLp_eq_actual_testL2 T hmem]
      exact Submodule.subset_span ⟨T, rfl⟩
  | zero =>
      intro hmem
      simpa only [MemLp.toLp_zero] using smoothTensorL2Span.zero_mem
  | add F G hF hG ihF ihG =>
      intro hmem
      have hMF := span_memLp hF
      have hMG := span_memLp hG
      have heq : hmem.toLp (F + G) = hMF.toLp F + hMG.toLp G :=
        MemLp.toLp_add hMF hMG
      rw [heq]
      exact smoothTensorL2Span.add_mem (ihF hMF) (ihG hMG)
  | smul c G hG ih =>
      intro hmem
      have hMG := span_memLp hG
      have heq : hmem.toLp (c • G) = c • hMG.toLp G :=
        MemLp.toLp_const_smul c hMG
      rw [heq]
      exact smoothTensorL2Span.smul_mem c (ih hMG)

theorem actual_testL2_mem_upperSupported (T : SmoothPositiveTensor) :
    testL2 (toMaassTensor T) ∈ upperSupportedSubmodule := by
  have hmem : MemLp (planeTensor T) 2 (volume : Measure (ℝ × ℝ)) :=
    (planeTensor_continuous T).memLp_of_hasCompactSupport (planeTensor_compact T)
  rw [← planeTensor_toLp_eq_actual_testL2 T hmem]
  change ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
    p ∉ upperChart → (hmem.toLp (planeTensor T)) p = 0
  filter_upwards [hmem.coeFn_toLp] with p hp
  intro hout
  rw [hp]
  exact image_eq_zero_of_notMem_tsupport
    (fun ht => hout (tsupport_planeTensor_subset_upperChart T ht))

theorem smoothTensorL2Span_le_upperSupported : smoothTensorL2Span ≤ upperSupportedSubmodule := by
  apply Submodule.span_le.2
  rintro _ ⟨T, rfl⟩
  exact actual_testL2_mem_upperSupported T

/-- The genuine actual upper-supported quotient tensor-density theorem. -/
theorem smoothTensorL2Span_topologicalClosure_eq_upperSupported :
    smoothTensorL2Span.topologicalClosure = upperSupportedSubmodule := by
  apply le_antisymm
  · exact smoothTensorL2Span.topologicalClosure_minimal smoothTensorL2Span_le_upperSupported
      isClosed_upperSupportedSubmodule
  · intro F hF
    change F ∈ closure (smoothTensorL2Span : Set PlaneL2)
    apply Metric.mem_closure_iff.2
    intro epsilon hepsilon
    obtain ⟨H, hH, happrox⟩ :=
      exists_tensor_L2_approx_of_upperSupported F hF epsilon hepsilon
    have hmem := span_memLp hH
    refine ⟨hmem.toLp H, span_toLp_mem_actual_test_span hH hmem, ?_⟩
    have he : edist F (hmem.toLp H) =
        eLpNorm ((F : (ℝ × ℝ) → ℂ) - H) 2 volume := by
      simpa only [Lp.toLp_coeFn] using
        (Lp.edist_toLp_toLp F H (Lp.memLp F) hmem)
    rw [Lp.dist_edist, he]
    exact ENNReal.toReal_lt_of_lt_ofReal happrox

end
end ImbalancedChen.Part3.UpperSupportedTensorL2Closure20261025a
