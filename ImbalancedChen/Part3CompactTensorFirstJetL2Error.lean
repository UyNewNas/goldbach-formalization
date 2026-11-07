import ImbalancedChen.Part3CompactC2FiniteTensorApproximation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual common-support finite-tensor C2 supplier yields a quantitative
global L2 error bound for every one of its six jets, including the value
and both first derivatives. The measure factor is the SAME compact box
for all accuracies. This is the smooth-to-finite-tensor step of H1 density;
it does not assume that an arbitrary H1 function is smooth, and does not
claim the missing scalar-convolution/native-L2 representative bridge.
-/

namespace ImbalancedChen.Part3.CompactTensorFirstJetL2Error20261026a
noncomputable section
open Set MeasureTheory
open scoped Topology
open CompactProductKernelSixJet20261025a
open CompactC2ProductMollifier20261026a
open CompactC2FiniteTensorApproximation20261026a
open Gamma0SmoothCompactTensorCore20261025a
open MaassWeakOperatorCore20261024zz

def approximatingFunction {F : Plane → ℂ} {A a b ε : ℝ}
    (P : CompactC2TensorApproximation F A a b ε) : Plane → ℂ :=
  finiteChartFunction P.indices (fun t => (P.tensors t).toCompactTensor)

def jetError {F : Plane → ℂ} {A a b ε : ℝ}
    (P : CompactC2TensorApproximation F A a b ε) (ij : JetIndex) (p : Plane) : ℂ :=
  partialJet ij (approximatingFunction P) p - partialJet ij F p

theorem jetError_continuous {F : Plane → ℂ} {A a b ε : ℝ}
    (P : CompactC2TensorApproximation F A a b ε) (ij : JetIndex) :
    Continuous (jetError P ij) := by
  have hG := finiteSmoothChart_contDiff P.indices P.tensors
  have heq : jetError P ij = fun p => mixedJet (approximatingFunction P) ij p -
      mixedJet F ij p := by
    funext p
    rw [jetError, partialJet_eq_mixedJet hG, partialJet_eq_mixedJet P.source_smooth]
  rw [heq]
  exact (mixedJet_smooth hG ij).continuous.sub
    (mixedJet_smooth P.source_smooth ij).continuous

theorem jetError_zero_off_box {F : Plane → ℂ} {A a b ε : ℝ}
    (P : CompactC2TensorApproximation F A a b ε) (ij : JetIndex)
    (p : Plane) (hp : p ∉ commonBox A a b) : jetError P ij p = 0 := by
  have hG := finiteSmoothChart_contDiff P.indices P.tensors
  have hg : partialJet ij (approximatingFunction P) p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp
      (P.common_support (partialJet_tsupport_subset hG ij h)))
  have hf : partialJet ij F p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp
      (P.source_support (partialJet_tsupport_subset P.source_smooth ij h)))
  simp only [jetError, hg, hf, sub_self]

theorem jetError_memLp {F : Plane → ℂ} {A a b ε : ℝ}
    (P : CompactC2TensorApproximation F A a b ε) (ij : JetIndex) :
    MemLp (jetError P ij) 2 (volume : Measure Plane) := by
  apply (jetError_continuous P ij).memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (commonBox_isCompact A a b)
  intro p hp
  by_contra hn
  exact hp (jetError_zero_off_box P ij p hn)

/-- Global squared-L2 error, not merely an estimate on the common box.
All first-jet choices are contained in the six genuine jet indices. -/
theorem jetError_integral_norm_sq_le {F : Plane → ℂ} {A a b ε : ℝ}
    (P : CompactC2TensorApproximation F A a b ε) (hε : 0 < ε) (ij : JetIndex) :
    (∫ p : Plane, ‖jetError P ij p‖ ^ 2) ≤
      ε ^ 2 * (volume : Measure Plane).real (commonBox A a b) := by
  have hK := commonBox_isCompact A a b
  have he : Integrable (fun p : Plane => ‖jetError P ij p‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (jetError_memLp P ij).aestronglyMeasurable).mp
      (jetError_memLp P ij)
  have hzero : (∫ p in commonBox A a b, ‖jetError P ij p‖ ^ 2) =
      ∫ p : Plane, ‖jetError P ij p‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [jetError_zero_off_box P ij p hp]
    norm_num
  rw [← hzero]
  calc
    _ ≤ ∫ _p in commonBox A a b, ε ^ 2 := by
      apply integral_mono_ae he.integrableOn
        (integrableOn_const.mpr (Or.inr hK.measure_lt_top.ne))
      exact Filter.Eventually.of_forall (fun p => by
        have hb := (P.uniform_sixJet_error_global hε p ij).le
        have hsq := mul_self_le_mul_self (norm_nonneg (jetError P ij p)) hb
        simpa only [pow_two] using hsq)
    _ = ε ^ 2 * (volume : Measure Plane).real (commonBox A a b) := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_comm]

end
end ImbalancedChen.Part3.CompactTensorFirstJetL2Error20261026a
