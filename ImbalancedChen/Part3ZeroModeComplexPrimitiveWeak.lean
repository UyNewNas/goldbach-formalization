import ImbalancedChen.Part3ZeroModeRealPrimitiveWeak
import ImbalancedChen.Part3WeakDerivativeIntervalRigidity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The literal complex indefinite Lebesgue integral satisfies its smooth-test
weak derivative identity. Real and imaginary parts use the native scalar
absolute-continuity calculation. L2 on the actual finite interval supplies
every required L1 hypothesis. No tail-Hardy or graph-approximation supplier.
-/

namespace ImbalancedChen.Part3.ZeroModeComplexPrimitiveWeak20261026b
noncomputable section
open MeasureTheory Set Filter
open ZeroModeRealPrimitiveWeak20261026b
open WeakDerivativeIntervalRigidity20261026a

def complexPrimitive (a : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in a..x, g t

theorem complexPrimitive_re {a b : ℝ} {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume a b) {x : ℝ} (hx : x ∈ uIcc a b) :
    (complexPrimitive a g x).re = realPrimitive a (fun t => (g t).re) x := by
  exact (Complex.reCLM.intervalIntegral_comp_comm
    (hg.mono_set (uIcc_subset_uIcc_left hx))).symm

theorem complexPrimitive_im {a b : ℝ} {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume a b) {x : ℝ} (hx : x ∈ uIcc a b) :
    (complexPrimitive a g x).im = realPrimitive a (fun t => (g t).im) x := by
  exact (Complex.imCLM.intervalIntegral_comp_comm
    (hg.mono_set (uIcc_subset_uIcc_left hx))).symm

theorem complexPrimitive_continuousOn {a b : ℝ} {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (complexPrimitive a g) (uIcc a b) :=
  intervalIntegral.continuousOn_primitive_interval' hg (by simp)

theorem complexPrimitive_weak_identity {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume a b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, deriv ψ x • complexPrimitive a g x) = -(∫ x, ψ x • g x) := by
  have hGcont : ContinuousOn (complexPrimitive a g) (Ioo a b) :=
    (complexPrimitive_continuousOn hg).mono (by
      rw [uIcc_of_le hab]
      exact Ioo_subset_Icc_self)
  have hGloc := hGcont.locallyIntegrableOn measurableSet_Ioo
  have hgloc : LocallyIntegrableOn g (Ioo a b) :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hg).locallyIntegrableOn
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hdψs : tsupport (deriv ψ) ⊆ Ioo a b := tsupport_deriv_subset.trans hψs
  have hiL : Integrable (fun x => deriv ψ x • complexPrimitive a g x) :=
    integrable_local_test_smul hGloc hdψ.continuous hψc.deriv hdψs
  have hiR : Integrable (fun x => ψ x • g x) :=
    integrable_local_test_smul hgloc hψ.continuous hψc hψs
  have hgre : IntervalIntegrable (fun x => (g x).re) volume a b := ⟨hg.1.re, hg.2.re⟩
  have hgim : IntervalIntegrable (fun x => (g x).im) volume a b := ⟨hg.1.im, hg.2.im⟩
  have hre := realPrimitive_weak_identity hgre hψ hψc hψs
  have him := realPrimitive_weak_identity hgim hψ hψc hψs
  have hrepoint (x : ℝ) :
      (deriv ψ x • complexPrimitive a g x).re =
        deriv ψ x * realPrimitive a (fun t => (g t).re) x := by
    by_cases hx : x ∈ Ioo a b
    · have hxu : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hx.1.le, hx.2.le⟩
      simp only [Complex.smul_re, complexPrimitive_re hg hxu]
    · have hout : x ∉ tsupport ψ := fun h => hx (hψs h)
      simp [deriv_of_notMem_tsupport hout]
  have himpoint (x : ℝ) :
      (deriv ψ x • complexPrimitive a g x).im =
        deriv ψ x * realPrimitive a (fun t => (g t).im) x := by
    by_cases hx : x ∈ Ioo a b
    · have hxu : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hx.1.le, hx.2.le⟩
      simp only [Complex.smul_im, complexPrimitive_im hg hxu]
    · have hout : x ∉ tsupport ψ := fun h => hx (hψs h)
      simp [deriv_of_notMem_tsupport hout]
  apply Complex.ext
  · rw [Complex.neg_re, ← integral_re hiL, ← integral_re hiR]
    simp_rw [hrepoint, Complex.smul_re]
    exact hre
  · rw [Complex.neg_im, ← integral_im hiL, ← integral_im hiR]
    simp_rw [himpoint, Complex.smul_im]
    exact him

/-- L2 on the finite interval provides the primitive's genuine weak identity;
no L1 or regular-representative assumption is added. -/
theorem complexPrimitive_weak_identity_of_memLp {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, deriv ψ x • complexPrimitive a g x) = -(∫ x, ψ x • g x) := by
  have hi : IntegrableOn g (Ioo a b) := MemLp.integrable (by norm_num) hg
  exact complexPrimitive_weak_identity hab
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hi) hψ hψc hψs

end
end ImbalancedChen.Part3.ZeroModeComplexPrimitiveWeak20261026b
