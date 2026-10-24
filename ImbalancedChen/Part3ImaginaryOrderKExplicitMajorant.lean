import ImbalancedChen.Part3ImaginaryOrderKPositiveAxis
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
SOURCEONLY 20261024q. UNCOMPILED; no acceptance credit.

For the specific integral realization already defined in
Part3ImaginaryOrderKPositiveAxis, integrate its actual exponential
majorant with mathlib's integral_exp_mul_Ioi. The result is uniform in
every real order parameter t and valid for every positive argument q.
The factor 1/q is retained in the complex kernel estimate.

The last bound is the genuine sup norm of this particular extended
continuous kernel restricted to P.region. It is not a claim about an
arbitrary PacketData.kernel. No equality with another Bessel library or
with a full Kuznetsov kernel is asserted. This basic absolute bound
provides no spectral saving; the weighted Kuznetsov / 7/32 gap remains.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKExplicitMajorantSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open P3ActualLiteralPacketIntegralSourceOnly
open ImaginaryOrderKBesselSourceOnly

/-- Evaluate the actual exponential majorant, rather than assuming its integral. -/
lemma exponential_majorant_integral {q : ℝ} (hq : 0 < q) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-(q/2)*u)) = 2/q := by
  rw [integral_exp_mul_Ioi (by linarith : -(q/2) < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [hq.ne']

/-- Uniform in all real t, including t=0, for all positive q. -/
theorem imaginaryOrderK_abs_le (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |imaginaryOrderK t q| ≤ 2/q := by
  calc
    |imaginaryOrderK t q| =
        ‖∫ u in Ioi (0 : ℝ), kIntegrand t q u‖ := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-(q/2)*u) :=
      norm_integral_le_of_norm_le (exponential_majorant_integrable hq)
        (Filter.Eventually.of_forall (fun u => kIntegrand_norm_le hq le_rfl t u))
    _ = 2/q := exponential_majorant_integral hq

/-- The dq/q normalization costs another power of q. -/
theorem imaginaryOrderK_div_norm_le (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 2/q^2 := by
  calc
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ = |imaginaryOrderK t q|/q := by
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    _ ≤ (2/q)/q :=
      div_le_div_of_nonneg_right (imaginaryOrderK_abs_le t hq) hq.le
    _ = 2/q^2 := by rw [div_div, ← pow_two]

/-- Pointwise estimate for the actual extension on the full physical region. -/
theorem extendedKKernel_norm_le_on_region {ι : Type*} (P : PacketData ι)
    (t q : ℝ) (hq : q ∈ P.region) :
    ‖extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q‖ ≤
      512/P.Y0^2 := by
  rw [extendedKKernel_eq_on_physical_region P t q hq]
  change P.Y0/16 ≤ q ∧ q ≤ 16*P.Y0 at hq
  have hlow : 0 < P.Y0/16 := by have h := P.Y0_pos; positivity
  have hqpos : 0 < q := lt_of_lt_of_le hlow hq.1
  calc
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 2/q^2 :=
      imaginaryOrderK_div_norm_le t hqpos
    _ ≤ 2/(P.Y0/16)^2 := by
      gcongr; linarith [hq.1]
    _ = 512/P.Y0^2 := by
      field_simp [P.Y0_pos.ne']; ring

/-- Restrict this specific K kernel using the same interface as P.restrictedKernel. -/
def restrictedKKernel {ι : Type*} (P : PacketData ι) (t : ℝ) : C(P.region, ℂ) :=
  (extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t).comp
    ⟨Subtype.val, continuous_subtype_val⟩

/-- The restricted map is exactly K_{2it}(q)/q throughout P.region. -/
theorem restrictedKKernel_eq {ι : Type*} (P : PacketData ι)
    (t : ℝ) (q : P.region) :
    restrictedKKernel P t q =
      (imaginaryOrderK t (q : ℝ) : ℂ)/((q : ℝ) : ℂ) := by
  change extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t
      (q : ℝ) = _
  exact extendedKKernel_eq_on_physical_region P t (q : ℝ) q.property

/-- Actual continuous-map sup norm; no arbitrary kernel bound is assumed. -/
theorem restrictedKKernel_norm_le {ι : Type*} (P : PacketData ι) (t : ℝ) :
    ‖restrictedKKernel P t‖ ≤ 512/P.Y0^2 := by
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 512/P.Y0^2)).mpr
  intro q
  change ‖extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t
      (q : ℝ)‖ ≤ 512/P.Y0^2
  exact extendedKKernel_norm_le_on_region P t (q : ℝ) q.property

end
end ImbalancedChen.Part3.ImaginaryOrderKExplicitMajorantSourceOnly
