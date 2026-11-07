import ImbalancedChen.Part3ImaginaryOrderKQDerivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED / 2026-10-24. No acceptance credit.
Companion of the sealed q-derivative candidate in the parent directory.
Its intended import is another source-only module; no actual source file
has been created or changed and no compiler/checker is run.

This adapts ONLY the actual real q derivative to the actual complex K/q
kernel and the specific extension already used on PacketData.region.
The extension is differentiated strictly above its cutoff. No derivative
or C1 claim at the cutoff is made, since that extension uses max(q,a).
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKQDerivativeAdapterSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly

def quotientQDerivative (t q : ℝ) : ℝ :=
  (qDerivative t q*q-imaginaryOrderK t q)/q^2

lemma imaginaryOrderK_div_complex_hasDerivAt_q (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r : ℝ => (imaginaryOrderK t r : ℂ)/(r : ℂ))
      (quotientQDerivative t q : ℂ) q := by
  simpa only [quotientQDerivative, Complex.ofReal_div] using
    (imaginaryOrderK_div_hasDerivAt_q t hq).ofReal_comp

/-- The actual extension agrees with the literal quotient on ONE genuine
neighborhood of q whenever q is strictly above its positive cutoff. -/
theorem extendedKKernel_hasDerivAt_q (a : ℝ) (ha : 0 < a) (t : ℝ)
    {q : ℝ} (hqa : a < q) :
    HasDerivAt (fun r : ℝ => extendedKKernel a ha t r)
      (quotientQDerivative t q : ℂ) q := by
  have hq : 0 < q := lt_trans ha hqa
  apply (imaginaryOrderK_div_complex_hasDerivAt_q t hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hqa] with r hr
  exact extendedKKernel_eq a ha t r hr.le

theorem extendedKKernel_deriv_norm_le (a : ℝ) (ha : 0 < a) (t : ℝ)
    {q : ℝ} (hqa : a < q) :
    ‖deriv (fun r : ℝ => extendedKKernel a ha t r) q‖ ≤ 10/q^3 := by
  have hq : 0 < q := lt_trans ha hqa
  calc
    ‖deriv (fun r : ℝ => extendedKKernel a ha t r) q‖ =
        |deriv (fun r : ℝ => imaginaryOrderK t r/r) q| := by
      rw [(extendedKKernel_hasDerivAt_q a ha t hqa).deriv,
        (imaginaryOrderK_div_hasDerivAt_q t hq).deriv]
      simp only [quotientQDerivative, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 10/q^3 := imaginaryOrderK_div_deriv_abs_le t hq

/-- Physical q is above Y0/16, hence strictly above the extension cutoff
Y0/32. No extra local-agreement or differentiability hypothesis is needed. -/
theorem physical_extendedKKernel_hasDerivAt_q {ι : Type*} (P : PacketData ι)
    (t q : ℝ) (hq : q ∈ P.region) :
    HasDerivAt
      (fun r : ℝ => extendedKKernel (P.Y0/32)
        (by have h := P.Y0_pos; positivity) t r)
      (quotientQDerivative t q : ℂ) q := by
  have hqa : P.Y0/32 < q := by linarith [P.Y0_pos, hq.1]
  exact extendedKKernel_hasDerivAt_q (P.Y0/32)
    (by have h := P.Y0_pos; positivity) t hqa

/-- A q-derivative bound for the actual extension on the complete physical
region, including both physical endpoints. The cutoff is lower still. -/
theorem physical_extendedKKernel_deriv_norm_le {ι : Type*} (P : PacketData ι)
    (t q : ℝ) (hq : q ∈ P.region) :
    ‖deriv (fun r : ℝ => extendedKKernel (P.Y0/32)
      (by have h := P.Y0_pos; positivity) t r) q‖ ≤ 40960/P.Y0^3 := by
  have hqa : P.Y0/32 < q := by linarith [P.Y0_pos, hq.1]
  have hlow : 0 < P.Y0/16 := by have h := P.Y0_pos; positivity
  have hpow : (P.Y0/16)^3 ≤ q^3 := by
    gcongr
    exact hq.1
  calc
    ‖deriv (fun r : ℝ => extendedKKernel (P.Y0/32)
        (by have h := P.Y0_pos; positivity) t r) q‖ ≤ 10/q^3 :=
      extendedKKernel_deriv_norm_le (P.Y0/32)
        (by have h := P.Y0_pos; positivity) t hqa
    _ ≤ 10/(P.Y0/16)^3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hlow 3) hpow
    _ = 40960/P.Y0^3 := by field_simp [P.Y0_pos.ne'] <;> ring

end
end ImbalancedChen.Part3.ImaginaryOrderKQDerivativeAdapterSourceOnly
