import ImbalancedChen.Part3ProductKernelL2TranslationAverage
import ImbalancedChen.Part3CompactL2TestSeparation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For a genuinely compactly supported L2 function, the native L2 Bochner
average equals the class of its actual pointwise product convolution.
The proof establishes scalar joint integrability before Fubini, commutes
the continuous linear L2 test pairing with the Bochner integral, and uses
proved compact-continuous test separation. No representative join is an
input. Compact support is required of this scalar function; applying the
theorem to an entire compact H1 jet requires support of each component.
-/

namespace ImbalancedChen.Part3.CompactProductBochnerAEJoin20261026a
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
open CompactC2ProductMollifier20261026a
open ProductKernelL2TranslationAverage20261026a

theorem scalar_convolution_pairing {k f h : Plane → ℂ}
    (hk : Integrable k volume) (hf : Integrable f volume)
    (hh : Continuous h) (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C) :
    (∫ x, h x * convolutionC k f x) =
      ∫ t, k t * (∫ x, h x * f (x - t)) := by
  have hj : Integrable (fun p : Plane × Plane =>
      h p.1 * (k p.2 * f (p.1 - p.2))) (volume.prod volume) := by
    apply (hk.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hf).bdd_mul
      (hh.comp continuous_fst).aestronglyMeasurable
    exact Eventually.of_forall fun p => hbound p.1
  calc
    _ = ∫ x, ∫ t, h x * (k t * f (x - t)) := by
      simp only [convolutionC, convolution_def, ContinuousLinearMap.mul_apply',
        integral_const_mul]
    _ = ∫ t, ∫ x, h x * (k t * f (x - t)) := integral_integral_swap hj
    _ = _ := by
      have heq (x t : Plane) : h x * (k t * f (x - t)) =
          k t * (h x * f (x - t)) := by ring
      simp_rw [heq, integral_const_mul]

theorem compact_memLp_integrable {f : Plane → ℂ} (hf : MemLp f 2 volume)
    (hc : HasCompactSupport f) : Integrable f volume := by
  have hl := (hf.locallyIntegrable (by norm_num)).integrableOn_isCompact hc.isCompact
  exact (integrableOn_iff_integrable_of_support_subset subset_closure).mp hl

theorem smoothing_continuous {f : Plane → ℂ} (hf : MemLp f 2 volume)
    (r : ℝ) (hr : 0 < r) : Continuous (productSmoothing r hr f) :=
  ((complexProductKernel_compact r hr).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ) (complexProductKernel_smooth r hr)
    (hf.locallyIntegrable (by norm_num))).continuous

theorem smoothing_compact {f : Plane → ℂ} (hc : HasCompactSupport f)
    (r : ℝ) (hr : 0 < r) : HasCompactSupport (productSmoothing r hr f) :=
  (complexProductKernel_compact r hr).convolution (ContinuousLinearMap.mul ℝ ℂ) hc

theorem smoothing_memLp {f : Plane → ℂ} (hf : MemLp f 2 volume)
    (hc : HasCompactSupport f) (r : ℝ) (hr : 0 < r) :
    MemLp (productSmoothing r hr f) 2 volume :=
  (smoothing_continuous hf r hr).memLp_of_hasCompactSupport (smoothing_compact hc r hr)

theorem inner_translation_toLp {f h : Plane → ℂ}
    (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) (t : Plane) :
    inner ℂ (hh.toLp h) (translation (hf.toLp f) (-t)) =
      ∫ x, star (h x) * f (x - t) := by
  have hs := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-t)) (hf.toLp f)
  have ht := (measurePreserving_vadd (-t) (volume : Measure Plane))
    .quasiMeasurePreserving.ae hf.coeFn_toLp
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp, hs, ht] with x hhx hsx htx
  change (inner ℂ ((hh.toLp h) x)
    ((DomAddAct.mk (-t) +ᵥ hf.toLp f) x)) = _
  rw [hhx, hsx, htx]
  simp only [RCLike.inner_apply', Complex.star_def, vadd_eq_add,
    sub_eq_add_neg, add_comm]

theorem inner_productAverage_toLp {f h : Plane → ℂ}
    (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) (r : ℝ) (hr : 0 < r) :
    inner ℂ (hh.toLp h) (productAverage r hr (hf.toLp f)) =
      ∫ t, complexProductKernel r hr t * (∫ x, star (h x) * f (x - t)) := by
  rw [productAverage_integral,
    ← (innerSL ℂ (hh.toLp h)).integral_comp_comm
      (productAverage_integrable r hr (hf.toLp f))]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    simp only [innerSL_apply_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_right, inner_translation_toLp hf hh,
      complexProductKernel_eq]

/-- Exact class equality, established through actual compact continuous
test density and scalar Fubini. No hJoin or a.e.-equality input occurs. -/
theorem productAverage_eq_scalar_toLp {f : Plane → ℂ} (hf : MemLp f 2 volume)
    (hc : HasCompactSupport f) (r : ℝ) (hr : 0 < r) :
    productAverage r hr (hf.toLp f) =
      (smoothing_memLp hf hc r hr).toLp (productSmoothing r hr f) := by
  apply CompactL2TestSeparation20261026a.eq_of_compact_continuous_tests
  intro h hh hhc hm
  obtain ⟨C, hC⟩ := hh.norm.bddAbove_range_of_hasCompactSupport hhc.norm
  have hbound : ∀ x, ‖star (h x)‖ ≤ C := fun x => by
    simpa only [norm_star] using hC (mem_range_self x)
  have hp := scalar_convolution_pairing
    ((complexProductKernel_smooth r hr).continuous.integrable_of_hasCompactSupport
      (complexProductKernel_compact r hr))
    (compact_memLp_integrable hf hc) hh.star C hbound
  rw [inner_productAverage_toLp hf hm]
  calc
    _ = ∫ x, star (h x) * productSmoothing r hr f x := hp.symm
    _ = inner ℂ (hm.toLp h)
        ((smoothing_memLp hf hc r hr).toLp (productSmoothing r hr f)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hm.coeFn_toLp, (smoothing_memLp hf hc r hr).coeFn_toLp]
        with x hx hfx
      rw [hx, hfx]
      simp only [RCLike.inner_apply', Complex.star_def]

theorem productAverage_coe_ae {f : Plane → ℂ} (hf : MemLp f 2 volume)
    (hc : HasCompactSupport f) (r : ℝ) (hr : 0 < r) :
    productAverage r hr (hf.toLp f) =ᵐ[volume] productSmoothing r hr f := by
  rw [productAverage_eq_scalar_toLp hf hc r hr]
  exact (smoothing_memLp hf hc r hr).coeFn_toLp

end
end ImbalancedChen.Part3.CompactProductBochnerAEJoin20261026a
