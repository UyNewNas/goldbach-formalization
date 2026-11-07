import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
A compact-rectangle boundary integral lemma. Continuity on the actual compact
rectangle constructs the common finite bound; no domination or limit is an
input. This is used for the continuous actual Stone square-root paths.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.CompactRectangleBoundaryIntegral20261025a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem integral_tendsto_of_continuousOn_rectangle
    (F : ℝ × ℝ → ℂ) (A B delta : ℝ) (hdelta : 0 < delta)
    (hF : ContinuousOn F (Icc A B ×ˢ Icc 0 delta)) :
    Tendsto (fun eps : ℝ => ∫ x in Icc A B, F (x, eps)) (𝓝[>] 0)
      (𝓝 (∫ x in Icc A B, F (x, 0))) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF
  have hevent : ∀ᶠ eps : ℝ in 𝓝[>] 0, eps ∈ Icc 0 delta := by
    filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds hdelta).filter_mono nhdsWithin_le_nhds] with eps heps hupper
    exact ⟨heps.le, hupper.le⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C)
  · filter_upwards [hevent] with eps heps
    have hc : ContinuousOn (fun x : ℝ => F (x, eps)) (Icc A B) :=
      hF.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, heps⟩)
    exact hc.integrableOn_Icc.aestronglyMeasurable
  · filter_upwards [hevent] with eps heps
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hC (x, eps) ⟨hx, heps⟩
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hmap : Tendsto (fun eps : ℝ => (x, eps)) (𝓝[>] 0)
        (𝓝[Icc A B ×ˢ Icc 0 delta] (x, 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_const_nhds.prodMk
        (tendsto_id.mono_left nhdsWithin_le_nhds), ?_⟩
      filter_upwards [hevent] with eps heps
      exact ⟨hx, heps⟩
    exact (hF ⟨hx, ⟨le_rfl, hdelta.le⟩⟩).tendsto.comp hmap

end
end ImbalancedChen.Part3.CompactRectangleBoundaryIntegral20261025a
