import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

/-!
# Genuine Stokes identity on a positive periodic cusp strip

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The native planar divergence theorem is applied to the finite rectangle.
C1 regularity supplies the Frechet derivatives and compact-rectangle L1
obligation. Period one supplies the actual equality of vertical edges;
no Green identity or boundary cancellation is an input.
-/
namespace ImbalancedChen.Part3.PeriodicCuspStripStokes20261026b
noncomputable section
open Set MeasureTheory
open scoped Topology Interval

def positiveStripChart : Set (ℝ × ℝ) := {p | 0 < p.2}

def stripDivergence (Jx Jy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ Jx p (1,0) + fderiv ℝ Jy p (0,1)

theorem positiveStripChart_isOpen : IsOpen positiveStripChart :=
  isOpen_lt continuous_const continuous_snd

/-- Actual periodic-strip Stokes, deriving the vertical-edge cancellation
from period one and both horizontal boundary integrals from native Stokes. -/
theorem periodic_positive_strip_stokes (Jx Jy : ℝ × ℝ → ℂ)
    (hx : ContDiffOn ℝ 1 Jx positiveStripChart)
    (hy : ContDiffOn ℝ 1 Jy positiveStripChart)
    (hperiod : ∀ y : ℝ, 0 < y → Function.Periodic (fun x : ℝ => Jx (x,y)) 1)
    {Y T : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) :
    (∫ x in (0 : ℝ)..1, ∫ y in Y..T, stripDivergence Jx Jy (x,y)) =
      (∫ x in (0 : ℝ)..1, Jy (x,T)) - ∫ x in (0 : ℝ)..1, Jy (x,Y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let R : Set (ℝ × ℝ) := uIcc (0 : ℝ) 1 ×ˢ uIcc Y T
  have hR : R ⊆ positiveStripChart := by
    intro p hp
    simp only [R, uIcc_of_le h01, uIcc_of_le hYT, mem_prod, mem_Icc] at hp
    exact hY.trans_le hp.2.1
  have hxc := hx.continuousOn.mono hR
  have hyc := hy.continuousOn.mono hR
  have hdx := hx.continuousOn_fderiv_of_isOpen positiveStripChart_isOpen (by norm_num)
  have hdy := hy.continuousOn_fderiv_of_isOpen positiveStripChart_isOpen (by norm_num)
  have hdiv : ContinuousOn (stripDivergence Jx Jy) positiveStripChart :=
    (hdx.clm_apply continuousOn_const).add (hdy.clm_apply continuousOn_const)
  have hi : IntegrableOn (stripDivergence Jx Jy) R :=
    (hdiv.mono hR).integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hdf : ∀ p ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1) ×ˢ Ioo (min Y T) (max Y T),
      HasFDerivAt Jx (fderiv ℝ Jx p) p := by
    intro p hp
    have hp0 : p ∈ positiveStripChart := by
      simp only [min_eq_left hYT, max_eq_right hYT, mem_prod, mem_Ioo] at hp
      exact hY.trans hp.2.1
    exact ((hx p hp0).contDiffAt (positiveStripChart_isOpen.mem_nhds hp0)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hdg : ∀ p ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1) ×ˢ Ioo (min Y T) (max Y T),
      HasFDerivAt Jy (fderiv ℝ Jy p) p := by
    intro p hp
    have hp0 : p ∈ positiveStripChart := by
      simp only [min_eq_left hYT, max_eq_right hYT, mem_prod, mem_Ioo] at hp
      exact hY.trans hp.2.1
    exact ((hy p hp0).contDiffAt (positiveStripChart_isOpen.mem_nhds hp0)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hstokes := integral2_divergence_prod_of_hasFDerivAt Jx Jy (fderiv ℝ Jx) (fderiv ℝ Jy)
    0 Y 1 T hxc hyc hdf hdg hi
  have hside : (∫ y in Y..T, Jx (1,y)) = ∫ y in Y..T, Jx (0,y) := by
    apply intervalIntegral.integral_congr
    intro y hyR
    have hy0 : 0 < y := hY.trans_le (by simpa only [min_eq_left hYT] using hyR.1)
    simpa only [zero_add] using hperiod y hy0 0
  rw [hside] at hstokes
  simpa only [stripDivergence, add_sub_cancel_right] using hstokes

end
end ImbalancedChen.Part3.PeriodicCuspStripStokes20261026b

