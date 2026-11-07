import ImbalancedChen.Part3StandardModularCellCurrentPullback
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Tactic

/-!
# Genuine curved-bottom Stokes on the standard truncated modular cell

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The domain is literally -1/2<=x<=1/2, sqrt(1-x^2)<=y<=T.
The proved graph-current pullback and its exact divergence Jacobian reduce
the integral to native rectangular Stokes. All four actual boundary pieces
remain, including the exact lower-graph one-form -Jy dx+Jx dy.
No Stokes identity, coset reindexing or side-cancellation is assumed.
-/
namespace ImbalancedChen.Part3.StandardModularCellCurvedStokes20261026b
noncomputable section
open Set MeasureTheory
open scoped Topology Interval
open StandardModularCellGraph20261026b StandardModularCellCurrentPullback20261026b
open PeriodicCuspStripStokes20261026b

def lowerGraphFlux (Jx Jy : ℝ × ℝ → ℂ) (x : ℝ) : ℂ :=
  -Jy (x, modularBottom x) + (bottomSlope x : ℂ) * Jx (x, modularBottom x)

/-- True curved modular-cell divergence theorem in canonical dy dx chart.
The lower boundary is the actual unit-circle graph and all side traces are
retained for the separate genuine group-covariance cancellation theorem. -/
theorem standard_modular_cell_curved_stokes (Jx Jy : ℝ × ℝ → ℂ)
    (hx : ContDiffOn ℝ 1 Jx positiveStripChart) (hy : ContDiffOn ℝ 1 Jy positiveStripChart)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T, stripDivergence Jx Jy (x,y)) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), Jy (x,T)) +
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), lowerGraphFlux Jx Jy x) +
      (∫ y in modularBottom (1 / 2)..T, Jx (1 / 2,y)) -
      (∫ y in modularBottom (-(1 / 2))..T, Jx (-(1 / 2),y)) := by
  have hab : -(1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let R : Set (ℝ × ℝ) := uIcc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ uIcc (0 : ℝ) 1
  have hR : R ⊆ graphDomain T := by
    intro p hp
    apply modular_rectangle_maps_positive hT
    simpa only [R, uIcc_of_le hab, uIcc_of_le h01] using hp
  have hKx := graphPullbackX_contDiffOn T Jx hx
  have hKy := graphPullbackY_contDiffOn T Jx Jy hx hy
  have hdx := hKx.continuousOn_fderiv_of_isOpen (graphDomain_isOpen T) (by norm_num)
  have hdy := hKy.continuousOn_fderiv_of_isOpen (graphDomain_isOpen T) (by norm_num)
  have hdiv : ContinuousOn (stripDivergence (graphPullbackX T Jx) (graphPullbackY T Jx Jy))
      (graphDomain T) :=
    (hdx.clm_apply continuousOn_const).add (hdy.clm_apply continuousOn_const)
  have hi : IntegrableOn (stripDivergence (graphPullbackX T Jx) (graphPullbackY T Jx Jy)) R :=
    (hdiv.mono hR).integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hdKx : ∀ p ∈ Ioo (min (-(1 / 2 : ℝ)) (1 / 2)) (max (-(1 / 2 : ℝ)) (1 / 2)) ×ˢ
      Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasFDerivAt (graphPullbackX T Jx) (fderiv ℝ (graphPullbackX T Jx) p) p := by
    intro p hp
    have hpR : p ∈ R := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
    exact ((hKx p (hR hpR)).contDiffAt ((graphDomain_isOpen T).mem_nhds (hR hpR))).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hdKy : ∀ p ∈ Ioo (min (-(1 / 2 : ℝ)) (1 / 2)) (max (-(1 / 2 : ℝ)) (1 / 2)) ×ˢ
      Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasFDerivAt (graphPullbackY T Jx Jy) (fderiv ℝ (graphPullbackY T Jx Jy) p) p := by
    intro p hp
    have hpR : p ∈ R := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
    exact ((hKy p (hR hpR)).contDiffAt ((graphDomain_isOpen T).mem_nhds (hR hpR))).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hstokes := integral2_divergence_prod_of_hasFDerivAt
    (graphPullbackX T Jx) (graphPullbackY T Jx Jy)
    (fderiv ℝ (graphPullbackX T Jx)) (fderiv ℝ (graphPullbackY T Jx Jy))
    (-(1 / 2 : ℝ)) 0 (1 / 2) 1 (hKx.continuousOn.mono hR) (hKy.continuousOn.mono hR) hdKx hdKy hi
  have hmass :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ r in (0 : ℝ)..1,
        stripDivergence (graphPullbackX T Jx) (graphPullbackY T Jx Jy) (x,r)) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T, stripDivergence Jx Jy (x,y) := by
    calc
      _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ r in (0 : ℝ)..1,
          ((T - modularBottom x : ℝ) : ℂ) * stripDivergence Jx Jy (graphMap T (x,r)) := by
        apply intervalIntegral.integral_congr
        intro x hxR
        apply intervalIntegral.integral_congr
        intro r hrR
        exact graphPullback_divergence T Jx Jy hx hy x r (hR ⟨hxR,hrR⟩)
      _ = _ := by
        simp_rw [intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        exact graph_vertical_integral T x (fun y => stripDivergence Jx Jy (x,y))
  have htop :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), graphPullbackY T Jx Jy (x,1)) =
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Jy (x,T) := by
    apply intervalIntegral.integral_congr
    intro x _
    have ht : graphHeight T x 1 = T := by unfold graphHeight; ring
    simp [graphPullbackY, graphMap, ht]
  have hbottom :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), graphPullbackY T Jx Jy (x,0)) =
        -(∫ x in (-(1 / 2 : ℝ))..(1 / 2), lowerGraphFlux Jx Jy x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [graphPullbackY, graphMap, graphHeight, mul_zero, add_zero, sub_zero, one_mul,
      lowerGraphFlux]
    ring
  have hside (x : ℝ) : (∫ r in (0 : ℝ)..1, graphPullbackX T Jx (x,r)) =
      ∫ y in modularBottom x..T, Jx (x,y) := by
    unfold graphPullbackX
    rw [intervalIntegral.integral_const_mul]
    exact graph_vertical_integral T x (fun y => Jx (x,y))
  rw [hmass, htop, hbottom, hside, hside] at hstokes
  simpa only [sub_neg_eq_add] using hstokes

end
end ImbalancedChen.Part3.StandardModularCellCurvedStokes20261026b
