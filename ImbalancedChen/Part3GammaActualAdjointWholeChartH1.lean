import ImbalancedChen.Part3GammaActualAdjointLocalizedH1

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Every native actual adjoint-domain vector, with arbitrary adjoint output,
belongs to the original actual energy form domain and has one genuine
ordinary-coordinate weak gradient on the entire upper chart. The value
and gradient are L2 on every compact positive set, and all smooth compact
positive tests are legal. Cutoffs, localizations, kernel tails, forcing,
and local witnesses are derived. No converse graph characterization is
asserted; that independent supplier is not replaced by H1 alone. -/

namespace ImbalancedChen.Part3.GammaActualAdjointWholeChartH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualFriedrichsOperator20261025a GammaActualAdjointFormRegularity20261026b
open GammaActualAdjointLocalizedH120261026b Gamma0CompactDefectMollifier20261026a
open Gamma0QuotientCellPushforward20261025a
open UpperRectangleMollifierGeometry20261026b NestedRectangleRealCutoff20261026b
open PlanarLocalWeakGradientExtraction20261026b ActualPullbackLocalH1Transfer20261026b
open LocalL2WeakGradientUniqueness20261026b CountableLocalWeakGradientPatching20261026b
open WholeUpperChartWeakH1Patching20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z

theorem actual_adjoint_every_positive_rectangle_H1 (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    (L R c d : ℝ) (hLR : L ≤ R) (hcd : c ≤ d) (hcpos : 0 < c) :
    HasCoordinateLocalH1On (Icc L R ×ˢ Icc c d) (actualPlanePullback N f) := by
  let δ : ℝ := c/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hmargin : 2*δ < c := by dsimp [δ]; linarith
  let K := upperRectangle (L-2*δ) (R+2*δ) (c-2*δ) (d+2*δ)
  let a := c-2*δ
  let B := d+2*δ
  have ha : 0 < a := by dsimp [a]; linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hK : IsCompact K := upperRectangle_isCompact _ _ _ _ ha
  have hbound : ∀ z ∈ K, z.im ≤ B := fun z hz => hz.2.2
  have hlower : ∀ z ∈ K, a ≤ z.im := fun z hz => hz.2.1
  obtain ⟨n₀, htail⟩ := exists_rectangle_mollifier_tail L R c d δ hLR hcd hδ hmargin
  have hlocal : HasLocalL2GradientOn (Icc L R ×ˢ Icc c d) (localizedPlane N K B f) :=
    actual_adjoint_localized_H1 N hfw hK hB ha hbound hlower
      (rectangleCutoff_smooth L R c d δ hLR hcd hδ)
      (rectangleCutoff_compact L R c d δ hLR hcd hδ)
      (rectangleCutoff_range L R c d δ hLR hcd hδ) _
      (fun p hp => rectangleCutoff_one L R c d δ hLR hcd hδ hp)
      n₀ (fun n => (htail n).1) (fun n => (htail n).2)
  have hinner : upperRectangle L R c d ⊆ K := by
    intro z hz
    change (L-2*δ ≤ z.re ∧ z.re ≤ R+2*δ) ∧ (c-2*δ ≤ z.im ∧ z.im ≤ d+2*δ)
    constructor <;> constructor <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]
  exact localH1_of_local_extension (measurableSet_Icc.prod measurableSet_Icc) hlocal
    (localizedPlane_eq_actual_on_rectangle N hcpos hbound f hinner)

/-- Countably many genuine rectangle local-H1 witnesses patch to one
whole-upper-chart weak gradient, without a global ordinary L2 bound. -/
theorem wholeChart_H1_of_rectangle_localH1 (F : Plane → ℂ)
    (hrect : ∀ L R c d : ℝ, L ≤ R → c ≤ d → 0 < c →
      HasCoordinateLocalH1On (Icc L R ×ˢ Icc c d) F) : HasUpperChartWeakH1 F := by
  have hclosed (n : ℕ) : HasCoordinateLocalH1On
      (Icc (-((n : ℝ)+1)) ((n : ℝ)+1) ×ˢ
        Icc (mollifierRadius (n+1)) ((n : ℝ)+1)) F := by
    have hLR : -((n : ℝ)+1) ≤ (n : ℝ)+1 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hr : mollifierRadius (n+1) ≤ (n : ℝ)+1 := by
      have hsmall : mollifierRadius (n+1) ≤ 1 := by
        unfold mollifierRadius
        have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ)+1 := by
          have hnn : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) hn
      have hn : (1 : ℝ) ≤ (n : ℝ)+1 := by
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      exact hsmall.trans hn
    exact hrect _ _ _ _ hLR hr (mollifierRadius_pos (n+1))
  have hsub (n : ℕ) : chartRectangle n ⊆
      Icc (-((n : ℝ)+1)) ((n : ℝ)+1) ×ˢ
        Icc (mollifierRadius (n+1)) ((n : ℝ)+1) := fun p hp =>
    ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2.1.le,hp.2.2.le⟩
  choose gx gy hgrad using (fun n => (hclosed n).2)
  have hF (n : ℕ) : MemLp F 2 ((volume : Measure Plane).restrict (chartRectangle n)) :=
    (hclosed n).1.mono_measure (Measure.restrict_mono_set volume (hsub n))
  have hopen (n : ℕ) : IsLocalWeakGradientOn (chartRectangle n) F (gx n) (gy n) :=
    fun ψ hψ hc hs => hgrad n ψ hψ hc (hs.trans (hsub n))
  obtain ⟨Gx,Gy,hpatch⟩ := exists_patched_local_weak_gradient chartRectangle
    chartRectangle_open F hF gx gy hopen
  refine ⟨Gx,Gy,?_,?_⟩
  · intro K hK hpos
    obtain ⟨n,hn⟩ := compact_subset_chartRectangle hK hpos
    have hm := Measure.restrict_mono_set (volume : Measure Plane) hn
    exact ⟨(hpatch n).1.mono_measure hm,(hpatch n).2.1.mono_measure hm,
      (hpatch n).2.2.1.mono_measure hm⟩
  · intro ψ hψ hc hs
    obtain ⟨n,hn⟩ := compact_subset_chartRectangle hc hs
    exact (hpatch n).2.2.2 ψ hψ hc hn

/-- Arbitrary actual adjoint graph input, not just a negative-one
deficiency vector, has ordinary-coordinate H1_loc on the whole chart. -/
theorem actual_adjoint_graph_whole_upperChart_H1 (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph) :
    HasUpperChartWeakH1 (actualPlanePullback N f) :=
  wholeChart_H1_of_rectangle_localH1 (actualPlanePullback N f)
    (actual_adjoint_every_positive_rectangle_H1 N hfw)

theorem actual_adjoint_domain_form_and_wholeChart_H1 (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).adjoint.domain) :
    (u : QuotientL2 N) ∈ actualEnergyFormDomain N ∧
      HasUpperChartWeakH1 (actualPlanePullback N (u : QuotientL2 N)) :=
  ⟨actual_adjoint_domain_le_energyFormDomain N u.property,
    actual_adjoint_graph_whole_upperChart_H1 N (LinearPMap.mem_graph _ u)⟩

end
end ImbalancedChen.Part3.GammaActualAdjointWholeChartH120261026b
