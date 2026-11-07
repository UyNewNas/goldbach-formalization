import ImbalancedChen.Part3LocalWeakH1CutoffProduct
import ImbalancedChen.Part3ActualPullbackLocalH1Transfer

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Compact H1 products of the ORIGINAL automorphic orbit pullback. The raw
pullback is only locally L2. A measurable indicator gives a genuine global
L2 extension, and the compact cutoff removes that indicator exactly,
including in both Leibniz derivatives. The actual endpoint invokes the
proved defect regularity supplier; no actual-H1 premise is assumed.
-/
namespace ImbalancedChen.Part3.CoordinateLocalH1CompactProducts20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open WeakH1ProductMollifierDerivative20261026a
open PlanarLocalWeakGradientExtraction20261026b
open LocalWeakH1CutoffProduct20261026b
open ActualPullbackLocalH1Transfer20261026b
open Gamma0ActualDefectLocalH120261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0CompactDefectMollifier20261026a Gamma0TranslatedProductWeakPDE20261026a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open NestedRectangleRealCutoff20261026b UpperRectangleMollifierGeometry20261026b

/-- The indicator is an L2 extension, not a purported global H1 function.
Only test derivatives supported in Ω are used in its local weak identities. -/
theorem indicator_hasLocalL2Gradient {Ω : Set Plane} (hΩ : MeasurableSet Ω)
    {F : Plane → ℂ} (hF : HasCoordinateLocalH1On Ω F) :
    HasLocalL2GradientOn Ω (Ω.indicator F) := by
  obtain ⟨hF,gx,gy,hgrad⟩ := hF
  have hG : MemLp (Ω.indicator F) 2 volume := (memLp_indicator_iff_restrict hΩ).2 hF
  refine ⟨hG,gx,gy,fun ψ hψ hc hs => ?_⟩
  have hpair (v : Plane) :
      (∫ p, star (directional v ψ p) * Ω.indicator F p) =
        ∫ p, star (directional v ψ p) * F p := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      by_cases hp : p ∈ Ω
      · rw [indicator_of_mem hp]
      · have hnot : p ∉ tsupport ψ := fun h => hp (hs h)
        have hd : directional v ψ p = 0 := by
          unfold directional
          rw [fderiv_of_notMem_tsupport hnot]
          simp
        simp only [hd,star_zero,zero_mul]
  obtain ⟨hx,hy⟩ := hgrad ψ hψ hc hs
  exact ⟨(hpair ex).symm ▸ hx,(hpair ey).symm ▸ hy⟩

/-- Global compact H1 cutoff product of a merely LOCAL H1 function. Both
raw product derivatives are identified, and remain compactly supported. -/
theorem coordinate_local_compact_product {Ω : Set Plane} (hΩ : MeasurableSet Ω)
    {F χ : Plane → ℂ} (hF : HasCoordinateLocalH1On Ω F)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    ∃ (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) (J : CompactH1Jet),
      J.value = (fun p => χ p * F p) ∧
      J.dx = productDerivative χ F gx ex ∧ J.dy = productDerivative χ F gy ey ∧
      tsupport J.value ⊆ tsupport χ ∧ tsupport J.dx ⊆ tsupport χ ∧ tsupport J.dy ⊆ tsupport χ := by
  obtain ⟨hG,gx,gy,hgrad⟩ := indicator_hasLocalL2Gradient hΩ hF
  have hg : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * Ω.indicator F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * Ω.indicator F p)) := hgrad
  let J := cutoffJet hG gx gy hχ hχc hχΩ hg
  have hs := cutoffJet_supports hG gx gy hχ hχc hχΩ hg
  have hχzero (p : Plane) (hp : p ∉ Ω) : χ p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp (hχΩ h))
  have hdχzero (v p : Plane) (hp : p ∉ Ω) : directional v χ p = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hp (hχΩ (tsupport_fderiv_apply_subset ℝ v h)))
  refine ⟨gx,gy,J,?_,?_,?_,hs.1,hs.2.1,hs.2.2⟩
  · funext p
    by_cases hp : p ∈ Ω
    · simp only [J,cutoffJet,indicator_of_mem hp]
    · simp only [J,cutoffJet,hχzero p hp,zero_mul]
  · funext p
    by_cases hp : p ∈ Ω
    · simp only [J,cutoffJet,productDerivative,indicator_of_mem hp]
    · simp only [J,cutoffJet,productDerivative,hχzero p hp,hdχzero ex p hp,zero_mul,add_zero]
  · funext p
    by_cases hp : p ∈ Ω
    · simp only [J,cutoffJet,productDerivative,indicator_of_mem hp]
    · simp only [J,cutoffJet,productDerivative,hχzero p hp,hdχzero ey p hp,zero_mul,add_zero]

/-- ACTUAL defect specialization. Every differential input is supplied
by actual_defect_rectangle_local_H1, and every original raw value is
identified by the proved coordinate transfer. Remaining tail premises
are literal geometric kernel legality, not H1 or PDE assumptions. -/
theorem actual_defect_compact_cutoff_H1 (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (L R c d δ : ℝ) (hLR : L ≤ R) (hcd : c ≤ d) (hc : 0 < c) (hδ : 0 < δ)
    (hKrect : upperRectangle L R c d ⊆ K) (n₀ : ℕ)
    (hheight : ∀ n p, p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ) →
      mollifierRadius (n + n₀) < p.2)
    (hlocal : ∀ n p, p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ) →
      productRectangle (n + n₀) p.1 p.2 ⊆ K)
    (hcarrier : ∀ n p, p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ) →
      productRectangle (n + n₀) p.1 p.2 ⊆ reducedCarrier N)
    {χ : Plane → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχrect : tsupport χ ⊆ Icc L R ×ˢ Icc c d) :
    ∃ (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) (J : CompactH1Jet),
      J.value = (fun p => χ p * actualPlanePullback N f p) ∧
      J.dx = productDerivative χ (actualPlanePullback N f) gx ex ∧
      J.dy = productDerivative χ (actualPlanePullback N f) gy ey ∧
      tsupport J.value ⊆ tsupport χ ∧ tsupport J.dx ⊆ tsupport χ ∧ tsupport J.dy ⊆ tsupport χ := by
  have hloc := actual_defect_rectangle_local_H1 N hK hB ha hbound hlower f hf
    L R c d δ hLR hcd hδ n₀ hheight hlocal hcarrier
  have hraw := localH1_of_local_extension (measurableSet_Icc.prod measurableSet_Icc) hloc
    (localizedPlane_eq_actual_on_rectangle N hc hbound f hKrect)
  exact coordinate_local_compact_product (measurableSet_Icc.prod measurableSet_Icc)
    hraw hχ hχc hχrect

end
end ImbalancedChen.Part3.CoordinateLocalH1CompactProducts20261026b
