import ImbalancedChen.Part3HilbertWeakGradientEnergyBound
import ImbalancedChen.Part3GammaActualInteriorSmoothGraphBudget

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Quantitative interior H1 for arbitrary native actual adjoint/closed graph
pairs. The displayed geometric constant is fixed by N and the positive
rectangle before f,w or mollifier scale. Exact Hilbert lower semicontinuity
passes the proved smooth bound to actual literal weak-gradient witnesses.
No energy, weak-gradient, H1, localization or kernel-tail budget is supplied.
-/

namespace ImbalancedChen.Part3.GammaActualQuantitativeInteriorH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open GammaActualMinimalDefectVanishes20261026b Gamma0CompactDefectMollifier20261026a
open Gamma0SmoothedCoordinateWeakPDE20261026a Gamma0SmoothedPotentialL2Budget20261026a
open NestedRectangleRealCutoff20261026b Gamma0InteriorSmoothedCaccioppoli20261026b
open PlanarLocalWeakGradientExtraction20261026b LocalL2WeakGradientUniqueness20261026b
open Gamma0ActualDefectLocalH120261026b ActualPullbackLocalH1Transfer20261026b
open UpperRectangleMollifierGeometry20261026b HilbertWeakGradientEnergyBound20261026b
open GammaActualInteriorSmoothGraphBudget20261026b

/-- Quantitative version of the genuine compact-test limit, retaining
the exact sum-of-squared-gradient bound through the extracted subsequence. -/
theorem local_gradient_with_energy_bound
    (F : Plane → ℂ) (hF : MemLp F 2 volume)
    (U : ℕ → Plane → ℂ) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hU2 : ∀ n, MemLp (U n) 2 volume)
    (hvalue : Tendsto (fun n => (hU2 n).toLp (U n)) atTop (𝓝 (hF.toLp F)))
    {θ : Plane → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ n, ‖weightedGradientL2 hθ hc (hU n) xDirection‖^2+
      ‖weightedGradientL2 hθ hc (hU n) yDirection‖^2 ≤ C)
    (Ω : Set Plane) (hone : ∀ p ∈ Ω, θ p=1) :
    ∃ gx gy : PlaneL2, ‖gx‖^2+‖gy‖^2 ≤ C ∧ IsLocalWeakGradientOn Ω F gx gy := by
  let X n := weightedGradientL2 hθ hc (hU n) xDirection
  let Y n := weightedGradientL2 hθ hc (hU n) yDirection
  obtain ⟨gx,gy,hbound,σ,hσ,hxl,hyl⟩ := exists_weak_pair_with_energy_bound X Y C hC henergy
  refine ⟨gx,gy,hbound,fun ψ hψ hψc hψΩ => ?_⟩
  have honeψ : ∀ p ∈ tsupport ψ, θ p=1 := fun p hp => hone p (hψΩ hp)
  have hψ2 := hψ.continuous.memLp_of_hasCompactSupport hψc (p := (2 : ℝ≥0∞))
  have hlim (v : Plane) (G : PlaneL2)
      (hg : Tendsto (fun n => inner ℂ (hψ2.toLp ψ)
        (weightedGradientL2 hθ hc (hU (σ n)) v)) atTop (𝓝 (inner ℂ (hψ2.toLp ψ) G))) :
      (∫ p, star (ψ p)*G p)=-(∫ p,star (directional v ψ p)*F p) := by
    let hd := (directional_cinfty hψ v).continuous.memLp_of_hasCompactSupport
      (directional_hasCompactSupport hψc v) (p := (2 : ℝ≥0∞))
    have hr := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => hd.toLp (directional v ψ))
      atTop (𝓝 (hd.toLp (directional v ψ)))).inner (hvalue.comp hσ.tendsto_atTop)).neg
    have heq : (fun n => inner ℂ (hψ2.toLp ψ) (weightedGradientL2 hθ hc (hU (σ n)) v))=
        (fun n => -inner ℂ (hd.toLp (directional v ψ)) ((hU2 (σ n)).toLp (U (σ n)))) :=
      funext fun n => weightedGradient_green hθ hc (hU (σ n)) (hU2 (σ n)) hψ hψc honeψ v
    rw [← heq] at hr
    have he := tendsto_nhds_unique hg hr
    rw [inner_toLp_Lp_integral,inner_toLp_integral] at he
    exact he
  exact ⟨hlim xDirection gx (hxl _),hlim yDirection gy (hyl _)⟩

def interiorGraphConstant (N : ℕ) (L R c d : ℝ)
    (hLR : L ≤ R) (hcd : c ≤ d) (hc : 0 < c) : ℝ :=
  let δ := c/4
  let hδ : 0 < δ := by dsimp [δ]; positivity
  localSmoothGradientConstant N
    (upperRectangle (L-2*δ) (R+2*δ) (c-2*δ) (d+2*δ)) (d+2*δ) (c-2*δ)
    (rectangleCutoff L R c d δ hLR hcd hδ)

/-- Explicit geometric local elliptic estimate for EVERY actual adjoint
graph pair, with genuine weak-gradient witnesses of the original pullback.
The witnesses are global L2 extensions whose norm bounds imply the local
rectangle gradient budget. No caller norm, energy or PDE estimate occurs. -/
theorem actual_adjoint_rectangle_gradient_energy (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    (L R c d : ℝ) (hLR : L ≤ R) (hcd : c ≤ d) (hcpos : 0 < c) :
    MemLp (actualPlanePullback N f) 2 ((volume : Measure Plane).restrict (Icc L R ×ˢ Icc c d)) ∧
    ∃ gx gy : PlaneL2,
      ‖gx‖^2+‖gy‖^2 ≤ interiorGraphConstant N L R c d hLR hcd hcpos*(‖f‖^2+‖w‖^2) ∧
      IsLocalWeakGradientOn (Icc L R ×ˢ Icc c d) (actualPlanePullback N f) gx gy := by
  let δ : ℝ := c/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hmargin : 2*δ<c := by dsimp [δ]; linarith
  let K := upperRectangle (L-2*δ) (R+2*δ) (c-2*δ) (d+2*δ)
  let a := c-2*δ
  let B := d+2*δ
  have ha : 0<a := by dsimp [a]; linarith
  have hB : 0≤B := by dsimp [B]; linarith
  have hK : IsCompact K := upperRectangle_isCompact _ _ _ _ ha
  have hbound : ∀ z∈K,z.im≤B := fun z hz => hz.2.2
  have hlower : ∀ z∈K,a≤z.im := fun z hz => hz.2.1
  let θ := rectangleCutoff L R c d δ hLR hcd hδ
  have hθ : ContDiff ℝ ∞ θ := rectangleCutoff_smooth L R c d δ hLR hcd hδ
  have hθc : HasCompactSupport θ := rectangleCutoff_compact L R c d δ hLR hcd hδ
  obtain ⟨n₀,htail⟩ := exists_rectangle_mollifier_tail L R c d δ hLR hcd hδ hmargin
  let F := localizedPlane N K B f
  have hF : MemLp F 2 volume := localizedPlane_memLp N hK hB f
  let U n := actualProductSmooth N K B f (n+n₀)
  have hU (n : ℕ) : ContDiff ℝ ∞ (U n) := actualProductSmooth_cinfty N hK hB f _
  have hU2 (n : ℕ) : MemLp (U n) 2 volume := actualProductSmooth_memLp N hK hB hbound f _
  have hadd : StrictMono (fun n : ℕ => n+n₀) := fun i j hij => Nat.add_lt_add_right hij n₀
  have hvalue : Tendsto (fun n => (hU2 n).toLp (U n)) atTop (𝓝 (hF.toLp F)) :=
    (actualProductSmooth_strong_L2 N hK hB hbound f).comp hadd.tendsto_atTop
  let C := localSmoothGradientConstant N K B a θ*(‖f‖^2+‖w‖^2)
  have hC : 0≤C := by
    have hd := cutoffDerivativeCap_nonneg θ
    dsimp [C,localSmoothGradientConstant,localizationSquaredConstant]
    positivity
  have he (n : ℕ) : ‖weightedGradientL2 hθ hθc (hU n) xDirection‖^2+
      ‖weightedGradientL2 hθ hθc (hU n) yDirection‖^2≤C := by
    have h := actual_adjoint_smooth_gradient_budget N hfw hK hB ha hbound hlower
      hθ hθc (rectangleCutoff_range L R c d δ hLR hcd hδ) (n+n₀)
      ((htail n).1) ((htail n).2)
    rw [weightedEnergy_eq_L2 hθ hθc (hU n)] at h
    exact h
  obtain ⟨gx,gy,henergy,hweak⟩ := local_gradient_with_energy_bound F hF U hU hU2 hvalue
    hθ hθc C hC he (Icc L R ×ˢ Icc c d)
    (fun p hp => rectangleCutoff_one L R c d δ hLR hcd hδ hp)
  have hinner : upperRectangle L R c d⊆K := by
    intro z hz
    change (L-2*δ≤z.re ∧ z.re≤R+2*δ) ∧ (c-2*δ≤z.im ∧ z.im≤d+2*δ)
    constructor <;> constructor <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]
  have heq := localizedPlane_eq_actual_on_rectangle N hcpos hbound f hinner
  have hraw := localH1_of_local_extension (measurableSet_Icc.prod measurableSet_Icc)
    (show HasLocalL2GradientOn (Icc L R ×ˢ Icc c d) F from ⟨hF,gx,gy,hweak⟩) heq
  refine ⟨hraw.1,gx,gy,henergy,fun ψ hψ hc hs => ?_⟩
  have hp (v : Plane) : (∫ p,star (directional v ψ p)*F p)=
      ∫ p,star (directional v ψ p)*actualPlanePullback N f p := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      by_cases hpin : p∈tsupport ψ
      · rw [heq p (hs hpin)]
      · unfold directional
        rw [fderiv_of_notMem_tsupport hpin]
        simp
  obtain ⟨hx,hy⟩ := hweak ψ hψ hc hs
  exact ⟨(hp xDirection) ▸ hx,(hp yDirection) ▸ hy⟩

theorem actual_closed_rectangle_gradient_energy (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w)∈(actualClosedGammaMaass N).graph)
    (L R c d : ℝ) (hLR : L≤R) (hcd : c≤d) (hc : 0<c) :
    MemLp (actualPlanePullback N f) 2 ((volume : Measure Plane).restrict (Icc L R ×ˢ Icc c d)) ∧
    ∃ gx gy : PlaneL2,
      ‖gx‖^2+‖gy‖^2 ≤ interiorGraphConstant N L R c d hLR hcd hc*(‖f‖^2+‖w‖^2) ∧
      IsLocalWeakGradientOn (Icc L R ×ˢ Icc c d) (actualPlanePullback N f) gx gy := by
  apply actual_adjoint_rectangle_gradient_energy N ?_ L R c d hLR hcd hc
  rw [LinearPMap.isSelfAdjoint_def.mp (actual_minimal_closure_isSelfAdjoint N)]
  exact hfw

end
end ImbalancedChen.Part3.GammaActualQuantitativeInteriorH120261026b
