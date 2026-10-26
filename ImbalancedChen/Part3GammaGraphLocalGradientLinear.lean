import ImbalancedChen.Part3RestrictedL2WeakDerivative

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
On a fixed open positive rectangle, the actual closed graph has a
bounded COMPLEX LINEAR map to the pair of ordinary local L2 derivatives.
The value localization is proved linear through canonical AE transport.
The gradient is chosen from quantitative extraction, but native local
uniqueness proves additivity and scalar compatibility independently of
that choice. The domain has its inherited product graph norm. -/

namespace ImbalancedChen.Part3.GammaGraphLocalGradientLinear20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0CompactDefectMollifier20261026a Gamma0CompactQuotientLocalLp20261025a
open Gamma0QuotientCellPushforward20261025a CanonicalPlanarL2UnitarySourceOnly
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeightedCoordinateL220261024zz
open GammaActualInteriorSmoothGraphBudget20261026b GammaActualQuantitativeInteriorH120261026b
open PlanarLocalWeakGradientExtraction20261026b ActualPullbackLocalH1Transfer20261026b
open UpperRectangleMollifierGeometry20261026b RestrictedL2WeakDerivative20261026b

def localizationLinear (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) {B : ℝ} (hB : 0≤B) : QuotientL2 N →ₗ[ℂ] PlaneL2 where
  toFun f := (localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)
  map_add' f g := by
    have hq := (ae_restrict_iff' hK.measurableSet).1
      (quotient_ae_eq_pullback_compact N hK (Lp.coeFn_add f g))
    have hc : compactPullback N K (f+g)=ᵐ[(volume : Measure UpperHalfPlane)]
        (fun z => compactPullback N K f z+compactPullback N K g z) := by
      filter_upwards [hq] with z hz
      by_cases hzin : z∈K <;> simp [compactPullback,hzin,hz]
    have hf := forwardFunction_congr_ae hc
    apply Lp.ext
    filter_upwards [(localizedPlane_memLp N hK hB (f+g)).coeFn_toLp,
      (localizedPlane_memLp N hK hB f).coeFn_toLp,(localizedPlane_memLp N hK hB g).coeFn_toLp,
      Lp.coeFn_add ((localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f))
        ((localizedPlane_memLp N hK hB g).toLp (localizedPlane N K B g)),hf]
      with p hfg hfp hgp ho hforw
    rw [hfg,ho,hfp,hgp]
    simp only [localizedPlane]
    rw [hforw]
    by_cases hpos : p∈upperChart <;>
      simp [forwardFunction,unweightChart,chartPullback,hpos,smul_add]
  map_smul' c f := by
    have hq := (ae_restrict_iff' hK.measurableSet).1
      (quotient_ae_eq_pullback_compact N hK (Lp.coeFn_smul c f))
    have hc : compactPullback N K (c • f)=ᵐ[(volume : Measure UpperHalfPlane)]
        (fun z => c • compactPullback N K f z) := by
      filter_upwards [hq] with z hz
      by_cases hzin : z∈K <;> simp [compactPullback,hzin,hz]
    have hf := forwardFunction_congr_ae hc
    apply Lp.ext
    filter_upwards [(localizedPlane_memLp N hK hB (c • f)).coeFn_toLp,
      (localizedPlane_memLp N hK hB f).coeFn_toLp,
      Lp.coeFn_smul c ((localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)),hf]
      with p hcf hfp ho hforw
    rw [hcf,ho,hfp]
    simp only [localizedPlane]
    rw [hforw]
    by_cases hpos : p∈upperChart <;>
      simp [forwardFunction,unweightChart,chartPullback,hpos,Complex.real_smul,smul_eq_mul] <;> ring

theorem localizationLinear_bound (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) {B : ℝ} (hB : 0≤B) (f : QuotientL2 N) :
    ‖localizationLinear N hK hB f‖≤Real.sqrt (localizationSquaredConstant N K B)*‖f‖ := by
  have hC : 0≤localizationSquaredConstant N K B := by dsimp [localizationSquaredConstant]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC]
  exact localizedPlane_norm_sq_le N hK hB f

def localizationCLM (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) {B : ℝ} (hB : 0≤B) : QuotientL2 N →L[ℂ] PlaneL2 :=
  (localizationLinear N hK hB).mkContinuous (Real.sqrt (localizationSquaredConstant N K B))
    (localizationLinear_bound N hK hB)

structure PositiveRectangle where
  L R c d : ℝ
  hLR : L≤R
  hcd : c≤d
  hc : 0<c

namespace PositiveRectangle
def region (r : PositiveRectangle) : Set Plane := Ioo r.L r.R ×ˢ Ioo r.c r.d
def closedRegion (r : PositiveRectangle) : Set Plane := Icc r.L r.R ×ˢ Icc r.c r.d
def outer (r : PositiveRectangle) : Set UpperHalfPlane :=
  upperRectangle (r.L-r.c/2) (r.R+r.c/2) (r.c/2) (r.d+r.c/2)
def height (r : PositiveRectangle) : ℝ := r.d+r.c/2
theorem region_open (r : PositiveRectangle) : IsOpen r.region := isOpen_Ioo.prod isOpen_Ioo
theorem region_subset (r : PositiveRectangle) : r.region⊆r.closedRegion :=
  fun p hp => ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2.1.le,hp.2.2.le⟩
theorem outer_compact (r : PositiveRectangle) : IsCompact r.outer :=
  upperRectangle_isCompact _ _ _ _ (half_pos r.hc)
theorem height_nonneg (r : PositiveRectangle) : 0≤r.height := by
  dsimp [height]
  linarith [r.hc,r.hcd]
theorem outer_bound (r : PositiveRectangle) : ∀ z∈r.outer,z.im≤r.height := fun z hz => hz.2.2
theorem inner_subset (r : PositiveRectangle) : upperRectangle r.L r.R r.c r.d⊆r.outer := by
  intro z hz
  change (r.L-r.c/2≤z.re ∧ z.re≤r.R+r.c/2) ∧ (r.c/2≤z.im ∧ z.im≤r.d+r.c/2)
  constructor <;> constructor <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2,r.hc]
end PositiveRectangle

abbrev ActualGraph (N : ℕ) [NeZero N] := (actualClosedGammaMaass N).graph
abbrev LocalGradientPair (r : PositiveRectangle) := LocalL2 r.region × LocalL2 r.region

def localValueCLM (N : ℕ) [NeZero N] (r : PositiveRectangle) : QuotientL2 N →L[ℂ] LocalL2 r.region :=
  (restrictionCLM r.region).comp (localizationCLM N r.outer_compact r.height_nonneg)

def graphValueCLM (N : ℕ) [NeZero N] (r : PositiveRectangle) : ActualGraph N →L[ℂ] LocalL2 r.region :=
  (localValueCLM N r).comp ((ContinuousLinearMap.fst ℂ (QuotientL2 N) (QuotientL2 N)).comp
    (actualClosedGammaMaass N).graph.subtypeL)

theorem localValue_coe_ae (N : ℕ) [NeZero N] (r : PositiveRectangle) (f : QuotientL2 N) :
    (localValueCLM N r f : Plane → ℂ)=ᵐ[(volume : Measure Plane).restrict r.region]
      actualPlanePullback N f := by
  have hloc := ae_restrict_of_ae (localizedPlane_memLp N r.outer_compact r.height_nonneg f).coeFn_toLp
  have heq := localizedPlane_eq_actual_on_rectangle N r.hc r.outer_bound f r.inner_subset
  have hmem : ∀ᵐ p ∂(volume : Measure Plane).restrict r.region,p∈r.region :=
    ae_restrict_mem r.region_open.measurableSet
  filter_upwards [restriction_coe_ae r.region (localizationCLM N r.outer_compact r.height_nonneg f),
    hloc,hmem] with p hp hq hm
  rw [hp,hq]
  exact heq p (r.region_subset hm)

def graphGradientConstant (N : ℕ) (r : PositiveRectangle) : ℝ :=
  interiorGraphConstant N r.L r.R r.c r.d r.hLR r.hcd r.hc

theorem graphGradientConstant_nonneg (N : ℕ) (r : PositiveRectangle) :
    0≤graphGradientConstant N r := by
  have hd := cutoffDerivativeCap_nonneg
    (rectangleCutoff r.L r.R r.c r.d (r.c/4) r.hLR r.hcd
      (by exact div_pos r.hc (by norm_num)))
  dsimp [graphGradientConstant,interiorGraphConstant,localSmoothGradientConstant,localizationSquaredConstant]
  positivity

theorem exists_graph_local_gradient (N : ℕ) [NeZero N] (r : PositiveRectangle) (p : ActualGraph N) :
    ∃ G : LocalGradientPair r,
      ‖G‖≤Real.sqrt (2*graphGradientConstant N r)*‖p‖ ∧
      HasRestrictedDerivative r.region (graphValueCLM N r p) G.1 xDirection ∧
      HasRestrictedDerivative r.region (graphValueCLM N r p) G.2 yDirection := by
  obtain ⟨_,gx,gy,henergy,hweak⟩ := actual_closed_rectangle_gradient_energy N p.property
    r.L r.R r.c r.d r.hLR r.hcd r.hc
  let X := restrictionCLM r.region gx
  let Y := restrictionCLM r.region gy
  have hx := restricted_derivative_of_global_tests r.region_open.measurableSet
    (actualPlanePullback N p.val.1) (localValueCLM N r p.val.1) (localValue_coe_ae N r p.val.1)
    gx xDirection (fun ψ hψ hc hs => (hweak ψ hψ hc (hs.trans r.region_subset)).1)
  have hy := restricted_derivative_of_global_tests r.region_open.measurableSet
    (actualPlanePullback N p.val.1) (localValueCLM N r p.val.1) (localValue_coe_ae N r p.val.1)
    gy yDirection (fun ψ hψ hc hs => (hweak ψ hψ hc (hs.trans r.region_subset)).2)
  have hX := mul_self_le_mul_self (norm_nonneg _) (restriction_norm_le r.region gx)
  have hY := mul_self_le_mul_self (norm_nonneg _) (restriction_norm_le r.region gy)
  simp only [← pow_two] at hX hY
  have hpair : ‖(X,Y)‖^2≤‖gx‖^2+‖gy‖^2 := by
    rw [Prod.norm_def]
    by_cases hxy : ‖X‖≤‖Y‖
    · rw [max_eq_right hxy]
      nlinarith [sq_nonneg ‖gx‖]
    · rw [max_eq_left (le_of_not_ge hxy)]
      nlinarith [sq_nonneg ‖gy‖]
  have hf : ‖p.val.1‖≤‖p‖ := le_max_left _ _
  have hw : ‖p.val.2‖≤‖p‖ := le_max_right _ _
  have hsum : ‖p.val.1‖^2+‖p.val.2‖^2≤2*‖p‖^2 := by
    have hf2 := mul_self_le_mul_self (norm_nonneg _) hf
    have hw2 := mul_self_le_mul_self (norm_nonneg _) hw
    nlinarith
  have hC := graphGradientConstant_nonneg N r
  have hbound : ‖(X,Y)‖^2≤2*graphGradientConstant N r*‖p‖^2 := by
    have hm := mul_le_mul_of_nonneg_left hsum hC
    calc
      _ ≤ ‖gx‖^2+‖gy‖^2 := hpair
      _ ≤ graphGradientConstant N r*(‖p.val.1‖^2+‖p.val.2‖^2) := henergy
      _ ≤ graphGradientConstant N r*(2*‖p‖^2) := hm
      _ = _ := by ring
  have hn : ‖(X,Y)‖≤Real.sqrt (2*graphGradientConstant N r)*‖p‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num) hC)]
    exact hbound
  exact ⟨(X,Y),hn,hx,hy⟩

def chosenGraphGradient (N : ℕ) [NeZero N] (r : PositiveRectangle) (p : ActualGraph N) : LocalGradientPair r :=
  Classical.choose (exists_graph_local_gradient N r p)

theorem chosenGraphGradient_spec (N : ℕ) [NeZero N] (r : PositiveRectangle) (p : ActualGraph N) :
    ‖chosenGraphGradient N r p‖≤Real.sqrt (2*graphGradientConstant N r)*‖p‖ ∧
      HasRestrictedDerivative r.region (graphValueCLM N r p) (chosenGraphGradient N r p).1 xDirection ∧
      HasRestrictedDerivative r.region (graphValueCLM N r p) (chosenGraphGradient N r p).2 yDirection :=
  Classical.choose_spec (exists_graph_local_gradient N r p)

def graphGradientLinear (N : ℕ) [NeZero N] (r : PositiveRectangle) : ActualGraph N →ₗ[ℂ] LocalGradientPair r where
  toFun := chosenGraphGradient N r
  map_add' p q := by
    apply Prod.ext
    · apply restricted_derivative_unique r.region_open (chosenGraphGradient_spec N r (p+q)).2.1
      simpa only [map_add] using restricted_derivative_add
        (chosenGraphGradient_spec N r p).2.1 (chosenGraphGradient_spec N r q).2.1
    · apply restricted_derivative_unique r.region_open (chosenGraphGradient_spec N r (p+q)).2.2
      simpa only [map_add] using restricted_derivative_add
        (chosenGraphGradient_spec N r p).2.2 (chosenGraphGradient_spec N r q).2.2
  map_smul' c p := by
    apply Prod.ext
    · apply restricted_derivative_unique r.region_open (chosenGraphGradient_spec N r (c • p)).2.1
      simpa only [map_smul] using restricted_derivative_smul
        (chosenGraphGradient_spec N r p).2.1 c
    · apply restricted_derivative_unique r.region_open (chosenGraphGradient_spec N r (c • p)).2.2
      simpa only [map_smul] using restricted_derivative_smul
        (chosenGraphGradient_spec N r p).2.2 c

def graphGradientCLM (N : ℕ) [NeZero N] (r : PositiveRectangle) : ActualGraph N →L[ℂ] LocalGradientPair r :=
  (graphGradientLinear N r).mkContinuous (Real.sqrt (2*graphGradientConstant N r))
    (fun p => (chosenGraphGradient_spec N r p).1)

end
end ImbalancedChen.Part3.GammaGraphLocalGradientLinear20261026b
