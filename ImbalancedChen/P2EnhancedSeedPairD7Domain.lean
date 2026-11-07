import ImbalancedChen.P2EnhancedSeedPairD6Primitive

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal D7 of second-seed-certified-finite-feedback.tex. The support wall
is retained with its correct weak inequality. The two exact slices retain
strict prime order; no arithmetic endpoint is discarded as null. Native
same-Q residual, physical cutoff, stable ceiling and both square tests are
proved before any integral boundary replacement. No enhanced count bound,
lambda, J2omega, certificate result or numerical target is an assumption.
-/

namespace ImbalancedChen.P2EnhancedSeedPairD7Domain

noncomputable section

open Set MeasureTheory Classical
open P2EnhancedSeedSingletonPrimitive (S s0 parameters seedUpper)
open P5OriginalActionMassBound (Point)

def uLo : ℝ := 50/227
def uHi : ℝ := 100/353
def supportStart : ℝ := 1265/5648
def boundaryCut : ℝ := 5/21
def supportLine (u : ℝ) : ℝ := 1-(16/5)*u
def lowerEndpoint (u : ℝ) : ℝ := max u (supportLine u)
def D7 : Set Point := P5OriginalActionMassBound.W2Pair7 parameters
def profile (x : Point) : ℝ := (1-x 0-x 1)/x 0
def supportedD7 : Set Point := D7 ∩ {x | profile x ∈ Icc (1 : ℝ) S}
def closedRectangle : Set Point := Icc ![uLo,uLo] ![uHi,uHi]
def feedback (J : ℝ) (x : Point) : ℝ :=
  seedUpper J (profile x)*P2EnhancedSeedPairD6Primitive.pairKernel x

theorem D7_dictionary (x : Point) :
    x ∈ D7 ↔ uLo<x 0 ∧ x 0<x 1 ∧ x 1<uHi := by
  norm_num [D7,P5OriginalActionMassBound.W2Pair7,parameters,
    P5OriginalActionMassBound.a0,P5OriginalActionMassBound.a1,uLo,uHi]

theorem D7_subset_closed : D7 ⊆ closedRectangle := by
  intro x hx
  obtain ⟨hu,huv,hv⟩ := (D7_dictionary x).mp hx
  constructor <;> intro i <;> fin_cases i
  · exact hu.le
  · exact (hu.trans huv).le
  · exact (huv.trans hv).le
  · exact hv.le

theorem closed_geometry {x : Point} (hx : x ∈ closedRectangle) :
    0<x 0 ∧ 0<x 1 ∧ 0<1-x 0-x 1 := by
  have hu0 := hx.1 0
  have hv0 := hx.1 1
  have hu1 := hx.2 0
  have hv1 := hx.2 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,uLo,uHi] at hu0 hv0 hu1 hv1
  constructor
  · linarith only [hu0]
  constructor
  · linarith only [hv0]
  · linarith only [hu1,hv1]

theorem D7_retained_gates {x : Point} (hx : x ∈ D7) :
    uLo<x 0 ∧ x 0<x 1 ∧ 2*x 1<1 ∧ x 1+2*x 0<1 := by
  obtain ⟨hu,huv,hv⟩ := (D7_dictionary x).mp hx
  dsimp [uHi] at hv
  exact ⟨hu,huv,by linarith only [hv],by linarith only [huv,hv]⟩

theorem D7_actual_profile_gt_one {x : Point} (hx : x ∈ D7) : 1<profile x := by
  have hg := closed_geometry (D7_subset_closed hx)
  have hgate := (D7_retained_gates hx).2.2.2
  exact (lt_div_iff₀ hg.1).mpr (by linarith only [hgate])

theorem profile_eq_original (x : Point) :
    profile x=P5OriginalFeedbackDomains.movingPairProfile x := rfl

theorem support_dictionary (x : Point) : x ∈ supportedD7 ↔
    uLo<x 0 ∧ x 0<x 1 ∧ x 1<uHi ∧ supportLine (x 0)≤x 1 := by
  constructor
  · rintro ⟨hx,hp⟩
    obtain ⟨hu,huv,hv⟩ := (D7_dictionary x).mp hx
    have hu0 := (closed_geometry (D7_subset_closed hx)).1
    have h := (div_le_iff₀ hu0).mp hp.2
    dsimp [S,supportLine] at *
    exact ⟨hu,huv,hv,by linarith only [h]⟩
  · rintro ⟨hu,huv,hv,hs⟩
    have hx : x ∈ D7 := (D7_dictionary x).mpr ⟨hu,huv,hv⟩
    have hu0 := (closed_geometry (D7_subset_closed hx)).1
    refine ⟨hx,(D7_actual_profile_gt_one hx).le,?_⟩
    apply (div_le_iff₀ hu0).mpr
    dsimp [S,supportLine] at *
    linarith only [hs]

/-- Exact slicing, including the support wall and the junction u=5/21. -/
theorem supported_vec (u v : ℝ) : (![u,v] : Point) ∈ supportedD7 ↔
    (u ∈ Ioo supportStart boundaryCut ∧ v ∈ Ico (supportLine u) uHi) ∨
    (u ∈ Ico boundaryCut uHi ∧ v ∈ Ioo u uHi) := by
  rw [support_dictionary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,mem_Ioo,mem_Ico]
  dsimp [uLo,uHi,supportStart,boundaryCut,supportLine]
  constructor
  · rintro ⟨hu,huv,hv,hs⟩
    by_cases hc : u<(5/21 : ℝ)
    · left
      exact ⟨⟨by linarith only [hv,hs],hc⟩,hs,hv⟩
    · right
      exact ⟨⟨le_of_not_gt hc,by linarith only [huv,hv]⟩,huv,hv⟩
  · rintro (⟨⟨hu,hc⟩,hs,hv⟩ | ⟨⟨hc,hu⟩,huv,hv⟩)
    · exact ⟨by linarith only [hu],by linarith only [hc,hs],hv,hs⟩
    · exact ⟨by linarith only [hc],huv,hv,by linarith only [hc,huv]⟩

theorem lowerEndpoint_first {u : ℝ} (hu : u≤boundaryCut) :
    lowerEndpoint u=supportLine u := by
  apply max_eq_right
  dsimp [boundaryCut,supportLine] at *
  linarith only [hu]

theorem lowerEndpoint_second {u : ℝ} (hu : boundaryCut≤u) :
    lowerEndpoint u=u := by
  apply max_eq_left
  dsimp [boundaryCut,supportLine] at *
  linarith only [hu]

theorem support_outer_bounds {x : Point} (hx : x ∈ supportedD7) :
    x 0 ∈ Ioo supportStart uHi := by
  obtain ⟨hu,huv,hv,hs⟩ := (support_dictionary x).mp hx
  dsimp [supportLine,supportStart] at *
  dsimp [uHi] at hv ⊢
  exact ⟨by linarith only [hs,hv],huv.trans hv⟩

theorem measurableSet_D7 : MeasurableSet D7 :=
  P5OriginalActionMassBound.W2Pair7_measurable parameters

theorem measurable_profile : Measurable profile := by
  exact (((measurable_const.sub (measurable_pi_apply 0)).sub
    (measurable_pi_apply 1)).div (measurable_pi_apply 0))

theorem measurableSet_supportedD7 : MeasurableSet supportedD7 :=
  measurableSet_D7.inter (measurable_profile measurableSet_Icc)

/-- Same total Q is represented by L and alpha throughout. The residual
L(1-u-v), actual physical cutoff Lu, seed comparison and old ceiling are
distinct quantities. No new comparison licence for the parent is inserted. -/
theorem D7_cutoff_inheritance {L chi alpha : ℝ} (hL : 0<L)
    (hchi : L/S<chi) (ha : 2≤alpha) {x : Point} (hx : x ∈ supportedD7) :
    0<L*(1-x 0-x 1) ∧
      (L*(1-x 0-x 1))/S≤L*x 0 ∧
      (L*(1-x 0-x 1))/profile x=L*x 0 ∧
      L*x 0<L*x 1 ∧ L*x 1<L/S ∧ L/S<chi ∧
      2*x 1<1 ∧ x 1+2*x 0<1 ∧
      alpha≤P5OriginalFeedbackDomains.pairChildAlpha alpha x := by
  have hd := (D7_dictionary x).mp hx.1
  have hg := closed_geometry (D7_subset_closed hx.1)
  have hs := (support_dictionary x).mp hx
  have hS : 0<S := by norm_num [S]
  have hc : (1-x 0-x 1)/S≤x 0 := by
    apply (div_le_iff₀ hS).mpr
    dsimp [supportLine,S] at hs ⊢
    linarith only [hs.2.2.2]
  have hcomp := mul_le_mul_of_nonneg_left hc hL.le
  have hphysical : (L*(1-x 0-x 1))/profile x=L*x 0 := by
    dsimp [profile]
    field_simp [hg.1.ne',hg.2.2.ne']
    <;> ring
  have hv : x 1<1/S := by
    dsimp [uHi] at hd
    dsimp [S]
    linarith only [hd.2.2]
  have hcut := mul_lt_mul_of_pos_left hv hL
  have halpha := P5OriginalFeedbackDomains.alpha_transport_mono (by linarith : 1≤alpha)
    hg.2.2 (show 1-x 0-x 1≤1 by linarith only [hg.1,hg.2.1])
  have hgate := D7_retained_gates hx.1
  refine ⟨mul_pos hL hg.2.2,?_,hphysical,mul_lt_mul_of_pos_left hd.2.1 hL,
    ?_,hchi,hgate.2.2.1,hgate.2.2.2,halpha⟩
  · convert hcomp using 1 <;> ring
  · convert hcut using 1 <;> ring

theorem feedback_eq_supported_indicator (J : ℝ) {x : Point} (hx : x ∈ D7) :
    feedback J x=supportedD7.indicator
      (fun x => J*P2EnhancedSeedPairD6Primitive.pairKernel x) x := by
  by_cases hp : profile x ∈ Icc (1 : ℝ) S
  · rw [feedback,seedUpper,indicator_of_mem hp,indicator_of_mem ⟨hx,hp⟩]
  · have hs : x ∉ supportedD7 := fun h => hp h.2
    rw [feedback,seedUpper,indicator_of_notMem hp,indicator_of_notMem hs,zero_mul]

end
end ImbalancedChen.P2EnhancedSeedPairD7Domain
