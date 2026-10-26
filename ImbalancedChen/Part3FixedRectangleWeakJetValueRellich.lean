import ImbalancedChen.Part3FixedRectangleH1OriginalCore
import ImbalancedChen.Part3PositiveRectanglePhysicalRellich
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Rellich for the VALUE projection of the genuine nonsmooth closed native
rectangle-H1 jet model. Smooth physical Rellich is an immutable proved
supplier. A literal larger positive affine frame and one explicit uniform
margin contain every normalized finite approximation. Its actual smooth
H1 budget is bounded by three times the native jet norm squared. Genuine
jet convergence pays the nonsmooth closure step before compact-operator
compactness is concluded. No Rellich, approximation, margin or uniform
smooth-budget premise is assumed.
-/
namespace ImbalancedChen.Part3.FixedRectangleWeakJetValueRellich20261026b
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology UpperHalfPlane
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open SupportedH1FiniteTensorDensity20261026a ProductKernelL2TranslationAverage20261026a
open WeakH1ProductMollifierDerivative20261026a Gamma0SmoothCompactTensorCore20261025a
open MaassWeakOperatorCore20261024zz CompactH1QuotientEnergyLimit20261026b
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b
open FixedRectangleH1JetSpace20261026b FixedRectangleH1EnergyLift20261026b
open FixedRectangleH1OriginalCore20261026b
open PositiveRectangleAffineNormalization20261026b PositiveRectanglePhysicalRellich20261026b

/-- Literal ordinary planar value component, without weights or quotient. -/
def valueProjection (L R a b : ℝ) : RectangleJet L R a b →L[ℂ]
    ProductKernelL2TranslationAverage20261026a.PlaneL2 :=
  (ContinuousLinearMap.proj (0 : Fin 3)).comp (rectangleH1Jets L R a b).subtypeL

@[simp] theorem valueProjection_apply (L R a b : ℝ) (v : RectangleJet L R a b) :
    valueProjection L R a b v = v.val 0 := rfl

/-- The approximant source box is [L-1,R+1]×[a/2,b+1]. This strictly
larger physical frame has positive bottom a/4 and explicit side lengths. -/
def rellichFrame (L R a b : ℝ) (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) : Rectangle where
  left := L-2
  bottom := a/4
  width := R-L+4
  height := b+2-a/4
  bottom_pos := by linarith
  width_pos := by linarith
  height_pos := by linarith

def rellichMargin (F : Rectangle) : ℝ := min (1/F.width) (min ((F.bottom)/F.height) (1/F.height))

theorem rellichMargin_pos (F : Rectangle) : 0 < rellichMargin F :=
  lt_min (div_pos (by norm_num) F.width_pos)
    (lt_min (div_pos F.bottom_pos F.height_pos) (div_pos (by norm_num) F.height_pos))

/-- All four source-to-frame boundary margins are proved before the
physical smooth Rellich theorem is applied. -/
theorem approximant_source_subset_region (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    rect (L-1) (R+1) (a/2) (b+1) ⊆
      region (rellichFrame L R a b hLR ha hab) (rellichMargin (rellichFrame L R a b hLR ha hab)) := by
  let F := rellichFrame L R a b hLR ha hab
  let δ := rellichMargin F
  have hx : δ*F.width ≤ 1 := (le_div_iff₀ F.width_pos).mp (min_le_left _ _)
  have hylo : δ*F.height ≤ F.bottom := (le_div_iff₀ F.height_pos).mp
    ((min_le_right _ _).trans (min_le_left _ _))
  have hyhi : δ*F.height ≤ 1 := (le_div_iff₀ F.height_pos).mp
    ((min_le_right _ _).trans (min_le_right _ _))
  intro p hp
  refine ⟨F.inverse p,?_,F.affine_inverse p⟩
  change ((δ ≤ (p.1-F.left)/F.width ∧ (p.1-F.left)/F.width ≤ 1-δ) ∧
    (δ ≤ (p.2-F.bottom)/F.height ∧ (p.2-F.bottom)/F.height ≤ 1-δ))
  dsimp [F,rellichFrame] at hx hylo hyhi ⊢
  constructor
  · constructor
    · apply (le_div_iff₀ (show 0 < R-L+4 by linarith)).mpr
      linarith [hp.1.1]
    · apply (div_le_iff₀ (show 0 < R-L+4 by linarith)).mpr
      nlinarith [hp.1.2]
  · constructor
    · apply (le_div_iff₀ (show 0 < b+2-a/4 by linarith)).mpr
      linarith [hp.2.1]
    · apply (div_le_iff₀ (show 0 < b+2-a/4 by linarith)).mpr
      nlinarith [hp.2.2]

def approximantRellichSeed (L R a b : ℝ) (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    {F : CompactC2ProductMollifier20261026a.Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hs : tsupport F ⊆ rect (L-1) (R+1) (a/2) (b+1)) :
    RectangleSeed (rellichFrame L R a b hLR ha hab) (rellichMargin (rellichFrame L R a b hLR ha hab)) where
  function := F
  smooth := hF.of_le (by simp)
  support_subset := subset_tsupport.trans (hs.trans (approximant_source_subset_region L R a b hLR ha hab))

theorem approximantRellichSeed_value (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    {F : CompactC2ProductMollifier20261026a.Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ rect (L-1) (R+1) (a/2) (b+1)) :
    physical (approximantRellichSeed L R a b hLR ha hab hF hs) = smoothJetClass hF hc 0 := by
  apply Lp.ext
  exact (hF.continuous.memLp_of_hasCompactSupport _).coeFn_toLp.trans
    (partial_memLp hF hc (firstIndex 0)).coeFn_toLp.symm

/-- The immutable physical H1 ball contains the actual smooth native jet
with the DERIVED constant 3, including both genuine partial derivatives. -/
theorem approximantRellichSeed_h1_bound (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    {F : CompactC2ProductMollifier20261026a.Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ rect (L-1) (R+1) (a/2) (b+1)) :
    ‖physical (approximantRellichSeed L R a b hLR ha hab hF hs)‖^2 +
      energy (approximantRellichSeed L R a b hLR ha hab hF hs) ≤ 3 * ‖smoothJetClass hF hc‖^2 := by
  have hx : CompactRectanglePhysicalRellich20261026a.partial F 0 =
      fun p => partialJet (firstIndex 1) F p := by
    funext p
    rw [partialJet_eq_mixedJet hF]
    rfl
  have hy : CompactRectanglePhysicalRellich20261026a.partial F 1 =
      fun p => partialJet (firstIndex 2) F p := by
    funext p
    rw [partialJet_eq_mixedJet hF]
    rfl
  rw [approximantRellichSeed_value L R a b hLR ha hab hF hc hs]
  change ‖smoothJetClass hF hc 0‖^2 +
    ((∫ p, ‖CompactRectanglePhysicalRellich20261026a.partial F 0 p‖^2) +
      (∫ p, ‖CompactRectanglePhysicalRellich20261026a.partial F 1 p‖^2)) ≤ _
  rw [hx,hy,← jet_norm_sq_integral hF hc 1,← jet_norm_sq_integral hF hc 2]
  have hb (i : Fin 3) : ‖smoothJetClass hF hc i‖^2 ≤ ‖smoothJetClass hF hc‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm _ i)
  linarith [hb 0,hb 1,hb 2]

/-- Every nonsmooth bounded model value is a limit of smooth values in
ONE physical H1 ball with a uniform explicit boundary margin and budget. -/
theorem value_ball_subset_smooth_rellich_closure (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (A : ℝ) (hA : 0 ≤ A) :
    valueProjection L R a b '' {v : RectangleJet L R a b | ‖v‖^2 ≤ A} ⊆
      closure (physical '' h1Ball (rellichFrame L R a b hLR ha hab)
        (rellichMargin (rellichFrame L R a b hLR ha hab)) (3*(A+1))) := by
  rintro u ⟨v,hv,rfl⟩
  have hLR' : L-1 < R+1 := by linarith
  have hab' : a/2 < b+1 := by linarith
  have ho : rect L R a b ⊆ openRect (L-1) (R+1) (a/2) (b+1) := by
    intro p hp
    constructor <;> constructor <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2]
  obtain ⟨P⟩ := exists_normalizedH1TensorSequence (compactJet v)
    (representative_compact v 1) (representative_compact v 2)
    (L-1) (R+1) (a/2) (b+1) (half_pos ha) hLR' hab'
    ((representative_support v 0).trans ho)
  let F (k : ℕ) := finiteChartFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor)
  have hF (k : ℕ) : ContDiff ℝ ∞ (F k) := finiteSmoothChart_contDiff Finset.univ (P.tensors k)
  have hs (k : ℕ) : tsupport (F k) ⊆ rect (L-1) (R+1) (a/2) (b+1) :=
    finiteTensor_tsupport_rect Finset.univ (P.tensors k) _ _ _ _ (fun i =>
      ⟨(P.horizontal_support k i).trans Ioo_subset_Icc_self,
        (P.vertical_support k i).trans Ioo_subset_Icc_self⟩)
  let s (k : ℕ) := approximantRellichSeed L R a b hLR ha hab (hF k) (hs k)
  have hjet : Tendsto (fun k => smoothJetClass (hF k) (P.compact k)) atTop (𝓝 v.val) := by
    simpa only [compactJet_class] using P.jet_tendsto
  have hvalue : Tendsto (fun k => physical (s k)) atTop (𝓝 (valueProjection L R a b v)) := by
    have h := tendsto_pi_nhds.mp hjet (0 : Fin 3)
    simpa only [s,approximantRellichSeed_value,valueProjection_apply] using h
  have hroot : ‖v.val‖ < Real.sqrt (A+1) := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ A+1 by linarith)
    have hn := Real.sqrt_nonneg (A+1)
    change ‖v.val‖^2 ≤ A at hv
    nlinarith [norm_nonneg v.val]
  have hevent : ∀ᶠ k in atTop, ‖smoothJetClass (hF k) (P.compact k)‖ < Real.sqrt (A+1) :=
    hjet.norm.eventually (gt_mem_nhds hroot)
  apply mem_closure_of_tendsto hvalue
  filter_upwards [hevent] with k hk
  refine ⟨s k,?_,rfl⟩
  have hb := approximantRellichSeed_h1_bound L R a b hLR ha hab (hF k) (P.compact k) (hs k)
  have hsqrt := Real.sq_sqrt (show 0 ≤ A+1 by linarith)
  have hn := Real.sqrt_nonneg (A+1)
  change ‖physical (s k)‖^2 + energy (s k) ≤ 3*(A+1)
  nlinarith [norm_nonneg (smoothJetClass (hF k) (P.compact k))]

theorem value_ball_totallyBounded (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded (valueProjection L R a b '' {v : RectangleJet L R a b | ‖v‖^2 ≤ A}) :=
  (physical_h1Ball_totallyBounded (rellichFrame L R a b hLR ha hab)
    (rellichMargin_pos _) (3*(A+1)) (by positivity)).closure.subset
      (value_ball_subset_smooth_rellich_closure L R a b hLR ha hab A hA)

theorem value_ball_compact_closure (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (closure (valueProjection L R a b '' {v : RectangleJet L R a b | ‖v‖^2 ≤ A})) :=
  (value_ball_totallyBounded L R a b hLR ha hab A hA).closure.isCompact isClosed_closure.isComplete

/-- Rellich compactness for the ACTUAL native nonsmooth value projection. -/
theorem valueProjection_isCompactOperator (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) : IsCompactOperator (valueProjection L R a b) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (valueProjection L R a b).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  have he : closedBall (0 : RectangleJet L R a b) 1 = {v : RectangleJet L R a b | ‖v‖^2 ≤ 1} := by
    ext v
    simp only [mem_closedBall,dist_zero_right,mem_setOf_eq]
    constructor <;> intro h <;> nlinarith [norm_nonneg v]
  simpa only [he] using value_ball_compact_closure L R a b hLR ha hab 1 (by norm_num)

end
end ImbalancedChen.Part3.FixedRectangleWeakJetValueRellich20261026b
