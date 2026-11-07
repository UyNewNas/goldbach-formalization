import ImbalancedChen.Part3ActualMobiusPairChartL2Transport
import ImbalancedChen.Part3Gamma0CompactCarrierBump
import ImbalancedChen.Part3ActualModularSmoothCuspCutoff
import ImbalancedChen.Part3NestedRectangleRealCutoff
import ImbalancedChen.Part3CompactProductKernelSixJet

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual image of a positive compact chart has a positive nested
rectangle with strict margins. Existing attained compact height bounds
and the existing concrete separated cutoff supply a globally smooth,
compact complex cutoff with a true constant-one germ at every image point.
This pays geometric hypotheses of raw local H1 Mobius transport; no weak
derivative identity, local H1 regularity, or covariance is assumed here.
-/

namespace ImbalancedChen.Part3.ActualMobiusImageCutoffPlateau20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane Topology
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0CompactCarrierBump20261025a
open ActualModularSmoothCuspCutoff20261025a NestedRectangleRealCutoff20261026b
open CompactProductKernelSixJet20261025a

theorem mobius_image_compact (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) : IsCompact (mobiusChart g '' K) :=
  hK.image_of_continuousOn (fun p hp =>
    (mobiusChart_contDiffAt g (hKp p hp)).continuousAt.continuousWithinAt)

theorem mobius_image_positive (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hKp : ∀ p ∈ K, 0 < p.2) : ∀ q ∈ mobiusChart g '' K, 0 < q.2 := by
  rintro q ⟨p,hp,rfl⟩
  rw [mobiusChart_eq_actual g (hKp p hp)]
  exact (g • chartLift p).im_pos

/-- The existing compact-H height enclosure is reused after the native
positive lift. Both inner walls and the outer margin are strictly safe. -/
theorem exists_mobius_image_nested_rectangle (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) :
    ∃ A a b δ : ℝ, 0 < A ∧ 0 < a ∧ a < b ∧ 0 < δ ∧ 2*δ < a ∧
      mobiusChart g '' K ⊆ Ioo (-A) A ×ˢ Ioo a b := by
  let S := mobiusChart g '' K
  have hSc : IsCompact S := mobius_image_compact g hK hKp
  have hSp : ∀ p ∈ S, 0 < p.2 := mobius_image_positive g hKp
  have hH : IsCompact (chartLift '' S) := hSc.image_of_continuousOn
    (fun p hp => (chartLift_continuousAt_positive (hSp p hp)).continuousWithinAt)
  obtain ⟨A,a,b,hA,ha,hab,hrect⟩ := compact_height_rectangle hH
  refine ⟨A+1,a/2,b+1,a/8,by linarith,by linarith,by linarith,
    by linarith,by linarith,?_⟩
  intro p hp
  have hq := hrect (chartLift p) ⟨p,hp,rfl⟩
  rw [chartLift_of_positive (hSp p hp)] at hq
  change (p.1 ∈ Icc (-A) A) ∧ (p.2 ∈ Icc a b) at hq
  constructor <;> constructor <;> linarith [hq.1.1,hq.1.2,hq.2.1,hq.2.2]

/-- Concrete geometric supplier for the raw local-H1 transport theorem.
The complex cutoff is one on an open neighborhood of the whole actual
image, and its compact support lies in a measurable positive rectangle
and in a positive closed planeBox. All these objects are produced. -/
theorem exists_mobius_image_cutoff_plateau (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) :
    ∃ (Ω : Set (ℝ × ℝ)) (χ : ℝ × ℝ → ℂ) (A a b : ℝ),
      IsOpen Ω ∧ MeasurableSet Ω ∧ Ω ⊆ positiveChart ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      0 < a ∧ tsupport χ ⊆ planeBox A a b ∧
      ∀ q ∈ mobiusChart g '' K, χ =ᶠ[𝓝 q] (fun _ => (1 : ℂ)) := by
  obtain ⟨A,a,b,δ,hA,ha,hab,hδ,hmargin,himage⟩ :=
    exists_mobius_image_nested_rectangle g hK hKp
  have hLR : -A ≤ A := by linarith
  let θ := rectangleCutoff (-A) A a b δ hLR hab.le hδ
  let χ : ℝ × ℝ → ℂ := fun p => (θ p : ℂ)
  let Ω : Set (ℝ × ℝ) := Ioo (-A-δ) (A+δ) ×ˢ Ioo (a-δ) (b+δ)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
  have hθc : HasCompactSupport θ := rectangleCutoff_compact _ _ _ _ _ _ _ _
  have hχc : HasCompactSupport χ := hθc.comp_left (g := Complex.ofReal) rfl
  have hχs : tsupport χ ⊆ tsupport θ := by
    apply closure_minimal _ (isClosed_tsupport θ)
    intro p hp
    apply subset_closure
    intro hz
    exact hp (by simp only [χ,hz,Complex.ofReal_zero])
  have hθΩ : tsupport θ ⊆ Ω := rectangleCutoff_support _ _ _ _ _ _ _ _
  have hχΩ : tsupport χ ⊆ Ω := hχs.trans hθΩ
  have hlow : 0 < a-δ := by linarith
  refine ⟨Ω,χ,A+δ,a-δ,b+δ,hΩ,hΩ.measurableSet,?_,?_,hχc,hχΩ,hlow,?_,?_⟩
  · intro p hp
    exact hlow.trans hp.2.1
  · exact Complex.ofRealCLM.contDiff.comp (rectangleCutoff_smooth _ _ _ _ _ _ _ _)
  · intro p hp
    have hh := hχΩ hp
    change p.1 ∈ Icc (-(A+δ)) (A+δ) ∧ p.2 ∈ Icc (a-δ) (b+δ)
    constructor
    · constructor <;> linarith [hh.1.1,hh.1.2]
    · exact ⟨hh.2.1.le,hh.2.2.le⟩
  · intro q hq
    have hopen : IsOpen (Ioo (-A) A ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
      isOpen_Ioo.prod isOpen_Ioo
    filter_upwards [hopen.mem_nhds (himage hq)] with p hp
    have hone : θ p = 1 := rectangleCutoff_one _ _ _ _ _ _ _ _
      ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩
    simp only [χ,hone,Complex.ofReal_one]

end
end ImbalancedChen.Part3.ActualMobiusImageCutoffPlateau20261026b
