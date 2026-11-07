import ImbalancedChen.Part3CompactC2JetCutoffEstimate

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Finite actual smooth tensors approximate a genuine compact smooth
positive-height plane test in all six jets while every factor stays in a
prescribed open rectangle with a requested safety margin. One constructs
separated cutoffs FIRST, pays their genuine six-jet multiplier constant,
then invokes the already proved C2 finite approximation at that tolerance.
No support-preserving density, Gamma transport or H1 supplier is assumed.
-/

noncomputable section
namespace ImbalancedChen.Part3.CompactC2LocalizedTensorApproximation20261026a

open Set
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open CompactC2FiniteTensorApproximation20261026a CompactC2JetCutoffEstimate20261026a
open MaassWeakOperatorCore20261024zz Gamma0SmoothCompactTensorCore20261025a

structure IntervalCutoff (L R ρ : ℝ) where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  eq_one : ∀ x ∈ Icc L R, toFun x = 1
  support : tsupport toFun ⊆ Icc (L - 2 * ρ / 3) (R + 2 * ρ / 3)

instance {L R ρ : ℝ} : CoeFun (IntervalCutoff L R ρ) (fun _ => ℝ → ℂ) := ⟨IntervalCutoff.toFun⟩

def intervalBump (L R ρ : ℝ) (hLR : L ≤ R) (hρ : 0 < ρ) :
    ContDiffBump ((L + R) / 2) where
  rIn := (R - L) / 2 + ρ / 3
  rOut := (R - L) / 2 + 2 * ρ / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def actualIntervalCutoff (L R ρ : ℝ) (hLR : L ≤ R) (hρ : 0 < ρ) : IntervalCutoff L R ρ where
  toFun x := (intervalBump L R ρ hLR hρ x : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (intervalBump L R ρ hLR hρ).contDiff
  compact := (intervalBump L R ρ hLR hρ).hasCompactSupport.comp_left rfl
  eq_one := by
    intro x hx
    have h : intervalBump L R ρ hLR hρ x = 1 := by
      apply (intervalBump L R ρ hLR hρ).one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      change -((R - L) / 2 + ρ / 3) ≤ x - (L + R) / 2 ∧
        x - (L + R) / 2 ≤ (R - L) / 2 + ρ / 3
      constructor <;> linarith [hx.1, hx.2]
    simp only [h, Complex.ofReal_one]
  support := by
    intro x hx
    have hs := tsupport_comp_subset (g := Complex.ofReal) rfl
      (intervalBump L R ρ hLR hρ) hx
    rw [(intervalBump L R ρ hLR hρ).tsupport_eq, Metric.mem_closedBall,
      Real.dist_eq, abs_le] at hs
    change L - 2 * ρ / 3 ≤ x ∧ x ≤ R + 2 * ρ / 3
    constructor <;> linarith [hs.1, hs.2]

def cutoffPlane {L R a b ρ : ℝ} (χ : IntervalCutoff L R ρ) (ψ : IntervalCutoff a b ρ)
    (p : Plane) : ℂ := χ p.1 * ψ p.2

theorem cutoffPlane_smooth {L R a b ρ : ℝ} (χ : IntervalCutoff L R ρ) (ψ : IntervalCutoff a b ρ) :
    ContDiff ℝ ∞ (cutoffPlane χ ψ) :=
  (χ.smooth.comp contDiff_fst).mul (ψ.smooth.comp contDiff_snd)

theorem cutoffPlane_compact {L R a b ρ : ℝ} (χ : IntervalCutoff L R ρ) (ψ : IntervalCutoff a b ρ) :
    HasCompactSupport (cutoffPlane χ ψ) := by
  apply HasCompactSupport.intro (χ.compact.prod ψ.compact)
  intro p hp
  by_cases hh : p.1 ∈ tsupport χ
  · have hv : p.2 ∉ tsupport ψ := fun h => hp ⟨hh, h⟩
    simp only [cutoffPlane, image_eq_zero_of_notMem_tsupport hv, mul_zero]
  · simp only [cutoffPlane, image_eq_zero_of_notMem_tsupport hh, zero_mul]

theorem cutoffPlane_mul_original {F : Plane → ℂ} {L R a b ρ : ℝ}
    (χ : IntervalCutoff L R ρ) (ψ : IntervalCutoff a b ρ)
    (hs : tsupport F ⊆ Icc L R ×ˢ Icc a b) : (fun p => cutoffPlane χ ψ p * F p) = F := by
  funext p
  by_cases hp : p ∈ tsupport F
  · have h := hs hp
    simp only [cutoffPlane, χ.eq_one _ h.1, ψ.eq_one _ h.2, one_mul]
  · simp only [image_eq_zero_of_notMem_tsupport hp, mul_zero]

def localizeTensor {L R a b ρ : ℝ} (χ : IntervalCutoff L R ρ) (ψ : IntervalCutoff a b ρ)
    (T : SmoothCompactTensor) : SmoothCompactTensor where
  horizontal x := χ x * T.horizontal x
  vertical y := ψ y * T.vertical y
  horizontal_smooth := (χ.smooth.mul T.horizontal_cinfty).of_le (by simp)
  vertical_smooth := (ψ.smooth.mul T.vertical_cinfty).of_le (by simp)
  horizontal_compact := T.horizontal_compact.mul_left
  vertical_compact := T.vertical_compact.mul_left
  vertical_positive := tsupport_mul_subset_right.trans T.vertical_positive
  horizontal_cinfty := χ.smooth.mul T.horizontal_cinfty
  vertical_cinfty := ψ.smooth.mul T.vertical_cinfty

theorem localizeTensor_chart {ι : Type*} {L R a b ρ : ℝ}
    (χ : IntervalCutoff L R ρ) (ψ : IntervalCutoff a b ρ)
    (s : Finset ι) (T : ι → SmoothCompactTensor) :
    finiteChartFunction s (fun i => (localizeTensor χ ψ (T i)).toCompactTensor) =
      fun p => cutoffPlane χ ψ p * finiteChartFunction s (fun i => (T i).toCompactTensor) p := by
  funext p
  simp only [finiteChartFunction, localizeTensor, cutoffPlane, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The safety margin σ is specified BEFORE ε. The positive extra slack ρ
is genuinely left between the original support box and U shrunk by σ. -/
structure LocalizedC2Approximation (F : Plane → ℂ) (uL uR vL vR σ ε : ℝ) where
  A : ℝ
  a : ℝ
  b : ℝ
  indices : Finset (planeBox A a b)
  tensors : planeBox A a b → SmoothCompactTensor
  slack : ℝ
  slack_pos : 0 < slack
  horizontal_support : ∀ t,
    tsupport (tensors t).horizontal ⊆ Icc (uL + σ + slack) (uR - σ - slack)
  vertical_support : ∀ t,
    tsupport (tensors t).vertical ⊆ Icc (vL + σ + slack) (vR - σ - slack)
  uniform_sixJet_error : ∀ p : Plane, ∀ ij : JetIndex,
    ‖partialJet ij (finiteChartFunction indices (fun t => (tensors t).toCompactTensor)) p -
      partialJet ij F p‖ < ε

/-- A real support-preserving C2 finite tensor theorem, with arbitrary
requested margin σ and positive extra slack. The support may be far from
the horizontal origin; the original C2 approximation is localized afterward. -/
theorem exists_localizedC2Approximation {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (L R a b : ℝ) (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    (hs : tsupport F ⊆ Icc L R ×ˢ Icc a b)
    (uL uR vL vR σ ρ : ℝ) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hxL : uL + σ + ρ ≤ L) (hxR : R + σ + ρ ≤ uR)
    (hyL : vL + σ + ρ ≤ a) (hyR : b + σ + ρ ≤ vR)
    (ε : ℝ) (hε : 0 < ε) : ∃ P : LocalizedC2Approximation F uL uR vL vR σ ε, P.slack = ρ / 3 := by
  let χ := actualIntervalCutoff L R ρ hLR hρ
  let ψ := actualIntervalCutoff a b ρ hab hρ
  let C := cutoffPlane χ ψ
  have hC : ContDiff ℝ ∞ C := cutoffPlane_smooth χ ψ
  obtain ⟨M, hM, hCM⟩ := exists_global_jet_bound hC (cutoffPlane_compact χ ψ)
  let δ := ε / (8 * (M + 1))
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hden : 0 < 8 * (M + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let A := max |L| |R|
  have hcenter : tsupport F ⊆ planeBox A a b := by
    intro p hp
    have h := hs hp
    have hL : -A ≤ L := by
      have hh : |L| ≤ A := le_max_left _ _
      linarith [neg_abs_le L]
    have hR : R ≤ A := (le_abs_self R).trans (le_max_right _ _)
    exact ⟨⟨hL.trans h.1.1, h.1.2.trans hR⟩, h.2⟩
  obtain ⟨P⟩ := exists_compactC2TensorApproximation hF hc A a b ha hcenter δ hδ
  let G := finiteChartFunction P.indices (fun t => (P.tensors t).toCompactTensor)
  have hG : ContDiff ℝ ∞ G := finiteSmoothChart_contDiff P.indices P.tensors
  let E : Plane → ℂ := G - F
  have hE : ContDiff ℝ ∞ E := hG.sub hF
  have hEM : ∀ p ij, ‖mixedJet E ij p‖ ≤ δ := by
    intro p ij
    have h := P.uniform_sixJet_error_global hδ p ij
    rw [partialJet_eq_mixedJet hG, partialJet_eq_mixedJet hF] at h
    simpa only [E, mixedJet_sub hG hF, Pi.sub_apply] using h.le
  let T := fun t => localizeTensor χ ψ (P.tensors t)
  let H := finiteChartFunction P.indices (fun t => (T t).toCompactTensor)
  have hH : ContDiff ℝ ∞ H := finiteSmoothChart_contDiff P.indices T
  have hHF : H - F = fun p => C p * E p := by
    have hCF := cutoffPlane_mul_original χ ψ hs
    rw [show H = fun p => C p * G p from localizeTensor_chart χ ψ P.indices P.tensors]
    funext p
    have hp := congrFun hCF p
    change C p * G p - F p = C p * (G p - F p)
    calc
      C p * G p - F p = C p * G p - C p * F p := by rw [hp]
      _ = C p * (G p - F p) := by ring
  have hcost : 4 * M * δ < ε := by
    have heq : (8 * (M + 1)) * δ = ε := by
      dsimp [δ]
      field_simp [ne_of_gt hden]
    nlinarith [mul_nonneg hM0 hδ.le]
  refine ⟨{ A := A, a := a, b := b, indices := P.indices, tensors := T,
    slack := ρ / 3, slack_pos := by positivity,
    horizontal_support := ?_, vertical_support := ?_, uniform_sixJet_error := ?_ }, rfl⟩
  · intro t x hx
    have hh : x ∈ tsupport χ := tsupport_mul_subset_left hx
    have h := χ.support hh
    constructor <;> linarith [h.1, h.2]
  · intro t y hy
    have hh : y ∈ tsupport ψ := tsupport_mul_subset_left hy
    have h := ψ.support hh
    constructor <;> linarith [h.1, h.2]
  · intro p ij
    rw [partialJet_eq_mixedJet hH, partialJet_eq_mixedJet hF]
    have hsub := congrFun (mixedJet_sub hH hF ij) p
    rw [Pi.sub_apply] at hsub
    rw [← hsub, hHF]
    exact (mixedJet_mul_norm_le hC hE hM0 hδ.le hCM hEM p ij).trans_lt hcost

/-- Compactness inside the prescribed open rectangle produces the inner
rectangle and strictly positive residual slack. Adding one interior point
handles the empty support without a separate arbitrary supplier. -/
theorem exists_inner_rectangle_slack {K : Set Plane} (hK : IsCompact K)
    (uL uR vL vR σ : ℝ) (hσ : 0 ≤ σ) (hvL : 0 < vL)
    (hu : uL + σ < uR - σ) (hv : vL + σ < vR - σ)
    (hs : K ⊆ Ioo (uL + σ) (uR - σ) ×ˢ Ioo (vL + σ) (vR - σ)) :
    ∃ L R a b ρ : ℝ, L ≤ R ∧ 0 < a ∧ a ≤ b ∧ 0 < ρ ∧
      uL + σ + ρ ≤ L ∧ R + σ + ρ ≤ uR ∧
      vL + σ + ρ ≤ a ∧ b + σ + ρ ≤ vR ∧ K ⊆ Icc L R ×ˢ Icc a b := by
  let z : Plane := ((uL + uR) / 2, (vL + vR) / 2)
  have hz : z ∈ Ioo (uL + σ) (uR - σ) ×ˢ Ioo (vL + σ) (vR - σ) := by
    constructor <;> constructor <;> dsimp [z] <;> linarith
  let J := K ∪ {z}
  have hJ : IsCompact J := hK.union isCompact_singleton
  have hne : J.Nonempty := ⟨z, Or.inr rfl⟩
  have hsub : J ⊆ Ioo (uL + σ) (uR - σ) ×ˢ Ioo (vL + σ) (vR - σ) := by
    intro p hp
    rcases hp with hp | hp
    · exact hs hp
    · have hpz : p = z := Set.mem_singleton_iff.mp hp
      simpa only [hpz] using hz
  obtain ⟨xl, hxl, hminx⟩ := hJ.exists_isMinOn hne continuous_fst.continuousOn
  obtain ⟨xr, hxr, hmaxx⟩ := hJ.exists_isMaxOn hne continuous_fst.continuousOn
  obtain ⟨yl, hyl, hminy⟩ := hJ.exists_isMinOn hne continuous_snd.continuousOn
  obtain ⟨yr, hyr, hmaxy⟩ := hJ.exists_isMaxOn hne continuous_snd.continuousOn
  let ρ := min (min (xl.1 - (uL + σ)) ((uR - σ) - xr.1))
    (min (yl.2 - (vL + σ)) ((vR - σ) - yr.2))
  have hρ : 0 < ρ := lt_min
    (lt_min (sub_pos.mpr (hsub hxl).1.1) (sub_pos.mpr (hsub hxr).1.2))
    (lt_min (sub_pos.mpr (hsub hyl).2.1) (sub_pos.mpr (hsub hyr).2.2))
  have hρxL : ρ ≤ xl.1 - (uL + σ) := (min_le_left _ _).trans (min_le_left _ _)
  have hρxR : ρ ≤ (uR - σ) - xr.1 := (min_le_left _ _).trans (min_le_right _ _)
  have hρyL : ρ ≤ yl.2 - (vL + σ) := (min_le_right _ _).trans (min_le_left _ _)
  have hρyR : ρ ≤ (vR - σ) - yr.2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨xl.1, xr.1, yl.2, yr.2, ρ, hminx hxr, ?_, hminy hyr, hρ,
    ?_, ?_, ?_, ?_, ?_⟩
  · linarith [(hsub hyl).2.1]
  · linarith
  · linarith
  · linarith
  · linarith
  · intro p hp
    have hpJ : p ∈ J := Or.inl hp
    exact ⟨⟨hminx hpJ, hmaxx hpJ⟩, hminy hpJ, hmaxy hpJ⟩

/-- Native SAME-OPEN-RECTANGLE density, including a prescribed safety
margin σ: compactness supplies all missing inner support data. No tensor
approximation or smooth-core membership is among the hypotheses. -/
theorem exists_sameOpenRectangle_C2Approximation {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (uL uR vL vR σ : ℝ) (hσ : 0 ≤ σ) (hvL : 0 < vL)
    (hu : uL + σ < uR - σ) (hv : vL + σ < vR - σ)
    (hs : tsupport F ⊆ Ioo (uL + σ) (uR - σ) ×ˢ Ioo (vL + σ) (vR - σ))
    (ε : ℝ) (hε : 0 < ε) : Nonempty (LocalizedC2Approximation F uL uR vL vR σ ε) := by
  obtain ⟨L, R, a, b, ρ, hLR, ha, hab, hρ, hxL, hxR, hyL, hyR, hinner⟩ :=
    exists_inner_rectangle_slack hc uL uR vL vR σ hσ hvL hu hv hs
  obtain ⟨P, _hP⟩ := exists_localizedC2Approximation hF hc L R a b hLR ha hab hinner
    uL uR vL vR σ ρ hσ hρ hxL hxR hyL hyR ε hε
  exact ⟨P⟩
/-- Every factor lies STRICTLY inside the originally requested open
rectangle shrunk by σ, with the produced positive residual margin. -/
theorem LocalizedC2Approximation.factor_supports_open
    {F : Plane → ℂ} {uL uR vL vR σ ε : ℝ}
    (P : LocalizedC2Approximation F uL uR vL vR σ ε) (t : planeBox P.A P.a P.b) :
    tsupport (P.tensors t).horizontal ⊆ Ioo (uL + σ) (uR - σ) ∧
      tsupport (P.tensors t).vertical ⊆ Ioo (vL + σ) (vR - σ) := by
  constructor
  · intro x hx
    have h := P.horizontal_support t hx
    constructor <;> linarith [h.1, h.2, P.slack_pos]
  · intro y hy
    have h := P.vertical_support t hy
    constructor <;> linarith [h.1, h.2, P.slack_pos]

/-- The residual margin is chosen ONCE from the original support and U,
BEFORE epsilon. All finite families then share the same compact inner
rectangle, and every second derivative is controlled at the requested ε. -/
theorem exists_fixed_margin_all_epsilon_C2Approximation {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (uL uR vL vR σ : ℝ) (hσ : 0 ≤ σ) (hvL : 0 < vL)
    (hu : uL + σ < uR - σ) (hv : vL + σ < vR - σ)
    (hs : tsupport F ⊆ Ioo (uL + σ) (uR - σ) ×ˢ Ioo (vL + σ) (vR - σ)) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε →
      ∃ P : LocalizedC2Approximation F uL uR vL vR σ ε, P.slack = η := by
  obtain ⟨L, R, a, b, ρ, hLR, ha, hab, hρ, hxL, hxR, hyL, hyR, hinner⟩ :=
    exists_inner_rectangle_slack hc uL uR vL vR σ hσ hvL hu hv hs
  refine ⟨ρ / 3, by positivity, ?_⟩
  intro ε hε
  exact exists_localizedC2Approximation hF hc L R a b hLR ha hab hinner
    uL uR vL vR σ ρ hσ hρ hxL hxR hyL hyR ε hε
end ImbalancedChen.Part3.CompactC2LocalizedTensorApproximation20261026a