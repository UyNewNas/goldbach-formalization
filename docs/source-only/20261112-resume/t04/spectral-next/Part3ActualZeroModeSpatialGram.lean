import ImbalancedChen.Part3ActualNativeHorizontalGrowth
import ImbalancedChen.Part3EndpointDampedRectangle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Batteries.Tactic.OpenPrivate

/-! The full native-cusp continuous and constant Gram on the actual
compact zero-mode Poincaré generators.  No isometry, full quotient
Plancherel, power bound for primitive L-functions at 1+it, or vanishing
of a horizontal side is taken as an input. -/
namespace ImbalancedChen.Part3.ActualZeroModeSpatialGram20261112

noncomputable section
open Set Filter Topology Complex MeasureTheory Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators Interval Classical
open ActualNativeHorizontalGrowth20261112 EndpointDampedRectangle20261112
open ActualIncompleteEisensteinGram20261110 ActualIncompleteCriticalColumns20261110
open ActualIncompleteContinuousGram20261110 ActualIncompleteResidualContour20261110
open NativeCuspCompactMellinSynthesis20261027 CompactHeightMellinInversion20261027
open Gamma0ActualConstantMode20261025a NormalizedCuspCompactPoincare20261026b
open AllNormalizedCuspAnnihilator20261026b SmoothZeroHeightSeedProfiles20261026b OriginalFrameZeroSeedMellin20261027
open private regularPart regularPart_formula regularPart_diff scalar_regular from
  ImbalancedChen.Part3ActualIncompleteResidualContour

private def corrected (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (s : ℂ) :=
  regularPart (scalar N g h ψ φ) (residue N ψ φ) s + residue N ψ φ/s

private theorem corrected_formula (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed)
    {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) : corrected N g h ψ φ s =
      scalar N g h ψ φ s-residue N ψ φ/(s*(s-1)) := by
  rw [corrected,regularPart_formula _ _ h₁]
  field_simp [h₀,sub_ne_zero.mpr h₁] <;> ring

private theorem regular_diff (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    DifferentiableOn ℂ (regularPart (scalar N g h ψ φ) (residue N ψ φ)) {s : ℂ | 1/2 ≤ s.re} :=
  regularPart_diff _ _ (fun _ => scalar_regular N g h ψ φ) (scalar_pole N g h ψ φ)

private theorem corrected_diff (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    DifferentiableOn ℂ (corrected N g h ψ φ) {s : ℂ | 1/2 ≤ s.re} := by
  apply (regular_diff N g h ψ φ).add
  exact differentiableOn_const.div differentiableOn_id (fun s hs e => by
    change 1/2 ≤ s.re at hs
    norm_num [e] at hs)

private theorem line_ne {c : ℝ} (hc : c=1/2 ∨ c=3/2) (t : ℝ) :
    verticalParameter c t ≠ 0 ∧ verticalParameter c t ≠ 1 := by
  rcases hc with rfl|rfl <;> constructor <;> intro e <;>
    have E := congrArg Complex.re e <;> rw [verticalParameter_re] at E <;> norm_num at E

private theorem rational_integrable (r : ℂ) {c : ℝ} (hc : c=1/2 ∨ c=3/2) :
    Integrable (fun t : ℝ => r/(verticalParameter c t*(verticalParameter c t-1))) := by
  let z := verticalParameter c
  have cc : Continuous z := by unfold z verticalParameter; fun_prop
  have D (t : ℝ) : z t*(z t-1) ≠ 0 :=
    mul_ne_zero (line_ne hc t).1 (sub_ne_zero.mpr (line_ne hc t).2)
  apply (integrable_inv_one_add_sq.const_mul (4*‖r‖)).mono'
    (continuous_const.div (cc.mul (cc.sub continuous_const)) D).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have X : ‖z t‖^2 = c^2+t^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp [z,verticalParameter,Complex.mul_re,Complex.mul_im,pow_two]
  have Y : ‖z t-1‖^2 = (c-1)^2+t^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp [z,verticalParameter,Complex.mul_re,Complex.mul_im,pow_two]
  have h : ‖z t-1‖ ≤ ‖z t‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rcases hc with e|e <;> rw [e] at X Y <;> nlinarith
  have W : 1+t^2 ≤ 4*(‖z t‖*‖z t-1‖) := by
    have m := mul_le_mul_of_nonneg_right h (norm_nonneg (z t-1))
    rcases hc with e|e <;> rw [e] at Y <;> nlinarith [sq_nonneg t]
  have hp : 0 < ‖z t‖*‖z t-1‖ := by rw [← norm_mul]; exact norm_pos_iff.mpr (D t)
  change ‖r/(z t*(z t-1))‖ ≤ (4*‖r‖)*(1+t^2)⁻¹
  rw [norm_div,norm_mul,← div_eq_mul_inv]
  apply (div_le_div_iff₀ hp (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left W (norm_nonneg r)]

private theorem corrected_integrable (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed)
    {c : ℝ} (hc : c=1/2 ∨ c=3/2) :
    Integrable (fun t : ℝ => corrected N g h ψ φ (verticalParameter c t)) := by
  have V : Integrable (gramIntegrand N g h ψ φ c) := by
    rcases hc with rfl|rfl
    · exact gram_critical_integrable N g h ψ φ
    · exact (initial_spatial_gram N h g ψ φ (3/2) (by norm_num)).1
  apply (V.sub (rational_integrable (residue N ψ φ) hc)).congr
  apply Eventually.of_forall
  intro t
  rw [corrected_formula _ _ _ _ _ (line_ne hc t).1 (line_ne hc t).2,scalar_on_line] <;> rfl

private theorem corrected_horizontal (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (1/2 : ℝ) (3/2), ∀ t : ℝ, 1 ≤ |t| →
      (x-1/2)*‖corrected N g h ψ φ (verticalParameter x t)‖ ≤ C*Real.exp (Real.pi*|t|) := by
  obtain ⟨B,hB,H⟩ := scalar_horizontal N g h ψ φ
  let r := residue N ψ φ
  refine ⟨B+‖r‖,add_nonneg hB (norm_nonneg _),?_⟩
  intro x hx t ht
  rcases eq_or_lt_of_le hx.1 with e|h
  · rw [← e,sub_self,zero_mul]
    positivity
  let s := verticalParameter x t
  have E : s.im = t := by simp [s,verticalParameter,Complex.mul_im]
  have R : s.re=x := verticalParameter_re x t
  have S₀ : 1 ≤ ‖s‖ := ht.trans (by simpa only [E] using Complex.abs_im_le_norm s)
  have S₁ : 1 ≤ ‖s-1‖ := ht.trans (by simpa [Complex.sub_im,E] using Complex.abs_im_le_norm (s-1))
  have h₀ : s ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le S₀)
  have h₁ : s ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp (zero_lt_one.trans_le S₁))
  have Z := H s (by simpa only [R] using h) (by simpa only [R] using hx.2) (by simpa only [E] using ht)
  change (x-1/2)*‖corrected N g h ψ φ s‖ ≤ _
  rw [corrected_formula _ _ _ _ _ h₀ h₁]
  have M : ‖r/(s*(s-1))‖ ≤ ‖r‖ := by
    rw [norm_div,norm_mul]
    exact div_le_self (norm_nonneg _) (one_le_mul_of_one_le_of_one_le S₀ S₁)
  have J := mul_le_mul_of_nonneg_left (norm_sub_le (scalar N g h ψ φ s) (r/(s*(s-1)))) (sub_nonneg.mpr hx.1)
  have A := mul_le_mul (by linarith [hx.2] : x-1/2 ≤ 1) M (norm_nonneg _) zero_le_one
  have B' := le_mul_of_one_le_right (norm_nonneg r) (Real.one_le_exp (by positivity : 0 ≤ Real.pi*|t|))
  change (s.re-1/2)*_ ≤ B*_ at Z
  rw [show s.re=x from R,E] at Z
  nlinarith only [Z,J,A,B']

private theorem rational_flux (r : ℂ) : Tendsto (flux (fun s => r/s)) atTop (𝓝 0) := by
  have side (negSide : Bool) :
      Tendsto (fun T : ℝ => ∫ x : ℝ in (1/2)..(3/2),
        r/verticalParameter x (if negSide then -T else T)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun T : ℝ => ‖r‖/T) atTop (𝓝 0) by
      simpa [div_eq_mul_inv] using
        (show Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) from tendsto_inv_atTop_zero).const_mul ‖r‖)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1/2 : ℝ)) (b := 3/2)
      (C := ‖r‖/T) (f := fun x => r/verticalParameter x (if negSide then -T else T)) (fun x _ => by
        rw [norm_div]
        apply div_le_div_of_nonneg_left (norm_nonneg _) hT
        have Q := Complex.abs_im_le_norm (verticalParameter x (if negSide then -T else T))
        cases negSide <;> simpa [verticalParameter,Complex.mul_im,abs_of_pos hT] using Q)
    simpa only [show |(3/2 : ℝ)-1/2|=1 by norm_num,mul_one] using H
  simpa [flux] using ((side false).sub (side true)).const_mul I

private theorem flux_split (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (T : ℝ) :
    edge N g h ψ φ T =
      flux (corrected N g h ψ φ) T-flux (fun s => residue N ψ φ/s) T := by
  let F := scalar N g h ψ φ
  let r := residue N ψ φ
  let U := regularPart F r
  let K := [[(1/2 : ℝ),3/2]]
  have mapHalf (t : ℝ) : MapsTo (fun x : ℝ => verticalParameter x t) K {s : ℂ | 1/2 ≤ s.re} := by
    intro x hx
    rw [show K = Icc (1/2 : ℝ) (3/2) by simp [K,uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 3/2)]] at hx
    simpa only [mem_setOf_eq,verticalParameter_re] using hx.1
  have splitSide (t : ℝ) :
      (∫ x : ℝ in (1/2)..(3/2),corrected N g h ψ φ (verticalParameter x t)) =
      (∫ x : ℝ in (1/2)..(3/2),U (verticalParameter x t))+
      ∫ x : ℝ in (1/2)..(3/2),r/verticalParameter x t := by
    have C : Continuous (fun x : ℝ => verticalParameter x t) := by unfold verticalParameter; fun_prop
    have D : ContinuousOn (fun x => U (verticalParameter x t)) K :=
      (regular_diff N g h ψ φ).continuousOn.comp C.continuousOn (mapHalf t)
    have V : ContinuousOn (fun x : ℝ => r/verticalParameter x t) K :=
      continuousOn_const.div C.continuousOn (fun x hx e => by
        have J := mapHalf t hx
        change 1/2 ≤ (verticalParameter x t).re at J
        norm_num [e] at J)
    exact intervalIntegral.integral_add D.intervalIntegrable V.intervalIntegrable
  unfold flux edge
  rw [splitSide T,splitSide (-T)]
  change I*((∫ x : ℝ in (1/2)..(3/2),U (verticalParameter x T))-
    ∫ x : ℝ in (1/2)..(3/2),U (verticalParameter x (-T))) = _
  dsimp only [r]
  ring

/-- The original, unweighted horizontal error of the actual cusp Gram
vanishes as T tends to infinity along the entire real half-line. -/
theorem native_horizontal_edges_vanish (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    Tendsto (edge N g h ψ φ) atTop (𝓝 0) := by
  let U := corrected N g h ψ φ
  have d := corrected_diff N g h ψ φ
  have l := corrected_integrable N g h ψ φ (c := 1/2) (Or.inl rfl)
  have r := corrected_integrable N g h ψ φ (c := 3/2) (Or.inr rfl)
  have Q := vertical_equality U d l r (corrected_horizontal N g h ψ φ)
  have R := intervalIntegral_tendsto_integral r tendsto_neg_atTop_atBot (tendsto_id (α := ℝ))
  have L := intervalIntegral_tendsto_integral l tendsto_neg_atTop_atBot (tendsto_id (α := ℝ))
  have V : Tendsto (flux U) atTop (𝓝 0) := by
    have J := (R.sub L).neg
    change Tendsto _ _ (𝓝 (-((∫ t : ℝ,U (verticalParameter (3/2) t))-
      ∫ t : ℝ,U (verticalParameter (1/2) t)))) at J
    rw [Q,sub_self,neg_zero] at J
    apply J.congr'
    exact Eventually.of_forall (fun T => by rw [rect U d T,neg_neg])
  have H := V.sub (rational_flux (residue N ψ φ))
  simpa only [zero_sub,neg_zero,← flux_split N g h ψ φ,U] using H

/-- The actual full cusp-summed Gram, including its sole constant
projection on these generators, the full real line and 1/(4π).
The spectral coordinates in physicalProduct are the genuine quotient
pairings of the sharp compact Poincaré vectors. -/
theorem spatial_gram (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    let V := frameZeroSeedL2 N (NeZero.pos N) h ψ.toHeightSeed
    let W := frameZeroSeedL2 N (NeZero.pos N) g φ.toHeightSeed
    inner ℂ V W = (4*Real.pi)⁻¹ • (∫ t : ℝ,physicalProduct N h g ψ φ t) +
      inner ℂ V ((ℂ ∙ constantL2 N).starProjection W) := by
  have A := (native_horizontal_edges_vanish N g h ψ φ).const_smul ((2*Real.pi)⁻¹ : ℝ)
  have H := tendsto_nhds_unique A (physical_contour_limit N g h ψ φ)
  simp only [smul_zero] at H
  dsimp only
  linear_combination H

end
end ImbalancedChen.Part3.ActualZeroModeSpatialGram20261112
