import ImbalancedChen.Part3CompactRectanglePhysicalRellich
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
An arbitrary positive-height rectangle is normalized by its actual affine
coordinate map. The Jacobian and the two distinct derivative-energy
constants are proved by change of variables and the actual chain rule.
No compact embedding or new Fourier tail estimate is assumed. -/

namespace ImbalancedChen.Part3.PositiveRectangleAffineNormalization20261026b
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open CompactRectanglePhysicalRellich20261026a

abbrev Plane := ℝ × ℝ
abbrev PhysicalL2 := Lp ℂ 2 (volume : Measure Plane)

structure Rectangle where
  left : ℝ
  bottom : ℝ
  width : ℝ
  height : ℝ
  bottom_pos : 0 < bottom
  width_pos : 0 < width
  height_pos : 0 < height

def Rectangle.affine (R : Rectangle) (p : Plane) : Plane :=
  (R.left + R.width * p.1, R.bottom + R.height * p.2)

def Rectangle.inverse (R : Rectangle) (p : Plane) : Plane :=
  ((p.1 - R.left) / R.width, (p.2 - R.bottom) / R.height)

theorem Rectangle.inverse_affine (R : Rectangle) (p : Plane) :
    R.inverse (R.affine p) = p := by
  ext <;> simp [Rectangle.affine, Rectangle.inverse, R.width_pos.ne', R.height_pos.ne']

theorem Rectangle.affine_inverse (R : Rectangle) (p : Plane) :
    R.affine (R.inverse p) = p := by
  ext <;> dsimp [Rectangle.affine, Rectangle.inverse] <;>
    field_simp [R.width_pos.ne', R.height_pos.ne'] <;> ring

theorem Rectangle.affine_injective (R : Rectangle) : Function.Injective R.affine :=
  Function.LeftInverse.injective R.inverse_affine

theorem Rectangle.affine_contDiff (R : Rectangle) : ContDiff ℝ 2 R.affine := by
  dsimp [Rectangle.affine]
  fun_prop

def region (R : Rectangle) (δ : ℝ) : Set Plane := R.affine '' marginRectangle δ

theorem region_isCompact (R : Rectangle) (δ : ℝ) : IsCompact (region R δ) :=
  (isCompact_Icc.prod isCompact_Icc).image R.affine_contDiff.continuous

theorem support_pull (R : Rectangle) {δ : ℝ} (F : Plane → ℂ)
    (hs : Function.support F ⊆ region R δ) :
    Function.support (fun p => F (R.affine p)) ⊆ marginRectangle δ := by
  intro p hp
  obtain ⟨q, hq, heq⟩ := hs hp
  exact (R.affine_injective heq) ▸ hq

theorem compact_of_support (R : Rectangle) {δ : ℝ} {F : Plane → ℂ}
    (hs : Function.support F ⊆ region R δ) : HasCompactSupport F :=
  (region_isCompact R δ).of_isClosed_subset isClosed_tsupport
    (closure_minimal hs (region_isCompact R δ).isClosed)

theorem compact_pull (R : Rectangle) {δ : ℝ} {F : Plane → ℂ}
    (hs : Function.support F ⊆ region R δ) :
    HasCompactSupport (fun p => F (R.affine p)) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_tsupport
    (closure_minimal (support_pull R F hs) (isClosed_Icc.prod isClosed_Icc))

/-- Both affine changes of variable are literal Lebesgue substitutions. -/
theorem integral_affine_line (g : ℝ → ℝ) (a c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ, g (a + c*x)) = c⁻¹ * ∫ x : ℝ, g x := by
  have h := Measure.integral_comp_mul_left (fun t => g (a+t)) c
  rw [integral_add_left_eq_self] at h
  simpa only [abs_of_pos (inv_pos.mpr hc), smul_eq_mul] using h

theorem integral_affine_plane (R : Rectangle) (G : Plane → ℝ)
    (hG : Integrable G) (hGC : Integrable (fun p => G (R.affine p))) :
    (∫ p : Plane, G (R.affine p)) =
      (R.width * R.height)⁻¹ * ∫ p : Plane, G p := by
  rw [Measure.volume_eq_prod] at hG hGC ⊢
  rw [integral_prod _ hGC]
  simp_rw [Rectangle.affine, integral_affine_line _ R.bottom R.height R.height_pos]
  rw [integral_const_mul, integral_affine_line _ R.left R.width R.width_pos,
    ← integral_prod G hG]
  ring

structure RectangleSeed (R : Rectangle) (δ : ℝ) where
  function : Plane → ℂ
  smooth : ContDiff ℝ 2 function
  support_subset : Function.support function ⊆ region R δ

def normalized {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) : Seed δ :=
  ⟨fun p => s.function (R.affine p), s.smooth.comp R.affine_contDiff,
    support_pull R s.function s.support_subset⟩

def physical {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) : PhysicalL2 :=
  (s.smooth.continuous.memLp_of_hasCompactSupport
    (compact_of_support R s.support_subset)).toLp s.function

theorem physical_square {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    ‖physical s‖^2 = ∫ p : Plane, ‖s.function p‖^2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (physical s) (physical s))]
  apply integral_congr_ae
  filter_upwards [(s.smooth.continuous.memLp_of_hasCompactSupport
    (compact_of_support R s.support_subset)).coeFn_toLp] with p hp
  simp only [hp, inner_self_eq_norm_sq_to_K, Complex.ofReal_re]

theorem normalized_square {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    ‖physicalSeed (normalized s)‖^2 = (R.width * R.height)⁻¹ * ‖physical s‖^2 := by
  rw [physicalSeed_square, physical_square]
  apply integral_affine_plane
  · exact (s.smooth.continuous.norm.pow 2).integrable_of_hasCompactSupport
      ((compact_of_support R s.support_subset).norm.comp_left (g := fun t : ℝ => t^2) (by simp))
  · exact ((normalized s).smooth.continuous.norm.pow 2).integrable_of_hasCompactSupport
      ((seed_compactSupport (normalized s)).norm.comp_left (g := fun t : ℝ => t^2) (by simp))

def diagonal (R : Rectangle) : Plane →L[ℝ] Plane :=
  (R.width • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (R.height • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem affine_hasFDerivAt (R : Rectangle) (p : Plane) :
    HasFDerivAt R.affine (diagonal R) p := by
  simpa only [Rectangle.affine, diagonal, zero_add] using
    ((hasFDerivAt_const p (R.left,R.bottom)).add (diagonal R).hasFDerivAt)

def side (R : Rectangle) (j : Fin 2) : ℝ := if j = 0 then R.width else R.height

/-- The derivative is the actual Fréchet derivative of the normalized
function. Its scaling is proved, rather than encoded as a Fourier input. -/
theorem normalized_partial {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ)
    (j : Fin 2) (p : Plane) :
    partial (normalized s).function j p =
      R.side j • partial s.function j (R.affine p) := by
  have hd := ((s.smooth.differentiable (by norm_num) (R.affine p)).hasFDerivAt.comp p
    (affine_hasFDerivAt R p)).fderiv
  change fderiv ℝ (fun q => s.function (R.affine q)) p (direction j) = _
  rw [hd]
  fin_cases j <;> simp [diagonal, side, partial, direction, map_smul]

theorem partial_support_region {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ)
    (j : Fin 2) : Function.support (partial s.function j) ⊆ region R δ := by
  exact (subset_closure.trans (tsupport_fderiv_apply_subset ℝ (direction j))).trans
    (closure_minimal s.support_subset (region_isCompact R δ).isClosed)

def directionalEnergy {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) (j : Fin 2) : ℝ :=
  ∫ p : Plane, ‖partial s.function j p‖^2

theorem normalized_directional_energy {R : Rectangle} {δ : ℝ}
    (s : RectangleSeed R δ) (j : Fin 2) :
    (∫ p : Plane, ‖partial (normalized s).function j p‖^2) =
      (R.side j)^2 * (R.width * R.height)⁻¹ * directionalEnergy s j := by
  simp_rw [normalized_partial, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul]
  have hc := partial_continuous s.function s.smooth j
  have hs := partial_support_region s j
  rw [integral_affine_plane R (fun p => ‖partial s.function j p‖^2)
    ((hc.norm.pow 2).integrable_of_hasCompactSupport
      ((compact_of_support R hs).norm.comp_left (g := fun t : ℝ => t^2) (by simp)))
    (((hc.comp R.affine_contDiff.continuous).norm.pow 2).integrable_of_hasCompactSupport
      ((compact_pull R hs).norm.comp_left (g := fun t : ℝ => t^2) (by simp)))]
  dsimp [directionalEnergy]
  ring

/-- The two constants are width/height and height/width. A rectangle's
height cannot be discarded by reusing the unit-square energy unchanged. -/
theorem normalized_energy {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    physicalEnergy (normalized s) =
      (R.width / R.height) * directionalEnergy s 0 +
      (R.height / R.width) * directionalEnergy s 1 := by
  simp only [physicalEnergy, Fin.sum_univ_two, normalized_directional_energy, side,
    if_pos rfl, Fin.one_ne_zero, if_false]
  field_simp [R.width_pos.ne', R.height_pos.ne']
  <;> ring

theorem region_height {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ) {p : Plane}
    (hp : p ∈ region R δ) : R.bottom ≤ p.2 ∧ p.2 ≤ R.bottom + R.height := by
  obtain ⟨q, hq, rfl⟩ := hp
  dsimp [Rectangle.affine]
  have hq0 : 0 ≤ q.2 := hδ.trans hq.2.1
  have hq1 : q.2 ≤ 1 := by linarith [hq.2.2]
  constructor <;> nlinarith [R.height_pos]

/-- The literal hyperbolic density on the physical rectangle. -/
theorem hyperbolic_density_bounds (R : Rectangle) {p : Plane}
    (hp : R.bottom ≤ p.2 ∧ p.2 ≤ R.bottom + R.height) :
    ((R.bottom + R.height)⁻¹)^2 ≤ (p.2⁻¹)^2 ∧
      (p.2⁻¹)^2 ≤ (R.bottom⁻¹)^2 := by
  have hp0 : 0 < p.2 := R.bottom_pos.trans_le hp.1
  have hlo := one_div_le_one_div_of_le hp0 hp.2
  have hhi := one_div_le_one_div_of_le R.bottom_pos hp.1
  simp only [one_div] at hlo hhi
  constructor
  · exact pow_le_pow_left₀ (by positivity) hlo 2
  · exact pow_le_pow_left₀ (by positivity) hhi 2

end
end ImbalancedChen.Part3.PositiveRectangleAffineNormalization20261026b
