import ImbalancedChen.Part3Gamma0PositiveRectangleRellichCharts
import ImbalancedChen.Part3Gamma0CompactCoreGradient

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Actual coordinate product differentiation and actual Mobius covariance
give a pointwise localized chart mass/gradient budget. Only the cutoff's
value and its own geometric gradient are bounded inputs. No local H1
budget for the automorphic function is assumed. Integration and passage
from the genuine core to the completed form are subsequent obligations. -/

namespace ImbalancedChen.Part3.Gamma0LocalizedChartPointwiseEnergy20261026b
noncomputable section
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactGreenProductL120261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0LocalFourierTailCharts20261026a
open ActualGamma0MaassDescent20261025a
open ActualMobiusDirichletCovariance20261025a
open ActualPoincareDirichletTrace20261025a
open ActualPoincareGradientEnergyBudget20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open ActualGamma0CoreDirichletForm20261025a

theorem sliceDx_mul_at (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    sliceDx (F*G) p = sliceDx F p * G p + F p * sliceDx G p := by
  have hline := (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hf := (hF.hasFDerivAt.comp_hasDerivAt p.1 hline).differentiableAt
  have hg := (hG.hasFDerivAt.comp_hasDerivAt p.1 hline).differentiableAt
  simpa only [sliceDx, Pi.mul_apply] using deriv_mul hf hg

theorem sliceDy_mul_at (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    sliceDy (F*G) p = sliceDy F p * G p + F p * sliceDy G p := by
  have hline := (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hf := (hF.hasFDerivAt.comp_hasDerivAt p.2 hline).differentiableAt
  have hg := (hG.hasFDerivAt.comp_hasDerivAt p.2 hline).differentiableAt
  simpa only [sliceDy, Pi.mul_apply] using deriv_mul hf hg

theorem complex_norm_add_square_le (a b : ℂ) :
    ‖a+b‖^2 ≤ 2*‖a‖^2 + 2*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- The two genuine coordinate product derivatives imply the geometric
cutoff energy bound, with the necessary factor two retained. -/
theorem chartEnergy_mul_le (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    chartEnergy (F*G) p ≤
      2*‖F p‖^2*chartEnergy G p + 2*‖G p‖^2*chartEnergy F p := by
  have hx := complex_norm_add_square_le (sliceDx F p * G p) (F p * sliceDx G p)
  have hy := complex_norm_add_square_le (sliceDy F p * G p) (F p * sliceDy G p)
  simp only [norm_mul, mul_pow] at hx hy
  unfold chartEnergy
  rw [sliceDx_mul_at F G p hF hG, sliceDy_mul_at F G p hF hG]
  have h := mul_le_mul_of_nonneg_left (add_le_add hx hy) (sq_nonneg p.2)
  nlinarith

def coreClassPullback (N : ℕ) [NeZero N] (u : smoothCore N)
    (q : gamma0Classes N) (z : UpperHalfPlane) : ℂ :=
  coreRepresentative N u (inverseClassRep N q • z)

theorem classPullback_chart_germ (N : ℕ) [NeZero N] (u : smoothCore N)
    (q : gamma0Classes N) {p : ℝ × ℝ} (hp : 0 < p.2) :
    extendUpper (coreClassPullback N u q) =ᶠ[𝓝 p]
      (fun r => extendUpper (coreRepresentative N u) (mobiusChart (inverseClassRep N q) r)) := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with r hr
  rw [extendUpper_chartLift _ r hr, extendUpper_mobiusChart _ _ r hr]
  rfl

theorem coreClassPullback_C2 (N : ℕ) [NeZero N] (u : smoothCore N)
    (q : gamma0Classes N) :
    ContDiffOn ℝ 2 (extendUpper (coreClassPullback N u q)) positiveChart := by
  intro p hp
  let g := inverseClassRep N q
  have hgp : 0 < (mobiusChart g p).2 := by
    rw [mobiusChart_eq_actual g hp]
    exact (g • chartLift p).im_pos
  have hF2 : ContDiffOn ℝ 2 (extendUpper (coreRepresentative N u)) positiveChart :=
    (coreRepresentative_cinfty N u).of_le (by norm_num)
  have hf := (hF2 (mobiusChart g p) hgp).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hgp)
  exact ((hf.comp p (mobiusChart_contDiffAt g hp)).congr_of_eventuallyEq
    (classPullback_chart_germ N u q hp)).contDiffWithinAt

/-- Exact hyperbolic first-energy covariance for each actual inverse
class representative. The RHS is the canonical quotient form density. -/
theorem coreClassPullback_energy (N : ℕ) [NeZero N] (u : smoothCore N)
    (q : gamma0Classes N) (z : UpperHalfPlane) :
    chartEnergy (extendUpper (coreClassPullback N u q)) (z.re,z.im) =
      (coreDirichletDensity N u u
        (orbitProjection N (inverseClassRep N q • z))).re := by
  let g := inverseClassRep N q
  let p : ℝ × ℝ := (z.re,z.im)
  have hp : 0 < p.2 := z.im_pos
  have hgp : 0 < (mobiusChart g p).2 := by
    rw [mobiusChart_eq_actual g hp]
    exact (g • chartLift p).im_pos
  have hf : ContDiffAt ℝ 1 (extendUpper (coreRepresentative N u)) (mobiusChart g p) :=
    (((coreRepresentative_cinfty N u).of_le (by norm_num)) _ hgp).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hgp)
  rw [chartEnergy_eq_re_hyperbolicDirichlet,
    hyperbolicChartDirichlet_congr_of_eventuallyEq
      (classPullback_chart_germ N u q hp) (classPullback_chart_germ N u q hp),
    hyperbolicChartDirichlet_comp_mobiusChart g _ _ p hp hf hf,
    coreDirichletDensity_projection]
  rw [mobiusChart_eq_actual g hp, chartLift_pair]
  rfl

theorem localized_chart_product (N : ℕ) [NeZero N] (u : smoothCore N)
    (ρ : UpperHalfPlane → ℂ) (q : gamma0Classes N) :
    extendUpper (localizedClassChart N (coreRepresentative N u) ρ q) =
      extendUpper ρ * extendUpper (coreClassPullback N u q) := by
  funext p
  by_cases hp : 0 < p.2 <;>
    simp [extendUpper, hp, localizedClassChart, coreClassPullback]

/-- Explicit local chart budget at a point. B bounds only the cutoff;
D bounds only its own geometric gradient. The automorphic function's
energy is the ACTUAL canonical quotient Dirichlet density. -/
theorem localized_chart_mass_energy_le (N : ℕ) [NeZero N] (u : smoothCore N)
    (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (q : gamma0Classes N) (z : UpperHalfPlane) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hρB : ‖ρ z‖ ≤ B)
    (hρD : chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) :
    ‖localizedClassChart N (coreRepresentative N u) ρ q z‖^2 +
      chartEnergy (extendUpper (localizedClassChart N (coreRepresentative N u) ρ q))
        (z.re,z.im) ≤
      (B^2+2*D) * ‖coreRepresentative N u (inverseClassRep N q • z)‖^2 +
      2*B^2 * (coreDirichletDensity N u u
        (orbitProjection N (inverseClassRep N q • z))).re := by
  let p : ℝ × ℝ := (z.re,z.im)
  have hρAt := (hρ p z.im_pos).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)
  have hfAt := (coreClassPullback_C2 N u q p z.im_pos).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)
  have he := chartEnergy_mul_le (extendUpper ρ) (extendUpper (coreClassPullback N u q)) p
    (hρAt.differentiableAt (by norm_num)) (hfAt.differentiableAt (by norm_num))
  rw [← localized_chart_product, coreClassPullback_energy,
    extendUpper_pair, extendUpper_pair] at he
  have hBs := pow_le_pow_left₀ (norm_nonneg (ρ z)) hρB 2
  have hn := sq_nonneg ‖coreRepresentative N u (inverseClassRep N q • z)‖
  have hE := coreDirichletDensity_self_re_nonneg N u
    (orbitProjection N (inverseClassRep N q • z))
  have h1 := mul_le_mul_of_nonneg_right hBs hn
  have h2 := mul_le_mul_of_nonneg_right hBs hE
  have h3 := mul_le_mul_of_nonneg_right hρD hn
  simp only [localizedClassChart, norm_mul, mul_pow]
  dsimp [coreClassPullback] at he
  nlinarith

end
end ImbalancedChen.Part3.Gamma0LocalizedChartPointwiseEnergy20261026b
