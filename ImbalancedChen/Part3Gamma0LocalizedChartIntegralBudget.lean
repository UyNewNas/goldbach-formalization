import ImbalancedChen.Part3Gamma0LocalizedChartPointwiseEnergy
import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Integrating the actual local product derivatives gives a genuine chart
mass-plus-two-gradient budget from the ORIGINAL quotient norm and form.
The constant is the proper-action compact overlap of the ACTUAL Mobius
image of the cutoff support. No local chart energy budget is assumed.
This leaf proves the smooth-core estimate needed for dense form completion. -/

namespace ImbalancedChen.Part3.Gamma0LocalizedChartIntegralBudget20261026b
noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open Gamma0LocalizedChartPointwiseEnergy20261026b
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0QuotientCellPushforward20261025a
open Gamma0CompactGlobalOverlap20261025a
open Gamma0CompactQuotientLocalLp20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0CompactCoreGradient20261025a
open ActualGamma0CoreDirichletForm20261025a
open ActualGamma0MaassDescent20261025a
open Gamma0CompactGreenProductL120261025a
open ActualPoincareGradientEnergyBudget20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0LocalFourierTailCharts20261026a
open MaassWeakOperatorCore20261024zz

def classAction (N : ℕ) [NeZero N] (q : gamma0Classes N) (z : UpperHalfPlane) :
    UpperHalfPlane := inverseClassRep N q • z

theorem classAction_continuous (N : ℕ) [NeZero N] (q : gamma0Classes N) :
    Continuous (classAction N q) := by
  change Continuous (fun z : UpperHalfPlane =>
    (Matrix.SpecialLinearGroup.mapGL ℝ (inverseClassRep N q)) • z)
  exact continuous_const_smul _

theorem classAction_measurePreserving (N : ℕ) [NeZero N] (q : gamma0Classes N) :
    MeasurePreserving (classAction N q) (volume : Measure UpperHalfPlane) volume := by
  change MeasurePreserving (fun z : UpperHalfPlane =>
    (Matrix.SpecialLinearGroup.mapGL ℝ (inverseClassRep N q)) • z) volume volume
  exact measurePreserving_smul _ _

theorem classAction_measurableEmbedding (N : ℕ) [NeZero N] (q : gamma0Classes N) :
    MeasurableEmbedding (classAction N q) := by
  change MeasurableEmbedding (fun z : UpperHalfPlane =>
    (Matrix.SpecialLinearGroup.mapGL ℝ (inverseClassRep N q)) • z)
  exact measurableEmbedding_const_smul _

def chartOverlap (N : ℕ) [NeZero N] (K : Set UpperHalfPlane) (q : gamma0Classes N) : ℕ :=
  compactOverlapBound N (classAction N q '' K)

theorem core_compact_mass_bound (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (u : smoothCore N) :
    (∫ z in K, ‖coreRepresentative N u z‖^2) ≤
      (compactOverlapBound N K : ℝ) * ‖(u : QuotientL2 N)‖^2 := by
  have hF : MemLp (chosenQuotientRepresentative N u) 2 (carrierPushforward N) :=
    (u : QuotientL2 N).memLp.ae_eq (chosenRepresentative_spec N u).1
  have h := quotient_memLp_two_compact_integral_sq_le N hK hF
  have hglobal : (∫ q, ‖chosenQuotientRepresentative N u q‖^2 ∂carrierPushforward N) =
      ‖(u : QuotientL2 N)‖^2 := by
    calc
      _ = ∫ q, ‖(u : QuotientL2 N) q‖^2 ∂carrierPushforward N :=
        integral_congr_ae ((chosenRepresentative_spec N u).1.symm.mono
          (fun q hq => by rw [hq]))
      _ = _ := by
        apply Complex.ofRealLI.injective
        simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
          (L2.inner_def (𝕜 := ℂ) (u : QuotientL2 N) (u : QuotientL2 N)).symm
  rw [hglobal] at h
  exact h

theorem actual_chart_mass_bound (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (u : smoothCore N) (q : gamma0Classes N) :
    (∫ z in K, ‖coreRepresentative N u (inverseClassRep N q • z)‖^2) ≤
      (chartOverlap N K q : ℝ) * ‖(u : QuotientL2 N)‖^2 := by
  have hI := hK.image (classAction_continuous N q)
  have he := (classAction_measurePreserving N q).setIntegral_image_emb
    (classAction_measurableEmbedding N q) (fun z => ‖coreRepresentative N u z‖^2) K
  rw [← he]
  exact core_compact_mass_bound N hI u

theorem actual_chart_gradient_bound (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (u : smoothCore N) (q : gamma0Classes N) :
    (∫ z in K, (coreDirichletDensity N u u
      (orbitProjection N (inverseClassRep N q • z))).re) ≤
      (chartOverlap N K q : ℝ) * (coreDirichletForm N u u).re := by
  have hI := hK.image (classAction_continuous N q)
  have he := (classAction_measurePreserving N q).setIntegral_image_emb
    (classAction_measurableEmbedding N q)
    (fun z => ‖weightedCoreGradient N u z‖^2) K
  have hg : (∫ z in K, (coreDirichletDensity N u u
      (orbitProjection N (inverseClassRep N q • z))).re) =
      ∫ z in K, ‖weightedCoreGradient N u (classAction N q z)‖^2 := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => (weightedCoreGradient_norm_sq N u _).symm)
  rw [hg, ← he]
  exact weightedCoreGradient_compact_integral_le N hI u

theorem native_chartEnergy_continuous (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart) :
    Continuous (fun z : UpperHalfPlane => chartEnergy (extendUpper f) (z.re,z.im)) := by
  have hchart : Continuous (fun z : UpperHalfPlane => (z.re,z.im)) :=
    UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im
  have hF : ContDiffOn ℝ 1 (extendUpper f) positiveChart := hf.of_le (by norm_num)
  have hx : Continuous (fun z : UpperHalfPlane => sliceDx (extendUpper f) (z.re,z.im)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((sliceDx_continuousOn_of_C1 _ hF).continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)).comp hchart.continuousAt
  have hy : Continuous (fun z : UpperHalfPlane => sliceDy (extendUpper f) (z.re,z.im)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((sliceDy_continuousOn_of_C1 _ hF).continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)).comp hchart.continuousAt
  exact (UpperHalfPlane.continuous_im.pow 2).mul ((hx.norm.pow 2).add (hy.norm.pow 2))

/-- This is the literal mass and both physical derivative squares, in
canonical volume: the y² multiplying the derivatives cancels dy/y². -/
def localizedChartH1Mass (N : ℕ) [NeZero N] (K : Set UpperHalfPlane)
    (u : smoothCore N) (ρ : UpperHalfPlane → ℂ) (q : gamma0Classes N) : ℝ :=
  ∫ z in K, ‖localizedClassChart N (coreRepresentative N u) ρ q z‖^2 +
    chartEnergy (extendUpper (localizedClassChart N (coreRepresentative N u) ρ q))
      (z.re,z.im)

/-- A genuine integrated actual quotient-form chart budget. All
automorphic dependence is the ORIGINAL quotient mass and Dirichlet form;
B,D concern only rho and its own geometric gradient on the compact K. -/
theorem localizedChartH1Mass_bound (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (u : smoothCore N) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρB : ∀ z ∈ K, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) :
    localizedChartH1Mass N K u ρ q ≤
      (chartOverlap N K q : ℝ) * (B^2+2*D) * ‖(u : QuotientL2 N)‖^2 +
      (chartOverlap N K q : ℝ) * (2*B^2) * (coreDirichletForm N u u).re := by
  have hF := localizedClassChart_C2 N (coreRepresentative N u) ρ
    ((coreRepresentative_cinfty N u).of_le (by norm_num)) hρ q
  have hleft : IntegrableOn (fun z : UpperHalfPlane =>
      ‖localizedClassChart N (coreRepresentative N u) ρ q z‖^2 +
      chartEnergy (extendUpper (localizedClassChart N (coreRepresentative N u) ρ q))
        (z.re,z.im)) K :=
    (((native_C2_continuous _ hF).norm.pow 2).add
      (native_chartEnergy_continuous _ hF)).continuousOn.integrableOn_compact hK
  have hm : IntegrableOn (fun z : UpperHalfPlane =>
      ‖coreRepresentative N u (inverseClassRep N q • z)‖^2) K :=
    (((coreRepresentative_continuous N u).comp (classAction_continuous N q)).norm.pow 2).
      continuousOn.integrableOn_compact hK
  have hg : IntegrableOn (fun z : UpperHalfPlane => (coreDirichletDensity N u u
      (orbitProjection N (inverseClassRep N q • z))).re) K := by
    have hc := (((weightedCoreGradient_continuous N u).comp
      (classAction_continuous N q)).norm.pow 2).continuousOn.integrableOn_compact hK
    exact hc.congr (Eventually.of_forall (fun z => weightedCoreGradient_norm_sq N u _))
  have hright := (hm.const_mul (B^2+2*D)).add (hg.const_mul (2*B^2))
  have hle := integral_mono_ae hleft hright (by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact localized_chart_mass_energy_le N u ρ hρ q z B D hB hD (hρB z hz) (hρD z hz))
  rw [integral_add (hm.const_mul _) (hg.const_mul _), integral_const_mul,
    integral_const_mul] at hle
  apply hle.trans
  have hmB := mul_le_mul_of_nonneg_left (actual_chart_mass_bound N hK u q)
    (show 0 ≤ B^2+2*D by positivity)
  have hgB := mul_le_mul_of_nonneg_left (actual_chart_gradient_bound N hK u q)
    (show 0 ≤ 2*B^2 by positivity)
  nlinarith

/-- The same estimate on the actual shifted energy core, with no
uncontrolled chart norm. This is the uniform dense-core budget. -/
theorem localizedChartH1Mass_energy_bound (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (u : EnergyCore N) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρB : ∀ z ∈ K, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) :
    localizedChartH1Mass N K u ρ q ≤
      (chartOverlap N K q : ℝ) * (3*B^2+2*D) * ‖u‖^2 := by
  have h := localizedChartH1Mass_bound N hK u ρ hρ q B D hB hD hρB hρD
  have hp := pow_le_pow_left₀ (norm_nonneg (physicalCore N u))
    (physical_norm_le_energy_norm N u) 2
  have hd := coreDirichlet_le_energy_norm_sq N u
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (chartOverlap N K q : ℝ)*(B^2+2*D) by positivity)
  have hg := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ (chartOverlap N K q : ℝ)*(2*B^2) by positivity)
  change ‖(u : QuotientL2 N)‖^2 ≤ ‖u‖^2 at hp
  change (chartOverlap N K q : ℝ)*(B^2+2*D)*‖(u : QuotientL2 N)‖^2 ≤ _ at hm
  nlinarith

end
end ImbalancedChen.Part3.Gamma0LocalizedChartIntegralBudget20261026b
