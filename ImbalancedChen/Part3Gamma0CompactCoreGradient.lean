import ImbalancedChen.Part3ActualGamma0CoreDirichletForm
import ImbalancedChen.Part3ActualPoincareGradientEnergyBudget
import ImbalancedChen.Part3Gamma0CompactQuotientMeasureDomination
import ImbalancedChen.Part3Gamma0ActualEnergyCompletion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The genuine weighted coordinate gradient of the existing canonical smooth
Gamma0 core representative is a TWO-COMPONENT vector on H. Its squared
norm is the already proved orbit-descended geometric Dirichlet density.
Compact quotient-measure domination therefore bounds its local L2 mass
by the actual global quotient Dirichlet form. Neither the vector gradient
nor its separate components are claimed to descend to the scalar quotient.
No local-gradient-L2 or energy-budget conclusion is an input premise.
-/

namespace ImbalancedChen.Part3.Gamma0CompactCoreGradient20261025a

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a
open ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a
open ImbalancedChen.Part3.ActualPoincareGradientEnergyBudget20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.ActualGamma0CoreDirichletForm20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientMeasureDomination20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a

abbrev GradientFiber := EuclideanSpace ℂ (Fin 2)

def weightedCoreGradient (N : ℕ) [NeZero N] (u : smoothCore N)
    (z : UpperHalfPlane) : GradientFiber :=
  !₂[(z.im : ℂ)*sliceDx (extendUpper (coreRepresentative N u)) (z.re,z.im),
    (z.im : ℂ)*sliceDy (extendUpper (coreRepresentative N u)) (z.re,z.im)]

theorem weightedCoreGradient_norm_sq (N : ℕ) [NeZero N] (u : smoothCore N)
    (z : UpperHalfPlane) :
    ‖weightedCoreGradient N u z‖^2 =
      (coreDirichletDensity N u u (orbitProjection N z)).re := by
  rw [coreDirichletDensity_projection]
  change ‖weightedCoreGradient N u z‖^2 =
    (hyperbolicChartDirichlet (extendUpper (coreRepresentative N u))
      (extendUpper (coreRepresentative N u)) (z.re,z.im)).re
  rw [← chartEnergy_eq_re_hyperbolicDirichlet,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [weightedCoreGradient,PiLp.toLp_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos z.im_pos,mul_pow,chartEnergy]
  ring

theorem weightedCoreGradient_continuous (N : ℕ) [NeZero N] (u : smoothCore N) :
    Continuous (weightedCoreGradient N u) := by
  have hchart : Continuous (fun z : UpperHalfPlane => (z.re,z.im)) :=
    UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im
  have hF : ContDiffOn ℝ 1 (extendUpper (coreRepresentative N u)) positiveChart :=
    (coreRepresentative_cinfty N u).of_le (by norm_num)
  have hDx : Continuous (fun z : UpperHalfPlane =>
      sliceDx (extendUpper (coreRepresentative N u)) (z.re,z.im)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((sliceDx_continuousOn_of_C1 _ hF).continuousAt
      (positiveChart_isOpen.mem_nhds z.im_pos)).comp hchart.continuousAt
  have hDy : Continuous (fun z : UpperHalfPlane =>
      sliceDy (extendUpper (coreRepresentative N u)) (z.re,z.im)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((sliceDy_continuousOn_of_C1 _ hF).continuousAt
      (positiveChart_isOpen.mem_nhds z.im_pos)).comp hchart.continuousAt
  apply PiLp.continuous_toLp.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul hDx
  · exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul hDy

theorem weightedCoreGradient_compact_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : smoothCore N) :
    MemLp (weightedCoreGradient N u) 2 ((volume : Measure UpperHalfPlane).restrict K) := by
  have hc := weightedCoreGradient_continuous N u
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact ContinuousOn.integrableOn_compact hK (hc.norm.pow 2).continuousOn

theorem weightedCoreGradient_compact_lintegral_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : smoothCore N) :
    (∫⁻ z in K, ENNReal.ofReal (‖weightedCoreGradient N u z‖^2)) ≤
      (compactOverlapBound N K : ℝ≥0∞)*
        ∫⁻ q, ENNReal.ofReal ((coreDirichletDensity N u u q).re) ∂carrierPushforward N := by
  have hdom := compactQuotientPushforward_le N hK
  have hAC : compactQuotientPushforward N K ≪ carrierPushforward N :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hE : AEMeasurable (fun q => ENNReal.ofReal ((coreDirichletDensity N u u q).re))
      (compactQuotientPushforward N K) :=
    ((coreDirichletDensity_integrable N u u).re.aestronglyMeasurable.aemeasurable
      .ennreal_ofReal).mono_ac hAC
  calc
    _ = ∫⁻ q, ENNReal.ofReal ((coreDirichletDensity N u u q).re)
        ∂compactQuotientPushforward N K := by
      rw [lintegral_map' hE (orbitProjection_measurable N).aemeasurable]
      exact lintegral_congr_ae (Eventually.of_forall (fun z =>
        congrArg ENNReal.ofReal (weightedCoreGradient_norm_sq N u z)))
    _ ≤ ∫⁻ q, ENNReal.ofReal ((coreDirichletDensity N u u q).re)
        ∂((compactOverlapBound N K : ℝ≥0∞) • carrierPushforward N) :=
      lintegral_mono_measure hdom
    _ = _ := by rw [lintegral_smul_measure]; rfl

/-- Actual geometric local gradient mass, with the true compact proper
action overlap constant and the canonical global quotient Dirichlet form. -/
theorem weightedCoreGradient_compact_integral_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : smoothCore N) :
    (∫ z in K, ‖weightedCoreGradient N u z‖^2) ≤
      (compactOverlapBound N K : ℝ)*(coreDirichletForm N u u).re := by
  have hi := (weightedCoreGradient_compact_memLp N hK u).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  have hE := (coreDirichletDensity_integrable N u u).re
  have hlocal : 0 ≤ᵐ[(volume : Measure UpperHalfPlane).restrict K]
      (fun z => ‖weightedCoreGradient N u z‖^2) :=
    Eventually.of_forall (fun _ => sq_nonneg _)
  have hglobal : 0 ≤ᵐ[carrierPushforward N]
      (fun q => (coreDirichletDensity N u u q).re) :=
    Eventually.of_forall (coreDirichletDensity_self_re_nonneg N u)
  have h := weightedCoreGradient_compact_lintegral_le N hK u
  rw [← ofReal_integral_eq_lintegral_ofReal hi hlocal,
    ← ofReal_integral_eq_lintegral_ofReal hE hglobal] at h
  have hr := ENNReal.toReal_mono (by simp) h
  have heq : (∫ q, (coreDirichletDensity N u u q).re ∂carrierPushforward N) =
      (coreDirichletForm N u u).re :=
    integral_re (coreDirichletDensity_integrable N u u)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hlocal),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hglobal),heq] using hr

theorem coreDirichlet_le_energy_norm_sq (N : ℕ) [NeZero N] (u : EnergyCore N) :
    (coreDirichletForm N u u).re ≤ ‖u‖^2 := by
  rw [energy_norm_sq,coreDirichletForm_eq_operatorPair]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem weightedCoreGradient_compact_energy_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : EnergyCore N) :
    (∫ z in K, ‖weightedCoreGradient N u z‖^2) ≤
      (compactOverlapBound N K : ℝ)*‖u‖^2 :=
  (weightedCoreGradient_compact_integral_le N hK u).trans
    (mul_le_mul_of_nonneg_left (coreDirichlet_le_energy_norm_sq N u) (Nat.cast_nonneg _))

private theorem sliceDx_add_at (F G : ℝ × ℝ → ℂ)
    (hF : ContDiffOn ℝ 1 F positiveChart) (hG : ContDiffOn ℝ 1 G positiveChart)
    {p : ℝ × ℝ} (hp : p ∈ positiveChart) :
    sliceDx (F+G) p = sliceDx F p+sliceDx G p := by
  have hdF := hF.differentiableOn (by norm_num)
  have hdG := hG.differentiableOn (by norm_num)
  rw [sliceDx_eq_fderiv _ (hdF.add hdG) hp,sliceDx_eq_fderiv _ hdF hp,
    sliceDx_eq_fderiv _ hdG hp,fderiv_add
      ((hdF p hp).differentiableAt (positiveChart_isOpen.mem_nhds hp))
      ((hdG p hp).differentiableAt (positiveChart_isOpen.mem_nhds hp))]
  rfl

private theorem sliceDy_add_at (F G : ℝ × ℝ → ℂ)
    (hF : ContDiffOn ℝ 1 F positiveChart) (hG : ContDiffOn ℝ 1 G positiveChart)
    {p : ℝ × ℝ} (hp : p ∈ positiveChart) :
    sliceDy (F+G) p = sliceDy F p+sliceDy G p := by
  have hdF := hF.differentiableOn (by norm_num)
  have hdG := hG.differentiableOn (by norm_num)
  rw [sliceDy_eq_fderiv _ (hdF.add hdG) hp,sliceDy_eq_fderiv _ hdF hp,
    sliceDy_eq_fderiv _ hdG hp,fderiv_add
      ((hdF p hp).differentiableAt (positiveChart_isOpen.mem_nhds hp))
      ((hdG p hp).differentiableAt (positiveChart_isOpen.mem_nhds hp))]
  rfl

theorem weightedCoreGradient_add (N : ℕ) [NeZero N] (u v : smoothCore N) :
    weightedCoreGradient N (u+v) = weightedCoreGradient N u+weightedCoreGradient N v := by
  funext z
  have hF := (coreRepresentative_cinfty N u).of_le (show (1 : ℕ∞ω) ≤ ∞ by norm_num)
  have hG := (coreRepresentative_cinfty N v).of_le (show (1 : ℕ∞ω) ≤ ∞ by norm_num)
  unfold weightedCoreGradient
  rw [coreRepresentative_add,Gamma0ActualSmoothQuotientCore20261025a.extendUpper_add,
    sliceDx_add_at _ _ hF hG z.im_pos,sliceDy_add_at _ _ hF hG z.im_pos]
  ext i
  fin_cases i <;> simp [mul_add]

theorem weightedCoreGradient_smul (N : ℕ) [NeZero N] (c : ℂ) (u : smoothCore N) :
    weightedCoreGradient N (c • u) = c • weightedCoreGradient N u := by
  funext z
  unfold weightedCoreGradient
  rw [coreRepresentative_smul,Gamma0ActualSmoothQuotientCore20261025a.extendUpper_smul]
  ext i
  fin_cases i <;>
    simp [sliceDx,sliceDy,Pi.smul_apply,smul_eq_mul,deriv_const_mul_field',mul_left_comm]

abbrev CompactGradientL2 (K : Set UpperHalfPlane) :=
  Lp GradientFiber 2 ((volume : Measure UpperHalfPlane).restrict K)

def coreGradientL2 (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K)
    (u : EnergyCore N) : CompactGradientL2 K :=
  (weightedCoreGradient_compact_memLp N hK u).toLp (weightedCoreGradient N u)

def coreGradientLinear (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K) :
    EnergyCore N →ₗ[ℂ] CompactGradientL2 K where
  toFun := coreGradientL2 N hK
  map_add' u v := by
    let hu := weightedCoreGradient_compact_memLp N hK u
    let hv := weightedCoreGradient_compact_memLp N hK v
    calc
      _ = (hu.add hv).toLp (weightedCoreGradient N u+weightedCoreGradient N v) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (fun z =>
          congrFun (weightedCoreGradient_add N u v) z))
      _ = _ := MemLp.toLp_add hu hv
  map_smul' c u := by
    let hu := weightedCoreGradient_compact_memLp N hK u
    calc
      _ = (hu.const_smul c).toLp (c • weightedCoreGradient N u) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (fun z =>
          congrFun (weightedCoreGradient_smul N c u) z))
      _ = _ := MemLp.toLp_const_smul c hu

theorem coreGradientL2_norm_sq (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : EnergyCore N) :
    ‖coreGradientL2 N hK u‖^2 = ∫ z in K, ‖weightedCoreGradient N u z‖^2 := by
  have hlp := weightedCoreGradient_compact_memLp N hK u
  have hnorm : (∫ z in K, ‖coreGradientL2 N hK u z‖^2) = ‖coreGradientL2 N hK u‖^2 := by
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using
      (L2.inner_def (𝕜 := ℂ) (coreGradientL2 N hK u) (coreGradientL2 N hK u)).symm
  rw [← hnorm]
  apply integral_congr_ae
  filter_upwards [hlp.coeFn_toLp] with z hz
  rw [hz]

theorem coreGradientL2_norm_sq_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : EnergyCore N) :
    ‖coreGradientL2 N hK u‖^2 ≤ (compactOverlapBound N K : ℝ)*‖u‖^2 := by
  rw [coreGradientL2_norm_sq]
  exact weightedCoreGradient_compact_energy_bound N hK u

theorem coreGradientLinear_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : EnergyCore N) :
    ‖coreGradientLinear N hK u‖ ≤ Real.sqrt (compactOverlapBound N K : ℝ)*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact coreGradientL2_norm_sq_bound N hK u

end
end ImbalancedChen.Part3.Gamma0CompactCoreGradient20261025a
