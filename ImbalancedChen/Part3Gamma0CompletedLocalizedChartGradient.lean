import ImbalancedChen.Part3Gamma0CompletedLocalizedChartValue
import Mathlib.Analysis.Normed.Operator.Extend

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
The actual localized chart gradient extends from the ORIGINAL dense
Gamma0 energy core to the ORIGINAL energy completion. The bound is
derived from the integrated actual chart product estimate, not supplied
as a local H1 assumption. Both components are genuine weighted physical
partial derivatives on the core. The completed value/gradient pair lies
in the strong closure of that actual derivative graph. -/

namespace ImbalancedChen.Part3.Gamma0CompletedLocalizedChartGradient20261026b
noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open Gamma0CompletedLocalizedChartValue20261026b
open Gamma0LocalizedChartIntegralBudget20261026b
open Gamma0LocalizedChartPointwiseEnergy20261026b
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0CompactCoreGradient20261025a
open Gamma0CompactQuotientPullbackLinear20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a
open Gamma0LocalFourierTailCharts20261026a
open ActualPoincareGradientEnergyBudget20261025a
open MaassWeakOperatorCore20261024zz

def nativeGradient (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : GradientFiber :=
  !₂[(z.im : ℂ)*sliceDx (extendUpper f) (z.re,z.im),
    (z.im : ℂ)*sliceDy (extendUpper f) (z.re,z.im)]

theorem nativeGradient_norm_sq (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖nativeGradient f z‖^2 = chartEnergy (extendUpper f) (z.re,z.im) := by
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [nativeGradient, PiLp.toLp_apply, Matrix.cons_val_zero,Matrix.cons_val_one,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos,mul_pow,chartEnergy]
  ring

theorem nativeGradient_continuous (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart) : Continuous (nativeGradient f) := by
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
  apply PiLp.continuous_toLp.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul hx
  · exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul hy

def localizedCoreFunction (N : ℕ) [NeZero N] (ρ : UpperHalfPlane → ℂ)
    (q : gamma0Classes N) (u : EnergyCore N) : UpperHalfPlane → ℂ :=
  localizedClassChart N (coreRepresentative N u) ρ q

theorem localizedCoreFunction_C2 (N : ℕ) [NeZero N] (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (u : EnergyCore N) : ContDiffOn ℝ 2 (extendUpper (localizedCoreFunction N ρ q u)) positiveChart :=
  localizedClassChart_C2 N (coreRepresentative N u) ρ
    ((coreRepresentative_cinfty N u).of_le (by norm_num)) hρ q

theorem localizedCoreFunction_add (N : ℕ) [NeZero N] (ρ : UpperHalfPlane → ℂ)
    (q : gamma0Classes N) (u v : EnergyCore N) :
    localizedCoreFunction N ρ q (u+v) = localizedCoreFunction N ρ q u + localizedCoreFunction N ρ q v := by
  funext z
  simp only [localizedCoreFunction,localizedClassChart,coreRepresentative_add,Pi.add_apply,mul_add]

theorem localizedCoreFunction_smul (N : ℕ) [NeZero N] (ρ : UpperHalfPlane → ℂ)
    (q : gamma0Classes N) (c : ℂ) (u : EnergyCore N) :
    localizedCoreFunction N ρ q (c • u) = c • localizedCoreFunction N ρ q u := by
  funext z
  simp only [localizedCoreFunction,localizedClassChart,coreRepresentative_smul,Pi.smul_apply,smul_eq_mul]
  ring

private theorem nativeGradient_add (f g : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    (hg : ContDiffOn ℝ 2 (extendUpper g) positiveChart) :
    nativeGradient (f+g) = nativeGradient f + nativeGradient g := by
  funext z
  have hdF := hf.differentiableOn (by norm_num)
  have hdG := hg.differentiableOn (by norm_num)
  have hp : (z.re,z.im) ∈ positiveChart := z.im_pos
  have hx : sliceDx (extendUpper f + extendUpper g) (z.re,z.im) =
      sliceDx (extendUpper f) (z.re,z.im)+sliceDx (extendUpper g) (z.re,z.im) := by
    rw [sliceDx_eq_fderiv _ (hdF.add hdG) hp,sliceDx_eq_fderiv _ hdF hp,
      sliceDx_eq_fderiv _ hdG hp,fderiv_add
        ((hdF _ hp).differentiableAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp))
        ((hdG _ hp).differentiableAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp))]
    rfl
  have hy : sliceDy (extendUpper f + extendUpper g) (z.re,z.im) =
      sliceDy (extendUpper f) (z.re,z.im)+sliceDy (extendUpper g) (z.re,z.im) := by
    rw [sliceDy_eq_fderiv _ (hdF.add hdG) hp,sliceDy_eq_fderiv _ hdF hp,
      sliceDy_eq_fderiv _ hdG hp,fderiv_add
        ((hdF _ hp).differentiableAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp))
        ((hdG _ hp).differentiableAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp))]
    rfl
  unfold nativeGradient
  rw [Gamma0ActualSmoothQuotientCore20261025a.extendUpper_add,hx,hy]
  ext i
  fin_cases i <;> simp [mul_add]

private theorem nativeGradient_smul (f : UpperHalfPlane → ℂ) (c : ℂ) :
    nativeGradient (c • f) = c • nativeGradient f := by
  funext z
  unfold nativeGradient
  rw [Gamma0ActualSmoothQuotientCore20261025a.extendUpper_smul]
  ext i
  fin_cases i <;>
    simp [sliceDx,sliceDy,Pi.smul_apply,smul_eq_mul,deriv_const_mul_field',mul_left_comm]

theorem localizedCoreGradient_memLp (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (u : EnergyCore N) : MemLp (nativeGradient (localizedCoreFunction N ρ q u)) 2
      ((volume : Measure UpperHalfPlane).restrict K) := by
  have hc := nativeGradient_continuous _ (localizedCoreFunction_C2 N ρ hρ q u)
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    ((hc.norm.pow 2).continuousOn.integrableOn_compact hK)

def localizedCoreGradient (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (u : EnergyCore N) : CompactGradientL2 K :=
  (localizedCoreGradient_memLp N hK ρ hρ q u).toLp (nativeGradient (localizedCoreFunction N ρ q u))

def localizedCoreGradientLinear (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N) :
    EnergyCore N →ₗ[ℂ] CompactGradientL2 K where
  toFun := localizedCoreGradient N hK ρ hρ q
  map_add' u v := by
    let hu := localizedCoreGradient_memLp N hK ρ hρ q u
    let hv := localizedCoreGradient_memLp N hK ρ hρ q v
    calc
      _ = (hu.add hv).toLp (nativeGradient (localizedCoreFunction N ρ q u)+
          nativeGradient (localizedCoreFunction N ρ q v)) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (fun z => by
          rw [localizedCoreFunction_add,nativeGradient_add _ _
            (localizedCoreFunction_C2 N ρ hρ q u) (localizedCoreFunction_C2 N ρ hρ q v)]))
      _ = _ := MemLp.toLp_add hu hv
  map_smul' c u := by
    let hu := localizedCoreGradient_memLp N hK ρ hρ q u
    calc
      _ = (hu.const_smul c).toLp (c • nativeGradient (localizedCoreFunction N ρ q u)) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (fun z => by
          rw [localizedCoreFunction_smul,nativeGradient_smul]))
      _ = _ := MemLp.toLp_const_smul c hu

theorem localizedCoreGradient_norm_sq (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (u : EnergyCore N) : ‖localizedCoreGradient N hK ρ hρ q u‖^2 =
      ∫ z in K, chartEnergy (extendUpper (localizedCoreFunction N ρ q u)) (z.re,z.im) := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
    ← integral_re (L2.integrable_inner (localizedCoreGradient N hK ρ hρ q u)
      (localizedCoreGradient N hK ρ hρ q u))]
  apply integral_congr_ae
  filter_upwards [(localizedCoreGradient_memLp N hK ρ hρ q u).coeFn_toLp] with z hz
  simp only [hz,inner_self_eq_norm_sq_to_K,Complex.ofReal_re,nativeGradient_norm_sq]

def chartEnergyConstant (N : ℕ) [NeZero N] (K : Set UpperHalfPlane)
    (q : gamma0Classes N) (B D : ℝ) : ℝ := (chartOverlap N K q : ℝ)*(3*B^2+2*D)

theorem localizedCoreGradient_bound (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hρB : ∀ z ∈ K, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) (u : EnergyCore N) :
    ‖localizedCoreGradientLinear N hK ρ hρ q u‖ ≤
      Real.sqrt (chartEnergyConstant N K q B D)*‖u‖ := by
  have hmass := localizedChartH1Mass_energy_bound N hK u ρ hρ q B D hB hD hρB hρD
  have hf := localizedCoreFunction_C2 N ρ hρ q u
  have hi := (((native_C2_continuous _ hf).norm.pow 2).continuousOn.integrableOn_compact hK)
  have hg := (native_chartEnergy_continuous _ hf).continuousOn.integrableOn_compact hK
  have hC : 0 ≤ chartEnergyConstant N K q B D := by unfold chartEnergyConstant; positivity
  change ‖localizedCoreGradient N hK ρ hρ q u‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC,localizedCoreGradient_norm_sq]
  unfold localizedChartH1Mass at hmass
  rw [integral_add hi hg] at hmass
  have hn := integral_nonneg (μ := (volume : Measure UpperHalfPlane).restrict K)
    (fun z => sq_nonneg ‖localizedCoreFunction N ρ q u z‖)
  exact (le_add_of_nonneg_left hn).trans hmass

def completedLocalizedGradient (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N) :
    EnergyCompletion N →L[ℂ] CompactGradientL2 K :=
  (localizedCoreGradientLinear N hK ρ hρ q).extendOfNorm (coreEmbedding N).toLinearMap

theorem completedLocalizedGradient_core (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hρB : ∀ z ∈ K, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) (u : EnergyCore N) :
    completedLocalizedGradient N hK ρ hρ q (coreEmbedding N u) = localizedCoreGradient N hK ρ hρ q u := by
  apply LinearMap.extendOfNorm_eq (coreEmbedding_denseRange N)
    ⟨Real.sqrt (chartEnergyConstant N K q B D),?_⟩ u
  intro v
  rw [coreEmbedding_norm]
  exact localizedCoreGradient_bound N hK ρ hρ q B D hB hD hρB hρD v

theorem completedLocalizedGradient_norm_sq (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hρB : ∀ z ∈ K, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) (e : EnergyCompletion N) :
    ‖completedLocalizedGradient N hK ρ hρ q e‖^2 ≤ chartEnergyConstant N K q B D * ‖e‖^2 := by
  have hbound (u : EnergyCore N) : ‖localizedCoreGradientLinear N hK ρ hρ q u‖ ≤
      Real.sqrt (chartEnergyConstant N K q B D) * ‖coreEmbedding N u‖ := by
    rw [coreEmbedding_norm]
    exact localizedCoreGradient_bound N hK ρ hρ q B D hB hD hρB hρD u
  have h := LinearMap.norm_extendOfNorm_apply_le (f := localizedCoreGradientLinear N hK ρ hρ q)
    (e := (coreEmbedding N).toLinearMap) (coreEmbedding_denseRange N)
    (Real.sqrt (chartEnergyConstant N K q B D)) hbound e
  have hC : 0 ≤ chartEnergyConstant N K q B D := by unfold chartEnergyConstant; positivity
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow,Real.sq_sqrt hC] using hs

/-- The actual completed localized value and gradient belong to the
strong graph closure of the literal smooth localized derivatives. -/
theorem completed_localized_pair_mem_graph_closure (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (hc : Continuous ρ)
    (q : gamma0Classes N) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρB : ∀ z, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) (e : EnergyCompletion N) :
    (localizedCompletedValue N hK q ρ hc B hρB e, completedLocalizedGradient N hK ρ hρ q e) ∈
      closure (range (fun u : EnergyCore N =>
        (localizedCompletedValue N hK q ρ hc B hρB (coreEmbedding N u),
          localizedCoreGradient N hK ρ hρ q u))) := by
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_closure.preimage
      ((localizedCompletedValue N hK q ρ hc B hρB).continuous.prodMk
        (completedLocalizedGradient N hK ρ hρ q).continuous)
  · intro u
    rw [completedLocalizedGradient_core N hK ρ hρ q B D hB hD (fun z _ => hρB z) hρD]
    exact subset_closure ⟨u,rfl⟩

/-- Explicit mass and BOTH derivative-component budget on the actual
completed form. The vector norm is the sum of the two component squares. -/
theorem completed_localized_mass_gradient_budget (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (hc : Continuous ρ)
    (q : gamma0Classes N) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρB : ∀ z, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D) (e : EnergyCompletion N) :
    ‖localizedCompletedValue N hK q ρ hc B hρB e‖^2 +
      ‖completedLocalizedGradient N hK ρ hρ q e‖^2 ≤
      (chartOverlap N K q : ℝ)*(4*B^2+2*D)*‖e‖^2 := by
  have hm := localizedCompletedValue_norm_sq N hK q ρ hc B hB hρB e
  have hg := completedLocalizedGradient_norm_sq N hK ρ hρ q B D hB hD
    (fun z _ => hρB z) hρD e
  dsimp [chartEnergyConstant] at hg
  nlinarith

theorem actualForm_localized_mass_gradient_budget (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (hc : Continuous ρ)
    (q : gamma0Classes N) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρB : ∀ z, ‖ρ z‖ ≤ B)
    (hρD : ∀ z ∈ K, chartEnergy (extendUpper ρ) (z.re,z.im) ≤ D)
    (u : actualEnergyFormDomain N) :
    ‖localizedCompletedValue N hK q ρ hc B hρB (actualEnergyLift N u)‖^2 +
      ‖completedLocalizedGradient N hK ρ hρ q (actualEnergyLift N u)‖^2 ≤
      (chartOverlap N K q : ℝ)*(4*B^2+2*D)*(‖(u : QuotientL2 N)‖^2 +
        (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re) := by
  rw [actualEnergyLift_shifted_norm]
  exact completed_localized_mass_gradient_budget N hK ρ hρ hc q B D hB hD hρB hρD _

end
end ImbalancedChen.Part3.Gamma0CompletedLocalizedChartGradient20261026b
