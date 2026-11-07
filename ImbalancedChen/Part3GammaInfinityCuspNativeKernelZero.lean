import ImbalancedChen.Part3GammaInfinityCuspNativeRestriction
import ImbalancedChen.Part3GammaZeroAtomConstantClosure
import ImbalancedChen.Part3PositiveRectangleSmoothTensorDensity
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine ORIGINAL incomplete Eisenstein height profile has physical
quotient mean exactly one. It is y^2 times a normalized smooth positive-
height bump; actual Poincare/Fourier unfolding cancels the original y^-2
density. Hence the full infinity-cusp annihilator contains no nonzero
constant. Actual ambient native kernel rigidity then proves that the
new full infinity-cusp native restriction has zero kernel. Native full
infinity-cusp eigenvectors have zero physical mean for every real eigenvalue.
No restricted-domain density, resolvent reduction or completeness is used.
-/
namespace ImbalancedChen.Part3.GammaInfinityCuspNativeKernelZero20261026b

noncomputable section
open Set MeasureTheory
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a Gamma0ActualFriedrichsOperator20261025a
open ActualPoincareSpectralCoefficient20261026a
open ActualInfinityCuspAnnihilator20261026b
open SmoothZeroHeightSeedProfiles20261026b GammaSmoothZeroSeedNativeGraph20261026b
open GammaInfinityCuspNativeRestriction20261026b
open GammaConstantFormClosure20261026a GammaFriedrichsKernelConstantRigidity20261026a
open PositiveRectangleSmoothTensorDensity20261025a

def meanWitnessBump : ContDiffBump ((1 + 2 : ℝ) / 2) :=
  verticalBump 1 2 (by norm_num) (by norm_num)

def meanWitnessNormalizedBump : ℝ → ℝ := meanWitnessBump.normed (volume : Measure ℝ)

theorem meanWitnessNormalizedBump_positive_support :
    tsupport meanWitnessNormalizedBump ⊆ Ioi (0 : ℝ) := by
  rw [meanWitnessNormalizedBump, meanWitnessBump.tsupport_normed_eq,
    ← meanWitnessBump.tsupport_eq]
  exact verticalBump_positive_support 1 2 (by norm_num) (by norm_num)

/-- The original hyperbolic density is paid by y^2, not changed. -/
def meanWitnessHeightSeed : SmoothHeightSeed where
  toFun := fun y => (y : ℂ)^2 * (meanWitnessNormalizedBump y : ℂ)
  continuous := (Complex.continuous_ofReal.pow 2).mul
    (Complex.continuous_ofReal.comp meanWitnessBump.continuous_normed)
  compact := ((meanWitnessBump.hasCompactSupport_normed (μ := (volume : Measure ℝ))).comp_left
    (by simp)).mul_left
  positive := tsupport_mul_subset_right.trans
    ((tsupport_comp_subset rfl _).trans meanWitnessNormalizedBump_positive_support)
  cinfty := (Complex.ofRealCLM.contDiff.pow 2).mul
    (Complex.ofRealCLM.contDiff.comp meanWitnessBump.contDiff_normed)

theorem actualTestFourier_constant_one_zero (N : ℕ) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N (fun _ => (1 : ℂ)) 0 y = 1 := by
  rw [actualTestFourier_positive_height N _ 0 hy]
  simp

/-- Literal actual incomplete Eisenstein pairing with the physical
constant. The chosen original compact profile has no supplied mean field. -/
theorem meanWitness_zeroSeed_inner_constant_eq_one (N : ℕ) [NeZero N] :
    inner ℂ (zeroSeedL2 N meanWitnessHeightSeed.toHeightSeed) (constantL2 N) = 1 := by
  have hp := actual_poincare_L2_inner_eq_fourier N 0 meanWitnessHeightSeed.toFun
    meanWitnessHeightSeed.continuous meanWitnessHeightSeed.compact meanWitnessHeightSeed.positive
    (fun _ => (1 : ℂ)) continuous_const (constant_memLp_two N)
  rw [← constantL2_eq_toLp N] at hp
  change inner ℂ (zeroSeedL2 N meanWitnessHeightSeed.toHeightSeed) (constantL2 N) = _ at hp
  rw [hp]
  have heq : (fun y : ℝ => ((y⁻¹)^2 : ℝ) •
      (star (meanWitnessHeightSeed.toFun y) * actualTestFourier N (fun _ => (1 : ℂ)) 0 y)) =ᵐ[
        (volume : Measure ℝ).restrict (Ioi (0 : ℝ))]
      (fun y => (meanWitnessNormalizedBump y : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [actualTestFourier_constant_one_zero N hy]
    rw [Complex.real_smul]
    change (((y⁻¹)^2 : ℝ) : ℂ) *
      (star ((y : ℂ)^2 * (meanWitnessNormalizedBump y : ℂ)) * 1) =
        (meanWitnessNormalizedBump y : ℂ)
    have hc : (((y⁻¹)^2 : ℝ) : ℂ) * (y : ℂ)^2 = 1 := by
      have hr : (y⁻¹)^2 * y^2 = (1 : ℝ) := by
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hy), one_pow]
      exact_mod_cast hr
    simp only [Complex.star_def, map_mul, map_pow, Complex.conj_ofReal, mul_one]
    rw [← mul_assoc, hc, one_mul]
  rw [integral_congr_ae heq]
  have hzero : ∀ y : ℝ, y ∉ Ioi (0 : ℝ) → (meanWitnessNormalizedBump y : ℂ) = 0 := by
    intro y hy
    have hz : meanWitnessNormalizedBump y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (meanWitnessNormalizedBump_positive_support h))
    simp only [hz, Complex.ofReal_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_complex_ofReal]
  simpa only [meanWitnessNormalizedBump, Complex.ofReal_one] using
    congrArg Complex.ofReal (meanWitnessBump.integral_normed (μ := (volume : Measure ℝ)))

/-- Literal original quotient integral, with no volume renormalization. -/
theorem meanWitness_zeroSeed_physical_mean_eq_one (N : ℕ) [NeZero N] :
    (∫ q, zeroSeedL2 N meanWitnessHeightSeed.toHeightSeed q ∂carrierPushforward N) = 1 := by
  rw [← constantL2_inner]
  simpa only [inner_conj_symm, map_one] using
    congrArg star (meanWitness_zeroSeed_inner_constant_eq_one N)

theorem scalar_constant_mem_infinityCusp_iff_zero (N : ℕ) [NeZero N] (c : ℂ) :
    c • constantL2 N ∈ infinityCuspSubspace N ↔ c = 0 := by
  constructor
  · intro hc
    have ht := (mem_infinityCuspSubspace_iff N (c • constantL2 N)).mp hc meanWitnessHeightSeed.toHeightSeed
    simpa only [inner_smul_right, meanWitness_zeroSeed_inner_constant_eq_one, mul_one] using ht
  · intro hc
    rw [hc, zero_smul]
    exact Submodule.zero_mem _

theorem actual_infinityCusp_zero_native_graph_eq_zero (N : ℕ) [NeZero N]
    {f : QuotientL2 N} (hf : (f, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph)
    (hcusp : f ∈ infinityCuspSubspace N) : f = 0 := by
  obtain ⟨u, hu, hzero⟩ := LinearPMap.mem_graph_iff.mp hf
  obtain ⟨c, hc⟩ := native_friedrichs_kernel_eq_scalar_constant N u hzero
  have hfc : f = c • constantL2 N := hu.symm.trans hc
  rw [hfc] at hcusp
  have hz := (scalar_constant_mem_infinityCusp_iff_zero N c).mp hcusp
  rw [hfc, hz, zero_smul]

/-- The new actual full infinity-cusp native partial operator has no
nonzero native kernel vector. No dense-domain premise is needed. -/
theorem actualInfinityCuspNativeRestriction_eq_zero_of_apply_zero (N : ℕ) [NeZero N]
    (u : (actualInfinityCuspNativeRestriction N).domain)
    (hu : actualInfinityCuspNativeRestriction N u = 0) : u = 0 := by
  have hg := (actualInfinityCuspNativeRestriction_mem_graph_iff N
    (u : InfinityCuspL2 N) (actualInfinityCuspNativeRestriction N u)).mp
      ((actualInfinityCuspNativeRestriction N).mem_graph u)
  rw [hu] at hg
  have hz := actual_infinityCusp_zero_native_graph_eq_zero N hg (u : InfinityCuspL2 N).property
  apply Subtype.ext
  apply Subtype.ext
  exact hz

theorem actualInfinityCuspNativeRestriction_kernel_eq_bot (N : ℕ) [NeZero N] :
    (actualInfinityCuspNativeRestriction N).toFun.ker = ⊥ := by
  apply Submodule.eq_bot_iff.mpr
  intro u hu
  exact actualInfinityCuspNativeRestriction_eq_zero_of_apply_zero N u (LinearMap.mem_ker.mp hu)

/-- A nonzero native eigenvalue is physically orthogonal to constants
by the actual native constant graph and native cross symmetry. -/
theorem actual_native_nonzero_eigen_physical_mean_zero (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (λ : ℝ) (hλ : λ ≠ 0)
    (hf : (f, (λ : ℂ) • f) ∈ (actualGammaFriedrichs N).graph) :
    (∫ q, f q ∂carrierPushforward N) = 0 := by
  have hi := actual_native_graph_cross_symmetry N hf (constantL2_mem_friedrichsGraph_zero N)
  simp only [inner_smul_right, inner_zero_left] at hi
  rw [← constantL2_inner]
  exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast hλ)

/-- Every real native eigenvalue is admitted, with the zero-eigenvalue
case excluded by the genuine nonzero-mean original zeroSeed witness. -/
theorem actual_full_infinityCusp_eigen_physical_mean_zero (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (λ : ℝ) (hcusp : f ∈ infinityCuspSubspace N)
    (hf : (f, (λ : ℂ) • f) ∈ (actualGammaFriedrichs N).graph) :
    (∫ q, f q ∂carrierPushforward N) = 0 := by
  by_cases hλ : λ = 0
  · have hzero : f = 0 := actual_infinityCusp_zero_native_graph_eq_zero N
      (by simpa only [hλ, Complex.ofReal_zero, zero_smul] using hf) hcusp
    rw [← constantL2_inner, hzero, inner_zero_right]
  · exact actual_native_nonzero_eigen_physical_mean_zero N f λ hλ hf

end
end ImbalancedChen.Part3.GammaInfinityCuspNativeKernelZero20261026b
