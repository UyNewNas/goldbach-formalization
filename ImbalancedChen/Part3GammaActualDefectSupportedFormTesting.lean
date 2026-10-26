import ImbalancedChen.Part3GammaCompactSeedOuterCutoffTesting
import ImbalancedChen.Part3ActualCutoffDefectFormDomain
import ImbalancedChen.Part3ActualCutoffSquareSupportedEnergy
import ImbalancedChen.Part3Gamma0PhysicalClosedDirichletForm
import ImbalancedChen.Part3GammaCompactSeedCutoffPlateau

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The native defect equation is extended to the ACTUAL cutoff-square form
test. Its finite tensor approximation is constructed with one common
compact SOURCE, an outer cutoff plateau is chosen only after that source,
and every native graph pairing is replaced exactly by a pairing against
the outer cutoff form vector. Genuine energy convergence then permits
the nonsmooth test. This is not an assumed weak IMS/Green/legal-test join.
-/

namespace ImbalancedChen.Part3.GammaActualDefectSupportedFormTesting20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane Topology
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a GammaActualQuotientCutoffMultiplier20261026b
open GammaSmoothMultiplierLegalTests20261026a GammaCompactSeedOuterCutoffTesting20261026b
open ActualCutoffDefectFormDomain20261026b ActualCutoffSquareSupportedEnergy20261026b
open GammaCompactSeedCutoffPlateau20261026a ActualModularSmoothCuspCutoff20261025a
open ActualModularSmoothCutoffL2Tail20261025a LocalH1TensorDifferenceABI20261026b

theorem actual_cutoff_product_literal_ae (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    (actualQuotientCutoffMultiplier N Y hY f : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N] fun q => (quotientCutoff N Y q : ℂ) * f q := by
  simpa only [actualCutoff_quotientMultiplier, Pi.mul_apply] using
    actualQuotientCutoffMultiplier_coe_ae N Y hY f

def actualDefectCutoffFormPoint (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 < Y) : actualEnergyFormDomain N :=
  ⟨actualQuotientCutoffMultiplier N Y hY f,
    actual_cutoff_defect_mem_form_domain N f hf Y hY.le _
      (actual_cutoff_product_literal_ae N Y hY f)⟩

def actualDefectCutoffEnergyLift (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 < Y) : EnergyCompletion N :=
  actualEnergyLift N (actualDefectCutoffFormPoint N f hf Y hY)

theorem actualDefectCutoffEnergyLift_projection (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 < Y) :
    physicalProjection N (actualDefectCutoffEnergyLift N f hf Y hY) =
      actualQuotientCutoffMultiplier N Y hY f :=
  actualEnergyLift_projection N _

/-- Native finite tests, now against the honest outer-cutoff energy
vector. The source plateau pays BOTH original differential coordinates. -/
theorem actual_defect_outer_energy_finite_test (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (s : SmoothSeed)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsK : Gamma0CompactTensorPoincareLocalFinite20261025a.finiteCompactTensorSupportK
      Finset.univ (seedTensors s) ⊆ K)
    (Z : ℝ) (hZ : 1 < Z) (hplateau : ∀ z ∈ K, globalCutoff Z z = 1) :
    inner ℂ (actualDefectCutoffEnergyLift N f hf Z hZ)
      (coreEmbedding N (seedCoreElement N s : EnergyCore N)) = 0 := by
  rw [physicalProjection_testing, actualDefectCutoffEnergyLift_projection]
  change inner ℂ (actualQuotientCutoffMultiplier N Z hZ f)
    (seedVector N s + actualCoreLaplacian N (seedCoreElement N s)) = 0
  rw [actualCoreLaplacian_seed]
  have h := actual_defect_finite_seed_outer_cutoff_test N f hf s hK hsK Z hZ hplateau
  have hstar := congrArg star h
  simpa only [inner_conj_symm, star_zero] using hstar

/-- Constructed cutoff-square form test and one outer scale threshold.
For EVERY later outer cutoff the true shifted form pairing is zero and
the outer cutoff nests the original inner cutoff exactly. -/
theorem actual_defect_cutoff_square_form_testing (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ (e : EnergyCompletion N) (Z₀ : ℝ), 1 < Z₀ ∧
      (((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ)
        =ᵐ[carrierPushforward N] fun q => (quotientCutoff N Y q : ℂ)^2 * f q) ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∃ hZ : 1 < Z,
        inner ℂ (actualDefectCutoffEnergyLift N f hf Z hZ) e = 0 ∧
        (∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z) := by
  obtain ⟨L,R,a,b,J,P,K,e,ha,hLR,hab,hK,hPs,hSources,he,hphysical,hcover⟩ :=
    actual_cutoff_square_supported_energy_approximation N f hf Y hY
  obtain ⟨Z₁,hZ₁,hplateau⟩ := exists_uniform_compact_orbit_plateau hK
  let Z₀ : ℝ := max Z₁ 2
  have hZ₀ : 1 < Z₀ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨e,Z₀,hZ₀,hphysical,fun Z hZZ => ?_⟩
  have hZ : 1 < Z := hZ₀.trans_le hZZ
  have hZ₁Z : Z₁ ≤ Z := (le_max_left _ _).trans hZZ
  have hone : ∀ z ∈ K, globalCutoff Z z = 1 := by
    intro z hz
    have h := (hplateau Z hZ₁Z z hz (1 : SL(2,ℤ))).self_of_nhds
    simpa only [one_smul] using h
  have htest (k : ℕ) : inner ℂ (actualDefectCutoffEnergyLift N f hf Z hZ)
      (coreEmbedding N (familyEnergyCore N (P.tensors k))) = 0 := by
    exact actual_defect_outer_energy_finite_test N f hf (P.seed k) hK (hPs k) Z hZ hone
  have hlim : Tendsto (fun k => inner ℂ (actualDefectCutoffEnergyLift N f hf Z hZ)
      (coreEmbedding N (familyEnergyCore N (P.tensors k)))) atTop
      (𝓝 (inner ℂ (actualDefectCutoffEnergyLift N f hf Z hZ) e)) :=
    tendsto_const_nhds.inner he
  have hzero : Tendsto (fun k => inner ℂ (actualDefectCutoffEnergyLift N f hf Z hZ)
      (coreEmbedding N (familyEnergyCore N (P.tensors k)))) atTop (𝓝 (0 : ℂ)) := by
    simpa only [htest] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  refine ⟨hZ,tendsto_nhds_unique hlim hzero,fun z => ?_⟩
  by_cases hz : globalCutoff Y z = 0
  · simp [hz]
  · obtain ⟨q,hq⟩ := hcover z hz
    have h := hone _ hq
    rw [effectiveMatrixAction, globalCutoff_sl2_invariant] at h
    rw [h,one_mul]

end
end ImbalancedChen.Part3.GammaActualDefectSupportedFormTesting20261026b
