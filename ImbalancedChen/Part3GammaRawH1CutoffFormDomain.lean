import ImbalancedChen.Part3CoherentUpperChartH1CompactProduct
import ImbalancedChen.Part3CompactH1PoincareFormDomain
import ImbalancedChen.Part3GammaActualCompactWeakSeedH1

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Any actual quotient L2 vector with raw whole-chart H1_loc, regardless of
whether it has a native operator output or finite global energy, becomes
an EXISTING form-domain vector after the actual modular cutoff. Compact
coefficient normalization, literal weak product, genuine H1 tensor
approximation and actual Poincare reconstruction supply the result.
No form membership or differential equation is a premise.
-/

namespace ImbalancedChen.Part3.GammaRawH1CutoffFormDomain20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz ActualGamma0MaassDescent20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0CompactDefectMollifier20261026a
open CompactSeedSmoothPlaneExtension20261025a WholeUpperChartWeakH1Patching20261026b
open GammaActualCompactWeakSeedH120261026b GammaActualCutoffWeakSeedReconstruction20261026b
open CoherentUpperChartH1CompactProduct20261026b CompactH1PoincareFormDomain20261026b
open CompactH1CanonicalSeedL220261026b LocalH1Tests20261026b
open GammaCompactWeakSeedPoincareL220261026b ActualModularSmoothCutoffL2Tail20261025a

/-- A general raw local-H1 quotient vector, without adjoint or defect
membership, produces an actual compact H1 coefficient seed. -/
theorem raw_H1_compact_coefficient_jet (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hF : HasUpperChartWeakH1 (ActualPullbackLocalH1Transfer20261026b.actualPlanePullback N f))
    (σ : UpperHalfPlane → ℂ) (hc : HasCompactSupport σ)
    (hsm : ContDiffOn ℝ ∞ (extendUpper σ) positiveChart) :
    ∃ (L R a b : ℝ) (J : CompactH1Jet),
      0 < a ∧ L < R ∧ a < b ∧ J.value = extendUpper (compactCoefficientSeed N σ f) ∧
      HasCompactSupport J.dx ∧ HasCompactSupport J.dy ∧
      tsupport J.value ⊆ openRect L R a b ∧
      tsupport J.dx ⊆ openRect L R a b ∧ tsupport J.dy ⊆ openRect L R a b := by
  obtain ⟨Gx,Gy,hb,hw⟩ := hF
  obtain ⟨hχ,hχc,hχpos⟩ := extendUpper_compact_cinfty_positive σ hc hsm
  obtain ⟨J,hval,hdx,hdy,hsv,hsx,hsy⟩ := exists_coherent_compact_H1_product
    _ Gx Gy hb hw hχ hχc hχpos
  obtain ⟨n,hn⟩ := compact_subset_chartRectangle hχc hχpos
  let L : ℝ := -((n : ℝ)+1)
  let R : ℝ := (n : ℝ)+1
  let a : ℝ := mollifierRadius (n+1)
  let b : ℝ := (n : ℝ)+1
  have ha : 0 < a := mollifierRadius_pos _
  have hLR : L < R := by
    dsimp [L,R]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hab : a < b := by
    have hhalf : mollifierRadius (n+1) ≤ (1/2 : ℝ) := by
      unfold mollifierRadius
      apply one_div_le_one_div_of_le (by norm_num)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
    dsimp [a,b]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨L,R,a,b,J,ha,hLR,hab,?_,
    hχc.of_isClosed_subset isClosed_tsupport hsx,
    hχc.of_isClosed_subset isClosed_tsupport hsy,hsv.trans hn,hsx.trans hn,hsy.trans hn⟩
  rw [coefficientSeed_zero_extension]
  exact hval

/-- Actual cutoff form membership is proved from local weak Sobolev
data alone. The represented cutoff product is the original quotient one. -/
theorem raw_H1_cutoff_has_energy_vector (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hF : HasUpperChartWeakH1 (ActualPullbackLocalH1Transfer20261026b.actualPlanePullback N f))
    (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ e : EnergyCompletion N,
      ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        fun q => (quotientCutoff N Y q : ℂ)*f q := by
  obtain ⟨σ,hc,hsm,hseed,hproduct⟩ := actual_cutoff_product_has_compact_weak_seed N Y hY f
  obtain ⟨L,R,a,b,J,ha,hLR,hab,hval,hx,hy,hsv,hsx,hsy⟩ :=
    raw_H1_compact_coefficient_jet N f hF σ hc hsm
  obtain ⟨e,he⟩ := compactH1_periodization_has_energy_vector N J hx hy L R a b ha hLR hab hsv
  have hupper : upperSeed J.value = compactCoefficientSeed N σ f := by
    funext z
    rw [hval]
    exact extendUpper_pair (compactCoefficientSeed N σ f) z
  rw [hupper] at he
  have hrep := weakSeedL2_ae N (compactCoefficientSeed N σ f) hseed (tsupport σ) hc
    ((compactCoefficientSeed_support N σ f).trans subset_closure)
  exact ⟨e,he.trans (hrep.symm.trans hproduct)⟩

theorem raw_H1_cutoff_mem_form_domain (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hF : HasUpperChartWeakH1 (ActualPullbackLocalH1Transfer20261026b.actualPlanePullback N f))
    (Y : ℝ) (hY : 1 ≤ Y) (u : QuotientL2 N)
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      fun q => (quotientCutoff N Y q : ℂ)*f q) : u ∈ actualEnergyFormDomain N := by
  obtain ⟨e,he⟩ := raw_H1_cutoff_has_energy_vector N f hF Y hY
  exact ⟨e,Lp.ext (he.trans hu.symm)⟩

end
end ImbalancedChen.Part3.GammaRawH1CutoffFormDomain20261026b
