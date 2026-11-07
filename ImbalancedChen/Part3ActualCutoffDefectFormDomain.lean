import ImbalancedChen.Part3CompactH1PoincareFormDomain
import ImbalancedChen.Part3GammaActualCompactWeakSeedH1
import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL actual modular cutoff times an actual native adjoint defect
belongs to the EXISTING quotient closed-form domain. Compact normalized
seed reconstruction, actual H1 regularity, constructive finite-tensor
energy completion and literal physical Poincare identification are all
invoked. No adjoint form membership, H1, cutoff-domain or weak-PDE premise
occurs. No spectral/completeness conclusion is asserted.
-/
namespace ImbalancedChen.Part3.ActualCutoffDefectFormDomain20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz ActualGamma0MaassDescent20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open GammaCompactWeakSeedPoincareL220261026b
open GammaActualCutoffWeakSeedReconstruction20261026b GammaActualCompactWeakSeedH120261026b
open CompactH1PoincareFormDomain20261026b CompactH1CanonicalSeedL220261026b
open Gamma0WholeChartCoordinateWeakEquation20261026b
open ActualModularSmoothCutoffL2Tail20261025a

theorem actual_cutoff_defect_has_energy_vector (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ e : EnergyCompletion N,
      ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        fun q => (quotientCutoff N Y q : ℂ) * f q := by
  obtain ⟨σ,hc,hsm,hseed,hproduct⟩ := actual_cutoff_product_has_compact_weak_seed N Y hY f
  obtain ⟨L,R,a,b,J,ha,hLR,hab,hval,hx,hy,hsv,hsx,hsy⟩ :=
    actual_defect_compact_coefficient_H1 N f hf σ hc hsm
  obtain ⟨e,he⟩ := compactH1_periodization_has_energy_vector N J hx hy L R a b ha hLR hab hsv
  have hupper : upperSeed J.value = compactCoefficientSeed N σ f := by
    funext z
    rw [hval]
    exact extendUpper_pair (compactCoefficientSeed N σ f) z
  rw [hupper] at he
  have hrep := weakSeedL2_ae N (compactCoefficientSeed N σ f) hseed (tsupport σ) hc
    ((compactCoefficientSeed_support N σ f).trans subset_closure)
  exact ⟨e,he.trans (hrep.symm.trans hproduct)⟩

/-- A typed member of the EXISTING actualEnergyFormDomain realizes the
literal original cutoff product. The only analytic premise is native
minimalShiftDefect membership of f. -/
theorem actual_cutoff_defect_form_vector (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ u : actualEnergyFormDomain N,
      ((u : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        fun q => (quotientCutoff N Y q : ℂ) * f q := by
  obtain ⟨e,he⟩ := actual_cutoff_defect_has_energy_vector N f hf Y hY
  exact ⟨⟨physicalProjection N e,⟨e,rfl⟩⟩,he⟩

/-- Representation-independent actual form membership, with only the
literal AE cutoff-product identification supplied for the physical vector. -/
theorem actual_cutoff_defect_mem_form_domain (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 ≤ Y)
    (u : QuotientL2 N)
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      fun q => (quotientCutoff N Y q : ℂ) * f q) :
    u ∈ actualEnergyFormDomain N := by
  obtain ⟨e,he⟩ := actual_cutoff_defect_has_energy_vector N f hf Y hY
  exact ⟨e,Lp.ext (he.trans hu.symm)⟩

end
end ImbalancedChen.Part3.ActualCutoffDefectFormDomain20261026b
