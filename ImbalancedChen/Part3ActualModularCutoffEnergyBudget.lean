import ImbalancedChen.Part3ActualModularCutoffGradient

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL native gradient density of the constructed global smooth
cutoff descends to the actual Gamma0 quotient. Its canonical quotient
integral is <= C_chi * index(Gamma0(N))/Y. The derivative estimate is
produced by the previous true local-germ/covariance theorem, and the
index factor by actual finite-cover measure transport. There is no
postulated energy density, cutoff energy, or form-core membership.
-/

namespace ImbalancedChen.Part3.ActualModularCutoffEnergyBudget20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane ENNReal
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a Gamma0ModularFiniteCoverMeasure20261025a
open Gamma0ActualHighCuspTail20261025a Gamma0ActualParabolicUnfolding20261025a
open ActualCuspStripCutoff20261025a ActualModularCutoffGradient20261025a

/-- Genuine quotient lift of the actual slice-gradient density, not a
chosen representative energy supplied independently of the cutoff. -/
def quotientModularEnergy (Y : ℝ) (hY : 0 < Y) : Gamma0OrbitSpace 1 → ℝ :=
  Quotient.lift (cutoffEnergyH Y) (by
    intro z w hzw
    obtain ⟨g, rfl⟩ := (MulAction.orbitRel_apply).mp hzw
    exact cutoffEnergyH_sl2_invariant Y hY (g : SL(2, ℤ)) w)

@[simp] theorem quotientModularEnergy_projection (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) :
    quotientModularEnergy Y hY (orbitProjection 1 z) = cutoffEnergyH Y z := rfl

theorem quotientModularEnergy_measurable (Y : ℝ) (hY : 0 < Y) :
    Measurable (quotientModularEnergy Y hY) :=
  measurable_from_quotient.mpr (cutoffEnergyH_continuous Y hY).measurable

theorem quotientModularEnergy_bound_ae (Y : ℝ) (hY : 1 < Y) :
    ∀ᵐ q ∂carrierPushforward 1,
      ENNReal.ofReal (quotientModularEnergy Y (lt_trans (by norm_num) hY) q) ≤
        ENNReal.ofReal cutoffEnergyConstant * quotientHighIndicator 1 Y q := by
  filter_upwards [reducedProjection_range_ae 1] with q hq
  obtain ⟨z, rfl⟩ := hq
  change ENNReal.ofReal (cutoffEnergyH Y (z : UpperHalfPlane)) ≤ _
  rw [quotientHighIndicator, parabolicNonnegativePoincare_projection]
  exact cutoffEnergyH_le_high_trace Y hY z

theorem lintegral_quotientModularEnergy_le (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, ENNReal.ofReal (quotientModularEnergy Y (lt_trans (by norm_num) hY) q)
      ∂carrierPushforward 1) ≤
      ENNReal.ofReal cutoffEnergyConstant * ENNReal.ofReal (1 / Y) := by
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal cutoffEnergyConstant * quotientHighIndicator 1 Y q
        ∂carrierPushforward 1 := lintegral_mono_ae (quotientModularEnergy_bound_ae Y hY)
    _ = ENNReal.ofReal cutoffEnergyConstant * ENNReal.ofReal (1 / Y) := by
      rw [lintegral_const_mul _ (quotientHighIndicator_measurable 1 Y),
        quotientHighIndicator_eq_indicator 1 Y hY,
        lintegral_indicator (quotientHighTail_measurable 1 Y)]
      simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
      rw [quotientHighTail_volume 1 Y hY]

/-- The derivative density on the original level-N quotient. Its actual
projection formula below identifies it with the native global gradient. -/
def quotientCutoffEnergy (N : ℕ) (Y : ℝ) (hY : 0 < Y) : Gamma0OrbitSpace N → ℝ :=
  quotientModularEnergy Y hY ∘ forgetLevel N

@[simp] theorem quotientCutoffEnergy_projection (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) :
    quotientCutoffEnergy N Y hY (orbitProjection N z) = cutoffEnergyH Y z := rfl

theorem quotientCutoffEnergy_nonneg (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (q : Gamma0OrbitSpace N) : 0 ≤ quotientCutoffEnergy N Y hY q := by
  refine Quotient.inductionOn q (fun z => ?_)
  exact cutoffEnergyH_nonneg Y z

/-- Actual TOTAL hyperbolic Dirichlet energy budget for the constructed
full-modular cutoff on Gamma0(N), with a level/height independent bump
constant and the actual index. No hEnergy assumption occurs. -/
theorem quotientCutoff_Dirichlet_energy_le (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, ENNReal.ofReal (quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q)
      ∂carrierPushforward N) ≤
      ENNReal.ofReal cutoffEnergyConstant *
        ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) := by
  let F := fun q => ENNReal.ofReal (quotientModularEnergy Y (lt_trans (by norm_num) hY) q)
  have hF : Measurable F :=
    (quotientModularEnergy_measurable Y (lt_trans (by norm_num) hY)).ennreal_ofReal
  change (∫⁻ q, F (forgetLevel N q) ∂carrierPushforward N) ≤ _
  rw [← lintegral_map hF (forgetLevel_measurable N), forgetLevel_map_carrier,
    lintegral_smul_measure]
  calc
    _ ≤ ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) *
        (ENNReal.ofReal cutoffEnergyConstant * ENNReal.ofReal (1 / Y)) :=
      mul_le_mul_left' (lintegral_quotientModularEnergy_le Y hY) _
    _ = _ := by ac_rfl

end
end ImbalancedChen.Part3.ActualModularCutoffEnergyBudget20261025a
