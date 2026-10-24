import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Data.Complex.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit. 2026-10-24.
Public compact-height energy operations on the actual modeRow. Integration
is exactly unweighted Lebesgue dt on Icc (-T) T. Finite-mode aggregation
means a sum of the actual mode energies, retaining every labelled Gram
pair within each mode. No spectral interpretation or decay is asserted.
-/

namespace ImbalancedChen.Part3.P0CommonHeightEnergyPublicAPISourceOnly
noncomputable section

open Classical Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualCommonHeightKGramSourceOnly

variable {ι : Type*}

/-- A nonpositive radius has zero Lebesgue energy, including radius zero. -/
theorem compactHeightEnergy_eq_zero_of_nonpos (P : PacketData ι)
    (k : D4 → ℤ) (q : ℝ) {T : ℝ} (hT : T ≤ 0) :
    compactHeightEnergy P k q T = 0 := by
  by_cases hzero : T = 0
  · subst T
    simp [compactHeightEnergy]
  · have hneg : T < 0 := lt_of_le_of_ne hT hzero
    have hempty : Icc (-T) T = ∅ := Icc_eq_empty_of_lt (by linarith)
    simp [compactHeightEnergy, hempty]

theorem compactHeightEnergy_zero (P : PacketData ι)
    (k : D4 → ℤ) (q : ℝ) : compactHeightEnergy P k q 0 = 0 := by
  exact compactHeightEnergy_eq_zero_of_nonpos P k q le_rfl

/-- Interval inclusion and actual integrability give radius monotonicity.
There is no assumption that a spectral quadratic form is positive. -/
theorem compactHeightEnergy_mono (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    compactHeightEnergy P k q T₁ ≤ compactHeightEnergy P k q T₂ := by
  have hsub : Icc (-T₁) T₁ ⊆ Icc (-T₂) T₂ := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2.trans hT⟩
  exact setIntegral_mono_set (compactHeightEnergy_integrable P k hq T₂)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hsub)

theorem compactHeightEnergy_monotone (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) : Monotone (compactHeightEnergy P k q) := by
  intro T₁ T₂ hT
  exact compactHeightEnergy_mono P k hq hT

/-- The physical region itself supplies positive q. -/
theorem region_compactHeightEnergy_mono (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : q ∈ P.region) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    compactHeightEnergy P k q T₁ ≤ compactHeightEnergy P k q T₂ := by
  have hqpos : 0 < q := by
    have hlow : P.Y0/16 ≤ q := hq.1
    linarith [P.Y0_pos]
  exact compactHeightEnergy_mono P k hqpos hT

/-- Sum of the actual energies over a specified finite collection of modes. -/
def finiteModeEnergy (P : PacketData ι) (modes : Finset (D4 → ℤ))
    (q T : ℝ) : ℝ :=
  ∑ k ∈ modes, compactHeightEnergy P k q T

theorem finiteModeEnergy_nonneg (P : PacketData ι)
    (modes : Finset (D4 → ℤ)) (q T : ℝ) :
    0 ≤ finiteModeEnergy P modes q T := by
  exact Finset.sum_nonneg (fun k _hk => compactHeightEnergy_nonneg P k q T)

theorem finiteModeEnergy_eq_zero_of_nonpos (P : PacketData ι)
    (modes : Finset (D4 → ℤ)) (q : ℝ) {T : ℝ} (hT : T ≤ 0) :
    finiteModeEnergy P modes q T = 0 := by
  apply Finset.sum_eq_zero
  intro k _hk
  exact compactHeightEnergy_eq_zero_of_nonpos P k q hT

theorem finiteModeEnergy_empty (P : PacketData ι) (q T : ℝ) :
    finiteModeEnergy P ∅ q T = 0 := by
  simp [finiteModeEnergy]

theorem finiteModeEnergy_singleton (P : PacketData ι) (k : D4 → ℤ) (q T : ℝ) :
    finiteModeEnergy P {k} q T = compactHeightEnergy P k q T := by
  simp [finiteModeEnergy]

/-- Integrability of the finite sum is derived mode by mode. -/
theorem finiteModeEnergy_integrand_integrable (P : PacketData ι)
    (modes : Finset (D4 → ℤ)) {q : ℝ} (hq : 0 < q) (T : ℝ) :
    IntegrableOn (fun t : ℝ => ∑ k ∈ modes, ‖modeRow P k q t‖^2)
      (Icc (-T) T) := by
  exact integrable_finsetSum modes
    (fun k _hk => compactHeightEnergy_integrable P k hq T)

/-- Exact finite-to-integral interchange for the aggregate energy. -/
theorem finiteModeEnergy_eq_integral (P : PacketData ι)
    (modes : Finset (D4 → ℤ)) {q : ℝ} (hq : 0 < q) (T : ℝ) :
    finiteModeEnergy P modes q T =
      ∫ t in Icc (-T) T, ∑ k ∈ modes, ‖modeRow P k q t‖^2 := by
  exact (integral_finsetSum modes
    (fun k _hk => compactHeightEnergy_integrable P k hq T)).symm

theorem finiteModeEnergy_mono_radius (P : PacketData ι)
    (modes : Finset (D4 → ℤ)) {q : ℝ} (hq : 0 < q)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    finiteModeEnergy P modes q T₁ ≤ finiteModeEnergy P modes q T₂ := by
  exact Finset.sum_le_sum (fun k _hk => compactHeightEnergy_mono P k hq hT)

/-- Enlarging the finite mode set only adds actual nonnegative energies. -/
theorem finiteModeEnergy_mono_modes (P : PacketData ι)
    {modes₁ modes₂ : Finset (D4 → ℤ)} (hsub : modes₁ ⊆ modes₂)
    (q T : ℝ) :
    finiteModeEnergy P modes₁ q T ≤ finiteModeEnergy P modes₂ q T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _hk _hnot => compactHeightEnergy_nonneg P k q T)

/-- Every original labelled off-diagonal Gram pair survives aggregation. -/
theorem finiteModeEnergy_full_gram (P : PacketData ι)
    (modes : Finset (D4 → ℤ)) {q : ℝ} (hq : 0 < q) (T : ℝ) :
    (finiteModeEnergy P modes q T : ℂ) =
      ∑ k ∈ modes, ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
        ∫ t in Icc (-T) T,
          modeAtom P k q a t * star (modeAtom P k q b t) := by
  unfold finiteModeEnergy
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  exact actual_compact_height_full_gram P k hq T

/-- Physical-region entry point: no separate positive-q or integrability
premise is required to use the aggregate integral and full Gram identities. -/
theorem region_finiteModeEnergy_public (P : PacketData ι)
    (modes : Finset (D4 → ℤ)) {q : ℝ} (hq : q ∈ P.region) (T : ℝ) :
    IntegrableOn (fun t : ℝ => ∑ k ∈ modes, ‖modeRow P k q t‖^2)
        (Icc (-T) T) ∧
      0 ≤ finiteModeEnergy P modes q T ∧
      finiteModeEnergy P modes q T =
        ∫ t in Icc (-T) T, ∑ k ∈ modes, ‖modeRow P k q t‖^2 := by
  have hqpos : 0 < q := by
    have hlow : P.Y0/16 ≤ q := hq.1
    linarith [P.Y0_pos]
  exact ⟨finiteModeEnergy_integrand_integrable P modes hqpos T,
    finiteModeEnergy_nonneg P modes q T,
    finiteModeEnergy_eq_integral P modes hqpos T⟩

end
end ImbalancedChen.Part3.P0CommonHeightEnergyPublicAPISourceOnly
