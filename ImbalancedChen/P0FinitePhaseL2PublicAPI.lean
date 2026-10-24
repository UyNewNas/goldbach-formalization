import ImbalancedChen.Part3ActualPacketCommonPhaseFiniteL2
import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram

/-!
SOURCE_WRITTEN / UNCOMPILED / NOT ROOT_ACCEPTED. 2026-10-24.

Public finite-mode consumers of the actual common-phase finite L2 module.
Finite mode restriction concerns sums of nonnegative mode energies. It does
not assert monotonicity of the squared norm of a coherent mode combination.
The combination estimate below explicitly pays its coefficient L2 mass.
All original row/n interference is retained inside each kSlice.
The common-height bridge uses the actual FullGram modeRow_eq_actual theorem.
No height decay, majorant, Kuznetsov measure, or spectral saving is asserted.
-/

namespace ImbalancedChen.Part3.P0FinitePhaseL2PublicAPI
noncomputable section

open Classical MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3.ActualKPacketAdapterSourceOnly
  (withKKernel kModeFunction)
open ImbalancedChen.Part3.ActualPacketCommonPhaseL2_20261024u
  (mSlice k_phasePacket_parseval kModeFunction_sq_le_phaseL2)
open ImbalancedChen.Part3.ActualPacketPhysicalRegionL2_20261024w
  (kSlice k_mSlice_eq_literal_on_region kModeFunction_zero_off_region
   kModeFunction_continuous kModeFunction_sq_integrableOn_region
   kModeFunction_integrated_sq_le)
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
  (commonHeight modeRow modeRow_eq_actual)

variable {ι : Type*}

abbrev Mode := D4 → ℤ

/-- The nonnegative energy of an arbitrary finite collection of actual modes. -/
def finiteModeEnergy (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (S : Finset Mode) (q : ℝ) : ℝ :=
  ∑ k ∈ S, ‖kModeFunction P t k q‖^2

/-- Literal physical slices; each summand keeps its complete row/n sum. -/
def finiteSliceEnergy (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (S : Finset Mode) (q : ℝ) : ℝ :=
  ∑ k ∈ S, ∑ m ∈ P.mCarrier, ‖kSlice P t k q m‖^2

/-- A coherent finite mode combination, with its actual complex coefficients. -/
def finiteModeCombination (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (S : Finset Mode) (c : Mode → ℂ) (q : ℝ) : ℂ :=
  ∑ k ∈ S, c k * kModeFunction P t k q

theorem finiteModeEnergy_nonneg (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) (q : ℝ) :
    0 ≤ finiteModeEnergy P t S q := by
  exact Finset.sum_nonneg (fun k _hk => sq_nonneg _)

theorem finiteModeEnergy_mono (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) {S T : Finset Mode} (hST : S ⊆ T) (q : ℝ) :
    finiteModeEnergy P t S q ≤ finiteModeEnergy P t T q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun k _hk _hnot => sq_nonneg _)

theorem finiteModeEnergy_zero_off_region (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) (q : ℝ) (hq : q ∉ P.region) :
    finiteModeEnergy P t S q = 0 := by
  apply Finset.sum_eq_zero
  intro k _hk
  rw [kModeFunction_zero_off_region P t k q hq]
  simp

theorem finiteModeEnergy_integrableOn_region (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) :
    IntegrableOn (finiteModeEnergy P t S) P.region := by
  exact integrable_finsetSum S
    (fun k _hk => kModeFunction_sq_integrableOn_region P t k)

/-- Finite mode summation commutes with the exact physical integral. -/
theorem finiteModeEnergy_integral_eq (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) :
    (∫ q in P.region, finiteModeEnergy P t S q) =
      ∑ k ∈ S, ∫ q in P.region, ‖kModeFunction P t k q‖^2 := by
  exact integral_finsetSum S
    (fun k _hk => kModeFunction_sq_integrableOn_region P t k)

/-- Restricting the mode set can only reduce its integrated nonnegative energy. -/
theorem finiteModeEnergy_integral_mono (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) {S T : Finset Mode} (hST : S ⊆ T) :
    (∫ q in P.region, finiteModeEnergy P t S q) ≤
      ∫ q in P.region, finiteModeEnergy P t T q := by
  exact integral_mono (finiteModeEnergy_integrableOn_region P t S)
    (finiteModeEnergy_integrableOn_region P t T)
    (finiteModeEnergy_mono P t hST)

/-- Direct literal-slice consumer, on the original q region. -/
theorem finiteModeEnergy_le_slices (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) (q : ℝ) (hq : q ∈ P.region) :
    finiteModeEnergy P t S q ≤ (P.mCarrier.card : ℝ) * finiteSliceEnergy P t S q := by
  unfold finiteModeEnergy finiteSliceEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _hk
  have h := kModeFunction_sq_le_phaseL2 P t k q
  rw [k_phasePacket_parseval] at h
  have hs : (∑ m ∈ P.mCarrier, ‖mSlice (withKKernel P t) k q m‖^2) =
      ∑ m ∈ P.mCarrier, ‖kSlice P t k q m‖^2 := by
    apply Finset.sum_congr rfl
    intro m _hm
    rw [k_mSlice_eq_literal_on_region P t k q hq m]
  rwa [hs] at h

/-- Each mode uses the actual integrated finite L2 theorem. -/
theorem finiteModeEnergy_integrated_le_slices (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) :
    (∫ q in P.region, finiteModeEnergy P t S q) ≤
      (P.mCarrier.card : ℝ) *
        ∑ k ∈ S, ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
  rw [finiteModeEnergy_integral_eq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _hk => kModeFunction_integrated_sq_le P t k)

/-- Actual support identifies the full real-line and physical-region integrals. -/
theorem finiteModeEnergy_full_integral_eq (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) :
    (∫ q : ℝ, finiteModeEnergy P t S q) =
      ∫ q in P.region, finiteModeEnergy P t S q := by
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (finiteModeEnergy_zero_off_region P t S)

theorem finiteModeEnergy_full_integral_le_slices (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) :
    (∫ q : ℝ, finiteModeEnergy P t S q) ≤
      (P.mCarrier.card : ℝ) *
        ∑ k ∈ S, ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
  rw [finiteModeEnergy_full_integral_eq]
  exact finiteModeEnergy_integrated_le_slices P t S

/-- Finite Cauchy--Schwarz retains the explicit coefficient energy cost. -/
theorem finiteModeCombination_sq_le_energy (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) (c : Mode → ℂ) (q : ℝ) :
    ‖finiteModeCombination P t S c q‖^2 ≤
      (∑ k ∈ S, ‖c k‖^2) * finiteModeEnergy P t S q := by
  have ht : ‖finiteModeCombination P t S c q‖ ≤
      ∑ k ∈ S, ‖c k‖ * ‖kModeFunction P t k q‖ := by
    simpa only [finiteModeCombination, norm_mul] using
      norm_sum_le S (fun k => c k * kModeFunction P t k q)
  have hnonneg : 0 ≤ ∑ k ∈ S, ‖c k‖ * ‖kModeFunction P t k q‖ :=
    Finset.sum_nonneg (fun k _hk => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq : ‖finiteModeCombination P t S c q‖^2 ≤
      (∑ k ∈ S, ‖c k‖ * ‖kModeFunction P t k q‖)^2 := by
    simpa only [pow_two] using mul_le_mul ht ht (norm_nonneg _) hnonneg
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq S
    (fun k => ‖c k‖) (fun k => ‖kModeFunction P t k q‖))

theorem finiteModeCombination_sq_le_slices (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) (c : Mode → ℂ)
    (q : ℝ) (hq : q ∈ P.region) :
    ‖finiteModeCombination P t S c q‖^2 ≤
      (∑ k ∈ S, ‖c k‖^2) *
        ((P.mCarrier.card : ℝ) * finiteSliceEnergy P t S q) := by
  exact (finiteModeCombination_sq_le_energy P t S c q).trans
    (mul_le_mul_of_nonneg_left (finiteModeEnergy_le_slices P t S q hq)
      (Finset.sum_nonneg (fun k _hk => sq_nonneg _)))

theorem finiteModeCombination_continuous (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) (c : Mode → ℂ) :
    Continuous (finiteModeCombination P t S c) := by
  unfold finiteModeCombination
  exact continuous_finsetSum S
    (fun k _hk => continuous_const.mul (kModeFunction_continuous P t k))

/-- An actual integrated bound for a coherent finite mode combination. -/
theorem finiteModeCombination_integrated_sq_le_slices (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (S : Finset Mode) (c : Mode → ℂ) :
    (∫ q in P.region, ‖finiteModeCombination P t S c q‖^2) ≤
      (∑ k ∈ S, ‖c k‖^2) * ((P.mCarrier.card : ℝ) *
        ∑ k ∈ S, ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2) := by
  have hi : IntegrableOn
      (fun q => ‖finiteModeCombination P t S c q‖^2) P.region :=
    ((finiteModeCombination_continuous P t S c).norm.pow 2).integrableOn_Icc
  have hle := integral_mono hi
    ((finiteModeEnergy_integrableOn_region P t S).const_mul (∑ k ∈ S, ‖c k‖^2))
    (finiteModeCombination_sq_le_energy P t S c)
  rw [integral_const_mul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left
    (finiteModeEnergy_integrated_le_slices P t S)
    (Finset.sum_nonneg (fun k _hk => sq_nonneg _)))

/-- Connects the existing FullGram row object to the finite-phase public API. -/
theorem commonHeight_modeRows_energy_eq (P : PacketData ι)
    (S : Finset Mode) (q h : ℝ) :
    (∑ k ∈ S, ‖modeRow P k q h‖^2) =
      finiteModeEnergy P (commonHeight h) S q := by
  simp only [finiteModeEnergy, modeRow_eq_actual]

theorem commonHeight_modeRows_energy_le_slices (P : PacketData ι)
    (S : Finset Mode) (q h : ℝ) (hq : q ∈ P.region) :
    (∑ k ∈ S, ‖modeRow P k q h‖^2) ≤
      (P.mCarrier.card : ℝ) * finiteSliceEnergy P (commonHeight h) S q := by
  rw [commonHeight_modeRows_energy_eq]
  exact finiteModeEnergy_le_slices P (commonHeight h) S q hq

end
end ImbalancedChen.Part3.P0FinitePhaseL2PublicAPI
