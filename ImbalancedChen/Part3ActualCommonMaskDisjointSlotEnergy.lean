import ImbalancedChen.Part3ActualCommonMaskLongslotEnergy
import ImbalancedChen.Part3ActualFullPacketFourierTailL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.

The raw-height full packet energy, and separately the genuine Fourier-mode
remainder energy, pay for every finite disjoint family of measurable height
slots simultaneously. The same restricted PacketData occurs in every slot:
one m interval, original signed/coprime n fibres, original physical q kernel.
The Fourier tail is a tail in four-dimensional reconstruction frequency, not
a claimed decay rate as |t| tends to infinity.
-/

namespace ImbalancedChen.Part3.ActualCommonMaskDisjointSlotEnergySourceOnly
noncomputable section

open Classical Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualKPacketAdapterSourceOnly
open ActualKTransformFourier20261024z
open ActualKFullHeightEnergy20261024z
open ActualKHeightFourierTail20261024z
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.ActualCommonMaskLongslotEnergySourceOnly
open ImbalancedChen.Part3.ActualFullPacketFourierBridgeSourceOnly
open ImbalancedChen.Part3.ActualFullPacketRawHeightEnergySourceOnly
open ImbalancedChen.Part3.ActualFullPacketFourierTailL2SourceOnly

variable {ι κ : Type*}

/-- Only measure additivity and nonnegativity are used in this local lemma. -/
private theorem disjoint_slot_sum_le_total (f : ℝ → ℝ)
    (hf : Integrable f) (hf0 : ∀ t, 0 ≤ f t)
    (F : Finset κ) (S : κ → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisj : Set.Pairwise (↑F) (Disjoint on S)) :
    (∑ i ∈ F, ∫ t in S i, f t) ≤ ∫ t : ℝ, f t := by
  rw [← integral_biUnion_finset F hS hdisj
    (fun i _hi => hf.integrableOn)]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall hf0)

/-- Energy over disjoint slots is paid once by the exact whole-height
Fourier profile of the *restricted physical packet*. No slot may choose a
separate m interval or row family. -/
theorem maskedPhysicalHeight_disjoint_slot_sum_le (P : PacketData ι)
    (a b : ℕ) (F : Finset κ) (S : κ → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisj : Set.Pairwise (↑F) (Disjoint on S)) :
    (∑ i ∈ F, ∫ t in S i, ‖maskedPhysicalHeight P a b t‖ ^ 2) ≤
      (Real.pi/4) *
        ∫ u : ℝ, ‖physicalEvenProfile (restrictM P a b) u‖ ^ 2 := by
  have h := disjoint_slot_sum_le_total
    (fun t : ℝ => ‖maskedPhysicalHeight P a b t‖ ^ 2)
    (maskedPhysicalHeight_norm_sq_integrable P a b)
    (fun t => sq_nonneg _) F S hS hdisj
  exact h.trans_eq (by
    simpa only [maskedPhysicalHeight_eq_full] using
      fullPhysicalHeight_energy (restrictM P a b))

/-- Count any selected disjoint slots whose entire physical packet energy
is at least eta. This is a finite large-values statement for actual data. -/
theorem maskedPhysicalHeight_large_slot_count (P : PacketData ι)
    (a b : ℕ) (F : Finset κ) (S : κ → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisj : Set.Pairwise (↑F) (Disjoint on S))
    (eta : ℝ)
    (hlarge : ∀ i ∈ F, eta ≤
      ∫ t in S i, ‖maskedPhysicalHeight P a b t‖ ^ 2) :
    (F.card : ℝ) * eta ≤
      (Real.pi/4) *
        ∫ u : ℝ, ‖physicalEvenProfile (restrictM P a b) u‖ ^ 2 := by
  calc
    (F.card : ℝ) * eta = ∑ _i ∈ F, eta := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ F, ∫ t in S i, ‖maskedPhysicalHeight P a b t‖ ^ 2 :=
      Finset.sum_le_sum hlarge
    _ ≤ _ := maskedPhysicalHeight_disjoint_slot_sum_le P a b F S hS hdisj

/-- The actual common-mask Fourier remainder, with the full physical q
packet on the left and only a finite sum of its genuine reconstruction modes
subtracted. -/
def maskedFourierRemainder (P : PacketData ι) (a b : ℕ)
    (K : Finset (D4 → ℤ)) (t : ℝ) : ℂ :=
  fullPhysicalHeight (restrictM P a b) t -
    ∑ k ∈ K, heightFourierTerm (restrictM P a b) t k

theorem maskedFourierRemainder_norm_sq_integrable (P : PacketData ι)
    (a b : ℕ) (K : Finset (D4 → ℤ)) :
    Integrable (fun t : ℝ => ‖maskedFourierRemainder P a b K t‖ ^ 2) := by
  let R := restrictM P a b
  have h := amplitudeK_norm_sq_integrable R (tailAmplitude R K)
    (tailAmplitude_physical R K)
  have heq : (fun t : ℝ => ‖maskedFourierRemainder P a b K t‖ ^ 2) =
      fun t : ℝ => ‖amplitudeK R (tailAmplitude R K) t‖ ^ 2 := by
    funext t
    change ‖fullPhysicalHeight R t - ∑ k ∈ K, heightFourierTerm R t k‖ ^ 2 = _
    rw [tailAmplitudeK_eq_heightRemainder]
  rw [heq]
  exact h

/-- Quantitative simultaneous energy control for disjoint slots, by the
existing real four-coordinate Fourier tail of the same masked PacketData. -/
theorem maskedFourierRemainder_disjoint_slot_sum_le (P : PacketData ι)
    (a b : ℕ) (K : Finset (D4 → ℤ))
    (F : Finset κ) (S : κ → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisj : Set.Pairwise (↑F) (Disjoint on S)) :
    (∑ i ∈ F, ∫ t in S i, ‖maskedFourierRemainder P a b K t‖ ^ 2) ≤
      ((Real.pi/4) *
        ∫ u : ℝ, Real.exp (-((restrictM P a b).Y0/16)*|u|)) *
        (((volume : Measure ℝ).real (restrictM P a b).region *
          (coefficientMass (restrictM P a b) *
            (16/(restrictM P a b).Y0))) *
          tailCoefficientMass (restrictM P a b) K) ^ 2 := by
  have hslots := disjoint_slot_sum_le_total
    (fun t : ℝ => ‖maskedFourierRemainder P a b K t‖ ^ 2)
    (maskedFourierRemainder_norm_sq_integrable P a b K)
    (fun t => sq_nonneg _) F S hS hdisj
  exact hslots.trans (by
    simpa only [maskedFourierRemainder] using
      fullHeightFourier_tail_energy_le (restrictM P a b) K)

/-- The number of disjoint high-remainder slots is controlled by the
actual Fourier coefficient tail, not by an assumed supplier. -/
theorem maskedFourierRemainder_large_slot_count (P : PacketData ι)
    (a b : ℕ) (K : Finset (D4 → ℤ))
    (F : Finset κ) (S : κ → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisj : Set.Pairwise (↑F) (Disjoint on S))
    (eta : ℝ)
    (hlarge : ∀ i ∈ F, eta ≤
      ∫ t in S i, ‖maskedFourierRemainder P a b K t‖ ^ 2) :
    (F.card : ℝ) * eta ≤
      ((Real.pi/4) *
        ∫ u : ℝ, Real.exp (-((restrictM P a b).Y0/16)*|u|)) *
        (((volume : Measure ℝ).real (restrictM P a b).region *
          (coefficientMass (restrictM P a b) *
            (16/(restrictM P a b).Y0))) *
          tailCoefficientMass (restrictM P a b) K) ^ 2 := by
  calc
    (F.card : ℝ) * eta = ∑ _i ∈ F, eta := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ F, ∫ t in S i, ‖maskedFourierRemainder P a b K t‖ ^ 2 :=
      Finset.sum_le_sum hlarge
    _ ≤ _ := maskedFourierRemainder_disjoint_slot_sum_le P a b K F S hS hdisj

end
end ImbalancedChen.Part3.ActualCommonMaskDisjointSlotEnergySourceOnly
