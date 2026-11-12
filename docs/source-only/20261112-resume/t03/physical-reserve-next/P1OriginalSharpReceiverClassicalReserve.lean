import ImbalancedChen.P1OriginalSharpFiniteReceiver
import ImbalancedChen.P4AOriginalFull87SharpCentreCarrier
import ImbalancedChen.P4AOriginalFull87SharpMeanPaymentLedger

/-! Read the original singleton payment on each actual small/rough
coefficient, then subtract with its original sign before taking absolute values. -/
namespace ImbalancedChen.P1OriginalSharpReceiverClassicalReserve
noncomputable section
open Filter
open scoped Classical BigOperators
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87SharpCentreCarrier (actualSharpCarrierLiteral actual_carrier_eq_receiver)
open P4AOriginalFull87SharpMeanPaymentLedger (physical_full_q_valid)
open P4AOriginalFull87EighthPrimeMeanLedger (primeMass densityTest receiverTest)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87CentreFrozenHN (frozenHN)
abbrev cut := P1OriginalSharpFiniteReceiver.cut

def above (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  physical P N cap w z L (highQTest (cut N) (sharpPrimeError N))

theorem carrier_is_physical (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    actualSharpCarrierLiteral P N cap w z L=physical P N cap w z L (receiverTest N) := by
  rw [actual_carrier_eq_receiver]
  exact P1OriginalSharpFiniteReceiver.literal_eq N (actualSmallRoughModuli (P false) N cap w z)
    (actualSmallRoughRho (P false) N cap w z L)

theorem eventually_singleton_reserve (u : ℝ) (hu : 0<u) :
    ∀ᶠ N : ℕ in atTop,Even N → ∀ (P : Bool → List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      |actualSharpCarrierLiteral P N cap w z L-primeMass N*physical P N cap w z L densityTest-
        above P N cap w z L|≤u*frozenHN N := by
  filter_upwards [P1OriginalSharpFiniteReceiver.eventual_receiver u hu] with N H
  intro hev P cap w z L
  rw [actual_carrier_eq_receiver]
  apply H hev
  intro d hd
  have hp := physical_full_q_valid P N cap w z hd
  exact ⟨hp.2.1,hp.2.2,actualSmallRoughRho_abs_le_one _ _ _ _ _ _ d⟩

/-- Preserve the two actual high-modulus coefficients under subtraction.
The budgets for the two singleton applications add to the original u. -/
theorem eventually_receiver_pair (u : ℝ) (hu : 0<u) :
    ∀ᶠ N : ℕ in atTop,Even N → ∀ (P Q : Bool → List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      |(physical P N cap w z L (receiverTest N)-physical Q N cap w z L (receiverTest N))-
        primeMass N*(physical P N cap w z L densityTest-physical Q N cap w z L densityTest)-
        (above P N cap w z L-above Q N cap w z L)|≤u*frozenHN N := by
  filter_upwards [eventually_singleton_reserve (u/2) (half_pos hu)] with N H
  intro hev P Q cap w z L
  have hP := H hev P cap w z L
  have hQ := H hev Q cap w z L
  rw [carrier_is_physical] at hP hQ
  calc
    _ = |(physical P N cap w z L (receiverTest N)-primeMass N*physical P N cap w z L densityTest-
        above P N cap w z L)-
        (physical Q N cap w z L (receiverTest N)-primeMass N*physical Q N cap w z L densityTest-
        above Q N cap w z L)| := by congr 1 <;> ring
    _ ≤ _ := (abs_sub_le _ _).trans (by linarith only [hP,hQ])

end
end ImbalancedChen.P1OriginalSharpReceiverClassicalReserve
