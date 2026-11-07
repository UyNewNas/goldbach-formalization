import ImbalancedChen.P4AOriginalFull87TrueSingletonPPMean
import ImbalancedChen.P4AOriginalFull87ActualRhoDivisorTau
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.
The earlier sharp literal counts ALL primes p < N. The actual
Chen additive prime carrier excludes p dividing N, including 2
for an even N. Restore that centre correction exactly ONCE.
-/

namespace ImbalancedChen.P4AOriginalFull87SharpCentreCarrier
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87WeightedSharpSmooth
open P4AOriginalFull87TrueSingletonPPMean
open P4AOriginalFull87ExceptionDivisorFibres
open P4AOriginalFull87ActualRhoDivisorTau
open P4AOriginalFull87EighthPrimeMeanLedger

def actualSharpCarrierLiteral (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ p ∈ chenAdditivePrimeCarrier N,
    originalGapFibre P N cap w z L (N - p)

def centreSharpSigned (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
    actualSmallRoughRho (P false) N cap w z L d *
      chenCentrePrimeAPCount N N d

/-- The existing exact centre AP fibres retain every full-modulus term. -/
theorem centre_signed_eq_actual_gap_sum
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    centreSharpSigned P N cap w z L =
      ∑ p ∈ centrePrimeFactors N,
        originalGapFibre P N cap w z L (N - p) := by
  classical
  let Q := actualSmallRoughModuli (P false) N cap w z
  let ρ := actualSmallRoughRho (P false) N cap w z L
  unfold centreSharpSigned
  simp_rw [centrePrimeAPCount_eq_divisor_fibres]
  change (∑ d ∈ Q, ρ d *
    (∑ p ∈ centrePrimeFactors N,
      if d ∣ N - p then (1 : ℝ) else 0)) = _
  calc
    _ = ∑ d ∈ Q, ∑ p ∈ centrePrimeFactors N,
          if d ∣ N - p then ρ d else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hd : d ∣ N - p <;> simp [hd]
    _ = ∑ p ∈ centrePrimeFactors N, ∑ d ∈ Q,
          if d ∣ N - p then ρ d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ centrePrimeFactors N,
          originalGapFibre P N cap w z L (N - p) := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [originalGapFibre, Finset.sum_filter]

/-- Nonprime centre removes p=N only, not the other prime divisors. -/
theorem sharp_inclusive_prefix
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ)
    (hN : ¬ Nat.Prime N) :
    originalSharpLiteral P N D cap w z L =
      ∑ p ∈ chenPrimePrefix N,
        originalGapFibre P N cap w z L (N - p) := by
  classical
  have hset :
      (chenPrimePrefix (N + D)).filter (fun p => p < N) =
        chenPrimePrefix N := by
    ext p
    simp only [Finset.mem_filter, mem_chenPrimePrefix]
    constructor
    · rintro ⟨⟨_, hp⟩, hlt⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hle, hp⟩
      have hne : p ≠ N := fun heq => hN (heq ▸ hp)
      exact ⟨⟨by omega, hp⟩, by omega⟩
  unfold originalSharpLiteral
  rw [← Finset.sum_filter, hset]

/-- True prime source = unrestricted sharp literal MINUS centre AP. -/
theorem sharp_eq_actual_carrier_add_centre
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ)
    (hN : ¬ Nat.Prime N) :
    originalSharpLiteral P N D cap w z L =
      actualSharpCarrierLiteral P N cap w z L +
        centreSharpSigned P N cap w z L := by
  classical
  let f : ℕ → ℝ := fun p => originalGapFibre P N cap w z L (N - p)
  have hsplit :
      (∑ p ∈ chenPrimePrefix N, f p) =
        (∑ p ∈ (chenPrimePrefix N).filter (fun p => ¬ p ∣ N), f p) +
        (∑ p ∈ centrePrimeFactors N, f p) := by
    unfold centrePrimeFactors
    calc
      _ = ∑ p ∈ chenPrimePrefix N,
            ((if ¬ p ∣ N then f p else 0) +
             (if p ∣ N then f p else 0)) := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hd : p ∣ N <;> simp [hd]
      _ = (∑ p ∈ chenPrimePrefix N,
             if ¬ p ∣ N then f p else 0) +
          (∑ p ∈ chenPrimePrefix N,
             if p ∣ N then f p else 0) := by
        rw [Finset.sum_add_distrib]
      _ = _ := by
        rw [← Finset.sum_filter, ← Finset.sum_filter]
  calc
    originalSharpLiteral P N D cap w z L =
        ∑ p ∈ chenPrimePrefix N, f p := by
      simpa only [f] using sharp_inclusive_prefix
        P N D cap w z L hN
    _ = (∑ p ∈ (chenPrimePrefix N).filter (fun p => ¬ p ∣ N), f p) +
        (∑ p ∈ centrePrimeFactors N, f p) := hsplit
    _ = actualSharpCarrierLiteral P N cap w z L +
        centreSharpSigned P N cap w z L := by
      rw [← chenAdditivePrimeCarrier_eq_prefix_filter N]
      rw [← centre_signed_eq_actual_gap_sum]
      rfl

/-- Already-established receiver injection preserves every original label. -/
theorem actual_carrier_eq_receiver
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    actualSharpCarrierLiteral P N cap w z L =
      ∑ n ∈ chenPrimeReceiverSource N,
        originalGapFibre P N cap w z L n := by
  unfold actualSharpCarrierLiteral
  exact (sum_chenPrimeReceiverSource N
    (originalGapFibre P N cap w z L)).symm

/-- Existing actual centre invoice bounds this signed deletion ONCE. -/
theorem centre_signed_abs_le_invoice
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    |centreSharpSigned P N cap w z L| ≤
      centreDivisorInvoice P N cap w z L := by
  classical
  calc
    |centreSharpSigned P N cap w z L| ≤
        ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
          |actualSmallRoughRho (P false) N cap w z L d *
            chenCentrePrimeAPCount N N d| := by
      unfold centreSharpSigned
      exact Finset.abs_sum_le_sum_abs _ _
    _ = absolutePhysical P N cap w z L (chenCentrePrimeAPCount N N) := by
      simp only [abs_mul]
      rfl
    _ = centreDivisorInvoice P N cap w z L :=
      absolutePhysical_centre_eq_divisor_invoice P N cap w z L

/-- Same physical rho, one PP remainder, two endpoints and one centre. -/
theorem actual_carrier_singleton_PP_invoice
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1)
    (hW : ∀ p, 0 ≤ W p ∧ W p ≤ 1) :
    |actualSharpCarrierLiteral P N cap w z L -
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
            (Nat.totient d : ℝ)))| ≤
      |∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| +
      lowerEndpointInvoice P N D cap w z L +
      upperEndpointInvoice P N D cap w z L +
      centreDivisorInvoice P N cap w z L := by
  let M : ℝ :=
    ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L d *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
          (Nat.totient d : ℝ))
  let E : ℝ :=
    ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L d *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  have hSplit := sharp_eq_actual_carrier_add_centre
    P N D cap w z L hN
  have hOld :
      |originalSharpLiteral P N D cap w z L - M| ≤
        |E| + lowerEndpointInvoice P N D cap w z L +
          upperEndpointInvoice P N D cap w z L :=
    original_sharp_true_singleton_PP_invoice
      P N D cap w z L W hN hInterior hW
  have hCentre := centre_signed_abs_le_invoice P N cap w z L
  have hLinear :
      actualSharpCarrierLiteral P N cap w z L - M =
        (originalSharpLiteral P N D cap w z L - M) -
          centreSharpSigned P N cap w z L := by
    rw [hSplit]
    ring
  change |actualSharpCarrierLiteral P N cap w z L - M| ≤
    |E| + lowerEndpointInvoice P N D cap w z L +
      upperEndpointInvoice P N D cap w z L +
      centreDivisorInvoice P N cap w z L
  calc
    _ = |(originalSharpLiteral P N D cap w z L - M) -
          centreSharpSigned P N cap w z L| := congrArg abs hLinear
    _ ≤ |originalSharpLiteral P N D cap w z L - M| +
          |centreSharpSigned P N cap w z L| := abs_sub_le _ _
    _ ≤ (|E| + lowerEndpointInvoice P N D cap w z L +
          upperEndpointInvoice P N D cap w z L) +
          centreDivisorInvoice P N cap w z L :=
      add_le_add hOld hCentre
    _ = _ := by ring

end
end ImbalancedChen.P4AOriginalFull87SharpCentreCarrier
