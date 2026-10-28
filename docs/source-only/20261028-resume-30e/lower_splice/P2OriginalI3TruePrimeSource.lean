import ImbalancedChen.P2OriginalI3ActualSmallRosserAttachment
import ImbalancedChen.ChenInitialPrimeSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite A parameter is instantiated with the existing independently
specified original additive-prime carrier, retaining its centre deletion,
strict receiver endpoint and exact modulus-dependent coprime mean.
-/
namespace ImbalancedChen.P2OriginalI3TruePrimeSource
noncomputable section
open scoped Classical BigOperators
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment

theorem attachedSupport_coprime_target {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z : ℝ) (q : ℕ)
    (hq : q ∈ attachedSupport D N cap y z) : Nat.Coprime q N := by
  rw [attachedSupport_eq_actual_union] at hq
  rcases Finset.mem_union.mp hq with hn | ho
  · exact actualLowerSmallRoughModuli_coprime_target
      (thirdRetain D N) N cap y z hn
  · exact actualLowerSmallRoughModuli_coprime_target
      (seedRetain D N) N cap y z ho

/-- The source is the production prime sequence, not a generic supplied A. -/
theorem true_source_residue_count (N q : ℕ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, if q ∣ N-P then (1 : ℝ) else 0) =
      finiteCongruenceMass (chenAdditivePrimeCarrier N) (fun _ => 1) N q := by
  rw [← Finset.sum_filter, chenAdditivePrimeCarrier_filter_dvd_eq_AP]
  rfl

/-- The full prime prefix has two visible exceptional prime sets. The
centre AP deletion and its centre-divisor mass are never erased. -/
theorem true_source_error_eq_prefix_error {N q : ℕ} (hqN : Nat.Coprime q N) :
    finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N q =
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q +
        chenPrimeDivisorCount N N / (Nat.totient q : ℝ) -
          chenCentrePrimeAPCount N N q := by
  have hAP : finiteCongruenceMass (chenAdditivePrimeCarrier N) (fun _ => 1) N q =
      chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q := by
    simpa [finiteCongruenceMass] using chenAdditivePrimeCarrier_AP_count N N q
  have hfullAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N q =
      chenPrimeAPCount N N q := by
    simp [finiteCongruenceMass, chenPrimeAPCount]
  unfold finitePrimitiveDiscrepancy
  rw [hAP, hfullAP, chenAdditivePrimeCarrier_coprime_mass hqN,
    chenAdditivePrimeCarrier_card_cast, chenPrimePrefix_coprime_mass]
  ring

def truePrimeError {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) : ℝ :=
  attachedDiscrepancy D N cap y z L (chenAdditivePrimeCarrier N) (fun _ => 1)

/-- The actual attached physical rho is applied to the original prime
residue count and the exact coprime mean of that same prime source. -/
theorem truePrimeError_eq_same_rho_primitive_sum {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) :
    truePrimeError D N cap y z L =
      ∑ q ∈ attachedSupport D N cap y z, attachedRho D N cap y z L q *
        finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N q := by
  unfold truePrimeError attachedDiscrepancy finitePrimitiveDiscrepancy
  apply Finset.sum_congr rfl
  intro q hq
  rw [true_source_residue_count]
  simp only [finiteCoprimeMass, Finset.sum_filter]

/-- This identifies the genuine supplier-facing prime AP source while
preserving its exact centre and modulus corrections and its fixed rho. -/
theorem truePrimeError_eq_full_prefix_with_centre_corrections {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ) :
    truePrimeError D N cap y z L =
      ∑ q ∈ attachedSupport D N cap y z, attachedRho D N cap y z L q *
        (finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q +
          chenPrimeDivisorCount N N / (Nat.totient q : ℝ) -
            chenCentrePrimeAPCount N N q) := by
  rw [truePrimeError_eq_same_rho_primitive_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [true_source_error_eq_prefix_error (attachedSupport_coprime_target D N cap y z q hq)]

/-- The exact mean retains the nonprimitive modulus primes, rather than
replacing it with total source mass divided by phi. -/
theorem true_prime_exact_mean {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) :
    attachedExactMean D N cap y z L (chenAdditivePrimeCarrier N) (fun _ => 1) =
      ∑ q ∈ attachedSupport D N cap y z, attachedRho D N cap y z L q *
        ((((chenAdditivePrimeCarrier N).card : ℝ) - chenPrimeDivisorCount N q) /
          (Nat.totient q : ℝ)) := by
  unfold attachedExactMean
  apply Finset.sum_congr rfl
  intro q hq
  have hm := chenAdditivePrimeCarrier_coprime_mass
    (attachedSupport_coprime_target D N cap y z q hq)
  rw [finiteCoprimeMass, Finset.sum_filter] at hm
  rw [hm]

/-- Original-prime shifted count, same signed attached coefficient, and
same exact mean. All receiver endpoints follow the production source. -/
theorem true_prime_count_mean_error {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N,
      physicalDivisorSum (attachedSupport D N cap y z)
        (attachedRho D N cap y z L) (N-P)) =
      attachedExactMean D N cap y z L (chenAdditivePrimeCarrier N) (fun _ => 1) +
        truePrimeError D N cap y z L := by
  have he := attachedDiscrepancy_eq_actual_count_sub_exact_mean D N cap y z L
    (chenAdditivePrimeCarrier N) (fun _ => 1)
  unfold attachedCount at he
  simp only [one_mul] at he
  unfold truePrimeError
  linarith

end
end ImbalancedChen.P2OriginalI3TruePrimeSource
