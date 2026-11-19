import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The ORIGINAL physical sieve modulus is d in
  actualSmallRoughModuli retainOdd N cap w z,
with coefficient
  actualSmallRoughRho retainOdd N cap w z L d.
The receiver n=N-P is only the ARGUMENT of its divisor sum. In
particular, the previous reflected one-shell Q=a*(p::pre).prod>N/2
is NOT substituted for this physical d.

Two finite identities below use the literal primitive additive-prime
carrier, preserve signed rho, and expose both the centre-prime and
modulus-prime corrections. No PP, smoothness, H_N payment, numerical
archive, or frozen-87 occurrence aggregation is assumed.

The retention policy is a parameter because the original dynamic
policy/ordered occurrence aggregation remains a separate obligation.
-/

namespace ImbalancedChen.P4AOriginalFull87TruePhysicalPrimeDivisor

noncomputable section
open scoped BigOperators
open Classical

/-- Genuine physical R_N(n) averaged over the ORIGINAL injective
prime receiver set. The modulus d remains in its real small/rough
support; the receiver n is only tested for d | n. Every signed
coefficient is used exactly once, with no copied shell modulus. -/
theorem actual_physical_prime_receiver_eq_signed_AP
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    (∑ n ∈ chenPrimeReceiverSource N,
      physicalDivisorSum
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n) =
      ∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
        actualSmallRoughRho retainOdd N cap w z L d *
          (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d) := by
  classical
  change (∑ n ∈ chenPrimeReceiverSource N,
      ∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
        if d ∣ n then
          actualSmallRoughRho retainOdd N cap w z L d else 0) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [chenPrimeReceiverSource_divisibility_fibre_card,
    chenAdditivePrimeCarrier_AP_count]
  ring

/-- Exact finite prime-source main + primitive discrepancy + real
modulus-prime correction for THE SAME physical rho(d).

The original receiver source removes centre-prime divisors. Its
coprime mass is not its total mass at every modulus, so the final
minus sign is essential. The signed distribution term is kept
whole, without taking absolute values or invoking a PP theorem.
Evenness is used solely by the existing initial BoundingSieve
remainder identity; no external analytic estimate is installed. -/
theorem actual_physical_prime_receiver_primitive_invoice
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hN : Even N) :
    (∑ n ∈ chenPrimeReceiverSource N,
      physicalDivisorSum
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum
          (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) +
      (∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
        actualSmallRoughRho retainOdd N cap w z L d *
          finitePrimitiveDiscrepancy
            (chenAdditivePrimeCarrier N) (fun _ => 1) N d) -
      (∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
        actualSmallRoughRho retainOdd N cap w z L d *
          (chenPrimeDivisorCount N d / (Nat.totient d : ℝ))) := by
  classical
  rw [actual_physical_prime_receiver_eq_signed_AP]
  let S : Finset ℕ := actualSmallRoughModuli retainOdd N cap w z
  let rho : ℕ → ℝ := actualSmallRoughRho retainOdd N cap w z L
  let M : ℝ := ((chenAdditivePrimeCarrier N).card : ℝ)
  change (∑ d ∈ S,
    rho d * (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)) =
    M * physicalDensitySum S rho +
    (∑ d ∈ S, rho d *
      finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N d) -
    (∑ d ∈ S, rho d *
      (chenPrimeDivisorCount N d / (Nat.totient d : ℝ)))
  calc
    _ = ∑ d ∈ S, rho d *
        (M / (Nat.totient d : ℝ) +
          finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
            (fun _ => 1) N d -
          chenPrimeDivisorCount N d / (Nat.totient d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hcop : Nat.Coprime d N :=
        actualSmallRoughModuli_coprime_target
          retainOdd N cap w z hd
      have hrem :=
        chenInitialBoundingSieve_rem_eq_source_discrepancy
          N z hN hcop
      rw [chenInitialBoundingSieve_rem] at hrem
      have heq :
          chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d =
            M / (Nat.totient d : ℝ) +
              finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
                (fun _ => 1) N d -
              chenPrimeDivisorCount N d / (Nat.totient d : ℝ) := by
        dsimp [M]
        linarith
      rw [heq]
    _ = (∑ d ∈ S, rho d * (M / (Nat.totient d : ℝ))) +
        (∑ d ∈ S, rho d *
          finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
            (fun _ => 1) N d) -
        (∑ d ∈ S, rho d *
          (chenPrimeDivisorCount N d / (Nat.totient d : ℝ))) := by
      simp only [mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      have hmean :
          (∑ d ∈ S, rho d * (M / (Nat.totient d : ℝ))) =
            M * physicalDensitySum S rho := by
        unfold physicalDensitySum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      rw [hmean]

end
end ImbalancedChen.P4AOriginalFull87TruePhysicalPrimeDivisor
