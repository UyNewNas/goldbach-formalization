import ImbalancedChen.P4AOriginalFull87SharpCentreCarrier
import ImbalancedChen.P4AOriginalFull87WeightedPrimitiveRecentering
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: exact smooth-coprime singleton mean to sharp prime density on the
SAME actual sixth/eighth full-q coefficient. This is the missing finite
payment ledger after correcting the actual centre-prime deletion.
No new arithmetic mask, no independent sieve bound, no analytic PP
hypothesis, no asymptotic estimate and no reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87SharpMeanPaymentLedger
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87WeightedSharpSmooth
open P4AOriginalFull87WeightedPrimitiveRecentering
open P4AOriginalFull87SharpCentreCarrier
open P4AOriginalFull87TrueSingletonPPMean

/-- Difference between sharp unit weight and the smooth weight on the
INCLUSIVE original prime prefix. The eventual Gevrey input must prove
its smallness separately. -/
def lowerWeightDefect (N : ℕ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ chenPrimePrefix N, (1 - W p)

/-- Upper smooth prime tail of the very same enlarged prefix. -/
def upperWeightTail (N D : ℕ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (chenPrimePrefix (N + D)).filter (fun p => N < p), W p

/-- Exact smooth prime mass split. This has no positivity or support
hypotheses and does not conflate the two signs of the endpoint. -/
theorem weighted_prime_mass_sharp_split (N D : ℕ) (W : ℕ → ℝ) :
    weightedPrimeMass N D W =
      ((chenPrimePrefix N).card : ℝ) -
        lowerWeightDefect N W + upperWeightTail N D W := by
  classical
  have hprefix :
      (chenPrimePrefix (N + D)).filter (fun p => p ≤ N) =
        chenPrimePrefix N := by
    ext p
    simp only [Finset.mem_filter, mem_chenPrimePrefix]
    constructor
    · rintro ⟨⟨_, hp⟩, hle⟩
      exact ⟨hle, hp⟩
    · rintro ⟨hle, hp⟩
      exact ⟨⟨by omega, hp⟩, hle⟩
  have hlow :
      (∑ p ∈ chenPrimePrefix N, W p) =
        ((chenPrimePrefix N).card : ℝ) - lowerWeightDefect N W := by
    unfold lowerWeightDefect
    have hsum :
        (∑ p ∈ chenPrimePrefix N, (1 : ℝ) - W p) =
          ((chenPrimePrefix N).card : ℝ) -
            ∑ p ∈ chenPrimePrefix N, W p := by
      rw [Finset.sum_sub_distrib]
      simp
    linarith
  unfold weightedPrimeMass
  calc
    (∑ p ∈ chenPrimePrefix (N + D), W p) =
        ∑ p ∈ chenPrimePrefix (N + D),
          ((if p ≤ N then W p else 0) +
            (if N < p then W p else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ≤ N
      · simp [hp, not_lt.mpr hp]
      · have hgt : N < p := Nat.lt_of_not_ge hp
        simp [hp, hgt]
    _ = (∑ p ∈ (chenPrimePrefix (N + D)).filter (fun p => p ≤ N), W p) +
        (∑ p ∈ (chenPrimePrefix (N + D)).filter (fun p => N < p), W p) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    _ = ((chenPrimePrefix N).card : ℝ) -
          lowerWeightDefect N W + upperWeightTail N D W := by
      rw [hprefix, hlow]
      rfl

/-- The actual displayed full-q carrier has neither a zero modulus nor
a non-squarefree or centre-sharing modulus, for either frozen policy. -/
theorem physical_full_q_valid
    (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ actualSmallRoughModuli (P false) N cap w z) :
    0 < q ∧ Squarefree q ∧ Nat.Coprime q N := by
  have hsq := actualSmallRoughModuli_squarefree (P false) N cap w z hq
  exact ⟨Nat.pos_of_ne_zero hsq.ne_zero, hsq,
    actualSmallRoughModuli_coprime_target (P false) N cap w z hq⟩

/-- NEW exact q-dependent normalization. The true smooth-coprime
singleton mean is not the sharp prime density: their discrepancy is
ONE lower weight defect, ONE upper smooth tail, and the actual
weighted modulus-prime correction. All signs and full-q rho survive. -/
theorem actual_smooth_mean_to_sharp_density_exact
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L q *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W q /
          (Nat.totient q : ℝ))) -
      ((chenPrimePrefix N).card : ℝ) *
        (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
          actualSmallRoughRho (P false) N cap w z L q /
            (Nat.totient q : ℝ)) =
      (upperWeightTail N D W - lowerWeightDefect N W) *
        (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
          actualSmallRoughRho (P false) N cap w z L q /
            (Nat.totient q : ℝ)) -
      (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L q *
          (weightedModulusPrimeMass N D q W / (Nat.totient q : ℝ))) := by
  classical
  let Q := actualSmallRoughModuli (P false) N cap w z
  let ρ := actualSmallRoughRho (P false) N cap w z L
  let T := weightedPrimeMass N D W
  let V : ℝ := ∑ q ∈ Q, ρ q / (Nat.totient q : ℝ)
  let C : ℝ := ∑ q ∈ Q, ρ q *
    (weightedModulusPrimeMass N D q W / (Nat.totient q : ℝ))
  have hpoint (q : ℕ) :
      ρ q * (finiteCoprimeMass (chenPrimePrefix (N + D)) W q /
        (Nat.totient q : ℝ)) =
      T * (ρ q / (Nat.totient q : ℝ)) -
        ρ q * (weightedModulusPrimeMass N D q W /
          (Nat.totient q : ℝ)) := by
    rw [weighted_coprime_mass_eq_full_sub_modulus_primes]
    ring
  have hmean :
      (∑ q ∈ Q, ρ q *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W q /
          (Nat.totient q : ℝ))) = T * V - C := by
    calc
      _ = ∑ q ∈ Q,
          (T * (ρ q / (Nat.totient q : ℝ)) -
            ρ q * (weightedModulusPrimeMass N D q W /
              (Nat.totient q : ℝ))) := by
        apply Finset.sum_congr rfl
        intro q _
        exact hpoint q
      _ = T * V - C := by
        simp only [Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        rfl
  have hmass := weighted_prime_mass_sharp_split N D W
  change (∑ q ∈ Q, ρ q *
    (finiteCoprimeMass (chenPrimePrefix (N + D)) W q /
      (Nat.totient q : ℝ))) -
    ((chenPrimePrefix N).card : ℝ) * V =
      (upperWeightTail N D W - lowerWeightDefect N W) * V - C
  rw [hmean, hmass]
  ring

/-- Quantitative finite absolute invoice, still *not* a small-o or a
reserve payment. The modulus error is the true weighted prime-divisor
mass, not an unrelated rough-sieve majorant. -/
theorem actual_smooth_mean_to_sharp_density_invoice
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) :
    |(∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L q *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W q /
          (Nat.totient q : ℝ))) -
      ((chenPrimePrefix N).card : ℝ) *
        (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
          actualSmallRoughRho (P false) N cap w z L q /
            (Nat.totient q : ℝ))| ≤
      |upperWeightTail N D W - lowerWeightDefect N W| *
        (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
          |actualSmallRoughRho (P false) N cap w z L q /
            (Nat.totient q : ℝ)|) +
      (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
        |actualSmallRoughRho (P false) N cap w z L q *
          (weightedModulusPrimeMass N D q W / (Nat.totient q : ℝ))|) := by
  classical
  let Q := actualSmallRoughModuli (P false) N cap w z
  let ρ := actualSmallRoughRho (P false) N cap w z L
  let V : ℝ := ∑ q ∈ Q, ρ q / (Nat.totient q : ℝ)
  let C : ℝ := ∑ q ∈ Q, ρ q *
    (weightedModulusPrimeMass N D q W / (Nat.totient q : ℝ))
  let E := upperWeightTail N D W - lowerWeightDefect N W
  have hV : |V| ≤ ∑ q ∈ Q, |ρ q / (Nat.totient q : ℝ)| := by
    dsimp [V]
    exact Finset.abs_sum_le_sum_abs _ _
  have hC : |C| ≤ ∑ q ∈ Q,
      |ρ q * (weightedModulusPrimeMass N D q W /
        (Nat.totient q : ℝ))| := by
    dsimp [C]
    exact Finset.abs_sum_le_sum_abs _ _
  have hExact := actual_smooth_mean_to_sharp_density_exact P N D cap w z L W
  change |(∑ q ∈ Q,
    ρ q * (finiteCoprimeMass (chenPrimePrefix (N + D)) W q /
      (Nat.totient q : ℝ))) -
    ((chenPrimePrefix N).card : ℝ) * V| ≤
    |E| * (∑ q ∈ Q, |ρ q / (Nat.totient q : ℝ)|) +
    (∑ q ∈ Q,
      |ρ q * (weightedModulusPrimeMass N D q W /
        (Nat.totient q : ℝ))|)
  rw [hExact]
  calc
    |E * V - C| ≤ |E * V| + |C| := abs_sub_le _ _
    _ = |E| * |V| + |C| := by rw [abs_mul]
    _ ≤ |E| * (∑ q ∈ Q, |ρ q / (Nat.totient q : ℝ)|) +
        (∑ q ∈ Q,
          |ρ q * (weightedModulusPrimeMass N D q W /
            (Nat.totient q : ℝ))|) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hV (abs_nonneg E)) hC

/-- Final same-rho *finite* sharp-density bridge after actual centre
deletion, without charging that centre twice. The sharp π/φ comparison
is now explicit; proving the right side o(H_N) is still the real task. -/
theorem actual_carrier_sharp_density_invoice
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1)
    (hW : ∀ p, 0 ≤ W p ∧ W p ≤ 1) :
    |actualSharpCarrierLiteral P N cap w z L -
      ((chenPrimePrefix N).card : ℝ) *
        (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
          actualSmallRoughRho (P false) N cap w z L q /
            (Nat.totient q : ℝ))| ≤
      |∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L q *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N q| +
      lowerEndpointInvoice P N D cap w z L +
      upperEndpointInvoice P N D cap w z L +
      centreDivisorInvoice P N cap w z L +
      |upperWeightTail N D W - lowerWeightDefect N W| *
        (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
          |actualSmallRoughRho (P false) N cap w z L q /
            (Nat.totient q : ℝ)|) +
      (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
        |actualSmallRoughRho (P false) N cap w z L q *
          (weightedModulusPrimeMass N D q W / (Nat.totient q : ℝ))|) := by
  let M : ℝ := ∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
    actualSmallRoughRho (P false) N cap w z L q *
      (finiteCoprimeMass (chenPrimePrefix (N + D)) W q /
        (Nat.totient q : ℝ))
  let V : ℝ := ∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
    actualSmallRoughRho (P false) N cap w z L q /
      (Nat.totient q : ℝ)
  let T : ℝ := ((chenPrimePrefix N).card : ℝ) * V
  let A : ℝ := |∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
    actualSmallRoughRho (P false) N cap w z L q *
      finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N q| +
    lowerEndpointInvoice P N D cap w z L +
    upperEndpointInvoice P N D cap w z L +
    centreDivisorInvoice P N cap w z L
  let B : ℝ := |upperWeightTail N D W - lowerWeightDefect N W| *
    (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
      |actualSmallRoughRho (P false) N cap w z L q /
        (Nat.totient q : ℝ)|) +
    (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
      |actualSmallRoughRho (P false) N cap w z L q *
        (weightedModulusPrimeMass N D q W / (Nat.totient q : ℝ))|)
  have hActual : |actualSharpCarrierLiteral P N cap w z L - M| ≤ A :=
    actual_carrier_singleton_PP_invoice P N D cap w z L W hN hInterior hW
  have hMean : |M - T| ≤ B :=
    actual_smooth_mean_to_sharp_density_invoice P N D cap w z L W
  change |actualSharpCarrierLiteral P N cap w z L - T| ≤ A + B
  calc
    _ = |(actualSharpCarrierLiteral P N cap w z L - M) +
      (M - T)| := by congr 1; ring
    _ ≤ |actualSharpCarrierLiteral P N cap w z L - M| +
      |M - T| := abs_add_le _ _
    _ ≤ A + B := add_le_add hActual hMean

end
end ImbalancedChen.P4AOriginalFull87SharpMeanPaymentLedger
