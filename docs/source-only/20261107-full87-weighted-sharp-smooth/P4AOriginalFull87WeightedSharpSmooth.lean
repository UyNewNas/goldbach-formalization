import ImbalancedChen.P4AOriginalFull87SameRhoEndpointDivisor
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: the finite, signed, SAME-RHO sharp-to-smooth original-prime bridge.
The previous signedEndpointBoundary sums two unweighted endpoint sources.
For a general smoothing profile it is NOT literally the sharp-minus-smooth
difference. The correct difference uses (1-W p) below N and -W p above N.
This packet proves that precise algebraic identity and its absolute invoice
for the original sign-attached physical beta. It does not claim that the
analytic smoothing profile, prime-product distribution, the mean endpoint
or the density reserve has been discharged.
-/

namespace ImbalancedChen.P4AOriginalFull87WeightedSharpSmooth
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SameRhoEndpointDivisor

/-- The literal physical modulus fibre at a positive prime/centre gap.
The sign and full modulus are unchanged from the sixth/eighth source. -/
def originalGapFibre (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (gap : ℕ) : ℝ :=
  ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
    (fun d => d ∣ gap),
    actualSmallRoughRho (P false) N cap w z L d

/-- Sharp original-prime sum, written in one common finite prime universe.
The centre is separately excluded; for the manuscript's even N>2 this is
exactly the inclusive prime prefix with its (impossible) prime centre gone. -/
def originalSharpLiteral (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ p ∈ chenPrimePrefix (N + D),
    if p < N then originalGapFibre P N cap w z L (N - p) else 0

/-- Smooth original-prime sum over the SAME frozen rho and same modulus.
The two physical gaps have the same divisibility as the integer N-p.
The p=N zero gap is excluded rather than charged to the divisor sum. -/
def originalSmoothLiteral (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ chenPrimePrefix (N + D),
    if p < N then W p * originalGapFibre P N cap w z L (N - p)
    else if N < p then W p * originalGapFibre P N cap w z L (p - N)
    else 0

/-- Actual lower endpoint correction: (1-W) rather than one copy of rho. -/
def weightedLowerBoundary (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ lowerEndpointPrimes N D,
    (1 - W p) * originalGapFibre P N cap w z L (N - p)

/-- Actual upper endpoint correction: the smooth tail, with its minus sign
introduced by the sharp-minus-smooth identity below. -/
def weightedUpperBoundary (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ upperEndpointPrimes N D,
    W p * originalGapFibre P N cap w z L (p - N)

/-- On the lower side, only the true nonzero endpoint window contributes.
The smoothing is required to be identically one below that window; this
is an explicit condition and NOT a property inferred from a smooth PP. -/
private theorem lower_weighted_sum_localizes
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1) :
    (∑ p ∈ chenPrimePrefix (N + D),
       if p < N then
         (1 - W p) * originalGapFibre P N cap w z L (N - p) else 0) =
      weightedLowerBoundary P N D cap w z L W := by
  classical
  have hset : (chenPrimePrefix (N + D)).filter
      (fun p => p < N ∧ N - p ≤ D) = lowerEndpointPrimes N D := by
    ext p
    simp only [Finset.mem_filter, mem_chenPrimePrefix, lowerEndpointPrimes]
    constructor
    · rintro ⟨⟨hle, hprime⟩, ⟨hlt, hgap⟩⟩
      exact ⟨⟨by omega, hprime⟩, ⟨hlt, hgap⟩⟩
    · rintro ⟨⟨hle, hprime⟩, ⟨hlt, hgap⟩⟩
      exact ⟨⟨by omega, hprime⟩, ⟨hlt, hgap⟩⟩
  calc
    (∑ p ∈ chenPrimePrefix (N + D),
       if p < N then
         (1 - W p) * originalGapFibre P N cap w z L (N - p) else 0) =
      ∑ p ∈ chenPrimePrefix (N + D),
        if p < N ∧ N - p ≤ D then
          (1 - W p) * originalGapFibre P N cap w z L (N - p) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hlt : p < N
        · by_cases hgap : N - p ≤ D
          · simp [hlt, hgap]
          · have hW := hInterior p hlt (by omega)
            simp [hlt, hgap, hW]
        · simp [hlt]
    _ = ∑ p ∈ (chenPrimePrefix (N + D)).filter
        (fun p => p < N ∧ N - p ≤ D),
        (1 - W p) * originalGapFibre P N cap w z L (N - p) := by
          rw [Finset.sum_filter]
    _ = weightedLowerBoundary P N D cap w z L W := by
          rw [hset]
          rfl

/-- The actual upper smoothing extension is exactly the old upper
endpoint prime list, since all p in that extension obey p-N≤D. -/
private theorem upper_weighted_sum_localizes
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) :
    (∑ p ∈ chenPrimePrefix (N + D),
       if N < p then
         W p * originalGapFibre P N cap w z L (p - N) else 0) =
      weightedUpperBoundary P N D cap w z L W := by
  classical
  have hset : (chenPrimePrefix (N + D)).filter (fun p => N < p) =
      upperEndpointPrimes N D := by
    ext p
    simp only [Finset.mem_filter, mem_chenPrimePrefix, upperEndpointPrimes]
    constructor
    · rintro ⟨⟨hle, hp⟩, hgt⟩
      exact ⟨⟨hle, hp⟩, ⟨hgt, by omega⟩⟩
    · rintro ⟨⟨hle, hp⟩, ⟨hgt, _⟩⟩
      exact ⟨⟨hle, hp⟩, hgt⟩
  calc
    (∑ p ∈ chenPrimePrefix (N + D),
       if N < p then
         W p * originalGapFibre P N cap w z L (p - N) else 0) =
      ∑ p ∈ (chenPrimePrefix (N + D)).filter (fun p => N < p),
        W p * originalGapFibre P N cap w z L (p - N) := by
          rw [Finset.sum_filter]
    _ = weightedUpperBoundary P N D cap w z L W := by
          rw [hset]
          rfl

/-- The signed sharp/smooth difference has a MINUS upper tail and
a (1-W) lower correction. It is not the former two-positive-tail
signedEndpointBoundary. Both tests use one fixed actual rho. -/
theorem sharp_minus_smooth_eq_weighted_boundaries
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1) :
    originalSharpLiteral P N D cap w z L -
      originalSmoothLiteral P N D cap w z L W =
    weightedLowerBoundary P N D cap w z L W -
      weightedUpperBoundary P N D cap w z L W := by
  classical
  have hpoint (p : ℕ) :
      (if p < N then originalGapFibre P N cap w z L (N - p) else 0) -
        (if p < N then W p * originalGapFibre P N cap w z L (N - p)
         else if N < p then W p * originalGapFibre P N cap w z L (p - N)
         else 0) =
      (if p < N then (1 - W p) * originalGapFibre P N cap w z L (N - p)
       else 0) -
      (if N < p then W p * originalGapFibre P N cap w z L (p - N)
       else 0) := by
    by_cases hlt : p < N
    · have hnot : ¬ N < p := by omega
      simp [hlt, hnot]
      ring
    · by_cases hgt : N < p
      · simp [hlt, hgt]
      · have heq : p = N := by omega
        subst p
        simp
  have hraw :
      originalSharpLiteral P N D cap w z L -
        originalSmoothLiteral P N D cap w z L W =
      ∑ p ∈ chenPrimePrefix (N + D),
        ((if p < N then originalGapFibre P N cap w z L (N - p) else 0) -
         (if p < N then W p * originalGapFibre P N cap w z L (N - p)
          else if N < p then W p * originalGapFibre P N cap w z L (p - N)
          else 0)) := by
    rw [Finset.sum_sub_distrib]
    rfl
  rw [hraw]
  calc
    (∑ p ∈ chenPrimePrefix (N + D),
        ((if p < N then originalGapFibre P N cap w z L (N - p) else 0) -
         (if p < N then W p * originalGapFibre P N cap w z L (N - p)
          else if N < p then W p * originalGapFibre P N cap w z L (p - N)
          else 0))) =
      ∑ p ∈ chenPrimePrefix (N + D),
        ((if p < N then
            (1 - W p) * originalGapFibre P N cap w z L (N - p) else 0) -
         (if N < p then W p * originalGapFibre P N cap w z L (p - N)
          else 0)) := by
            apply Finset.sum_congr rfl
            intro p _
            exact hpoint p
    _ = (∑ p ∈ chenPrimePrefix (N + D),
            if p < N then
              (1 - W p) * originalGapFibre P N cap w z L (N - p) else 0) -
        (∑ p ∈ chenPrimePrefix (N + D),
            if N < p then
              W p * originalGapFibre P N cap w z L (p - N) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = weightedLowerBoundary P N D cap w z L W -
          weightedUpperBoundary P N D cap w z L W := by
          rw [lower_weighted_sum_localizes P N D cap w z L W hInterior,
              upper_weighted_sum_localizes P N D cap w z L W]

/-- Direct arithmetic identification with the true inclusive sharp
original-prime prefix: no extra primes are created by the ambient
smoothing extension. -/
theorem original_sharp_eq_strict_prime_prefix
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ) :
    originalSharpLiteral P N D cap w z L =
      ∑ p ∈ chenPrimePrefix N,
        if p < N then originalGapFibre P N cap w z L (N - p) else 0 := by
  classical
  have hsub : chenPrimePrefix N ⊆ chenPrimePrefix (N + D) := by
    intro p hp
    obtain ⟨hle, hprime⟩ := mem_chenPrimePrefix.mp hp
    exact mem_chenPrimePrefix.mpr ⟨by omega, hprime⟩
  have hzero : ∀ p ∈ chenPrimePrefix (N + D),
      p ∉ chenPrimePrefix N →
      (if p < N then originalGapFibre P N cap w z L (N - p) else 0) = 0 := by
    intro p hp hnot
    have hnotLt : ¬ p < N := by
      intro hlt
      have hprime := (mem_chenPrimePrefix.mp hp).2
      exact hnot (mem_chenPrimePrefix.mpr ⟨by omega, hprime⟩)
    simp [hnotLt]
  unfold originalSharpLiteral
  exact (Finset.sum_subset hsub hzero).symm

/-- At the manuscript's nonprime (in particular even >2) centre, the
sharp prefix can be written with the original unmasked prime endpoint. -/
theorem original_sharp_eq_full_prime_prefix_of_nonprime
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ)
    (hN : ¬ Nat.Prime N) :
    originalSharpLiteral P N D cap w z L =
      ∑ p ∈ chenPrimePrefix N, originalGapFibre P N cap w z L (N - p) := by
  rw [original_sharp_eq_strict_prime_prefix]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hle, hprime⟩ := mem_chenPrimePrefix.mp hp
  have hlt : p < N := by
    by_contra hn
    have heq : p = N := by omega
    exact hN (heq ▸ hprime)
  simp [hlt]

/-- A one-bounded smoothing weight cannot cost more than the physical
absolute original-modulus divisor fibre. This bound is local, not PP. -/
private theorem weighted_original_gap_abs_le_invoice
    (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (gap : ℕ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |a * originalGapFibre P N cap w z L gap| ≤
      ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun d => d ∣ gap),
        |actualSmallRoughRho (P false) N cap w z L d| := by
  let S := (actualSmallRoughModuli (P false) N cap w z).filter
    (fun d => d ∣ gap)
  have htri : |originalGapFibre P N cap w z L gap| ≤
      ∑ d ∈ S, |actualSmallRoughRho (P false) N cap w z L d| := by
    unfold originalGapFibre
    exact Finset.abs_sum_le_sum_abs _ _
  have hnon : 0 ≤ ∑ d ∈ S,
      |actualSmallRoughRho (P false) N cap w z L d| := by
    apply Finset.sum_nonneg
    intro d _
    exact abs_nonneg _
  calc
    |a * originalGapFibre P N cap w z L gap| =
        a * |originalGapFibre P N cap w z L gap| := by
          rw [abs_mul, abs_of_nonneg ha0]
    _ ≤ a * ∑ d ∈ S, |actualSmallRoughRho (P false) N cap w z L d| :=
          mul_le_mul_of_nonneg_left htri ha0
    _ ≤ 1 * ∑ d ∈ S, |actualSmallRoughRho (P false) N cap w z L d| :=
          mul_le_mul_of_nonneg_right ha1 hnon
    _ = _ := by simp [S]

/-- Concrete two-sided sharp/smooth arithmetic payment for one original
policy. This requires the actual smoothing weights to stay in [0,1]. -/
theorem sharp_smooth_abs_le_actual_endpoint_invoices
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1)
    (hW : ∀ p, 0 ≤ W p ∧ W p ≤ 1) :
    |originalSharpLiteral P N D cap w z L -
      originalSmoothLiteral P N D cap w z L W| ≤
      lowerEndpointInvoice P N D cap w z L +
      upperEndpointInvoice P N D cap w z L := by
  have hlow : |weightedLowerBoundary P N D cap w z L W| ≤
      lowerEndpointInvoice P N D cap w z L := by
    classical
    unfold weightedLowerBoundary lowerEndpointInvoice
    calc
      |∑ p ∈ lowerEndpointPrimes N D,
          (1 - W p) * originalGapFibre P N cap w z L (N - p)| ≤
        ∑ p ∈ lowerEndpointPrimes N D,
          |(1 - W p) * originalGapFibre P N cap w z L (N - p)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have hw := hW p
        exact weighted_original_gap_abs_le_invoice
          P N cap w z L (N - p) (1 - W p)
          (by linarith) (by linarith)
  have hupp : |weightedUpperBoundary P N D cap w z L W| ≤
      upperEndpointInvoice P N D cap w z L := by
    classical
    unfold weightedUpperBoundary upperEndpointInvoice
    calc
      |∑ p ∈ upperEndpointPrimes N D,
          W p * originalGapFibre P N cap w z L (p - N)| ≤
        ∑ p ∈ upperEndpointPrimes N D,
          |W p * originalGapFibre P N cap w z L (p - N)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact weighted_original_gap_abs_le_invoice
          P N cap w z L (p - N) (W p) (hW p).1 (hW p).2
  rw [sharp_minus_smooth_eq_weighted_boundaries
    P N D cap w z L W hInterior]
  exact (abs_sub_le _ _).trans (add_le_add hlow hupp)

/-- The original sixth and eighth policies keep their distinct signed
rho coefficients, but share one fixed N,D and one endpoint profile W. -/
theorem original_sixth_eighth_sharp_smooth_abs_le_four_tau
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1)
    (hW : ∀ p, 0 ≤ W p ∧ W p ≤ 1) :
    |originalSharpLiteral (sixthPolicy n e q om (N : ℝ)) N D cap w z L -
      originalSmoothLiteral (sixthPolicy n e q om (N : ℝ)) N D cap w z L W| +
    |originalSharpLiteral (policy delta n e q om (N : ℝ)) N D cap w z L -
      originalSmoothLiteral (policy delta n e q om (N : ℝ)) N D cap w z L W| ≤
      4 * ∑ m ∈ Finset.Icc 1 D, (((m.divisors.card : ℕ) : ℝ)) := by
  have h6 := sharp_smooth_abs_le_actual_endpoint_invoices
    (sixthPolicy n e q om (N : ℝ)) N D cap w z L W hInterior hW
  have h8 := sharp_smooth_abs_le_actual_endpoint_invoices
    (policy delta n e q om (N : ℝ)) N D cap w z L W hInterior hW
  have l6 := lower_endpoint_invoice_le_divisor_sum
    (sixthPolicy n e q om (N : ℝ)) N D cap w z L
  have u6 := upper_endpoint_invoice_le_divisor_sum
    (sixthPolicy n e q om (N : ℝ)) N D cap w z L
  have l8 := lower_endpoint_invoice_le_divisor_sum
    (policy delta n e q om (N : ℝ)) N D cap w z L
  have u8 := upper_endpoint_invoice_le_divisor_sum
    (policy delta n e q om (N : ℝ)) N D cap w z L
  linarith

end
end ImbalancedChen.P4AOriginalFull87WeightedSharpSmooth
