import ImbalancedChen.P4AOriginalFull87ActualRhoDivisorTau
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: exact arithmetic endpoint payment for the manuscript's sharp
original-prime smoothing. The test coefficient is the *same* sign-attached
actualSmallRoughRho and the displayed set is its literal full physical
modulus support, fixed before inspecting primes. This packet proves the
finite two-sided endpoint divisor-sum inequality. It does NOT assert the
analytic summatory-divisor estimate, the smooth PP instance, a power
support bound, a saving relative to H_N, or a reserve payment.

Both half-open gaps exclude p = N arithmetically, even when N is prime.
There is one prime at most for each signed gap, not an occurrence-free
replacement of the original source. Prime counts here are inclusive in
their upper endpoints; the *strict* gap is handled separately.
-/

namespace ImbalancedChen.P4AOriginalFull87SameRhoEndpointDivisor
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87ActualRhoDivisorTau
open P4AOriginalFull87LicensedSixthPolicy

/-- Lower endpoint of the same original prime prefix, excluding p=N. -/
def lowerEndpointPrimes (N D : ℕ) : Finset ℕ :=
  (chenPrimePrefix N).filter (fun p => p < N ∧ N - p ≤ D)

/-- Upper smoothing extension, with fixed coefficient parameters at N. -/
def upperEndpointPrimes (N D : ℕ) : Finset ℕ :=
  (chenPrimePrefix (N + D)).filter (fun p => N < p ∧ p - N ≤ D)

/-- Same-rho lower endpoint absolute divisor cost. -/
def lowerEndpointInvoice (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ p ∈ lowerEndpointPrimes N D,
    ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
      (fun d => d ∣ N - p),
      |actualSmallRoughRho (P false) N cap w z L d|

/-- Same-rho upper endpoint cost; no new coefficient is introduced. -/
def upperEndpointInvoice (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ p ∈ upperEndpointPrimes N D,
    ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
      (fun d => d ∣ p - N),
      |actualSmallRoughRho (P false) N cap w z L d|

/-- The real signed boundary term: both endpoint fibres share the
identical coefficient, modulus carrier, centre and frozen parameters. -/
def signedEndpointBoundary (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) : ℝ :=
  (∑ p ∈ lowerEndpointPrimes N D,
    ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
      (fun d => d ∣ N - p),
      actualSmallRoughRho (P false) N cap w z L d) +
  (∑ p ∈ upperEndpointPrimes N D,
    ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
      (fun d => d ∣ p - N),
      actualSmallRoughRho (P false) N cap w z L d)

/-- Genuine divisor fibre, including the zero-coefficient entries, is
bounded by tau of a nonzero gap. The original rho-one theorem provides
the coefficient size; no independent beta-majorant is assumed. -/
private theorem gap_fibre_le_tau
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (gap : ℕ) (hgap : gap ≠ 0) :
    (∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
      (fun d => d ∣ gap),
      |actualSmallRoughRho (P false) N cap w z L d|) ≤
      ((gap.divisors.card : ℕ) : ℝ) := by
  classical
  let S : Finset ℕ :=
    (actualSmallRoughModuli (P false) N cap w z).filter (fun d => d ∣ gap)
  have hsub : S ⊆ gap.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hgap⟩
  change (∑ d ∈ S, |actualSmallRoughRho (P false) N cap w z L d|) ≤
    ((gap.divisors.card : ℕ) : ℝ)
  calc
    (∑ d ∈ S, |actualSmallRoughRho (P false) N cap w z L d|) ≤
        ∑ d ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d _
          exact actualSmallRoughRho_abs_le_one (P false) N cap w z L d
    _ = (S.card : ℝ) := by simp
    _ ≤ ((gap.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub

/-- Every lower endpoint gap appears at most once and lies in [1,D].
The bound is uniform in the actual full modulus carrier. -/
theorem lower_endpoint_invoice_le_divisor_sum
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ) :
    lowerEndpointInvoice P N D cap w z L ≤
      ∑ n ∈ Finset.Icc 1 D, (((n.divisors.card : ℕ) : ℝ)) := by
  classical
  have himage :
      (lowerEndpointPrimes N D).image (fun p => N - p) ⊆ Finset.Icc 1 D := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨_, hpLt, hpD⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨by omega, hpD⟩
  calc
    lowerEndpointInvoice P N D cap w z L ≤
        ∑ p ∈ lowerEndpointPrimes N D,
          (((N - p).divisors.card : ℕ) : ℝ) := by
          unfold lowerEndpointInvoice
          apply Finset.sum_le_sum
          intro p hp
          have hpLt : p < N := (Finset.mem_filter.mp hp).2.1
          exact gap_fibre_le_tau P N cap w z L (N - p) (by omega)
    _ = ∑ v ∈ (lowerEndpointPrimes N D).image (fun p => N - p),
          (((v.divisors.card : ℕ) : ℝ)) := by
          symm
          apply Finset.sum_image
          intro p hp q hq heq
          have hpLt : p < N := (Finset.mem_filter.mp hp).2.1
          have hqLt : q < N := (Finset.mem_filter.mp hq).2.1
          omega
    _ ≤ ∑ n ∈ Finset.Icc 1 D,
          (((n.divisors.card : ℕ) : ℝ)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg himage
            (by intro n _ _; exact Nat.cast_nonneg _)

/-- The upper endpoint also has an injective positive-gap map. In particular
the p=N zero-gap endpoint is NOT charged to tau(0). -/
theorem upper_endpoint_invoice_le_divisor_sum
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ) :
    upperEndpointInvoice P N D cap w z L ≤
      ∑ n ∈ Finset.Icc 1 D, (((n.divisors.card : ℕ) : ℝ)) := by
  classical
  have himage :
      (upperEndpointPrimes N D).image (fun p => p - N) ⊆ Finset.Icc 1 D := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨_, hpGt, hpD⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨by omega, hpD⟩
  calc
    upperEndpointInvoice P N D cap w z L ≤
        ∑ p ∈ upperEndpointPrimes N D,
          (((p - N).divisors.card : ℕ) : ℝ) := by
          unfold upperEndpointInvoice
          apply Finset.sum_le_sum
          intro p hp
          have hpGt : N < p := (Finset.mem_filter.mp hp).2.1
          exact gap_fibre_le_tau P N cap w z L (p - N) (by omega)
    _ = ∑ v ∈ (upperEndpointPrimes N D).image (fun p => p - N),
          (((v.divisors.card : ℕ) : ℝ)) := by
          symm
          apply Finset.sum_image
          intro p hp q hq heq
          have hpGt : N < p := (Finset.mem_filter.mp hp).2.1
          have hqGt : N < q := (Finset.mem_filter.mp hq).2.1
          omega
    _ ≤ ∑ n ∈ Finset.Icc 1 D,
          (((n.divisors.card : ℕ) : ℝ)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg himage
            (by intro n _ _; exact Nat.cast_nonneg _)

/-- Triangle inequality applies to the exact original signed boundary.
No replacement of its signed rho by a unrelated positive sieve. -/
theorem signed_endpoint_boundary_abs_le_invoices
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ) :
    |signedEndpointBoundary P N D cap w z L| ≤
      lowerEndpointInvoice P N D cap w z L +
      upperEndpointInvoice P N D cap w z L := by
  classical
  have hlow :
      |∑ p ∈ lowerEndpointPrimes N D,
        ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
          (fun d => d ∣ N - p),
          actualSmallRoughRho (P false) N cap w z L d| ≤
      lowerEndpointInvoice P N D cap w z L := by
    unfold lowerEndpointInvoice
    calc
      _ ≤ ∑ p ∈ lowerEndpointPrimes N D,
          |∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
            (fun d => d ∣ N - p),
            actualSmallRoughRho (P false) N cap w z L d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        exact Finset.abs_sum_le_sum_abs _ _
  have hupp :
      |∑ p ∈ upperEndpointPrimes N D,
        ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
          (fun d => d ∣ p - N),
          actualSmallRoughRho (P false) N cap w z L d| ≤
      upperEndpointInvoice P N D cap w z L := by
    unfold upperEndpointInvoice
    calc
      _ ≤ ∑ p ∈ upperEndpointPrimes N D,
          |∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
            (fun d => d ∣ p - N),
            actualSmallRoughRho (P false) N cap w z L d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        exact Finset.abs_sum_le_sum_abs _ _
  unfold signedEndpointBoundary
  exact (abs_add_le _ _).trans (add_le_add hlow hupp)

/-- One genuine policy: the actual signed endpoint, both sides combined,
costs at most two copies of the positive-divisor sum. -/
theorem signed_endpoint_boundary_abs_le_two_divisor_sums
    (P : Bool → List ℕ → Bool) (N D cap : ℕ) (w z L : ℝ) :
    |signedEndpointBoundary P N D cap w z L| ≤
      2 * ∑ n ∈ Finset.Icc 1 D, (((n.divisors.card : ℕ) : ℝ)) := by
  have h0 := signed_endpoint_boundary_abs_le_invoices P N D cap w z L
  have h1 := lower_endpoint_invoice_le_divisor_sum P N D cap w z L
  have h2 := upper_endpoint_invoice_le_divisor_sum P N D cap w z L
  linarith

/-- Apply the two-sided boundary estimate to the *actual sixth and eighth*
strategies at the same physical N, cap, w,z,L and smoothing width D.
No claims about external PP or density reserves are packaged here. -/
theorem original_sixth_eighth_signed_endpoint_le_four_divisor_sums
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) :
    |signedEndpointBoundary (sixthPolicy n e q om (N : ℝ))
        N D cap w z L| +
    |signedEndpointBoundary (policy delta n e q om (N : ℝ))
        N D cap w z L| ≤
      4 * ∑ m ∈ Finset.Icc 1 D, (((m.divisors.card : ℕ) : ℝ)) := by
  have h6 := signed_endpoint_boundary_abs_le_two_divisor_sums
    (sixthPolicy n e q om (N : ℝ)) N D cap w z L
  have h8 := signed_endpoint_boundary_abs_le_two_divisor_sums
    (policy delta n e q om (N : ℝ)) N D cap w z L
  linarith

end
end ImbalancedChen.P4AOriginalFull87SameRhoEndpointDivisor
