import ImbalancedChen.P4AOriginalFull87UpperPrimeActualSupport
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A strictly finite, arithmetic boundary split of the ORIGINAL upper-half
stopped prime fibre. For a real fifthExclusive event, the original
fifth-power Rosser filter becomes redundant on X*p < N-P, or in
particular when 2*X*p <= N. The other part is the EXACT original
signed term, supported only in N < 2*X*p.

No prime distribution, smooth PP, new physical rho, or asymptotic
bound is asserted. The actual source List and occurrence multiplicities
are preserved; this is not a licence to delete the residual boundary.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperPrimeShortBoundary
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedGlobalPrimeLedger (upperPrimeFibreTerm)
open P4AOriginalFull87PlusBetaPowerFilter (largeFifthRosserIndices)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)

/-- Pure integer algebra: the fifth-power gate is forced by a
short product X*p<q, the exact COMPLETE modulus q=a*p*b5, and the
positivity of the real fifth history product b5. No a is rounded. -/
private theorem short_product_forces_fifth_power
    (X N P a p : ℕ) (pre : List ℕ)
    (hpre : 0 < pre.prod)
    (hfull : a * (p :: pre).prod = N - P)
    (hshort : X * p < N - P) :
    X ^ 5 < a ^ 5 * pre.prod ^ 6 := by
  have hmul : X * p < (a * pre.prod) * p := by
    calc
      X * p < N - P := hshort
      _ = a * (p :: pre).prod := hfull.symm
      _ = (a * pre.prod) * p := by
        simp [List.prod_cons, mul_assoc, mul_comm, mul_left_comm]
  have hbase : X < a * pre.prod := by
    by_contra hn
    have hle : a * pre.prod ≤ X := Nat.le_of_not_gt hn
    have hm := Nat.mul_le_mul_right p hle
    omega
  have hpow : X ^ 5 < (a * pre.prod) ^ 5 :=
    Nat.pow_lt_pow_left hbase (by norm_num)
  have hgrow : pre.prod ^ 5 ≤ pre.prod ^ 6 :=
    Nat.pow_le_pow_right hpre (by norm_num)
  calc
    X ^ 5 < (a * pre.prod) ^ 5 := hpow
    _ = a ^ 5 * pre.prod ^ 5 := by rw [mul_pow]
    _ ≤ a ^ 5 * pre.prod ^ 6 := Nat.mul_le_mul_left _ hgrow

/-- Every actual rough-prime occurrence is positive. We reason on
the ORIGINAL List, including duplicate positions if any, rather than
turning its product into a set. -/
private theorem actual_rough_list_product_pos
    (N cap : ℕ) (w z : ℝ) (xs : List ℕ)
    (hrough : ∀ r ∈ xs, r ∈ roughPrimeUniverse N cap w z) :
    0 < xs.prod := by
  induction xs with
  | nil => simp
  | cons r rs ih =>
      have hrmem : r ∈ roughPrimeUniverse N cap w z :=
        hrough r (by simp)
      have hr : 0 < r := (mem_roughPrimeUniverse_prime hrmem).pos
      have htail : ∀ t ∈ rs, t ∈ roughPrimeUniverse N cap w z := by
        intro t ht
        exact hrough t (by simp [ht])
      simpa only [List.prod_cons] using Nat.mul_pos hr (ih htail)

/-- On an ACTUAL receiver-generated fifth event and a real sixth
occurrence, a short full modulus eliminates the fifth-power Rosser
mask exactly, but NOT the underlying Rosser support membership.
The strict short-product test and exact a*b6=N-P remain present. -/
theorem actual_short_product_large_iff_small
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (a : ℕ)
    (hfull : a * (p :: fifth.selectedAfter).prod = N - P)
    (hshort : X * p < N - P) :
    a ∈ largeFifthRosserIndices N cap w X fifth.selectedAfter ↔
      a ∈ actualSmallRosserSupport N cap w := by
  have hjoined :
      fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
        roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough
        delta n e q om N cap w z L X (receiverTest N)
        state hstate (.fifthExclusive fifth) hfifth)
  have hpre : ∀ r ∈ fifth.selectedAfter,
      r ∈ roughPrimeUniverse N cap w z := by
    intro r hr
    have hrev : r ∈ fifth.selectedAfter.reverse := by simpa using hr
    exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
  have hprePos : 0 < fifth.selectedAfter.prod :=
    actual_rough_list_product_pos N cap w z fifth.selectedAfter hpre
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).1
  · intro ha
    exact Finset.mem_filter.mpr
      ⟨ha, short_product_forces_fifth_power X N P a p fifth.selectedAfter
        hprePos hfull hshort⟩

/-- Safe term has the SAME original beta, exact quotient, and strict
high-q/upper-half boundaries, but only the original small-Rosser
membership. Its extra arithmetic guard is explicitly X*p < N-P. -/
def upperPrimeShortNoPowerTerm
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ) : ℝ :=
  if 2 * P < N ∧ X < N - P ∧ X * p < N - P ∧
      (N - P) / (p :: pre).prod ∈ actualSmallRosserSupport N cap w ∧
      ((N - P) / (p :: pre).prod) * (p :: pre).prod = N - P
  then actualSmallRosserPlus N cap w L
      ((N - P) / (p :: pre).prod)
  else 0

/-- The other part is NOT smoothed, rounded, dropped or newly signed:
it remains the exact original prime-fibre term outside the short
product guard. This is an unpaid arithmetic boundary ledger. -/
def upperPrimeLongBoundaryTerm
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ) : ℝ :=
  if X * p < N - P then 0
  else upperPrimeFibreTerm N cap w L X P pre p

/-- Exact once-only decomposition on ONE original actual occurrence.
There is no cap monotonicity or signed saving inference. -/
theorem actual_prime_fibre_short_boundary
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
    upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p =
      upperPrimeShortNoPowerTerm N cap w L X P fifth.selectedAfter p +
        upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p := by
  by_cases hs : X * p < N - P
  · by_cases hfull :
        ((N - P) / (p :: fifth.selectedAfter).prod) *
          (p :: fifth.selectedAfter).prod = N - P
    · have hiff := actual_short_product_large_iff_small
        delta n e q om N cap w z L X P state hstate
        fifth hfifth p hp
        ((N - P) / (p :: fifth.selectedAfter).prod) hfull hs
      simp [upperPrimeFibreTerm, upperPrimeShortNoPowerTerm,
        upperPrimeLongBoundaryTerm, hs, hfull, hiff]
    · simp [upperPrimeFibreTerm, upperPrimeShortNoPowerTerm,
        upperPrimeLongBoundaryTerm, hs, hfull]
  · simp [upperPrimeShortNoPowerTerm, upperPrimeLongBoundaryTerm, hs]

/-- Any NONZERO leftover arithmetic boundary requires a large sixth
candidate in the exact integer sense N < 2*X*p.
This uses strict 2P<N, not any geometric null-set assumption. -/
theorem long_boundary_nonzero_implies_large_Xp
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm N cap w L X P pre p ≠ 0) :
    N < 2 * (X * p) := by
  by_cases hs : X * p < N - P
  · simp [upperPrimeLongBoundaryTerm, hs] at h
  · have hhalf : 2 * P < N := by
      by_contra hnot
      have hz : upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
        simp [upperPrimeLongBoundaryTerm, upperPrimeFibreTerm, hs, hnot]
      exact h hz
    have hle : N - P ≤ X * p := Nat.le_of_not_gt hs
    omega

theorem long_boundary_zero_of_two_Xp_le
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hsize : 2 * (X * p) ≤ N) :
    upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
  by_contra hnon
  have hlarge := long_boundary_nonzero_implies_large_Xp
    N cap w L X P pre p hnon
  omega

/-- Finite ordered-sum splitting never deduplicates the List. -/
private theorem ordered_sum_split {α : Type*}
    (xs : List α) (f g h : α → ℝ)
    (hpoint : ∀ x ∈ xs, f x = g x + h x) :
    (xs.map f).sum = (xs.map g).sum + (xs.map h).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx : f x = g x + h x := hpoint x (by simp)
      have htail : ∀ y ∈ rest, f y = g y + h y := by
        intro y hy
        exact hpoint y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      rw [hx, ih htail]
      ring

/-- Real original fifth signed mass and all ordered sixth occurrences,
split ONCE into a short-product term without the fifth-power mask
and an explicit unpaid arithmetic boundary. -/
theorem actual_fifth_prime_boundary_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum =
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeShortNoPowerTerm N cap w L X P fifth.selectedAfter p)).sum +
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p)).sum := by
  apply ordered_sum_split
  intro p hp
  rw [actual_prime_fibre_short_boundary
    delta n e q om N cap w z L X P state hstate fifth hfifth p hp]
  ring

/-- An actual fifth event whose ordered sixth candidates all satisfy
2*X*p<=N has ZERO arithmetic boundary, so its fifth-power mask is
redundant. This conditional is NOT claimed for every upper producer. -/
theorem actual_fifth_prime_no_boundary_of_size
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hsize : ∀ p ∈ fifth.remainingAfter, 2 * (X * p) ≤ N) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum =
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeShortNoPowerTerm N cap w L X P fifth.selectedAfter p)).sum := by
  have hzero :
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p)).sum =
      0 := by
    have hmap :
        fifth.remainingAfter.map (fun p =>
          signedTreeCoefficient true fifth.massAfter *
            upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p) =
        fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro p hp
      simp [long_boundary_zero_of_two_Xp_le
        N cap w L X P fifth.selectedAfter p (hsize p hp)]
    rw [hmap]
    simp
  rw [actual_fifth_prime_boundary_invoice
    delta n e q om N cap w z L X P state hstate fifth hfifth, hzero]
  simp

end
end ImbalancedChen.P4AOriginalFull87UpperPrimeShortBoundary
