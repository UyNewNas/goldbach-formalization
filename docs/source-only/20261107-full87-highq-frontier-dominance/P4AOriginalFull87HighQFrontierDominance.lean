import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import ImbalancedChen.FirstExitFrontierInvariants
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no PP or reserve payment.

A physical full-q cutoff can already be exceeded at the ACTUAL
rank-eight selected prefix, before any ordinary continuation chooses
its remaining rough primes. In that case every subsequent full modulus
is above the cutoff, including its original nonzero small Rosser factor.
Consequently the high-q ordinary OLD-minus-NEW saving is exactly the
UNTRUNCATED saving on that occurrence. This is a potentially serious
obstruction to treating all high-q mass as a negligible tail; no claim
that every original87 state satisfies the strict prefix threshold is made.
-/

namespace ImbalancedChen.P4AOriginalFull87HighQFrontierDominance
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest full87_high_q_gain_eq_owned_sources)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalLicensedSixthSignedLedger (physical)

/-- The unchanged original sign-sensitive small beta sees the same
physical terminal if its complete modulus already exceeds X. -/
private theorem attached_highQ_eq_of_large_prefix
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool)
    (hlarge : ∀ a ∈ actualSmallRosserSupport N cap w, X < a * pre.prod) :
    attachedLeafTest N cap 1 w L (highQTest X F) positive pre =
      attachedLeafTest N cap 1 w L F positive pre := by
  unfold attachedLeafTest
  apply Finset.sum_congr rfl
  intro a ha
  simp [highQTest, hlarge a ha]

/-- Once the current selected prefix exceeds X after multiplication
by every actual small divisor, descending the same original finite
remaining-prime carrier cannot return to the low-q region.
No monotonicity of a SIGNED saving is used. -/
theorem signedTest_highQ_eq_of_large_prefix
    (R : Bool → List ℕ → Bool) (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (F : ℕ → ℝ)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ) :
    (∀ a ∈ actualSmallRosserSupport N cap w, X < a * pre.prod) →
    (∀ p ∈ remaining, 0 < p) →
    signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining =
    signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L F)
      pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      intro hlarge _
      simp only [signedTest]
      rw [attached_highQ_eq_of_large_prefix N cap w L X F pre positive hlarge]
  | cons p ps ih =>
      intro hlarge hpositive
      have hp : 1 ≤ p := hpositive p (by simp)
      have htail : ∀ r ∈ ps, 0 < r := by
        intro r hr
        exact hpositive r (by simp [hr])
      have hprefix : pre.prod ≤ (p :: pre).prod := by
        simpa only [List.prod_cons, one_mul] using
          (Nat.mul_le_mul_right pre.prod hp)
      have htake : ∀ a ∈ actualSmallRosserSupport N cap w,
          X < a * (p :: pre).prod := by
        intro a ha
        exact (hlarge a ha).trans_le (Nat.mul_le_mul_left a hprefix)
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [signedTest, if_pos hr]
        rw [ih pre positive mass hlarge htail,
          ih (p :: pre) (!positive) (mass * (1 : ℝ)) htake htail]
      · simp only [signedTest, if_neg hr, add_zero]
        exact ih pre positive mass hlarge htail

/-- A true owned87 rank-eight state, with no synthetic prime sequence,
has only positive actual rough primes in its remaining carrier. -/
private theorem owned_state_remaining_positive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    ∀ p ∈ s.remaining, 0 < p := by
  have hfront : s ∈ frontier n e q om N cap w z := by
    rw [states_eq_owner_filter] at hs
    exact (List.mem_filter.mp hs).1
  have hsub : s.selectedPrefix.reverse ++ s.remaining <+
      roughPrimeUniverse N cap w z :=
    firstExitDepthFrontier_selected_remaining_sublist
      8 (sixthPolicy n e q om (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
      [] (roughPrimeUniverse N cap w z) true 1 s hfront
  intro p hp
  have hc : p ∈ roughPrimeUniverse N cap w z := by
    apply hsub.subset
    simp [hp]
  exact (mem_roughPrimeUniverse_prime hc).pos

/-- The threshold uses the ACTUAL original rank-eight selected product;
all actual small divisors are nonzero divisors of the genuine presieve
product. No outside positivity or hypothetical state source is assumed. -/
private theorem owned_state_large_small_products
    (N cap X : ℕ) (w : ℝ) (s : FirstExitDepthState ℕ)
    (hprefix : X < s.selectedPrefix.prod) :
    ∀ a ∈ actualSmallRosserSupport N cap w,
      X < a * s.selectedPrefix.prod := by
  intro a ha
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have haone : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr hsmall.1
  exact hprefix.trans_le (by
    simpa only [one_mul] using
      (Nat.mul_le_mul_right s.selectedPrefix.prod haone))

/-- A genuinely owned rank-eight high-prefix occurrence pays the FULL
old-minus-new signed ordinary saving to the high-q tail.
Both continuations keep the SAME parent, cap, beta and remaining list.
This statement is local, conditional on a checkable strict product gate. -/
theorem owned_highQ_saving_eq_full_of_large_prefix
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hprefix : X < s.selectedPrefix.prod) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s =
      ordinarySaving n e q om N cap w L F c s := by
  have hlarge := owned_state_large_small_products N cap X w s hprefix
  have hpositive :=
    owned_state_remaining_positive delta n e q om N cap w z c s hs
  have hold := signedTest_highQ_eq_of_large_prefix
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
    N cap w L X F s.selectedPrefix s.remaining s.positive s.mass
    hlarge hpositive
  have hnew := signedTest_highQ_eq_of_large_prefix
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
    N cap w L X F s.selectedPrefix s.remaining s.positive s.mass
    hlarge hpositive
  exact congrArg₂ (fun u v : ℝ => u - v) hold hnew

/-- If all ACTUAL owner occurrences cross the same physical threshold,
the entire original87 change occurs in the high-q tail.
The antecedent is NOT asserted by the manuscript/archive and must not
be confused with a PP level or an asymptotic estimate. -/
theorem full87_highQ_gain_eq_full_of_all_owned_prefix_large
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (hlarge : ∀ (c : Cell) (s : FirstExitDepthState ℕ),
      s ∈ states delta n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c → X < s.selectedPrefix.prod) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (highQTest X F) -
      physical (policy delta n e q om (N : ℝ)) N cap w z L
        (highQTest X F) =
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L F -
      physical (policy delta n e q om (N : ℝ)) N cap w z L F := by
  rw [full87_high_q_gain_eq_owned_sources,
    physical_saving_eq_owned_sources]
  apply Finset.sum_congr rfl
  intro c _
  unfold ownedSource
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  exact owned_highQ_saving_eq_full_of_large_prefix
    delta n e q om N cap w z L X F c s hs (hlarge c s hs)

/-- An elementary LIST partition, not a Finset conversion. Repeated
source occurrences survive in precisely their original multiplicity. -/
private theorem list_sum_partition_bool {α : Type*}
    (xs : List α) (select : α → Bool) (f : α → ℝ) :
    (xs.map f).sum =
      ((xs.filter select).map f).sum +
      ((xs.filter (fun a => ! select a)).map f).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      cases h : select a <;>
        simp [h, ih, add_assoc, add_left_comm, add_comm]

/-- This is unconditional on the archive's eight-prime products.
The high-q change of the ACTUAL original87 parent splits into two
disjoint occurrence lists: (1) strict large-prefix occurrences, where
high-q equals the entire ordinary saving, and (2) remaining original
occurrences, where the genuine high-q terminal mask is still required.

The second list includes equality selectedPrefix.prod = X.
No occurrence is counted twice or dropped, and no new policy is used. -/
theorem full87_highQ_gain_split_at_actual_frontier
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (highQTest X F) -
      physical (policy delta n e q om (N : ℝ)) N cap w z L
        (highQTest X F) =
      (∑ c : Cell,
        ((((states delta n e q om N cap w z
          (fun _ : ℕ => (1 : ℝ)) c).filter
          (fun s => decide (X < s.selectedPrefix.prod))).map
          (ordinarySaving n e q om N cap w L F c)).sum)) +
      (∑ c : Cell,
        ((((states delta n e q om N cap w z
          (fun _ : ℕ => (1 : ℝ)) c).filter
          (fun s => !decide (X < s.selectedPrefix.prod))).map
          (ordinarySaving n e q om N cap w L (highQTest X F) c)).sum)) := by
  rw [full87_high_q_gain_eq_owned_sources]
  have hcell (c : Cell) :
      ownedSource delta n e q om N cap w z L (highQTest X F) c =
        (((states delta n e q om N cap w z
            (fun _ : ℕ => (1 : ℝ)) c).filter
            (fun s => decide (X < s.selectedPrefix.prod))).map
            (ordinarySaving n e q om N cap w L F c)).sum +
        (((states delta n e q om N cap w z
            (fun _ : ℕ => (1 : ℝ)) c).filter
            (fun s => !decide (X < s.selectedPrefix.prod))).map
            (ordinarySaving n e q om N cap w L (highQTest X F) c)).sum := by
    let xs := states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c
    let big : FirstExitDepthState ℕ → Bool :=
      fun s => decide (X < s.selectedPrefix.prod)
    let f := ordinarySaving n e q om N cap w L (highQTest X F) c
    have hpartition := list_sum_partition_bool xs big f
    have hlarge :
        ((xs.filter big).map f).sum =
        ((xs.filter big).map
          (ordinarySaving n e q om N cap w L F c)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro s hs
      obtain ⟨hs0, hbig⟩ := List.mem_filter.mp hs
      have hstrict : X < s.selectedPrefix.prod := by
        exact of_decide_eq_true hbig
      exact owned_highQ_saving_eq_full_of_large_prefix
        delta n e q om N cap w z L X F c s hs0 hstrict
    rw [hlarge] at hpartition
    simpa only [ownedSource, xs, big, f] using hpartition
  calc
    (∑ c : Cell, ownedSource delta n e q om N cap w z L
      (highQTest X F) c) =
      ∑ c : Cell,
        ((((states delta n e q om N cap w z
          (fun _ : ℕ => (1 : ℝ)) c).filter
          (fun s => decide (X < s.selectedPrefix.prod))).map
          (ordinarySaving n e q om N cap w L F c)).sum +
        (((states delta n e q om N cap w z
          (fun _ : ℕ => (1 : ℝ)) c).filter
          (fun s => !decide (X < s.selectedPrefix.prod))).map
          (ordinarySaving n e q om N cap w L (highQTest X F) c)).sum := by
            apply Finset.sum_congr rfl
            intro c _
            exact hcell c
    _ = _ := Finset.sum_add_distrib

end
end ImbalancedChen.P4AOriginalFull87HighQFrontierDominance
