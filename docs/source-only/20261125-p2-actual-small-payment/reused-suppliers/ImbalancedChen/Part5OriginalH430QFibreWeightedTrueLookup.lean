import ImbalancedChen.Part5OriginalH430OriginalU34AnalyticLookup

/-!
P5.6 / h34 — retain genuine q-fibre weights in the true original
U3/U4 H430 lookup. Arbitrary signed weights belong to EACH (p,q,tag).
A true H430 table coefficient depends on p, whereas the selected
arithmetic or Theta weight may depend on q. Even at identical physical
slots the two original U4 tags must not be merged.

Finite source identities only: no count-to-integral estimate, owner
or full/selected/inherited filter, historical payment or new analytic input.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430QFibreWeightedTrueLookup
noncomputable section

open Set
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430UpperOverlapPhysicalSlot
open Part5OriginalH430TrueUpperU34Phase
open Part5OriginalH430OriginalU34AnalyticLookup

/-- Sum original receiver q-dependent weights in one selected p-fibre. -/
def originalQFibreWeight (N : ℕ) (w : TaggedPair → ℝ) (p : ℕ) : ℝ :=
  ∑ q ∈ originalReceiver N p, w ⟨p, q⟩

/-- Literal upper H430 lookup, preserving independent signed tag weights. -/
def originalWeightedTrueH430Lookup
    (N : ℕ) (w3 w4 : TaggedPair → ℝ) : ℝ :=
  ∑ z ∈ originalTagged N,
    Sum.elim
      (fun x => w3 x * U3H430Coefficient (primeCoordinate N x.1))
      (fun x => w4 x * U4H430Coefficient (primeCoordinate N x.1)) z

/-- Finite sigma disintegration; no positivity or event owner is needed. -/
private theorem sigma_weighted_root
    (ps : Finset ℕ) (fib : ℕ → Finset ℕ)
    (w : TaggedPair → ℝ) (c : ℕ → ℝ) :
    (∑ x ∈ ps.sigma fib, w x * c x.1) =
      ∑ p ∈ ps, c p * (∑ q ∈ fib p, w ⟨p, q⟩) := by
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  change (∑ q ∈ fib p, w ⟨p, q⟩ * c p) =
    c p * (∑ q ∈ fib p, w ⟨p, q⟩)
  rw [← Finset.sum_mul]
  ring

/-- Signed original arithmetic source, disintegrated by its genuine
selected prime p while keeping distinct (q,tag) occurrences. -/
theorem original_signed_q_source_by_prime_fibres
    (N : ℕ) (hN : 1 ≤ N) (w3 w4 : TaggedPair → ℝ) :
    (∑ z ∈ originalTagged N, Sum.elim w3 w4 z) =
      (∑ p ∈ upperExclusiveBand N, originalQFibreWeight N w3 p) +
      ∑ p ∈ originalBand N .U4,
        (originalQFibreWeight N w3 p + originalQFibreWeight N w4 p) := by
  have hsplit :=
    original_tag_dependent_signed_overlap N hN w3 w4
  have hleft :
      (∑ x ∈ upperExclusivePairs N, w3 x) =
        ∑ p ∈ upperExclusiveBand N, originalQFibreWeight N w3 p := by
    simp only [upperExclusivePairs, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have hright :
      (∑ x ∈ originalPairs N .U4, (w3 x + w4 x)) =
        ∑ p ∈ originalBand N .U4,
          (originalQFibreWeight N w3 p + originalQFibreWeight N w4 p) := by
    simp only [originalPairs, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [originalQFibreWeight, Finset.sum_add_distrib]
  calc
    (∑ z ∈ originalTagged N, Sum.elim w3 w4 z) =
        (∑ x ∈ upperExclusivePairs N, w3 x) +
          ∑ x ∈ originalPairs N .U4, (w3 x + w4 x) := hsplit
    _ = _ := by rw [hleft, hright]

/-- Each original U4 p has equal actual U3/U4 H430 lookup even if
its q-fibre is empty. The two independently signed q-fibre masses
then multiply ONE common coefficient without cancelling tag counts. -/
theorem original_weighted_true_H430_by_q_fibres
    (N : ℕ) (hN : 2 ≤ N) (w3 w4 : TaggedPair → ℝ) :
    originalWeightedTrueH430Lookup N w3 w4 =
      (∑ p ∈ upperExclusiveBand N,
        U3H430Coefficient (primeCoordinate N p) *
          originalQFibreWeight N w3 p) +
      ∑ p ∈ originalBand N .U4,
        U4H430Coefficient (primeCoordinate N p) *
          (originalQFibreWeight N w3 p +
            originalQFibreWeight N w4 p) := by
  have hleft :
      (∑ x ∈ upperExclusivePairs N,
        w3 x * U3H430Coefficient (primeCoordinate N x.1)) =
        ∑ p ∈ upperExclusiveBand N,
          U3H430Coefficient (primeCoordinate N p) *
            originalQFibreWeight N w3 p := by
    simpa only [upperExclusivePairs, originalQFibreWeight] using
      (sigma_weighted_root (upperExclusiveBand N)
        (originalReceiver N) w3
        (fun p => U3H430Coefficient (primeCoordinate N p)))
  have hright :
      (∑ x ∈ originalPairs N .U4,
        (w3 x * U3H430Coefficient (primeCoordinate N x.1) +
          w4 x * U4H430Coefficient (primeCoordinate N x.1))) =
        ∑ p ∈ originalBand N .U4,
          U4H430Coefficient (primeCoordinate N p) *
            (originalQFibreWeight N w3 p +
              originalQFibreWeight N w4 p) := by
    simp only [originalPairs, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    have hband : primeCoordinate N p ∈ Ico a (59 / 250 : ℝ) :=
      primeCoordinate_mem hN (by simpa only [originalBand] using hp)
    have heq := U3_eq_main_on_U4 hband
    change
      (∑ q ∈ originalReceiver N p,
        (w3 ⟨p, q⟩ * U3H430Coefficient (primeCoordinate N p) +
          w4 ⟨p, q⟩ * U4H430Coefficient (primeCoordinate N p))) =
        U4H430Coefficient (primeCoordinate N p) *
          (originalQFibreWeight N w3 p +
            originalQFibreWeight N w4 p)
    rw [heq]
    calc
      (∑ q ∈ originalReceiver N p,
        (w3 ⟨p, q⟩ * U4H430Coefficient (primeCoordinate N p) +
          w4 ⟨p, q⟩ * U4H430Coefficient (primeCoordinate N p))) =
        ∑ q ∈ originalReceiver N p,
          (w3 ⟨p, q⟩ + w4 ⟨p, q⟩) *
            U4H430Coefficient (primeCoordinate N p) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
      _ = (originalQFibreWeight N w3 p +
            originalQFibreWeight N w4 p) *
              U4H430Coefficient (primeCoordinate N p) := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib]
          rfl
      _ = _ := by ring
  calc
    originalWeightedTrueH430Lookup N w3 w4 =
      (∑ x ∈ upperExclusivePairs N,
        w3 x * U3H430Coefficient (primeCoordinate N x.1)) +
      ∑ x ∈ originalPairs N .U4,
        (w3 x * U3H430Coefficient (primeCoordinate N x.1) +
          w4 x * U4H430Coefficient (primeCoordinate N x.1)) := by
      simpa only [originalWeightedTrueH430Lookup] using
        (original_tag_dependent_signed_overlap N (by omega)
          (fun x => w3 x * U3H430Coefficient (primeCoordinate N x.1))
          (fun x => w4 x * U4H430Coefficient (primeCoordinate N x.1)))
    _ = _ := by rw [hleft, hright]

/-- Original Chen negative quarter for genuinely q-dependent signed
root weights; an algebraic identity, not a signed historical payment. -/
theorem original_weighted_true_H430_signed_quarter
    (N : ℕ) (hN : 2 ≤ N) (w3 w4 : TaggedPair → ℝ) :
    -(1 / 4 : ℝ) * originalWeightedTrueH430Lookup N w3 w4 =
      -(1 / 4 : ℝ) *
        (∑ p ∈ upperExclusiveBand N,
          U3H430Coefficient (primeCoordinate N p) *
            originalQFibreWeight N w3 p) -
      (1 / 4 : ℝ) *
        (∑ p ∈ originalBand N .U4,
          U4H430Coefficient (primeCoordinate N p) *
            (originalQFibreWeight N w3 p +
              originalQFibreWeight N w4 p)) := by
  rw [original_weighted_true_H430_by_q_fibres N hN w3 w4]
  ring

/-- Original arithmetic selected-count cardinalities are q-fibre
multiplicities. These are not normalized Theta weights or H430 table values. -/
theorem original_U34_real_count_by_q_fibres
    (N : ℕ) (hN : 1 ≤ N) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      (∑ p ∈ upperExclusiveBand N,
        ((originalReceiver N p).card : ℝ)) +
      2 * (∑ p ∈ originalBand N .U4,
        ((originalReceiver N p).card : ℝ)) := by
  rw [original_U34_count_double_overlap N hN]
  simp [upperExclusivePairs, originalPairs, Finset.card_sigma, Nat.cast_sum]

end
end ImbalancedChen.Part5OriginalH430QFibreWeightedTrueLookup
