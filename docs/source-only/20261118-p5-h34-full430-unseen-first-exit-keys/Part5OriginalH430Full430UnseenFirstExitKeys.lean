import ImbalancedChen.Part5OriginalH430LiteralSecondEdgeFinCapacity
import ImbalancedChen.Part5OriginalH430ActualQUniqueExitLedger

/-!
P5.6 / h34 -- exact rejection-lane visibility test over the WHOLE
literal 430-generation request history, using the original q/tag
first-excluded event keys and the previous actual Fin edge test.

The genuine first-excluded signed history can exist even when no
generated resolved edge at any generation visibly contains its excluded
factor. These histories are not discarded, and no equality of physical
(Q,p,ell) labels is taken as an actual request owner.

This separates a strict edge-visible candidate lane from a necessary
non-edge/rejection lane. It does NOT construct that rejection owner,
assert that either lane is nonempty, or pay the original U3/U4 count.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / COMPLETE_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430Full430UnseenFirstExitKeys

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430LiteralSecondEdgeFinCapacity

/-- Actual first-excluded (Q,p,ell) events which are witnessed by
SOME literal resolved Fin occurrence carrying the ell edge in its
original generated path, at SOME genuine generation g < 430.
This is visibility, not historical owner identification. -/
def visibleActualQExitKeys
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) : Finset (ℝ × EventKey) :=
  (actualQExitKeys N n precision tau z0 lower).filter
    (fun k => ∃ g : Fin 430,
      ∃ l : Index N n root tau p g,
        l ∈ literalSecondEdgeFinPositions N n root tau p g k)

/-- Genuine first-excluded physical keys with NO such edge-visible
occurrence across ANY of the 430 generations for this actual root.
They still have their original receipts and rank-two signed histories. -/
def invisibleActualQExitKeys
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) : Finset (ℝ × EventKey) :=
  actualQExitKeys N n precision tau z0 lower \
    visibleActualQExitKeys N n precision root tau z0 p lower

theorem visible_key_has_literal_second_edge
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ visibleActualQExitKeys N n precision root tau z0 p lower) :
    ∃ g : Fin 430, ∃ l : Index N n root tau p g,
      l ∈ literalSecondEdgeFinPositions N n root tau p g k :=
  (Finset.mem_filter.mp hk).2

/-- All 430 true generation indices are checked, not just a single
chosen request level. An unseen key cannot be assigned to an edge
visible position on this root, even if its numeric key is known. -/
theorem invisible_key_no_literal_second_edge
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower)
    (g : Fin 430) (l : Index N n root tau p g) :
    l ∉ literalSecondEdgeFinPositions N n root tau p g k := by
  intro hl
  have hnot : k ∉ visibleActualQExitKeys N n precision root tau z0 p lower :=
    (Finset.mem_sdiff.mp hk).2
  apply hnot
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_sdiff.mp hk).1, ⟨g, l, hl⟩⟩

theorem visible_invisible_exit_keys_disjoint
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    Disjoint
      (visibleActualQExitKeys N n precision root tau z0 p lower)
      (invisibleActualQExitKeys N n precision root tau z0 p lower) := by
  apply Finset.disjoint_left.mpr
  intro k hv hi
  exact (Finset.mem_sdiff.mp hi).2 hv

/-- This is a partition of the ORIGINAL actual-Q first-excluded event
keys: invisible events are not removed from the physical source. -/
theorem actual_Q_exit_keys_full430_partition
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    actualQExitKeys N n precision tau z0 lower =
      visibleActualQExitKeys N n precision root tau z0 p lower ∪
        invisibleActualQExitKeys N n precision root tau z0 p lower := by
  classical
  ext k
  constructor
  · intro hk
    by_cases hv : k ∈ visibleActualQExitKeys N n precision root tau z0 p lower
    · exact Finset.mem_union.mpr (Or.inl hv)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hk, hv⟩))
  · intro hk
    rcases Finset.mem_union.mp hk with hv | hi
    · exact (Finset.mem_filter.mp hv).1
    · exact (Finset.mem_sdiff.mp hi).1

/-- ANY signed or unsigned weight over the actual physical event keys
partitions without double counting and without identifying q/tag
receipts with history positions. -/
theorem actual_Q_exit_keys_full430_weight_partition
    {M : Type*} [AddCommMonoid M]
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (w : (ℝ × EventKey) → M) :
    (∑ k ∈ actualQExitKeys N n precision tau z0 lower, w k) =
      (∑ k ∈ visibleActualQExitKeys N n precision root tau z0 p lower, w k) +
      (∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower, w k) := by
  rw [actual_Q_exit_keys_full430_partition]
  exact Finset.sum_union
    (visible_invisible_exit_keys_disjoint
      N n precision root tau z0 p lower)

/-- The real once-per-key signed first-excluded Euler histories are
still counted on the invisible side; no zero-charge inference. -/
theorem actual_Q_signed_exit_full430_visibility_split
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
      actualRankTwoSignedExit N cap lower k.1 k.2) =
      (∑ k ∈ visibleActualQExitKeys N n precision root tau z0 p lower,
        actualRankTwoSignedExit N cap lower k.1 k.2) +
      (∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
        actualRankTwoSignedExit N cap lower k.1 k.2) := by
  exact actual_Q_exit_keys_full430_weight_partition
    (M := ℝ) N n precision root tau z0 p lower
    (fun k => actualRankTwoSignedExit N cap lower k.1 k.2)

/-- An event with a different true physical root Q cannot become
visible in this root's 430 literal request levels. -/
theorem true_Q_mismatch_forces_invisible
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower)
    (hQ : rootQ N n root tau p ≠ k.1) :
    k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower := by
  apply Finset.mem_sdiff.mpr
  refine ⟨hk, ?_⟩
  intro hv
  obtain ⟨g, l, hl⟩ :=
    visible_key_has_literal_second_edge N n precision root tau z0 p lower k hv
  have he := literal_second_edge_fin_empty_of_Q_mismatch
    N n root tau p g k hQ
  simpa [he] using hl

/-- Physical p is equally mandatory; sharing the ell factor alone
does not create a usable generated root position. -/
theorem true_prime_mismatch_forces_invisible
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower)
    (hp : p ≠ k.2.1) :
    k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower := by
  apply Finset.mem_sdiff.mpr
  refine ⟨hk, ?_⟩
  intro hv
  obtain ⟨g, l, hl⟩ :=
    visible_key_has_literal_second_edge N n precision root tau z0 p lower k hv
  have he := literal_second_edge_fin_empty_of_prime_mismatch
    N n root tau p g k hp
  simpa [he] using hl

/-- Every invisible key is still backed by at least one ORIGINAL
q/tag first-excluded receipt (including its genuine physical Q). -/
theorem invisible_key_has_original_receipt
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower) :
    ∃ z, z ∈ actualQExitFibre N n precision tau z0 lower k := by
  exact actual_Q_key_has_original_receipt
    N n precision tau z0 lower k (Finset.mem_sdiff.mp hk).1

/-- Edge invisibility does NOT destroy the actual one-event physical
first-excluded history or its original signed remaining Euler product.
The same cap and actual-Q hypotheses as the old source are retained. -/
theorem invisible_key_has_actual_signed_first_exit
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (hzcap : z0 ≤ (cap : ℝ))
    (k : ℝ × EventKey)
    (hk : k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower) :
    ∃ event : FirstExitDepthState ℕ,
      actualRankTwoHistory N cap lower k.1 k.2 = [event] ∧
      actualRankTwoSignedExit N cap lower k.1 k.2 =
        -originalEventMass k.2 *
          (event.remaining.map
            (fun q : ℕ => 1 - (1 / ((q : ℝ) - 1)))).prod := by
  obtain ⟨event, hsingle, _, _, _, hsigned⟩ :=
    actual_Q_unique_key_has_signed_first_exit
      N n cap precision tau z0 lower hzcap k
      (Finset.mem_sdiff.mp hk).1
  exact ⟨event, hsingle, hsigned⟩

/-- NO total map from all genuine receipts of an invisible key into
the strict edge-visible original Fin positions can satisfy the
literal compatibility test, even when the proposed generation may
vary with the receipt. This does not preclude a separate rejection
or first-forbidden lane, which is still manuscript-internal and OPEN. -/
theorem invisible_failure_no_total_edge_only_owner
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower)
    (ownerGeneration : TaggedReceiver → Fin 430)
    (ownerPosition : (z : TaggedReceiver) →
      Index N n root tau p (ownerGeneration z))
    (hmatch : ∀ z ∈ actualQExitFibre N n precision tau z0 lower k,
      ownerPosition z ∈
        literalSecondEdgeFinPositions N n root tau p (ownerGeneration z) k) :
    False := by
  obtain ⟨z, hz⟩ :=
    invisible_key_has_original_receipt
      N n precision root tau z0 p lower k hk
  exact (invisible_key_no_literal_second_edge
    N n precision root tau z0 p lower k hk
    (ownerGeneration z) (ownerPosition z)) (hmatch z hz)

end
end ImbalancedChen.Part5OriginalH430Full430UnseenFirstExitKeys
