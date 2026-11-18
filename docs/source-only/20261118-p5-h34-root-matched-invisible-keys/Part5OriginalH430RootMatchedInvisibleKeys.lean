import ImbalancedChen.Part5OriginalH430InvisiblePhysicalRejectionLane

/-!
P5.6 / h34 -- distinguish WRONG-ROOT first-excluded event keys from
genuine SAME-ROOT first-excluded keys not visible in any of the literal
430 resolved request levels.

The earlier invisibleActualQExitKeys fixes one generated root but scans
ALL original actual-Q q/tag failure keys. Therefore a wrong physical Q
or root prime is automatically invisible: it is not evidence that this
root's request resolver omitted a payable rejection action.

This packet proves the precise disjoint partition, identifies the
root-mismatched part with an original-source filter, and restricts the
remaining genuinely same-root absence to original receipt occurrences.
No historical event is made a request action or charged more than once.
Manuscript INTERNAL; SOURCE ONLY / UNCOMPILED / UNEVALUATED / H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430RootMatchedInvisibleKeys

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430Full430UnseenFirstExitKeys
open Part5OriginalH430InvisiblePhysicalRejectionLane
open Part5OriginalH430LiteralSecondEdgeFinCapacity
open Part5OriginalH430RealSignedExitPayment

/-- Root matching is an actual physical Q and original root-prime test.
An equal excluded factor alone is insufficient. -/
def rootMatchesKey (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (k : ℝ × EventKey) : Prop :=
  rootQ N n root tau p = k.1 ∧ p = k.2.1

/-- This is the genuinely SAME-ROOT part of the original invisible keys. -/
def matchedInvisibleKeys
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) : Finset (ℝ × EventKey) :=
  (invisibleActualQExitKeys N n precision root tau z0 p lower).filter
    (rootMatchesKey N n root tau p)

/-- The complement consists of ORIGINAL first-excluded keys that belong
to a different physical Q or a different root prime. No owner in this
root is expected for these keys. -/
def mismatchedInvisibleKeys
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) : Finset (ℝ × EventKey) :=
  (invisibleActualQExitKeys N n precision root tau z0 p lower).filter
    (fun k => ¬ rootMatchesKey N n root tau p k)

/-- Every edge-visible event must have BOTH the correct physical Q and
the correct original root prime. This is a theorem about the actual
literal Fin candidates, not an assumed source-to-history owner. -/
theorem visible_key_matches_root
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ visibleActualQExitKeys N n precision root tau z0 p lower) :
    rootMatchesKey N n root tau p k := by
  have hsource : k ∈ actualQExitKeys N n precision tau z0 lower :=
    (Finset.mem_filter.mp hk).1
  constructor
  · by_contra hQ
    have hi := true_Q_mismatch_forces_invisible
      N n precision root tau z0 p lower k hsource hQ
    exact (Finset.mem_sdiff.mp hi).2 hk
  · by_contra hp
    have hi := true_prime_mismatch_forces_invisible
      N n precision root tau z0 p lower k hsource hp
    exact (Finset.mem_sdiff.mp hi).2 hk

/-- A wrong-root key in the ORIGINAL failure source is invisible
without any Buchstab or rejection-lane argument. -/
theorem source_mismatch_forces_invisible
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower)
    (hm : ¬ rootMatchesKey N n root tau p k) :
    k ∈ mismatchedInvisibleKeys N n precision root tau z0 p lower := by
  have hcases : rootQ N n root tau p ≠ k.1 ∨ p ≠ k.2.1 := by
    by_cases hQ : rootQ N n root tau p = k.1
    · exact Or.inr (by
        intro hp
        exact hm ⟨hQ, hp⟩)
    · exact Or.inl hQ
  have hi : k ∈ invisibleActualQExitKeys
      N n precision root tau z0 p lower := by
    rcases hcases with hQ | hp
    · exact true_Q_mismatch_forces_invisible
        N n precision root tau z0 p lower k hk hQ
    · exact true_prime_mismatch_forces_invisible
        N n precision root tau z0 p lower k hk hp
  exact Finset.mem_filter.mpr ⟨hi, hm⟩

/-- Unlike the genuinely matched part, all wrong-root keys are
already completely determined by the original failure source. -/
theorem mismatched_invisible_eq_original_filter
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    mismatchedInvisibleKeys N n precision root tau z0 p lower =
      (actualQExitKeys N n precision tau z0 lower).filter
        (fun k => ¬ rootMatchesKey N n root tau p k) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hi, hm⟩ := (Finset.mem_filter.mp hk)
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, hm⟩
  · intro hk
    obtain ⟨hsource, hm⟩ := Finset.mem_filter.mp hk
    exact source_mismatch_forces_invisible
      N n precision root tau z0 p lower k hsource hm

/-- The same-root invisible keys are precisely the original physically
matched keys MINUS the actual 430-generation edge-visible keys. -/
theorem matched_invisible_eq_original_matched_minus_visible
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    matchedInvisibleKeys N n precision root tau z0 p lower =
      ((actualQExitKeys N n precision tau z0 lower).filter
        (rootMatchesKey N n root tau p)) \
        visibleActualQExitKeys N n precision root tau z0 p lower := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hi, hm⟩ := Finset.mem_filter.mp hk
    obtain ⟨hsource, hnot⟩ := Finset.mem_sdiff.mp hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨hsource, hm⟩, hnot⟩
  · intro hk
    obtain ⟨hmatched, hnot⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hsource, hm⟩ := Finset.mem_filter.mp hmatched
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hsource, hnot⟩, hm⟩

/-- No invisible physical event key is dropped, and no key is paid
twice by merely splitting physical eligibility. -/
theorem invisible_keys_matched_mismatched_partition
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    invisibleActualQExitKeys N n precision root tau z0 p lower =
      matchedInvisibleKeys N n precision root tau z0 p lower ∪
        mismatchedInvisibleKeys N n precision root tau z0 p lower := by
  classical
  ext k
  constructor
  · intro hk
    by_cases hm : rootMatchesKey N n root tau p k
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hk, hm⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hk, hm⟩))
  · intro hk
    rcases Finset.mem_union.mp hk with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1

theorem matched_mismatched_disjoint
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    Disjoint
      (matchedInvisibleKeys N n precision root tau z0 p lower)
      (mismatchedInvisibleKeys N n precision root tau z0 p lower) := by
  apply Finset.disjoint_left.mpr
  intro k hmatch hmismatch
  have hyes := (Finset.mem_filter.mp hmatch).2
  have hno := (Finset.mem_filter.mp hmismatch).2
  exact hno hyes

/-- EXACT signed first-excluded mass decomposition. The wrong-root
contribution may be nonzero but cannot be charged to this generated root. -/
theorem invisible_signed_exit_matched_mismatched
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    (∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
      actualRankTwoSignedExit N cap lower k.1 k.2) =
      (∑ k ∈ matchedInvisibleKeys N n precision root tau z0 p lower,
        actualRankTwoSignedExit N cap lower k.1 k.2) +
      (∑ k ∈ mismatchedInvisibleKeys N n precision root tau z0 p lower,
        actualRankTwoSignedExit N cap lower k.1 k.2) := by
  rw [invisible_keys_matched_mismatched_partition]
  exact Finset.sum_union
    (matched_mismatched_disjoint N n precision root tau z0 p lower)

/-- A same-root invisible key has a real signed first-excluded history
yet cannot be assigned to any literal edge-visible position at this root.
No non-edge generated rejection action is inferred from the history. -/
theorem matched_key_true_event_but_no_literal_edge
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (hzcap : z0 ≤ (cap : ℝ))
    (k : ℝ × EventKey)
    (hk : k ∈ matchedInvisibleKeys N n precision root tau z0 p lower) :
    rootMatchesKey N n root tau p k ∧
      (∃ e : FirstExitDepthState ℕ,
        actualRankTwoHistory N cap lower k.1 k.2 = [e] ∧
        actualRankTwoSignedExit N cap lower k.1 k.2 =
          -originalEventMass k.2 *
            (e.remaining.map
              (fun q : ℕ => 1 - (1 / ((q : ℝ) - 1)))).prod) ∧
      (∀ (g : Fin 430) (l : Index N n root tau p g),
        l ∉ literalSecondEdgeFinPositions N n root tau p g k) := by
  have hi := (Finset.mem_filter.mp hk).1
  refine ⟨(Finset.mem_filter.mp hk).2, ?_, ?_⟩
  · exact invisible_key_has_actual_signed_first_exit
      N n cap precision root tau z0 p lower hzcap k hi
  · intro g l
    exact invisible_key_no_literal_second_edge
      N n precision root tau z0 p lower k hi g l

/-- Original tagged q receipts whose actual physical failure key
matches BOTH root parameters and remains invisible in the real 430 waves. -/
def matchedInvisibleReceipts
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) : Finset TaggedReceiver :=
  (invisibleActualQReceipts N n precision root tau z0 p lower).filter
    (fun z => rootMatchesKey N n root tau p
      (actualQExitKey N n precision tau z0 lower z))

/-- No q/tag is reclassified as payable merely by having the right
physical Q and p: it still has no compatible literal edge at any g. -/
theorem matched_receipt_true_root_no_literal_edge
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (z : TaggedReceiver)
    (hz : z ∈ matchedInvisibleReceipts
      N n precision root tau z0 p lower) :
    rootMatchesKey N n root tau p
      (actualQExitKey N n precision tau z0 lower z) ∧
      (∀ (g : Fin 430) (l : Index N n root tau p g),
        l ∉ literalSecondEdgeFinPositions N n root tau p g
          (actualQExitKey N n precision tau z0 lower z)) := by
  obtain ⟨hreceipt, hmatch⟩ := Finset.mem_filter.mp hz
  have hi : actualQExitKey N n precision tau z0 lower z ∈
      invisibleActualQExitKeys N n precision root tau z0 p lower :=
    (Finset.mem_filter.mp hreceipt).2
  refine ⟨hmatch, ?_⟩
  intro g l
  exact invisible_key_no_literal_second_edge
    N n precision root tau z0 p lower
    (actualQExitKey N n precision tau z0 lower z) hi g l

end
end ImbalancedChen.Part5OriginalH430RootMatchedInvisibleKeys
