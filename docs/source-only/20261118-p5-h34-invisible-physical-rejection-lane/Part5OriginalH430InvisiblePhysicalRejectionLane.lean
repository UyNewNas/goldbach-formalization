import ImbalancedChen.Part5OriginalH430Full430UnseenFirstExitKeys

/-!
P5.6 / h34: bind original q/tag receipts whose actual-Q first-excluded
key is not present in ANY literal edge-visible resolved request position
to their genuine one-per-key rank-two rejected-history EVENT.

The event is selected from the existing historicalRejectedEvents computation,
not posited as a new payment or inserted into a generated request edge.
The original physical Q, p, ell and every q/tag fibre occurrence remain.
In particular the receipt-to-event map need not be injective. Its exact
signed discrepancy and cardinal excess are left explicitly unpaid.

MANUSCRIPT INTERNAL. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430InvisiblePhysicalRejectionLane

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430LiteralSecondEdgeFinCapacity
open Part5OriginalH430Full430UnseenFirstExitKeys

/-- The actual original failure RECEIPTS whose physical Q/p/ell key
has no literal edge-visible resolved Fin occurrence in all 430 levels
for the chosen root. This keeps each original U3/U4 tag and q. -/
def invisibleActualQReceipts
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) : Finset TaggedReceiver :=
  (actualQFailSource N n precision tau z0 lower).filter
    (fun z => actualQExitKey N n precision tau z0 lower z ∈
      invisibleActualQExitKeys N n precision root tau z0 p lower)

/-- Every invisible key is the image of at least one ORIGINAL q/tag
receipt, and no non-invisible key is introduced by this source. -/
theorem invisible_receipt_keys_exact
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    (invisibleActualQReceipts N n precision root tau z0 p lower).image
      (actualQExitKey N n precision tau z0 lower) =
      invisibleActualQExitKeys N n precision root tau z0 p lower := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hz).2
  · intro hk
    obtain ⟨z, hz⟩ :=
      invisible_key_has_original_receipt
        N n precision root tau z0 p lower k hk
    obtain ⟨hsource, hkey⟩ :=
      (mem_actual_Q_exit_fibre_iff
        N n precision tau z0 lower k z).mp hz
    have hin : actualQExitKey N n precision tau z0 lower z ∈
        invisibleActualQExitKeys N n precision root tau z0 p lower := by
      rw [hkey]
      exact hk
    exact Finset.mem_image.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hsource, hin⟩, hkey⟩

/-- The original source is indexed by original physical event keys
without merging distinct q/tag receipts. Works for signed weights. -/
theorem invisible_receipts_signed_fibre_partition
    {M : Type*} [AddCommMonoid M]
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (w : TaggedReceiver → M) :
    (∑ z ∈ invisibleActualQReceipts N n precision root tau z0 p lower,
      w z) =
    ∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
      ∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z := by
  classical
  symm
  unfold invisibleActualQReceipts actualQExitFibre
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hk : actualQExitKey N n precision tau z0 lower z ∈
      invisibleActualQExitKeys N n precision root tau z0 p lower
  · simp [hk]
  · simp [hk]

/-- Type-level ownership records exactly which ACTUAL invisible
physical key the particular original receipt belongs to. -/
def invisibleReceiptKey
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool)
    (z : {z : TaggedReceiver //
      z ∈ invisibleActualQReceipts N n precision root tau z0 p lower}) :
    {k : ℝ × EventKey //
      k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower} :=
  ⟨actualQExitKey N n precision tau z0 lower z.1,
    (Finset.mem_filter.mp z.property).2⟩

theorem invisible_receipt_key_preserves_physical_Q
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool)
    (z : {z : TaggedReceiver //
      z ∈ invisibleActualQReceipts N n precision root tau z0 p lower}) :
    (invisibleReceiptKey N n precision root tau z0 p lower z).1.1 =
      originalPhysicalQ N precision tau z.1 := rfl

theorem invisible_receipt_in_own_actual_Q_fibre
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool)
    (z : {z : TaggedReceiver //
      z ∈ invisibleActualQReceipts N n precision root tau z0 p lower}) :
    z.1 ∈ actualQExitFibre N n precision tau z0 lower
      (invisibleReceiptKey N n precision root tau z0 p lower z).1 := by
  apply Finset.mem_filter.mpr
  exact ⟨(Finset.mem_filter.mp z.property).1, rfl⟩

/-- A receipt's actual non-edge key cannot be assigned to a strict
edge-visible generated Fin position, at ANY g < 430. -/
theorem invisible_receipt_owner_has_no_literal_edge
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool)
    (z : {z : TaggedReceiver //
      z ∈ invisibleActualQReceipts N n precision root tau z0 p lower})
    (g : Fin 430) (l : Index N n root tau p g) :
    l ∉ literalSecondEdgeFinPositions N n root tau p g
      (invisibleReceiptKey N n precision root tau z0 p lower z).1 := by
  exact invisible_key_no_literal_second_edge
    N n precision root tau z0 p lower
    (invisibleReceiptKey N n precision root tau z0 p lower z).1
    (invisibleReceiptKey N n precision root tau z0 p lower z).2 g l

/-- Select the genuine single rejected-history EVENT proven to exist
by the earlier physical actual-Q first-exit theorem. Classical choice
only extracts its proved witness; it is not a new event or axiom. -/
def invisibleKeyRejectionEvent
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (hzcap : z0 ≤ (cap : ℝ))
    (k : {k : ℝ × EventKey //
      k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower}) :
    FirstExitDepthState ℕ :=
  Classical.choose
    (actual_Q_unique_key_has_signed_first_exit
      N n cap precision tau z0 lower hzcap k.1
      (Finset.mem_sdiff.mp k.property).1)

/-- This is the SINGLE actual rank-two historical first-excluded
event for the physical key, with its real prefix, sign, mass and full
remaining Euler product. No occurrence is multiplied by fibre size. -/
theorem invisible_key_rejection_event_spec
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (hzcap : z0 ≤ (cap : ℝ))
    (k : {k : ℝ × EventKey //
      k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower}) :
    let e := invisibleKeyRejectionEvent
      N n cap precision root tau z0 p lower hzcap k
    actualRankTwoHistory N cap lower k.1.1 k.1.2 = [e] ∧
      e.selectedPrefix = [k.1.2.2, k.1.2.1] ∧
      e.positive = true ∧
      e.mass = originalEventMass k.1.2 ∧
      actualRankTwoSignedExit N cap lower k.1.1 k.1.2 =
        -originalEventMass k.1.2 *
          (e.remaining.map
            (fun q : ℕ => 1 - (1 / ((q : ℝ) - 1)))).prod := by
  exact Classical.choose_spec
    (actual_Q_unique_key_has_signed_first_exit
      N n cap precision tau z0 lower hzcap k.1
      (Finset.mem_sdiff.mp k.property).1)

/-- A concrete receipt-to-REJECTION-EVENT map. It is a real history
witness, not a generated Fin owner; distinct receipts may map to it. -/
def invisibleReceiptRejectionEvent
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (hzcap : z0 ≤ (cap : ℝ))
    (z : {z : TaggedReceiver //
      z ∈ invisibleActualQReceipts N n precision root tau z0 p lower}) :
    FirstExitDepthState ℕ :=
  invisibleKeyRejectionEvent N n cap precision root tau z0 p lower
    hzcap (invisibleReceiptKey N n precision root tau z0 p lower z)

/-- Exact receipt count: one distinct physical rejection EVENT key,
plus all additional q/tag receipts under that same key. Cardinal
overhang is not a multiplier of its signed history mass. -/
theorem invisible_rejection_receipt_capacity
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    (invisibleActualQReceipts N n precision root tau z0 p lower).card =
      (invisibleActualQExitKeys N n precision root tau z0 p lower).card +
      ∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
        ((actualQExitFibre N n precision tau z0 lower k).card - 1) := by
  classical
  have hcount :
      (invisibleActualQReceipts N n precision root tau z0 p lower).card =
        ∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
          (actualQExitFibre N n precision tau z0 lower k).card := by
    simpa using
      (invisible_receipts_signed_fibre_partition (M := ℕ)
        N n precision root tau z0 p lower (fun _ => (1 : ℕ)))
  rw [hcount]
  calc
    (∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
      (actualQExitFibre N n precision tau z0 lower k).card) =
      ∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
        (1 + ((actualQExitFibre N n precision tau z0 lower k).card - 1)) := by
          apply Finset.sum_congr rfl
          intro k hk
          obtain ⟨z, hz⟩ := invisible_key_has_original_receipt
            N n precision root tau z0 p lower k hk
          have hpos : 0 <
              (actualQExitFibre N n precision tau z0 lower k).card :=
            Finset.card_pos.mpr ⟨z, hz⟩
          omega
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Exact signed rejection-lane ledger: the existing TRUE one-event
historical correction is credited once per physical key; every
unmatched q/tag weighted contribution remains EXPLICITLY UNPAID. -/
theorem invisible_rejection_signed_gap_ledger
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ invisibleActualQReceipts N n precision root tau z0 p lower,
      w z) =
      (∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
        actualRankTwoSignedExit N cap lower k.1 k.2) +
      (∑ k ∈ invisibleActualQExitKeys N n precision root tau z0 p lower,
        (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) -
          actualRankTwoSignedExit N cap lower k.1 k.2) := by
  rw [invisible_receipts_signed_fibre_partition]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end ImbalancedChen.Part5OriginalH430InvisiblePhysicalRejectionLane
