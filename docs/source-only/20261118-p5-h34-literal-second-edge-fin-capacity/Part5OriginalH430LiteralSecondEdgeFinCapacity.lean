import ImbalancedChen.Part5OriginalH430CrossSourceProjectedCapacity
import ImbalancedChen.Part5OriginalH430ActualRequestAllActionPartition

/-!
P5.6 / h34 — exact literal second-edge candidates at the ORIGINAL
generated request-history Fin positions.

A shared physical (Q,p,ell) key is not a historical owner. This file
makes the finite, position-indexed compatibility test explicit:
the true rooted Q and p must match, the position must be actually
resolved, and its REAL generated edge list must contain ell. We do
not assert that every legitimate first-excluded source must have
such a visible edge; that question is a separate manuscript-local
first-exit / rejection-lane obligation.

Any proposed assignment of literal retained/failure q/tag receipts
to THESE edge-visible positions must obey the proven image capacity.
We do not postulate such an assignment, nor injectivity, and we
do not treat this conditional capacity as arithmetic count payment.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / COMPLETE_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralSecondEdgeFinCapacity

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430CrossSourceProjectedCapacity

/-- The ORIGINAL generated request-list positions at generation g+1
whose literal root Q and prime p agree with k, and whose own real
edge history contains k's second prime. This is a candidate relation,
NOT a declaration that an arithmetic receiver is owned there. -/
def literalSecondEdgeFinPositions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (k : ℝ × EventKey) :
    Finset (Index N n root tau p g) :=
  (resolvedLevel N n root tau p g).filter (fun l =>
    rootQ N n root tau p = k.1 ∧
    p = k.2.1 ∧
    ∃ e ∈ (levelOccurrence l).path, edgePrimes e = k.2.2)

/-- All tests are performed on the true list position. No quotient by
the catalog label, the real Q, or the numeric event key occurs. -/
theorem mem_literal_second_edge_fin_positions_iff
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (k : ℝ × EventKey)
    (l : Index N n root tau p g) :
    l ∈ literalSecondEdgeFinPositions N n root tau p g k ↔
      l ∈ resolvedLevel N n root tau p g ∧
      rootQ N n root tau p = k.1 ∧
      p = k.2.1 ∧
      ∃ e ∈ (levelOccurrence l).path, edgePrimes e = k.2.2 := by
  simp [literalSecondEdgeFinPositions]

theorem literal_second_edge_fin_subset_resolved
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (k : ℝ × EventKey) :
    literalSecondEdgeFinPositions N n root tau p g k ⊆
      resolvedLevel N n root tau p g :=
  Finset.filter_subset _ _

/-- A candidate does carry the literal edge witness; its existence
does NOT establish first-forbidden owner semantics. -/
theorem literal_second_edge_fin_witness
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (k : ℝ × EventKey)
    (l : Index N n root tau p g)
    (hl : l ∈ literalSecondEdgeFinPositions N n root tau p g k) :
    ∃ e ∈ (levelOccurrence l).path, edgePrimes e = k.2.2 := by
  rcases (mem_literal_second_edge_fin_positions_iff
    N n root tau p g k l).mp hl with ⟨_, _, _, hpath⟩
  exact hpath

/-- A numeric same-key match cannot manufacture a request position
for an incompatible physical Q. -/
theorem literal_second_edge_fin_empty_of_Q_mismatch
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (k : ℝ × EventKey)
    (hQ : rootQ N n root tau p ≠ k.1) :
    literalSecondEdgeFinPositions N n root tau p g k = ∅ := by
  ext l
  simp [literalSecondEdgeFinPositions, hQ]

/-- Nor can a projected key with a different prime p be assigned to
this rooted request list merely because the second factor agrees. -/
theorem literal_second_edge_fin_empty_of_prime_mismatch
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (k : ℝ × EventKey)
    (hp : p ≠ k.2.1) :
    literalSecondEdgeFinPositions N n root tau p g k = ∅ := by
  ext l
  simp [literalSecondEdgeFinPositions, hp]

/-- Image of the ORIGINAL q/tag receipt set under a PROPOSED owner.
This function is a variable: the proof does not grant its existence
as a valid owner, or assert it is injective. -/
def proposedLiteralFinImage
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (lower : Bool) (p : ℕ) (g : Fin 430)
    (k : ℝ × EventKey)
    (owner : TaggedReceiver → Index N n root tau p g) :
    Finset (Index N n root tau p g) :=
  (projectedJointFibre N n cap precision tau z0 lower k).image owner

/-- A proposed receipt-to-Fin assignment that obeys the exact
position test has an image contained in the REAL resolved positions.
No mathematical source-to-owner correspondence is assumed. -/
theorem proposed_literal_fin_image_subset
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (lower : Bool) (p : ℕ) (g : Fin 430)
    (k : ℝ × EventKey)
    (owner : TaggedReceiver → Index N n root tau p g)
    (hmatch : ∀ z ∈ projectedJointFibre N n cap precision tau z0 lower k,
      owner z ∈ literalSecondEdgeFinPositions N n root tau p g k) :
    proposedLiteralFinImage N n cap precision root tau z0 lower p g k owner ⊆
      literalSecondEdgeFinPositions N n root tau p g k := by
  intro l hl
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hl
  exact hmatch z hz

theorem proposed_literal_fin_image_capacity_le
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (lower : Bool) (p : ℕ) (g : Fin 430)
    (k : ℝ × EventKey)
    (owner : TaggedReceiver → Index N n root tau p g)
    (hmatch : ∀ z ∈ projectedJointFibre N n cap precision tau z0 lower k,
      owner z ∈ literalSecondEdgeFinPositions N n root tau p g k) :
    (proposedLiteralFinImage N n cap precision root tau z0 lower p g k owner).card ≤
      (literalSecondEdgeFinPositions N n root tau p g k).card :=
  Finset.card_le_card
    (proposed_literal_fin_image_subset
      N n cap precision root tau z0 lower p g k owner hmatch)

/-- If there are strictly more literal q/tag receipts than genuinely
edge-compatible Fin positions, EVERY proposed complete matching has
a strictly positive receipt-minus-distinct-position overhang. It
cannot be removed by treating repeated numeric keys as one receipt. -/
theorem positive_literal_fin_collision_overhang
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (lower : Bool) (p : ℕ) (g : Fin 430)
    (k : ℝ × EventKey)
    (owner : TaggedReceiver → Index N n root tau p g)
    (hmatch : ∀ z ∈ projectedJointFibre N n cap precision tau z0 lower k,
      owner z ∈ literalSecondEdgeFinPositions N n root tau p g k)
    (hshort :
      (literalSecondEdgeFinPositions N n root tau p g k).card <
      (projectedJointFibre N n cap precision tau z0 lower k).card) :
    0 <
      (projectedJointFibre N n cap precision tau z0 lower k).card -
      (proposedLiteralFinImage N n cap precision root tau z0 lower p g k owner).card := by
  have hc := proposed_literal_fin_image_capacity_le
    N n cap precision root tau z0 lower p g k owner hmatch
  omega

/-- At a genuine failure event key sharing at least one retained
receipt, ONE available edge-compatible Fin position is insufficient
for a collision-free matching of all literal q/tag receipts.
This is conditional on an actual proposed matching: it creates no
new historical payment or first-forbidden owner. -/
theorem shared_failure_key_one_fin_forces_overhang
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (lower : Bool) (p : ℕ) (g : Fin 430)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower)
    (hret : ∃ z,
      z ∈ retainedProjectedFibre N cap precision tau z0 lower k)
    (hcap : (literalSecondEdgeFinPositions N n root tau p g k).card ≤ 1)
    (owner : TaggedReceiver → Index N n root tau p g)
    (hmatch : ∀ z ∈ projectedJointFibre N n cap precision tau z0 lower k,
      owner z ∈ literalSecondEdgeFinPositions N n root tau p g k) :
    0 <
      (projectedJointFibre N n cap precision tau z0 lower k).card -
      (proposedLiteralFinImage N n cap precision root tau z0 lower p g k owner).card := by
  have hmore := projected_shared_key_has_extra_receipt
    N n cap precision tau z0 lower hN htau htauhi hn k hk hret
  have hshort :
      (literalSecondEdgeFinPositions N n root tau p g k).card <
        (projectedJointFibre N n cap precision tau z0 lower k).card := by
    omega
  exact positive_literal_fin_collision_overhang
    N n cap precision root tau z0 lower p g k owner hmatch hshort

end
end ImbalancedChen.Part5OriginalH430LiteralSecondEdgeFinCapacity
