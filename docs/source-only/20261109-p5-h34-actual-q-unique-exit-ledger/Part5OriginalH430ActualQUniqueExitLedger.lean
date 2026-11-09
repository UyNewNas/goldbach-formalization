import ImbalancedChen.Part5OriginalH430ActualQFirstExitReceipts

/-!
P5.6 / h34 — one signed rank-two first-excluded event per DISTINCT
actual (physical Q, p, ell) key, not per original U3/U4 q/tag receipt.

Both genuinely different cutoff-failure sources are used at the
receipt's own originalPhysicalQ. The key fibre retains every original
q/tag occurrence, even if two receipts have identical Q/p/ell.
The signed historical exit uses its complete remaining Euler product.
The difference between original signed receipts and the once-per-key
historical exit remains EXPLICITLY UNPAID.

Manuscript-internal SOURCE ONLY / UNCOMPILED / UNEVALUATED.
No root owner, selected/inherited licence, or quantitative H430 bound
is assumed or concluded.
-/

namespace ImbalancedChen.Part5OriginalH430ActualQUniqueExitLedger

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualQFirstExitReceipts

/-- Precisely the two ORIGINAL eligible first-excluded receipt lanes.
They are disjoint as q/tag receipts, not necessarily as event keys. -/
def actualQFailSource (N n precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) : Finset TaggedReceiver :=
  frozenFailAtActualQ N n precision tau z0 lower ∪
    rejectedFailAtActualQ N n precision tau z0 lower

/-- Historical key includes the TRUE tag-dependent physical Q.
Each lane uses its own original bad-factor function. The fallback is
used only for receipts outside the first lane; on the source union
it is necessarily in the second lane. -/
def actualQExitKey (N n precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (z : TaggedReceiver) : ℝ × EventKey :=
  (originalPhysicalQ N precision tau z,
    if z ∈ frozenFailAtActualQ N n precision tau z0 lower then
      receiverEventKey (frozenOnlyBad N) z
    else
      receiverEventKey (rejectedFrozenBad N n tau) z)

/-- Physical Q and (p,ell) are deduplicated as a TRIPLE, not by
arithmetic q, tag, p alone, or a global caller-specified Q. -/
def actualQExitKeys (N n precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) : Finset (ℝ × EventKey) :=
  (actualQFailSource N n precision tau z0 lower).image
    (actualQExitKey N n precision tau z0 lower)

/-- Full receipt fibre, preserving all colliding q/tag multiplicities. -/
def actualQExitFibre (N n precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (k : ℝ × EventKey) : Finset TaggedReceiver :=
  (actualQFailSource N n precision tau z0 lower).filter
    (fun z => actualQExitKey N n precision tau z0 lower z = k)

theorem mem_actual_Q_exit_fibre_iff
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey) (z : TaggedReceiver) :
    z ∈ actualQExitFibre N n precision tau z0 lower k ↔
      z ∈ actualQFailSource N n precision tau z0 lower ∧
        actualQExitKey N n precision tau z0 lower z = k := by
  simp [actualQExitFibre]

/-- A true fibre cannot silently move one receipt to a different Q. -/
theorem actual_Q_fibre_preserves_physical_Q
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey) (z : TaggedReceiver)
    (hz : z ∈ actualQExitFibre N n precision tau z0 lower k) :
    originalPhysicalQ N precision tau z = k.1 := by
  have hk := (mem_actual_Q_exit_fibre_iff
    N n precision tau z0 lower k z).mp hz
  simpa [actualQExitKey] using congrArg Prod.fst hk.2

/-- Genuine original signed q/tag source partitions over actual
physical event keys, with NO injectivity or sign assumption. -/
theorem actual_Q_signed_fibre_partition
    {M : Type*} [AddCommMonoid M]
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → M) :
    (∑ z ∈ actualQFailSource N n precision tau z0 lower, w z) =
      ∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        ∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z := by
  classical
  symm
  unfold actualQExitKeys actualQExitFibre
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hm : actualQExitKey N n precision tau z0 lower z ∈
      (actualQFailSource N n precision tau z0 lower).image
        (actualQExitKey N n precision tau z0 lower) :=
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  simp [hm]

/-- Every source q/tag occurrence remains in the cardinal ledger;
one physical key need not mean one receipt. -/
theorem actual_Q_receipt_card_by_unique_keys
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (actualQFailSource N n precision tau z0 lower).card =
      ∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        (actualQExitFibre N n precision tau z0 lower k).card := by
  simpa using
    (actual_Q_signed_fibre_partition (M := ℕ)
      N n precision tau z0 lower (fun _ => (1 : ℕ)))

/-- The original two disjoint rejection lanes remain present with
their separate bad-factor rules and arbitrary SIGNED weights. -/
theorem actual_Q_two_fail_signed_split
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ actualQFailSource N n precision tau z0 lower, w z) =
      (∑ z ∈ frozenFailAtActualQ N n precision tau z0 lower, w z) +
      (∑ z ∈ rejectedFailAtActualQ N n precision tau z0 lower, w z) := by
  simpa [actualQFailSource] using
    (Finset.sum_union
      (actual_Q_two_fail_sources_disjoint
        N n precision tau z0 lower) w)

/-- For EACH DISTINCT actual (Q,p,ell), exactly one genuine
rank-two signed first-excluded history is available. This follows
from a real original receipt in one of the two lanes, not from an
assumed globally fixed Q or an injected q/tag source. -/
theorem actual_Q_unique_key_has_signed_first_exit
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower) :
    ∃ event : FirstExitDepthState ℕ,
      actualRankTwoHistory N cap lower k.1 k.2 = [event] ∧
      event.selectedPrefix = [k.2.2, k.2.1] ∧
      event.positive = true ∧
      event.mass = originalEventMass k.2 ∧
      actualRankTwoSignedExit N cap lower k.1 k.2 =
        -originalEventMass k.2 *
          (event.remaining.map
            (fun q : ℕ => 1 - (1 / ((q : ℝ) - 1)))).prod := by
  classical
  change k ∈ (actualQFailSource N n precision tau z0 lower).image
    (actualQExitKey N n precision tau z0 lower) at hk
  obtain ⟨z, hz, hkey⟩ := Finset.mem_image.mp hk
  rcases Finset.mem_union.mp hz with hf | hr
  · have hactual :
        actualQExitKey N n precision tau z0 lower z =
          (originalPhysicalQ N precision tau z,
            receiverEventKey (frozenOnlyBad N) z) := by
          simp [actualQExitKey, hf]
    rw [hactual] at hkey
    subst k
    simpa [receiverEventKey] using
      (frozen_fail_actual_Q_unique_signed_first_exit
        N n cap precision tau z0 lower hzcap z hf)
  · have hn : z ∉ frozenFailAtActualQ N n precision tau z0 lower := by
      intro hf
      exact (Finset.disjoint_left.mp
        (actual_Q_two_fail_sources_disjoint
          N n precision tau z0 lower)) hf hr
    have hactual :
        actualQExitKey N n precision tau z0 lower z =
          (originalPhysicalQ N precision tau z,
            receiverEventKey (rejectedFrozenBad N n tau) z) := by
          simp [actualQExitKey, hn]
    rw [hactual] at hkey
    subst k
    simpa [receiverEventKey] using
      (rejected_fail_actual_Q_unique_signed_first_exit
        N n cap precision tau z0 lower hzcap z hr)

/-- A DISTINCT physical (Q,p,ell) history is charged ONCE, while its
original q/tag source fibre remains a separate signed amount. The
entire difference is NOT YET PAID; no positivity, cancellation, owner,
or H430 inequality is inferred from this exact identity. -/
theorem actual_Q_unique_signed_exit_and_unpaid_fibre_ledger
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ frozenFailAtActualQ N n precision tau z0 lower, w z) +
    (∑ z ∈ rejectedFailAtActualQ N n precision tau z0 lower, w z) =
      (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        actualRankTwoSignedExit N cap lower k.1 k.2) +
      (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) -
          actualRankTwoSignedExit N cap lower k.1 k.2) := by
  calc
    _ = (∑ z ∈ actualQFailSource N n precision tau z0 lower, w z) :=
      (actual_Q_two_fail_signed_split N n precision tau z0 lower w).symm
    _ = (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
          ∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) :=
      actual_Q_signed_fibre_partition N n precision tau z0 lower w
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring

end
end ImbalancedChen.Part5OriginalH430ActualQUniqueExitLedger
