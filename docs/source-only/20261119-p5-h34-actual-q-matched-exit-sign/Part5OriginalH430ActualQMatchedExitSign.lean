import ImbalancedChen.Part5OriginalH430RootMatchedInvisibleKeys
import ImbalancedChen.Part5OriginalH430EvenSignedExitBounds

/-!
P5.6 / h34 -- an ACTUAL PHYSICAL-Q (not caller-fixed Q) sign bound
for the original U3/U4 first-excluded q/tag source, restricted to
the genuine root-matched 430-edge-invisible rejection keys.

The earlier even-N signed rank-two interval was stated for the original
fourth-lane keys at ONE fixed Q. This file discharges that membership
condition separately at each original receipt's true tag-dependent Q,
then applies it to the genuinely same-root invisible subset.

In particular the one-per-PHYSICAL-KEY first-excluded correction has
negative sign, not a positive source payment. For the original UNIT
receipt count, the still-unpaid residual is at least the FULL number
of matching q/tag receipts. Distinct q and U3/U4 tags are not collapsed.

This is an internal source-only candidate. The strict edge-only
obstruction is not a new rejection Choice or a positive CLOSED-CELL
consumer. No newly external analytic theorem or new axiom.
UNCOMPILED / UNEVALUATED / COMPLETE H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualQMatchedExitSign

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430TrueReceiverWeightedExit
open Part5OriginalH430ActualQFirstExitReceipts
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430InvisiblePhysicalRejectionLane
open Part5OriginalH430RootMatchedInvisibleKeys
open Part5OriginalH430EvenSignedExitBounds

/-- Each physical (Q,p,ell) key of the original actual-Q failure
source is a genuine old fourth-lane key AT THAT SAME physical Q.
This is NOT the false assertion that all tags share a caller Q. -/
theorem actual_Q_key_is_fourth_key_at_own_Q
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower) :
    k.2 ∈ fourthDistinctKeys N n tau z0 k.1 lower := by
  classical
  change k ∈ (actualQFailSource N n precision tau z0 lower).image
    (actualQExitKey N n precision tau z0 lower) at hk
  obtain ⟨z, hz, hkey⟩ := Finset.mem_image.mp hk
  rcases Finset.mem_union.mp hz with hf | hr
  · have hlocal : z ∈ fourthFrozenFail N n tau z0
        (originalPhysicalQ N precision tau z) lower := by
      simpa [fourthFrozenFail] using (Finset.mem_filter.mp hf).2
    have hfourth : receiverEventKey (frozenOnlyBad N) z ∈
        fourthDistinctKeys N n tau z0
          (originalPhysicalQ N precision tau z) lower := by
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨z, hlocal, rfl⟩)
    have hactual : actualQExitKey N n precision tau z0 lower z =
        (originalPhysicalQ N precision tau z,
          receiverEventKey (frozenOnlyBad N) z) := by
      simp [actualQExitKey, hf]
    rw [← hkey, hactual]
    exact hfourth
  · have hn : z ∉ frozenFailAtActualQ N n precision tau z0 lower := by
      intro hf
      exact (Finset.disjoint_left.mp
        (actual_Q_two_fail_sources_disjoint
          N n precision tau z0 lower)) hf hr
    have hlocal : z ∈ fourthRejectedFail N n tau z0
        (originalPhysicalQ N precision tau z) lower := by
      simpa [fourthRejectedFail] using (Finset.mem_filter.mp hr).2
    have hfourth : receiverEventKey (rejectedFrozenBad N n tau) z ∈
        fourthDistinctKeys N n tau z0
          (originalPhysicalQ N precision tau z) lower := by
      apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_image.mpr ⟨z, hlocal, rfl⟩)
    have hactual : actualQExitKey N n precision tau z0 lower z =
        (originalPhysicalQ N precision tau z,
          receiverEventKey (rejectedFrozenBad N n tau) z) := by
      simp [actualQExitKey, hn]
    rw [← hkey, hactual]
    exact hfourth

/-- The unchanged even-N Euler-sign theorem now applies to EACH
distinct actual-Q key, without replacing tag-dependent Q by one
global parameter. The genuine remaining rough-prime Euler suffix
is retained, as in the old fixed-Q proof. -/
theorem actual_Q_key_signed_exit_interval
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower) :
    -originalEventMass k.2 ≤
      actualRankTwoSignedExit N cap lower k.1 k.2 ∧
      actualRankTwoSignedExit N cap lower k.1 k.2 ≤ 0 := by
  exact original_fourth_key_signed_exit_interval
    N n cap tau z0 k.1 lower hEven hzcap k.2
    (actual_Q_key_is_fourth_key_at_own_Q
      N n precision tau z0 lower k hk)

/-- True root-matched edge-invisible events still carry the ORIGINAL
negative first-excluded correction, even though no generated Fin edge
can hold the strict second-factor label. -/
theorem matched_invisible_signed_exit_interval
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (k : ℝ × EventKey)
    (hk : k ∈ matchedInvisibleKeys
      N n precision root tau z0 p lower) :
    -originalEventMass k.2 ≤
      actualRankTwoSignedExit N cap lower k.1 k.2 ∧
      actualRankTwoSignedExit N cap lower k.1 k.2 ≤ 0 := by
  have hsource : k ∈ actualQExitKeys
      N n precision tau z0 lower :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1
  exact actual_Q_key_signed_exit_interval
    N n cap precision tau z0 lower hEven hzcap k hsource

/-- Exactly the original tagged q receipts with a same-root invisible
physical key. Not a quotient by prime product or by common tag. -/
private theorem matched_receipts_eq_source_filter
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    matchedInvisibleReceipts N n precision root tau z0 p lower =
      (actualQFailSource N n precision tau z0 lower).filter
        (fun z => actualQExitKey N n precision tau z0 lower z ∈
          matchedInvisibleKeys N n precision root tau z0 p lower) := by
  classical
  ext z
  simp [matchedInvisibleReceipts, invisibleActualQReceipts,
    matchedInvisibleKeys, Finset.mem_filter, and_assoc]

/-- Actual q/tag receipts, not one receipt per event, reindex onto the
root-matched and truly 430-edge-invisible PHYSICAL key set. The
weight may be signed and may depend on both the tag and the q. -/
theorem matched_receipts_signed_fibres
    {M : Type*} [AddCommMonoid M]
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) (w : TaggedReceiver → M) :
    (∑ z ∈ matchedInvisibleReceipts N n precision root tau z0 p lower,
      w z) =
    ∑ k ∈ matchedInvisibleKeys N n precision root tau z0 p lower,
      ∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z := by
  classical
  rw [matched_receipts_eq_source_filter]
  symm
  unfold actualQExitFibre
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hk : actualQExitKey N n precision tau z0 lower z ∈
      matchedInvisibleKeys N n precision root tau z0 p lower
  · simp [hk]
  · simp [hk]

/-- Unit receipt cardinality keeps ALL original q/tag multiplicities,
whereas each physical first-excluded history is charged just once. -/
theorem matched_receipts_card_by_keys
    (N n precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool) :
    (matchedInvisibleReceipts N n precision root tau z0 p lower).card =
      ∑ k ∈ matchedInvisibleKeys N n precision root tau z0 p lower,
        (actualQExitFibre N n precision tau z0 lower k).card := by
  simpa using
    (matched_receipts_signed_fibres (M := ℕ)
      N n precision root tau z0 p lower (fun _ => (1 : ℕ)))

/-- For even N the once-per-physical-key historical first-excluded
signed correction is NONPOSITIVE. Subtracting it cannot fund ANY
positive original q/tag unit count at the genuinely matching root.
The full (unpaid) difference is at least the actual receipt count. -/
theorem matched_unit_receipt_unpaid_lower
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ)) :
    ((matchedInvisibleReceipts N n precision root tau z0 p lower).card : ℝ) ≤
      ∑ k ∈ matchedInvisibleKeys N n precision root tau z0 p lower,
        ((actualQExitFibre N n precision tau z0 lower k).card : ℝ) -
          actualRankTwoSignedExit N cap lower k.1 k.2 := by
  have hcard :
      ((matchedInvisibleReceipts
        N n precision root tau z0 p lower).card : ℝ) =
        ∑ k ∈ matchedInvisibleKeys N n precision root tau z0 p lower,
          ((actualQExitFibre N n precision tau z0 lower k).card : ℝ) := by
    exact_mod_cast matched_receipts_card_by_keys
      N n precision root tau z0 p lower
  rw [hcard]
  apply Finset.sum_le_sum
  intro k hk
  have hsign :=
    (matched_invisible_signed_exit_interval
      N n cap precision root tau z0 p lower hEven hzcap k hk).2
  linarith

/-- The unpaid count-surplus is strictly positive whenever the real
root-matched source actually contains a q/tag receipt. No existence
of such a source is asserted by this conditional result. -/
theorem matched_unit_unpaid_pos_of_receipt
    (N n cap precision : ℕ) (root : Root) (tau z0 : ℝ)
    (p : ℕ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (z : TaggedReceiver)
    (hz : z ∈ matchedInvisibleReceipts
      N n precision root tau z0 p lower) :
    0 < ∑ k ∈ matchedInvisibleKeys N n precision root tau z0 p lower,
      ((actualQExitFibre N n precision tau z0 lower k).card : ℝ) -
        actualRankTwoSignedExit N cap lower k.1 k.2 := by
  have hpositive :
      (0 : ℝ) <
        ((matchedInvisibleReceipts
          N n precision root tau z0 p lower).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨z, hz⟩)
  exact lt_of_lt_of_le hpositive
    (matched_unit_receipt_unpaid_lower
      N n cap precision root tau z0 p lower hEven hzcap)

end
end ImbalancedChen.Part5OriginalH430ActualQMatchedExitSign
