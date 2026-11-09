import ImbalancedChen.Part5OriginalH430ActualQUniqueExitLedger
import ImbalancedChen.Part5OriginalH430EvenSignedExitBounds

/-!
P5.6 / h34 — transfer the existing genuine even-N rank-two signed
Euler EXIT bounds from a caller-fixed Q to each ORIGINAL q/tag
receipt key's own tag/root-dependent physical Q.

The previous actual-Q source packet enumerated DISTINCT (Q,p,ell)
keys with full original q/tag fibres, but gave no direction on the
once-per-key signed correction or the unpaid fibre gap.  The existing
even-N bound applied only to a fixed-Q original fourth-key set.
The present bridge proves each new actual-Q key is indeed a member
of THAT fixed-Q fourth-key set evaluated at its very own k.1.
This membership uses the original frozen-only/rejected-frozen
arithmetic witnesses, with their DIFFERENT first-bad-prime cutoffs.

The signed rank-two exit is between -bareMass and 0 for each
distinct actual key; the true arbitrary signed q/tag fibre gap is
therefore between its literal receipt sum and that sum + bareMass.
This is a direction/budget for two event-bearing rejection lanes,
NOT a payment, an owner, or the h34 quantitative upper bound.
No claim is made that the global upper parity-safe Euler correction
has the sign of any individual rank-two signed exit.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualQSignedGapBounds

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430ActualQFirstExitReceipts
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430TrueReceiverWeightedExit
open Part5OriginalH430EvenSignedExitBounds

/-- The key's TRUE Q selects an existing, fixed-Q fourth-lane key.
This is proved from the actual tagged source witness; it does not
assume a global Q, injectivity, or a future selected-count owner. -/
theorem actual_Q_key_in_same_Q_fourth_keys
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower) :
    k.2 ∈ fourthDistinctKeys N n tau z0 k.1 lower := by
  classical
  change k ∈ (actualQFailSource N n precision tau z0 lower).image
    (actualQExitKey N n precision tau z0 lower) at hk
  obtain ⟨z, hz, hkey⟩ := Finset.mem_image.mp hk
  rcases Finset.mem_union.mp hz with hf | hr
  · have hpair :
        (originalPhysicalQ N precision tau z,
          receiverEventKey (frozenOnlyBad N) z) = k := by
      simpa [actualQExitKey, hf] using hkey
    have hQ : originalPhysicalQ N precision tau z = k.1 :=
      congrArg Prod.fst hpair
    have hkey' : receiverEventKey (frozenOnlyBad N) z = k.2 :=
      congrArg Prod.snd hpair
    have hfixed : z ∈ fourthFrozenFail N n tau z0 k.1 lower := by
      change z ∈ ownPolicyFail (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 k.1 lower
      rw [← hQ]
      exact (Finset.mem_filter.mp hf).2
    unfold fourthDistinctKeys
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨z, hfixed, hkey'⟩))
  · have hnot :
        z ∉ frozenFailAtActualQ N n precision tau z0 lower := by
      intro hf
      exact (Finset.disjoint_left.mp
        (actual_Q_two_fail_sources_disjoint
          N n precision tau z0 lower)) hf hr
    have hpair :
        (originalPhysicalQ N precision tau z,
          receiverEventKey (rejectedFrozenBad N n tau) z) = k := by
      simpa [actualQExitKey, hnot] using hkey
    have hQ : originalPhysicalQ N precision tau z = k.1 :=
      congrArg Prod.fst hpair
    have hkey' :
        receiverEventKey (rejectedFrozenBad N n tau) z = k.2 :=
      congrArg Prod.snd hpair
    have hfixed : z ∈ fourthRejectedFail N n tau z0 k.1 lower := by
      change z ∈ ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 k.1 lower
      rw [← hQ]
      exact (Finset.mem_filter.mp hr).2
    unfold fourthDistinctKeys
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨z, hfixed, hkey'⟩))

/-- The literal even-N first-excluded correction at each DISTINCT
actual physical key is nonpositive, and its magnitude does not
exceed one original bare event mass.  The historical Euler suffix
is retained by the inherited fixed-Q theorem, not replaced by 1. -/
theorem actual_Q_unique_key_signed_exit_interval
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower) :
    -originalEventMass k.2 ≤
        actualRankTwoSignedExit N cap lower k.1 k.2 ∧
      actualRankTwoSignedExit N cap lower k.1 k.2 ≤ 0 := by
  exact original_fourth_key_signed_exit_interval
    N n cap tau z0 k.1 lower hEven hzcap k.2
    (actual_Q_key_in_same_Q_fourth_keys
      N n precision tau z0 lower k hk)

/-- Each true q/tag fibre retains its arbitrary signed arithmetic
weight.  Subtracting the one REAL signed rank-two exit can only
increase the unpaid gap, by at most one bare event mass.
This is NOT a theorem bounding that gap by the h34 budget. -/
theorem actual_Q_single_fibre_gap_interval
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (w : TaggedReceiver → ℝ) (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower) :
    (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) ≤
      (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) -
        actualRankTwoSignedExit N cap lower k.1 k.2 ∧
    (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) -
        actualRankTwoSignedExit N cap lower k.1 k.2 ≤
      (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) +
        originalEventMass k.2 := by
  obtain ⟨hlow, hhigh⟩ :=
    actual_Q_unique_key_signed_exit_interval
      N n cap precision tau z0 lower hEven hzcap k hk
  constructor <;> linarith

/-- Across the WHOLE actual-Q two-lane source, preserve original
q/tag multiplicity and arbitrary signs while bounding the still-unpaid
difference in the correct direction.  One rank-two Euler event is
used once per distinct (Q,p,ell), never once per q or tag. -/
theorem actual_Q_total_unpaid_gap_interval
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ actualQFailSource N n precision tau z0 lower, w z) ≤
      ∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) -
          actualRankTwoSignedExit N cap lower k.1 k.2 ∧
    (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        (∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) -
          actualRankTwoSignedExit N cap lower k.1 k.2) ≤
      (∑ z ∈ actualQFailSource N n precision tau z0 lower, w z) +
      (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        originalEventMass k.2) := by
  have hsource := actual_Q_signed_fibre_partition
    N n precision tau z0 lower w
  constructor
  · calc
      _ = ∑ k ∈ actualQExitKeys N n precision tau z0 lower,
          ∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z :=
            hsource
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact (actual_Q_single_fibre_gap_interval
          N n cap precision tau z0 lower hEven hzcap w k hk).1
  · calc
      _ ≤ ∑ k ∈ actualQExitKeys N n precision tau z0 lower,
          ((∑ z ∈ actualQExitFibre N n precision tau z0 lower k, w z) +
            originalEventMass k.2) := by
              apply Finset.sum_le_sum
              intro k hk
              exact (actual_Q_single_fibre_gap_interval
                N n cap precision tau z0 lower hEven hzcap w k hk).2
      _ = _ := by
        rw [Finset.sum_add_distrib, ← hsource]

/-- Summed real signed exits for the actual physical-Q image are
NONPOSITIVE, unlike the entire parity-safe upper Euler correction.
This keeps the two distinct historical objects' signs separate. -/
theorem actual_Q_total_rank_two_signed_exit_nonpos
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ)) :
    (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
      actualRankTwoSignedExit N cap lower k.1 k.2) ≤ 0 := by
  calc
    _ ≤ ∑ _k ∈ actualQExitKeys N n precision tau z0 lower,
        (0 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact (actual_Q_unique_key_signed_exit_interval
            N n cap precision tau z0 lower hEven hzcap k hk).2
    _ = 0 := by simp

/-- In the original Chen NEGATIVE-quarter convention, subtracting
these individual negative rank-two exits creates a nonnegative term.
It therefore cannot be booked as an already-paid positive q/tag
rejection.  This does not identify full/selected/inherited owners. -/
theorem actual_Q_chen_quarter_rank_two_exit_nonneg
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ)) :
    0 ≤ -(1 / 4 : ℝ) *
      (∑ k ∈ actualQExitKeys N n precision tau z0 lower,
        actualRankTwoSignedExit N cap lower k.1 k.2) := by
  exact mul_nonneg_of_nonpos_of_nonpos
    (by norm_num)
    (actual_Q_total_rank_two_signed_exit_nonpos
      N n cap precision tau z0 lower hEven hzcap)

end
end ImbalancedChen.Part5OriginalH430ActualQSignedGapBounds
