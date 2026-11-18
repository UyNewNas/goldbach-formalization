import ImbalancedChen.Part5OriginalH430RetainedVsFirstExitSeparation

/-!
P5.6 / h34: distinguish literal q/tag receipts from their SHARED
projected physical (Q,p,ell) labels across the retained and the
actual first-excluded source lanes.

The retained label uses its canonical least ordinary-Rosser-eligible
SECOND prime divisor; the failure label uses its genuinely first
EXCLUDED factor. These are different historical semantics, even
when their numeric Q,p,ell triples coincide.

This packet proves the exact signed per-key receipt partition and
the extra combinatorial capacity beyond one failure event. No
projection equality is treated as a historical owner identification,
no nonzero charge is silently paid, and no historical multiplicity
is dropped. SOURCE ONLY / UNCOMPILED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430CrossSourceProjectedCapacity

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRetainedPrefixFibres
open Part5OriginalH430FirstCompatibleFrontierFactor
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430RetainedVsFirstExitSeparation

/-- Attach the literal physical Q to the canonical retained prefix.
The output is optional because some original receipts do not survive
the second ordinary Rosser gate. It never assigns those a fake key. -/
def retainedProjectedEventKey
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) : Option (ℝ × EventKey) :=
  (actualSecondPrefixKey N cap precision tau z0 lower z).map
    (fun key : SecondPrefixKey =>
      (originalPhysicalQ N precision tau z, (key.2.1, key.2.2)))

/-- At a retained receipt the projected label is witnessed by a
real prime divisor and an ACTUAL rank-two Rosser frontier state. -/
theorem retained_projected_key_is_frontier_compatible
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    ∃ ell : ℕ,
      retainedProjectedEventKey N cap precision tau z0 lower z =
        some (originalPhysicalQ N precision tau z,
          (arithmeticPrime z, ell)) ∧
      frontierEligibleSecond N cap precision tau z0 lower z ell := by
  obtain ⟨ell, hkey, hp, hdiv, hret⟩ :=
    actual_second_prefix_witness N cap precision tau z0 lower z hz
  refine ⟨ell, ?_, ?_⟩
  · simp [retainedProjectedEventKey, hkey]
  · exact (frontier_eligible_iff_actual_second
      N cap precision tau z0 lower z ell).2 ⟨hp, hdiv, hret⟩

/-- Each key fibre retains every original q/tag receipt, while
using the actual physical Q and the canonical compatible factor. -/
def retainedProjectedFibre
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey) : Finset TaggedReceiver :=
  (stageRetainedOriginal N cap precision tau z0 lower).filter
    (fun z => retainedProjectedEventKey N cap precision tau z0 lower z =
      some k)

theorem mem_retained_projected_fibre_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey) (z : TaggedReceiver) :
    z ∈ retainedProjectedFibre N cap precision tau z0 lower k ↔
      z ∈ stageRetainedOriginal N cap precision tau z0 lower ∧
      retainedProjectedEventKey N cap precision tau z0 lower z =
        some k := by
  simp [retainedProjectedFibre]

/-- Matching a failure label does not give a first-forbidden owner:
the retained receipt still has the genuine original compatible
frontier factor and the exact original physical Q. -/
theorem retained_projected_fibre_has_actual_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey) (z : TaggedReceiver)
    (hz : z ∈ retainedProjectedFibre N cap precision tau z0 lower k) :
    ∃ ell : ℕ,
      k = (originalPhysicalQ N precision tau z,
        (arithmeticPrime z, ell)) ∧
      frontierEligibleSecond N cap precision tau z0 lower z ell := by
  have hm := (mem_retained_projected_fibre_iff
    N cap precision tau z0 lower k z).mp hz
  obtain ⟨ell, hkey, hfront⟩ :=
    retained_projected_key_is_frontier_compatible
      N cap precision tau z0 lower z hm.1
  have hsome :
      some (originalPhysicalQ N precision tau z,
        (arithmeticPrime z, ell)) = some k :=
    hkey.symm.trans hm.2
  have hp :
      (originalPhysicalQ N precision tau z,
        (arithmeticPrime z, ell)) = k :=
    Option.some.inj hsome
  exact ⟨ell, hp.symm, hfront⟩

theorem retained_projected_fibre_preserves_Q
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey) (z : TaggedReceiver)
    (hz : z ∈ retainedProjectedFibre N cap precision tau z0 lower k) :
    originalPhysicalQ N precision tau z = k.1 := by
  obtain ⟨ell, hkey, _⟩ :=
    retained_projected_fibre_has_actual_frontier
      N cap precision tau z0 lower k z hz
  simpa using (congrArg Prod.fst hkey).symm

/-- A projected joint fibre can contain original retained receivers
and frozen-cutoff failure receivers with the SAME label. They are
combined as two disjoint sets of literal receipts. -/
def projectedJointFibre
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : ℝ × EventKey) : Finset TaggedReceiver :=
  retainedProjectedFibre N cap precision tau z0 lower k ∪
    actualQExitFibre N n precision tau z0 lower k

theorem projected_cross_source_receipts_disjoint
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (k : ℝ × EventKey) :
    Disjoint
      (retainedProjectedFibre N cap precision tau z0 lower k)
      (actualQExitFibre N n precision tau z0 lower k) := by
  apply Finset.disjoint_left.mpr
  intro z hret hfail
  have hr := (mem_retained_projected_fibre_iff
    N cap precision tau z0 lower k z).mp hret
  have hf := (mem_actual_Q_exit_fibre_iff
    N n precision tau z0 lower k z).mp hfail
  exact (retained_not_actual_Q_fail
    N n cap precision tau z0 lower hN htau htauhi hn hr.1) hf.1

/-- Cross-source numerical key collision means identical physical Q,
not an identical q/tag receipt nor identical first-forbidden action. -/
theorem projected_same_Q_but_distinct_receipts
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (k : ℝ × EventKey) (z y : TaggedReceiver)
    (hz : z ∈ retainedProjectedFibre N cap precision tau z0 lower k)
    (hy : y ∈ actualQExitFibre N n precision tau z0 lower k) :
    z ≠ y ∧
      originalPhysicalQ N precision tau z =
        originalPhysicalQ N precision tau y := by
  constructor
  · intro heq
    subst y
    exact (Finset.disjoint_left.mp
      (projected_cross_source_receipts_disjoint
        N n cap precision tau z0 lower hN htau htauhi hn k)) hz hy
  · calc
      originalPhysicalQ N precision tau z = k.1 :=
        retained_projected_fibre_preserves_Q
          N cap precision tau z0 lower k z hz
      _ = originalPhysicalQ N precision tau y :=
        (actual_Q_fibre_preserves_physical_Q
          N n precision tau z0 lower k y hy).symm

/-- The arithmetic signed source remains the sum of BOTH fibre
types, including negative weights and q/tag multiplicity. -/
theorem projected_joint_signed_sum
    {M : Type*} [AddCommMonoid M]
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (k : ℝ × EventKey) (w : TaggedReceiver → M) :
    (∑ z ∈ projectedJointFibre N n cap precision tau z0 lower k,
      w z) =
      (∑ z ∈ retainedProjectedFibre N cap precision tau z0 lower k,
        w z) +
      (∑ z ∈ actualQExitFibre N n precision tau z0 lower k,
        w z) := by
  simpa [projectedJointFibre] using
    (Finset.sum_union
      (projected_cross_source_receipts_disjoint
        N n cap precision tau z0 lower hN htau htauhi hn k)
      (f := w))

theorem projected_joint_card_partition
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (k : ℝ × EventKey) :
    (projectedJointFibre N n cap precision tau z0 lower k).card =
      (retainedProjectedFibre N cap precision tau z0 lower k).card +
      (actualQExitFibre N n precision tau z0 lower k).card := by
  simpa using
    (projected_joint_signed_sum (M := ℕ)
      N n cap precision tau z0 lower hN htau htauhi hn k
      (fun _ => (1 : ℕ)))

/-- At a genuine failure key one signed first-excluded history is
available, but the exact JOINT receipt capacity has both the previous
failure collision overhang and every retained projected receipt. -/
theorem projected_failure_key_exact_capacity
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower) :
    (projectedJointFibre N n cap precision tau z0 lower k).card =
      1 + (retainedProjectedFibre N cap precision tau z0 lower k).card +
        ((actualQExitFibre N n precision tau z0 lower k).card - 1) := by
  have hcard := projected_joint_card_partition
    N n cap precision tau z0 lower hN htau htauhi hn k
  obtain ⟨z, hz⟩ :=
    actual_Q_key_has_original_receipt N n precision tau z0 lower k hk
  have hpos :
      0 < (actualQExitFibre N n precision tau z0 lower k).card :=
    Finset.card_pos.mpr ⟨z, hz⟩
  omega

/-- If a genuine retained q/tag receipt shares the numerical
(Q,p,ell) failure label, there are STRICTLY MORE than one literal
receipt at the joint key. An event-key equality cannot justify a
one-receipt-per-history-slot claim. -/
theorem projected_shared_key_has_extra_receipt
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (k : ℝ × EventKey)
    (hk : k ∈ actualQExitKeys N n precision tau z0 lower)
    (hret : ∃ z,
      z ∈ retainedProjectedFibre N cap precision tau z0 lower k) :
    1 < (projectedJointFibre N n cap precision tau z0 lower k).card := by
  obtain ⟨z, hz⟩ := hret
  have hpositive :
      0 < (retainedProjectedFibre N cap precision tau z0 lower k).card :=
    Finset.card_pos.mpr ⟨z, hz⟩
  have hcapacity := projected_failure_key_exact_capacity
    N n cap precision tau z0 lower hN htau htauhi hn k hk
  omega

end
end ImbalancedChen.Part5OriginalH430CrossSourceProjectedCapacity
