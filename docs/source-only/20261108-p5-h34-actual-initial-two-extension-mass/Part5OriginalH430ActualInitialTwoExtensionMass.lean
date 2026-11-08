import ImbalancedChen.Part5OriginalH430ActualAllDepthFullPrefix
import ImbalancedChen.Part5OriginalH430UpperRetainedFinFibre

/-!
P5.6 / h34: EXACT first-two original-prime groups in the ACTUAL
arbitrary-depth ordinary-Rosser first-exit history.

The selectedPrefix of the real frontier is in REVERSE selection order:
at rank two it is [ell, p], whereas the original selection order is
[p, ell].  At rank k, a longer selectedPrefix can therefore have
different new letters but the same original (p,ell) first two letters.
We must keep ALL such deeper Fin occurrences.  Full-depth Nodup is not
rank-two fibre cardinality one at deeper levels.

This packet selects the first two original prime letters from the
actual list, proves disjointness of distinct such groups, and gives
an EXACT native weighted mass identity against the original admitted
tuple enumeration.  The weight function may be signed.  The real
retained U4 double-tag source is related to a genuine rank-two position,
not to an invented second history or a paid upper H430 owner.

This does NOT identify the manuscript full/selected/inherited owner,
the stage used by upper H430, original q/tag root weights, or any
signed first-excluded Euler-suffix payment.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualInitialTwoExtensionMass

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430ActualAllDepthFullPrefix
open Part5OriginalH430UpperRetainedFinFibre
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger

/-- The first two primes in ORIGINAL selection order; the genuine
frontier stores newest prime first. This is a partial first-two
projection also at ranks zero and one, without padding fake primes. -/
def actualFirstTwoOriginal (s : FirstExitDepthState ℕ) : List ℕ :=
  s.selectedPrefix.reverse.take 2

/-- Real Fin positions in the depth-k physical-Q LIST with the same
first two original prime labels. It does not quotient distinct deeper
extensions to a rank-two representative. -/
def actualDepthFirstTwoPositions
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (p ell : ℕ) :
    Finset (Fin (actualPhysicalDepthList k N cap z0 Q lower).length) :=
  Finset.univ.filter (fun i =>
    actualFirstTwoOriginal
      ((actualPhysicalDepthList k N cap z0 Q lower)[i]) = [p, ell])

theorem actual_depth_first_two_mem_iff
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (p ell : ℕ)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length) :
    i ∈ actualDepthFirstTwoPositions k N cap z0 Q lower p ell ↔
      ((actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix.reverse.take 2)
        = [p, ell] := by
  simp [actualDepthFirstTwoPositions, actualFirstTwoOriginal]

/-- Every observed Fin index is at EXACTLY the requested rank. This
instantiates the native frontier invariant, not a new rank convention. -/
theorem actual_depth_original_prefix_length
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length) :
    (actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix.length = k := by
  have hm :
      (actualPhysicalDepthList k N cap z0 Q lower)[i] ∈
        firstExitDepthFrontier k
          (ordinaryRosserRetainedPolicy lower Q)
          (fun r : ℕ => 1 / ((r : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap 0 z0) := by
    have hh : (actualPhysicalDepthList k N cap z0 Q lower)[i] ∈
        actualPhysicalDepthList k N cap z0 Q lower :=
      List.getElem_mem
    simpa only [actualPhysicalDepthList] using hh
  exact firstExitDepthFrontier_selected_length k
    (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap 0 z0) (by simp)
    _ hm

/-- The first-two original labels of a genuine depth-k position have
length two when k >= 2. No rank-two prefix is manufactured at rank 1. -/
theorem actual_depth_first_two_length
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (hk : 2 ≤ k)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length) :
    (actualFirstTwoOriginal
      ((actualPhysicalDepthList k N cap z0 Q lower)[i])).length = 2 := by
  have hlen := actual_depth_original_prefix_length k N cap z0 Q lower i
  simp [actualFirstTwoOriginal, List.length_take, hlen, Nat.min_eq_left hk]

/-- DISTINCT first-two groups at the SAME physical Q and depth
are disjoint as genuine Fin positions. This says nothing about the
cardinality INSIDE one group: many deeper extensions may survive. -/
theorem actual_depth_different_first_two_disjoint
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell p' ell' : ℕ) (hne : ([p, ell] : List ℕ) ≠ [p', ell']) :
    Disjoint
      (actualDepthFirstTwoPositions k N cap z0 Q lower p ell)
      (actualDepthFirstTwoPositions k N cap z0 Q lower p' ell') := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have h1 := (actual_depth_first_two_mem_iff
    k N cap z0 Q lower p ell i).mp hi
  have h2 := (actual_depth_first_two_mem_iff
    k N cap z0 Q lower p' ell' i).mp hj
  exact hne (h1.symm.trans h2)

/-- Exact signed native history mass of all rank-k extensions of
the same two ORIGINAL selected prime labels, before later owner
filters. We keep the genuine list order and all occurrences. -/
def actualDepthFirstTwoNativeMass
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (p ell : ℕ) : ℝ :=
  ((actualPhysicalDepthList k N cap z0 Q lower).map (fun s =>
    s.mass * (if actualFirstTwoOriginal s = [p, ell] then (1 : ℝ) else 0))).sum

/-- Exact tuple reindexing for a possibly SIGNED weight on the full
selected prefix. The indicator is applied to the first two original
prime labels and does not collapse later distinct suffix extensions.
This uses the existing genuine first-exit/admitted-tuple theorem. -/
theorem actual_depth_first_two_weighted_tuple_identity
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell : ℕ) (F : List ℕ → ℝ) :
    ((actualPhysicalDepthList k N cap z0 Q lower).map (fun s =>
      s.mass *
        (if actualFirstTwoOriginal s = [p, ell]
         then F s.selectedPrefix else 0))).sum =
    ∑ t ∈ firstExitAdmittedTuples k
        (ordinaryRosserRetainedPolicy lower Q)
        (roughPrimeUniverse N cap 0 z0),
      (∏ j, 1 / ((t j : ℝ) - 1)) *
        (if (List.ofFn t).reverse.reverse.take 2 = [p, ell]
         then F (List.ofFn t).reverse else 0) := by
  simpa only [actualFirstTwoOriginal] using
    (actual_depth_mass_sum_eq_admitted_tuples
      k N cap z0 Q lower
      (fun pre : List ℕ =>
        if pre.reverse.take 2 = [p, ell] then F pre else 0))

/-- The true numerical native mass of all deeper first-two extensions
equals the fixed-Q ordinary-Rosser ADMITTED-TUPLE sum, with every
original tuple occurrence included once and with no q/tag weight. -/
theorem actual_depth_first_two_native_mass_eq_admitted_tuples
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell : ℕ) :
    actualDepthFirstTwoNativeMass k N cap z0 Q lower p ell =
    ∑ t ∈ firstExitAdmittedTuples k
        (ordinaryRosserRetainedPolicy lower Q)
        (roughPrimeUniverse N cap 0 z0),
      (∏ j, 1 / ((t j : ℝ) - 1)) *
        (if (List.ofFn t).reverse.reverse.take 2 = [p, ell]
         then (1 : ℝ) else 0) := by
  simpa only [actualDepthFirstTwoNativeMass] using
    (actual_depth_first_two_weighted_tuple_identity
      k N cap z0 Q lower p ell (fun _ => (1 : ℝ)))

/-- Connect one GENUINELY retained original U4 quotient to the first-two
projection of the true depth-two Fin history at its actual physical Q.
The second U3/U4 tag is a DISTINCT arithmetic receipt at that very slot.
This is not an assertion that depth-k extensions give its upper owner. -/
theorem original_u4_retained_rank_two_initial_pair_and_two_receipts
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    (∃ i : Fin (actualPhysicalDepthList 2 N cap z0 slot.1 lower).length,
      i ∈ actualDepthFirstTwoPositions
        2 N cap z0 slot.1 lower slot.2.1 slot.2.2) ∧
      2 ≤ (originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).card := by
  dsimp
  let slot := physicalRankTwoSlot N precision tau
    (chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver))
  have hkey : chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver) ∈
      observedRankTwoKeys N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨Sum.inl x, hret, rfl⟩
  have hs : slot ∈ observedPhysicalSlots
      N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨
      chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver), hkey, rfl⟩
  obtain ⟨i, hi⟩ := observed_slot_has_actual_rank_two_position
    N cap precision tau z0 lower slot hs
  have htwo := original_u4_retained_slot_card_ge_two
    N cap precision tau z0 lower hN x hx hret
  refine ⟨⟨i, ?_⟩, htwo⟩
  apply (actual_depth_first_two_mem_iff
    2 N cap z0 slot.1 lower slot.2.1 slot.2.2 i).mpr
  change (actualPhysicalRankTwoList
    N cap z0 slot.1 lower)[i].selectedPrefix.reverse.take 2 =
      [slot.2.1, slot.2.2]
  rw [hi]
  simp

end
end ImbalancedChen.Part5OriginalH430ActualInitialTwoExtensionMass
