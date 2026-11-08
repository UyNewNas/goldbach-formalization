import ImbalancedChen.Part5OriginalH430UpperRankTwoPrefixCapacity
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-!
P5.6 / h34: the REAL ordinary-Rosser first-exit frontier at EVERY depth.

The earlier observed-slot uniqueness was restricted to rank two.  A
later upper H430 owner is not known to live at that rank.  Here we
recover the actual fixed-Q rank-k list, its literal full ordered-prefix
uniqueness, true state mass, and the ordinary full-prefix gate.  This
does not identify the upper H430 selected/inherited owner, or allow a
rank-two slot to pay two U3/U4 arithmetic receipts.  A common SHORT
prefix may have many deeper extensions: uniqueness below concerns an
identical COMPLETE selectedPrefix at a FIXED depth and Q only.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualAllDepthFullPrefix

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQPositionFilterLedger

/-- Actual first-exit list at the specified depth, unchanged ordinary
Rosser policy, true physical Q and literal prime carrier. -/
def actualPhysicalDepthList (k N cap : ℕ) (z0 Q : ℝ)
    (lower : Bool) : List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier k
    (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap 0 z0)

/-- The new depth parameter reduces definitionally to the previously
used actual rank-two list.  No new state semantics are introduced. -/
theorem actual_depth_two_eq_rank_two (N cap : ℕ)
    (z0 Q : ℝ) (lower : Bool) :
    actualPhysicalDepthList 2 N cap z0 Q lower =
      actualPhysicalRankTwoList N cap z0 Q lower := rfl

/-- The complete ordered selected prefixes of the genuine depth-k
list have no duplicates, for EVERY natural k.  This is obtained from
the existing admitted-tuple theorem over the actual Nodup carrier. -/
theorem actual_depth_selected_prefix_nodup
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) :
    ((actualPhysicalDepthList k N cap z0 Q lower).map
      (fun s => s.selectedPrefix)).Nodup := by
  apply List.Nodup.of_map (primeHistoryTuple k)
  simpa only [actualPhysicalDepthList, List.map_map,
    Function.comp_def] using
    (firstExitRootFrontier_admitted_tuple_nodup k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      (roughPrimeUniverse N cap 0 z0)
      (roughPrimeUniverse_nodup N cap 0 z0))

/-- At fixed true Q and depth, equal COMPLETE selected prefixes
necessarily have the same original Fin list position.  This does NOT
identify different complete extensions of the same rank-two prefix. -/
theorem actual_depth_full_prefix_position_unique
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (i j : Fin (actualPhysicalDepthList k N cap z0 Q lower).length)
    (hpre : (actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix =
      (actualPhysicalDepthList k N cap z0 Q lower)[j].selectedPrefix) :
    i = j := by
  let L := actualPhysicalDepthList k N cap z0 Q lower
  have hn : (L.map (fun s => s.selectedPrefix)).Nodup :=
    actual_depth_selected_prefix_nodup k N cap z0 Q lower
  have hi : i.1 < (L.map (fun s => s.selectedPrefix)).length := by
    simpa only [List.length_map] using i.isLt
  have hj : j.1 < (L.map (fun s => s.selectedPrefix)).length := by
    simpa only [List.length_map] using j.isLt
  have heq :
      (L.map (fun s => s.selectedPrefix))[i.1] =
        (L.map (fun s => s.selectedPrefix))[j.1] := by
    simpa only [List.getElem_map] using hpre
  have hij : i.1 = j.1 :=
    (hn.getElem_inj_iff (hi := hi) (hj := hj)).mp heq
  exact Fin.ext hij

/-- Every REAL Fin occurrence with this exact full prefix, without
quotienting by a set of states or original q/tag receivers. -/
def actualDepthFullPrefixPositions
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (pre : List ℕ) :
    Finset (Fin (actualPhysicalDepthList k N cap z0 Q lower).length) :=
  Finset.univ.filter (fun i =>
    (actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix = pre)

/-- An observed full prefix at any depth has exactly the observed
bounded list position.  The witness is a REAL Fin, not an owner axiom. -/
theorem actual_depth_prefix_positions_singleton_of_observed
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (pre : List ℕ)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length)
    (hi : (actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix =
      pre) :
    actualDepthFullPrefixPositions k N cap z0 Q lower pre = {i} := by
  classical
  ext j
  simp only [actualDepthFullPrefixPositions, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    apply actual_depth_full_prefix_position_unique
      k N cap z0 Q lower j i
    exact hj.trans hi.symm
  · intro hj
    subst j
    exact hi

theorem actual_depth_prefix_positions_card_one_of_observed
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (pre : List ℕ)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length)
    (hi : (actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix =
      pre) :
    (actualDepthFullPrefixPositions k N cap z0 Q lower pre).card = 1 := by
  rw [actual_depth_prefix_positions_singleton_of_observed
    k N cap z0 Q lower pre i hi]
  simp

/-- No subsequent position filter can multiply a COMPLETE depth-k
prefix occurrence.  Whether a given upper H430 owner really uses
this depth/position filter remains a separate manuscript obligation. -/
theorem actual_depth_filtered_full_prefix_card_le_one
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (pre : List ℕ)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length)
    (hi : (actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix =
      pre)
    (keep : FirstExitDepthState ℕ → Bool) :
    ((actualDepthFullPrefixPositions k N cap z0 Q lower pre) ∩
      (Finset.univ.filter (fun j :
        Fin (actualPhysicalDepthList k N cap z0 Q lower).length =>
        keep ((actualPhysicalDepthList k N cap z0 Q lower)[j]) = true))).card
      ≤ 1 := by
  have hsub :
      ((actualDepthFullPrefixPositions k N cap z0 Q lower pre) ∩
        (Finset.univ.filter (fun j :
          Fin (actualPhysicalDepthList k N cap z0 Q lower).length =>
          keep ((actualPhysicalDepthList k N cap z0 Q lower)[j]) = true))) ⊆
      actualDepthFullPrefixPositions k N cap z0 Q lower pre :=
    Finset.inter_subset_left
  have hcard := Finset.card_le_card hsub
  rw [actual_depth_prefix_positions_card_one_of_observed
    k N cap z0 Q lower pre i hi] at hcard
  exact hcard

/-- The *existing* complete-prefix ordinary Rosser policy is passed
by every genuine positive-depth frontier state; this binds a real
gate at arbitrary depth.  It is NOT the additional manuscript
full/selected/inherited count gate. -/
theorem actual_depth_ordinary_full_prefix_passes
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (hk : 0 < k)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length) :
    actualFullPrefixGate lower Q
      ((actualPhysicalDepthList k N cap z0 Q lower)[i]) = true := by
  have hm :
      (actualPhysicalDepthList k N cap z0 Q lower)[i] ∈
        firstExitDepthFrontier k
          (ordinaryRosserRetainedPolicy lower Q)
          (fun r : ℕ => 1 / ((r : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap 0 z0) := by
    have hmem :
        (actualPhysicalDepthList k N cap z0 Q lower)[i] ∈
          actualPhysicalDepthList k N cap z0 Q lower :=
      List.getElem_mem
    simpa only [actualPhysicalDepthList] using hmem
  have hv := mem_firstExitDepthFrontier_ordinaryRosser_admissible_of_pos
    lower Q k hk
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z0)
    ((actualPhysicalDepthList k N cap z0 Q lower)[i]) hm
  exact decide_eq_true hv

/-- The full ordinary Rosser PREFIX gate removes no actual rank-k
position.  This does not say the later selected/inherited count tests
remove none. -/
theorem actual_depth_full_prefix_keeps_all
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (hk : 0 < k) :
    (Finset.univ.filter (fun i :
        Fin (actualPhysicalDepthList k N cap z0 Q lower).length =>
        actualFullPrefixGate lower Q
          ((actualPhysicalDepthList k N cap z0 Q lower)[i]) = true)) =
      Finset.univ := by
  classical
  ext i
  have hi := actual_depth_ordinary_full_prefix_passes
    k N cap z0 Q lower hk i
  simp [hi]

/-- The REAL mass of a depth-k list state equals its ordered prime
reciprocal-product, not an invented root count or q-dependent weight. -/
theorem actual_depth_state_mass_eq_prefix_product
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (i : Fin (actualPhysicalDepthList k N cap z0 Q lower).length) :
    (actualPhysicalDepthList k N cap z0 Q lower)[i].mass =
      ((actualPhysicalDepthList k N cap z0 Q lower)[i].selectedPrefix.map
        (fun r : ℕ => 1 / ((r : ℝ) - 1))).prod := by
  have hm :
      (actualPhysicalDepthList k N cap z0 Q lower)[i] ∈
        firstExitDepthFrontier k
          (ordinaryRosserRetainedPolicy lower Q)
          (fun r : ℕ => 1 / ((r : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap 0 z0) := by
    have hmem :
        (actualPhysicalDepthList k N cap z0 Q lower)[i] ∈
          actualPhysicalDepthList k N cap z0 Q lower :=
      List.getElem_mem
    simpa only [actualPhysicalDepthList] using hmem
  exact mem_firstExitDepthFrontier_mass_eq_selected_prod k
    (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z0)
    ((actualPhysicalDepthList k N cap z0 Q lower)[i]) hm

/-- Exact native depth-k historical mass reindexing to the original
admitted tuples at this physical Q.  This is the fixed existing
first-exit recursion, not the complete selected U3/U4 count source
and not a paid signed Euler first-excluded term. -/
theorem actual_depth_mass_sum_eq_admitted_tuples
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (F : List ℕ → ℝ) :
    ((actualPhysicalDepthList k N cap z0 Q lower).map (fun s =>
      s.mass * F s.selectedPrefix)).sum =
      ∑ p ∈ firstExitAdmittedTuples k
          (ordinaryRosserRetainedPolicy lower Q)
          (roughPrimeUniverse N cap 0 z0),
        (∏ j, 1 / ((p j : ℝ) - 1)) * F (List.ofFn p).reverse := by
  have hbase := firstExitRootFrontier_history_sum_eq_admitted_tuple_sum
    k (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z0)
    (roughPrimeUniverse_nodup N cap 0 z0) F
  rw [← hbase]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hm : s.mass =
      (s.selectedPrefix.map (fun r : ℕ => 1 / ((r : ℝ) - 1))).prod :=
    mem_firstExitDepthFrontier_mass_eq_selected_prod k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      (roughPrimeUniverse N cap 0 z0) s
      (by simpa only [actualPhysicalDepthList] using hs)
  rw [hm]

end
end ImbalancedChen.Part5OriginalH430ActualAllDepthFullPrefix
