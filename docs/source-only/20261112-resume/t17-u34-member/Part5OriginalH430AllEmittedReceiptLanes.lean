import ImbalancedChen.Part5OriginalH430SelectedMemberFixedQuery

/-! Every remaining generation of the real 430-request history, including
seed, exterior, retention and Buchstab. A zero resolver value is not an
arithmetic zero. The original unfiltered count has an explicit complement. -/
namespace ImbalancedChen.Part5OriginalH430AllEmittedReceiptLanes
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter (iterate roundDecision Choice)
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2FrozenReceiverCountActions (frozenCount)
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430SameQHistoryCells Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430SelectedMemberBox

inductive Lane where
  | seed | outside | retained | buchstab | bank (slot : Fin 106)
  deriving DecidableEq, Fintype

def laneAt (G : ℕ) (r : Request) : Lane :=
  match G with
  | 0 => .seed
  | g+1 => match resolve (g+1) r with
    | none => .outside
    | some i => match (roundDecision (iterate g) r.node.upper i).choice with
      | .retained => .retained
      | .buchstab => .buchstab
      | .bank slot => .bank slot

def allPositions (N n mesh : ℕ) (k : Root) (t : ℝ) (p : ℕ) (G : Fin 431)
    (key : Box mesh × Lane) : Finset (LevelIndex N n k t p G.val) :=
  Finset.univ.filter (fun l =>
    (atBox mesh l, laneAt G.val (levelOccurrence l).current) = key)

/-- Exhaust each real level EXACTLY once in its finite labelled Member
boxes. This includes seed/exterior positions with a positive true count.
A complete U3/U4 selection can only drop the last summand after proving
a separate estimate or an exact cancellation appropriate to the action. -/
theorem all_emitted_original_receipts_plus_rejected
    {N n m : ℕ} (mesh : ℕ) (k : Root) {t : ℝ} (G : Fin 431) (c : RootKey n m)
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    let Q := cellQ N n c.1
    (∑ p ∈ rootFibre N n m k t c, ∑ l : LevelIndex N n k t p G.val,
      levelMark l * (frozenCount N (parentProduct (levelOccurrence l).current.old)
        (receiver N) (memberCutoff Q (levelOccurrence l)) : ℝ)) =
    ∑ key : Box mesh × Lane, ∑ p ∈ rootFibre N n m k t c,
      ∑ l ∈ allPositions N n mesh k t p G key,
        levelMark l *
          (((originalReceiptLane N p (tailProduct (levelOccurrence l))
                (memberCutoff Q (levelOccurrence l))).card : ℝ) +
           ((rejectedChild N (parentProduct (levelOccurrence l).current.old)
                (tailProduct (levelOccurrence l)) (memberCutoff Q (levelOccurrence l))).card : ℝ)) := by
  dsimp only
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Box mesh × Lane)))]
  apply Finset.sum_congr rfl
  intro p hp
  let F := fun l : LevelIndex N n k t p G.val =>
    levelMark l * (((originalReceiptLane N p (tailProduct (levelOccurrence l))
        (memberCutoff (cellQ N n c.1) (levelOccurrence l))).card : ℝ) +
      ((rejectedChild N (parentProduct (levelOccurrence l).current.old)
        (tailProduct (levelOccurrence l)) (memberCutoff (cellQ N n c.1) (levelOccurrence l))).card : ℝ))
  calc
    _ = ∑ l : LevelIndex N n k t p G.val, F l := by
      apply Finset.sum_congr rfl
      intro l _
      exact congrArg (fun x : ℝ => levelMark l * x)
        (actual_member_count_split hN ht hu hn hp (levelOccurrence_source l).1)
    _ = _ := (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (LevelIndex N n k t p G.val))) (t := Finset.univ)
      (g := fun l => (atBox mesh l, laneAt G.val (levelOccurrence l).current))
      (fun _ _ => Finset.mem_univ _) F).symm

end
end ImbalancedChen.Part5OriginalH430AllEmittedReceiptLanes
