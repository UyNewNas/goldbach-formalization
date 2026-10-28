import ImbalancedChen.P2ActualPairPlanRawSupport
import ImbalancedChen.P2OriginalCanonicalPairTentBank

/-!
# First decision disagreement in the actual warm CapPlan trace

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The compared executions are the actual original integer-retention run,
with the same stored pair root, current admission BEFORE the next freeze,
and the actual finite incomingCode lookup at full ranks 3,4,5. There is no
assumed successful selector or mixed-fibre wall cover. The final theorem
specializes to the independently constructed canonical TENT subbank;
it does not identify that bank with the missing complete W/adopted L56.
-/

namespace ImbalancedChen.P2ActualWarmDecisionDivergence

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2LowerIntegerRetainedSupport

/-- Public prefix-acceptance interface, including zero/one/two rough slots.
No extra first square is introduced at the marked pair root. -/
theorem run_take_accepted {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (H : Trace) (xs : List ℝ)
    (h : (run P a b H xs).accepted = true) (j : ℕ) :
    (run P a b H (xs.take j)).accepted = true := by
  have h' : (run P a b H (xs.take j ++ xs.drop j)).accepted = true := by
    simpa only [List.take_append_drop] using h
  rw [run_append] at h'
  exact run_accepted_incoming P a b _ _ h'

/-- Actual retained arithmetic words supply every physical prefix, in its
canonical chronological order. Later slots cannot undo a previous test. -/
theorem raw_canonical_prefix_accepted {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N enum : ℕ)
    (p : ℕ × ℕ) (z0 z : ℝ) {r : ℕ}
    (hr : r ∈ P2LowerFiniteCellRounding.rawSupport
      (pairPolicy P a b seed N p) N enum z0 z) (j : ℕ) :
    (run P a b (pairRoot N p seed)
      ((r.primeFactorsList.reverse.take j).map (coordinate N))).accepted = true := by
  have hc := (P2ActualPairPlanRawSupport.pair_raw_iff_canonical_warm
    P a b seed N enum p z0 z r).mp hr
  have hrun : (run P a b (pairRoot N p seed)
      (r.primeFactorsList.reverse.map (coordinate N))).accepted = true := by
    simpa only [pairPolicy, warmRetain, warmTrace, physicalWord] using hc.2
  simpa only [List.map_take] using run_take_accepted P a b _ _ hrun j

private theorem coded_getD (a b : ℝ) (mesh : ℕ) (xs : List ℝ) (j : ℕ) :
    let p := (marked xs).getD j (b, false)
    (exponentCode a b mesh p.1, p.2) =
      ((xs.map (exponentCode a b mesh)).getD j (exponentCode a b mesh b), false) := by
  induction xs generalizing j with
  | nil => simp [marked]
  | cons x xs ih =>
      cases j with
      | zero => simp [marked]
      | succ j => simpa only [marked, List.map_cons, List.getD_cons_succ] using ih j

/-- The actual code reader depends only on these finite coordinate codes.
Marks remain the literal unselected marks of the own-lower run. -/
theorem incomingCode_eq_of_coordinate_codes {depth mesh rank : ℕ}
    (a b : ℝ) (xs ys : List ℝ)
    (h : xs.map (exponentCode a b mesh) = ys.map (exponentCode a b mesh)) :
    incomingCode a b depth mesh rank (marked xs) =
      incomingCode a b depth mesh rank (marked ys) := by
  have ht : (xs.take rank).map (exponentCode a b mesh) =
      (ys.take rank).map (exponentCode a b mesh) := by
    simpa only [List.map_take] using congrArg (List.take rank) h
  unfold incomingCode
  simp only [marked, ← List.map_take]
  change physicalCode a b depth mesh (marked (xs.take rank)) =
    physicalCode a b depth mesh (marked (ys.take rank))
  funext i
  change (exponentCode a b mesh
      (((marked (xs.take rank)).getD i.val (b, false)).1),
      ((marked (xs.take rank)).getD i.val (b, false)).2) = _
  rw [coded_getD, coded_getD, ht]

/-- All SourceForm screening, tie order, fresh/inherit choices and stored
cap values in a fixed finite plan agree when their REAL code inputs agree.
This includes full ranks four and five, with no ideal-parent reset. -/
theorem planChoice_eq_of_coordinate_codes {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b : ℝ) (xs ys : List ℝ)
    (hlen : xs.length = ys.length)
    (hcodes : xs.map (exponentCode a b mesh) = ys.map (exponentCode a b mesh)) :
    planChoice P a b xs = planChoice P a b ys := by
  unfold planChoice
  rw [hlen]
  split_ifs
  · unfold incomingChoice
    rw [incomingCode_eq_of_coordinate_codes a b xs ys hcodes]
  · rfl

/-- A literal first-disagreement witness. Both traces have the SAME actual
incoming cap and acceptance status at the witnessed prefix. Either the
finite lookup changes or the current admission changes; no final cover is
assumed. The code choice is computed only AFTER that current admission. -/
theorem run_disagreement_first_decision {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b : ℝ) (xs ys : List ℝ)
    (hlen : xs.length = ys.length) :
    ∀ H K : Trace, H.cap = K.cap → H.accepted = K.accepted →
      (run P a b H xs).accepted ≠ (run P a b K ys).accepted →
      ∃ j : ℕ, j < xs.length ∧
        let A := run P a b H (xs.take j)
        let B := run P a b K (ys.take j)
        let x := xs.getD j 0
        let y := ys.getD j 0
        A.cap = B.cap ∧ A.accepted = B.accepted ∧
          (planChoice P a b (A.word ++ [x]) ≠ planChoice P a b (B.word ++ [y]) ∨
            ¬ (admission A x ↔ admission B y)) := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      intro H K hcap hacc hneq
      exact (hneq hacc).elim
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          intro H K hcap hacc hneq
          by_cases hc : planChoice P a b (H.word ++ [x]) =
              planChoice P a b (K.word ++ [y])
          · by_cases ha : admission H x ↔ admission K y
            · have hcap' : (step P a b H x).cap = (step P a b K y).cap := by
                simp only [step, hc, hcap]
              have hacc' : (step P a b H x).accepted = (step P a b K y).accepted := by
                simp only [step, hacc, ha]
              have hn : (run P a b (step P a b H x) xs).accepted ≠
                  (run P a b (step P a b K y) ys).accepted := hneq
              obtain ⟨j, hj, hw⟩ := ih ys (by simpa using hlen)
                (step P a b H x) (step P a b K y) hcap' hacc' hn
              refine ⟨j + 1, by simpa using Nat.succ_lt_succ hj, ?_⟩
              simpa only [List.take_succ_cons, List.getD_cons_succ,
                run, List.foldl_cons] using hw
            · exact ⟨0, by simp, by simpa only [List.take_zero, List.getD_cons_zero,
                run, List.foldl_nil] using And.intro hcap (And.intro hacc (Or.inr ha))⟩
          · exact ⟨0, by simp, by simpa only [List.take_zero, List.getD_cons_zero,
              run, List.foldl_nil] using And.intro hcap (And.intro hacc (Or.inl hc))⟩

/-- A changed actual admission with the same frozen parent is quantitatively
near the true even-cube wall. Odd ranks bypass and cannot be the witness. -/
theorem admission_disagreement_wall (H K : Trace) (x y tau : ℝ) (j : ℕ)
    (htau : 0 ≤ tau) (hlen : H.word.length = K.word.length)
    (hpos : 0 < H.word.length) (hcap : H.cap = K.cap)
    (hsum : |H.word.sum - K.word.sum| ≤ (j : ℝ) * tau)
    (hxy : |x - y| ≤ tau) (ha : ¬ (admission H x ↔ admission K y)) :
    (H.word.length + 1) % 2 = 0 ∧
      |H.word.sum + 3 * x - H.cap| ≤ ((j : ℝ) + 3) * tau := by
  have hn : H.word.length ≠ 0 := by omega
  have hkn : K.word.length ≠ 0 := by omega
  have he : (H.word.length + 1) % 2 = 0 := by
    by_contra he
    have hke : (K.word.length + 1) % 2 ≠ 0 := by simpa only [← hlen] using he
    exact ha (by simp only [admission, if_neg hn, if_neg hkn, if_neg he, if_neg hke])
  have hke : (K.word.length + 1) % 2 = 0 := by simpa only [← hlen] using he
  have hd : ¬ (H.word.sum + 3 * x < H.cap ↔ K.word.sum + 3 * y < H.cap) := by
    simpa only [admission, if_neg hn, if_neg hkn, if_pos he, if_pos hke, ← hcap] using ha
  obtain ⟨hsl, hsu⟩ := abs_le.mp hsum
  obtain ⟨hxl, hxu⟩ := abs_le.mp hxy
  refine ⟨he, abs_le.mpr ?_⟩
  by_cases hx : H.word.sum + 3 * x < H.cap
  · have hy : ¬ K.word.sum + 3 * y < H.cap := fun hy => hd (iff_of_true hx hy)
    have hy' := le_of_not_gt hy
    constructor <;> nlinarith
  · have hy : K.word.sum + 3 * y < H.cap := by
      by_contra hy
      exact hd (iff_of_false hx hy)
    have hx' := le_of_not_gt hx
    constructor <;> nlinarith

/-- The independently built tent bank is the actual plan in this instance.
There is no CandidateBank or selector-success input and no full-W claim. -/
theorem canonical_tent_run_disagreement
    (R : P2OriginalPairSourceReceiver.PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (N : ℕ) (p : ℕ × ℕ) (xs ys : List ℝ) (hlen : xs.length = ys.length)
    (hneq : (run (P2OriginalCanonicalPairTentBank.plan R mesh buffer seed)
      R.epsilon P2OriginalPairSourceReceiver.ceiling (pairRoot N p seed) xs).accepted ≠
      (run (P2OriginalCanonicalPairTentBank.plan R mesh buffer seed)
        R.epsilon P2OriginalPairSourceReceiver.ceiling (pairRoot N p seed) ys).accepted) :
    ∃ j : ℕ, j < xs.length ∧
      let P := P2OriginalCanonicalPairTentBank.plan R mesh buffer seed
      let a : ℝ := R.epsilon
      let b : ℝ := P2OriginalPairSourceReceiver.ceiling
      let A := run P a b (pairRoot N p seed) (xs.take j)
      let B := run P a b (pairRoot N p seed) (ys.take j)
      let x := xs.getD j 0
      let y := ys.getD j 0
      A.cap = B.cap ∧ A.accepted = B.accepted ∧
        (planChoice P a b (A.word ++ [x]) ≠ planChoice P a b (B.word ++ [y]) ∨
          ¬ (admission A x ↔ admission B y)) := by
  exact run_disagreement_first_decision _ _ _ xs ys hlen _ _ rfl rfl hneq

end
end ImbalancedChen.P2ActualWarmDecisionDivergence
