import ImbalancedChen.Part5OriginalH430ExactOuterQ80FloorCredit

/-!
P5.6 / h34: decompose the ACTUAL selected W1/W2 positive anchor
defects into a zero-generation seed defect and the downward variation
of the ORIGINAL integer Q80 upper-table iteration.

Unlike the earlier maximum-of-82 and selected-action payment packets,
this proves a time-recursive upper bound, not a new free error parameter.
Every backward step uses the exact iterate k and iterate (k+1),
at the SAME original fixed-cell endpoint. W2 has the original 4:1
endpoint mixture. The final payment retains every selected Fin occurrence,
its true same-Q Theta/mark and the original 430-generation root.

The final root inequality additionally combines the COMPLETE capped
integer-floor credit (per-product and outer quotient) with the selected
anchor split; earlier root bounds used only the first floor credit.
No monotonicity or smallness of the Q80 iteration is presumed.
Full CLOSED-CELL, seed, Buchstab, native count, PP/same-rho and causal
430+11 refinement remain OPEN. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430SelectedAnchorBackwardVariation

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430TrueBankFeedbackFloorCredit
open Part5OriginalH430ClosedCellPositivePrefloor
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430SelectedPositiveAnchorPayment
open Part5OriginalH430ExactOuterQ80FloorCredit

/-- The first ORIGINAL table generation. It is not the terminal
generation and contains no invented prime-history occurrence. -/
def firstOriginalGeneration : Fin 430 := ⟨0, by decide⟩

/-- Downward motion of one ORIGINAL Q80 upper-table cell between two
consecutive literal iterates. Negative motion is never charged. -/
def actualUpperCellDrop (k : ℕ) (i : Fin 200) : ℝ :=
  max 0 (floorValue (iterate k true) i -
    floorValue (iterate (k+1) true) i)

/-- Each action sees only its original fixed endpoints. In particular
W2 preserves the actual 4:1 weighting rather than paying both in full. -/
def actionBackwardDrop (k : ℕ) : Original106Action → ℝ
  | .inl ij => actualUpperCellDrop k (w1Cell ij.2)
  | .inr j => (4 * actualUpperCellDrop k (w2Cell j true) +
      actualUpperCellDrop k (w2Cell j false)) / 5

/-- Exact prefix of the predecessor-table backward variation, with no
free delta and no extra generation-430 transition. -/
def actionCumulativeBackwardDrop (g : Fin 430)
    (a : Original106Action) : ℝ :=
  ∑ k ∈ Finset.range g.val, actionBackwardDrop k a

/-- Elementary temporal positive-part bound. This lemma cannot claim
the original Q80 table is monotone: it pays EVERY actual downward step. -/
private theorem clipped_gap_le_seed_plus_drops
    (f : ℕ → ℝ) (z : ℝ) (m : ℕ) :
    max 0 (z - f m) ≤
      max 0 (z - f 0) +
        ∑ k ∈ Finset.range m, max 0 (f k - f (k+1)) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hstep :
          max 0 (z - f (m+1)) ≤
            max 0 (z - f m) + max 0 (f m - f (m+1)) := by
        have hx0 : 0 ≤ max 0 (z - f m) := le_max_left _ _
        have hy0 : 0 ≤ max 0 (f m - f (m+1)) := le_max_left _ _
        have hx : z - f m ≤ max 0 (z - f m) := le_max_right _ _
        have hy : f m - f (m+1) ≤
            max 0 (f m - f (m+1)) := le_max_right _ _
        apply max_le
        · linarith only [hx0, hy0]
        · linarith only [hx, hy]
      calc
        max 0 (z - f (m+1)) ≤
            max 0 (z - f m) + max 0 (f m - f (m+1)) := hstep
        _ ≤ max 0 (z - f 0) +
            (∑ k ∈ Finset.range m, max 0 (f k - f (k+1))) +
              max 0 (f m - f (m+1)) := by
                linarith only [ih]
        _ = max 0 (z - f 0) +
            ∑ k ∈ Finset.range (m+1), max 0 (f k - f (k+1)) := by
              rw [Finset.sum_range_succ]
              ring

/-- Genuine selected-action endpoint debt is bounded by the SAME
action's seed endpoint debt plus its ACTUAL Q80 backward variation.
No monotonicity, fresh smallness hypothesis or fictitious cell owner. -/
theorem selected_action_anchor_le_seed_plus_variation
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ) :
    actionPositiveAnchorAllowance g F a ≤
      actionPositiveAnchorAllowance firstOriginalGeneration F a +
        actionCumulativeBackwardDrop g a := by
  rcases a with ⟨i, j⟩ | j
  · have h := clipped_gap_le_seed_plus_drops
      (fun k : ℕ => floorValue (iterate k true) (w1Cell j))
      (F (W1Anchor j)) g.val
    simpa [actionPositiveAnchorAllowance, firstOriginalGeneration,
      actionCumulativeBackwardDrop, actionBackwardDrop,
      actualUpperCellDrop, precedingH] using h
  · have h0 := clipped_gap_le_seed_plus_drops
      (fun k : ℕ => floorValue (iterate k true) (w2Cell j true))
      (F (originalW2At j).s0) g.val
    have h1 := clipped_gap_le_seed_plus_drops
      (fun k : ℕ => floorValue (iterate k true) (w2Cell j false))
      (F (originalW2At j).phi1) g.val
    have hsum :
        (∑ k ∈ Finset.range g.val,
          (4 * actualUpperCellDrop k (w2Cell j true) +
            actualUpperCellDrop k (w2Cell j false)) / 5) =
          (4 * (∑ k ∈ Finset.range g.val,
              actualUpperCellDrop k (w2Cell j true)) +
            (∑ k ∈ Finset.range g.val,
              actualUpperCellDrop k (w2Cell j false))) / 5 := by
      calc
        _ = ∑ k ∈ Finset.range g.val,
            ((4/5 : ℝ) * actualUpperCellDrop k (w2Cell j true) +
              (1/5 : ℝ) * actualUpperCellDrop k (w2Cell j false)) := by
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = (4 * (∑ k ∈ Finset.range g.val,
              actualUpperCellDrop k (w2Cell j true)) +
            (∑ k ∈ Finset.range g.val,
              actualUpperCellDrop k (w2Cell j false))) / 5 := by
                simp only [Finset.sum_add_distrib, Finset.mul_sum]
                ring
    have hineq :
        (4 * max 0 (F (originalW2At j).s0 -
              floorValue (iterate g.val true) (w2Cell j true)) +
          max 0 (F (originalW2At j).phi1 -
              floorValue (iterate g.val true) (w2Cell j false))) / 5 ≤
        (4 * max 0 (F (originalW2At j).s0 -
              floorValue (iterate 0 true) (w2Cell j true)) +
          max 0 (F (originalW2At j).phi1 -
              floorValue (iterate 0 true) (w2Cell j false))) / 5 +
        (∑ k ∈ Finset.range g.val,
          (4 * actualUpperCellDrop k (w2Cell j true) +
            actualUpperCellDrop k (w2Cell j false)) / 5) := by
      rw [hsum]
      simp only [actualUpperCellDrop] at h0 h1 ⊢
      linarith only [h0, h1]
    simpa [actionPositiveAnchorAllowance, firstOriginalGeneration,
      actionCumulativeBackwardDrop, actionBackwardDrop,
      precedingH] using hineq

/-- Seed-anchor charges at the CURRENT genuine selected Fin positions
and with their CURRENT true parent Theta and original positive marks.
This does not replace the actual terminal generation-zero seed. -/
def bankSelectedSeedAnchorPayment (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        actionPositiveAnchorAllowance firstOriginalGeneration F a

/-- True Q80 downward-variation charge on the SAME selected paths,
without deduplicating occurrences or using scalar closed-min ownership. -/
def bankSelectedBackwardVariationPayment (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        actionCumulativeBackwardDrop g a

/-- At the real selected Fin locations, all anchor loss is charged either
to the literal zero-iterate anchor mismatch or to an ACTUAL earlier Q80
table decrease at that endpoint. Both charges use the same occurrence. -/
theorem selected_anchor_payment_le_seed_plus_backward_variation
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankSelectedPositiveAnchorPayment N n root tau p g F ≤
      bankSelectedSeedAnchorPayment N n root tau p g F +
        bankSelectedBackwardVariationPayment N n root tau p g := by
  unfold bankSelectedPositiveAnchorPayment
    bankSelectedSeedAnchorPayment bankSelectedBackwardVariationPayment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  have hs := occurrenceScale_nonneg N n root tau p g l
    hN ht ht' hn hp hband
  have hpoint := selected_action_anchor_le_seed_plus_variation g a F
  have hweighted := mul_le_mul_of_nonneg_left hpoint hs
  simpa only [mul_add] using hweighted

/-- The root uses BOTH true integer floors and the actual Q80 temporal
anchor decomposition at once. All other original manuscript-local debts
remain visible, especially the UNPROVED predecessor CLOSED-CELL premise.
No original U3/U4 count identity or h34 closing input is presumed. -/
theorem frozen_root_le_seed_and_backward_variation_with_complete_floor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430, bankCompleteFloorCredit N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedSeedAnchorPayment N n root tau p g F +
            bankSelectedBackwardVariationPayment N n root tau p g) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_prefloor_with_complete_credit
    N n root tau p hN ht ht' hn hp hband
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPreFloorIdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g)) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedSeedAnchorPayment N n root tau p g F +
            bankSelectedBackwardVariationPayment N n root tau p g) +
          bankPhysicalAppliedAbs N n root tau p g) := by
    apply Finset.sum_le_sum
    intro g _
    have h0 := bank_prefloor_le_closed_cell_positive
      N n root tau p g F hN ht ht' hn hp hband (hclosed g)
    have h1 := (bank_closed_cell_positive_sandwich
      N n root tau p g F hN ht ht' hn hp hband (hclosed g)).2
    have h2 := bankFixedSlackMass_le_selectedPositiveAnchorPayment
      N n root tau p g F hN ht ht' hn hp hband
    have h3 := selected_anchor_payment_le_seed_plus_backward_variation
      N n root tau p g F hN ht ht' hn hp hband
    linarith only [h0, h1, h2, h3]
  exact hroot.trans (add_le_add_left hlevels _)

end
end ImbalancedChen.Part5OriginalH430SelectedAnchorBackwardVariation
