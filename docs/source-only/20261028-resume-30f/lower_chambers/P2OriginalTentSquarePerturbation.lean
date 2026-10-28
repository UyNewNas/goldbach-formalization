import ImbalancedChen.P2OriginalPairSourceReceiver

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Whole-box upper endpoints inflate the two ORIGINAL square systems by at
most (rank+1)*step. The selected initial product is not reset to zero: its
own selected-coordinate perturbation is included before the remaining word.
These are the finite exponent inequalities needed for ideal tent points to
enter the concrete source screen; no sourceCheck is assumed.
-/

namespace ImbalancedChen.P2OriginalTentSquarePerturbation

noncomputable section
open scoped Classical
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (strictSquareGates)

def slotStep (h : ℝ) (p q : Slot) : Prop :=
  q.exponent ≤ p.exponent + h ∧ p.selected = q.selected

private theorem sum_step {h : ℝ} {xs ys : List ℝ}
    (hxy : List.Forall₂ (fun x y => y ≤ x + h) xs ys) :
    ys.sum ≤ xs.sum + xs.length * h := by
  induction hxy with
  | nil => simp
  | @cons x y xs ys hxy ht ih =>
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

private theorem words_step {h : ℝ} {xs ys : List Slot}
    (hxy : List.Forall₂ (slotStep h) xs ys) :
    List.Forall₂ (fun x y => y ≤ x + h) (xs.map Slot.exponent) (ys.map Slot.exponent) ∧
    List.Forall₂ (fun x y => y ≤ x + h) (selectedWord xs) (selectedWord ys) ∧
    List.Forall₂ (fun x y => y ≤ x + h) (remainingWord xs) (remainingWord ys) := by
  induction hxy with
  | nil => exact ⟨.nil, .nil, .nil⟩
  | @cons p q xs ys hp ht ih =>
      have hf := List.Forall₂.cons hp.1 ih.1
      by_cases hs : p.selected = true
      · have hq : q.selected = true := hp.2 ▸ hs
        exact ⟨hf, by simpa [selectedWord, hs, hq] using List.Forall₂.cons hp.1 ih.2.1,
          by simpa [remainingWord, hs, hq] using ih.2.2⟩
      · have hq : q.selected ≠ true := by intro hq; exact hs (hp.2.trans hq)
        exact ⟨hf, by simpa [selectedWord, hs, hq] using ih.2.1,
          by simpa [remainingWord, hs, hq] using List.Forall₂.cons hp.1 ih.2.2⟩

private theorem partition_length (xs : List Slot) :
    (selectedWord xs).length + (remainingWord xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      by_cases hp : p.selected = true <;>
        simp [selectedWord, remainingWord, hp] at * <;> omega

private theorem squares_step {h cap T U cap' : ℝ} {xs ys : List ℝ}
    (hh : 0 ≤ h) (k : ℕ)
    (hxy : List.Forall₂ (fun x y => y ≤ x + h) xs ys)
    (hTU : U ≤ T + k * h)
    (hcap : cap + (k + xs.length + 1 : ℕ) * h ≤ cap')
    (hsq : strictSquareGates cap T xs) : strictSquareGates cap' U ys := by
  induction hxy generalizing T U k with
  | nil => trivial
  | @cons x y xs ys hxy ht ih =>
      have hk : ((k + 2 : ℕ) : ℝ) ≤ (k + (x :: xs).length + 1 : ℕ) := by
        exact_mod_cast (show k + 2 ≤ k + (x :: xs).length + 1 by simp; omega)
      have hhead : U + 2 * y < cap' := by
        have hbudget := mul_le_mul_of_nonneg_right hk hh
        have hroot := hsq.1
        push_cast at *
        linarith
      refine ⟨hhead, ?_⟩
      apply ih (k + 1)
      · push_cast
        linarith
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcap
      · exact hsq.2

-- At most five prefix slots produce the exact six-step upper-bound cost
-- in BOTH full and selected-complement tests. Original tags are preserved.
theorem full_and_selected_squares_step
    (h cap cap' : ℝ) (hh : 0 ≤ h) (xs ys : List Slot)
    (hxy : List.Forall₂ (slotStep h) xs ys) (hlen : xs.length ≤ 5)
    (hcap : cap + 6 * h ≤ cap')
    (hfull : strictSquareGates cap 0 (xs.map Slot.exponent))
    (hselected : strictSquareGates cap (selectedWord xs).sum (remainingWord xs)) :
    strictSquareGates cap' 0 (ys.map Slot.exponent) ∧
      strictSquareGates cap' (selectedWord ys).sum (remainingWord ys) := by
  have hw := words_step hxy
  have hpart := partition_length xs
  constructor
  · apply squares_step hh 0 hw.1 (by simp)
    · have hn : (((0 + (xs.map Slot.exponent).length + 1 : ℕ) : ℝ)) ≤ 6 := by
        exact_mod_cast (show 0 + (xs.map Slot.exponent).length + 1 ≤ 6 by simpa using Nat.add_le_add_right hlen 1)
      exact (add_le_add_left (mul_le_mul_of_nonneg_right hn hh) cap).trans hcap
    · exact hfull
  · apply squares_step hh (selectedWord xs).length hw.2.2 (sum_step hw.2.1)
    · have hn : ((((selectedWord xs).length + (remainingWord xs).length + 1 : ℕ) : ℝ)) ≤ 6 := by
        exact_mod_cast (show (selectedWord xs).length + (remainingWord xs).length + 1 ≤ 6 by omega)
      exact (add_le_add_left (mul_le_mul_of_nonneg_right hn hh) cap).trans hcap
    · exact hselected

-- Reverse transport costs zero: the actual screen at upper endpoints
-- licenses every smaller physical point with exactly the same stored tags.
-- This works at all ranks, including codeAt's padded future coordinates.
theorem sourceCheck_point_squares_upper
    (R : P2OriginalPairSourceReceiver.PairRange) {mesh : ℕ}
    (code : P2OriginalLowerSelectedCapConstructor.Code mesh) (rank : Fin 6)
    (buffer : ℚ) (branch : P2OriginalLowerWholeBoxBranchSelect.SelectedBranchData)
    (x : Fin 5 → ℝ)
    (hupper : ∀ i, x i ≤ (P2OriginalPairSourceReceiver.qHi R mesh (code i).1 : ℝ))
    (hsource : P2OriginalPairSourceReceiver.sourceCheck R rank code buffer branch) :
    strictSquareGates (P2OriginalPairSourceReceiver.rowCap R code buffer branch : ℝ) 0
        ((P2OriginalPairSourceReceiver.pointSlots rank code branch.form.supportMask x).map Slot.exponent) ∧
      strictSquareGates (P2OriginalPairSourceReceiver.rowCap R code buffer branch : ℝ)
        (selectedWord (P2OriginalPairSourceReceiver.pointSlots rank code branch.form.supportMask x)).sum
        (remainingWord (P2OriginalPairSourceReceiver.pointSlots rank code branch.form.supportMask x)) := by
  let xs := P2OriginalPairSourceReceiver.ownSlots R rank code branch.form.supportMask
  let ys := P2OriginalPairSourceReceiver.pointSlots rank code branch.form.supportMask x
  have hslots : List.Forall₂ (slotStep 0) xs ys := by
    fin_cases rank <;>
      simp [xs, ys, P2OriginalPairSourceReceiver.ownSlots,
        P2OriginalPairSourceReceiver.pointSlots, slotStep,
        P2OriginalPairSourceReceiver.ownSlot, P2OriginalPairSourceReceiver.pointSlot, hupper]
  have hlen : xs.length ≤ 5 := by
    simp only [xs, P2OriginalPairSourceReceiver.ownSlots, List.length_take,
      List.length_cons, List.length_nil]
    exact min_le_right _ _
  exact full_and_selected_squares_step 0 _ _ (le_refl 0) xs ys hslots hlen
    (by simp) hsource.2.2.1 hsource.2.2.2.1

theorem sourceCheck_point_squares
    (R : P2OriginalPairSourceReceiver.PairRange) {mesh : ℕ}
    (code : P2OriginalLowerSelectedCapConstructor.Code mesh) (rank : Fin 6)
    (buffer : ℚ) (branch : P2OriginalLowerWholeBoxBranchSelect.SelectedBranchData)
    (x : Fin 5 → ℝ)
    (hx : P2OriginalLowerBufferedAffineBoxes.inBox
      (P2OriginalPairSourceReceiver.box R code) x)
    (hsource : P2OriginalPairSourceReceiver.sourceCheck R rank code buffer branch) :
    strictSquareGates (P2OriginalPairSourceReceiver.rowCap R code buffer branch : ℝ) 0
        ((P2OriginalPairSourceReceiver.pointSlots rank code branch.form.supportMask x).map Slot.exponent) ∧
      strictSquareGates (P2OriginalPairSourceReceiver.rowCap R code buffer branch : ℝ)
        (selectedWord (P2OriginalPairSourceReceiver.pointSlots rank code branch.form.supportMask x)).sum
        (remainingWord (P2OriginalPairSourceReceiver.pointSlots rank code branch.form.supportMask x)) := by
  apply sourceCheck_point_squares_upper R code rank buffer branch x _ hsource
  intro i
  simpa [P2OriginalPairSourceReceiver.box] using (hx i).2

end
end ImbalancedChen.P2OriginalTentSquarePerturbation
