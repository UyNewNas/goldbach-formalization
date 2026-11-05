import ImbalancedChen.P1Pair12RetainedSignedSource

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Finite stopped-tree accounting. Policy agreement is required on actual
extensions of the starting prefix; agreement at the starting node alone
would not suffice. The terminal remains arbitrary and nonmultiplicative.
The finite owner partition preserves LIST occurrences, including duplicates.
-/
namespace ImbalancedChen.P1SignedDescendantAccounting
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource

/-- The prefix is already selected. Only decisions on its descendants can
change its continuation. No arithmetic or multiplicative test is assumed. -/
theorem signedTest_congr_extensions {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α)
    (positive : Bool) (mass : ℝ)
    (heq : ∀ later : List α, ∀ b : Bool,
      R b (later ++ pre) = S b (later ++ pre)) :
    signedTest R h T pre positive mass remaining =
      signedTest S h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hnode : R (!positive) (p :: pre) = S (!positive) (p :: pre) := by
        simpa only [List.singleton_append] using heq [p] (!positive)
      have hchild : ∀ later : List α, ∀ b : Bool,
          R b (later ++ (p :: pre)) = S b (later ++ (p :: pre)) := by
        intro later b
        simpa only [List.append_assoc, List.singleton_append] using
          heq (later ++ [p]) b
      simp only [signedTest, hnode]
      rw [ih pre positive mass heq,
        ih (p :: pre) (!positive) (mass * h p) hchild]

/-- Linearity concerns the terminal test, not the policy or its cap. -/
theorem signedTest_linear {α : Type*} (R : Bool → List α → Bool)
    (h : α → ℝ) (T U : Bool → List α → ℝ) (a b : ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    signedTest R h (fun s p => a * T s p + b * U s p)
        pre positive mass remaining =
      a * signedTest R h T pre positive mass remaining +
        b * signedTest R h U pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp only [signedTest]; ring
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [signedTest, if_pos hr]
        rw [ih, ih]
        ring
      · simp only [signedTest, if_neg hr, add_zero]
        exact ih pre positive mass

/-- The small-prime beta factor keeps the sign of each leaf. -/
theorem attachedLeafTest_linear (N cap mark : ℕ) (w L : ℝ)
    (G H : ℕ → ℝ) (a b : ℝ) (positive : Bool) (pre : List ℕ) :
    attachedLeafTest N cap mark w L (fun d => a * G d + b * H d) positive pre =
      a * attachedLeafTest N cap mark w L G positive pre +
        b * attachedLeafTest N cap mark w L H positive pre := by
  unfold attachedLeafTest
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Reversing a difference reverses its total, without dropping duplicate
occurrences or assigning a sign to the individual summands. -/
theorem sum_map_opposite {α : Type*} (xs : List α) (f g : α → ℝ) :
    -((xs.map (fun x => f x - g x)).sum) =
      (xs.map (fun x => g x - f x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- A partition of an occurrence list by a finite partial owner. The
unowned contribution must actually vanish; it is never discarded because
its geometric set happens to have zero volume. -/
theorem sum_by_owner {α β : Type*} [Fintype β]
    (xs : List α) (owner : α → Option β) (f : α → ℝ)
    (hzero : ∀ x ∈ xs, owner x = none → f x = 0) :
    (xs.map f).sum =
      ∑ b : β, ((xs.filter (fun x => decide (owner x = some b))).map f).sum := by
  revert hzero
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro hzero
      have ht := ih (fun y hy => hzero y (List.mem_cons_of_mem x hy))
      have hh : (∑ b : β, if owner x = some b then f x else 0) = f x := by
        cases ho : owner x with
        | none => simp [ho, hzero x (by simp) ho]
        | some b => simp [ho, eq_comm]
      calc
        ((x :: xs).map f).sum = f x + (xs.map f).sum := rfl
        _ = (∑ b : β, if owner x = some b then f x else 0) +
            ∑ b : β, ((xs.filter (fun y => decide (owner y = some b))).map f).sum := by
              rw [hh, ht]
        _ = ∑ b : β,
            (((x :: xs).filter (fun y => decide (owner y = some b))).map f).sum := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro b _
              by_cases hb : owner x = some b <;> simp [List.filter_cons, hb]

end
end ImbalancedChen.P1SignedDescendantAccounting
