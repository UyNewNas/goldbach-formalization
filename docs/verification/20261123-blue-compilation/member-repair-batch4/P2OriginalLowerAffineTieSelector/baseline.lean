import Mathlib

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Paper internal finite-branch primitive for the causal lower approximation.
-- This is the deterministic label selector, not the selected certificate
-- array, a legal whole-box CapPlan, or the lower coefficient theorem.
--
-- Original source: lower-start-joint-finite-approximation.tex, lines 81-113.
-- Identical affine expressions are structural equality chambers. The
-- inherited branch is scanned first and remains selected on every tie.
-- Nonidentical ties are proper closed affine walls, isolated from the
-- full-measure inherit chamber. A later nested rational-box construction
-- must trim their neighborhoods while keeping the parent cap frozen.
-- The mesh is later chosen on [epsilon,w], with epsilon below the lower
-- start a; this selector itself assumes no fixed exponent interval.

namespace ImbalancedChen.P2OriginalLowerAffineTieSelector

noncomputable section
open Set Classical

abbrev Point (d : ℕ) := Fin d → ℝ

structure AffineBranch (d : ℕ) where
  constant : ℚ
  slope : Fin d → ℚ

def AffineBranch.eval {d : ℕ} (a : AffineBranch d) (x : Point d) : ℝ :=
  (a.constant : ℝ) + ∑ i : Fin d, (a.slope i : ℝ) * x i

theorem AffineBranch.eval_eq_of_eq {d : ℕ}
    {a b : AffineBranch d} (h : a = b) (x : Point d) :
    a.eval x = b.eval x := by
  rw [h]

theorem AffineBranch.eval_zero {d : ℕ} (a : AffineBranch d) :
    a.eval (fun _ => 0) = (a.constant : ℝ) := by
  simp [AffineBranch.eval]

theorem AffineBranch.eval_basis {d : ℕ} (a : AffineBranch d) (j : Fin d) :
    a.eval (fun i => if i = j then 1 else 0) =
      (a.constant : ℝ) + (a.slope j : ℝ) := by
  simp [AffineBranch.eval]

-- A real affine expression is determined by its constant and its d
-- coordinate slopes. This rules out treating an identical formula as
-- a codimension-one wall.
theorem AffineBranch.eq_of_eval_eq_all {d : ℕ} {a b : AffineBranch d}
    (h : ∀ x : Point d, a.eval x = b.eval x) : a = b := by
  have hcR : (a.constant : ℝ) = (b.constant : ℝ) := by
    simpa only [AffineBranch.eval_zero] using h (fun _ => 0)
  have hc : a.constant = b.constant := by exact_mod_cast hcR
  have hs : a.slope = b.slope := by
    funext j
    have hj := h (fun i => if i = j then 1 else 0)
    rw [a.eval_basis j, b.eval_basis j] at hj
    have hjR : (a.slope j : ℝ) = (b.slope j : ℝ) := by linarith
    exact_mod_cast hjR
  cases a with
  | mk ac av =>
      cases b with
      | mk bc bv =>
          simp only at hc hs
          cases hc
          cases hs
          rfl

def AffineBranch.tieSet {d : ℕ} (a b : AffineBranch d) : Set (Point d) :=
  {x | a.eval x = b.eval x}

theorem AffineBranch.tieSet_eq_univ_iff {d : ℕ} (a b : AffineBranch d) :
    a.tieSet b = Set.univ ↔ a = b := by
  constructor
  · intro h
    apply AffineBranch.eq_of_eval_eq_all
    intro x
    have hx : x ∈ a.tieSet b := by rw [h]; trivial
    exact hx
  · intro h
    subst b
    ext x
    simp [AffineBranch.tieSet]

theorem AffineBranch.tieSet_proper_of_ne {d : ℕ}
    {a b : AffineBranch d} (h : a ≠ b) :
    a.tieSet b ≠ Set.univ := by
  intro heq
  exact h ((a.tieSet_eq_univ_iff b).mp heq)

theorem AffineBranch.continuous_eval {d : ℕ} (a : AffineBranch d) :
    Continuous a.eval := by
  unfold AffineBranch.eval
  fun_prop

theorem AffineBranch.tieSet_closed {d : ℕ} (a b : AffineBranch d) :
    IsClosed (a.tieSet b) := by
  exact isClosed_eq a.continuous_eval b.continuous_eval

-- The tie equation exposes the exact rational affine wall; no boundary
-- has been removed from an arithmetic prime sum.
theorem AffineBranch.mem_tieSet_iff {d : ℕ}
    (a b : AffineBranch d) (x : Point d) :
    x ∈ a.tieSet b ↔
      (∑ i : Fin d, ((a.slope i - b.slope i : ℚ) : ℝ) * x i) =
        ((b.constant - a.constant : ℚ) : ℝ) := by
  simp only [AffineBranch.tieSet, Set.mem_setOf_eq, AffineBranch.eval,
    Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

structure LabeledBranch (d : ℕ) where
  label : ℕ
  cap : AffineBranch d
  argument : ℚ

def LabeledBranch.value {d : ℕ} (b : LabeledBranch d) (x : Point d) : ℝ :=
  b.cap.eval x

-- The parent is the accumulator at the start. A tie never replaces it;
-- subsequent ties preserve the first earlier label. This fixed list order
-- is the deterministic rule on every chamber.
def keepOrRaise {d : ℕ} (x : Point d)
    (current next : LabeledBranch d) : LabeledBranch d :=
  if current.value x < next.value x then next else current

def scan {d : ℕ} (x : Point d) (current : LabeledBranch d) :
    List (LabeledBranch d) → LabeledBranch d
  | [] => current
  | next :: rest => scan x (keepOrRaise x current next) rest

theorem keepOrRaise_ge_left {d : ℕ} (x : Point d)
    (current next : LabeledBranch d) :
    current.value x ≤ (keepOrRaise x current next).value x := by
  unfold keepOrRaise
  split_ifs with h
  · exact h.le
  · exact le_rfl

theorem keepOrRaise_ge_right {d : ℕ} (x : Point d)
    (current next : LabeledBranch d) :
    next.value x ≤ (keepOrRaise x current next).value x := by
  unfold keepOrRaise
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_gt h

theorem scan_ge_start {d : ℕ} (x : Point d)
    (current : LabeledBranch d) (rest : List (LabeledBranch d)) :
    current.value x ≤ (scan x current rest).value x := by
  induction rest generalizing current with
  | nil => exact le_rfl
  | cons next rest ih =>
      exact (keepOrRaise_ge_left x current next).trans
        (ih (keepOrRaise x current next))

theorem scan_ge_member {d : ℕ} (x : Point d)
    (current : LabeledBranch d) (rest : List (LabeledBranch d))
    {next : LabeledBranch d} (hnext : next ∈ rest) :
    next.value x ≤ (scan x current rest).value x := by
  induction rest generalizing current with
  | nil => simp at hnext
  | cons first rest ih =>
      rcases List.mem_cons.mp hnext with rfl | hmem
      · exact (keepOrRaise_ge_right x current first).trans
          (scan_ge_start x (keepOrRaise x current first) rest)
      · exact ih (keepOrRaise x current first) hmem

theorem scan_eq_start_of_all_le {d : ℕ} (x : Point d)
    (current : LabeledBranch d) (rest : List (LabeledBranch d))
    (h : ∀ b ∈ rest, b.value x ≤ current.value x) :
    scan x current rest = current := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest ih =>
      have hn := h next (List.mem_cons_self)
      have hkeep : keepOrRaise x current next = current := by
        simp only [keepOrRaise, if_neg (not_lt.mpr hn)]
      simp only [scan, hkeep]
      exact ih current (fun b hb => h b (List.mem_cons_of_mem _ hb))

-- none is the literal inherit label. A fresh output exists only after a
-- strict improvement over the incoming parent; equality chambers survive.
def selected {d : ℕ} (base : LabeledBranch d)
    (rest : List (LabeledBranch d)) (x : Point d) :
    Option (LabeledBranch d) :=
  let winner := scan x base rest
  if winner = base then none else some winner

theorem selected_none_of_all_le {d : ℕ}
    (base : LabeledBranch d) (rest : List (LabeledBranch d))
    (x : Point d) (h : ∀ b ∈ rest, b.value x ≤ base.value x) :
    selected base rest x = none := by
  simp [selected, scan_eq_start_of_all_le x base rest h]

theorem selected_none_of_identical_branches {d : ℕ}
    (base : LabeledBranch d) (rest : List (LabeledBranch d))
    (x : Point d) (h : ∀ b ∈ rest, b.cap = base.cap) :
    selected base rest x = none := by
  apply selected_none_of_all_le
  intro b hb
  simpa [LabeledBranch.value, h b hb]

-- A proper nonidentical tie is recorded as a wall. Identical formulas
-- are excluded from this wall union even if labels/arguments differ.
def properTieWalls {d : ℕ} (base : LabeledBranch d)
    (rest : List (LabeledBranch d)) : Set (Point d) :=
  {x | ∃ a ∈ base :: rest, ∃ b ∈ base :: rest,
    a.cap ≠ b.cap ∧ a.value x = b.value x}

theorem distinct_equal_values_mem_wall {d : ℕ}
    (base : LabeledBranch d) (rest : List (LabeledBranch d))
    {a b : LabeledBranch d} (ha : a ∈ base :: rest)
    (hb : b ∈ base :: rest) (hne : a.cap ≠ b.cap)
    {x : Point d} (heq : a.value x = b.value x) :
    x ∈ properTieWalls base rest := by
  exact ⟨a, ha, b, hb, hne, heq⟩

theorem off_wall_distinct_values {d : ℕ}
    (base : LabeledBranch d) (rest : List (LabeledBranch d))
    {x : Point d} (hx : x ∉ properTieWalls base rest)
    {a b : LabeledBranch d} (ha : a ∈ base :: rest)
    (hb : b ∈ base :: rest) (hne : a.cap ≠ b.cap) :
    a.value x ≠ b.value x := by
  intro heq
  exact hx (distinct_equal_values_mem_wall base rest ha hb hne heq)

-- Adapter for the buffered-box constructor's primitive rational triple.
-- The selector itself has no hidden CapPlan, certificate or N input.
def LabeledBranch.asBranchData (b : LabeledBranch 5) :
    ℚ × (Fin 5 → ℚ) × ℚ :=
  (b.cap.constant, b.cap.slope, b.argument)

end
end ImbalancedChen.P2OriginalLowerAffineTieSelector


