import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-! A finite prefix evaluator for the original Winner9 homogeneous coefficient. -/

namespace ImbalancedChen.P2Winner9HomogeneousRecurrence

open scoped BigOperators

/-- The source coefficient, allowing a common bound for all degrees of one table. -/
def boundedHomogeneous {n : ℕ} (y : Fin n → ℕ) (bound degree : ℕ) : ℕ :=
  ∑ exponents : Fin n → Fin (bound + 1),
    if (∑ i : Fin n, (exponents i).val) = degree then
      ∏ i : Fin n, y i ^ (exponents i).val
    else 0

private theorem empty_coefficient (y : Fin 0 → ℕ) (bound degree : ℕ) :
    boundedHomogeneous y bound degree = if degree = 0 then 1 else 0 := by
  classical
  unfold boundedHomogeneous
  rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → Fin (bound + 1))]
  · simp [eq_comm]
  · intro a _ ha
    exact (ha (funext fun i => i.elim0)).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Separate the first exponent by a bijection with the head and tail. -/
theorem split_coefficient {n bound degree : ℕ} (y : Fin (n + 1) → ℕ)
    (hdegree : degree ≤ bound) :
    boundedHomogeneous y bound degree =
      ∑ j ∈ Finset.range (degree + 1),
        y 0 ^ j * boundedHomogeneous (fun i : Fin n => y i.succ) bound (degree - j) := by
  classical
  let splitTerm (x : Fin (bound + 1) × (Fin n → Fin (bound + 1))) : ℕ :=
    if x.1.val + (∑ i : Fin n, (x.2 i).val) = degree then
      y 0 ^ x.1.val * ∏ i : Fin n, y i.succ ^ (x.2 i).val
    else 0
  let term (j : ℕ) : ℕ :=
    y 0 ^ j * boundedHomogeneous (fun i : Fin n => y i.succ) bound (degree - j)
  calc
    boundedHomogeneous y bound degree = ∑ x, splitTerm x := by
      symm
      unfold boundedHomogeneous
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin (bound + 1)))
      intro x
      simp only [splitTerm, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
    _ = ∑ j : Fin (bound + 1), ∑ a : Fin n → Fin (bound + 1), splitTerm (j, a) :=
      Fintype.sum_prod_type splitTerm
    _ = ∑ j : Fin (bound + 1), if j.val ≤ degree then term j.val else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j.val ≤ degree
      · rw [if_pos h]
        unfold term boundedHomogeneous
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        have he : j.val + (∑ i : Fin n, (a i).val) = degree ↔
            (∑ i : Fin n, (a i).val) = degree - j.val := by omega
        simp only [splitTerm, he, mul_ite, mul_zero]
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro a _
        have he : j.val + (∑ i : Fin n, (a i).val) ≠ degree := by omega
        exact if_neg he
    _ = ∑ j ∈ Finset.range (bound + 1), if j ≤ degree then term j else 0 :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ degree then term j else 0) (bound + 1)
    _ = ∑ j ∈ Finset.range (degree + 1), if j ≤ degree then term j else 0 := by
      symm
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdegree)) ?_
      intro j _ hj
      exact if_neg (fun h => hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
    _ = ∑ j ∈ Finset.range (degree + 1), term j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

/-- At positive degree, either the leading exponent vanishes or removing one
copy of the leading variable reduces the degree by one. -/
theorem coefficient_succ {n bound k : ℕ} (y : Fin (n + 1) → ℕ)
    (hk : k + 1 ≤ bound) :
    boundedHomogeneous y bound (k + 1) =
      boundedHomogeneous (fun i : Fin n => y i.succ) bound (k + 1) +
        y 0 * boundedHomogeneous y bound k := by
  have hprev : k ≤ bound := Nat.le_trans (Nat.le_succ k) hk
  rw [split_coefficient y hk, split_coefficient y hprev, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, pow_succ', mul_assoc]
  exact Nat.add_comm _ _

/-- Insert one variable into the coefficient table in a single pass. -/
private def addVariable (a carry : ℕ) (xs : List ℕ) : List ℕ :=
  xs.foldr (fun x next previous =>
    let value := x + a * previous
    value :: next value) (fun _ => []) carry

private theorem addVariable_cons (a carry x : ℕ) (xs : List ℕ) :
    addVariable a carry (x :: xs) = (x + a * carry) :: addVariable a (x + a * carry) xs :=
  rfl

private theorem addVariable_length (a carry : ℕ) (xs : List ℕ) :
    (addVariable a carry xs).length = xs.length := by
  induction xs generalizing carry with
  | nil => rfl
  | cons x xs ih => simp only [addVariable_cons, List.length_cons, ih]

private theorem addVariable_first (a carry : ℕ) (xs : List ℕ) (h : 0 < xs.length) :
    (addVariable a carry xs)[0]?.getD 0 = xs[0]?.getD 0 + a * carry := by
  cases xs with
  | nil => simp at h
  | cons x xs => rfl

private theorem addVariable_next (a carry k : ℕ) (xs : List ℕ) (h : k + 1 < xs.length) :
    (addVariable a carry xs)[k + 1]?.getD 0 =
      xs[k + 1]?.getD 0 + a * (addVariable a carry xs)[k]?.getD 0 := by
  induction k generalizing carry xs with
  | zero =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      cases xs with
      | nil => simp at h
      | cons z zs => rfl
  | succ k ih =>
    cases xs with
    | nil => simp at h
    | cons x xs => exact ih (x + a * carry) xs (by simpa using h)

/-- Table of all coefficients through `bound`, initialized by the constant 1. -/
def prefixCoefficients (bound n : ℕ) (y : Fin n → ℕ) : List ℕ :=
  (List.ofFn y).foldr (fun a coefficients => addVariable a 0 coefficients)
    (1 :: List.replicate bound 0)

private theorem prefixCoefficients_zero (bound : ℕ) (y : Fin 0 → ℕ) :
    prefixCoefficients bound 0 y = 1 :: List.replicate bound 0 := by
  simp only [prefixCoefficients, List.ofFn_zero, List.foldr_nil]

private theorem prefixCoefficients_succ (bound n : ℕ) (y : Fin (n + 1) → ℕ) :
    prefixCoefficients bound (n + 1) y =
      addVariable (y 0) 0 (prefixCoefficients bound n (fun i => y i.succ)) := by
  simp only [prefixCoefficients, List.ofFn_succ, List.foldr_cons]

theorem prefixCoefficients_length (bound n : ℕ) (y : Fin n → ℕ) :
    (prefixCoefficients bound n y).length = bound + 1 := by
  induction n with
  | zero => simp [prefixCoefficients_zero]
  | succ n ih => simp only [prefixCoefficients_succ, addVariable_length, ih]

/-- Every emitted coefficient agrees with the bounded finite source formula. -/
theorem prefixCoefficients_correct (bound n : ℕ) (y : Fin n → ℕ) (k : ℕ)
    (hk : k ≤ bound) :
    (prefixCoefficients bound n y)[k]?.getD 0 = boundedHomogeneous y bound k := by
  induction n generalizing k with
  | zero =>
    rw [prefixCoefficients_zero, empty_coefficient]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.getElem?_cons_succ, List.getElem?_replicate_of_lt (by omega : k < bound),
        Option.getD_some, Nat.succ_ne_zero, if_false]
  | succ n ih =>
    induction k with
    | zero =>
      have hlen : 0 < (prefixCoefficients bound n (fun i : Fin n => y i.succ)).length := by
        simp [prefixCoefficients_length]
      rw [prefixCoefficients_succ, addVariable_first _ _ _ hlen, Nat.mul_zero, Nat.add_zero, ih _ _ hk,
        split_coefficient y hk]
      simp
    | succ k ihk =>
      have hprev : k ≤ bound := Nat.le_trans (Nat.le_succ k) hk
      have hlen : k + 1 < (prefixCoefficients bound n (fun i : Fin n => y i.succ)).length := by
        simpa only [prefixCoefficients_length] using Nat.lt_succ_of_le hk
      rw [prefixCoefficients_succ, addVariable_next _ _ _ _ hlen, ih _ _ hk,
        ← prefixCoefficients_succ, ihk hprev, coefficient_succ y hk]

/-- Kernel-safe evaluator for the exact coefficient used by the Winner9 ledger. -/
def homogeneousFast (y : Fin 9 → ℕ) (k : ℕ) : ℕ :=
  (prefixCoefficients k 9 y)[k]?.getD 0

/-- The right side is definitionally the original `homogeneous y k`. -/
theorem homogeneousFast_eq_source (y : Fin 9 → ℕ) (k : ℕ) :
    homogeneousFast y k =
      ∑ exponents : Fin 9 → Fin (k + 1),
        if (∑ i : Fin 9, (exponents i).val) = k then
          ∏ i : Fin 9, y i ^ (exponents i).val
        else 0 :=
  prefixCoefficients_correct k 9 y k (Nat.le_refl k)

end ImbalancedChen.P2Winner9HomogeneousRecurrence
