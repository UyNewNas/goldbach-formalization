import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Original Winner9 exact Gaussian algorithm and proof, copied mechanically
into a new representation namespace. Every original helper remains private.
The specification is the existing Matrix.det; no original heavy owner or
previously accepted dependency context is modified. -/
namespace ImbalancedChen.P2Winner9FastDetPure

private def forceNat {α : Type} (n : Nat) (k : (x : Nat) → x = n → α) : α :=
  match n with
  | 0 => k 0 rfl
  | m + 1 => k (m + 1) rfl

private theorem forceNat_eq {α : Type} (n : Nat) (k : (x : Nat) → x = n → α) :
    forceNat n k = k n rfl := by cases n <;> rfl

private def forceInt {α : Type} (n : Int) (k : (x : Int) → x = n → α) : α :=
  match n with
  | .ofNat m => forceNat m fun x h => k (.ofNat x) (congrArg Int.ofNat h)
  | .negSucc m => forceNat m fun x h => k (.negSucc x) (congrArg Int.negSucc h)

private theorem forceInt_eq {α : Type} (n : Int) (k : (x : Int) → x = n → α) :
    forceInt n k = k n rfl := by cases n <;> simp only [forceInt, forceNat_eq]

private def forceFn {α β : Type} (force : (x : β) → ((y : β) → y = x → α) → α)
    {n : Nat} : (f : Fin n → β) → ((g : Fin n → β) → g = f → α) → α :=
  Nat.rec (motive := fun m => (f : Fin m → β) → ((g : Fin m → β) → g = f → α) → α)
    (fun _ k => k Fin.elim0 (funext fun i => i.elim0))
    (fun _ recurse f k => force (f 0) fun x hx =>
      recurse (fun i => f i.succ) fun t ht =>
        k (Fin.cons x t) (by rw [hx, ht]; exact Fin.cons_self_tail f)) n

private theorem forceFn_eq {α β : Type} (force : (x : β) → ((y : β) → y = x → α) → α)
    (hs : ∀ x k, force x k = k x rfl) {n : Nat} (f : Fin n → β)
    (k : (g : Fin n → β) → g = f → α) : forceFn force f k = k f rfl := by
  induction n with
  | zero =>
    have hf : f = Fin.elim0 := funext fun i => i.elim0
    subst f
    rfl
  | succ n ih =>
    change (force (f 0) fun x hx =>
      forceFn force (fun i : Fin n => f i.succ) fun t ht =>
        k (Fin.cons x t) (by rw [hx, ht]; exact Fin.cons_self_tail f)) = k f rfl
    rw [hs, ih]
    generalize_proofs h
    congr 1

private def forceRat {α : Type} (q : ℚ) (k : (x : ℚ) → x = q → α) : α :=
  forceInt q.num fun a ha => forceNat q.den fun b hb =>
    k ⟨a, b, hb.symm ▸ q.den_nz, by rw [ha, hb]; exact q.reduced⟩ (Rat.ext ha hb)

private theorem forceRat_eq {α : Type} (q : ℚ) (k : (x : ℚ) → x = q → α) :
    forceRat q k = k q rfl := by
  simp only [forceRat, forceInt_eq, forceNat_eq]

/-- The complement remaining after eliminating the first column. -/
private def pivotMinor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ := fun i j =>
  A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ

private theorem pivotMinor_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hp : A 0 0 ≠ 0) : A.det = A 0 0 * (pivotMinor A).det := by
  let c : Fin (n + 1) → ℚ := fun i => if i = 0 then 0 else -(A i 0 / A 0 0)
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := fun i j => A i j + c i * A 0 j
  have hdet : E.det = A.det := Matrix.det_eq_of_forall_row_eq_smul_add_const c 0
    (by simp [c]) (fun _ _ => rfl)
  have hz (i : Fin (n + 1)) (hi : i ≠ 0) : E i 0 = 0 := by
    simp [E, c, hi, div_mul_cancel₀ (A i 0) hp]
  have h00 : E 0 0 = A 0 0 := by simp [E, c]
  have hminor : E.submatrix (0 : Fin (n + 1)).succAbove Fin.succ = pivotMinor A := by
    ext i j
    change E ((0 : Fin (n + 1)).succAbove i) j.succ = pivotMinor A i j
    rw [Fin.succAbove_zero]
    simp [E, c, pivotMinor, sub_eq_add_neg]
  rw [← hdet, Matrix.det_succ_column_zero, Finset.sum_eq_single 0, h00, hminor]
  · simp
  · intro i _ hi
    simp [hz i hi]
  · simp

private def swapPivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (p : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  A.submatrix (Equiv.swap 0 p) id

private theorem swapPivot_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (p : Fin (n + 1)) : (swapPivot A p).det = (if p = 0 then 1 else -1) * A.det := by
  unfold swapPivot
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Matrix.det_permute, Equiv.Perm.sign_swap (Ne.symm hp), if_neg hp]
    norm_num

/-- Exact Gaussian determinant over ℚ with first-column pivoting.
Materialize each minor before the next pivot search and elimination. -/
private def fastDetCore {n : ℕ} : Matrix (Fin n) (Fin n) ℚ → ℚ :=
  Nat.rec (motive := fun m => Matrix (Fin m) (Fin m) ℚ → ℚ) (fun _ => 1)
    (fun m recurse A =>
      match (List.finRange (m + 1)).find? (fun i => A i 0 != 0) with
      | none => 0
      | some p =>
          let B := swapPivot A p
          forceFn (fun row k => forceFn forceRat row k) (fun i j => pivotMinor B i j)
            (fun C _ => (if p = 0 then 1 else -1) * B 0 0 * recurse C)) n

private theorem fastDetCore_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : fastDetCore A = A.det := by
  induction n with
  | zero => simp [fastDetCore]
  | succ n ih =>
      change (match (List.finRange (n + 1)).find? (fun i => A i 0 != 0) with
        | none => 0
        | some p =>
          let B := swapPivot A p
          forceFn (fun row k => forceFn forceRat row k) (fun i j => pivotMinor B i j)
            (fun C _ => (if p = 0 then 1 else -1) * B 0 0 * fastDetCore C)) = A.det
      split <;> rename_i h
      · rw [Matrix.det_succ_column_zero]
        symm
        apply Finset.sum_eq_zero
        intro i _
        have hi := List.find?_eq_none.mp h i (List.mem_finRange i)
        have hz : A i 0 = 0 := by simpa using hi
        simp [hz]
      · rename_i p
        have hp : A p 0 ≠ 0 := by simpa using List.find?_some h
        have h00 : swapPivot A p 0 0 = A p 0 := by simp [swapPivot]
        dsimp only
        rw [forceFn_eq _ (fun row k => forceFn_eq _ forceRat_eq row k)]
        change (if p = 0 then 1 else -1) * swapPivot A p 0 0 *
          fastDetCore (pivotMinor (swapPivot A p)) = A.det
        rw [ih, mul_assoc, ← pivotMinor_det _ (h00 ▸ hp), swapPivot_det]
        split_ifs <;> ring

/-- Materialize the exact rational entries once before Gaussian reduction. -/
def fastDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  forceFn (fun row k => forceFn forceRat row k) (fun i j => A i j) (fun B _ => fastDetCore B)

theorem fastDet_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : fastDet A = A.det := by
  unfold fastDet
  rw [forceFn_eq _ (fun r k => forceFn_eq _ forceRat_eq r k)]
  exact fastDetCore_eq A

#print axioms fastDet_eq

end ImbalancedChen.P2Winner9FastDetPure
