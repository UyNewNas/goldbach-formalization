import ImbalancedChen.Part5SavedParent394700BuchstabAll32

/- SOURCEONLY. Dependency is the actual modular All32 source under the
   module name above; see the companion checkpoint for the exact source pin.
   No row data or finite-certificate assembly is duplicated here. -/
namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
namespace P0All32RowPublicAPI

open Set

noncomputable section

/-- The original 32 certificates use two different uniform subdivisions. -/
def rowLeft (k : Fin 32) : ℝ :=
  if k.val < 16 then (247264 + 4905 * (k.val : ℝ)) / 325744
  else 883 * ((k.val - 16 : ℕ) : ℝ) / 160128

def rowRight (k : Fin 32) : ℝ :=
  if k.val < 16 then (247264 + 4905 * (k.val : ℝ) + 4905) / 325744
  else (883 * ((k.val - 16 : ℕ) : ℝ) + 883) / 160128

/-- Nat callers supply only the actual finite range, with no modular wrap. -/
def ofNat (n : ℕ) (hn : n < 32) : Fin 32 := ⟨n, hn⟩

@[simp] theorem ofNat_val (n : ℕ) (hn : n < 32) :
    (ofNat n hn).val = n := by rfl

@[simp] theorem ofNat_val_inverse (k : Fin 32) :
    ofNat k.val k.isLt = k := by rfl

theorem ofNat_proof_irrel (n : ℕ) (h h' : n < 32) :
    ofNat n h = ofNat n h' := by rfl

theorem forall_fin_iff_nat (P : Fin 32 → Prop) :
    (∀ k, P k) ↔ ∀ n (hn : n < 32), P (ofNat n hn) := by
  constructor
  · intro h n hn
    exact h (ofNat n hn)
  · intro h k
    exact h k.val k.isLt

theorem rowLeft_eq_affine (k : Fin 32) :
    rowLeft k = (affineA k : ℝ) / (affineD k : ℝ) := by
  by_cases hk : k.val < 16
  · simp [rowLeft, affineA, affineD, hk]
  · simp [rowLeft, affineA, affineD, hk]

theorem rowRight_eq_affine (k : Fin 32) :
    rowRight k = ((affineA k : ℝ) + (affineB k : ℝ)) / (affineD k : ℝ) := by
  by_cases hk : k.val < 16
  · simp [rowRight, affineA, affineB, affineD, hk]
  · simp [rowRight, affineA, affineB, affineD, hk]

/-- Every row is a genuine interval of positive width. -/
theorem rowLeft_lt_rowRight (k : Fin 32) : rowLeft k < rowRight k := by
  by_cases hk : k.val < 16
  · simp only [rowLeft, rowRight, if_pos hk]
    linarith
  · simp only [rowLeft, rowRight, if_neg hk]
    linarith

/-- The explicit row intervals stay inside the original local coordinate cell. -/
theorem row_bounds (k : Fin 32) : 0 ≤ rowLeft k ∧ rowRight k ≤ 1 := by
  by_cases hk : k.val < 16
  · have hzero : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    have htop : (k.val : ℝ) ≤ 15 := by
      exact_mod_cast (show k.val ≤ 15 by omega)
    simp only [rowLeft, rowRight, if_pos hk]
    constructor <;> linarith
  · have hzero : (0 : ℝ) ≤ ((k.val - 16 : ℕ) : ℝ) := Nat.cast_nonneg _
    have htop : ((k.val - 16 : ℕ) : ℝ) ≤ 15 := by
      have hlt := k.isLt
      exact_mod_cast (show k.val - 16 ≤ 15 by omega)
    simp only [rowLeft, rowRight, if_neg hk]
    constructor <;> linarith
/-- Rows 0..15 concern cell 10; rows 16..31 concern cell 11. -/
theorem cellIndex_bounds (k : Fin 32) :
    10 ≤ cellIndex k ∧ cellIndex k ≤ 11 := by
  unfold cellIndex
  split <;> omega

/-- All finite indices expose their certified integer identity. -/
theorem all_rows_good (k : Fin 32) : BernsteinGood k := by
  exact finiteBernsteinGood k

/-- Public form of the assembly's private row-local barrier theorem. -/
theorem row_barrier_nonneg (k : Fin 32) {t : ℝ}
    (ht : t ∈ Icc (rowLeft k) (rowRight k)) :
    0 ≤ evalList (barrierList (cellIndex k)) t := by
  have h := all_rows_good k
  apply integer_Bernstein_certificate_on_interval 52 bernsteinMultiplier
    (affineA k) (affineB k) (affineD k) (barrierList (cellIndex k))
    (bernsteinCoefficients k) multiplier_positive h.2.1 h.2.2.1 h.1 h.2.2.2
  simpa only [mem_Icc, rowLeft_eq_affine, rowRight_eq_affine] using ht

/-- The actual dense polynomial upper bound, including its original error term. -/
theorem row_polynomial_upper (k : Fin 32) {t : ℝ}
    (ht : t ∈ Icc (rowLeft k) (rowRight k)) :
    evalList (row (cellIndex k)) t + (err (cellIndex k) : ℝ) ≤
      (omegaHalf : ℝ) * ((cellIndex k : ℝ) + t) := by
  have h := row_barrier_nonneg k ht
  have he : evalList (barrierList (cellIndex k)) t =
      (omegaHalf : ℝ) * ((cellIndex k : ℝ) + t) -
        (err (cellIndex k) : ℝ) - evalList (row (cellIndex k)) t := by
    simp only [barrierList, eval_addList, eval_scaleList, evalList,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_neg, Int.cast_one, mul_zero, add_zero]
    ring
  rw [he] at h
  linarith

/-- Complete row-local contract: the actual interval and cell bounds, its
integer certificate, and its real barrier and polynomial consequences. -/
theorem all_rows_contract (k : Fin 32) :
    rowLeft k < rowRight k ∧
    (0 ≤ rowLeft k ∧ rowRight k ≤ 1) ∧
    (10 ≤ cellIndex k ∧ cellIndex k ≤ 11) ∧
    BernsteinGood k ∧
    ∀ t ∈ Icc (rowLeft k) (rowRight k),
      0 ≤ evalList (barrierList (cellIndex k)) t ∧
      evalList (row (cellIndex k)) t + (err (cellIndex k) : ℝ) ≤
        (omegaHalf : ℝ) * ((cellIndex k : ℝ) + t) := by
  refine ⟨rowLeft_lt_rowRight k, row_bounds k, cellIndex_bounds k, all_rows_good k, ?_⟩
  intro t ht
  exact ⟨row_barrier_nonneg k ht, row_polynomial_upper k ht⟩

theorem nat_row_barrier_nonneg (n : ℕ) (hn : n < 32) {t : ℝ}
    (ht : t ∈ Icc (rowLeft (ofNat n hn)) (rowRight (ofNat n hn))) :
    0 ≤ evalList (barrierList (cellIndex (ofNat n hn))) t := by
  exact row_barrier_nonneg (ofNat n hn) ht

theorem nat_row_polynomial_upper (n : ℕ) (hn : n < 32) {t : ℝ}
    (ht : t ∈ Icc (rowLeft (ofNat n hn)) (rowRight (ofNat n hn))) :
    evalList (row (cellIndex (ofNat n hn))) t +
        (err (cellIndex (ofNat n hn)) : ℝ) ≤
      (omegaHalf : ℝ) * ((cellIndex (ofNat n hn) : ℝ) + t) := by
  exact row_polynomial_upper (ofNat n hn) ht

end
end P0All32RowPublicAPI
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly


