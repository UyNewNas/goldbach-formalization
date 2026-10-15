import ImbalancedChen.ActualTwoCapacityGreedy
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp

/-!
# Selected slots and the actual original D-well vector

The four selected products are the manuscript's initial prefix, second
prime, first-and-third primes, and second-and-third primes.  For each one
the complete remaining-square budget is proved from the full original
support and exactly the displayed extra initial gate.  Later remaining
primes use the original prefix product, not a larger replacement product.

The bounded factors below are the actual deterministic greedy factors.
These statements cover the `C ≥ 1` numerical allocation.  The `C < 1`
branch uses `actualDwell_full_vector_repair` on the original list, so its
right factor is deliberately allowed to change.  Analytic monomial bounds,
alpha perturbations, and the same-policy arithmetic mean remain separate.
-/

namespace ImbalancedChen

noncomputable section

open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- Every tail index still has the exact original preceding product. -/
theorem actualDwell_original_tail_square {D : ℝ} (front tail : List ℕ)
    (hfull : actualDwellSupport D (front ++ tail))
    (i : ℕ) (hi : i < tail.length) :
    (front.prod : ℝ) * ((tail.take i).map (fun p : ℕ => (p : ℝ))).prod *
      (tail[i] : ℝ) ^ 2 ≤ D := by
  have hs := hfull (front.length + i) (by simp only [List.length_append]; omega)
  have htake : (front ++ tail).take (front.length + i) = front ++ tail.take i := by
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  have hget : (front ++ tail)[front.length + i] = tail[i] := by
    rw [List.getElem_append_right (by omega), Nat.add_sub_cancel_left]
  simpa only [htake, hget, List.map_append, List.prod_append,
    actualNatList_cast_prod] using hs

/-- Selecting an initial block needs no additional remaining-square gate. -/
theorem actualDwell_selected_prefix_budget {D : ℝ} (front tail : List ℕ)
    (hfront : 0 < front.prod) (hfull : actualDwellSupport D (front ++ tail)) :
    actualDwellSupport (D / front.prod) tail := by
  have hpos : (0 : ℝ) < front.prod := by exact_mod_cast hfront
  intro i hi
  apply (le_div_iff₀ hpos).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    actualDwell_original_tail_square front tail hfull i hi

/-- A removed short initial block leaves one first remaining prime.  Its
initial square is the only new test; every subsequent test is inherited
from the full original vector through the exact product identity. -/
private theorem actualDwell_selected_one_start_budget {D : ℝ}
    (front tail : List ℕ) (b₀ q : ℕ) (hb : 0 < b₀)
    (hprod : front.prod = b₀ * q)
    (hfull : actualDwellSupport D (front ++ tail))
    (hstart : (b₀ : ℝ) * (q : ℝ) ^ 2 ≤ D) :
    actualDwellSupport (D / b₀) (q :: tail) := by
  have hbpos : (0 : ℝ) < b₀ := by exact_mod_cast hb
  intro i hi
  apply (le_div_iff₀ hbpos).mpr
  cases i with
  | zero => simpa only [List.take_zero, List.map_nil, List.prod_nil,
      List.getElem_cons_zero, one_mul, mul_comm] using hstart
  | succ i =>
      have hit : i < tail.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have hs := actualDwell_original_tail_square front tail hfull i hit
      simpa only [List.take_succ_cons, List.map_cons, List.prod_cons,
        List.getElem_cons_succ, hprod, Nat.cast_mul, mul_assoc, mul_comm,
        mul_left_comm] using hs

theorem actualDwell_selected_p2_budget {D : ℝ} (p₁ p₂ : ℕ) (tail : List ℕ)
    (hp₂ : 0 < p₂) (hfull : actualDwellSupport D (p₁ :: p₂ :: tail))
    (hgate : (p₁ : ℝ) ^ 2 * p₂ ≤ D) :
    actualDwellSupport (D / p₂) (p₁ :: tail) := by
  apply actualDwell_selected_one_start_budget [p₁, p₂] tail p₂ p₁ hp₂
  · simp only [List.prod_cons, List.prod_nil, mul_one, mul_comm]
  · exact hfull
  · simpa only [mul_comm] using hgate

theorem actualDwell_selected_p1p3_budget {D : ℝ} (p₁ p₂ p₃ : ℕ)
    (tail : List ℕ) (hp₁ : 0 < p₁) (hp₃ : 0 < p₃)
    (hfull : actualDwellSupport D (p₁ :: p₂ :: p₃ :: tail))
    (hgate : (p₁ : ℝ) * (p₂ : ℝ) ^ 2 * p₃ ≤ D) :
    actualDwellSupport (D / (p₁ * p₃ : ℕ)) (p₂ :: tail) := by
  apply actualDwell_selected_one_start_budget [p₁, p₂, p₃] tail
    (p₁ * p₃) p₂ (Nat.mul_pos hp₁ hp₃)
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  · exact hfull
  · simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate

theorem actualDwell_selected_p2p3_budget {D : ℝ} (p₁ p₂ p₃ : ℕ)
    (tail : List ℕ) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hfull : actualDwellSupport D (p₁ :: p₂ :: p₃ :: tail))
    (hgate : (p₁ : ℝ) ^ 2 * p₂ * p₃ ≤ D) :
    actualDwellSupport (D / (p₂ * p₃ : ℕ)) (p₁ :: tail) := by
  apply actualDwell_selected_one_start_budget [p₁, p₂, p₃] tail
    (p₂ * p₃) p₁ (Nat.mul_pos hp₂ hp₃)
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  · exact hfull
  · simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate

/-- Allocation of the now proved remainder budget.  This is private: the
public concrete-mask consumers below pay this budget from original support. -/
private theorem actualSelectedRemainder_allocate {D A : ℝ} (hA : 1 ≤ A)
    (b₀ : ℕ) (hb : 0 < b₀) (remainder : List ℕ)
    (hC : 1 ≤ D / (A * b₀))
    (hbudget : actualDwellSupport (D / b₀) remainder) :
    (actualTwoCapacityFactors A remainder).1 * (actualTwoCapacityFactors A remainder).2 =
      remainder.prod ∧
      ((actualTwoCapacityFactors A remainder).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A remainder).2 : ℝ) ≤ D / (A * b₀) := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hbpos : (0 : ℝ) < b₀ := by exact_mod_cast hb
  have hsplit : A * (D / (A * b₀)) = D / b₀ := by
    field_simp [hApos.ne', hbpos.ne']
  have hfull : actualDwellSupport (A * (D / (A * b₀))) remainder := by
    simpa only [hsplit] using hbudget
  exact actualTwoCapacityFactors_correct hA hC remainder hfull

theorem actualDwell_selected_prefix_allocate {D A : ℝ} (hA : 1 ≤ A)
    (front tail : List ℕ) (hfront : 0 < front.prod)
    (hfull : actualDwellSupport D (front ++ tail))
    (hC : 1 ≤ D / (A * front.prod)) :
    (actualTwoCapacityFactors A tail).1 * front.prod *
        (actualTwoCapacityFactors A tail).2 = (front ++ tail).prod ∧
      ((actualTwoCapacityFactors A tail).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A tail).2 : ℝ) ≤ D / (A * front.prod) := by
  obtain ⟨hprod, hleft, hright⟩ := actualSelectedRemainder_allocate hA
    front.prod hfront tail hC (actualDwell_selected_prefix_budget front tail hfront hfull)
  refine ⟨?_, hleft, hright⟩
  calc
    _ = front.prod * ((actualTwoCapacityFactors A tail).1 *
        (actualTwoCapacityFactors A tail).2) := by ring
    _ = (front ++ tail).prod := by rw [hprod, List.prod_append]

private theorem actualSelectedOneStart_allocate {D A : ℝ} (hA : 1 ≤ A)
    (front tail : List ℕ) (b₀ q : ℕ) (hb : 0 < b₀)
    (hprod : front.prod = b₀ * q)
    (hfull : actualDwellSupport D (front ++ tail))
    (hstart : (b₀ : ℝ) * (q : ℝ) ^ 2 ≤ D)
    (hC : 1 ≤ D / (A * b₀)) :
    (actualTwoCapacityFactors A (q :: tail)).1 * b₀ *
        (actualTwoCapacityFactors A (q :: tail)).2 = (front ++ tail).prod ∧
      ((actualTwoCapacityFactors A (q :: tail)).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A (q :: tail)).2 : ℝ) ≤ D / (A * b₀) := by
  obtain ⟨hp, hleft, hright⟩ := actualSelectedRemainder_allocate hA b₀ hb
    (q :: tail) hC
    (actualDwell_selected_one_start_budget front tail b₀ q hb hprod hfull hstart)
  refine ⟨?_, hleft, hright⟩
  calc
    _ = b₀ * ((actualTwoCapacityFactors A (q :: tail)).1 *
        (actualTwoCapacityFactors A (q :: tail)).2) := by ring
    _ = (front ++ tail).prod := by rw [hp, List.prod_cons, List.prod_append, hprod]; ring

theorem actualDwell_selected_p2_allocate {D A : ℝ} (hA : 1 ≤ A)
    (p₁ p₂ : ℕ) (tail : List ℕ) (hp₂ : 0 < p₂)
    (hfull : actualDwellSupport D (p₁ :: p₂ :: tail))
    (hgate : (p₁ : ℝ) ^ 2 * p₂ ≤ D) (hC : 1 ≤ D / (A * p₂)) :
    (actualTwoCapacityFactors A (p₁ :: tail)).1 * p₂ *
        (actualTwoCapacityFactors A (p₁ :: tail)).2 = (p₁ :: p₂ :: tail).prod ∧
      ((actualTwoCapacityFactors A (p₁ :: tail)).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A (p₁ :: tail)).2 : ℝ) ≤ D / (A * p₂) := by
  apply actualSelectedOneStart_allocate hA [p₁, p₂] tail p₂ p₁ hp₂
  · simp only [List.prod_cons, List.prod_nil, mul_one, mul_comm]
  · exact hfull
  · simpa only [mul_comm] using hgate
  · exact hC

theorem actualDwell_selected_p1p3_allocate {D A : ℝ} (hA : 1 ≤ A)
    (p₁ p₂ p₃ : ℕ) (tail : List ℕ) (hp₁ : 0 < p₁) (hp₃ : 0 < p₃)
    (hfull : actualDwellSupport D (p₁ :: p₂ :: p₃ :: tail))
    (hgate : (p₁ : ℝ) * (p₂ : ℝ) ^ 2 * p₃ ≤ D)
    (hC : 1 ≤ D / (A * (p₁ * p₃ : ℕ))) :
    (actualTwoCapacityFactors A (p₂ :: tail)).1 * (p₁ * p₃) *
        (actualTwoCapacityFactors A (p₂ :: tail)).2 = (p₁ :: p₂ :: p₃ :: tail).prod ∧
      ((actualTwoCapacityFactors A (p₂ :: tail)).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A (p₂ :: tail)).2 : ℝ) ≤ D / (A * (p₁ * p₃ : ℕ)) := by
  apply actualSelectedOneStart_allocate hA [p₁, p₂, p₃] tail
    (p₁ * p₃) p₂ (Nat.mul_pos hp₁ hp₃)
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  · exact hfull
  · simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate
  · exact hC

theorem actualDwell_selected_p2p3_allocate {D A : ℝ} (hA : 1 ≤ A)
    (p₁ p₂ p₃ : ℕ) (tail : List ℕ) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hfull : actualDwellSupport D (p₁ :: p₂ :: p₃ :: tail))
    (hgate : (p₁ : ℝ) ^ 2 * p₂ * p₃ ≤ D)
    (hC : 1 ≤ D / (A * (p₂ * p₃ : ℕ))) :
    (actualTwoCapacityFactors A (p₁ :: tail)).1 * (p₂ * p₃) *
        (actualTwoCapacityFactors A (p₁ :: tail)).2 = (p₁ :: p₂ :: p₃ :: tail).prod ∧
      ((actualTwoCapacityFactors A (p₁ :: tail)).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A (p₁ :: tail)).2 : ℝ) ≤ D / (A * (p₂ * p₃ : ℕ)) := by
  apply actualSelectedOneStart_allocate hA [p₁, p₂, p₃] tail
    (p₂ * p₃) p₁ (Nat.mul_pos hp₂ hp₃)
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  · exact hfull
  · simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate
  · exact hC

/-- The full original prime vector is squarefree, before any selected slots
are removed or assigned to capacity bins. -/
theorem actualPrimeVector_squarefree (input : List ℕ)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hnodup : input.Nodup) :
    Squarefree input.prod := by
  induction input with
  | nil => simp
  | cons p tail ih =>
      obtain ⟨hpnot, htail⟩ := List.nodup_cons.mp hnodup
      have hp : Nat.Prime p := hprime p (by simp)
      have hprimeTail : ∀ q ∈ tail, Nat.Prime q :=
        fun q hq => hprime q (List.mem_cons_of_mem p hq)
      rw [List.prod_cons, Nat.squarefree_mul_iff]
      refine ⟨?_, hp.squarefree, ih hprimeTail htail⟩
      apply Nat.coprime_list_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hp (hprimeTail q hq)).mpr
        (fun hpq => hpnot (hpq.symm ▸ hq))

/-- Consequently every actual three-factor allocation above has all three
coprimality properties.  This uses original distinct primes and the proved
literal product identity, not a supplied coprimality license. -/
theorem actualPrimeVector_threeFactors_coprime (input : List ℕ)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hnodup : input.Nodup)
    (a b c : ℕ) (hprod : a * b * c = input.prod) :
    Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c := by
  have hs : Squarefree (a * b * c) := hprod.symm ▸ actualPrimeVector_squarefree input hprime hnodup
  have hab : Nat.Coprime a b := Nat.coprime_of_squarefree_mul hs.of_mul_left
  have hc : Nat.Coprime (a * b) c := Nat.coprime_of_squarefree_mul hs
  exact ⟨hab, (Nat.coprime_mul_iff_left.mp hc).1, (Nat.coprime_mul_iff_left.mp hc).2⟩

end

end ImbalancedChen
