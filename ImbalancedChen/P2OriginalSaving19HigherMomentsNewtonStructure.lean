import ImbalancedChen.P2OriginalSaving19HigherMomentsCore

/-! SOURCE CANDIDATE: pending production normal/kernel/full-owned acceptance.
The manuscript simplex-moment formula and existing Core definitions are retained.
Only finite sum reindexing and bounded Newton algebra are reorganized.
No finite exponent-vector list is enumerated; no tactic budget is increased. -/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
noncomputable section
open scoped BigOperators

def powerSum {A : Type*} [CommRing A] (as : List A) (k : ℕ) : A :=
  (as.map (fun a => a ^ k)).sum

theorem completeH_newton_small {A : Type*} [CommRing A]
    (as : List A) (k : ℕ) (hk : k ≤ 5) :
    ((k + 1 : ℕ) : A) * completeH as (k + 1) =
      ∑ j : Fin (k + 1), powerSum as (j.val + 1) * completeH as (k - j.val) := by
  induction as generalizing k with
  | nil => simp [completeH, powerSum]
  | cons a as ih =>
    have h0 := ih 0 (by decide)
    have h1 := ih 1 (by decide)
    have h2 := ih 2 (by decide)
    have h3 := ih 3 (by decide)
    have h4 := ih 4 (by decide)
    have h5 := ih 5 (by decide)
    norm_num [powerSum, completeH_zero, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
    interval_cases k
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h1 + a * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h2 + a * h1 + a ^ 2 * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h3 + a * h2 + a ^ 2 * h1 + a ^ 3 * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h4 + a * h3 + a ^ 2 * h2 + a ^ 3 * h1 + a ^ 4 * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h5 + a * h4 + a ^ 2 * h3 + a ^ 3 * h2 + a ^ 4 * h1 + a ^ 5 * h0

theorem duplicateH_eq_completeH_small {A : Type*} [CommRing A] [Algebra ℚ A]
    (y : Fin 9 → A) (i : Fin 9) (k : ℕ) (hk : k ≤ 6) :
    duplicateH y i k = completeH (y i :: List.ofFn y) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp only [duplicateH, completeH_zero]
    | succ k =>
      have hn := completeH_newton_small (y i :: List.ofFn y) k (by omega)
      have hs :
          (∑ j : Fin (k + 1),
            ((∑ r : Fin 9, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
              completeH (y i :: List.ofFn y) (k - j.val)) =
          (k + 1 : ℚ) • completeH (y i :: List.ofFn y) (k + 1) := by
        simpa only [powerSum, List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn,
          Algebra.smul_def, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one,
          Function.comp_def, add_comm]
          using hn.symm
      calc
        duplicateH y i (k + 1) =
            ((k + 1 : ℚ)⁻¹) •
              ∑ j : Fin (k + 1),
                ((∑ r : Fin 9, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
                  completeH (y i :: List.ofFn y) (k - j.val) := by
          rw [duplicateH]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [ih (k - j.val) (by omega) (by omega)]
        _ = ((k + 1 : ℚ)⁻¹) •
            ((k + 1 : ℚ) • completeH (y i :: List.ofFn y) (k + 1)) := by rw [hs]
        _ = completeH (y i :: List.ofFn y) (k + 1) := by
          rw [smul_smul, inv_mul_cancel₀ (show (k + 1 : ℚ) ≠ 0 by positivity)]
          simp

theorem duplicateH_author_guard_structural (y : Fin 9 → ℚ) (i : Fin 9)
    (k : ℕ) (hk : k ≤ 6) :
    duplicateH y i k = ∑ j : Fin (k + 1),
      completeH (List.ofFn y) (k - j.val) * y i ^ j.val := by
  rw [duplicateH_eq_completeH_small y i k hk, completeH]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
