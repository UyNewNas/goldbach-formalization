import ImbalancedChen.FirstExitFrontierTupleReindex
import ImbalancedChen.RosserShortPrefixAdmissibility
import ImbalancedChen.ActualPrimeBoxTestFunctions

/-!
# The ordinary upper fifth-candidate region

This is a finite exact dictionary for a constant ordinary parent. Its
first four selections are admitted; the fifth candidate's own cube is
not tested. The complete rank-four total-product cutoff is paid by the
proved short-prefix theorem. The logarithmic form keeps strict endpoints
and the original target, prime exclusions, and enumeration cap.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators

private theorem ordinaryParity_parent_valid_iff (lower : Bool) (Q : ℝ) (hQ : 1 < Q)
    (chosen : List ℕ) (hprime : ∀ p ∈ chosen, Nat.Prime p)
    (hsort : chosen.Pairwise (· > ·))
    (hlevel : lower = true → ∀ p ∈ chosen, (p : ℝ) < Q) :
    FirstExitValidSelection (ordinaryParityRosserPolicy lower Q) [] true chosen ↔
      ordinaryRosserPrefixAdmissible lower Q chosen.reverse := by
  have hp : ∀ p ∈ chosen.reverse ++ [], Nat.Prime p := by simpa using hprime
  have hs : (chosen.reverse ++ []).Pairwise (· < ·) := by
    simpa only [List.append_nil, List.pairwise_reverse] using hsort
  rw [firstExitValidSelection_ordinaryParityRosser_iff lower Q chosen [] true
    (ordinaryRosserPrefixAdmissible_nil lower hQ) (by simp [evenListLength]) hp hlevel hs,
    firstExitValidSelection_ordinaryRosser_iff lower Q chosen [] true
      (ordinaryRosserPrefixAdmissible_nil lower hQ) hp hs,
    List.append_nil]

/-- Proper-parent validity is exactly the first and third cubic tests.
No admission test at the fifth candidate appears. -/
theorem ordinaryUpperFive_parent_valid_iff (Q : ℝ) (hQ : 1 < Q)
    (p : Fin 5 → ℕ) (hprime : ∀ i, Nat.Prime (p i)) (hsort : StrictAnti p) :
    FirstExitValidSelection (ordinaryParityRosserPolicy false Q) [] true
      (List.ofFn p).dropLast ↔
      (p 0 : ℝ) ^ 3 < Q ∧ (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < Q := by
  have hparentPrime : ∀ q ∈ (List.ofFn p).dropLast, Nat.Prime q := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ((List.dropLast_sublist _).subset hq)
    exact hprime i
  have hfullSort : (List.ofFn p).Pairwise (· > ·) := List.pairwise_ofFn.mpr hsort
  have hparentSort : (List.ofFn p).dropLast.Pairwise (· > ·) :=
    hfullSort.sublist (List.dropLast_sublist _)
  rw [ordinaryParity_parent_valid_iff false Q hQ _ hparentPrime hparentSort (by simp)]
  have hdrop : (List.ofFn p).dropLast.reverse = [p 3, p 2, p 1, p 0] := by
    simp [List.ofFn_succ]
  rw [hdrop]
  exact ordinaryRosserPrefixAdmissible_upper_four_iff Q (p 0) (p 1) (p 2) (p 3)
    (hprime 3).pos (hsort (by decide : (2 : Fin 5) < 3))
    (hsort (by decide : (1 : Fin 5) < 2)) (hsort (by decide : (0 : Fin 5) < 1))

/-- Literal arithmetic description, with the same target and strict cutoff. -/
theorem mem_ordinaryUpperFiveFrontierTuples_iff (Q : ℝ) (hQ : 1 < Q)
    (N cap : ℕ) (w z : ℝ) (p : Fin 5 → ℕ) :
    p ∈ firstExitFrontierTuples 4 (ordinaryParityRosserPolicy false Q)
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, p i < cap ∧ Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        (p 0 : ℝ) ^ 3 < Q ∧ (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < Q := by
  rw [mem_actualPrimeFrontierTuples_iff]
  apply and_congr_right
  intro hs
  apply and_congr_right
  intro hp
  exact ordinaryUpperFive_parent_valid_iff Q hQ p (fun i => (hp i).2.1) hs

theorem mem_ordinaryUpperFiveFrontierTuples_iff_of_cutoff_le_cap
    (Q : ℝ) (hQ : 1 < Q) (N cap : ℕ) (w z : ℝ) (hzcap : z ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) :
    p ∈ firstExitFrontierTuples 4 (ordinaryParityRosserPolicy false Q)
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        (p 0 : ℝ) ^ 3 < Q ∧ (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < Q := by
  rw [mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 4 _ N cap w z hzcap]
  apply and_congr_right
  intro hs
  apply and_congr_right
  intro hp
  exact ordinaryUpperFive_parent_valid_iff Q hQ p (fun i => (hp i).1) hs

/-- The two literal cubic inequalities are exactly their logarithmic
affine inequalities; no rounded power or weak endpoint is substituted. -/
theorem ordinaryUpperFive_cube_tests_iff_log {N : ℕ} (hN : 1 < N)
    (old : ℝ) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ old ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ old) ↔
      3 * actualPrimeTupleLog N p 0 < old ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < old := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN'
  have hc i := actualPrimeTupleLog_rpow hN p hpos i
  have hcub (i : Fin 5) : (N : ℝ) ^ (3 * actualPrimeTupleLog N p i) = (p i : ℝ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hN0.le, hc]
    norm_num
  have hprod : (N : ℝ) ^ (actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2) = (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, hc, hc, hcub]
  rw [← hcub 0, ← hprod, Real.rpow_lt_rpow_left_iff hN', Real.rpow_lt_rpow_left_iff hN']

theorem mem_ordinaryUpperFiveFrontierTuples_iff_log
    (N cap : ℕ) (old w z : ℝ) (hN : 1 < N) (hold : 0 < old)
    (hzcap : z ≤ (cap : ℝ)) (p : Fin 5 → ℕ) :
    p ∈ firstExitFrontierTuples 4 (ordinaryParityRosserPolicy false ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        3 * actualPrimeTupleLog N p 0 < old ∧
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 < old := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hQ : (1 : ℝ) < (N : ℝ) ^ old := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hN' hold
  rw [mem_ordinaryUpperFiveFrontierTuples_iff_of_cutoff_le_cap _ hQ N cap w z hzcap]
  apply and_congr_right
  intro _hs
  apply and_congr_right
  intro hp
  exact ordinaryUpperFive_cube_tests_iff_log hN old p (fun i => (hp i).1.pos)

end

end ImbalancedChen
