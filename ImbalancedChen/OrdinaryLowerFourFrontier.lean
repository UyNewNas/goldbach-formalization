import ImbalancedChen.FirstExitFrontierTupleReindex
import ImbalancedChen.RosserShortPrefixAdmissibility
import ImbalancedChen.OrdinaryUpperFiveAffineGates

/-!
# The actual ordinary lower fourth-candidate frontier

The lower parent stops after three selections. Its first and third tests
are inactive, and its only active test is the second cubic inequality.
The fourth candidate is enumerated before its own admission test. The
old and new fourth own-cube gates therefore remain separate residual
factors, rather than conditions on this frontier.

The arithmetic dictionary retains the target deletion, the strict
enumeration cap and the original real endpoints. Processing coordinates
are strictly decreasing; the selected history is stored in reverse.
This finite dictionary does not assert an integral or a numerical bound.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators
open Set
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

private theorem lowerRosserAdmissibleSet_two_iff
    (Q : ℝ) (p1 p2 : ℕ) (h21 : p2 < p1) :
    LowerAdmissibleSet Q [p2, p1].toFinset ↔
      (p1 : ℝ) * p2 ^ 3 < Q := by
  let S : Finset ℕ := {p2, p1}
  have hf1 : S.filter (fun p => p1 ≤ p) = {p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf2 : S.filter (fun p => p2 ≤ p) = S := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [List.toFinset_cons, List.toFinset_nil]
  change LowerAdmissibleSet Q S ↔ _
  simp only [LowerAdmissibleSet, S, Finset.forall_mem_insert,
    Finset.mem_singleton, forall_eq]
  rw [hf1, hf2]
  norm_num [S, h21.ne, Nat.cast_mul, pow_succ,
    mul_comm, mul_left_comm, mul_assoc]

/-- At the lower second test the own cube also pays the complete
strict product cutoff. No primality beyond positivity is needed. -/
theorem ordinaryRosserPrefixAdmissible_lower_two_iff
    (Q : ℝ) (p1 p2 : ℕ) (h2 : 0 < p2) (h21 : p2 < p1) :
    ordinaryRosserPrefixAdmissible true Q [p2, p1] ↔
      (p1 : ℝ) * p2 ^ 3 < Q := by
  have hsq : (1 : ℝ) ≤ (p2 : ℝ) ^ 2 := by
    have hp : (1 : ℝ) ≤ p2 := by exact_mod_cast h2
    nlinarith
  have hprod : (([p2, p1].prod : ℕ) : ℝ) ≤ (p1 : ℝ) * p2 ^ 3 := by
    calc
      _ = (p1 : ℝ) * p2 := by
        simp [List.prod_cons, Nat.cast_mul, mul_comm]
      _ ≤ ((p1 : ℝ) * p2) * p2 ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq
          (by positivity : (0 : ℝ) ≤ (p1 : ℝ) * p2)
      _ = (p1 : ℝ) * p2 ^ 3 := by ring
  simp only [ordinaryRosserPrefixAdmissible, if_true,
    lowerRosserAdmissibleSet_two_iff Q p1 p2 h21]
  exact ⟨fun h => h.2, fun h => ⟨hprod.trans_lt h, h⟩⟩

/-- The proper parent tests only the second cube. The fourth candidate's
own cube is absent, and the inactive first and third tests need no
additional level or cutoff hypothesis for this finite identity. -/
theorem ordinaryLowerFour_parent_valid_iff
    (Q : ℝ) (p : Fin 4 → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hsort : StrictAnti p) :
    FirstExitValidSelection (ordinaryParityRosserPolicy true Q) [] true
      (List.ofFn p).dropLast ↔
      (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < Q := by
  have hdrop : (List.ofFn p).dropLast = [p 0, p 1, p 2] := by
    simp [List.ofFn_succ]
  rw [hdrop]
  simp [FirstExitValidSelection, ordinaryParityRosserPolicy, evenFirstExitPolicy,
    ordinaryRosserPrefixAdmissible_lower_two_iff Q (p 0) (p 1)
      (hprime 1).pos (hsort (by decide : (0 : Fin 4) < 1))]

/-- Literal membership on the same actual prime carrier, including
`p < cap`, target deletion, and strict right endpoints. -/
theorem mem_ordinaryLowerFourFrontierTuples_iff
    (Q : ℝ) (N cap : ℕ) (w z : ℝ) (p : Fin 4 → ℕ) :
    p ∈ firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true Q)
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, p i < cap ∧ Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < Q := by
  rw [mem_actualPrimeFrontierTuples_iff]
  apply and_congr_right
  intro hs
  apply and_congr_right
  intro hp
  exact ordinaryLowerFour_parent_valid_iff Q p (fun i => (hp i).2.1) hs

/-- Cap coverage removes only the redundant integer enumeration test;
all prime, target, order, and strict cutoff conditions remain. -/
theorem mem_ordinaryLowerFourFrontierTuples_iff_of_cutoff_le_cap
    (Q : ℝ) (N cap : ℕ) (w z : ℝ) (hzcap : z ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) :
    p ∈ firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true Q)
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < Q := by
  rw [mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 3 _ N cap w z hzcap]
  apply and_congr_right
  intro hs
  apply and_congr_right
  intro hp
  exact ordinaryLowerFour_parent_valid_iff Q p (fun i => (hp i).1) hs

/-- The actual second cubic test has this exact strict logarithmic form.
Natural prime labels and the literal real power are unchanged. -/
theorem ordinaryLowerFour_cube_test_iff_log {N : ℕ} (hN : 1 < N)
    (old : ℝ) (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) :
    (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < (N : ℝ) ^ old ↔
      actualPrimeTupleLog N p 0 + 3 * actualPrimeTupleLog N p 1 < old := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN'
  have hc i := actualPrimeTupleLog_rpow hN p hpos i
  have hcub : (N : ℝ) ^ (3 * actualPrimeTupleLog N p 1) = (p 1 : ℝ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hN0.le, hc]
    norm_num
  have hprod : (N : ℝ) ^ (actualPrimeTupleLog N p 0 +
      3 * actualPrimeTupleLog N p 1) = (p 0 : ℝ) * (p 1 : ℝ) ^ 3 := by
    rw [Real.rpow_add hN0, hc, hcub]
  rw [← hprod, Real.rpow_lt_rpow_left_iff hN']

/-- Exact logarithmic dictionary for the actual lower fourth candidate.
No old fourth own-cube test filters the candidate enumeration. -/
theorem mem_ordinaryLowerFourFrontierTuples_iff_log
    (N cap : ℕ) (old w z : ℝ) (hN : 1 < N)
    (hzcap : z ≤ (cap : ℝ)) (p : Fin 4 → ℕ) :
    p ∈ firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        actualPrimeTupleLog N p 0 + 3 * actualPrimeTupleLog N p 1 < old := by
  rw [mem_ordinaryLowerFourFrontierTuples_iff_of_cutoff_le_cap _ N cap w z hzcap]
  apply and_congr_right
  intro _hs
  apply and_congr_right
  intro hp
  exact ordinaryLowerFour_cube_test_iff_log hN old p (fun i => (hp i).1.pos)

/-- Three strict order rows and the single inherited second-cube row.
Each old or new fourth own-cube row is attached separately by the
existing residual-integral supplier. -/
def ordinaryLowerFourGateForms : Fin 4 → (Fin 4 → ℝ) →L[ℝ] ℝ :=
  let e (i : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  ![e 1 - e 0, e 2 - e 1, e 3 - e 2, e 0 + (3 : ℝ) • e 1]

def ordinaryLowerFourGateBounds (old : ℝ) : Fin 4 → ℝ := ![0, 0, 0, old]

theorem ordinaryLowerFourGateForms_ne_zero : ∀ j, ordinaryLowerFourGateForms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun F : (Fin 4 → ℝ) →L[ℝ] ℝ =>
    F (fun i => (i.val : ℝ) + 1)) h
  fin_cases j <;> norm_num [ordinaryLowerFourGateForms] at hh

theorem mem_ordinaryLowerFourGateRegion (old : ℝ) (t : Fin 4 → ℝ) :
    t ∈ primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old) ↔
      StrictAnti t ∧ t 0 + 3 * t 1 < old := by
  have hanti : StrictAnti t ↔ t 1 < t 0 ∧ t 2 < t 1 ∧ t 3 < t 2 := by
    constructor
    · intro h
      exact ⟨h (by decide), h (by decide), h (by decide)⟩
    · rintro ⟨h1, h2, h3⟩
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
  simp only [hanti]
  simp [primeAffineGateRegion, ordinaryLowerFourGateForms, ordinaryLowerFourGateBounds,
    Fin.forall_fin_succ, and_assoc]

end

end ImbalancedChen
