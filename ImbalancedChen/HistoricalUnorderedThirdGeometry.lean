import ImbalancedChen.FinitePrimeGeometryCore
import ImbalancedChen.FirstExitFrontierTupleReindex
import ImbalancedChen.AffinePrimeGates

/-!
# Historical fifth-parent geometry when the third level can decrease

The actual rank-three test rechecks the first cube at its own level.  When
that level is below the initial level, the two first-cube tests cannot be
merged by monotonicity.  This file retains both of them, plus the third
cube, without imposing an ordering or positivity assumption on the caps.

The resulting seven-row cell dictionary is for the literal third-capped
tree.  It does not identify a finite cap table with the manuscript's rough
activation rule, and does not prove any distribution or integral bound.
The previous six-row dictionary remains valid under its stronger hypotheses.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators
open Set
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

private theorem unorderedThird_singleton_admissible_iff
    (Q : ℝ) (p : ℕ) (hp : 0 < p) :
    ordinaryRosserPrefixAdmissible false Q [p] ↔ (p : ℝ) ^ 3 < Q := by
  have hsq : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hprod : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) p)
    simpa only [mul_one, pow_succ, mul_comm] using hm
  have hc : UpperAdmissibleSet Q [p].toFinset ↔ (p : ℝ) ^ 3 < Q := by
    simp [UpperAdmissibleSet, Finset.filter_singleton, pow_succ, mul_comm]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    List.prod_cons, List.prod_nil, mul_one]
  rw [hc]
  exact ⟨fun h => h.2, fun h => ⟨hprod.trans_lt h, h⟩⟩

/-- The full third-prefix test includes its own inherited first cube.
Its last cube already pays the strict total-product cutoff. -/
theorem historicalUnorderedThird_admissible_iff
    (Q : ℝ) (p1 p2 p3 : ℕ) (h3 : 0 < p3)
    (h32 : p3 < p2) (h21 : p2 < p1) :
    ordinaryRosserPrefixAdmissible false Q [p3, p2, p1] ↔
      (p1 : ℝ) ^ 3 < Q ∧ (p1 : ℝ) * p2 * p3 ^ 3 < Q := by
  have h31 := h32.trans h21
  let S : Finset ℕ := {p3, p2, p1}
  have hf1 : S.filter (fun p => p1 ≤ p) = {p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf2 : S.filter (fun p => p2 ≤ p) = {p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf3 : S.filter (fun p => p3 ≤ p) = S := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hc : UpperAdmissibleSet Q [p3, p2, p1].toFinset ↔
      (p1 : ℝ) ^ 3 < Q ∧ (p1 : ℝ) * p2 * p3 ^ 3 < Q := by
    simp only [List.toFinset_cons, List.toFinset_nil]
    change UpperAdmissibleSet Q S ↔ _
    simp only [UpperAdmissibleSet, S, Finset.forall_mem_insert,
      Finset.mem_singleton, forall_eq]
    rw [hf1, hf2, hf3]
    norm_num [S, h32.ne, h21.ne, h31.ne, Nat.cast_mul, pow_succ,
      mul_comm, mul_left_comm, mul_assoc, and_comm]
  have hsq : (1 : ℝ) ≤ (p3 : ℝ) ^ 2 := by
    have hp3 : (1 : ℝ) ≤ p3 := by exact_mod_cast h3
    nlinarith
  have hprod : (([p3, p2, p1].prod : ℕ) : ℝ) ≤
      (p1 : ℝ) * p2 * p3 ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hsq
      (by positivity : (0 : ℝ) ≤ (p1 : ℝ) * p2 * p3)
    simp only [List.prod_cons, List.prod_nil, Nat.cast_mul, mul_one]
    nlinarith only [hh]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false, hc]
  exact ⟨fun h => h.2, fun h => ⟨hprod.trans_lt h.2, h⟩⟩

/-- Exact proper-parent validity, even when the third level is smaller
than the initial level.  No fifth own-cube test filters the candidates. -/
theorem historicalUnorderedThird_parent_valid_iff
    (Q : ℝ) (Q3 : List ℕ → ℝ) (p : Fin 5 → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hsort : StrictAnti p) :
    FirstExitValidSelection
        (thirdCappedUpperPolicy (ordinaryParityRosserPolicy false Q) Q3)
        [] true (List.ofFn p).dropLast ↔
      (p 0 : ℝ) ^ 3 < Q ∧
        (p 0 : ℝ) ^ 3 < Q3 [p 2, p 1, p 0] ∧
          (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < Q3 [p 2, p 1, p 0] := by
  have hdrop : (List.ofFn p).dropLast = [p 0, p 1, p 2, p 3] := by
    simp [List.ofFn_succ]
  have hhistory :
      FirstExitValidSelection
          (thirdCappedUpperPolicy (ordinaryParityRosserPolicy false Q) Q3)
          [] true (List.ofFn p).dropLast ↔
        ordinaryRosserPrefixAdmissible false Q [p 0] ∧
          ordinaryRosserPrefixAdmissible false (Q3 [p 2, p 1, p 0]) [p 2, p 1, p 0] := by
    rw [hdrop]
    simp [FirstExitValidSelection, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
      frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
      oddFirstExitPolicy, rosserAncestor]
  rw [hhistory, unorderedThird_singleton_admissible_iff Q (p 0) (hprime 0).pos,
    historicalUnorderedThird_admissible_iff _ (p 0) (p 1) (p 2) (hprime 2).pos
      (hsort (by decide : (1 : Fin 5) < 2))
      (hsort (by decide : (0 : Fin 5) < 1))]

/-- Four ordering rows, the initial first cube, the inherited first cube
at the third level, and the third cube.  Each row is nonzero. -/
def historicalUnorderedThirdGateForms : Fin 7 → (Fin 5 → ℝ) →L[ℝ] ℝ :=
  let e (i : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  ![e 1 - e 0, e 2 - e 1, e 3 - e 2, e 4 - e 3,
    (3 : ℝ) • e 0, (3 : ℝ) • e 0, e 0 + e 1 + (3 : ℝ) • e 2]

def historicalUnorderedThirdGateBounds (initial third : ℝ) : Fin 7 → ℝ :=
  ![0, 0, 0, 0, initial, third, third]

theorem historicalUnorderedThirdGateForms_ne_zero :
    ∀ j, historicalUnorderedThirdGateForms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun F : (Fin 5 → ℝ) →L[ℝ] ℝ => F (fun i => (i.val : ℝ) + 1)) h
  fin_cases j <;> norm_num [historicalUnorderedThirdGateForms] at hh

theorem mem_historicalUnorderedThirdGateRegion (initial third : ℝ) (t : Fin 5 → ℝ) :
    t ∈ primeAffineGateRegion historicalUnorderedThirdGateForms
        (historicalUnorderedThirdGateBounds initial third) ↔
      StrictAnti t ∧ 3 * t 0 < initial ∧ 3 * t 0 < third ∧
        t 0 + t 1 + 3 * t 2 < third := by
  have hanti : StrictAnti t ↔
      t 1 < t 0 ∧ t 2 < t 1 ∧ t 3 < t 2 ∧ t 4 < t 3 := by
    constructor
    · intro h
      exact ⟨h (by decide), h (by decide), h (by decide), h (by decide)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
      · exact h4
  simp only [hanti]
  simp [primeAffineGateRegion, historicalUnorderedThirdGateForms,
    historicalUnorderedThirdGateBounds, Fin.forall_fin_succ, and_assoc]

theorem historicalUnorderedThird_cube_tests_iff_log {N : ℕ} (hN : 1 < N)
    (initial third : ℝ) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ initial ∧
      (p 0 : ℝ) ^ 3 < (N : ℝ) ^ third ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ third) ↔
      3 * actualPrimeTupleLog N p 0 < initial ∧
        3 * actualPrimeTupleLog N p 0 < third ∧
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 < third := by
  have hfirst := historicalUpperFive_cube_tests_iff_log hN initial third p hpos
  have hthird := ordinaryUpperFive_cube_tests_iff_log hN third p hpos
  constructor
  · rintro ⟨hi, ht, hc⟩
    exact ⟨(hfirst.mp ⟨hi, hc⟩).1, hthird.mp ⟨ht, hc⟩⟩
  · rintro ⟨hi, ht, hc⟩
    exact ⟨(hfirst.mpr ⟨hi, hc⟩).1, hthird.mpr ⟨ht, hc⟩⟩

/-- The actual next-candidate frontier on an owned fifth cell, without
`levelCheck` or an initial-to-third level comparison. -/
theorem mem_historicalUnorderedThirdFrontierTuples_iff_log_on_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (j : Fin 5 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          0 ≤ (p i : ℝ) ∧ (p i : ℝ) < (N : ℝ) ^ (D.b : ℝ)) ∧
        3 * actualPrimeTupleLog N p 0 < (D.old : ℝ) ∧
          3 * actualPrimeTupleLog N p 0 <
            (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) ∧
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 <
              (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  rw [mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 4 _ N cap 0 _ hcap]
  apply and_congr_right
  intro hsort
  apply and_congr_right
  intro hprime
  change FirstExitValidSelection
    (thirdCappedUpperPolicy
      (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
      (D.level3 (N : ℝ))) [] true (List.ofFn p).dropLast ↔ _
  rw [historicalUnorderedThird_parent_valid_iff _ (D.level3 (N : ℝ)) p
    (fun i => (hprime i).1) hsort,
    D.level3_tuple_on_fifth_cell hab N p j ht]
  exact historicalUnorderedThird_cube_tests_iff_log hN (D.old : ℝ)
    (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) p
    (fun i => (hprime i).1.pos)

/-- Literal cell equality ready for the existing affine-cell integral
supplier.  Ownership remains half-open and all three cube tests strict. -/
theorem historicalUnorderedThirdFrontierTuples_cell_filter
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) :
    (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion historicalUnorderedThirdGateForms
              (historicalUnorderedThirdGateBounds (D.old : ℝ)
                (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ))) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hf, ht⟩
    have hh := (mem_historicalUnorderedThirdFrontierTuples_iff_log_on_cell
      D hab.le N cap hN hcap p j ht).mp hf
    have hp : p ∈ actualPrimeBoxTuples N
        (fun _ : Fin 5 => (D.a : ℝ)) (fun _ => (D.b : ℝ)) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hh.2.1 i).1, (hh.2.1 i).2.1⟩,
          logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht⟩
    refine ⟨hp, ht, (mem_historicalUnorderedThirdGateRegion _ _ _).mpr
      ⟨?_, hh.2.2⟩⟩
    exact (actualPrimeTupleLog_strictAnti_iff hN p
      (fun i => (hh.2.1 i).1.pos)).mpr hh.1
  · rintro ⟨hp, ht, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hh := (mem_historicalUnorderedThirdGateRegion _ _ _).mp hg
    refine ⟨(mem_historicalUnorderedThirdFrontierTuples_iff_log_on_cell
      D hab.le N cap hN hcap p j ht).mpr ⟨?_, ?_, hh.2⟩, ht⟩
    · exact (actualPrimeTupleLog_strictAnti_iff hN p
        (fun i => (hpi i).1.pos)).mp hh.1
    · exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

end

end ImbalancedChen
