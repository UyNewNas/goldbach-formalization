import ImbalancedChen.HistoricalUpperFiveCellGeometry
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-!
# P1: the historical fourth dictionary on a common mesh

The rank-three parent is the actual third-capped upper policy.  Its fourth
selection is inactive, so the fourth candidate set equals the admitted
rank-four set used by `actualHistoricalFourthSaving`.  The root first
threshold and the effective third ancestor threshold are kept separately.
This is finite geometry; no asymptotic density or certificate value is claimed.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical List BigOperators
open Set
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

private theorem p1_upper_three_iff (Q : ℝ) (p1 p2 p3 : ℕ)
    (h3 : 0 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
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
  have hu : UpperAdmissibleSet Q [p3, p2, p1].toFinset ↔
      (p1 : ℝ) ^ 3 < Q ∧ (p1 : ℝ) * p2 * p3 ^ 3 < Q := by
    simp only [List.toFinset_cons, List.toFinset_nil]
    change UpperAdmissibleSet Q S ↔ _
    simp only [UpperAdmissibleSet, S, Finset.forall_mem_insert,
      Finset.mem_singleton, forall_eq]
    rw [hf1, hf2, hf3]
    norm_num [S, h32.ne, h21.ne, h31.ne, Nat.cast_mul,
      pow_succ, mul_comm, mul_left_comm, mul_assoc, and_comm]
  have hs : (1 : ℝ) ≤ (p3 : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ p3 := by exact_mod_cast h3
    nlinarith
  have hp : (([p3, p2, p1].prod : ℕ) : ℝ) ≤
      (p1 : ℝ) * p2 * p3 ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hs
      (by positivity : (0 : ℝ) ≤ (p1 : ℝ) * p2 * p3)
    simp only [List.prod_cons, List.prod_nil, Nat.cast_mul, mul_one]
    nlinarith only [h]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false, hu]
  exact ⟨fun h => h.2, fun h => ⟨hp.trans_lt h.2, h⟩⟩

private theorem p1_upper_singleton_iff (Q : ℝ) (p : ℕ) (hp : 0 < p) :
    ordinaryRosserPrefixAdmissible false Q [p] ↔ (p : ℝ) ^ 3 < Q := by
  have hs : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hm : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) p)
    simpa only [mul_one, pow_succ, mul_comm] using h
  have hu : UpperAdmissibleSet Q [p].toFinset ↔ (p : ℝ) ^ 3 < Q := by
    simp [UpperAdmissibleSet, Finset.filter_singleton, pow_succ, mul_comm]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    List.prod_cons, List.prod_nil, mul_one]
  rw [hu]
  exact ⟨fun h => h.2, fun h => ⟨hm.trans_lt h, h⟩⟩

/-- Complete validity for a fourth tuple.  Its own cube is absent. -/
theorem p1_historicalUpperFourth_valid_iff (Q : ℝ) (Q3 : List ℕ → ℝ)
    (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hs : StrictAnti p)
    (hlevel : Q ≤ Q3 [p 2, p 1, p 0]) :
    FirstExitValidSelection
      (thirdCappedUpperPolicy (ordinaryParityRosserPolicy false Q) Q3)
      [] true (List.ofFn p) ↔
      (p 0 : ℝ) ^ 3 < Q ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < Q3 [p 2, p 1, p 0] := by
  have hv : FirstExitValidSelection
      (thirdCappedUpperPolicy (ordinaryParityRosserPolicy false Q) Q3)
      [] true (List.ofFn p) ↔
      ordinaryRosserPrefixAdmissible false Q [p 0] ∧
        ordinaryRosserPrefixAdmissible false (Q3 [p 2, p 1, p 0])
          [p 2, p 1, p 0] := by
    simp [List.ofFn_succ, FirstExitValidSelection, thirdCappedUpperPolicy,
      firstExitDepthSplicePolicy, frozenParityRosserPolicy, ancestorFrozenPolicy,
      ordinaryParityRosserPolicy, oddFirstExitPolicy, rosserAncestor]
  rw [hv, p1_upper_singleton_iff Q (p 0) (hp 0).pos,
    p1_upper_three_iff _ (p 0) (p 1) (p 2) (hp 2).pos
      (hs (by decide : (1 : Fin 4) < 2)) (hs (by decide : (0 : Fin 4) < 1))]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, h.1.trans_le hlevel, h.2⟩⟩

namespace HistoricalPrefixCapData

/-- Three order rows and the two historical parent rows. -/
def p1_fourthParentGateForms : Fin 5 → (Fin 4 → ℝ) →L[ℝ] ℝ :=
  let e (i : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  ![e 1 - e 0, e 2 - e 1, e 3 - e 2,
    (3 : ℝ) • e 0, e 0 + e 1 + (3 : ℝ) • e 2]

def p1_fourthParentGateBounds (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) : Fin 5 → ℝ :=
  ![0, 0, 0, (D.old : ℝ), (D.old4 j : ℝ)]

theorem p1_fourthParentGateForms_ne_zero : ∀ i, p1_fourthParentGateForms i ≠ 0 := by
  intro i h
  have hh := congrArg (fun F : (Fin 4 → ℝ) →L[ℝ] ℝ =>
    F (fun q => (q.val : ℝ) + 1)) h
  fin_cases i <;> norm_num [p1_fourthParentGateForms] at hh

theorem p1_mem_fourthParentGateRegion (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (t : Fin 4 → ℝ) :
    t ∈ primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j) ↔
      StrictAnti t ∧ 3 * t 0 < (D.old : ℝ) ∧
        t 0 + t 1 + 3 * t 2 < (D.old4 j : ℝ) := by
  have ha : StrictAnti t ↔ t 1 < t 0 ∧ t 2 < t 1 ∧ t 3 < t 2 := by
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
  simp only [ha]
  simp [primeAffineGateRegion, p1_fourthParentGateForms,
    p1_fourthParentGateBounds, Fin.forall_fin_succ, and_assoc]

/-- The old fourth level reads its actual projected third owner. -/
theorem p1_level3_on_fourth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 4)
    (j : Fin 4 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 4 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 N (rosserAncestor 3 history) = N ^ (D.old4 j : ℝ) := by
  unfold level3 old4
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 4) hlen]
  rw [D.exponent3_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)]

theorem p1_level3_tuple_on_fourth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℕ) (p : Fin 4 → ℕ) (j : Fin 4 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 (N : ℝ) [p 2, p 1, p 0] = (N : ℝ) ^ (D.old4 j : ℝ) := by
  have hc : primeHistoryLogCoordinates (N : ℝ) 4 [p 3, p 2, p 1, p 0] =
      actualPrimeTupleLog N p := by
    funext i
    fin_cases i <;> rfl
  have ht' : primeHistoryLogCoordinates (N : ℝ) 4 [p 3, p 2, p 1, p 0] ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j := by
    rw [hc]
    exact ht
  simpa [rosserAncestor] using
    D.p1_level3_on_fourth_cell hab (N : ℝ) [p 3, p 2, p 1, p 0] (by simp) j ht'

/-- The new fourth value and its fallback share that same owner. -/
theorem p1_level4_on_fourth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (j : Fin 4 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 4 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level4 N history = N ^ (D.cell4 j : ℝ) := by
  unfold level4
  rw [D.exponent4_on_cell hab _ _ ht]

end HistoricalPrefixCapData

private theorem p1_fourth_cube_tests_iff_log {N : ℕ} (hN : 1 < N)
    (old third : ℝ) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ old ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ third) ↔
      3 * actualPrimeTupleLog N p 0 < old ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < third := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hc i := actualPrimeTupleLog_rpow hN p hp i
  have hcube (i : Fin 4) :
      (N : ℝ) ^ (3 * actualPrimeTupleLog N p i) = (p i : ℝ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hn0.le, hc]
    norm_num
  have hprod : (N : ℝ) ^ (actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2) = (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 := by
    rw [Real.rpow_add hn0, Real.rpow_add hn0, hc, hc, hcube]
  rw [← hcube 0, ← hprod, Real.rpow_lt_rpow_left_iff hn,
    Real.rpow_lt_rpow_left_iff hn]

/-- Real fourth selections on the historical tree, with target deletion
and strict cutoff.  No fourth old/new own-cube gate is inserted. -/
theorem p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j : Fin 4 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧ 0 ≤ (p i : ℝ) ∧
          (p i : ℝ) < (N : ℝ) ^ (D.b : ℝ)) ∧
        3 * actualPrimeTupleLog N p 0 < (D.old : ℝ) ∧
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 < (D.old4 j : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hl : (N : ℝ) ^ (D.old : ℝ) ≤ D.level3 (N : ℝ) [p 2, p 1, p 0] := by
    unfold HistoricalPrefixCapData.level3
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    exact_mod_cast D.old_le_exponent3 hcheck
      (primeHistoryLogCoordinates (N : ℝ) 3 [p 2, p 1, p 0])
  rw [mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 4 _ N cap 0 _ hcap]
  apply and_congr_right
  intro hs
  apply and_congr_right
  intro hp
  change FirstExitValidSelection
    (thirdCappedUpperPolicy (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
      (D.level3 (N : ℝ))) [] true (List.ofFn p) ↔ _
  rw [p1_historicalUpperFourth_valid_iff _ _ p (fun i => (hp i).1) hs hl,
    D.p1_level3_tuple_on_fourth_cell hab N p j ht]
  exact p1_fourth_cube_tests_iff_log hN (D.old : ℝ) (D.old4 j : ℝ)
    p (fun i => (hp i).1.pos)

/-- Exact joint-cell dictionary for the tuple set actually summed by the
fourth historical saving.  Both selected and fallback T3 cells are covered. -/
theorem p1_historicalUpperFourthAdmittedTuples_cell_filter
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) :
    (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion HistoricalPrefixCapData.p1_fourthParentGateForms
              (D.p1_fourthParentGateBounds j)) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hf, ht⟩
    have hh := (p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
      D hab.le hcheck N cap hN hcap p j ht).mp hf
    have hp : p ∈ actualPrimeBoxTuples N
        (fun _ : Fin 4 => (D.a : ℝ)) (fun _ => (D.b : ℝ)) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hh.2.1 i).1, (hh.2.1 i).2.1⟩,
          logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht⟩
    refine ⟨hp, ht, (D.p1_mem_fourthParentGateRegion j _).mpr ⟨?_, hh.2.2⟩⟩
    exact (actualPrimeTupleLog_strictAnti_iff hN p
      (fun i => (hh.2.1 i).1.pos)).mpr hh.1
  · rintro ⟨hp, ht, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hh := (D.p1_mem_fourthParentGateRegion j _).mp hg
    refine ⟨(p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
      D hab.le hcheck N cap hN hcap p j ht).mpr ⟨?_, ?_, hh.2⟩, ht⟩
    · exact (actualPrimeTupleLog_strictAnti_iff hN p
        (fun i => (hpi i).1.pos)).mp hh.1
    · exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

/-- The fourth even test is identically retained.  Thus a next candidate
at rank three is precisely an admitted fourth tuple, on any carrier. -/
theorem p1_historicalUpperFourth_candidates_eq_admitted
    (D : HistoricalPrefixCapData) (N : ℝ) (carrier : List ℕ) :
    firstExitFrontierTuples 3 (D.upperThirdPolicy N) carrier =
      firstExitAdmittedTuples 4 (D.upperThirdPolicy N) carrier := by
  ext p
  rw [mem_firstExitFrontierTuples_iff, mem_firstExitAdmittedTuples_iff]
  apply and_congr_right
  intro _hsub
  simp [List.ofFn_succ, FirstExitValidSelection,
    HistoricalPrefixCapData.upperThirdPolicy_even]

/-- The same dictionary also describes literal rank-three next candidates. -/
theorem p1_historicalUpperFourthCandidateTuples_cell_filter
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) :
    (firstExitFrontierTuples 3 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion HistoricalPrefixCapData.p1_fourthParentGateForms
              (D.p1_fourthParentGateBounds j)) := by
  rw [p1_historicalUpperFourth_candidates_eq_admitted]
  exact p1_historicalUpperFourthAdmittedTuples_cell_filter
    D hab hcheck N cap hN hcap j

end
end ImbalancedChen
