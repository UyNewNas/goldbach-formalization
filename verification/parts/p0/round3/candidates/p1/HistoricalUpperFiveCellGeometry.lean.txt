import ImbalancedChen.HistoricalPrefixCertificate
import ImbalancedChen.OrdinaryPrimeFrontierAffineRegion
import ImbalancedChen.OrdinaryUpperFiveAffineGates
import ImbalancedChen.ActualOwnCubeTupleDictionary

/-!
# Actual historical fifth candidates on a common owned cell

The rank-four parent is the actual third-capped upper tree.  Its first
cube keeps the ordinary root level; its third cube uses the effective
third ancestor cell, including that cell's fallback.  The fourth level
does not filter the next candidates.  It supplies their old residual
level, separately from the new fifth level and its own-cube indicator.

The finite data are fixed before the target.  All dictionaries below keep
the original target-deleted primes, strict processing order, strict power
cutoff and half-open ownership.  This module supplies a cell geometry
interface, not the reported independently compiled fifth-integral source
or a global density limit for the adopted manuscript construction.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators
open Set
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

namespace HistoricalPrefixCapData

/-- The first test keeps the root cap; the third test reads its effective
ancestor cap on this same fifth cell.  The fifth own cube is absent. -/
def fifthParentGateBounds (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Fin 6 → ℝ :=
  ![0, 0, 0, 0, (D.old : ℝ),
    (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)]

/-- The six existing nonzero rows now have their two actual historical
thresholds.  No fourth or fifth admission condition is introduced. -/
theorem mem_fifthParentGateRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ) :
    t ∈ primeAffineGateRegion ordinaryUpperFiveGateForms
        (D.fifthParentGateBounds j) ↔
      StrictAnti t ∧ 3 * t 0 < (D.old : ℝ) ∧
        t 0 + t 1 + 3 * t 2 <
          (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
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
  simp [primeAffineGateRegion, ordinaryUpperFiveGateForms,
    fifthParentGateBounds, Fin.forall_fin_succ, and_assoc]

/-- A five-prime history fixes its third ancestor's effective level on
the projected owner, whether or not that ancestor cell was selected. -/
theorem level3_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5)
    (j : Fin 5 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 N (rosserAncestor 3 history) =
      N ^ (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  unfold level3
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 5) hlen]
  rw [D.exponent3_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht)]

/-- The old fifth residual reads the complete effective fourth cell,
including an unselected fourth cell's inherited third level. -/
theorem level4_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5)
    (j : Fin 5 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level4 N (rosserAncestor 4 history) = N ^ (D.old5 j : ℝ) := by
  unfold level4 old5
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 4 ≤ 5) hlen]
  rw [D.exponent4_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)]

/-- The effective fifth cell includes its exact inherited fallback. -/
theorem level5_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ)
    (j : Fin 5 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = N ^ (D.cell5 j : ℝ) := by
  unfold level5
  rw [D.exponent5_on_cell hab _ _ ht]

/-- On an adopted fifth cell the new residual uses its stored cap; this
statement does not impose either the old or the new own-cube test. -/
theorem level5_on_selected_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = N ^ (D.cap5 j : ℝ) := by
  rw [D.level5_on_fifth_cell hab N history j ht, cell5, if_pos hj]

/-- The actual processing-order tuple and the reverse-stored third
history select the same projected owner. -/
theorem level3_tuple_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℕ) (p : Fin 5 → ℕ) (j : Fin 5 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 (N : ℝ) [p 2, p 1, p 0] =
      (N : ℝ) ^ (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  have hcoords :
      primeHistoryLogCoordinates (N : ℝ) 5 [p 4, p 3, p 2, p 1, p 0] =
        actualPrimeTupleLog N p := by
    funext i
    fin_cases i <;> rfl
  have ht' : primeHistoryLogCoordinates (N : ℝ) 5 [p 4, p 3, p 2, p 1, p 0] ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j := by
    rw [hcoords]
    exact ht
  simpa [rosserAncestor] using
    D.level3_on_fifth_cell hab (N : ℝ) [p 4, p 3, p 2, p 1, p 0] (by simp) j ht'

end HistoricalPrefixCapData

private theorem historicalUpperFive_singleton_admissible_iff
    (Q : ℝ) (p : ℕ) (hp : 0 < p) :
    ordinaryRosserPrefixAdmissible false Q [p] ↔ (p : ℝ) ^ 3 < Q := by
  have hsq : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hprod : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) p)
    simpa only [mul_one, pow_succ, mul_comm] using hm
  have hc : UpperAdmissibleSet Q [p].toFinset ↔ (p : ℝ) ^ 3 < Q := by
    simp [UpperAdmissibleSet, pow_succ, mul_comm]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    List.prod_cons, List.prod_nil, mul_one]
  rw [hc]
  exact ⟨fun h => h.2, fun h => ⟨hprod.trans_lt h, h⟩⟩

/-- The ordinary short-prefix supplier pays the complete third-parent
test.  Only its first test is strengthened back to the actual root cap. -/
private theorem historicalUpperFive_parent_valid_iff
    (Q : ℝ) (hQ : 1 < Q) (Q3 : List ℕ → ℝ)
    (p : Fin 5 → ℕ) (hprime : ∀ i, Nat.Prime (p i)) (hsort : StrictAnti p)
    (hlevel : Q ≤ Q3 [p 2, p 1, p 0]) :
    FirstExitValidSelection
        (thirdCappedUpperPolicy (ordinaryParityRosserPolicy false Q) Q3)
        [] true (List.ofFn p).dropLast ↔
      (p 0 : ℝ) ^ 3 < Q ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < Q3 [p 2, p 1, p 0] := by
  have hdrop : (List.ofFn p).dropLast = [p 0, p 1, p 2, p 3] := by
    simp [List.ofFn_succ]
  have hordinary :
      (ordinaryRosserPrefixAdmissible false (Q3 [p 2, p 1, p 0]) [p 0] ∧
        ordinaryRosserPrefixAdmissible false (Q3 [p 2, p 1, p 0]) [p 2, p 1, p 0]) ↔
      (p 0 : ℝ) ^ 3 < Q3 [p 2, p 1, p 0] ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < Q3 [p 2, p 1, p 0] := by
    simpa [hdrop, FirstExitValidSelection, ordinaryParityRosserPolicy,
      oddFirstExitPolicy] using ordinaryUpperFive_parent_valid_iff
        (Q3 [p 2, p 1, p 0]) (hQ.trans_le hlevel) p hprime hsort
  have hhistorical :
      FirstExitValidSelection
          (thirdCappedUpperPolicy (ordinaryParityRosserPolicy false Q) Q3)
          [] true (List.ofFn p).dropLast ↔
        ordinaryRosserPrefixAdmissible false Q [p 0] ∧
          ordinaryRosserPrefixAdmissible false (Q3 [p 2, p 1, p 0]) [p 2, p 1, p 0] := by
    rw [hdrop]
    simp [FirstExitValidSelection, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
      frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
      oddFirstExitPolicy, rosserAncestor]
  rw [hhistorical]
  constructor
  · rintro ⟨hfirst, hthird⟩
    refine ⟨(historicalUpperFive_singleton_admissible_iff Q (p 0) (hprime 0).pos).mp
      hfirst, ?_⟩
    exact (hordinary.mp ⟨ordinaryRosserPrefixAdmissible_mono false [p 0]
      hlevel hfirst, hthird⟩).2
  · rintro ⟨hfirst, hthird⟩
    refine ⟨(historicalUpperFive_singleton_admissible_iff Q (p 0) (hprime 0).pos).mpr
      hfirst, ?_⟩
    exact (hordinary.mpr ⟨hfirst.trans_le hlevel, hthird⟩).2

/-- The first and third power tests may use different historical levels.
Both logarithmic inequalities retain their strict endpoints. -/
theorem historicalUpperFive_cube_tests_iff_log {N : ℕ} (hN : 1 < N)
    (old third : ℝ) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ old ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ third) ↔
      3 * actualPrimeTupleLog N p 0 < old ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < third := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN'
  have hc i := actualPrimeTupleLog_rpow hN p hpos i
  have hcub (i : Fin 5) :
      (N : ℝ) ^ (3 * actualPrimeTupleLog N p i) = (p i : ℝ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hN0.le, hc]
    norm_num
  have hprod :
      (N : ℝ) ^ (actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
        3 * actualPrimeTupleLog N p 2) = (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, hc, hc, hcub]
  rw [← hcub 0, ← hprod, Real.rpow_lt_rpow_left_iff hN', Real.rpow_lt_rpow_left_iff hN']

/-- The actual third-capped frontier, on a fixed owned fifth cell, has
the target deletion and the two correct historical cube thresholds.
The fifth candidate is not filtered by either residual own-cube test. -/
theorem mem_historicalUpperFiveFrontierTuples_iff_log_on_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
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
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 <
              (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hQ : (1 : ℝ) < (N : ℝ) ^ (D.old : ℝ) := by
    have ho : (0 : ℝ) < D.old := by exact_mod_cast hold
    simpa using Real.rpow_lt_rpow_of_exponent_lt hN' ho
  have hlevel : (N : ℝ) ^ (D.old : ℝ) ≤ D.level3 (N : ℝ) [p 2, p 1, p 0] := by
    unfold HistoricalPrefixCapData.level3
    apply Real.rpow_le_rpow_of_exponent_le hN'.le
    exact_mod_cast D.old_le_exponent3 hcheck
      (primeHistoryLogCoordinates (N : ℝ) 3 [p 2, p 1, p 0])
  rw [mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 4 _ N cap 0 _ hcap]
  apply and_congr_right
  intro hsort
  apply and_congr_right
  intro hprime
  change FirstExitValidSelection
    (thirdCappedUpperPolicy
      (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
      (D.level3 (N : ℝ))) [] true (List.ofFn p).dropLast ↔ _
  rw [historicalUpperFive_parent_valid_iff _ hQ (D.level3 (N : ℝ)) p
    (fun i => (hprime i).1) hsort hlevel,
    D.level3_tuple_on_fifth_cell hab N p j ht]
  exact historicalUpperFive_cube_tests_iff_log hN (D.old : ℝ)
    (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) p
    (fun i => (hprime i).1.pos)

/-- Exact equality of the real historical candidate cell with its
target-deleted prime box and fixed affine parent region.  Half-open
ownership and the original strict prime cutoff are unchanged. -/
theorem historicalUpperFiveFrontierTuples_cell_filter
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
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
            primeAffineGateRegion ordinaryUpperFiveGateForms
              (D.fifthParentGateBounds j)) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hf, ht⟩
    have hh := (mem_historicalUpperFiveFrontierTuples_iff_log_on_cell
      D hab.le hold hcheck N cap hN hcap p j ht).mp hf
    have hp : p ∈ actualPrimeBoxTuples N
        (fun _ : Fin 5 => (D.a : ℝ)) (fun _ => (D.b : ℝ)) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hh.2.1 i).1, (hh.2.1 i).2.1⟩,
          logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht⟩
    refine ⟨hp, ht, (D.mem_fifthParentGateRegion j _).mpr ⟨?_, hh.2.2⟩⟩
    exact (actualPrimeTupleLog_strictAnti_iff hN p
      (fun i => (hh.2.1 i).1.pos)).mpr hh.1
  · rintro ⟨hp, ht, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hh := (D.mem_fifthParentGateRegion j _).mp hg
    refine ⟨(mem_historicalUpperFiveFrontierTuples_iff_log_on_cell
      D hab.le hold hcheck N cap hN hcap p j ht).mpr ⟨?_, ?_, hh.2⟩, ht⟩
    · exact (actualPrimeTupleLog_strictAnti_iff hN p
        (fun i => (hpi i).1.pos)).mp hh.1
    · exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

end

end ImbalancedChen
