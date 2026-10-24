import ImbalancedChen.P1ActualCoarseLowRankSupport
import ImbalancedChen.ActualHistoricalThirdTupleDictionary
import ImbalancedChen.P1ActualHistoricalThirdCellPartition

/-!
# The actual original coarse coefficient on ordered prime triples

The actual fixed modulus support is reindexed to the literal processing
list `[p1,p2,p3]` and reverse history `[p3,p2,p1]`. Its coefficient is -1
precisely when the original first test and both current third cube tests
pass, and is zero otherwise. The full tuple partition then supplies the
unique selected joint owner or the original outside/inactive fallback.
-/

namespace ImbalancedChen.P1ActualCoarseTripleSupport

noncomputable section

open scoped Classical
open HistoricalThirdCoarse
open P1ActualCoarseFixedCoefficient P1ActualCoarseLowRankSupport
open HistoricalThirdCoarse.P1ActualTuple HistoricalThirdCoarse.P1ActualPartition

/-- The initial first cube is separate from the third level's own first
cube. The third level is the literal active/cell/fallback `rawLevel`. -/
def tripleTests (e chi : ℝ) (m : ℕ) (omega : ℝ) (N p1 p2 p3 : ℕ) : Prop :=
  firstStop e m (N : ℝ) [p1] ∧
    (p1 : ℝ) ^ 3 < (N : ℝ) ^ initial e ∧
    (p1 : ℝ) ^ 3 < rawLevel e chi m omega (N : ℝ) [p3, p2, p1] ∧
    (p1 : ℝ) * p2 * (p3 : ℝ) ^ 3 < rawLevel e chi m omega (N : ℝ) [p3, p2, p1]

private theorem triple_pairwise (p1 p2 p3 : ℕ) (h32 : p3 < p2) (h21 : p2 < p1) :
    [p1, p2, p3].Pairwise (· > ·) := by
  simp [List.pairwise_cons, h32, h21, h32.trans h21]

private theorem triple_prime (p1 p2 p3 : ℕ)
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime) :
    ∀ r ∈ [p1, p2, p3], r.Prime := by
  intro r hr
  simp only [List.mem_cons, List.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp1
  · exact hp2
  · exact hp3

theorem valid_triple_iff_tests
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N p1 p2 p3 : ℕ)
    (hp1 : p1.Prime) (hp3 : p3.Prime) (h32 : p3 < p2) (h21 : p2 < p1) :
    FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true [p1, p2, p3] ↔
      tripleTests e chi m omega N p1 p2 p3 := by
  have hsplit :
      FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true [p1, p2, p3] ↔
        FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true [p1, p2] ∧
          policy e chi m omega (N : ℝ) false [p3, p2, p1] = true := by
    simp [FirstExitValidSelection, and_assoc]
  rw [hsplit, valid_pair_iff_original_first_tests e chi m omega N p1 p2 hp1,
    policy_third_iff e chi m omega (N : ℝ) p1 p2 p3 hp3.pos h32 h21]
  simp only [tripleTests, and_assoc]

/-- Actual support membership recovers the ordered triple itself from
its product. The reverse direction constructs its actual valid selection. -/
theorem ordered_triple_mem_support_iff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p1 p2 p3 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime)
    (h32 : p3 < p2) (h21 : p2 < p1) :
    p1 * p2 * p3 ∈ roughSupport e chi m omega N cap w z ↔
      p1 ∈ roughPrimeUniverse N cap w z ∧ p2 ∈ roughPrimeUniverse N cap w z ∧
      p3 ∈ roughPrimeUniverse N cap w z ∧ tripleTests e chi m omega N p1 p2 p3 := by
  have ht := triple_pairwise p1 p2 p3 h32 h21
  have hprime := triple_prime p1 p2 p3 hp1 hp2 hp3
  rw [support_eq_original_retainedModuli, mem_firstExitRetainedModuli_iff_validSelection]
  constructor
  · rintro ⟨chosen, hsub, hvalid, hprod⟩
    have hcprime : ∀ r ∈ chosen, r.Prime :=
      fun _ hr => mem_roughPrimeUniverse_prime (hsub.subset hr)
    have hp : chosen.prod = [p1, p2, p3].prod := by simpa [mul_assoc] using hprod
    have hperm := (Nat.primeFactorsList_unique hp hcprime).trans
      (Nat.primeFactorsList_unique (rfl : [p1, p2, p3].prod = [p1, p2, p3].prod)
        hprime).symm
    have heq : chosen = [p1, p2, p3] := List.Perm.eq_of_pairwise
      (fun _ _ _ _ hab hba => Nat.le_antisymm hba hab)
      (((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub).imp fun h => h.le)
      (ht.imp fun h => h.le) hperm
    subst chosen
    exact ⟨hsub.subset (by simp), hsub.subset (by simp), hsub.subset (by simp),
      (valid_triple_iff_tests e chi m omega N p1 p2 p3 hp1 hp3 h32 h21).1 hvalid⟩
  · rintro ⟨hc1, hc2, hc3, htests⟩
    have hmem : [p1, p2, p3] ⊆ roughPrimeUniverse N cap w z := by
      intro r hr
      simp only [List.mem_cons, List.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact hc1
      · exact hc2
      · exact hc3
    have hsub := List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset ht.nodup hmem) ht (roughPrimeUniverse_pairwise_gt N cap w z)
    exact ⟨[p1, p2, p3], hsub,
      (valid_triple_iff_tests e chi m omega N p1 p2 p3 hp1 hp3 h32 h21).2 htests,
      by simp [mul_assoc]⟩

/-- Literal arithmetic coefficient: all original and current tests are
visible in `tripleTests`; failure gives zero rather than a changed policy. -/
theorem ordered_triple_coefficient_formula
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p1 p2 p3 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime)
    (h32 : p3 < p2) (h21 : p2 < p1) :
    roughCoefficient e chi m omega N cap w z (p1 * p2 * p3) =
      if p1 ∈ roughPrimeUniverse N cap w z ∧ p2 ∈ roughPrimeUniverse N cap w z ∧
        p3 ∈ roughPrimeUniverse N cap w z ∧ tripleTests e chi m omega N p1 p2 p3
      then -1 else 0 := by
  have hmu : ArithmeticFunction.moebius (p1 * p2 * p3) = (-1 : ℤ) := by
    have h := moebius_list_prod_eq_negOnePow_length [p1, p2, p3]
      (triple_pairwise p1 p2 p3 h32 h21).nodup (triple_prime p1 p2 p3 hp1 hp2 hp3)
    simpa [mul_assoc] using h
  have hs := ordered_triple_mem_support_iff
    e chi m omega N cap w z p1 p2 p3 hp1 hp2 hp3 h32 h21
  change ((if p1 * p2 * p3 ∈ roughSupport e chi m omega N cap w z then
    ArithmeticFunction.moebius (p1 * p2 * p3) else 0 : ℤ) : ℝ) = _
  by_cases hc : p1 ∈ roughPrimeUniverse N cap w z ∧ p2 ∈ roughPrimeUniverse N cap w z ∧
      p3 ∈ roughPrimeUniverse N cap w z ∧ tripleTests e chi m omega N p1 p2 p3
  · rw [if_pos (hs.2 hc), if_pos hc, hmu]
    norm_num
  · rw [if_neg (fun hd => hc (hs.1 hd)), if_neg hc]
    norm_num

theorem ordered_triple_coefficient_eq_neg_one_iff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p1 p2 p3 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime)
    (h32 : p3 < p2) (h21 : p2 < p1) :
    roughCoefficient e chi m omega N cap w z (p1 * p2 * p3) = -1 ↔
      p1 ∈ roughPrimeUniverse N cap w z ∧ p2 ∈ roughPrimeUniverse N cap w z ∧
      p3 ∈ roughPrimeUniverse N cap w z ∧ tripleTests e chi m omega N p1 p2 p3 := by
  rw [ordered_triple_coefficient_formula
    e chi m omega N cap w z p1 p2 p3 hp1 hp2 hp3 h32 h21]
  split_ifs with hc <;> simp [hc]

/-- The actual product support and the existing actual retained tuple
dictionary describe exactly the same ordered triple. -/
theorem tuple_product_mem_support_iff_retained
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (z : ℝ)
    (p : Fin 3 → ℕ) (hprime : ∀ i, (p i).Prime) (hsort : StrictAnti p) :
    p 0 * p 1 * p 2 ∈ roughSupport e chi m omega N cap 0 z ↔
      p ∈ retainedTuples e chi m omega N cap z := by
  rw [ordered_triple_mem_support_iff e chi m omega N cap 0 z
    (p 0) (p 1) (p 2) (hprime 0) (hprime 1) (hprime 2)
    (hsort (by decide : (1 : Fin 3) < 2)) (hsort (by decide : (0 : Fin 3) < 1)),
    mem_retainedTuples_iff]
  have hof : List.ofFn p = [p 0, p 1, p 2] := by simp [List.ofFn_succ]
  rw [hof, valid_triple_iff_tests e chi m omega N (p 0) (p 1) (p 2)
    (hprime 0) (hprime 2) (hsort (by decide : (1 : Fin 3) < 2))
    (hsort (by decide : (0 : Fin 3) < 1))]
  constructor
  · rintro ⟨hc0, hc1, hc2, ht⟩
    have hpair := triple_pairwise (p 0) (p 1) (p 2)
      (hsort (by decide : (1 : Fin 3) < 2)) (hsort (by decide : (0 : Fin 3) < 1))
    have hm : [p 0, p 1, p 2] ⊆ roughPrimeUniverse N cap 0 z := by
      intro q hq
      simp only [List.mem_cons, List.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hc0
      · exact hc1
      · exact hc2
    exact ⟨List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset hpair.nodup hm) hpair (roughPrimeUniverse_pairwise_gt N cap 0 z), ht⟩
  · rintro ⟨hsub, ht⟩
    exact ⟨hsub.subset (by simp), hsub.subset (by simp), hsub.subset (by simp), ht⟩

theorem tuple_product_coefficient_formula
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (z : ℝ)
    (p : Fin 3 → ℕ) (hprime : ∀ i, (p i).Prime) (hsort : StrictAnti p) :
    roughCoefficient e chi m omega N cap 0 z (p 0 * p 1 * p 2) =
      if p ∈ retainedTuples e chi m omega N cap z then -1 else 0 := by
  rw [ordered_triple_coefficient_formula e chi m omega N cap 0 z
    (p 0) (p 1) (p 2) (hprime 0) (hprime 1) (hprime 2)
    (hsort (by decide : (1 : Fin 3) < 2)) (hsort (by decide : (0 : Fin 3) < 1)),
    ← ordered_triple_mem_support_iff e chi m omega N cap 0 z
      (p 0) (p 1) (p 2) (hprime 0) (hprime 1) (hprime 2)
      (hsort (by decide : (1 : Fin 3) < 2)) (hsort (by decide : (0 : Fin 3) < 1)),
    tuple_product_mem_support_iff_retained e chi m omega N cap z p hprime hsort]

private theorem selected_joint_exists_iff_unique
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (t : Fin 3 → ℝ) :
    (∃ j ∈ cells e chi m,
      t ∈ logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j) ↔
    ∃! j : Cell m, j ∈ cells e chi m ∧
      t ∈ logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j := by
  constructor
  · rintro ⟨j, hj, ht⟩
    refine ⟨j, ⟨hj, ht⟩, ?_⟩
    intro k hk
    exact logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hk.2.1 ht.1
  · rintro ⟨j, ⟨hj, ht⟩, _⟩
    exact ⟨j, hj, ht⟩

/-- Direct reuse of the full actual cell partition: every retained tuple
has either a unique selected joint owner or the precise original fallback. -/
theorem full_mem_iff_joint_owner_or_fallback
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (p : Fin 3 → ℕ) :
    p ∈ full e chi m omega N cap ↔
      p ∈ primeBox N ∧
        ((∃! j : Cell m, j ∈ cells e chi m ∧ actualPrimeTupleLog N p ∈
          logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j) ∨
        actualPrimeTupleLog N p ∈ outsideRegion e chi m omega ∨
        actualPrimeTupleLog N p ∈ inactiveRegion e m omega) := by
  have hcell (j : Cell m) (hj : j ∈ cells e chi m) :
      selectedCell e chi m omega N cap j =
        (primeBox N).filter (fun q => actualPrimeTupleLog N q ∈
          logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j) := by
    exact activeRetainedTuples_cell_filter e chi m omega N cap hN hcap j hj
  have hselected : p ∈ selectedPart e chi m omega N cap ↔
      p ∈ primeBox N ∧ ∃ j ∈ cells e chi m, actualPrimeTupleLog N p ∈
        logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j := by
    simp only [selectedPart, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj, hp⟩
      rw [hcell j hj] at hp
      exact ⟨(Finset.mem_filter.mp hp).1, j, hj, (Finset.mem_filter.mp hp).2⟩
    · rintro ⟨hp, j, hj, ht⟩
      refine ⟨j, hj, ?_⟩
      rw [hcell j hj]
      exact Finset.mem_filter.mpr ⟨hp, ht⟩
  rw [full_partition]
  simp only [Finset.mem_union]
  rw [hselected, activeOutside_eq_log_filter e chi m omega N cap hN hcap,
    inactivePart_eq_log_filter e chi m omega N cap hN hcap]
  simp only [Finset.mem_filter]
  rw [selected_joint_exists_iff_unique]
  tauto

/-- The coefficient itself, on the original full triple range, is the
indicator of the actual unique-joint-owner/outside/inactive partition.
Its selected term keeps the inclusive active threshold; both fallbacks
keep the original firstStop and initial exponent via their real regions. -/
theorem coefficient_eq_joint_owner_or_fallback_indicator
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 3 → ℕ) (hprime : ∀ i, (p i).Prime) (hsort : StrictAnti p) :
    roughCoefficient e chi m omega N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))
        (p 0 * p 1 * p 2) =
      if p ∈ primeBox N ∧
        ((∃! j : Cell m, j ∈ cells e chi m ∧ actualPrimeTupleLog N p ∈
          logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j) ∨
        actualPrimeTupleLog N p ∈ outsideRegion e chi m omega ∨
        actualPrimeTupleLog N p ∈ inactiveRegion e m omega) then -1 else 0 := by
  rw [tuple_product_coefficient_formula e chi m omega N cap
    ((N : ℝ) ^ (19 / 96 : ℝ)) p hprime hsort]
  change (if p ∈ full e chi m omega N cap then (-1 : ℝ) else 0) = _
  rw [full_mem_iff_joint_owner_or_fallback e chi m omega N cap hN hcap p]

end

end ImbalancedChen.P1ActualCoarseTripleSupport
