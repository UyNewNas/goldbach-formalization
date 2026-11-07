import ImbalancedChen.P1ActualCoarseRetainedModulusLevel
import ImbalancedChen.P1OriginalCoarseFifthContinuationCells
import ImbalancedChen.P1OriginalHistoricalPhysicalCoefficient
import ImbalancedChen.FirstExitHistoricalLevels
import ImbalancedChen.P1HistoricalCapCeilingCheck
import Mathlib.Data.Finset.Max

/-!
Full retained-leaf validity for the original historical fifth-capped policy.
The parent is the literal original initialPolicy and rawLevel, including
firstStop, rough activation and Theta fallback. Through rank four the level
is the original frozen third level; from rank five it is the actual Q5
frozen at its rank-five ancestor. A rank-five odd test resets the COMPLETE
predicate at Q5; even-rank continuation inherits full validity via sorted
prime insertion. Q3 <= Q5 is not needed for this validity statement.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical
open HistoricalThirdCoarse P1ActualCoarseRetainedModulusLevel
open P1ActualCoarseLevelCeiling VariableEnvelope

namespace P1OriginalHistoricalRetainedModulusLevel

def originalFifthPolicy (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  fifthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q5

def currentLevel (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  if pre.length ≤ 4 then frozenLevel e chi m omega N pre
  else Q5 (rosserAncestor 5 pre)

theorem currentLevel_through_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    currentLevel e chi m omega N Q5 pre = frozenLevel e chi m omega N pre := by
  exact if_pos hlen

theorem currentLevel_from_five (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) (pre : List ℕ) (hlen : 5 ≤ pre.length) :
    currentLevel e chi m omega N Q5 pre = Q5 (rosserAncestor 5 pre) := by
  exact if_neg (by omega)

private theorem evenListLength_eq_decide_even (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- Reuse the actual coarse retained-leaf theorem on its literal one-step tree. -/
theorem original_coarse_step_valid (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (pre : List ℕ) (positive : Bool) (q : ℕ)
    (hpre : ordinaryRosserPrefixAdmissible false (frozenLevel e chi m omega N pre) pre)
    (hsign : positive = evenListLength pre) (hq : q.Prime)
    (hsort : (q :: pre).Pairwise (· < ·))
    (hpass : policy e chi m omega N (!positive) (q :: pre) = true) :
    ordinaryRosserPrefixAdmissible false
      (frozenLevel e chi m omega N (q :: pre)) (q :: pre) := by
  have hprime : ∀ p ∈ [q], p.Prime := by
    intro p hp
    have hpq : p = q := by simpa using hp
    simpa only [hpq] using hq
  have hleaf : ({selected := q :: pre, positive := !positive, mass := 1} : FirstExitLeaf ℕ) ∈
      firstExitRetainedLeaves (policy e chi m omega N) (fun _ => 1) pre positive 1 [q] := by
    simp [firstExitRetainedLeaves, hpass]
  exact (mem_retained_leaf_valid_from_entry e chi m omega N (fun _ => 1) pre [q]
    positive 1 hpre hsign hprime (by simpa using hsort)
    {selected := q :: pre, positive := !positive, mass := 1} hleaf).1

/-- All reset and inherited cases occur in the actual final-policy recursion. -/
theorem mem_original_fifth_leaf_valid_from_entry
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (Q5 : List ℕ → ℝ) (weight : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hpre : ordinaryRosserPrefixAdmissible false (currentLevel e chi m omega N Q5 pre) pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (originalFifthPolicy e chi m omega N Q5)
      weight pre positive mass carrier) :
    ordinaryRosserPrefixAdmissible false
        (currentLevel e chi m omega N Q5 leaf.selected) leaf.selected ∧
      leaf.positive = evenListLength leaf.selected := by
  induction carrier generalizing pre positive mass with
  | nil =>
      simp only [firstExitRetainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      exact ⟨hpre, hsign⟩
  | cons q qs ih =>
      have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
      have hskipSort : (qs.reverse ++ pre).Pairwise (· < ·) :=
        hsort'.sublist ((List.Sublist.refl qs.reverse).append ((List.Sublist.refl pre).cons q))
      have hprime' : ∀ p ∈ qs, p.Prime :=
        fun p hp => hprime p (List.mem_cons_of_mem q hp)
      rw [firstExitRetainedLeaves, List.mem_append] at hleaf
      rcases hleaf with hskip | hselect
      · exact ih pre positive mass hpre hsign hprime' hskipSort hskip
      · by_cases ht : originalFifthPolicy e chi m omega N Q5 (!positive) (q :: pre) = true
        · rw [if_pos ht] at hselect
          have hnext : ordinaryRosserPrefixAdmissible false
              (currentLevel e chi m omega N Q5 (q :: pre)) (q :: pre) := by
            by_cases hshort : (q :: pre).length ≤ 4
            · have hpreShort : pre.length ≤ 4 := by simp only [List.length_cons] at hshort; omega
              have hprior : ordinaryRosserPrefixAdmissible false
                  (frozenLevel e chi m omega N pre) pre := by
                simpa only [currentLevel, if_pos hpreShort] using hpre
              have hpass : policy e chi m omega N (!positive) (q :: pre) = true := by
                simpa only [originalFifthPolicy, fifthCappedUpperPolicy,
                  firstExitDepthSplicePolicy, if_pos hshort, policy] using ht
              rw [currentLevel_through_four e chi m omega N Q5 (q :: pre) hshort]
              exact original_coarse_step_valid e chi m omega N pre positive q hprior hsign
                (hprime q (by simp)) (List.pairwise_append.mp hsort').2.1 hpass
            · have hnewrank : 5 ≤ (q :: pre).length := by omega
              have ht' : ordinaryParityRosserPolicy false
                  (Q5 (rosserAncestor 5 (q :: pre))) (!positive) (q :: pre) = true := by
                simpa only [originalFifthPolicy, fifthCappedUpperPolicy,
                  firstExitDepthSplicePolicy, if_neg hshort,
                  frozenParityRosserPolicy, ancestorFrozenPolicy] using ht
              rw [currentLevel_from_five e chi m omega N Q5 (q :: pre) hnewrank]
              by_cases hdeep : 5 ≤ pre.length
              · have hprior : ordinaryRosserPrefixAdmissible false
                    (Q5 (rosserAncestor 5 pre)) pre := by
                  simpa only [currentLevel, if_neg (by omega : ¬pre.length ≤ 4)] using hpre
                rw [rosserAncestor_cons 5 q pre hdeep] at ht' ⊢
                rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
                  (Q5 (rosserAncestor 5 pre)) pre positive q hprior hsign
                  (hprime q (by simp)) (by simp)
                  (List.pairwise_append.mp hsort').2.1] at ht'
                exact of_decide_eq_true ht'
              · have hlen4 : pre.length = 4 := by simp only [List.length_cons] at hshort; omega
                have hs : positive = true := by
                  rw [hsign, evenListLength_eq_decide_even, hlen4]
                  decide
                simpa only [hs, Bool.not_true, ordinaryParityRosserPolicy,
                  Bool.false_eq_true, if_false, oddFirstExitPolicy, Bool.false_or,
                  decide_eq_true_eq] using ht'
          have hsign' : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
          exact ih (q :: pre) (!positive) (mass * weight q) hnext hsign'
            hprime' hsort' hselect
        · simp only [if_neg ht, List.not_mem_nil] at hselect

/-- Arbitrary actual Q5 data need no assumed validity or monotone level update. -/
theorem original_fifth_retained_leaf_valid
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (Q5 : List ℕ → ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < N)
    (weight : ℕ → ℝ) (carrier : List ℕ)
    (hprime : ∀ p ∈ carrier, p.Prime) (hsort : carrier.Pairwise (· > ·))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (originalFifthPolicy e chi m omega N Q5)
      weight [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible false
      (currentLevel e chi m omega N Q5 leaf.selected) leaf.selected := by
  have hroot : ordinaryRosserPrefixAdmissible false
      (currentLevel e chi m omega N Q5 []) [] := by
    rw [currentLevel_through_four e chi m omega N Q5 [] (by simp),
      frozenLevel_short e chi m omega N [] (by simp)]
    exact ordinaryRosserPrefixAdmissible_nil false (initial_level_gt_one e N heupper hN)
  exact (mem_original_fifth_leaf_valid_from_entry e chi m omega N Q5 weight [] carrier
    true 1 hroot rfl hprime
    (by simpa only [List.append_nil, List.pairwise_reverse] using hsort) leaf hleaf).1

theorem actual_original_fifth_retained_leaf_valid
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) (Q5 : List ℕ → ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (originalFifthPolicy e chi m omega (N : ℝ) Q5)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      (currentLevel e chi m omega (N : ℝ) Q5 leaf.selected) leaf.selected := by
  exact original_fifth_retained_leaf_valid e chi m omega (N : ℝ) Q5 heupper hN weight _
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (roughPrimeUniverse_pairwise_gt N cap w z) leaf hleaf

theorem actual_original_fifth_retained_leaf_prod_lt_current
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) (Q5 : List ℕ → ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (originalFifthPolicy e chi m omega (N : ℝ) Q5)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    (leaf.selected.prod : ℝ) < currentLevel e chi m omega (N : ℝ) Q5 leaf.selected := by
  exact (actual_original_fifth_retained_leaf_valid e chi m omega N cap w z Q5
    heupper hN weight leaf hleaf).1

section ActualOriginalLookup

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (J4 : Finset (Fin 4 → Fin (m + 1))) (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
  (J5 : Finset (Fin 5 → Fin (m + 1))) (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)

local notation "Q5" => P1OriginalCoarseFifthContinuation.level5 e chi m omega J4 cap4 J5 cap5
local notation "P" => P1OriginalHistoricalPhysicalCoefficient.finalPolicy e chi m omega J4 cap4 J5 cap5
local notation "S" => P1OriginalHistoricalPhysicalCoefficient.roughSupport e chi m omega J4 cap4 J5 cap5
local notation "C" => P1OriginalHistoricalPhysicalCoefficient.roughCoefficient e chi m omega J4 cap4 J5 cap5

/-- Finite upper checks refer only to the ORIGINAL selected continuation cells.
They are separate from h34/h45 lower-comparison checks. -/
def originalCeilingCheck (theta : ℚ) : Bool :=
  decide (0 ≤ e) && (decide ((299 / 500 : ℚ) - 2 * e ≤ theta) &&
    (@decide _ (Finset.decidableDforallFinset
      (s := P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4)
      (p := fun j _ => cap4 j ≤ theta)) &&
    @decide _ (Finset.decidableDforallFinset
      (s := P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
      (p := fun j _ => cap5 j ≤ theta))))

theorem originalCeilingCheck_sound (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true) :
    0 ≤ e ∧ (299 / 500 : ℚ) - 2 * e ≤ theta ∧
      (∀ j ∈ P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4, cap4 j ≤ theta) ∧
      (∀ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5, cap5 j ≤ theta) := by
  simpa only [originalCeilingCheck, Bool.and_eq_true, decide_eq_true_eq] using hc

/-- A safe actual rational ceiling exists for every finite table. Its numerical
smallness is NOT assumed: it includes every actual selected fourth/fifth cap. -/
def tableValues : Finset ℚ :=
  insert ((299 / 500 : ℚ) - 2 * e)
    (((P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4).image cap4) ∪
      ((P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5).image cap5))

theorem tableValues_nonempty : (tableValues e chi m omega J4 cap4 J5 cap5).Nonempty := by
  exact ⟨(299 / 500 : ℚ) - 2 * e, Finset.mem_insert_self _ _⟩

def tableCeiling : ℚ :=
  (tableValues e chi m omega J4 cap4 J5 cap5).max'
    (tableValues_nonempty e chi m omega J4 cap4 J5 cap5)

theorem mem_tableValues_le_ceiling (a : ℚ)
    (ha : a ∈ tableValues e chi m omega J4 cap4 J5 cap5) :
    a ≤ tableCeiling e chi m omega J4 cap4 J5 cap5 := by
  exact Finset.le_max' _ a ha

theorem tableCeilingCheck_true (he : 0 ≤ e) :
    originalCeilingCheck e chi m omega J4 cap4 J5 cap5
      (tableCeiling e chi m omega J4 cap4 J5 cap5) = true := by
  simp only [originalCeilingCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨he, ?_, ?_, ?_⟩
  · exact mem_tableValues_le_ceiling e chi m omega J4 cap4 J5 cap5 _
      (Finset.mem_insert_self _ _)
  · intro j hj
    apply mem_tableValues_le_ceiling e chi m omega J4 cap4 J5 cap5
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  · intro j hj
    apply mem_tableValues_le_ceiling e chi m omega J4 cap4 J5 cap5
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))

theorem actual_effectiveExponent3Q_le_ceiling (theta : ℚ)
    (he : 0 ≤ e) (hTheta : (299 / 500 : ℚ) - 2 * e ≤ theta)
    (N : ℝ) (pre : List ℕ) :
    P1OriginalCoarseContinuation.effectiveExponent3Q e chi m omega N pre ≤ theta := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hthird : (P1OriginalCoarseContinuation.effectiveExponent3Q e chi m omega N pre : ℝ) ≤
      initial (e : ℝ) := by
    rw [P1OriginalCoarseContinuation.cast_effectiveExponent3Q]
    unfold P1CoarseFirstCubeFallbackMargin.effectiveExponent
    split_ifs
    · exact exponent_le_initial (e : ℝ) chi heR m _
    · exact le_rfl
  have hThetaR : (((299 / 500 : ℚ) - 2 * e : ℚ) : ℝ) ≤ (theta : ℝ) := by
    exact_mod_cast hTheta
  have hinit : initial (e : ℝ) ≤ (theta : ℝ) := by
    simpa [initial, extendedDistributionCap] using hThetaR
  exact_mod_cast hthird.trans hinit

theorem actual_effectiveExponent4Q_le_ceiling (theta : ℚ)
    (he : 0 ≤ e) (hTheta : (299 / 500 : ℚ) - 2 * e ≤ theta)
    (h4 : ∀ j ∈ P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4, cap4 j ≤ theta)
    (N : ℝ) (pre : List ℕ) :
    P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 N pre ≤ theta := by
  unfold P1OriginalCoarseContinuation.effectiveExponent4Q
  split_ifs
  · exact p1HistoricalPrefixLookup_le_of_bounds 0 (19 / 96) (by norm_num) m
      (P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4) cap4 _ theta
      (actual_effectiveExponent3Q_le_ceiling e chi m omega theta he hTheta N _) h4 _
  · exact actual_effectiveExponent3Q_le_ceiling e chi m omega theta he hTheta N _

theorem actual_effectiveExponent5Q_le_ceiling (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true)
    (N : ℝ) (pre : List ℕ) :
    P1OriginalCoarseFifthContinuation.effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre ≤ theta := by
  obtain ⟨he, hTheta, h4, h5⟩ := originalCeilingCheck_sound e chi m omega J4 cap4 J5 cap5 theta hc
  unfold P1OriginalCoarseFifthContinuation.effectiveExponent5Q
  split_ifs
  · exact p1HistoricalPrefixLookup_le_of_bounds 0 (19 / 96) (by norm_num) m
      (P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5) cap5 _ theta
      (actual_effectiveExponent4Q_le_ceiling e chi m omega J4 cap4 theta he hTheta N _) h5 _
  · exact actual_effectiveExponent4Q_le_ceiling e chi m omega J4 cap4 theta he hTheta N _

theorem actual_level5_le_power_ceiling (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true)
    (N : ℝ) (hN : 1 ≤ N) (pre : List ℕ) : Q5 N pre ≤ N ^ (theta : ℝ) := by
  change N ^ (P1OriginalCoarseFifthContinuation.effectiveExponent5Q
    e chi m omega J4 cap4 J5 cap5 N pre : ℝ) ≤ N ^ (theta : ℝ)
  apply Real.rpow_le_rpow_of_exponent_le hN
  exact_mod_cast actual_effectiveExponent5Q_le_ceiling e chi m omega J4 cap4 J5 cap5 theta hc N pre

theorem actual_currentLevel_le_power_ceiling (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true)
    (N : ℝ) (hN : 1 ≤ N) (pre : List ℕ) :
    currentLevel (e : ℝ) chi m omega N (Q5 N) pre ≤ N ^ (theta : ℝ) := by
  obtain ⟨he, hTheta, _h4, _h5⟩ := originalCeilingCheck_sound e chi m omega J4 cap4 J5 cap5 theta hc
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  unfold currentLevel
  split_ifs
  · apply (frozenLevel_le_initial (e : ℝ) chi heR m omega N hN pre).trans
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hThetaR : (((299 / 500 : ℚ) - 2 * e : ℚ) : ℝ) ≤ (theta : ℝ) := by
      exact_mod_cast hTheta
    simpa [initial, extendedDistributionCap] using hThetaR
  · exact actual_level5_le_power_ceiling e chi m omega J4 cap4 J5 cap5 theta hc N hN _

/-- The new original lookup instantiates the already proved arbitrary-Q5 validity. -/
theorem actual_final_leaf_valid (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (P (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      (currentLevel (e : ℝ) chi m omega (N : ℝ) (Q5 (N : ℝ)) leaf.selected) leaf.selected := by
  exact actual_original_fifth_retained_leaf_valid (e : ℝ) chi m omega N cap w z
    (Q5 (N : ℝ)) heupper hN weight leaf hleaf

theorem actual_final_leaf_prod_lt_ceiling (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true)
    (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (P (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z)) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ (theta : ℝ) := by
  exact (actual_final_leaf_valid e chi m omega J4 cap4 J5 cap5 N cap w z
    heupper hN weight leaf hleaf).1.trans_le
      (actual_currentLevel_le_power_ceiling e chi m omega J4 cap4 J5 cap5 theta hc
        (N : ℝ) hN.le leaf.selected)

theorem actual_final_rough_nonzero_mem_support (N cap : ℕ) (w z : ℝ) (d : ℕ)
    (hd : C N cap w z d ≠ 0) : d ∈ S N cap w z := by
  by_contra hnot
  apply hd
  change d ∉ firstExitRetainedModuli (P (N : ℝ)) (roughPrimeUniverse N cap w z) at hnot
  change ((if d ∈ firstExitRetainedModuli (P (N : ℝ)) (roughPrimeUniverse N cap w z)
    then ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = 0
  rw [if_neg hnot]
  norm_num

/-- One actual witness carries d < its real current level <= the finite ceiling. -/
theorem actual_final_rough_nonzero_valid_witness (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true)
    (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : C N cap w z d ≠ 0) :
    ∃ leaf : FirstExitLeaf ℕ,
      leaf ∈ firstExitRetainedLeaves (P (N : ℝ)) (fun _ => 1) [] true 1
        (roughPrimeUniverse N cap w z) ∧
      leaf.selected.prod = d ∧
      ordinaryRosserPrefixAdmissible false
        (currentLevel (e : ℝ) chi m omega (N : ℝ) (Q5 (N : ℝ)) leaf.selected) leaf.selected ∧
      (d : ℝ) < currentLevel (e : ℝ) chi m omega (N : ℝ) (Q5 (N : ℝ)) leaf.selected ∧
      currentLevel (e : ℝ) chi m omega (N : ℝ) (Q5 (N : ℝ)) leaf.selected ≤
        (N : ℝ) ^ (theta : ℝ) := by
  have hmem := actual_final_rough_nonzero_mem_support e chi m omega J4 cap4 J5 cap5 N cap w z d hd
  change d ∈ firstExitRetainedModuli (P (N : ℝ)) (roughPrimeUniverse N cap w z) at hmem
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_firstExitRetainedModuli (P (N : ℝ)) (roughPrimeUniverse N cap w z) d).mp hmem
  have hvalid := actual_final_leaf_valid e chi m omega J4 cap4 J5 cap5 N cap w z
    heupper hN (fun _ => 1) leaf hleaf
  refine ⟨leaf, hleaf, hprod, hvalid, ?_,
    actual_currentLevel_le_power_ceiling e chi m omega J4 cap4 J5 cap5 theta hc
      (N : ℝ) hN.le leaf.selected⟩
  simpa only [hprod] using hvalid.1

theorem actual_final_rough_nonzero_modulus_lt_ceiling (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true)
    (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : C N cap w z d ≠ 0) : (d : ℝ) < (N : ℝ) ^ (theta : ℝ) := by
  obtain ⟨_leaf, _hleaf, _hprod, _hvalid, hdcurrent, hcurrent⟩ :=
    actual_final_rough_nonzero_valid_witness e chi m omega J4 cap4 J5 cap5 theta hc
      N cap w z heupper hN d hd
  exact hdcurrent.trans_le hcurrent

theorem actual_final_rough_zero_of_ceiling_le (theta : ℚ)
    (hc : originalCeilingCheck e chi m omega J4 cap4 J5 cap5 theta = true)
    (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : (N : ℝ) ^ (theta : ℝ) ≤ (d : ℝ)) : C N cap w z d = 0 := by
  by_contra hnonzero
  exact (not_lt_of_ge hd) (actual_final_rough_nonzero_modulus_lt_ceiling
    e chi m omega J4 cap4 J5 cap5 theta hc N cap w z heupper hN d hnonzero)

/-- A complete finite-table support bound, with no unproved upper-check premise. -/
theorem actual_final_rough_nonzero_modulus_lt_tableCeiling (he : 0 ≤ e)
    (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : C N cap w z d ≠ 0) :
    (d : ℝ) < (N : ℝ) ^ (tableCeiling e chi m omega J4 cap4 J5 cap5 : ℝ) := by
  exact actual_final_rough_nonzero_modulus_lt_ceiling e chi m omega J4 cap4 J5 cap5
    (tableCeiling e chi m omega J4 cap4 J5 cap5)
    (tableCeilingCheck_true e chi m omega J4 cap4 J5 cap5 he)
    N cap w z heupper hN d hd

end ActualOriginalLookup

end P1OriginalHistoricalRetainedModulusLevel
end
end ImbalancedChen
