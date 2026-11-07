import ImbalancedChen.P1OriginalSupportedRemainderJointCover
import ImbalancedChen.P5OriginalCommonRefinedAncestry
import ImbalancedChen.Part3ActualRetainedAncestorTests
import ImbalancedChen.P4AActualEighthInheritedHistoryGuard

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The fifth lower guard is obtained from the actual passed fifth decision.
The old original fifth policy and the independently constructed COMMON
final policy are separate applications. The common policy's fifth exponent
is re-seeded at its own common third/fourth ancestors; it is never identified
with the old exponent5. No H5 guard, ceiling, replacement-policy identity,
sixth cell licence or distribution conclusion is a premise.
-/

namespace ImbalancedChen.P1ActualOriginalAndCommonFifthGuard

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFifthContinuation
open Part3.ActualRetainedAncestorTests

private theorem sign_parity (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- Reuse the actual causal ancestor-test supplier; do not assume the
fifth prefix was admitted by an unrelated historical policy. -/
private theorem actual_fifth_admissible_of_test
    (R : Bool → List ℕ → Bool) (Q5 : List ℕ → ℝ)
    (htest : ∀ pre : List ℕ, pre.length = 5 →
      R false pre = decide (ordinaryRosserPrefixAdmissible false (Q5 pre) pre))
    (weight : ℕ → ℝ) (carrier : List ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves R weight [] true 1 carrier)
    (hlen : 5 ≤ leaf.selected.length) :
    ordinaryRosserPrefixAdmissible false
      (Q5 (rosserAncestor 5 leaf.selected)) (rosserAncestor 5 leaf.selected) := by
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by
    rw [rosserAncestor_length, Nat.min_eq_left hlen]
  have hpass := retained_leaf_ancestor_tests R weight carrier leaf hleaf 5 (by decide) hlen
  have hsign : evenListLength (rosserAncestor 5 leaf.selected) = false := by
    rw [sign_parity, h5]
    decide
  rw [hsign, htest _ h5] at hpass
  exact of_decide_eq_true hpass

theorem original_retained_fifth_admissible
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (weight : ℕ → ℝ) (carrier : List ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega N rows4 licensedOriginal J5 rows5)
      weight [] true 1 carrier) (hlen : 5 ≤ leaf.selected.length) :
    ordinaryRosserPrefixAdmissible false
      (level5 e chi m omega N rows4 licensedOriginal J5 rows5
        (rosserAncestor 5 leaf.selected)) (rosserAncestor 5 leaf.selected) := by
  apply actual_fifth_admissible_of_test _
    (level5 e chi m omega N rows4 licensedOriginal J5 rows5) _ weight carrier leaf hleaf hlen
  intro pre h5
  simp [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy,
    rosserAncestor_self_of_length 5 pre h5, ordinaryParityRosserPolicy,
    oddFirstExitPolicy, h5]

/-- Every actual final leaf of the independent common constructor retains
the full fifth test at its OWN re-seeded fifth level. No old-parent equality
or numerical bound for the common constructor is needed. -/
theorem common_final_retained_fifth_admissible
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ)
    (weight : ℕ → ℝ) (carrier : List ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P5OriginalCommonRefinedConstructor.policy8 d N) weight [] true 1 carrier)
    (hlen : 5 ≤ leaf.selected.length) :
    ordinaryRosserPrefixAdmissible false
      (P5OriginalCommonRefinedConstructor.level5 d N (rosserAncestor 5 leaf.selected))
      (rosserAncestor 5 leaf.selected) := by
  apply actual_fifth_admissible_of_test _
    (P5OriginalCommonRefinedConstructor.level5 d N) _ weight carrier leaf hleaf hlen
  intro pre h5
  rw [P5OriginalCommonRefinedAncestry.policy8_through_six_eq_fifth d N false pre (by omega)]
  simp [P5OriginalCommonRefinedConstructor.policy5, firstExitDepthSplicePolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy,
    rosserAncestor_self_of_length 5 pre h5, ordinaryParityRosserPolicy,
    oddFirstExitPolicy, h5]

/-- Arithmetic-to-log transport of the already derived fifth test. All
prime, order and positivity facts come from the SAME actual source carrier.
The six-vector is the real sixth ancestor, including when the leaf is deeper. -/
private theorem actual_fifth_H5_of_admissible
    (R : Bool → List ℕ → Bool) (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves R weight [] true 1
      (roughPrimeUniverse N cap w z)) (hlen : 6 ≤ leaf.selected.length)
    (lambda : ℝ)
    (hadm : ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ lambda)
      (rosserAncestor 5 leaf.selected)) :
    Certificates.P2OriginalSixthElevenLogSemantics.H5
        (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected)) < lambda := by
  let a := rosserAncestor 5 leaf.selected
  let b := rosserAncestor 6 leaf.selected
  have ha : a.length = 5 := by simp only [a, rosserAncestor_length]; omega
  have hb : b.length = 6 := by simp only [b, rosserAncestor_length]; omega
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using
      firstExitRetainedLeaves_selected_reverse_sublist R weight []
        (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hsort : leaf.selected.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hapos : ∀ p ∈ a, 0 < p := by
    intro p hp
    have hp' : p ∈ leaf.selected :=
      (List.drop_sublist (leaf.selected.length - 5) leaf.selected).subset hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp'))).pos
  have hcube : (a.prod : ℝ) * (a.headD 0 : ℝ) ^ 2 < (N : ℝ) ^ lambda := by
    have hasort : a.Pairwise (· < ·) := hsort.drop
    cases heq : a with
    | nil => simp [heq] at ha
    | cons p pre =>
        exact P4AActualEighthInheritedHistoryGuard.odd_history_own_cube _ p pre
          (by simpa only [heq] using hasort)
          (by rw [← heq, ha]; decide) (by simpa only [heq] using hadm)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN
  have hp2 : (N : ℝ) ^ (2 * primeHistoryLogCoordinates (N : ℝ) 5 a 4) =
      (a.headD 0 : ℝ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hN0.le,
      rpow_primeHistoryLogCoordinates (N : ℝ) hN ha hapos]
    rw [primeHistoryTuple_last (k := 4) ha]
    norm_num
  have hpow : (N : ℝ) ^ ((∑ i : Fin 5, primeHistoryLogCoordinates (N : ℝ) 5 a i) +
      2 * primeHistoryLogCoordinates (N : ℝ) 5 a 4) =
      (a.prod : ℝ) * (a.headD 0 : ℝ) ^ 2 := by
    rw [Real.rpow_add hN0, rpow_sum_primeHistoryLogCoordinates (N : ℝ) hN ha hapos, hp2]
  have hineq : (∑ i : Fin 5, primeHistoryLogCoordinates (N : ℝ) 5 a i) +
      2 * primeHistoryLogCoordinates (N : ℝ) 5 a 4 < lambda := by
    apply (Real.rpow_lt_rpow_left_iff hN).mp
    rw [hpow]
    exact hcube
  have hcoord (i : Fin 5) : primeHistoryLogCoordinates (N : ℝ) 5 a i =
      primeHistoryLogCoordinates (N : ℝ) 6 b (i.castLE (by decide)) := by
    simpa only [a, b, rosserAncestor_nested 5 6 (by decide)] using
      primeHistoryLogCoordinates_ancestor (N : ℝ) hb (by decide : 5 ≤ 6) i
  have hsum : (∑ i : Fin 5, primeHistoryLogCoordinates (N : ℝ) 5 a i) +
      2 * primeHistoryLogCoordinates (N : ℝ) 5 a 4 =
      Certificates.P2OriginalSixthElevenLogSemantics.H5
        (primeHistoryLogCoordinates (N : ℝ) 6 b) := by
    simp only [Fin.sum_univ_succ, hcoord, Certificates.P2OriginalSixthElevenLogSemantics.H5]
    ring
  rwa [hsum] at hineq

theorem original_actual_retained_H5_lower_guard
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (weight : ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega (N : ℝ) rows4 licensedOriginal J5 rows5)
      weight [] true 1 (roughPrimeUniverse N cap w z)) (hlen : 6 ≤ leaf.selected.length) :
    Certificates.P2OriginalSixthElevenLogSemantics.H5
        (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected)) <
      exponent5 e chi m omega (N : ℝ) rows4 licensedOriginal J5 rows5
        (rosserAncestor 5 leaf.selected) := by
  apply actual_fifth_H5_of_admissible _ N cap hN w z weight leaf hleaf hlen
  exact original_retained_fifth_admissible e chi m omega (N : ℝ) rows4 licensedOriginal
    J5 rows5 weight _ leaf hleaf (by omega)

/-- This is the missing LOWER guard for the actual common final leaf.
It is separate from the remaining upper guard actualParent5<=oldCap. -/
theorem common_final_actual_retained_H5_lower_guard
    (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (weight : ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z)) (hlen : 6 ≤ leaf.selected.length) :
    Certificates.P2OriginalSixthElevenLogSemantics.H5
        (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected)) <
      P5OriginalCommonRefinedConstructor.actualParent5 d (N : ℝ) (rosserAncestor 6 leaf.selected) := by
  rw [P5OriginalCommonRefinedAncestry.actualParent5_ancestor_six]
  apply actual_fifth_H5_of_admissible _ N cap hN w z weight leaf hleaf hlen
  exact common_final_retained_fifth_admissible d (N : ℝ) weight _ leaf hleaf (by omega)

/-- The proved guard belongs to the literal common final SAME-rho source,
including its actual small-prime beta and full marked terminal test. Short
leaves remain explicitly present. Taking G=count-exactCoprimeMean uses the
same integer coefficient in both terms, without a distribution hypothesis. -/
theorem common_final_same_rho_guarded_source
    (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N cap mark : ℕ) (hN : 1 < (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ P5OriginalCommonRefinedConstructor.moduli d N cap w z,
      P5OriginalCommonRefinedConstructor.rho d N cap w z L q * G (mark * q)) =
    ((firstExitRetainedLeaves
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) (fun _ => 1)
      [] true 1 (roughPrimeUniverse N cap w z)).map (fun leaf =>
        if 6 ≤ leaf.selected.length then
          if Certificates.P2OriginalSixthElevenLogSemantics.H5
              (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected)) <
              P5OriginalCommonRefinedConstructor.actualParent5 d (N : ℝ)
                (rosserAncestor 6 leaf.selected) then
            leaf.value * P1Pair12RetainedSignedSource.attachedLeafTest N cap mark w L G
              leaf.positive leaf.selected
          else 0
        else leaf.value * P1Pair12RetainedSignedSource.attachedLeafTest N cap mark w L G
          leaf.positive leaf.selected)).sum := by
  change (∑ q ∈ actualSmallRoughModuli
      ((P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) false) N cap w z,
    actualSmallRoughRho ((P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) false)
      N cap w z L q * G (mark * q)) = _
  rw [P1Pair12RetainedSignedSource.physical_test_eq_signedTest _
    (P5OriginalCommonRefinedConstructor.policy8_even d (N : ℝ)),
    P1Pair12RetainedSignedSource.signedTest_eq_leaves]
  congr 1
  apply List.map_congr_left
  intro leaf hleaf
  by_cases hlen : 6 ≤ leaf.selected.length
  · have hg := common_final_actual_retained_H5_lower_guard d N cap hN w z
      (fun _ => 1) leaf hleaf hlen
    simp only [if_pos hlen, if_pos hg]
  · simp only [if_neg hlen]

end
end ImbalancedChen.P1ActualOriginalAndCommonFifthGuard
