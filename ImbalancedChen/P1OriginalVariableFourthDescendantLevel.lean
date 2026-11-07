import ImbalancedChen.P1OriginalVariableFourthContinuation
import ImbalancedChen.P1OriginalHistoricalRetainedModulusLevel
import ImbalancedChen.P1ActualCoarseLevelCeiling

/-!
The literal original firstStop/rough-activated Q3 policy with the pointwise
variable Q4 continuation. The fifth-stage spelling below is an exact policy
identity, not an ordinary upper-third substitute. It lets the existing
retained-leaf validity argument apply at every depth after the fourth frontier.
Only the canonical continuous producer row profile is used for the uniform
cap ceiling. Row licensing remains the caller's separate geometric input.
Source-only candidate; no compiler was run.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical
open HistoricalThirdCoarse VariableEnvelope P1ActualCoarseLevelCeiling
open P1OriginalVariableFourthContinuation

namespace P1OriginalVariableFourthDescendantLevel

/-- The actual Q4 level is frozen at the original fourth ancestor. -/
def fourthDescendantLevel {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (pre : List ℕ) : ℝ :=
  if pre.length ≤ 4 then frozenLevel e chi m omega N pre
  else frozenLevel4 e chi m omega N rows eligible profile pre

/-- The old Q3 exponent is the exact seed of the fourth ancestor's max. -/
theorem fourth_ancestor_exponent_order {ι : Type*} (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (pre : List ℕ)
    (_hlen : 4 ≤ pre.length) :
    seedExponent e chi m omega N pre ≤
      exponent4 e chi m omega N rows eligible profile (rosserAncestor 4 pre) := by
  rw [← seedExponent_ancestor_four e chi m omega N pre]
  exact seedExponent_le_exponent4 e chi m omega N rows eligible profile _

/-- LevelCheck at every fourth ancestor and every later descendant. -/
theorem frozenThird_le_frozenFourth {ι : Type*} (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (hN : 1 ≤ N) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (pre : List ℕ)
    (_hlen : 4 ≤ pre.length) :
    frozenLevel e chi m omega N pre ≤
      frozenLevel4 e chi m omega N rows eligible profile pre := by
  have h := frozenThird_le_level4 e chi m omega N hN rows eligible profile
    (rosserAncestor 4 pre)
  simpa only [frozenLevel4, frozenLevel,
    rosserAncestor_nested 3 4 (by omega : 3 ≤ 4)] using h

/-- The two policy spellings agree on every history, including all firstStop
and rough-activation decisions before the variable fourth continuation. -/
theorem policy4_eq_original_fifth_spelling {ι : Type*} (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) :
    policy4 e chi m omega N rows eligible profile =
      P1OriginalHistoricalRetainedModulusLevel.originalFifthPolicy e chi m omega N
        (fun pre => level4 e chi m omega N rows eligible profile (rosserAncestor 4 pre)) := by
  unfold policy4 P1OriginalHistoricalRetainedModulusLevel.originalFifthPolicy
    fourthCappedUpperPolicy fifthCappedUpperPolicy
  rw [frozenParityRosserPolicy_nested false 4 5 (by omega : 4 ≤ 5)
    (level4 e chi m omega N rows eligible profile)]

/-- The original third-capped rank-four frontier is preserved exactly. -/
theorem frontier_four_eq_original_third {ι : Type*} (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (weight : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4 (policy4 e chi m omega N rows eligible profile)
        weight pre positive mass carrier =
      firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy e chi m omega N)
        weight pre positive mass carrier := by
  exact fourthCappedUpperPolicy_frontier_four (initialPolicy e m N)
    (rawLevel e chi m omega N) (level4 e chi m omega N rows eligible profile)
    weight pre carrier positive mass

theorem fourthDescendantLevel_eq_original_spelling {ι : Type*}
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (pre : List ℕ) :
    fourthDescendantLevel e chi m omega N rows eligible profile pre =
      P1OriginalHistoricalRetainedModulusLevel.currentLevel e chi m omega N
        (fun q => level4 e chi m omega N rows eligible profile (rosserAncestor 4 q)) pre := by
  by_cases hshort : pre.length ≤ 4
  · simp only [fourthDescendantLevel,
      P1OriginalHistoricalRetainedModulusLevel.currentLevel, if_pos hshort]
  · simp only [fourthDescendantLevel,
      P1OriginalHistoricalRetainedModulusLevel.currentLevel, if_neg hshort,
      frozenLevel4, rosserAncestor_nested 4 5 (by omega : 4 ≤ 5)]

/-- Complete validity for every retained history, including rank five and
all deeper descendants. An even-rank continuation inherits the full sorted
prefix predicate; an odd-rank selection tests it at the same frozen Q4. -/
theorem retained_leaf_valid {ι : Type*} (e chi : ℝ) (m : ℕ)
    (omega : ℝ) (N cap : ℕ) (w z : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy4 e chi m omega (N : ℝ) rows eligible profile)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      (fourthDescendantLevel e chi m omega (N : ℝ) rows eligible profile leaf.selected)
      leaf.selected := by
  have hspelling : leaf ∈ firstExitRetainedLeaves
      (P1OriginalHistoricalRetainedModulusLevel.originalFifthPolicy e chi m omega (N : ℝ)
        (fun pre => level4 e chi m omega (N : ℝ) rows eligible profile
          (rosserAncestor 4 pre))) weight [] true 1 (roughPrimeUniverse N cap w z) := by
    rw [← policy4_eq_original_fifth_spelling]
    exact hleaf
  rw [fourthDescendantLevel_eq_original_spelling]
  exact P1OriginalHistoricalRetainedModulusLevel.actual_original_fifth_retained_leaf_valid
    e chi m omega N cap w z _ heupper hN weight leaf hspelling

theorem retained_leaf_modulus_lt_current {ι : Type*} (e chi : ℝ) (m : ℕ)
    (omega : ℝ) (N cap : ℕ) (w z : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy4 e chi m omega (N : ℝ) rows eligible profile)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    (leaf.selected.prod : ℝ) <
      fourthDescendantLevel e chi m omega (N : ℝ) rows eligible profile leaf.selected := by
  exact (retained_leaf_valid e chi m omega N cap w z rows eligible profile
    heupper hN weight leaf hleaf).1

section ProducerRows

open P2OriginalFourthCapProducerInterface

/-- The actual rawQ3 seed and every pointwise M_I(t)-2e candidate remain
below the original initial exponent. This is independent of row overlap. -/
theorem producer_exponent4_le_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (pre : List ℕ) :
    exponent4 e chi m omega N rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e) pre ≤ initial e := by
  have hseed : seedExponent e chi m omega N pre ≤ initial e := by
    unfold seedExponent P1CoarseFirstCubeFallbackMargin.effectiveExponent
    split_ifs
    · exact exponent_le_initial e chi he m _
    · exact le_rfl
  have hrow (r : ProducerRow) (t : Point) :
      r.bufferedCandidate e t ≤ initial e := by
    rw [r.bufferedCandidate_eq]
    have hv := v_le_cap (∑ i ∈ r.selected, t i)
    have hc : VariableEnvelope.cap ≤ extendedDistributionCap := by
      norm_num [VariableEnvelope.cap, extendedDistributionCap]
    exact (sub_le_sub_right hv _).trans (by
      simpa only [initial] using sub_le_sub_right hc (2 * e))
  unfold exponent4
  split_ifs
  · exact finiteMax_le rows _ _ _ (initial e) hseed
      (fun r _hr _he => hrow r _)
  · exact hseed

theorem producer_frozenLevel4_le_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (pre : List ℕ) :
    producerFrozenLevel4 e chi m omega N rows licensed pre ≤ N ^ initial e := by
  change N ^ exponent4 e chi m omega N rows (producerEligible licensed)
    (fun r => r.bufferedCandidate e) (rosserAncestor 4 pre) ≤ N ^ initial e
  exact Real.rpow_le_rpow_of_exponent_le hN
    (producer_exponent4_le_initial e chi he m omega N rows licensed _)

theorem producer_descendantLevel_le_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (pre : List ℕ) :
    fourthDescendantLevel e chi m omega N rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e) pre ≤ N ^ initial e := by
  unfold fourthDescendantLevel
  split_ifs
  · exact frozenLevel_le_initial e chi he m omega N hN pre
  · exact producer_frozenLevel4_le_initial e chi he m omega N hN rows licensed pre

def producerRoughModuli (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) : Finset ℕ :=
  firstExitRetainedModuli
    (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
    (roughPrimeUniverse N cap w z)

def producerRoughCoefficient (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (d : ℕ) : ℝ :=
  (firstExitRetainedCoefficient
    (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
    (roughPrimeUniverse N cap w z) d : ℝ)

/-- A strict rough modulus bound for the exact variable-fourth policy;
the right side is the original Theta level, without a target-density premise. -/
theorem producer_roughModulus_lt_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (d : ℕ) (hd : d ∈ producerRoughModuli e chi m omega N cap w z rows licensed) :
    (d : ℝ) < (N : ℝ) ^ initial e := by
  change d ∈ firstExitRetainedModuli
    (policy4 e chi m omega (N : ℝ) rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e)) (roughPrimeUniverse N cap w z) at hd
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_firstExitRetainedModuli
      (policy4 e chi m omega (N : ℝ) rows (producerEligible licensed)
        (fun r => r.bufferedCandidate e)) (roughPrimeUniverse N cap w z) d).mp hd
  have hstrict := retained_leaf_modulus_lt_current e chi m omega N cap w z rows
    (producerEligible licensed) (fun r => r.bufferedCandidate e)
    heupper hN (fun _ => 1) leaf hleaf
  rw [hprod] at hstrict
  exact hstrict.trans_le (producer_descendantLevel_le_initial e chi he m omega
    (N : ℝ) hN.le rows licensed leaf.selected)

theorem producer_roughModulus_lt_theta (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (d : ℕ) (hd : d ∈ producerRoughModuli e chi m omega N cap w z rows licensed) :
    (d : ℝ) < (N : ℝ) ^ extendedDistributionCap := by
  have hinit : initial e ≤ extendedDistributionCap := by
    dsimp [initial]
    linarith
  exact (producer_roughModulus_lt_initial e chi he m omega N cap w z rows licensed
    heupper hN d hd).trans_le
      (Real.rpow_le_rpow_of_exponent_le hN.le hinit)

theorem producer_nonzeroCoefficient_modulus_lt_theta (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (d : ℕ)
    (hd : producerRoughCoefficient e chi m omega N cap w z rows licensed d ≠ 0) :
    (d : ℝ) < (N : ℝ) ^ extendedDistributionCap := by
  have hmem : d ∈ producerRoughModuli e chi m omega N cap w z rows licensed := by
    by_contra hnot
    apply hd
    simp [producerRoughCoefficient, firstExitRetainedCoefficient,
      producerRoughModuli, hnot]
  exact producer_roughModulus_lt_theta e chi he m omega N cap w z rows licensed
    heupper hN d hmem

end ProducerRows

end P1OriginalVariableFourthDescendantLevel
end
end ImbalancedChen
