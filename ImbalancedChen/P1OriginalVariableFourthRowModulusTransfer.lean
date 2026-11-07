import ImbalancedChen.P1OriginalVariableFourthDescendantLevel

/-!
Exact pointwise transfer from the original rough-activated raw Q3 cap to
the variable fourth cap on a retained first-exit modulus. A matching row
must win against the inherited raw Q3 seed and every other eligible row;
mere membership in a row box does not make it the maximum. Outside all
row boxes, the literal original T3 policy and retained-modulus finset agree.
Source-only candidate; no compiler was run.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthDescendantLevel
open P2OriginalFourthCapProducerInterface

namespace P1OriginalVariableFourthRowModulusTransfer

/-- A real producer row is the exact fourth cap when it dominates the
original rawQ3 seed and every simultaneously eligible producer row. -/
theorem producerLevel4_eq_winning_row (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (pre : List ℕ) (hlen : pre.length = 4) (r : ProducerRow)
    (hr : r ∈ rows)
    (her : producerEligible licensed r (primeHistoryLogCoordinates N 4 pre))
    (hseed : seedExponent e chi m omega N pre ≤
      r.bufferedCandidate e (primeHistoryLogCoordinates N 4 pre))
    (hrows : ∀ s ∈ rows,
      producerEligible licensed s (primeHistoryLogCoordinates N 4 pre) →
      s.bufferedCandidate e (primeHistoryLogCoordinates N 4 pre) ≤
        r.bufferedCandidate e (primeHistoryLogCoordinates N 4 pre)) :
    producerLevel4 e chi m omega N rows licensed pre =
      N ^ (v (∑ i ∈ r.selected, primeHistoryLogCoordinates N 4 pre i) - 2 * e) := by
  let t := primeHistoryLogCoordinates N 4 pre
  have hmax : profile4 (seedExponent e chi m omega N pre) rows
      (producerEligible licensed) (fun s => s.bufferedCandidate e) t =
        r.bufferedCandidate e t := by
    apply le_antisymm
    · exact finiteMax_le rows _ _ _ _ hseed hrows
    · exact profile4_row_le _ rows (producerEligible licensed) _ t r hr her
  change N ^ (if pre.length = 4 then
      profile4 (seedExponent e chi m omega N pre) rows
        (producerEligible licensed) (fun s => s.bufferedCandidate e) t
      else seedExponent e chi m omega N pre) = _
  rw [if_pos hlen, hmax, r.bufferedCandidate_eq]

/-- The winning pointwise cap remains frozen at that exact fourth history
through the fifth selection and all later descendants. -/
theorem producerDescendantLevel_eq_winning_row (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (pre : List ℕ) (hlen : 5 ≤ pre.length)
    (r : ProducerRow) (hr : r ∈ rows)
    (her : producerEligible licensed r
      (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)))
    (hseed : seedExponent e chi m omega N (rosserAncestor 4 pre) ≤
      r.bufferedCandidate e (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)))
    (hrows : ∀ s ∈ rows,
      producerEligible licensed s
        (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)) →
      s.bufferedCandidate e (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)) ≤
        r.bufferedCandidate e (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre))) :
    fourthDescendantLevel e chi m omega N rows (producerEligible licensed)
      (fun s => s.bufferedCandidate e) pre =
        N ^ (v (∑ i ∈ r.selected,
          primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) i) - 2 * e) := by
  have hlen4 : (rosserAncestor 4 pre).length = 4 := by
    rw [rosserAncestor_length]
    omega
  have hcap := producerLevel4_eq_winning_row e chi m omega N rows licensed
    (rosserAncestor 4 pre) hlen4 r hr her hseed hrows
  rw [fourthDescendantLevel, if_neg (by omega : ¬pre.length ≤ 4)]
  change producerLevel4 e chi m omega N rows licensed (rosserAncestor 4 pre) = _
  exact hcap

/-- One retained first-exit leaf supplies a rough modulus witness whose
strict cap is precisely the winning row's M_I(t)-2e value. -/
theorem retained_winning_row_modulus (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (hlen : 5 ≤ leaf.selected.length) (r : ProducerRow) (hr : r ∈ rows)
    (her : producerEligible licensed r
      (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected)))
    (hseed : seedExponent e chi m omega (N : ℝ) (rosserAncestor 4 leaf.selected) ≤
      r.bufferedCandidate e
        (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected)))
    (hrows : ∀ s ∈ rows,
      producerEligible licensed s
        (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected)) →
      s.bufferedCandidate e
          (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected)) ≤
        r.bufferedCandidate e
          (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected))) :
    leaf.selected.prod ∈ producerRoughModuli e chi m omega N cap w z rows licensed ∧
      fourthDescendantLevel e chi m omega (N : ℝ) rows (producerEligible licensed)
        (fun s => s.bufferedCandidate e) leaf.selected =
          (N : ℝ) ^ (v (∑ i ∈ r.selected,
            primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected) i) -
              2 * e) ∧
      (leaf.selected.prod : ℝ) <
          (N : ℝ) ^ (v (∑ i ∈ r.selected,
            primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected) i) -
              2 * e) := by
  have hmem : leaf.selected.prod ∈
      producerRoughModuli e chi m omega N cap w z rows licensed := by
    apply (mem_firstExitRetainedModuli
      (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
      (roughPrimeUniverse N cap w z) leaf.selected.prod).mpr
    exact ⟨leaf, hleaf, rfl⟩
  have hcap := producerDescendantLevel_eq_winning_row e chi m omega (N : ℝ)
    rows licensed leaf.selected hlen r hr her hseed hrows
  have hstrict := retained_leaf_modulus_lt_current e chi m omega N cap w z rows
    (producerEligible licensed) (fun s => s.bufferedCandidate e)
    heupper hN (fun _ => 1) leaf hleaf
  exact ⟨hmem, hcap, hcap ▸ hstrict⟩

/-- Outside every producer box, Q4 is exactly the original rawQ3 frozen
level, including its rough-inactive or unselected Theta fallback. -/
theorem producerDescendantLevel_eq_rawQ3_outside (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (pre : List ℕ) (hlen : 5 ≤ pre.length)
    (hout : ∀ r ∈ rows,
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) ∉ r.box) :
    fourthDescendantLevel e chi m omega N rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e) pre =
        frozenLevel e chi m omega N pre := by
  rw [fourthDescendantLevel, if_neg (by omega : ¬pre.length ≤ 4)]
  exact frozenLevel4_outside e chi m omega N rows (producerEligible licensed)
    (fun r => r.bufferedCandidate e) pre (by
      intro r hr he
      exact hout r hr he.2)

/-- On an outside retained leaf, the strict modulus bound transfers to the
same original rawQ3 cap, with no replacement fifth gain. -/
theorem retained_outside_modulus_lt_rawQ3 (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (hlen : 5 ≤ leaf.selected.length)
    (hout : ∀ r ∈ rows,
      primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected) ∉ r.box) :
    leaf.selected.prod ∈ producerRoughModuli e chi m omega N cap w z rows licensed ∧
      (leaf.selected.prod : ℝ) <
        frozenLevel e chi m omega (N : ℝ) leaf.selected := by
  have hmem : leaf.selected.prod ∈
      producerRoughModuli e chi m omega N cap w z rows licensed := by
    apply (mem_firstExitRetainedModuli
      (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
      (roughPrimeUniverse N cap w z) leaf.selected.prod).mpr
    exact ⟨leaf, hleaf, rfl⟩
  have hcap := producerDescendantLevel_eq_rawQ3_outside e chi m omega (N : ℝ)
    rows licensed leaf.selected hlen hout
  have hstrict := retained_leaf_modulus_lt_current e chi m omega N cap w z rows
    (producerEligible licensed) (fun r => r.bufferedCandidate e)
    heupper hN (fun _ => 1) leaf hleaf
  exact ⟨hmem, hcap ▸ hstrict⟩

/-- If every queried fourth ancestor misses every licensed box, the entire
literal Q4 policy and its retained rough-modulus set equal the original T3
policy and support. This is stronger than equality of a single cap. -/
theorem producerRoughModuli_eq_originalT3_of_global_outside
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (hout : ∀ pre : List ℕ, ∀ r ∈ rows,
      primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 pre) ∉ r.box) :
    producerRoughModuli e chi m omega N cap w z rows licensed =
      firstExitRetainedModuli (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
        (roughPrimeUniverse N cap w z) := by
  have hpolicy : producerPolicy4 e chi m omega (N : ℝ) rows licensed =
      HistoricalThirdCoarse.policy e chi m omega (N : ℝ) := by
    funext positive pre
    exact producerPolicy4_outside_rows e chi m omega (N : ℝ) rows licensed
      positive pre (hout pre)
  simp only [producerRoughModuli, hpolicy]

end P1OriginalVariableFourthRowModulusTransfer
end
end ImbalancedChen
