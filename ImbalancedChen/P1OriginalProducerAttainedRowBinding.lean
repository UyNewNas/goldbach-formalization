import ImbalancedChen.P1OriginalVariableFourthRowModulusTransfer
import ImbalancedChen.P1OriginalCoarseFourthJointGeometry
import ImbalancedChen.ActualUpperPolicyFiniteBridge

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Construct a winning row from the literal finite producer maximum. The seed
branch is retained even inside a producer box: box membership alone cannot
prove that a row wins. Original joint geometry below is derived from actual
admitted tuples of HistoricalThirdCoarse.policy, which includes firstStop
and rough-activated rawQ3. No ordinary HistoricalPrefixCapData parent is
identified with this policy. The physical attachment is that of this exact
variable-fourth policy, and no stored-fifth density is identified with it.
-/

namespace ImbalancedChen.P1OriginalProducerAttainedRowBinding
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthDescendantLevel
open P1OriginalVariableFourthRowModulusTransfer

/-- Finite maximization supplies its winner; row dominance is a conclusion.
The original seed is a genuine alternative even when eligible rows exist. -/
theorem finiteMax_seed_or_winning_row {ι : Type*} (rows : Finset ι)
    (eligible : ι → Prop) (profile : ι → ℝ) (seed : ℝ) :
    (finiteMax rows eligible profile seed = seed ∧
      ∀ r ∈ rows, eligible r → profile r ≤ seed) ∨
    ∃ r ∈ rows, eligible r ∧ seed ≤ profile r ∧
      (∀ s ∈ rows, eligible s → profile s ≤ profile r) ∧
      finiteMax rows eligible profile seed = profile r := by
  have hm : finiteMax rows eligible profile seed ∈
      finiteValues rows eligible profile seed := by
    exact Finset.max'_mem _ _
  change finiteMax rows eligible profile seed ∈
    insert seed ((rows.filter eligible).image profile) at hm
  rcases Finset.mem_insert.mp hm with hs | hr
  · exact Or.inl ⟨hs, fun r hr he => hs ▸
      finiteMax_row_le rows eligible profile seed r hr he⟩
  · obtain ⟨r, hr, hv⟩ := Finset.mem_image.mp hr
    have hmax : finiteMax rows eligible profile seed = profile r := hv.symm
    obtain ⟨hr, he⟩ := Finset.mem_filter.mp hr
    exact Or.inr ⟨r, hr, he, hmax ▸ finiteMax_seed_le rows eligible profile seed,
      fun s hs hse => hmax ▸ finiteMax_row_le rows eligible profile seed s hs hse,
      hmax⟩

/-- The actual rank-four level resolves into the inherited rawQ3 level or
an attained licensed producer row. There are no winning-row premises. -/
theorem level4_seed_or_attained_row (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (pre : List ℕ) (hlen : pre.length = 4) :
    producerLevel4 e chi m omega N rows licensed pre =
        frozenLevel e chi m omega N pre ∨
      ∃ r ∈ rows, producerEligible licensed r (primeHistoryLogCoordinates N 4 pre) ∧
        producerLevel4 e chi m omega N rows licensed pre =
          N ^ (VariableEnvelope.v
            (∑ i ∈ r.selected, primeHistoryLogCoordinates N 4 pre i) - 2 * e) := by
  rcases finiteMax_seed_or_winning_row rows
      (fun r => producerEligible licensed r (primeHistoryLogCoordinates N 4 pre))
      (fun r => r.bufferedCandidate e (primeHistoryLogCoordinates N 4 pre))
      (seedExponent e chi m omega N pre) with hs | hr
  · left
    rw [frozenLevel_eq_rpow_seed]
    change N ^ (if pre.length = 4 then _ else _) = _
    rw [if_pos hlen]
    exact congrArg (fun x : ℝ => N ^ x) hs.1
  · obtain ⟨r, hr, he, hseed, hrows, _hmax⟩ := hr
    exact Or.inr ⟨r, hr, he,
      producerLevel4_eq_winning_row e chi m omega N rows licensed pre hlen r hr he
        hseed hrows⟩

/-- Descendants use the exact fourth ancestor of their own retained
history. The seed and all overlapping producer rows participate. -/
theorem descendant_seed_or_attained_row (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (pre : List ℕ) (hlen : 5 ≤ pre.length) :
    fourthDescendantLevel e chi m omega N rows (producerEligible licensed)
        (fun r => r.bufferedCandidate e) pre = frozenLevel e chi m omega N pre ∨
      ∃ r ∈ rows,
        producerEligible licensed r
          (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)) ∧
        fourthDescendantLevel e chi m omega N rows (producerEligible licensed)
            (fun s => s.bufferedCandidate e) pre =
          N ^ (VariableEnvelope.v (∑ i ∈ r.selected,
            primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) i) - 2 * e) := by
  have hl4 : (rosserAncestor 4 pre).length = 4 := by
    rw [rosserAncestor_length]
    omega
  have hlevel : fourthDescendantLevel e chi m omega N rows
      (producerEligible licensed) (fun r => r.bufferedCandidate e) pre =
      producerLevel4 e chi m omega N rows licensed (rosserAncestor 4 pre) := by
    rw [fourthDescendantLevel, if_neg (by omega : ¬pre.length ≤ 4)]
    rfl
  rw [hlevel]
  have hs : frozenLevel e chi m omega N (rosserAncestor 4 pre) =
      frozenLevel e chi m omega N pre := by
    rw [frozenLevel_eq_rpow_seed, frozenLevel_eq_rpow_seed,
      seedExponent_ancestor_four]
  simpa only [hs] using level4_seed_or_attained_row e chi m omega N rows licensed
    (rosserAncestor 4 pre) hl4

/-- An actual retained descendant binds its strict modulus bound to the
constructed cap winner. This does not discard the original-seed branch. -/
theorem retained_modulus_seed_or_attained_row (e chi : ℝ) (m : ℕ)
    (omega : ℝ) (N cap : ℕ) (w z : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (hlen : 5 ≤ leaf.selected.length) :
    leaf.selected.prod ∈ producerRoughModuli e chi m omega N cap w z rows licensed ∧
      ((leaf.selected.prod : ℝ) < frozenLevel e chi m omega (N : ℝ) leaf.selected ∨
      ∃ r ∈ rows,
        producerEligible licensed r
          (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected)) ∧
        (leaf.selected.prod : ℝ) < (N : ℝ) ^ (VariableEnvelope.v (∑ i ∈ r.selected,
          primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 leaf.selected) i) - 2 * e)) := by
  have hstrict := retained_leaf_modulus_lt_current e chi m omega N cap w z rows
    (producerEligible licensed) (fun r => r.bufferedCandidate e)
    heupper hN (fun _ => 1) leaf hleaf
  refine ⟨?_, ?_⟩
  · exact (mem_firstExitRetainedModuli _ _ _).mpr ⟨leaf, hleaf, rfl⟩
  · rcases descendant_seed_or_attained_row e chi m omega (N : ℝ) rows licensed
        leaf.selected hlen with hs | hr
    · exact Or.inl (hs ▸ hstrict)
    · obtain ⟨r, hr, he, hcap⟩ := hr
      exact Or.inr ⟨r, hr, he, hcap ▸ hstrict⟩

/-- Original JOINT geometry is produced from actual original-policy
admission, rather than inferred from an ordinary parent's cube tests. -/
theorem original_joint_geometry_from_admission (e chi : ℝ) (m n : ℕ)
    (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j3 : Cell m) (hj3 : j3 ∈ cells e chi m)
    (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N p ∈ P1OriginalFourth.jointCell m n j3 j4)
    (hp : p ∈ firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) :
    actualPrimeTupleLog N p ∈ P1OriginalFourth.jointRegion e omega m j3 := by
  exact ((P1OriginalFourth.mem_admitted_iff_log_on_selected_jointCell
    e chi m n omega N cap hN hcap p j3 hj3 j4 hwhole ht).mp hp).2

/-- The common original joint cell and the winning producer geometry refer
to one actual tuple. Both original firstStop/rawQ3 gates are obtained from
its original admission; every raised prefix/selected square comes from the
attained producer's endpoint geometry, rather than a postulated winner. -/
theorem original_admitted_tuple_row_binding (e chi : ℝ) (m n : ℕ)
    (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (hlicenses : ∀ r ∈ rows, licensed r → r.Geometry)
    (p : Fin 4 → ℕ) (j3 : Cell m) (hj3 : j3 ∈ cells e chi m)
    (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N p ∈ P1OriginalFourth.jointCell m n j3 j4)
    (hp : p ∈ firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) :
    actualPrimeTupleLog N p ∈ P1OriginalFourth.jointRegion e omega m j3 ∧
      (producerLevel4 e chi m omega (N : ℝ) rows licensed (P1OriginalFourth.history4 p) =
          frozenLevel e chi m omega (N : ℝ) (P1OriginalFourth.history4 p) ∨
      ∃ r ∈ rows, r.Geometry ∧ actualPrimeTupleLog N p ∈ r.box ∧
        producerLevel4 e chi m omega (N : ℝ) rows licensed (P1OriginalFourth.history4 p) =
          (N : ℝ) ^ (VariableEnvelope.v (∑ i ∈ r.selected, actualPrimeTupleLog N p i) - 2 * e) ∧
        (∀ k, prefixSquareExpr (actualPrimeTupleLog N p) k < r.candidate (actualPrimeTupleLog N p)) ∧
        (∀ k ∉ r.selected, selectedSquareExpr r.selected (actualPrimeTupleLog N p) k <
          r.candidate (actualPrimeTupleLog N p))) := by
  refine ⟨original_joint_geometry_from_admission e chi m n omega N cap hN hcap
    p j3 hj3 j4 hwhole ht hp, ?_⟩
  rcases level4_seed_or_attained_row e chi m omega (N : ℝ) rows licensed
      (P1OriginalFourth.history4 p) (by simp [P1OriginalFourth.history4]) with hs | hr
  · exact Or.inl hs
  · obtain ⟨r, hr, he, hrow⟩ := hr
    rw [P1OriginalFourth.history4_log] at he hrow
    have hg : r.Geometry := hlicenses r hr he.1
    have hs := r.geometry_sound hg (actualPrimeTupleLog N p) he.2
    exact Or.inr ⟨r, hr, hg, he.2, hrow, hs.2.2.2.1, hs.2.2.2.2⟩
/-- The variable producer's physical rho uses its very own first-exit
support and Mobius coefficient. This is not a stored-fifth identification. -/
theorem producer_same_physical_rho (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (w z L : ℝ) :
    actualSmallRoughRho (producerPolicy4 e chi m omega (N : ℝ) rows licensed false)
      N cap w z L =
    smallRoughRho (actualSmallRosserSupport N cap w)
      (producerRoughModuli e chi m omega N cap w z rows licensed)
      (producerRoughCoefficient e chi m omega N cap w z rows licensed)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  exact UpperPolicyFiniteBridge.actualSmallRoughRho_eq_firstExitAttachment
    (producerPolicy4 e chi m omega (N : ℝ) rows licensed) (by
      intro pre
      apply fourthCappedUpperPolicy_even_retained
      intro history
      simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]) N cap w z L

/-- The all-skip branch supplies d=1 with the empty history, independently
of every row licence or cap comparison. Rank-five premises are unnecessary. -/
theorem producer_empty_history_mem (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (w z : ℝ) :
    ({selected := [], positive := true, mass := 1} : FirstExitLeaf ℕ) ∈
      firstExitRetainedLeaves (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) := by
  exact firstExitRetainedLeaves_skipAll_mem _ _ _ _ _ _

theorem producer_one_mem (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (w z : ℝ) :
    1 ∈ producerRoughModuli e chi m omega N cap w z rows licensed := by
  apply (mem_firstExitRetainedModuli _ _ _).mpr
  exact ⟨⟨[], true, 1⟩,
    producer_empty_history_mem e chi m omega rows licensed N cap w z, by simp⟩

theorem producer_coefficient_one (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (w z : ℝ) :
    producerRoughCoefficient e chi m omega N cap w z rows licensed 1 = 1 := by
  have hmem := producer_one_mem e chi m omega rows licensed N cap w z
  simp only [producerRoughModuli] at hmem
  simp [producerRoughCoefficient, firstExitRetainedCoefficient, hmem]

end
end ImbalancedChen.P1OriginalProducerAttainedRowBinding