import ImbalancedChen.CurrentChenMeanLedger

/-!
# A common finite partition of the actual eleven receiver sources

Source-only candidate, uncompiled. Cells are genuine disjoint fibres of
`chenAdditivePrimeCarrier N`, not an assumed partition record. Different
occurrences can have different finite local policy labels. Taking all
eleven labels together constructs one finite common refinement.

The source in each cell remains the literal `chenY` count at `N - P`.
The same original pair predicate `E` occurs in six and eleven, including
the entire eleventh last-prime interval. Classifiers select additive
receiver cells only: their fibres are not asserted to be Cartesian boxes
of prime tuples. No admissibility, density or distribution claim is made.
-/

namespace ImbalancedChen

open scoped BigOperators Classical

noncomputable section

/-- The actual additive-prime cell carrying a finite local policy label. -/
def p5CausalReceiverCell {ι : Type*} [DecidableEq ι]
    (N : ℕ) (label : ℕ → ι) (a : ι) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter (fun P => label P = a)

@[simp] theorem mem_p5CausalReceiverCell {ι : Type*} [DecidableEq ι]
    {N P : ℕ} {label : ℕ → ι} {a : ι} :
    P ∈ p5CausalReceiverCell N label a ↔
      P ∈ chenAdditivePrimeCarrier N ∧ label P = a := by
  simp only [p5CausalReceiverCell, Finset.mem_filter]

theorem p5CausalReceiverCell_subset {ι : Type*} [DecidableEq ι]
    (N : ℕ) (label : ℕ → ι) (a : ι) :
    p5CausalReceiverCell N label a ⊆ chenAdditivePrimeCarrier N :=
  Finset.filter_subset _ _

theorem p5CausalReceiverCell_disjoint {ι : Type*} [DecidableEq ι]
    (N : ℕ) (label : ℕ → ι) {a b : ι} (hab : a ≠ b) :
    Disjoint (p5CausalReceiverCell N label a) (p5CausalReceiverCell N label b) := by
  apply Finset.disjoint_left.mpr
  intro P ha hb
  exact hab ((mem_p5CausalReceiverCell.mp ha).2.symm.trans
    (mem_p5CausalReceiverCell.mp hb).2)

/-- The finite cell family covers the original carrier exactly. Empty
cells are allowed and introduce no new receiver or multiplicity. -/
theorem p5CausalReceiverCell_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (label : ℕ → ι) :
    Finset.univ.biUnion (p5CausalReceiverCell N label) = chenAdditivePrimeCarrier N := by
  classical
  ext P
  constructor
  · intro hP
    obtain ⟨a, ha, hcell⟩ := Finset.mem_biUnion.mp hP
    exact (mem_p5CausalReceiverCell.mp hcell).1
  · intro hP
    exact Finset.mem_biUnion.mpr
      ⟨label P, Finset.mem_univ _, mem_p5CausalReceiverCell.mpr ⟨hP, rfl⟩⟩

/-- Finite Fubini on the actual carrier. All later specializations retain
the original receiver label even when two receivers have equal products. -/
theorem p5CausalReceiverCell_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (label : ℕ → ι) (f : ℕ → ℝ) :
    (∑ a, ∑ P ∈ p5CausalReceiverCell N label a, f P) =
      ∑ P ∈ chenAdditivePrimeCarrier N, f P := by
  exact Finset.sum_fiberwise_of_maps_to
    (s := chenAdditivePrimeCarrier N) (t := Finset.univ) (g := label)
    (fun P hP => Finset.mem_univ _) f

/-- Every occurrence is the literal source on the same receiver. In
particular the seventh/ninth moving cutoffs and all four labels in
ten/eleven remain inside the original definitions. -/
def p5CausalReceiverOccurrence (N : ℕ) (E : ℕ × ℕ → Prop) (P : ℕ) : Fin 11 → ℝ :=
  ![(chenY1 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ)) : ℝ),
    (chenY2 (N - P) ((N : ℝ) ^ (19 / 125 : ℝ)) : ℝ),
    (chenY3 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ),
    (chenY4 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ),
    (chenY5 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) : ℝ),
    (chenY6Selected (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))
      (fun t => ¬ E t) : ℝ),
    (chenY7 (N - P) (N : ℝ) ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ),
    (chenY8 (N - P) (N : ℝ) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ),
    (chenY9 (N - P) (N : ℝ) ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ),
    (chenY10 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) : ℝ),
    (chenY11Selected (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))
      (fun t => ¬ E t) : ℝ)]

def p5CausalReceiverLedgerWeight : Fin 11 → ℝ :=
  ![3, 1, -1, -1, 1, 1, -2, -1, -1, -1, -1]

def p5CausalCellOccurrence {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι) (i : Fin 11) : ℝ :=
  ∑ P ∈ p5CausalReceiverCell N label a, p5CausalReceiverOccurrence N E P i

def p5CausalCellSignedLedger {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι) : ℝ :=
  ∑ i, p5CausalReceiverLedgerWeight i * p5CausalCellOccurrence N E label a i

/-- Pointwise source identification, before partitioning or asymptotics. -/
theorem p5CausalReceiverOccurrence_signed (N : ℕ) (E : ℕ × ℕ → Prop) (P : ℕ) :
    (∑ i, p5CausalReceiverLedgerWeight i * p5CausalReceiverOccurrence N E P i) =
      currentChenPairedWeight (N - P) (N : ℝ) E := by
  rw [currentChenPairedWeight, chenPairedElevenWeight_eq_unselected]
  simp [p5CausalReceiverLedgerWeight, p5CausalReceiverOccurrence,
    Fin.sum_univ_succ] <;> ring

/-- All eleven local sums use one cell; the signs are not moved into
absolute values and the coefficient three/minus two occur once. -/
theorem p5CausalCellSignedLedger_eq {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι) :
    p5CausalCellSignedLedger N E label a =
      ∑ P ∈ p5CausalReceiverCell N label a,
        currentChenPairedWeight (N - P) (N : ℝ) E := by
  simp only [p5CausalCellSignedLedger, p5CausalCellOccurrence, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl
    (fun P hP => p5CausalReceiverOccurrence_signed N E P)

/-- Each individual Upsilon is regrouped, not merely the completed signed
weight. This includes the original mask in both masked occurrences. -/
theorem p5CausalCellOccurrence_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (i : Fin 11) :
    (∑ a, p5CausalCellOccurrence N E label a i) =
      ![currentChenUpsilon1 N, currentChenUpsilon2 N,
        currentChenUpsilon3 N, currentChenUpsilon4 N,
        currentChenUpsilon5 N, currentChenUpsilon6 N E,
        currentChenUpsilon7 N, currentChenUpsilon8 N,
        currentChenUpsilon9 N, currentChenUpsilon10 N,
        currentChenUpsilon11 N E] i := by
  rw [show (∑ a, p5CausalCellOccurrence N E label a i) =
      ∑ P ∈ chenAdditivePrimeCarrier N, p5CausalReceiverOccurrence N E P i from
    p5CausalReceiverCell_sum N label (fun P => p5CausalReceiverOccurrence N E P i)]
  fin_cases i <;> simp [p5CausalReceiverOccurrence,
    currentChenUpsilon1, currentChenUpsilon2, currentChenUpsilon3,
    currentChenUpsilon4, currentChenUpsilon5, currentChenUpsilon6,
    currentChenUpsilon7, currentChenUpsilon8, currentChenUpsilon9,
    currentChenUpsilon10, currentChenUpsilon11]

theorem p5CausalCellSignedLedger_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) :
    (∑ a, p5CausalCellSignedLedger N E label a) = currentChenPairedPrimeSum N E := by
  simp_rw [p5CausalCellSignedLedger_eq]
  exact p5CausalReceiverCell_sum N label
    (fun P => currentChenPairedWeight (N - P) (N : ℝ) E)

/-- An externally supplied finite partition can also be consumed directly.
Its disjointness and exact cover are explicit finite set facts, rather
than a new analytic validity record. -/
theorem p5Causal_disjoint_receiver_partition_sum {ι : Type*} [DecidableEq ι]
    (N : ℕ) (A : Finset ι) (cells : ι → Finset ℕ)
    (hdisjoint : Set.PairwiseDisjoint (A : Set ι) cells)
    (hcover : A.biUnion cells = chenAdditivePrimeCarrier N) (f : ℕ → ℝ) :
    (∑ a ∈ A, ∑ P ∈ cells a, f P) = ∑ P ∈ chenAdditivePrimeCarrier N, f P := by
  rw [← Finset.sum_biUnion hdisjoint, hcover]

/-- Arbitrary genuine disjoint receiver partitions regroup each original
Upsilon occurrence individually, with its actual tuple multiplicities. -/
theorem p5Causal_disjoint_partition_occurrence {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (A : Finset ι) (cells : ι → Finset ℕ)
    (hdisjoint : Set.PairwiseDisjoint (A : Set ι) cells)
    (hcover : A.biUnion cells = chenAdditivePrimeCarrier N) (i : Fin 11) :
    (∑ a ∈ A, ∑ P ∈ cells a, p5CausalReceiverOccurrence N E P i) =
      ![currentChenUpsilon1 N, currentChenUpsilon2 N,
        currentChenUpsilon3 N, currentChenUpsilon4 N,
        currentChenUpsilon5 N, currentChenUpsilon6 N E,
        currentChenUpsilon7 N, currentChenUpsilon8 N,
        currentChenUpsilon9 N, currentChenUpsilon10 N,
        currentChenUpsilon11 N E] i := by
  rw [p5Causal_disjoint_receiver_partition_sum N A cells hdisjoint hcover]
  have h := p5CausalCellOccurrence_sum N E (fun _ : ℕ => ()) i
  simpa [p5CausalCellOccurrence, p5CausalReceiverCell] using h

/-- The literal eleven-term signed ledger on any genuine disjoint
partition. There is one E, one original carrier and one root weighting. -/
theorem p5Causal_disjoint_partition_signed_ledger {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (A : Finset ι) (cells : ι → Finset ℕ)
    (hdisjoint : Set.PairwiseDisjoint (A : Set ι) cells)
    (hcover : A.biUnion cells = chenAdditivePrimeCarrier N) :
    (∑ a ∈ A, ∑ i, p5CausalReceiverLedgerWeight i *
      (∑ P ∈ cells a, p5CausalReceiverOccurrence N E P i)) =
      currentChenPairedPrimeSum N E := by
  calc
    _ = ∑ a ∈ A, ∑ P ∈ cells a,
        currentChenPairedWeight (N - P) (N : ℝ) E := by
      apply Finset.sum_congr rfl
      intro a ha
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl
        (fun P hP => p5CausalReceiverOccurrence_signed N E P)
    _ = _ := p5Causal_disjoint_receiver_partition_sum N A cells hdisjoint hcover
      (fun P => currentChenPairedWeight (N - P) (N : ℝ) E)

/-- A joint finite label constructs the actual intersection refinement. -/
theorem p5CausalReceiverCell_refine {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (N : ℕ) (parent : ℕ → ι) (child : ℕ → κ) (a : ι) (b : κ) :
    p5CausalReceiverCell N (fun P => (parent P, child P)) (a, b) =
      (p5CausalReceiverCell N parent a).filter (fun P => child P = b) := by
  ext P
  simp only [mem_p5CausalReceiverCell, Finset.mem_filter, Prod.mk.injEq]
  tauto

/-- A parent's full source sum is inherited by its disjoint children. -/
theorem p5CausalReceiverCell_sum_refine {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (parent : ℕ → ι) (child : ℕ → κ) (a : ι) (f : ℕ → ℝ) :
    (∑ P ∈ p5CausalReceiverCell N parent a, f P) =
      ∑ b, ∑ P ∈ p5CausalReceiverCell N (fun P => (parent P, child P)) (a, b), f P := by
  symm
  simp_rw [p5CausalReceiverCell_refine]
  exact Finset.sum_fiberwise_of_maps_to
    (s := p5CausalReceiverCell N parent a) (t := Finset.univ) (g := child)
    (fun P hP => Finset.mem_univ _) f

theorem p5CausalCellOccurrence_refine {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop) (parent : ℕ → ι) (child : ℕ → κ)
    (a : ι) (i : Fin 11) :
    p5CausalCellOccurrence N E parent a i =
      ∑ b, p5CausalCellOccurrence N E (fun P => (parent P, child P)) (a, b) i := by
  exact p5CausalReceiverCell_sum_refine N parent child a
    (fun P => p5CausalReceiverOccurrence N E P i)

theorem p5CausalCellSignedLedger_refine {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop) (parent : ℕ → ι) (child : ℕ → κ) (a : ι) :
    p5CausalCellSignedLedger N E parent a =
      ∑ b, p5CausalCellSignedLedger N E (fun P => (parent P, child P)) (a, b) := by
  simp_rw [p5CausalCellSignedLedger_eq]
  exact p5CausalReceiverCell_sum_refine N parent child a
    (fun P => currentChenPairedWeight (N - P) (N : ℝ) E)

/-- All eleven finite local policy classifiers are synchronized by one
function-valued label. No term chooses a separate receiver partition. -/
def p5CausalCommonPolicyLabel {ι : Type*}
    (policy : Fin 11 → ℕ → ι) (P : ℕ) : Fin 11 → ι := fun i => policy i P

/-- The common atom is the actual intersection of all eleven local
decision fibres, with the original additive-prime carrier retained. -/
theorem p5CausalCommonPolicyCell_eq_all {ι : Type*} [DecidableEq ι]
    (N : ℕ) (policy : Fin 11 → ℕ → ι) (a : Fin 11 → ι) :
    p5CausalReceiverCell N (p5CausalCommonPolicyLabel policy) a =
      (chenAdditivePrimeCarrier N).filter (fun P => ∀ i, policy i P = a i) := by
  ext P
  constructor
  · intro hP
    obtain ⟨hcarrier, hlabel⟩ := mem_p5CausalReceiverCell.mp hP
    exact Finset.mem_filter.mpr ⟨hcarrier, fun i => congrFun hlabel i⟩
  · intro hP
    obtain ⟨hcarrier, hlabel⟩ := Finset.mem_filter.mp hP
    exact mem_p5CausalReceiverCell.mpr ⟨hcarrier, funext hlabel⟩

theorem p5CausalCommonPolicy_constant {ι : Type*} [DecidableEq ι]
    {N P : ℕ} (policy : Fin 11 → ℕ → ι) (a : Fin 11 → ι)
    (hP : P ∈ p5CausalReceiverCell N (p5CausalCommonPolicyLabel policy) a)
    (i : Fin 11) : policy i P = a i := by
  exact congrFun (mem_p5CausalReceiverCell.mp hP).2 i

theorem p5CausalCommonPolicyCell_subset_term {ι : Type*} [DecidableEq ι]
    (N : ℕ) (policy : Fin 11 → ℕ → ι) (a : Fin 11 → ι) (i : Fin 11) :
    p5CausalReceiverCell N (p5CausalCommonPolicyLabel policy) a ⊆
      p5CausalReceiverCell N (policy i) (a i) := by
  intro P hP
  exact mem_p5CausalReceiverCell.mpr
    ⟨(mem_p5CausalReceiverCell.mp hP).1,
      p5CausalCommonPolicy_constant policy a hP i⟩

theorem p5CausalCommonPolicyCell_disjoint {ι : Type*} [DecidableEq ι]
    (N : ℕ) (policy : Fin 11 → ℕ → ι) {a b : Fin 11 → ι} (hab : a ≠ b) :
    Disjoint (p5CausalReceiverCell N (p5CausalCommonPolicyLabel policy) a)
      (p5CausalReceiverCell N (p5CausalCommonPolicyLabel policy) b) :=
  p5CausalReceiverCell_disjoint N (p5CausalCommonPolicyLabel policy) hab

theorem p5CausalCommonPolicyCell_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (policy : Fin 11 → ℕ → ι) :
    Finset.univ.biUnion (p5CausalReceiverCell N (p5CausalCommonPolicyLabel policy)) =
      chenAdditivePrimeCarrier N := by
  classical
  exact p5CausalReceiverCell_cover N (p5CausalCommonPolicyLabel policy)

/-- The actual common finite refinement supports term-dependent policy
labels while preserving the single signed source and the single E. -/
theorem p5Causal_common_policy_signed_ledger {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : Fin 11 → ℕ → ι) :
    currentChenPairedPrimeSum N E =
      ∑ a : Fin 11 → ι,
        p5CausalCellSignedLedger N E (p5CausalCommonPolicyLabel policy) a := by
  classical
  exact (p5CausalCellSignedLedger_sum N E (p5CausalCommonPolicyLabel policy)).symm

/-- Refinement replaces the selected parent. The unchanged parents and
the selected children sum to the original source exactly once. -/
theorem p5Causal_refinement_replaces_parent {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop) (parent : ℕ → ι) (child : ℕ → κ) (selected : ι) :
    (∑ a : ι, if a = selected then
      (∑ b, p5CausalCellSignedLedger N E (fun P => (parent P, child P)) (a, b))
      else p5CausalCellSignedLedger N E parent a) = currentChenPairedPrimeSum N E := by
  rw [← p5CausalCellSignedLedger_sum N E parent]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : a = selected
  · rw [if_pos h]
    exact (p5CausalCellSignedLedger_refine N E parent child a).symm
  · rw [if_neg h]

/-- A child-level bound already includes its source baseline. Its gain
over the old parent is the sum of child improvements, not the full new
bound added to the parent a second time. -/
theorem p5Causal_child_gains_once {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop) (parent : ℕ → ι) (child : ℕ → κ)
    (a : ι) (replacement : κ → ℝ) :
    (∑ b, replacement b) - p5CausalCellSignedLedger N E parent a =
      ∑ b, (replacement b -
        p5CausalCellSignedLedger N E (fun P => (parent P, child P)) (a, b)) := by
  rw [Finset.sum_sub_distrib, p5CausalCellSignedLedger_refine N E parent child a]

/-- Successive replacements telescope on the same parent. A previously
counted improvement is removed before the final replacement is applied. -/
theorem p5Causal_child_gains_telescope {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop) (parent : ℕ → ι) (child : ℕ → κ)
    (a : ι) (middle final : κ → ℝ) :
    (∑ b, (final b -
      p5CausalCellSignedLedger N E (fun P => (parent P, child P)) (a, b))) =
    ((∑ b, middle b) - p5CausalCellSignedLedger N E parent a) +
      ((∑ b, final b) - ∑ b, middle b) := by
  rw [← p5Causal_child_gains_once N E parent child a final]
  ring

end

end ImbalancedChen
