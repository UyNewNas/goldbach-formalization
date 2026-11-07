import ImbalancedChen.CurrentP5MarkedElevenWitnessSource

/-!
# Common finite tuple-policy refinement of the actual marked source

Source-only candidate, uncompiled. A policy can inspect the row, additive
prime and all padded witness coordinates. Thus these cells are finer than
receiver cells. No policy decision fibre is declared a Cartesian box.
Genuine Cartesian boxes have a separate explicit constructor and source
inclusion obligation, followed by a disjoint-cover finite assembly theorem.
-/

namespace ImbalancedChen

open scoped BigOperators Classical

noncomputable section

def p5MarkedWitnessCell {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : P5MarkedWitness → ι) (a : ι) :
    Finset P5MarkedWitness :=
  (p5MarkedElevenSource N E).filter (fun t => policy t = a)

@[simp] theorem mem_p5MarkedWitnessCell {ι : Type*} [DecidableEq ι]
    {N : ℕ} {E : ℕ × ℕ → Prop} {policy : P5MarkedWitness → ι}
    {a : ι} {t : P5MarkedWitness} :
    t ∈ p5MarkedWitnessCell N E policy a ↔
      t ∈ p5MarkedElevenSource N E ∧ policy t = a := by
  simp only [p5MarkedWitnessCell, Finset.mem_filter]

theorem p5MarkedWitnessCell_subset {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : P5MarkedWitness → ι) (a : ι) :
    p5MarkedWitnessCell N E policy a ⊆ p5MarkedElevenSource N E :=
  Finset.filter_subset _ _

theorem p5MarkedWitnessCell_disjoint {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : P5MarkedWitness → ι)
    {a b : ι} (hab : a ≠ b) :
    Disjoint (p5MarkedWitnessCell N E policy a) (p5MarkedWitnessCell N E policy b) := by
  apply Finset.disjoint_left.mpr
  intro t ha hb
  exact hab ((mem_p5MarkedWitnessCell.mp ha).2.symm.trans
    (mem_p5MarkedWitnessCell.mp hb).2)

theorem p5MarkedWitnessCell_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : P5MarkedWitness → ι) :
    Finset.univ.biUnion (p5MarkedWitnessCell N E policy) = p5MarkedElevenSource N E := by
  ext t
  constructor
  · intro h
    obtain ⟨a, ha, ht⟩ := Finset.mem_biUnion.mp h
    exact (mem_p5MarkedWitnessCell.mp ht).1
  · intro ht
    exact Finset.mem_biUnion.mpr
      ⟨policy t, Finset.mem_univ _, mem_p5MarkedWitnessCell.mpr ⟨ht, rfl⟩⟩

def p5MarkedWitnessCellContribution {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : P5MarkedWitness → ι) (a : ι) : ℝ :=
  ∑ t ∈ p5MarkedWitnessCell N E policy a, p5CausalReceiverLedgerWeight t.1

/-- Fubini retains the whole marked atom. In particular no equal-product
deduplication or tuple-to-receiver projection is involved. -/
theorem p5MarkedWitnessCell_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : P5MarkedWitness → ι)
    (f : P5MarkedWitness → ℝ) :
    (∑ a, ∑ t ∈ p5MarkedWitnessCell N E policy a, f t) =
      ∑ t ∈ p5MarkedElevenSource N E, f t := by
  exact Finset.sum_fiberwise_of_maps_to
    (s := p5MarkedElevenSource N E) (t := Finset.univ) (g := policy)
    (fun t ht => Finset.mem_univ _) f

theorem p5MarkedWitnessCellContribution_sum {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : P5MarkedWitness → ι) :
    (∑ a, p5MarkedWitnessCellContribution N E policy a) =
      currentChenPairedPrimeSum N E := by
  rw [← p5MarkedElevenSource_signed_sum N E]
  exact p5MarkedWitnessCell_sum N E policy (fun t => p5CausalReceiverLedgerWeight t.1)

/-- The joint label synchronizes any fixed finite family of tuple-policy
queries, including term-specific historical or alternative decisions. -/
def p5MarkedCommonPolicy {J ι : Type*} (policy : J → P5MarkedWitness → ι)
    (t : P5MarkedWitness) : J → ι := fun j => policy j t

theorem p5MarkedCommonPolicyCell_eq_all {J ι : Type*}
    [Fintype J] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : J → P5MarkedWitness → ι) (a : J → ι) :
    p5MarkedWitnessCell N E (p5MarkedCommonPolicy policy) a =
      (p5MarkedElevenSource N E).filter (fun t => ∀ j, policy j t = a j) := by
  ext t
  constructor
  · intro ht
    obtain ⟨hsource, hlabel⟩ := mem_p5MarkedWitnessCell.mp ht
    exact Finset.mem_filter.mpr ⟨hsource, fun j => congrFun hlabel j⟩
  · intro ht
    obtain ⟨hsource, hlabel⟩ := Finset.mem_filter.mp ht
    exact mem_p5MarkedWitnessCell.mpr ⟨hsource, funext hlabel⟩

theorem p5MarkedCommonPolicy_contribution_sum {J ι : Type*}
    [Fintype J] [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (policy : J → P5MarkedWitness → ι) :
    (∑ a : J → ι, p5MarkedWitnessCellContribution N E (p5MarkedCommonPolicy policy) a) =
      currentChenPairedPrimeSum N E :=
  p5MarkedWitnessCellContribution_sum N E (p5MarkedCommonPolicy policy)

/-- Joint policy labels form actual nested set intersections. -/
theorem p5MarkedWitnessCell_refine {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (parent : P5MarkedWitness → ι) (child : P5MarkedWitness → κ) (a : ι) (b : κ) :
    p5MarkedWitnessCell N E (fun t => (parent t, child t)) (a, b) =
      (p5MarkedWitnessCell N E parent a).filter (fun t => child t = b) := by
  ext t
  simp only [mem_p5MarkedWitnessCell, Finset.mem_filter, Prod.mk.injEq]
  tauto

theorem p5MarkedWitnessCellContribution_refine {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (parent : P5MarkedWitness → ι) (child : P5MarkedWitness → κ) (a : ι) :
    p5MarkedWitnessCellContribution N E parent a =
      ∑ b, p5MarkedWitnessCellContribution N E
        (fun t => (parent t, child t)) (a, b) := by
  symm
  simp only [p5MarkedWitnessCellContribution]
  simp_rw [p5MarkedWitnessCell_refine]
  exact Finset.sum_fiberwise_of_maps_to
    (s := p5MarkedWitnessCell N E parent a) (t := Finset.univ) (g := child)
    (fun t ht => Finset.mem_univ _) (fun t => p5CausalReceiverLedgerWeight t.1)

/-- Refined child gains subtract their actual baselines before being added. -/
theorem p5MarkedWitnessCell_child_gains_once {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (parent : P5MarkedWitness → ι) (child : P5MarkedWitness → κ)
    (a : ι) (replacement : κ → ℝ) :
    (∑ b, replacement b) - p5MarkedWitnessCellContribution N E parent a =
      ∑ b, (replacement b - p5MarkedWitnessCellContribution N E
        (fun t => (parent t, child t)) (a, b)) := by
  rw [Finset.sum_sub_distrib, p5MarkedWitnessCellContribution_refine N E parent child a]

/-- A genuine four-coordinate Cartesian box, with its row and additive
prime fixed. Lower-dimensional sources use singleton zero padding axes. -/
def p5MarkedCartesianBox (i : Fin 11) (P : ℕ)
    (B₀ B₁ B₂ B₃ : Finset ℕ) : Finset P5MarkedWitness :=
  ((B₀ ×ˢ B₁) ×ˢ (B₂ ×ˢ B₃)).image (fun q => (i, (P, q)))

theorem p5MarkFour_injective (i : Fin 11) (P : ℕ) :
    Function.Injective (fun q : P5WitnessFour => (i, (P, q))) := by
  intro q r h
  exact congrArg (fun t : P5MarkedWitness => t.2.2) h

theorem p5MarkedCartesianBox_card (i : Fin 11) (P : ℕ)
    (B₀ B₁ B₂ B₃ : Finset ℕ) :
    (p5MarkedCartesianBox i P B₀ B₁ B₂ B₃).card =
      (B₀.card * B₁.card) * (B₂.card * B₃.card) := by
  rw [p5MarkedCartesianBox, Finset.card_image_of_injective _ (p5MarkFour_injective i P)]
  simp only [Finset.card_product]

/-- A Cartesian box can be used only after its full original witness
support is proved. This does not follow from a policy classifier. -/
theorem p5MarkedCartesianBox_subset_source (N : ℕ) (E : ℕ × ℕ → Prop)
    (i : Fin 11) (P : ℕ) (B₀ B₁ B₂ B₃ : Finset ℕ)
    (hP : P ∈ chenAdditivePrimeCarrier N)
    (hwitness : ∀ q ∈ (B₀ ×ˢ B₁) ×ˢ (B₂ ×ˢ B₃),
      q ∈ p5PaddedActualWitnesses N E (N - P) i) :
    p5MarkedCartesianBox i P B₀ B₁ B₂ B₃ ⊆ p5MarkedElevenSource N E := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
  exact (mem_p5MarkedElevenSource N E i P q).mpr ⟨hP, hwitness q hq⟩

/-- The box scalar is the original signed row coefficient, once. -/
theorem p5MarkedCartesianBox_signed_sum (i : Fin 11) (P : ℕ)
    (B₀ B₁ B₂ B₃ : Finset ℕ) :
    (∑ t ∈ p5MarkedCartesianBox i P B₀ B₁ B₂ B₃,
      p5CausalReceiverLedgerWeight t.1) =
      (((B₀.card * B₁.card) * (B₂.card * B₃.card) : ℕ) : ℝ) *
        p5CausalReceiverLedgerWeight i := by
  rw [p5MarkedCartesianBox, Finset.sum_image]
  · simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
  · intro a ha b hb h
    exact p5MarkFour_injective i P h

/-- The actual additive-prime receiver fibre of one padded tuple. Its
quotient test, moving cutoff and original selected complement remain in
the original witness definition. -/
def p5MarkedTupleReceiverFibre (N : ℕ) (E : ℕ × ℕ → Prop)
    (i : Fin 11) (q : P5WitnessFour) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter (fun P =>
    q ∈ p5PaddedActualWitnesses N E (N - P) i)

/-- A genuine outer Cartesian tuple box with its actual receiver fibres.
The additive prime is not treated as a free Cartesian coordinate. -/
def p5MarkedCartesianSourceBox (N : ℕ) (E : ℕ × ℕ → Prop) (i : Fin 11)
    (B₀ B₁ B₂ B₃ : Finset ℕ) : Finset P5MarkedWitness :=
  (((B₀ ×ˢ B₁) ×ˢ (B₂ ×ˢ B₃)).sigma
    (p5MarkedTupleReceiverFibre N E i)).image (fun t => (i, (t.2, t.1)))

theorem p5MarkTupleReceiver_injective (i : Fin 11) :
    Function.Injective (fun t : Sigma (fun _ : P5WitnessFour => ℕ) =>
      (i, (t.2, t.1))) := by
  rintro ⟨q, P⟩ ⟨r, Q⟩ h
  have hqr : q = r := congrArg (fun t : P5MarkedWitness => t.2.2) h
  have hPQ : P = Q := congrArg (fun t : P5MarkedWitness => t.2.1) h
  subst r
  subst Q
  rfl

/-- Exact source restriction by a Cartesian tuple box. This equality
does not replace any decision fibre by a Cartesian box. -/
theorem p5MarkedCartesianSourceBox_eq_filter (N : ℕ) (E : ℕ × ℕ → Prop)
    (i : Fin 11) (B₀ B₁ B₂ B₃ : Finset ℕ) :
    p5MarkedCartesianSourceBox N E i B₀ B₁ B₂ B₃ =
      (p5MarkedElevenSource N E).filter (fun t =>
        t.1 = i ∧ t.2.2 ∈ (B₀ ×ˢ B₁) ×ˢ (B₂ ×ˢ B₃)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨⟨q, P⟩, hqP, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hq, hP⟩ := Finset.mem_sigma.mp hqP
    obtain ⟨hcarrier, hwitness⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_filter.mpr
      ⟨(mem_p5MarkedElevenSource N E i P q).mpr ⟨hcarrier, hwitness⟩, rfl, hq⟩
  · intro ht
    rcases t with ⟨j, P, q⟩
    obtain ⟨hsource, hji, hq⟩ := Finset.mem_filter.mp ht
    subst j
    have hP : P ∈ p5MarkedTupleReceiverFibre N E i q := by
      exact Finset.mem_filter.mpr ((mem_p5MarkedElevenSource N E i P q).mp hsource)
    exact Finset.mem_image.mpr ⟨⟨q, P⟩, Finset.mem_sigma.mpr ⟨hq, hP⟩, rfl⟩

theorem p5MarkedCartesianSourceBox_subset (N : ℕ) (E : ℕ × ℕ → Prop)
    (i : Fin 11) (B₀ B₁ B₂ B₃ : Finset ℕ) :
    p5MarkedCartesianSourceBox N E i B₀ B₁ B₂ B₃ ⊆ p5MarkedElevenSource N E := by
  rw [p5MarkedCartesianSourceBox_eq_filter]
  exact Finset.filter_subset _ _

/-- Cartesian local-contribution Fubini uses the complete actual inner
source for every outer tuple, without a constant receiver cutoff. -/
theorem p5MarkedCartesianSourceBox_signed_sum (N : ℕ) (E : ℕ × ℕ → Prop)
    (i : Fin 11) (B₀ B₁ B₂ B₃ : Finset ℕ) :
    (∑ t ∈ p5MarkedCartesianSourceBox N E i B₀ B₁ B₂ B₃,
      p5CausalReceiverLedgerWeight t.1) =
      ∑ q ∈ (B₀ ×ˢ B₁) ×ˢ (B₂ ×ˢ B₃),
        ((p5MarkedTupleReceiverFibre N E i q).card : ℝ) *
          p5CausalReceiverLedgerWeight i := by
  rw [p5MarkedCartesianSourceBox, Finset.sum_image]
  · rw [Finset.sum_sigma]
    simp only [Finset.sum_const, nsmul_eq_mul]
  · intro a ha b hb h
    exact p5MarkTupleReceiver_injective i h

/-- Any genuine disjoint partition of marked witnesses supports local
source estimates. Its atoms may be proved Cartesian boxes separately. -/
theorem p5Marked_disjoint_partition_signed_sum {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (A : Finset ι) (cells : ι → Finset P5MarkedWitness)
    (hdisjoint : Set.PairwiseDisjoint (A : Set ι) cells)
    (hcover : A.biUnion cells = p5MarkedElevenSource N E) :
    (∑ a ∈ A, ∑ t ∈ cells a, p5CausalReceiverLedgerWeight t.1) =
      currentChenPairedPrimeSum N E := by
  rw [← Finset.sum_biUnion hdisjoint, hcover]
  exact p5MarkedElevenSource_signed_sum N E

/-- Concrete Cartesian local-contribution assembly, retaining the row,
additive prime, original signed scalar and every coordinate. Overlapping
boxes require a disjoint refinement; their gains cannot just be added. -/
theorem p5MarkedCartesian_partition_signed_sum {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (A : Finset ι)
    (row : ι → Fin 11) (prime : ι → ℕ) (B₀ B₁ B₂ B₃ : ι → Finset ℕ)
    (hdisjoint : Set.PairwiseDisjoint (A : Set ι)
      (fun a => p5MarkedCartesianBox (row a) (prime a) (B₀ a) (B₁ a) (B₂ a) (B₃ a)))
    (hcover : A.biUnion (fun a =>
      p5MarkedCartesianBox (row a) (prime a) (B₀ a) (B₁ a) (B₂ a) (B₃ a)) =
        p5MarkedElevenSource N E) :
    (∑ a ∈ A,
      (((((B₀ a).card * (B₁ a).card) * ((B₂ a).card * (B₃ a).card)) : ℕ) : ℝ) *
        p5CausalReceiverLedgerWeight (row a)) = currentChenPairedPrimeSum N E := by
  rw [← p5Marked_disjoint_partition_signed_sum N E A
    (fun a => p5MarkedCartesianBox (row a) (prime a) (B₀ a) (B₁ a) (B₂ a) (B₃ a))
    hdisjoint hcover]
  exact Finset.sum_congr rfl
    (fun a ha => (p5MarkedCartesianBox_signed_sum (row a) (prime a)
      (B₀ a) (B₁ a) (B₂ a) (B₃ a)).symm)

/-- Assembly for true outer Cartesian tuple boxes, each with its actual
P-dependent quotient source. The disjoint cover pays each mark once. -/
theorem p5MarkedCartesianSource_partition_signed_sum {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (A : Finset ι)
    (row : ι → Fin 11) (B₀ B₁ B₂ B₃ : ι → Finset ℕ)
    (hdisjoint : Set.PairwiseDisjoint (A : Set ι) (fun a =>
      p5MarkedCartesianSourceBox N E (row a) (B₀ a) (B₁ a) (B₂ a) (B₃ a)))
    (hcover : A.biUnion (fun a =>
      p5MarkedCartesianSourceBox N E (row a) (B₀ a) (B₁ a) (B₂ a) (B₃ a)) =
        p5MarkedElevenSource N E) :
    (∑ a ∈ A, ∑ q ∈ (B₀ a ×ˢ B₁ a) ×ˢ (B₂ a ×ˢ B₃ a),
      ((p5MarkedTupleReceiverFibre N E (row a) q).card : ℝ) *
        p5CausalReceiverLedgerWeight (row a)) = currentChenPairedPrimeSum N E := by
  rw [← p5Marked_disjoint_partition_signed_sum N E A
    (fun a => p5MarkedCartesianSourceBox N E (row a) (B₀ a) (B₁ a) (B₂ a) (B₃ a))
    hdisjoint hcover]
  exact Finset.sum_congr rfl
    (fun a ha => (p5MarkedCartesianSourceBox_signed_sum N E (row a)
      (B₀ a) (B₁ a) (B₂ a) (B₃ a)).symm)

end

end ImbalancedChen
