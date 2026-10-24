import ImbalancedChen.CurrentP5CausalCommonReceiverPartition

/-!
# A literal heterogeneous marked source for all eleven Upsilon terms

Source-only candidate, uncompiled. The first import is the preceding
source-only common receiver partition candidate at its intended path.
The marks retain the row, additive prime and every witness coordinate.
Padding is injective within each row. No quotient by prime product occurs.
The single original predicate E is complemented in rows six and eleven.
-/

namespace ImbalancedChen

open scoped BigOperators Classical

noncomputable section

abbrev P5WitnessFour := (ℕ × ℕ) × (ℕ × ℕ)
abbrev P5MarkedWitness := Fin 11 × (ℕ × P5WitnessFour)

def p5WitnessZero : P5WitnessFour := ((0, 0), (0, 0))

def p5PadOne (p : ℕ) : P5WitnessFour := ((p, 0), (0, 0))

def p5PadPair (p : ℕ × ℕ) : P5WitnessFour := (p, (0, 0))

theorem p5PadOne_injective : Function.Injective p5PadOne := by
  intro p q h
  exact congrArg (fun t : P5WitnessFour => t.1.1) h

theorem p5PadPair_injective : Function.Injective p5PadPair := by
  intro p q h
  exact congrArg (fun t : P5WitnessFour => t.1) h

theorem p5PadFour_injective : Function.Injective (fun t : P5WitnessFour => t) := by
  intro p q h
  exact h

theorem p5PadOne_card (T : Finset ℕ) : (T.image p5PadOne).card = T.card :=
  Finset.card_image_of_injective T p5PadOne_injective

theorem p5PadPair_card (T : Finset (ℕ × ℕ)) : (T.image p5PadPair).card = T.card :=
  Finset.card_image_of_injective T p5PadPair_injective

/-- Indicator rows have one marked witness precisely when their actual
rough quotient indicator is one. -/
def p5IndicatorWitness (condition : Prop) : Finset P5WitnessFour :=
  if condition then {p5WitnessZero} else ∅

theorem p5IndicatorWitness_card (condition : Prop) :
    (p5IndicatorWitness condition).card = if condition then 1 else 0 := by
  by_cases h : condition <;> simp [p5IndicatorWitness, h]

theorem p5IndicatorWitness_quotient_one (n : ℕ) (A : ℝ) :
    p5IndicatorWitness (ChenQuotient 1 A n) =
      if ChenPrimeRough A n then {p5WitnessZero} else ∅ := by
  simp only [p5IndicatorWitness, chenQuotient_one_iff]

/-- Every fibre is an actual chenY witness set. Four-prime rows have no
padding or projection, and the full eleventh endpoint is unchanged. -/
def p5PaddedActualWitnesses (N : ℕ) (E : ℕ × ℕ → Prop) (n : ℕ) :
    Fin 11 → Finset P5WitnessFour :=
  ![p5IndicatorWitness (ChenQuotient 1 ((N : ℝ) ^ (417 / 5000 : ℝ)) n),
    p5IndicatorWitness (ChenQuotient 1 ((N : ℝ) ^ (19 / 125 : ℝ)) n),
    (chenSinglePrimeTuples n ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))).image p5PadOne,
    (chenSinglePrimeTuples n ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))).image p5PadOne,
    (chenY5Tuples n ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ))).image p5PadPair,
    (chenY6SelectedTuples n ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))
      (fun t => ¬ E t)).image p5PadPair,
    (chenY7Tuples n (N : ℝ) ((N : ℝ) ^ (59 / 250 : ℝ))).image p5PadPair,
    (chenY8Tuples n (N : ℝ) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))).image p5PadPair,
    (chenY9Tuples n (N : ℝ) ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))).image p5PadPair,
    chenY10Tuples n ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ)),
    chenY11SelectedTuples n ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))
      (fun t => ¬ E t)]

/-- Padding preserves the literal count separately at each receiver. -/
theorem p5PaddedActualWitnesses_card (N : ℕ) (E : ℕ × ℕ → Prop)
    (P : ℕ) (i : Fin 11) :
    ((p5PaddedActualWitnesses N E (N - P) i).card : ℝ) =
      p5CausalReceiverOccurrence N E P i := by
  fin_cases i <;>
    simp [p5PaddedActualWitnesses, p5CausalReceiverOccurrence,
      p5IndicatorWitness_card, p5PadOne_card, p5PadPair_card,
      chenY1, chenY2, chenY3, chenY4, chenY5, chenY6Selected,
      chenY7, chenY8, chenY9, chenY10, chenY11Selected]

/-- Constant-fibre sigma marks are converted to ordinary products without
forgetting either coordinate. This is used twice, not a product quotient. -/
def p5ConstantSigmaPair {α β : Type*} (t : Sigma (fun _ : α => β)) : α × β :=
  (t.1, t.2)

theorem p5ConstantSigmaPair_injective {α β : Type*} :
    Function.Injective (@p5ConstantSigmaPair α β) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hac : a = c := congrArg Prod.fst h
  have hbd : b = d := congrArg Prod.snd h
  subst c
  subst d
  rfl

theorem mem_p5ConstantSigmaPair_image {α β : Type*}
    [DecidableEq α] [DecidableEq β] (S : Finset α) (T : α → Finset β)
    (a : α) (b : β) :
    (a, b) ∈ (S.sigma T).image p5ConstantSigmaPair ↔ a ∈ S ∧ b ∈ T a := by
  constructor
  · intro h
    obtain ⟨⟨c, d⟩, hcd, heq⟩ := Finset.mem_image.mp h
    have hca : c = a := congrArg Prod.fst heq
    have hdb : d = b := congrArg Prod.snd heq
    subst c
    subst d
    exact Finset.mem_sigma.mp hcd
  · intro h
    exact Finset.mem_image.mpr ⟨⟨a, b⟩, Finset.mem_sigma.mpr h, rfl⟩

/-- A row source retains every original additive-prime label P. -/
def p5MarkedRowSource (N : ℕ) (E : ℕ × ℕ → Prop) (i : Fin 11) :
    Finset (ℕ × P5WitnessFour) :=
  ((chenAdditivePrimeCarrier N).sigma
    (fun P => p5PaddedActualWitnesses N E (N - P) i)).image p5ConstantSigmaPair

@[simp] theorem mem_p5MarkedRowSource (N : ℕ) (E : ℕ × ℕ → Prop)
    (i : Fin 11) (P : ℕ) (q : P5WitnessFour) :
    (P, q) ∈ p5MarkedRowSource N E i ↔
      P ∈ chenAdditivePrimeCarrier N ∧ q ∈ p5PaddedActualWitnesses N E (N - P) i :=
  mem_p5ConstantSigmaPair_image _ _ P q

/-- One finite tagged set for all heterogeneous eleven sources. -/
def p5MarkedElevenSource (N : ℕ) (E : ℕ × ℕ → Prop) : Finset P5MarkedWitness :=
  ((Finset.univ : Finset (Fin 11)).sigma (p5MarkedRowSource N E)).image
    p5ConstantSigmaPair

@[simp] theorem mem_p5MarkedElevenSource (N : ℕ) (E : ℕ × ℕ → Prop)
    (i : Fin 11) (P : ℕ) (q : P5WitnessFour) :
    (i, (P, q)) ∈ p5MarkedElevenSource N E ↔
      P ∈ chenAdditivePrimeCarrier N ∧ q ∈ p5PaddedActualWitnesses N E (N - P) i := by
  simp only [p5MarkedElevenSource, mem_p5ConstantSigmaPair_image,
    Finset.mem_univ, true_and, mem_p5MarkedRowSource]

/-- Each padded row has exactly its original actual Upsilon cardinality. -/
theorem p5MarkedRowSource_card (N : ℕ) (E : ℕ × ℕ → Prop) (i : Fin 11) :
    ((p5MarkedRowSource N E i).card : ℝ) =
      ![currentChenUpsilon1 N, currentChenUpsilon2 N,
        currentChenUpsilon3 N, currentChenUpsilon4 N,
        currentChenUpsilon5 N, currentChenUpsilon6 N E,
        currentChenUpsilon7 N, currentChenUpsilon8 N,
        currentChenUpsilon9 N, currentChenUpsilon10 N,
        currentChenUpsilon11 N E] i := by
  have hcard : ((p5MarkedRowSource N E i).card : ℝ) =
      ∑ P ∈ chenAdditivePrimeCarrier N, p5CausalReceiverOccurrence N E P i := by
    rw [p5MarkedRowSource, Finset.card_image_of_injective _ p5ConstantSigmaPair_injective,
      Finset.card_sigma, Nat.cast_sum]
    exact Finset.sum_congr rfl
      (fun P hP => p5PaddedActualWitnesses_card N E P i)
  rw [hcard]
  have h := p5CausalCellOccurrence_sum N E (fun _ : ℕ => ()) i
  simpa [p5CausalCellOccurrence, p5CausalReceiverCell] using h

/-- Row marks are disjoint even if padding or prime products coincide. -/
theorem p5MarkedElevenSource_row_filter (N : ℕ) (E : ℕ × ℕ → Prop) (i : Fin 11) :
    (p5MarkedElevenSource N E).filter (fun t => t.1 = i) =
      (p5MarkedRowSource N E i).image (fun t => (i, t)) := by
  ext t
  rcases t with ⟨j, P, q⟩
  constructor
  · intro h
    obtain ⟨hsource, hji⟩ := Finset.mem_filter.mp h
    subst j
    exact Finset.mem_image.mpr ⟨(P, q),
      (mem_p5MarkedRowSource N E i P q).mpr
        ((mem_p5MarkedElevenSource N E i P q).mp hsource), rfl⟩
  · intro h
    obtain ⟨⟨Q, r⟩, hrow, heq⟩ := Finset.mem_image.mp h
    cases heq
    exact Finset.mem_filter.mpr
      ⟨(mem_p5MarkedElevenSource N E i Q r).mpr
        ((mem_p5MarkedRowSource N E i Q r).mp hrow), rfl⟩

theorem p5MarkedElevenSource_row_filter_card (N : ℕ) (E : ℕ × ℕ → Prop) (i : Fin 11) :
    ((p5MarkedElevenSource N E).filter (fun t => t.1 = i)).card =
      (p5MarkedRowSource N E i).card := by
  rw [p5MarkedElevenSource_row_filter,
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]

/-- Summing a function of the row over the actual marks counts every
receiver/witness once, with no division by a witness multiplicity. -/
theorem p5MarkedElevenSource_sum_by_row (N : ℕ) (E : ℕ × ℕ → Prop)
    (f : Fin 11 → ℝ) :
    (∑ t ∈ p5MarkedElevenSource N E, f t.1) =
      ∑ i, ((p5MarkedRowSource N E i).card : ℝ) * f i := by
  rw [p5MarkedElevenSource, Finset.sum_image]
  · rw [Finset.sum_sigma]
    simp only [p5ConstantSigmaPair, Finset.sum_const, nsmul_eq_mul]
  · intro a ha b hb h
    exact p5ConstantSigmaPair_injective h

/-- The signed heterogeneous source is the literal paired prime sum. -/
theorem p5MarkedElevenSource_signed_sum (N : ℕ) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ p5MarkedElevenSource N E, p5CausalReceiverLedgerWeight t.1) =
      currentChenPairedPrimeSum N E := by
  rw [p5MarkedElevenSource_sum_by_row, currentChenPairedPrimeSum_eq_upsilon]
  simp [p5MarkedRowSource_card, p5CausalReceiverLedgerWeight,
    Fin.sum_univ_succ] <;> ring

end

end ImbalancedChen
