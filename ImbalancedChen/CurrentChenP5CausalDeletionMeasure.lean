import ImbalancedChen.CurrentChenP5SelectedMaskAggregate

/-!
# Literal nonnegative causal deletion measure on the original pair labels

The atom at a sixth-row pair is its unit mass minus the cardinality of
the actual full eleventh-row last-pair fibre. The unconditional actual
last-pair injection proves that this fibre has cardinality at most one.
The natural subtraction therefore has no truncation error.

The resulting finite positive measure is exactly the original full
weight minus the weight after deletion with the same original mask.
Finite additivity and monotonicity persist after summing over the actual
additive-prime receiver carrier.

SOURCE ONLY: this module and its two draft predecessors are uncompiled.
-/

namespace ImbalancedChen.P5CausalDeletionMeasure

open scoped BigOperators
open Classical
open P5SelectedMaskAggregate P5SelectedMaskTransport

noncomputable section

/-- Literal full eleventh support over one given last-pair label. -/
def fibre (n : ℕ) (A H D : ℝ) (t : ℕ × ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (chenY11FullTuples n A H D).filter (fun u => u.2 = t)

def fibreCount (n : ℕ) (A H D : ℝ) (t : ℕ × ℕ) : ℕ :=
  (fibre n A H D t).card

/-- An actual fibre is either absent or a singleton. -/
theorem fibreCount_le_one {n : ℕ} (hn : n ≠ 0) (A H D : ℝ)
    (t : ℕ × ℕ) : fibreCount n A H D t ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huFull, huLast⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvFull, hvLast⟩ := Finset.mem_filter.mp hv
  exact fullTuple_lastPair_injOn hn A H D huFull hvFull (huLast.trans hvLast.symm)

theorem fibreCount_eq_zero_of_not_mem {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (t : ℕ × ℕ) (ht : t ∉ chenY6Tuples n A H D) :
    fibreCount n A H D t = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨huFull, huLast⟩ := Finset.mem_filter.mp hu
  have hm := fullTuple_lastPair_mem hn huFull
  rw [huLast] at hm
  exact ht hm

/-- The fibre mass is dominated by the literal Y6 point indicator,
including labels outside Y6, rather than just by the constant one. -/
theorem fibreCount_le_indicator {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (t : ℕ × ℕ) :
    fibreCount n A H D t ≤ if t ∈ chenY6Tuples n A H D then 1 else 0 := by
  by_cases ht : t ∈ chenY6Tuples n A H D
  · simpa only [if_pos ht] using fibreCount_le_one hn A H D t
  · simp only [if_neg ht, fibreCount_eq_zero_of_not_mem hn A H D t ht, le_refl]

/-- Natural causal deletion atom on a literal pair label. -/
def atomNat (n : ℕ) (A H D : ℝ) (t : ℕ × ℕ) : ℕ :=
  (if t ∈ chenY6Tuples n A H D then 1 else 0) - fibreCount n A H D t

def atom (n : ℕ) (A H D : ℝ) (t : ℕ × ℕ) : ℝ :=
  (atomNat n A H D t : ℝ)

theorem atomNat_add_fibreCount {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (t : ℕ × ℕ) :
    atomNat n A H D t + fibreCount n A H D t =
      if t ∈ chenY6Tuples n A H D then 1 else 0 := by
  exact Nat.sub_add_cancel (fibreCount_le_indicator hn A H D t)

theorem atom_nonneg (n : ℕ) (A H D : ℝ) (t : ℕ × ℕ) :
    0 ≤ atom n A H D t := Nat.cast_nonneg _

/-- There is no truncation error in the natural difference. -/
theorem atom_eq_indicator_sub_fibre {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (t : ℕ × ℕ) :
    atom n A H D t = (if t ∈ chenY6Tuples n A H D then (1 : ℝ) else 0) -
      (fibreCount n A H D t : ℝ) := by
  unfold atom atomNat
  rw [Nat.cast_sub (fibreCount_le_indicator hn A H D t)]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero]

theorem atom_eq_zero_of_not_mem {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (t : ℕ × ℕ) (ht : t ∉ chenY6Tuples n A H D) :
    atom n A H D t = 0 := by
  rw [atom_eq_indicator_sub_fibre hn, if_neg ht,
    fibreCount_eq_zero_of_not_mem hn A H D t ht]
  norm_num

/-- Literal finite measure on the selected Y6 labels. -/
def deletionMass (n : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  mass (chenY6Tuples n A H D) (atom n A H D) E

theorem deletionMass_nonneg (n : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    0 ≤ deletionMass n A H D E := by
  exact mass_nonneg _ _ (fun t _ => atom_nonneg n A H D t) E

/-- Finite fibre disintegration on the actual receiver support. -/
theorem sum_fibreCount_selected {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ chenY6SelectedTuples n A H D E, fibreCount n A H D t) =
      chenY11Selected n A H D E := by
  have hmap : Set.MapsTo (fun u : (ℕ × ℕ) × (ℕ × ℕ) => u.2)
      (chenY11SelectedTuples n A H D E : Set ((ℕ × ℕ) × (ℕ × ℕ)))
      (chenY6SelectedTuples n A H D E : Set (ℕ × ℕ)) := by
    intro u hu
    obtain ⟨hfull, hE⟩ := mem_chenY11SelectedTuples.mp hu
    exact mem_chenY6SelectedTuples.mpr ⟨fullTuple_lastPair_mem hn hfull, hE⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  have hfibre : ∀ t ∈ chenY6SelectedTuples n A H D E,
      (chenY11SelectedTuples n A H D E).filter (fun u => u.2 = t) =
        fibre n A H D t := by
    intro t ht
    have hEt := (mem_chenY6SelectedTuples.mp ht).2
    ext u
    simp only [Finset.mem_filter, mem_chenY11SelectedTuples, fibre]
    constructor
    · rintro ⟨⟨hu, _⟩, heq⟩
      exact ⟨hu, heq⟩
    · rintro ⟨hu, heq⟩
      exact ⟨⟨hu, heq.symm ▸ hEt⟩, heq⟩
  calc
    _ = ∑ t ∈ chenY6SelectedTuples n A H D E,
        ((chenY11SelectedTuples n A H D E).filter (fun u => u.2 = t)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hfibre t ht]
      rfl
    _ = _ := hcard.symm

/-- The selected sixth count minus the selected eleventh count is the
sum of the nonnegative literal pair atoms. -/
theorem deletionMass_eq_selected_difference {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    deletionMass n A H D E = (chenY6Selected n A H D E : ℝ) -
      (chenY11Selected n A H D E : ℝ) := by
  have hsum : (∑ t ∈ chenY6SelectedTuples n A H D E,
      (fibreCount n A H D t : ℝ)) = (chenY11Selected n A H D E : ℝ) := by
    exact_mod_cast sum_fibreCount_selected hn A H D E
  have hones : (∑ _t ∈ chenY6SelectedTuples n A H D E, (1 : ℝ)) =
      (chenY6Selected n A H D E : ℝ) := by
    simp only [chenY6Selected, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  change (∑ t ∈ chenY6SelectedTuples n A H D E, atom n A H D t) = _
  calc
    _ = ∑ t ∈ chenY6SelectedTuples n A H D E,
        (1 - (fibreCount n A H D t : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [atom_eq_indicator_sub_fibre hn, if_pos (mem_chenY6SelectedTuples.mp ht).1]
    _ = _ := by rw [Finset.sum_sub_distrib, hones, hsum]

/-- Literal full weight minus masked weight is this positive measure. -/
theorem fullWeight_sub_pairedWeight {n : ℕ} (hn : n ≠ 0)
    (N A H D C : ℝ) (E : ℕ × ℕ → Prop) :
    chenElevenWeight n N A H D C - chenPairedElevenWeight n N A H D C E =
      deletionMass n A H D E := by
  rw [deletionMass_eq_selected_difference hn]
  unfold chenPairedElevenWeight
  ring

theorem deletionMass_mono (n : ℕ) (A H D : ℝ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) : deletionMass n A H D E ≤ deletionMass n A H D F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨hmem, hE⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨hmem, hEF t hE⟩
  · intro t ht hnot
    exact atom_nonneg n A H D t

/-- Inclusion-exclusion, hence finite additivity, on the literal pair
predicate algebra. -/
theorem deletionMass_union_add_inter (n : ℕ) (A H D : ℝ)
    (E F : ℕ × ℕ → Prop) :
    deletionMass n A H D (fun t => E t ∨ F t) +
      deletionMass n A H D (fun t => E t ∧ F t) =
      deletionMass n A H D E + deletionMass n A H D F := by
  unfold deletionMass mass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hE : E t <;> by_cases hF : F t <;> simp [hE, hF]

theorem deletionMass_empty (n : ℕ) (A H D : ℝ) :
    deletionMass n A H D (fun _ => False) = 0 := by
  simp [deletionMass, mass]

theorem deletionMass_add_disjoint (n : ℕ) (A H D : ℝ)
    (E F : ℕ × ℕ → Prop) (hdisj : ∀ t, ¬ (E t ∧ F t)) :
    deletionMass n A H D (fun t => E t ∨ F t) =
      deletionMass n A H D E + deletionMass n A H D F := by
  have hempty : (fun t => E t ∧ F t) = (fun _ => False) := by
    funext t
    exact propext ⟨hdisj t, False.elim⟩
  have h := deletionMass_union_add_inter n A H D E F
  rw [hempty, deletionMass_empty, add_zero] at h
  exact h

/-- Sum of the actual receiver measures at the original current cutoffs. -/
def currentDeletionMass (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    deletionMass (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)) E

theorem currentDeletionMass_nonneg (N : ℕ) (E : ℕ × ℕ → Prop) :
    0 ≤ currentDeletionMass N E := by
  exact Finset.sum_nonneg (fun _ _ => deletionMass_nonneg _ _ _ _ E)

theorem currentDeletionMass_empty (N : ℕ) :
    currentDeletionMass N (fun _ => False) = 0 := by
  simp only [currentDeletionMass, deletionMass_empty, Finset.sum_const_zero]

theorem currentDeletionMass_mono (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) : currentDeletionMass N E ≤ currentDeletionMass N F := by
  apply Finset.sum_le_sum
  intro P hP
  exact deletionMass_mono _ _ _ _ E F hEF

theorem currentDeletionMass_add_disjoint (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hdisj : ∀ t, ¬ (E t ∧ F t)) :
    currentDeletionMass N (fun t => E t ∨ F t) =
      currentDeletionMass N E + currentDeletionMass N F := by
  unfold currentDeletionMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  exact deletionMass_add_disjoint _ _ _ _ E F hdisj

/-- The original unmasked real full weight summed over actual receivers. -/
def currentFullPrimeSum (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N, currentChenElevenWeight (N - P) (N : ℝ)

theorem currentFullPrimeSum_sub_pairedPrimeSum (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentFullPrimeSum N - currentChenPairedPrimeSum N E = currentDeletionMass N E := by
  unfold currentFullPrimeSum currentChenPairedPrimeSum currentDeletionMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
  exact fullWeight_sub_pairedWeight (by omega : N - P ≠ 0) (N : ℝ) _ _ _ _ E

theorem pairedPrimeSum_change_eq_measure_change (N : ℕ)
    (E F : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E - currentChenPairedPrimeSum N F =
      currentDeletionMass N F - currentDeletionMass N E := by
  have hE := currentFullPrimeSum_sub_pairedPrimeSum N E
  have hF := currentFullPrimeSum_sub_pairedPrimeSum N F
  linarith only [hE, hF]

/-- The same positive measure can use the actual all-false-mask sum as
its base; this is the literal paired-deletion semantics of the ledger. -/
theorem unmaskedPairedPrimeSum_sub_pairedPrimeSum (N : ℕ)
    (E : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N (fun _ => False) - currentChenPairedPrimeSum N E =
      currentDeletionMass N E := by
  rw [pairedPrimeSum_change_eq_measure_change, currentDeletionMass_empty, sub_zero]

end

end ImbalancedChen.P5CausalDeletionMeasure
