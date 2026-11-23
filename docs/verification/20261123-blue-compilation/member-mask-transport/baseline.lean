import ImbalancedChen.CurrentChenUpsilon6ProductRestriction

/-!
# Exact finite transport of the common sixth/eleventh mask

The original sixth and eleventh quotient supports are used literally.
The additional buffered product gate is retained only on the positive
sixth row. All statements are finite, including squareful receivers.
No distribution theorem or assumed mask-error estimate is used.

SOURCE ONLY: this candidate has not been compiled or kernel checked.
-/

namespace ImbalancedChen.P5SelectedMaskTransport

open scoped BigOperators
open Classical

noncomputable section

/-- Weighted selection on the original labelled support. -/
def mass {α : Type*} (s : Finset α) (w : α → ℝ) (E : α → Prop) : ℝ :=
  ∑ t ∈ s.filter E, w t

/-- The same directed mask change will be used on both paired rows. -/
def change {α : Type*} (E F : α → Prop) (t : α) : Prop := F t ∧ ¬ E t

/-- Mask disagreement, without forgetting tuple labels. -/
def disagreement {α : Type*} (E F : α → Prop) (t : α) : Prop :=
  change E F t ∨ change F E t

theorem mass_nonneg {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ t ∈ s, 0 ≤ w t) (E : α → Prop) : 0 ≤ mass s w E := by
  apply Finset.sum_nonneg
  intro t ht
  exact hw t (Finset.mem_filter.mp ht).1

/-- Exact overlap cancellation; no monotonicity of a signed ledger is
assumed. -/
theorem mass_change_identity {α : Type*} (s : Finset α) (w : α → ℝ)
    (E F : α → Prop) :
    mass s w E + mass s w (change E F) =
      mass s w F + mass s w (change F E) := by
  unfold mass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hE : E t <;> by_cases hF : F t <;> simp [change, hE, hF]

/-- With the deletion convention in the original ledger, enlarging E
removes exactly the F\E fibres and restores exactly the E\F fibres. -/
theorem mass_compl_sub {α : Type*} (s : Finset α) (w : α → ℝ)
    (E F : α → Prop) :
    mass s w (fun t => ¬ E t) - mass s w (fun t => ¬ F t) =
      mass s w (change E F) - mass s w (change F E) := by
  have h := mass_change_identity s w E F
  have hE := Finset.sum_filter_add_sum_filter_not s E w
  have hF := Finset.sum_filter_add_sum_filter_not s F w
  change mass s w E + mass s w (fun t => ¬ E t) = _ at hE
  change mass s w F + mass s w (fun t => ¬ F t) = _ at hF
  linarith only [h, hE, hF]

theorem mass_disagreement {α : Type*} (s : Finset α) (w : α → ℝ)
    (E F : α → Prop) :
    mass s w (disagreement E F) =
      mass s w (change E F) + mass s w (change F E) := by
  unfold mass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hE : E t <;> by_cases hF : F t <;>
    simp [disagreement, change, hE, hF]

/-- An unconditional finite symmetric-difference bound, paid only by
actual nonnegative weights on the disagreement region. -/
theorem abs_mass_compl_sub_le {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ t ∈ s, 0 ≤ w t) (E F : α → Prop) :
    |mass s w (fun t => ¬ E t) - mass s w (fun t => ¬ F t)| ≤
      mass s w (disagreement E F) := by
  rw [mass_compl_sub, mass_disagreement]
  have hEF := mass_nonneg s w hw (change E F)
  have hFE := mass_nonneg s w hw (change F E)
  apply abs_le.mpr
  constructor <;> linarith only [hEF, hFE]

theorem mass_eq_zero_of_false {α : Type*} (s : Finset α) (w : α → ℝ)
    (E : α → Prop) (hE : ∀ t ∈ s, ¬ E t) : mass s w E = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  exact False.elim (hE t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2)

/-- Pointwise causal identity on literal receiver supports. This identity
itself needs no squarefreeness; only the subsequent sign uses injection. -/
theorem pairedWeight_mask_change (n : ℕ) (N A H D C : ℝ)
    (E F : ℕ × ℕ → Prop) :
    chenPairedElevenWeight n N A H D C E -
      chenPairedElevenWeight n N A H D C F =
      ((chenY6Selected n A H D (change E F) : ℝ) -
        (chenY11Selected n A H D (change E F) : ℝ)) -
      ((chenY6Selected n A H D (change F E) : ℝ) -
        (chenY11Selected n A H D (change F E) : ℝ)) := by
  have h6card : ∀ G : ℕ × ℕ → Prop,
      mass (chenY6Tuples n A H D) (fun _ => 1) G =
        (chenY6Selected n A H D G : ℝ) := by
    intro G
    simp only [mass, chenY6Selected, chenY6SelectedTuples,
      Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  have h11card : ∀ G : ℕ × ℕ → Prop,
      mass (chenY11FullTuples n A H D) (fun _ => 1) (fun t => G t.2) =
        (chenY11Selected n A H D G : ℝ) := by
    intro G
    simp only [mass, chenY11Selected, chenY11SelectedTuples,
      Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  have h6 := mass_change_identity (chenY6Tuples n A H D) (fun _ => 1) E F
  have h11 := mass_change_identity (chenY11FullTuples n A H D) (fun _ => 1)
    (fun t => E t.2) (fun t => F t.2)
  simp only [h6card] at h6
  change mass _ _ (fun t : (ℕ × ℕ) × (ℕ × ℕ) => E t.2) +
      mass _ _ (fun t : (ℕ × ℕ) × (ℕ × ℕ) => change E F t.2) =
    mass _ _ (fun t : (ℕ × ℕ) × (ℕ × ℕ) => F t.2) +
      mass _ _ (fun t : (ℕ × ℕ) × (ℕ × ℕ) => change F E t.2) at h11
  simp only [h11card] at h11
  unfold chenPairedElevenWeight
  linarith only [h6, h11]

/-- Enlarging the deleted mask decreases the paired weight on every
squarefree receiver, by the proved actual last-pair injection. -/
theorem pairedWeight_antitone_mask {n : ℕ} (hn : Squarefree n)
    (N A H D C : ℝ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) :
    chenPairedElevenWeight n N A H D C F ≤
      chenPairedElevenWeight n N A H D C E := by
  have hempty : change F E = (fun _ => False) := by
    funext t
    apply propext
    constructor
    · intro ht
      exact ht.2 (hEF t ht.1)
    · exact False.elim
  have hz6 : chenY6Selected n A H D (change F E) = 0 := by
    simp [hempty, chenY6Selected, chenY6SelectedTuples]
  have hz11 : chenY11Selected n A H D (change F E) = 0 := by
    simp [hempty, chenY11Selected, chenY11SelectedTuples]
  have hsign : (chenY11Selected n A H D (change E F) : ℝ) ≤
      (chenY6Selected n A H D (change E F) : ℝ) := by
    exact_mod_cast chenY11Selected_le_chenY6Selected hn (change E F)
  have hid := pairedWeight_mask_change n N A H D C E F
  rw [hz6, hz11] at hid
  push_cast at hid
  linarith only [hsign, hid]

abbrev sixthSupport (N : ℕ) : Finset (ℕ × ℕ) :=
  chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))

abbrev eleventhSupport (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  chenY11FullPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))

abbrev sixthWeight (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
    ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)

abbrev eleventhWeight (N : ℕ) (t : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
    (t.1.2 : ℝ)).card : ℝ)

def sixthMass (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  mass (sixthSupport N) (sixthWeight N) E

def eleventhMass (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  mass (eleventhSupport N) (eleventhWeight N) (fun t => E t.2)

/-- The product boundary is precisely the corrected Runbo boundary with
its fixed eta buffer; it is independent of the chosen common mask. -/
def retainedSupport (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  (sixthSupport N).filter fun t => ((t.1 * t.2 : ℕ) : ℝ) ≤
    (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta)

def retainedMass (N : ℕ) (eta : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  mass (retainedSupport N eta) (sixthWeight N) E

theorem upsilon6_eq_compl_mass (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6 N E = sixthMass N (fun t => ¬ E t) := by
  exact currentChenUpsilon6_eq_siftedQuotientPrimeSource N E

theorem upsilon11_eq_compl_mass (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E = eleventhMass N (fun t => ¬ E t) := by
  exact currentChenUpsilon11_eq_siftedQuotientPrimeSource N E

theorem retained_eq_compl_mass (N : ℕ) (eta : ℝ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6Retained N E eta = retainedMass N eta (fun t => ¬ E t) := by
  unfold currentChenUpsilon6Retained currentChenUpsilon6RetainedSelector
    retainedMass retainedSupport mass
  simp only [Finset.filter_filter, and_comm]

theorem upsilon6_mask_change (N : ℕ) (E F : ℕ × ℕ → Prop) :
    currentChenUpsilon6 N E - currentChenUpsilon6 N F =
      sixthMass N (change E F) - sixthMass N (change F E) := by
  rw [upsilon6_eq_compl_mass, upsilon6_eq_compl_mass]
  exact mass_compl_sub _ _ E F

/-- The last-pair pullback uses the identical E and F used in row six;
all four labels and the second-prime roughness cutoff survive. -/
theorem upsilon11_mask_change (N : ℕ) (E F : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E - currentChenUpsilon11 N F =
      eleventhMass N (change E F) - eleventhMass N (change F E) := by
  rw [upsilon11_eq_compl_mass, upsilon11_eq_compl_mass]
  exact mass_compl_sub _ _ (fun t => E t.2) (fun t => F t.2)

theorem retained_mask_change (N : ℕ) (eta : ℝ) (E F : ℕ × ℕ → Prop) :
    currentChenUpsilon6Retained N E eta - currentChenUpsilon6Retained N F eta =
      retainedMass N eta (change E F) - retainedMass N eta (change F E) := by
  rw [retained_eq_compl_mass, retained_eq_compl_mass]
  exact mass_compl_sub _ _ E F

/-- Exact causal change of the original paired ledger. Every mask-free
term cancels; the two directed changes retain the same pair region. -/
theorem pairedPrimeSum_mask_change (N : ℕ) (E F : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E - currentChenPairedPrimeSum N F =
      (sixthMass N (change E F) - eleventhMass N (change E F)) -
        (sixthMass N (change F E) - eleventhMass N (change F E)) := by
  have h6 := upsilon6_mask_change N E F
  have h11 := upsilon11_mask_change N E F
  rw [currentChenPairedPrimeSum_eq_upsilon, currentChenPairedPrimeSum_eq_upsilon]
  linarith only [h6, h11]

/-- Exact causal change after restricting the positive row. The negative
eleventh row remains the entire original row with the same mask. -/
theorem retained_pair_mask_change (N : ℕ) (eta : ℝ) (E F : ℕ × ℕ → Prop) :
    (currentChenUpsilon6Retained N E eta - currentChenUpsilon11 N E) -
      (currentChenUpsilon6Retained N F eta - currentChenUpsilon11 N F) =
      (retainedMass N eta (change E F) - eleventhMass N (change E F)) -
        (retainedMass N eta (change F E) - eleventhMass N (change F E)) := by
  have h6 := retained_mask_change N eta E F
  have h11 := upsilon11_mask_change N E F
  linarith only [h6, h11]

theorem abs_upsilon6_mask_change_le (N : ℕ) (E F : ℕ × ℕ → Prop) :
    |currentChenUpsilon6 N E - currentChenUpsilon6 N F| ≤
      sixthMass N (disagreement E F) := by
  rw [upsilon6_eq_compl_mass, upsilon6_eq_compl_mass]
  exact abs_mass_compl_sub_le _ _ (fun _ _ => Nat.cast_nonneg _) E F

theorem abs_upsilon11_mask_change_le (N : ℕ) (E F : ℕ × ℕ → Prop) :
    |currentChenUpsilon11 N E - currentChenUpsilon11 N F| ≤
      eleventhMass N (disagreement E F) := by
  rw [upsilon11_eq_compl_mass, upsilon11_eq_compl_mass]
  exact abs_mass_compl_sub_le _ _ (fun _ _ => Nat.cast_nonneg _)
    (fun t => E t.2) (fun t => F t.2)

theorem abs_retained_mask_change_le (N : ℕ) (eta : ℝ)
    (E F : ℕ × ℕ → Prop) :
    |currentChenUpsilon6Retained N E eta - currentChenUpsilon6Retained N F eta| ≤
      retainedMass N eta (disagreement E F) := by
  rw [retained_eq_compl_mass, retained_eq_compl_mass]
  exact abs_mass_compl_sub_le _ _ (fun _ _ => Nat.cast_nonneg _) E F

/-- A finite replacement of an approximate mask by the original mask
has an explicit error measured on literal original quotient supports. -/
theorem abs_pairedPrimeSum_mask_change_le (N : ℕ) (E F : ℕ × ℕ → Prop) :
    |currentChenPairedPrimeSum N E - currentChenPairedPrimeSum N F| ≤
      sixthMass N (disagreement E F) + eleventhMass N (disagreement E F) := by
  obtain ⟨h6lo, h6hi⟩ := abs_le.mp (abs_upsilon6_mask_change_le N E F)
  obtain ⟨h11lo, h11hi⟩ := abs_le.mp (abs_upsilon11_mask_change_le N E F)
  rw [currentChenPairedPrimeSum_eq_upsilon, currentChenPairedPrimeSum_eq_upsilon]
  apply abs_le.mpr
  constructor <;> linarith only [h6lo, h6hi, h11lo, h11hi]

/-- The corresponding bound for the corrected retained positive row and
the complete eleventh row. The product gate has not migrated to row 11. -/
theorem abs_retained_pair_mask_change_le (N : ℕ) (eta : ℝ)
    (E F : ℕ × ℕ → Prop) :
    |(currentChenUpsilon6Retained N E eta - currentChenUpsilon11 N E) -
      (currentChenUpsilon6Retained N F eta - currentChenUpsilon11 N F)| ≤
      retainedMass N eta (disagreement E F) + eleventhMass N (disagreement E F) := by
  obtain ⟨h6lo, h6hi⟩ := abs_le.mp (abs_retained_mask_change_le N eta E F)
  obtain ⟨h11lo, h11hi⟩ := abs_le.mp (abs_upsilon11_mask_change_le N E F)
  apply abs_le.mpr
  constructor <;> linarith only [h6lo, h6hi, h11lo, h11hi]

end

end ImbalancedChen.P5SelectedMaskTransport
