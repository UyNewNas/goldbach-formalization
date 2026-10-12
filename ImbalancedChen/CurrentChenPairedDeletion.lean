import ImbalancedChen.CurrentChenPointwise

/-!
# Literal paired deletion for the current eleven-term Chen weight

The same predicate `E` selects a pair in `Y6` and the last two prime values
in the full four-prime `Y11`. In the manuscript this predicate is the
pullback of the union of the selected rectangles under
`(p, q) ↦ (log_N q, log_N p)`. No property of the rectangles is needed for
the finite injection.

The map sends an actual quotient tuple to its last pair. Its first pair is
uniquely determined by the receiver, because quotient roughness makes it
the smallest two prime factors. The target quotient is proved rough from
these prime factors; neither its membership nor injectivity is assumed.
All endpoint conventions remain those of the existing literal tuple sets.
-/

namespace ImbalancedChen

open scoped ArithmeticFunction.Omega

noncomputable section

/-- The literal selected `Y6` pairs. The predicate takes the prime values in
increasing order, before their logarithmic-coordinate pullback. -/
def chenY6SelectedTuples (n : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) : Finset (ℕ × ℕ) := by
  classical
  exact (chenY6Tuples n A H D).filter E

/-- The literal selected full `Y11` tuples, with exactly the same predicate
applied to the last two prime values. -/
def chenY11SelectedTuples (n : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact (chenY11FullTuples n A H D).filter fun t => E t.2

def chenY6Selected (n : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) : ℕ :=
  (chenY6SelectedTuples n A H D E).card

def chenY11Selected (n : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) : ℕ :=
  (chenY11SelectedTuples n A H D E).card

@[simp] theorem mem_chenY6SelectedTuples {n : ℕ} {A H D : ℝ}
    {E : ℕ × ℕ → Prop} {t : ℕ × ℕ} :
    t ∈ chenY6SelectedTuples n A H D E ↔ t ∈ chenY6Tuples n A H D ∧ E t := by
  classical
  simp only [chenY6SelectedTuples, Finset.mem_filter]

@[simp] theorem mem_chenY11SelectedTuples {n : ℕ} {A H D : ℝ}
    {E : ℕ × ℕ → Prop} {t : (ℕ × ℕ) × (ℕ × ℕ)} :
    t ∈ chenY11SelectedTuples n A H D E ↔
      t ∈ chenY11FullTuples n A H D ∧ E t.2 := by
  classical
  simp only [chenY11SelectedTuples, Finset.mem_filter]

/-- A smallest pair starting at `A` forces roughness of the entire actual
receiver. This supplies roughness after removing the last pair as well. -/
theorem ChenSmallestTwo.rough_of_first_ge {n p₁ p₂ : ℕ} {A : ℝ}
    (hsmall : ChenSmallestTwo n p₁ p₂) (hA : A ≤ (p₁ : ℝ)) :
    ChenPrimeRough A n := by
  intro q hq hqd
  rcases hsmall.least_other q hq hqd with rfl | hle
  · exact hA
  · have hp₁₂ : (p₁ : ℝ) ≤ (p₂ : ℝ) := by
      exact_mod_cast hsmall.increasing.le
    have hp₂q : (p₂ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
    exact hA.trans (hp₁₂.trans hp₂q)

/-- The last pair of an actual full four-prime quotient tuple contributes
to `Y6`. In particular, its remaining quotient is actually `A`-rough. -/
theorem chenY11Full_lastPair_mem {n : ℕ} {A H D : ℝ}
    (hn : Squarefree n) {t : (ℕ × ℕ) × (ℕ × ℕ)}
    (ht : t ∈ chenY11FullTuples n A H D) :
    t.2 ∈ chenY6Tuples n A H D := by
  rcases t with ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩
  obtain ⟨hsmall, h₃, h₄, hA, h₂₃, h₃H, hH₄, h₄D⟩ :=
    (mem_chenY11FullTuples_iff_smallestTwo hn).mp ht
  have hrough : ChenPrimeRough A n := hsmall.rough_of_first_ge hA
  have h₃₄ : p₃ < p₄ := by exact_mod_cast (lt_of_lt_of_le h₃H hH₄)
  exact (mem_chenY6Tuples_iff hn.ne_zero).mpr
    ⟨h₃.1, h₄.1, hrough p₃ h₃.1 h₃.2, h₃H, hH₄, h₄D,
      chenQuotient_of_rough hrough
        (chen_two_prime_product_dvd h₃.1 h₄.1 h₃₄ h₃.2 h₄.2)⟩

/-- The actual first two coordinates are unique for each receiver. Hence
projection to the last pair loses no multiplicity. -/
theorem chenY11Full_lastPair_injOn {n : ℕ} {A H D : ℝ}
    (hn : Squarefree n) :
    Set.InjOn (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2)
      (chenY11FullTuples n A H D : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  rintro ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩ hp ⟨⟨q₁, q₂⟩, ⟨q₃, q₄⟩⟩ hq hlast
  have hsmallp := ((mem_chenY11FullTuples_iff_smallestTwo hn).mp hp).1
  have hsmallq := ((mem_chenY11FullTuples_iff_smallestTwo hn).mp hq).1
  obtain ⟨rfl, rfl⟩ := hsmallp.unique hsmallq
  exact Prod.ext rfl hlast

/-- Selection uses the same pair predicate on both sides of the injection. -/
theorem chenY11Selected_lastPair_mem {n : ℕ} {A H D : ℝ}
    {E : ℕ × ℕ → Prop} (hn : Squarefree n)
    {t : (ℕ × ℕ) × (ℕ × ℕ)} (ht : t ∈ chenY11SelectedTuples n A H D E) :
    t.2 ∈ chenY6SelectedTuples n A H D E := by
  obtain ⟨ht, hE⟩ := mem_chenY11SelectedTuples.mp ht
  exact mem_chenY6SelectedTuples.mpr ⟨chenY11Full_lastPair_mem hn ht, hE⟩

theorem chenY11Selected_lastPair_injOn {n : ℕ} {A H D : ℝ}
    {E : ℕ × ℕ → Prop} (hn : Squarefree n) :
    Set.InjOn (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2)
      (chenY11SelectedTuples n A H D E : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  intro t ht u hu heq
  exact chenY11Full_lastPair_injOn hn
    (mem_chenY11SelectedTuples.mp ht).1 (mem_chenY11SelectedTuples.mp hu).1 heq

/-- The manuscript's paired-injection inequality for any selected pair
region, proved on the actual quotient supports. No size bound is needed. -/
theorem chenY11Selected_le_chenY6Selected {n : ℕ} {A H D : ℝ}
    (hn : Squarefree n) (E : ℕ × ℕ → Prop) :
    chenY11Selected n A H D E ≤ chenY6Selected n A H D E := by
  classical
  unfold chenY11Selected chenY6Selected
  have himage :
      ((chenY11SelectedTuples n A H D E).image
        (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2)) ⊆ chenY6SelectedTuples n A H D E := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact chenY11Selected_lastPair_mem hn hu
  calc
    (chenY11SelectedTuples n A H D E).card =
        ((chenY11SelectedTuples n A H D E).image
          (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2)).card :=
      (Finset.card_image_iff.mpr (chenY11Selected_lastPair_injOn hn)).symm
    _ ≤ (chenY6SelectedTuples n A H D E).card := Finset.card_le_card himage

/-- Selected cardinalities cannot exceed the full cardinalities; these
bounds do not require squarefreeness. -/
theorem chenY6Selected_le_full (n : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    chenY6Selected n A H D E ≤ chenY6 n A H D := by
  classical
  exact Finset.card_filter_le _ _

theorem chenY11Selected_le_full (n : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    chenY11Selected n A H D E ≤ chenY11Full n A H D := by
  classical
  exact Finset.card_filter_le _ _

/-- Literal paired deletion in the real-valued eleven-term weight. -/
def chenPairedElevenWeight (n : ℕ) (N A H D C : ℝ)
    (E : ℕ × ℕ → Prop) : ℝ :=
  chenElevenWeight n N A H D C - (chenY6Selected n A H D E : ℝ) +
    (chenY11Selected n A H D E : ℝ)

/-- Paired deletion preserves every already-proved pointwise upper bound. -/
theorem chenPairedElevenWeight_le_weight {n : ℕ} (N A H D C : ℝ)
    (hn : Squarefree n) (E : ℕ × ℕ → Prop) :
    chenPairedElevenWeight n N A H D C E ≤ chenElevenWeight n N A H D C := by
  have hcard : (chenY11Selected n A H D E : ℝ) ≤ (chenY6Selected n A H D E : ℝ) := by
    exact_mod_cast chenY11Selected_le_chenY6Selected (A := A) (H := H) (D := D) hn E
  unfold chenPairedElevenWeight
  linarith

/-- The current manuscript's literal paired weight at its exact cutoffs. -/
def currentChenPairedWeight (n : ℕ) (N : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  chenPairedElevenWeight n N (N ^ (417 / 5000 : ℝ)) (N ^ (19 / 125 : ℝ))
    (N ^ (59 / 250 : ℝ)) (N ^ (1 / 3 : ℝ)) E

theorem currentChenPairedWeight_le_weight {n : ℕ} (N : ℝ)
    (hn : Squarefree n) (E : ℕ × ℕ → Prop) :
    currentChenPairedWeight n N E ≤ currentChenElevenWeight n N :=
  chenPairedElevenWeight_le_weight N _ _ _ _ hn E

/-- Paired deletion retains the current source inequality for every
squarefree receiver up to `N`, including one and without a lower size band. -/
theorem currentChenPairedWeight_le_four_indicator {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (hn : Squarefree n) (hnN : (n : ℝ) ≤ N)
    (E : ℕ × ℕ → Prop) :
    currentChenPairedWeight n N E ≤ if Ω n ≤ 2 then 4 else 0 :=
  (currentChenPairedWeight_le_weight N hn E).trans
    (currentChenElevenWeight_le_four_indicator hN hn hnN)

@[simp] theorem chenY6Selected_one (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    chenY6Selected 1 A H D E = 0 := by
  classical
  simp [chenY6Selected, chenY6SelectedTuples, chenY6Tuples, chenInitialPairCarrier]

@[simp] theorem chenY11Selected_one (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    chenY11Selected 1 A H D E = 0 := by
  classical
  simp [chenY11Selected, chenY11SelectedTuples, chenY11FullTuples, chenFourPrimeCarrier]

@[simp] theorem chenPairedElevenWeight_one (N A H D C : ℝ) (E : ℕ × ℕ → Prop) :
    chenPairedElevenWeight 1 N A H D C E = 4 := by
  simp [chenPairedElevenWeight]

@[simp] theorem currentChenPairedWeight_one (N : ℝ) (E : ℕ × ℕ → Prop) :
    currentChenPairedWeight 1 N E = 4 := by
  simp [currentChenPairedWeight]

end

end ImbalancedChen
