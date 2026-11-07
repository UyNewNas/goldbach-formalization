import ImbalancedChen.CurrentChenP5SelectedMaskTransport

/-!
# Uniform common-mask antitonicity on the actual prime carrier

The forward four-quotient-to-smallest-pair implication uses no
squarefreeness. The squarefree premise in the older iff theorem is used
only for its converse. Extracting the forward proof makes the last-pair
injection available for every nonzero receiver, hence makes the common-
mask excess nonpositive even on the actual squareful exceptional carrier.

We also supply the conventional squareful-card correction and prove its
normalized decay from the actual SummedBridge cardinal bound. No lower
mean hypothesis, numerical certificate, or abstract exceptional-error
bound is introduced.

SOURCE ONLY: both this module and its draft predecessor are uncompiled.
-/

namespace ImbalancedChen.P5SelectedMaskAggregate

open scoped BigOperators
open Classical Filter Topology
open P5SelectedMaskTransport

noncomputable section

/-- The unconditional forward half of the original four-prime iff. -/
theorem smallestTwo_of_four_quotient {n p₁ p₂ p₃ p₄ : ℕ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂)
    (h₃ : Nat.Prime p₃) (h₄ : Nat.Prime p₄)
    (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃) (h₃₄ : p₃ < p₄)
    (hQ : ChenQuotient (p₁ * p₂ * p₃ * p₄) (p₂ : ℝ) n) :
    ChenSmallestTwo n p₁ p₂ := by
  have hd₁ : p₁ ∣ p₁ * p₂ * p₃ * p₄ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃) p₄
  have hd₂ : p₂ ∣ p₁ * p₂ * p₃ * p₄ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃) p₄
  have hprod : (p₁ * p₂ * p₃ * p₄) * (n / (p₁ * p₂ * p₃ * p₄)) = n :=
    Nat.mul_div_cancel' hQ.1
  refine ⟨h₁, h₂, hd₁.trans hQ.1, hd₂.trans hQ.1, h₁₂, ?_⟩
  intro q hq hqn
  have hqprod : q ∣ (p₁ * p₂ * p₃ * p₄) * (n / (p₁ * p₂ * p₃ * p₄)) := by
    rwa [hprod]
  rcases hq.dvd_mul.mp hqprod with hprefix | hquotient
  · have hcases : q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q = p₄ := by
      simpa only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq h₁,
        Nat.prime_dvd_prime_iff_eq hq h₂, Nat.prime_dvd_prime_iff_eq hq h₃,
        Nat.prime_dvd_prime_iff_eq hq h₄, or_assoc] using hprefix
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr le_rfl
    · exact Or.inr h₂₃.le
    · exact Or.inr (lt_trans h₂₃ h₃₄).le
  · exact Or.inr (by exact_mod_cast hQ.2 q hq hquotient)

theorem fullTuple_smallestTwo {n : ℕ} (hn : n ≠ 0) {A H D : ℝ}
    {t : (ℕ × ℕ) × (ℕ × ℕ)} (ht : t ∈ chenY11FullTuples n A H D) :
    ChenSmallestTwo n t.1.1 t.1.2 := by
  rcases t with ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩
  obtain ⟨hc, hA, h₁₂, h₂₃, h₃H, hH₄, h₄D, hQ⟩ := Finset.mem_filter.mp ht
  obtain ⟨⟨h₁, hd₁⟩, ⟨h₂, hd₂⟩, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩⟩ :=
    (mem_chenFourPrimeCarrier hn).mp hc
  have h₃₄ : p₃ < p₄ := by exact_mod_cast (lt_of_lt_of_le h₃H hH₄)
  exact smallestTwo_of_four_quotient h₁ h₂ h₃ h₄ h₁₂ h₂₃ h₃₄ hQ

/-- Whole-receiver roughness and the last-pair quotient are valid on
squareful receivers too. -/
theorem fullTuple_lastPair_mem {n : ℕ} (hn : n ≠ 0) {A H D : ℝ}
    {t : (ℕ × ℕ) × (ℕ × ℕ)} (ht : t ∈ chenY11FullTuples n A H D) :
    t.2 ∈ chenY6Tuples n A H D := by
  have hsmall := fullTuple_smallestTwo hn ht
  rcases t with ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩
  obtain ⟨hc, hA, h₁₂, h₂₃, h₃H, hH₄, h₄D, hQ⟩ := Finset.mem_filter.mp ht
  obtain ⟨⟨h₁, hd₁⟩, ⟨h₂, hd₂⟩, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩⟩ :=
    (mem_chenFourPrimeCarrier hn).mp hc
  have hrough : ChenPrimeRough A n := hsmall.rough_of_first_ge hA
  have h₃₄ : p₃ < p₄ := by exact_mod_cast (lt_of_lt_of_le h₃H hH₄)
  exact (mem_chenY6Tuples_iff hn).mpr
    ⟨h₃, h₄, hrough p₃ h₃ hd₃, h₃H, hH₄, h₄D,
      chenQuotient_of_rough hrough
        (chen_two_prime_product_dvd h₃ h₄ h₃₄ hd₃ hd₄)⟩

theorem fullTuple_lastPair_injOn {n : ℕ} (hn : n ≠ 0) (A H D : ℝ) :
    Set.InjOn (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2)
      (chenY11FullTuples n A H D : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  rintro ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩ hp ⟨⟨q₁, q₂⟩, ⟨q₃, q₄⟩⟩ hq hlast
  have hsmallp := fullTuple_smallestTwo hn hp
  have hsmallq := fullTuple_smallestTwo hn hq
  obtain ⟨rfl, rfl⟩ := hsmallp.unique hsmallq
  exact Prod.ext rfl hlast

/-- The same original pair mask is preserved by the unconditional
injection; no new support or squarefree surrogate is used. -/
theorem selected11_le_selected6 {n : ℕ} (hn : n ≠ 0)
    (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    chenY11Selected n A H D E ≤ chenY6Selected n A H D E := by
  have hmem : ∀ t ∈ chenY11SelectedTuples n A H D E,
      t.2 ∈ chenY6SelectedTuples n A H D E := by
    intro t ht
    obtain ⟨hfull, hE⟩ := mem_chenY11SelectedTuples.mp ht
    exact mem_chenY6SelectedTuples.mpr ⟨fullTuple_lastPair_mem hn hfull, hE⟩
  have hinj : Set.InjOn (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2)
      (chenY11SelectedTuples n A H D E : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    intro t ht u hu heq
    exact fullTuple_lastPair_injOn hn A H D
      (mem_chenY11SelectedTuples.mp ht).1 (mem_chenY11SelectedTuples.mp hu).1 heq
  unfold chenY11Selected chenY6Selected
  exact Finset.card_le_card_of_injOn (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2) hmem hinj

theorem pairedWeight_antitone {n : ℕ} (hn : n ≠ 0)
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
    exact_mod_cast selected11_le_selected6 hn A H D (change E F)
  have hid := pairedWeight_mask_change n N A H D C E F
  rw [hz6, hz11] at hid
  push_cast at hid
  linarith only [hsign, hid]

theorem currentWeight_antitone {n : ℕ} (hn : n ≠ 0) (N : ℝ)
    (E F : ℕ × ℕ → Prop) (hEF : ∀ t, E t → F t) :
    currentChenPairedWeight n N F ≤ currentChenPairedWeight n N E := by
  exact pairedWeight_antitone hn N _ _ _ _ E F hEF

/-- Every actual additive receiver is nonzero, hence the aggregate is
exactly antitone, uniformly over all masks, for every N. -/
theorem pairedPrimeSum_antitone (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) :
    currentChenPairedPrimeSum N F ≤ currentChenPairedPrimeSum N E := by
  apply Finset.sum_le_sum
  intro P hP
  have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
  exact currentWeight_antitone (by omega : N - P ≠ 0) (N : ℝ) E F hEF

/-- An explicit bound on the actual bad-receiver contribution, stronger
than a positive per-receiver constant. It follows from the injection,
not from subtracting two one-sided weight bounds. -/
theorem squarefulExcess_nonpos (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) :
    (∑ P ∈ currentChenSquarefulPrimes N,
      (currentChenPairedWeight (N - P) (N : ℝ) F -
        currentChenPairedWeight (N - P) (N : ℝ) E)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro P hP
  have hc := (mem_currentChenSquarefulPrimes.mp hP).1
  have hPN := (mem_chenAdditivePrimeCarrier.mp hc).1
  exact sub_nonpos.mpr (currentWeight_antitone (by omega : N - P ≠ 0)
    (N : ℝ) E F hEF)

/-- The customary explicit squareful correction is also available. -/
theorem pairedPrimeSum_le_add_squareful_card (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) :
    currentChenPairedPrimeSum N F ≤ currentChenPairedPrimeSum N E +
      246 * ((currentChenSquarefulPrimes N).card : ℝ) := by
  have h := pairedPrimeSum_antitone N E F hEF
  have hc := Nat.cast_nonneg (α := ℝ) (currentChenSquarefulPrimes N).card
  linarith only [h, hc]

theorem pairedPrimeSum_le_add_squareful_bound (N : ℕ)
    (hA : 1 < (N : ℝ) ^ (417 / 5000 : ℝ)) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) :
    currentChenPairedPrimeSum N F ≤ currentChenPairedPrimeSum N E +
      246 * ((N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) := by
  have h := pairedPrimeSum_le_add_squareful_card N E F hEF
  have hc := currentChenSquarefulPrimes_card_cast_le N hA
  linarith only [h, hc]

/-- The literal cardinal correction is negligible in the original
singular normalization, by its actual proved arithmetic bound. -/
theorem eventually_squareful_card_cost (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, 246 * ((currentChenSquarefulPrimes N).card : ℝ) ≤
      epsilon * singularNormalization N := by
  filter_upwards [eventually_currentChen_weight_size_conditions,
    eventually_currentChen_weight_error_le_singularNormalization epsilon hepsilon]
    with N hsize hbudget
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hsize.1
  have hA := hsize.2
  have hc := currentChenSquarefulPrimes_card_cast_le N (by linarith)
  have hdiv : (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ) =
      (N : ℝ) ^ (1 - (417 / 5000 : ℝ)) := by
    rw [Real.rpow_sub hNp, Real.rpow_one]
  have hrecip : 1 / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1) ≤
      2 / (N : ℝ) ^ (417 / 5000 : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : 0 < (N : ℝ) ^ (417 / 5000 : ℝ) - 1)
      (by linarith : 0 < (N : ℝ) ^ (417 / 5000 : ℝ))).mpr
    linarith only [hA]
  have hquot : (N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1) ≤
      2 * (N : ℝ) ^ (1 - (417 / 5000 : ℝ)) := by
    calc
      _ = (N : ℝ) * (1 / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) := by ring
      _ ≤ (N : ℝ) * (2 / (N : ℝ) ^ (417 / 5000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg N)
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ)) := by ring
      _ = _ := by rw [hdiv]
  linarith only [hc, hquot, hbudget]

/-- The threshold precedes both masks. This gives the requested uniform
o(H) excess statement using the explicit squareful-card supplier. -/
theorem eventually_uniform_mask_antitone_error (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E F : ℕ × ℕ → Prop, (∀ t, E t → F t) →
      currentChenPairedPrimeSum N F ≤ currentChenPairedPrimeSum N E +
        epsilon * singularNormalization N := by
  filter_upwards [eventually_squareful_card_cost epsilon hepsilon] with N hcost
  intro E F hEF
  have h := pairedPrimeSum_le_add_squareful_card N E F hEF
  linarith only [h, hcost]

def positiveExcess (N : ℕ) (E F : ℕ × ℕ → Prop) : ℝ :=
  max 0 (currentChenPairedPrimeSum N F - currentChenPairedPrimeSum N E)

theorem positiveExcess_eq_zero (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ t, E t → F t) : positiveExcess N E F = 0 := by
  exact max_eq_left (sub_nonpos.mpr (pairedPrimeSum_antitone N E F hEF))

/-- Masks may depend arbitrarily on N. The normalized positive excess is
identically zero, which is stronger than its convergence to zero. -/
theorem tendsto_normalized_positiveExcess
    (E F : ℕ → ℕ × ℕ → Prop) (hEF : ∀ N t, E N t → F N t) :
    Tendsto (fun N : ℕ => positiveExcess N (E N) (F N) / singularNormalization N)
      atTop (𝓝 0) := by
  have hzero : (fun N : ℕ => positiveExcess N (E N) (F N) / singularNormalization N) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext N
    rw [positiveExcess_eq_zero N (E N) (F N) (hEF N), zero_div]
  rw [hzero]
  exact tendsto_const_nhds

end

end ImbalancedChen.P5SelectedMaskAggregate
