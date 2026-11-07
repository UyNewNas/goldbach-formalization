import ImbalancedChen.CurrentChenSummedBridge
import ImbalancedChen.ChenQuotientPrimeSource

/-!
# The actual current eleven-term mean ledger

This is a finite decomposition of `currentChenPairedPrimeSum`, with the
current exponents `417/5000`, `19/125`, `59/250`, and `1/3`. It does not
reuse the historical `chenUpsilon` definitions at different exponents.

Every entry sums the literal quotient count over the same additive-prime
carrier. Entries six and eleven retain the complement of the same pair
predicate `E`; thus the displayed signed expression still has exactly
eleven terms after paired deletion. In entry eleven the predicate is
applied to the last two prime values, and its fourth-prime interval remains
the complete `[N^(19/125), N^(59/250))`. For the manuscript's rectangle
mask, `E (p, q)` is pulled back from coordinates `(log_N q, log_N p)`.

All eleven entries are identified with their actual sifted receiver or
quotient sources. The switching terms use finite Fubini with a cutoff
that varies with the complete outer tuple. The ninth cutoff remains
`sqrt(N/(p₁*p₂))`; the tenth and eleventh retain all four prime labels.

The final lemma is finite signed arithmetic with eleven separate actual
term bounds. No distribution estimate, adopted mask, numerical integral
certificate, or lower mean theorem is supplied or assumed here.

Validation status and actual execution receipts are recorded in
`docs/CHEN_P5_ROUND2_HANDOFF.md`.
-/

namespace ImbalancedChen

open scoped BigOperators
open Classical

noncomputable section

/-- The selected and unselected sixth supports partition the actual full
support. This is valid for every receiver, including nonsquarefree ones. -/
theorem chenY6Selected_add_compl (n : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    chenY6Selected n A H D E + chenY6Selected n A H D (fun t => ¬ E t) =
      chenY6 n A H D := by
  classical
  unfold chenY6Selected chenY6SelectedTuples chenY6
  convert (Finset.card_filter_add_card_filter_not (s := chenY6Tuples n A H D) E) using 1
  congr

/-- The same partition in the full eleventh support applies the mask to
the last pair, without changing any factor cutoff or quotient condition. -/
theorem chenY11Selected_add_compl (n : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    chenY11Selected n A H D E + chenY11Selected n A H D (fun t => ¬ E t) =
      chenY11Full n A H D := by
  classical
  unfold chenY11Selected chenY11SelectedTuples chenY11Full
  simpa only [Finset.filter_congr_decidable] using
    (Finset.card_filter_add_card_filter_not (s := chenY11FullTuples n A H D)
      (fun t => E t.2))

/-- Paired deletion is exactly replacement of terms six and eleven by
their unselected actual quotient counts. The equality needs no injection
or squarefreeness assumption and all subtractions remain real-valued. -/
theorem chenPairedElevenWeight_eq_unselected (n : ℕ) (N A H D C : ℝ)
    (E : ℕ × ℕ → Prop) :
    chenPairedElevenWeight n N A H D C E =
      3 * (chenY1 n A : ℝ) + (chenY2 n H : ℝ) - (chenY3 n A C : ℝ) -
        (chenY4 n A D : ℝ) + (chenY5 n A H : ℝ) +
        (chenY6Selected n A H D (fun t => ¬ E t) : ℝ) -
        2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) -
        (chenY9 n N H D : ℝ) - (chenY10 n A H : ℝ) -
        (chenY11Selected n A H D (fun t => ¬ E t) : ℝ) := by
  have h₆ : (chenY6Selected n A H D E : ℝ) +
      (chenY6Selected n A H D (fun t => ¬ E t) : ℝ) = (chenY6 n A H D : ℝ) := by
    exact_mod_cast chenY6Selected_add_compl n A H D E
  have h₁₁ : (chenY11Selected n A H D E : ℝ) +
      (chenY11Selected n A H D (fun t => ¬ E t) : ℝ) =
      (chenY11Full n A H D : ℝ) := by
    exact_mod_cast chenY11Selected_add_compl n A H D E
  unfold chenPairedElevenWeight chenElevenWeight
  linarith only [h₆, h₁₁]

/-- Finite Fubini with a separate literal cutoff for every tuple. This
retains each tuple label and is suitable for all five switching terms. -/
theorem chen_sum_quotient_tuple_card_moving_cutoff {α : Type*} [DecidableEq α]
    (N : ℕ) (T : Finset α) (b : α → ℕ) (z : α → ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N,
      ((T.filter (fun t => ChenQuotient (b t) (z t) (N - P))).card : ℝ)) =
      ∑ t ∈ T, ((chenSiftedQuotientPrimeSource N (b t) (z t)).card : ℝ) := by
  classical
  simp_rw [chenSiftedQuotientPrimeSource_card]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  exact Finset.sum_comm

/-- Every prime factor of an actual additive receiver is a permitted
outer prime label. This supplies the carrier step for the switching rows. -/
theorem chen_prime_dvd_receiver_mem_additiveCarrier {N P p : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (hp : Nat.Prime p)
    (hd : p ∣ N - P) : p ∈ chenAdditivePrimeCarrier N := by
  obtain ⟨hPN, hprime, hcop⟩ := mem_chenAdditivePrimeCarrier.mp hP
  have hpos : 0 < N - P := by omega
  have hle : p ≤ N - P := Nat.le_of_dvd hpos hd
  have hPpos := hprime.pos
  exact mem_chenAdditivePrimeCarrier.mpr ⟨by omega, hp,
    ((Nat.coprime_self_sub_left hPN.le).mpr hcop).of_dvd_left hd⟩

/-- Actual seventh outer selector, with its strict square-root cap. -/
def chenY7PrimeSelector (N : ℕ) (D : ℝ) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun t =>
    D ≤ (t.1 : ℝ) ∧ t.1 < t.2 ∧
    (t.2 : ℝ) < Real.sqrt ((N : ℝ) / (t.1 : ℝ))

/-- Actual eighth selector, including equality at the second lower cap. -/
def chenY8PrimeSelector (N : ℕ) (A C : ℝ) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun t =>
    A ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < C ∧ C ≤ (t.2 : ℝ) ∧
    (t.2 : ℝ) < Real.sqrt ((N : ℝ) / (t.1 : ℝ))

/-- Actual ninth selector. Its quotient cutoff is kept separately below
and is not identified with the second prime. -/
def chenY9PrimeSelector (N : ℕ) (H D : ℝ) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun t =>
    H ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < D ∧ D ≤ (t.2 : ℝ) ∧
    (t.2 : ℝ) < Real.sqrt ((N : ℝ) / (t.1 : ℝ))

/-- Actual tenth selector keeps all four increasing prime labels. -/
def chenY10PrimeSelector (N : ℕ) (A H : ℝ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N) ×ˢ
    (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N)).filter fun t =>
    A ≤ (t.1.1 : ℝ) ∧ t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    (t.2.2 : ℝ) < H

/-- Actual full eleventh selector. The last-prime band is `[H,D)`. -/
def chenY11FullPrimeSelector (N : ℕ) (A H D : ℝ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N) ×ˢ
    (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N)).filter fun t =>
    A ≤ (t.1.1 : ℝ) ∧ t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧
    (t.2.1 : ℝ) < H ∧ H ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < D

/-- Seventh support reindexing is exact even on squareful receivers. -/
theorem chenY7Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (D : ℝ) :
    chenY7Tuples (N - P) (N : ℝ) D =
      (chenY7PrimeSelector N D).filter
        (fun t => ChenQuotient (t.1 * t.2) (t.2 : ℝ) (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext ⟨p₁, p₂⟩
  rw [mem_chenY7Tuples_iff hn]
  simp only [chenY7PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp₁, hp₂, hD, h₁₂, hcap, hQ⟩
    have h₁ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₁
      ((dvd_mul_right p₁ p₂).trans hQ.1)
    have h₂ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₂
      ((dvd_mul_left p₂ p₁).trans hQ.1)
    exact ⟨⟨⟨h₁, h₂⟩, hD, h₁₂, hcap⟩, hQ⟩
  · rintro ⟨⟨⟨h₁, h₂⟩, hD, h₁₂, hcap⟩, hQ⟩
    exact ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1, hD, h₁₂, hcap, hQ⟩

theorem chenY8Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A C : ℝ) :
    chenY8Tuples (N - P) (N : ℝ) A C =
      (chenY8PrimeSelector N A C).filter
        (fun t => ChenQuotient (t.1 * t.2) (t.2 : ℝ) (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext ⟨p₁, p₂⟩
  rw [mem_chenY8Tuples_iff hn]
  simp only [chenY8PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp₁, hp₂, hA, h₁C, hC₂, hcap, hQ⟩
    have h₁ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₁
      ((dvd_mul_right p₁ p₂).trans hQ.1)
    have h₂ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₂
      ((dvd_mul_left p₂ p₁).trans hQ.1)
    exact ⟨⟨⟨h₁, h₂⟩, hA, h₁C, hC₂, hcap⟩, hQ⟩
  · rintro ⟨⟨⟨h₁, h₂⟩, hA, h₁C, hC₂, hcap⟩, hQ⟩
    exact ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1, hA, h₁C, hC₂, hcap, hQ⟩

/-- The ninth support retains the actual `sqrt(N/(p₁*p₂))` quotient
cutoff, which differs from the cutoffs in the other pair switches. -/
theorem chenY9Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (H D : ℝ) :
    chenY9Tuples (N - P) (N : ℝ) H D =
      (chenY9PrimeSelector N H D).filter
        (fun t => ChenQuotient (t.1 * t.2)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ)))) (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext ⟨p₁, p₂⟩
  rw [mem_chenY9Tuples_iff hn]
  simp only [chenY9PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp₁, hp₂, hH, h₁D, hD₂, hcap, hQ⟩
    have h₁ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₁
      ((dvd_mul_right p₁ p₂).trans hQ.1)
    have h₂ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₂
      ((dvd_mul_left p₂ p₁).trans hQ.1)
    exact ⟨⟨⟨h₁, h₂⟩, hH, h₁D, hD₂, hcap⟩, hQ⟩
  · rintro ⟨⟨⟨h₁, h₂⟩, hH, h₁D, hD₂, hcap⟩, hQ⟩
    exact ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1, hH, h₁D, hD₂, hcap, hQ⟩

theorem chenY10Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A H : ℝ) :
    chenY10Tuples (N - P) A H =
      (chenY10PrimeSelector N A H).filter
        (fun t => ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ) (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩
  rw [mem_chenY10Tuples_iff hn]
  simp only [chenY10PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp₁, hp₂, hp₃, hp₄, hA, h₁₂, h₂₃, h₃₄, hH, hQ⟩
    have h₁ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₁
      ((dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃) p₄).trans hQ.1)
    have h₂ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₂
      ((dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃) p₄).trans hQ.1)
    have h₃ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₃
      ((dvd_mul_of_dvd_left (dvd_mul_left p₃ (p₁ * p₂)) p₄).trans hQ.1)
    have h₄ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₄
      ((dvd_mul_left p₄ (p₁ * p₂ * p₃)).trans hQ.1)
    exact ⟨⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, hA, h₁₂, h₂₃, h₃₄, hH⟩, hQ⟩
  · rintro ⟨⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, hA, h₁₂, h₂₃, h₃₄, hH⟩, hQ⟩
    exact ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₃).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₄).2.1, hA, h₁₂, h₂₃, h₃₄, hH, hQ⟩

/-- The complete eleventh source equality is also valid for squareful
receivers; the smallest-two characterization is not needed here. -/
theorem chenY11FullTuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A H D : ℝ) :
    chenY11FullTuples (N - P) A H D =
      (chenY11FullPrimeSelector N A H D).filter
        (fun t => ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ) (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩
  rw [chenY11FullTuples, Finset.mem_filter, mem_chenFourPrimeCarrier hn]
  simp only [chenY11FullPrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩, ⟨hp₃, hd₃⟩, ⟨hp₄, hd₄⟩⟩,
      hA, h₁₂, h₂₃, h₃H, hH₄, h₄D, hQ⟩
    have h₁ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₁ hd₁
    have h₂ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₂ hd₂
    have h₃ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₃ hd₃
    have h₄ := chen_prime_dvd_receiver_mem_additiveCarrier hP hp₄ hd₄
    exact ⟨⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, hA, h₁₂, h₂₃, h₃H, hH₄, h₄D⟩, hQ⟩
  · rintro ⟨⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, hA, h₁₂, h₂₃, h₃H, hH₄, h₄D⟩, hQ⟩
    refine ⟨⟨⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1, ?_⟩,
      ⟨(mem_chenAdditivePrimeCarrier.mp h₂).2.1, ?_⟩,
      ⟨(mem_chenAdditivePrimeCarrier.mp h₃).2.1, ?_⟩,
      ⟨(mem_chenAdditivePrimeCarrier.mp h₄).2.1, ?_⟩⟩,
      hA, h₁₂, h₂₃, h₃H, hH₄, h₄D, hQ⟩
    · exact (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃) p₄).trans hQ.1
    · exact (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃) p₄).trans hQ.1
    · exact (dvd_mul_of_dvd_left (dvd_mul_left p₃ (p₁ * p₂)) p₄).trans hQ.1
    · exact (dvd_mul_left p₄ (p₁ * p₂ * p₃)).trans hQ.1

/-- The seventh mean is an exact sum of actual quotient-source counts,
with the second prime still serving as its roughness cutoff. -/
theorem sum_chenY7_eq_siftedQuotientPrimeSource (N : ℕ) (D : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY7 (N - P) (N : ℝ) D : ℝ)) =
      ∑ t ∈ chenY7PrimeSelector N D,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ) := by
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        (((chenY7PrimeSelector N D).filter
          (fun t => ChenQuotient (t.1 * t.2) (t.2 : ℝ) (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [chenY7, chenY7Tuples_eq_selector_filter hP D]
    _ = _ := chen_sum_quotient_tuple_card_moving_cutoff N (chenY7PrimeSelector N D)
      (fun t => t.1 * t.2) (fun t => (t.2 : ℝ))

theorem sum_chenY8_eq_siftedQuotientPrimeSource (N : ℕ) (A C : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY8 (N - P) (N : ℝ) A C : ℝ)) =
      ∑ t ∈ chenY8PrimeSelector N A C,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ) := by
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        (((chenY8PrimeSelector N A C).filter
          (fun t => ChenQuotient (t.1 * t.2) (t.2 : ℝ) (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [chenY8, chenY8Tuples_eq_selector_filter hP A C]
    _ = _ := chen_sum_quotient_tuple_card_moving_cutoff N (chenY8PrimeSelector N A C)
      (fun t => t.1 * t.2) (fun t => (t.2 : ℝ))

/-- In the ninth mean, finite Fubini retains the distinct moving cutoff
`sqrt(N/(p₁*p₂))` without bounding or simplifying it. -/
theorem sum_chenY9_eq_siftedQuotientPrimeSource (N : ℕ) (H D : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY9 (N - P) (N : ℝ) H D : ℝ)) =
      ∑ t ∈ chenY9PrimeSelector N H D,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))).card : ℝ) := by
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        (((chenY9PrimeSelector N H D).filter
          (fun t => ChenQuotient (t.1 * t.2)
            (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ)))) (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [chenY9, chenY9Tuples_eq_selector_filter hP H D]
    _ = _ := chen_sum_quotient_tuple_card_moving_cutoff N (chenY9PrimeSelector N H D)
      (fun t => t.1 * t.2) (fun t => Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))

/-- The tenth reindexing preserves all four prime labels and the second
prime's role as the cutoff of the actual four-factor quotient. -/
theorem sum_chenY10_eq_siftedQuotientPrimeSource (N : ℕ) (A H : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY10 (N - P) A H : ℝ)) =
      ∑ t ∈ chenY10PrimeSelector N A H,
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ) := by
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        (((chenY10PrimeSelector N A H).filter
          (fun t => ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2)
            (t.1.2 : ℝ) (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [chenY10, chenY10Tuples_eq_selector_filter hP A H]
    _ = _ := chen_sum_quotient_tuple_card_moving_cutoff N (chenY10PrimeSelector N A H)
      (fun t => t.1.1 * t.1.2 * t.2.1 * t.2.2) (fun t => (t.1.2 : ℝ))

/-- Any selected last-pair mask commutes with the full eleventh source
reindexing. All four labels remain outer indices in the exact sum. -/
theorem sum_chenY11Selected_eq_siftedQuotientPrimeSource (N : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    (∑ P ∈ chenAdditivePrimeCarrier N,
      (chenY11Selected (N - P) A H D E : ℝ)) =
      ∑ t ∈ (chenY11FullPrimeSelector N A H D).filter (fun t => E t.2),
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ) := by
  classical
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        ((((chenY11FullPrimeSelector N A H D).filter (fun t => E t.2)).filter
          (fun t => ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2)
            (t.1.2 : ℝ) (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      simp only [chenY11Selected, chenY11SelectedTuples,
        chenY11FullTuples_eq_selector_filter hP A H D, Finset.filter_filter, and_comm]
    _ = _ := chen_sum_quotient_tuple_card_moving_cutoff N
      ((chenY11FullPrimeSelector N A H D).filter (fun t => E t.2))
      (fun t => t.1.1 * t.1.2 * t.2.1 * t.2.2) (fun t => (t.1.2 : ℝ))

/-- Current first term: the actual `N^(417/5000)`-rough receiver indicator. -/
def currentChenUpsilon1 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY1 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ)) : ℝ)

/-- Current second term on the identical additive-prime carrier. -/
def currentChenUpsilon2 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY2 (N - P) ((N : ℝ) ^ (19 / 125 : ℝ)) : ℝ)

/-- Current third term, retaining the strict upper endpoint `N^(1/3)`. -/
def currentChenUpsilon3 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY3 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ)

/-- Current fourth term, retaining the strict upper endpoint `N^(59/250)`. -/
def currentChenUpsilon4 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY4 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ)

/-- Current fifth term: strictly increasing pairs below `N^(19/125)`. -/
def currentChenUpsilon5 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY5 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) : ℝ)

/-- Current sixth term after deletion: actual pairs outside `E`, with the
second factor in the entire lower-inclusive, upper-strict interval. -/
def currentChenUpsilon6 (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY6Selected (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))
      (fun t => ¬ E t) : ℝ)

/-- Current seventh term keeps its actual square-root switching boundary. -/
def currentChenUpsilon7 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY7 (N - P) (N : ℝ) ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ)

/-- Current eighth term keeps inclusive ownership at `N^(1/3)`. -/
def currentChenUpsilon8 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY8 (N - P) (N : ℝ) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ)

/-- Current ninth term keeps its different, product-dependent quotient
roughness cutoff. Its actual tuple count is not replaced by an indicator. -/
def currentChenUpsilon9 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY9 (N - P) (N : ℝ) ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ)

/-- Current tenth term has four increasing factors below `N^(19/125)`. -/
def currentChenUpsilon10 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY10 (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) : ℝ)

/-- Current eleventh term after deletion: the same complement mask on
the last pair, with the full fourth-prime endpoint `N^(59/250)`. -/
def currentChenUpsilon11 (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY11Selected (N - P) ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))
      (fun t => ¬ E t) : ℝ)

/-- Reuse the actual prime-receiver sieve at the current first cutoff;
the previous fixed-exponent Upsilon theorem is not used. -/
theorem currentChenUpsilon1_eq_actual_siftedSum (N : ℕ) (hN : Even N) :
    currentChenUpsilon1 N =
      (chenInitialBoundingSieve N ((N : ℝ) ^ (417 / 5000 : ℝ)) hN).siftedSum := by
  symm
  exact chenInitialBoundingSieve_siftedSum_eq_Y1 N _ hN

/-- The second term uses the same actual prime-receiver source at its
current larger cutoff. The literal `Y1` and `Y2` formulas coincide. -/
theorem currentChenUpsilon2_eq_actual_siftedSum (N : ℕ) (hN : Even N) :
    currentChenUpsilon2 N =
      (chenInitialBoundingSieve N ((N : ℝ) ^ (19 / 125 : ℝ)) hN).siftedSum := by
  symm
  exact chenInitialBoundingSieve_siftedSum_eq_Y1 N _ hN

theorem currentChenUpsilon1_eq_actual_sifted_card (N : ℕ) (hN : Even N) :
    currentChenUpsilon1 N =
      ((chenSiftedPrimeSource N ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
  rw [currentChenUpsilon1_eq_actual_siftedSum N hN, chenInitialBoundingSieve_siftedSum]

theorem currentChenUpsilon2_eq_actual_sifted_card (N : ℕ) (hN : Even N) :
    currentChenUpsilon2 N =
      ((chenSiftedPrimeSource N ((N : ℝ) ^ (19 / 125 : ℝ))).card : ℝ) := by
  rw [currentChenUpsilon2_eq_actual_siftedSum N hN, chenInitialBoundingSieve_siftedSum]

/-- The current third term is the actual one-prime quotient-source sum
at its original endpoints, by the existing generic finite reindexing. -/
theorem currentChenUpsilon3_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon3 N =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
  exact sum_chenY3_eq_siftedQuotientPrimeSource N _ _

/-- The current fourth term uses the same reindexing with its distinct
strict upper endpoint. -/
theorem currentChenUpsilon4_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon4 N =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
  exact sum_chenY3_eq_siftedQuotientPrimeSource N _ _

/-- Current fifth-term reindexing preserves the ordered pair labels and
therefore their multiplicities across quotient fibres. -/
theorem currentChenUpsilon5_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon5 N =
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
  exact sum_chenY5_eq_siftedQuotientPrimeSource N _ _

/-- Any fixed pair selection commutes with the existing actual sixth
source reindexing. The selected tuple label is retained, and no product
image or quotient image loses multiplicity. -/
theorem sum_chenY6Selected_eq_siftedQuotientPrimeSource (N : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY6Selected (N - P) A H D E : ℝ)) =
      ∑ t ∈ (chenY6PrimeSelector N A H D).filter E,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) A).card : ℝ) := by
  classical
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        ((((chenY6PrimeSelector N A H D).filter E).filter
          (fun t => ChenQuotient (t.1 * t.2) A (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      simp only [chenY6Selected, chenY6SelectedTuples,
        chenY6Tuples_eq_selector_filter hP A H D, Finset.filter_filter, and_comm]
    _ = _ := chen_sum_quotient_tuple_card N ((chenY6PrimeSelector N A H D).filter E)
      (fun t => t.1 * t.2) A

/-- The paired sixth entry is thus a literal sifted quotient-source sum
on the complement of the same adopted pair mask. -/
theorem currentChenUpsilon6_eq_siftedQuotientPrimeSource (N : ℕ)
    (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6 N E =
      ∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
          (fun t => ¬ E t),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
  unfold currentChenUpsilon6
  convert (sum_chenY6Selected_eq_siftedQuotientPrimeSource N
    ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ))
    ((N : ℝ) ^ (59 / 250 : ℝ)) (fun t => ¬ E t)) using 1
  congr

/-- Current seventh term, with its actual second-prime quotient cutoff. -/
theorem currentChenUpsilon7_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon7 N =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ) := by
  exact sum_chenY7_eq_siftedQuotientPrimeSource N _

theorem currentChenUpsilon8_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon8 N =
      ∑ t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ) := by
  exact sum_chenY8_eq_siftedQuotientPrimeSource N _ _

/-- The current ninth source keeps the special square-root quotient
cutoff and the full original outer factor range. -/
theorem currentChenUpsilon9_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon9 N =
      ∑ t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))).card : ℝ) := by
  exact sum_chenY9_eq_siftedQuotientPrimeSource N _ _

theorem currentChenUpsilon10_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon10 N =
      ∑ t ∈ chenY10PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ) := by
  exact sum_chenY10_eq_siftedQuotientPrimeSource N _ _

/-- The current eleventh source uses precisely the same complement mask
as the sixth source, applied to its last pair, and retains all four labels. -/
theorem currentChenUpsilon11_eq_siftedQuotientPrimeSource (N : ℕ)
    (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E =
      ∑ t ∈ (chenY11FullPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
          (fun t => ¬ E t.2),
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ) := by
  unfold currentChenUpsilon11
  convert (sum_chenY11Selected_eq_siftedQuotientPrimeSource N
    ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ))
    ((N : ℝ) ^ (59 / 250 : ℝ)) (fun t => ¬ E t)) using 1
  congr

/-- Exact eleven-term identity for the actual current paired prime sum.
It preserves both the coefficient three on term one and the coefficient
minus two on term seven. This is an identity before any limiting step. -/
theorem currentChenPairedPrimeSum_eq_upsilon (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E =
      3 * currentChenUpsilon1 N + currentChenUpsilon2 N - currentChenUpsilon3 N -
        currentChenUpsilon4 N + currentChenUpsilon5 N + currentChenUpsilon6 N E -
        2 * currentChenUpsilon7 N - currentChenUpsilon8 N - currentChenUpsilon9 N -
        currentChenUpsilon10 N - currentChenUpsilon11 N E := by
  simp only [currentChenPairedPrimeSum, currentChenPairedWeight,
    chenPairedElevenWeight_eq_unselected, currentChenUpsilon1, currentChenUpsilon2,
    currentChenUpsilon3, currentChenUpsilon4, currentChenUpsilon5, currentChenUpsilon6,
    currentChenUpsilon7, currentChenUpsilon8, currentChenUpsilon9, currentChenUpsilon10,
    currentChenUpsilon11, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Finite signed assembly specifies the direction of every one of the
eleven required estimates: lower bounds for `1,2,5,6`, upper bounds for
`3,4,7,8,9,10,11`. The sixth and eleventh hypotheses use the same literal
mask, and no whole-weight mean estimate is an input. -/
theorem currentChenPairedPrimeSum_ge_of_term_bounds (N : ℕ) (E : ℕ × ℕ → Prop)
    (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀ u₁₁ : ℝ)
    (h₁ : l₁ ≤ currentChenUpsilon1 N)
    (h₂ : l₂ ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ u₃)
    (h₄ : currentChenUpsilon4 N ≤ u₄)
    (h₅ : l₅ ≤ currentChenUpsilon5 N)
    (h₆ : l₆ ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ u₇)
    (h₈ : currentChenUpsilon8 N ≤ u₈)
    (h₉ : currentChenUpsilon9 N ≤ u₉)
    (h₁₀ : currentChenUpsilon10 N ≤ u₁₀)
    (h₁₁ : currentChenUpsilon11 N E ≤ u₁₁) :
    3 * l₁ + l₂ - u₃ - u₄ + l₅ + l₆ - 2 * u₇ - u₈ - u₉ - u₁₀ - u₁₁ ≤
      currentChenPairedPrimeSum N E := by
  rw [currentChenPairedPrimeSum_eq_upsilon]
  linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁]

/-- Giving every actual term an error of `delta` on the literal singular
normalization costs exactly `14 * delta`: the absolute signed coefficient
sum is `3+1+1+1+1+1+2+1+1+1+1`. All eleven term estimates, with the same
mask in six and eleven, are still explicit inputs to this finite lemma. -/
theorem currentChenPairedPrimeSum_ge_of_normalized_term_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ delta : ℝ)
    (h₁ : (b₁ - delta) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : (b₂ - delta) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ (b₃ + delta) * singularNormalization N)
    (h₄ : currentChenUpsilon4 N ≤ (b₄ + delta) * singularNormalization N)
    (h₅ : (b₅ - delta) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : (b₆ - delta) * singularNormalization N ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ (b₇ + delta) * singularNormalization N)
    (h₈ : currentChenUpsilon8 N ≤ (b₈ + delta) * singularNormalization N)
    (h₉ : currentChenUpsilon9 N ≤ (b₉ + delta) * singularNormalization N)
    (h₁₀ : currentChenUpsilon10 N ≤ (b₁₀ + delta) * singularNormalization N)
    (h₁₁ : currentChenUpsilon11 N E ≤ (b₁₁ + delta) * singularNormalization N) :
    (3 * b₁ + b₂ - b₃ - b₄ + b₅ + b₆ - 2 * b₇ - b₈ - b₉ - b₁₀ - b₁₁ -
      14 * delta) * singularNormalization N ≤ currentChenPairedPrimeSum N E := by
  have h := currentChenPairedPrimeSum_ge_of_term_bounds N E
    ((b₁ - delta) * singularNormalization N)
    ((b₂ - delta) * singularNormalization N)
    ((b₃ + delta) * singularNormalization N)
    ((b₄ + delta) * singularNormalization N)
    ((b₅ - delta) * singularNormalization N)
    ((b₆ - delta) * singularNormalization N)
    ((b₇ + delta) * singularNormalization N)
    ((b₈ + delta) * singularNormalization N)
    ((b₉ + delta) * singularNormalization N)
    ((b₁₀ + delta) * singularNormalization N)
    ((b₁₁ + delta) * singularNormalization N)
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁
  convert h using 1
  ring

/-- A certificate for the combined last two terms can be consumed as one
upper bound on their actual sum. No separate numerical endpoints for
terms ten and eleven are needed or inferred. The first nine directions
are unchanged, and the same mask remains in terms six and eleven. -/
theorem currentChenPairedPrimeSum_ge_of_joint_last_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀₁₁ : ℝ)
    (h₁ : l₁ ≤ currentChenUpsilon1 N)
    (h₂ : l₂ ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ u₃)
    (h₄ : currentChenUpsilon4 N ≤ u₄)
    (h₅ : l₅ ≤ currentChenUpsilon5 N)
    (h₆ : l₆ ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ u₇)
    (h₈ : currentChenUpsilon8 N ≤ u₈)
    (h₉ : currentChenUpsilon9 N ≤ u₉)
    (h₁₀₁₁ : currentChenUpsilon10 N + currentChenUpsilon11 N E ≤ u₁₀₁₁) :
    3 * l₁ + l₂ - u₃ - u₄ + l₅ + l₆ - 2 * u₇ - u₈ - u₉ - u₁₀₁₁ ≤
      currentChenPairedPrimeSum N E := by
  rw [currentChenPairedPrimeSum_eq_upsilon]
  linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀₁₁]

/-- The normalized joint certificate pays `2 * delta` for the combined
last two terms. With the first nine entries this still costs exactly
`14 * delta` on the same singular normalization. `b₁₀₁₁` is a joint
coefficient; it is not split into unsupported individual endpoints. -/
theorem currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ delta : ℝ)
    (h₁ : (b₁ - delta) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : (b₂ - delta) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ (b₃ + delta) * singularNormalization N)
    (h₄ : currentChenUpsilon4 N ≤ (b₄ + delta) * singularNormalization N)
    (h₅ : (b₅ - delta) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : (b₆ - delta) * singularNormalization N ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ (b₇ + delta) * singularNormalization N)
    (h₈ : currentChenUpsilon8 N ≤ (b₈ + delta) * singularNormalization N)
    (h₉ : currentChenUpsilon9 N ≤ (b₉ + delta) * singularNormalization N)
    (h₁₀₁₁ : currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
      (b₁₀₁₁ + 2 * delta) * singularNormalization N) :
    (3 * b₁ + b₂ - b₃ - b₄ + b₅ + b₆ - 2 * b₇ - b₈ - b₉ - b₁₀₁₁ -
      14 * delta) * singularNormalization N ≤ currentChenPairedPrimeSum N E := by
  have h := currentChenPairedPrimeSum_ge_of_joint_last_bounds N E
    ((b₁ - delta) * singularNormalization N)
    ((b₂ - delta) * singularNormalization N)
    ((b₃ + delta) * singularNormalization N)
    ((b₄ + delta) * singularNormalization N)
    ((b₅ - delta) * singularNormalization N)
    ((b₆ - delta) * singularNormalization N)
    ((b₇ + delta) * singularNormalization N)
    ((b₈ + delta) * singularNormalization N)
    ((b₉ + delta) * singularNormalization N)
    ((b₁₀₁₁ + 2 * delta) * singularNormalization N)
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀₁₁
  convert h using 1
  ring

end

end ImbalancedChen
