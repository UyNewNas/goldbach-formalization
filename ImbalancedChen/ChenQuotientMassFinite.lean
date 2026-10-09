import ImbalancedChen.ChenPooledQuotientAP
import ImbalancedChen.ChenQuotientCentreBudget

/-!
# Bounded-weight replacement of the actual quotient masses

Owned finite candidate. Not compiled locally: Lean verification is CI-only.
No foreign import, analytic distribution premise, or added axiom is used.
Every literal selector and ordered-pair label is retained. The exact mass is
AP(N,N,b) minus the centre-prime count, even when b is primitive. Bounded
real coefficients can have either sign. The four primitive pools cost a
factor four, with no outer-cardinality loss.
-/

namespace ImbalancedChen

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

/-- Difference from a reciprocal-totient model, using the actual source. -/
def chenQuotientMassError (N : ℕ) (M : ℝ) (b : ℕ) : ℝ :=
  ((chenQuotientPrimeSource N b).card : ℝ) - M / (Nat.totient b : ℝ)

/-- This is the mass of the genuine quotient bounding sieve. -/
theorem chenQuotientBoundingSieve_massError (N b : ℕ) (A M : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) :
    (chenQuotientBoundingSieve N b A hN hb).totalMass - M / (Nat.totient b : ℝ) =
      chenQuotientMassError N M b := rfl

/-- The primitive-centre correction survives mass replacement. -/
theorem chenQuotientMassError_eq_primeAP_sub_centre (N : ℕ) (M : ℝ) (b : ℕ) :
    chenQuotientMassError N M b =
      chenQuotientPrimeAPError N M b - chenCentrePrimeAPCount N N b := by
  rw [chenQuotientMassError, chenQuotientPrimeSource_card_cast]
  unfold chenQuotientPrimeAPError
  ring

theorem abs_chenQuotientMassError_le (N : ℕ) (M : ℝ) (b : ℕ) :
    |chenQuotientMassError N M b| ≤
      |chenQuotientPrimeAPError N M b| + chenCentrePrimeAPCount N N b := by
  rw [chenQuotientMassError_eq_primeAP_sub_centre]
  simpa only [sub_eq_add_neg, abs_neg,
    abs_of_nonneg (chenCentrePrimeAPCount_nonneg N N b)] using
    (abs_add_le (chenQuotientPrimeAPError N M b) (-chenCentrePrimeAPCount N N b))

/-- The base multiplier pool keeps labels until injectivity is proved. -/
theorem sum_chenQuotientPrimeAPError_base_le_primitive
    {α : Type*} (N Q : ℕ) (M : ℝ) (T : Finset α) (b : α → ℕ)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hbinj : Set.InjOn b (T : Set α)) (hcap : ∀ t ∈ T, b t ≤ Q) :
    (∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| := by
  have hsub : T.image b ⊆ (Finset.Icc 1 Q).filter (fun k => Nat.Coprime k N) := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hbpos t ht, hcap t ht⟩, hbN t ht⟩
  calc
    _ = ∑ k ∈ T.image b, |chenQuotientPrimeAPError N M k| := by
      symm
      apply Finset.sum_image
      intro t ht u hu htu
      exact hbinj ht hu htu
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

/-- Absolute rowwise weighted mass errors, for arbitrary signed weights. -/
def chenSelectedWeightedMassError {α : Type*} (N : ℕ) (M : ℝ)
    (T : Finset α) (b : α → ℕ) (w : α → ℝ) : ℝ :=
  ∑ t ∈ T, |w t| * |chenQuotientMassError N M (b t)|

/-- Pure finite algebra and injective primitive pooling. This premise
bounds only the coefficient, not the sought distribution conclusion. -/
theorem chenSelectedWeightedMassError_le_primitive_add_centre
    {α : Type*} (N Q : ℕ) (M C : ℝ) (T : Finset α) (b : α → ℕ) (w : α → ℝ)
    (hC : 0 ≤ C) (hw : ∀ t ∈ T, |w t| ≤ C)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hbinj : Set.InjOn b (T : Set α)) (hcap : ∀ t ∈ T, b t ≤ Q) :
    chenSelectedWeightedMassError N M T b w ≤
      C * ((∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k|) + chenSelectedCentreMass N T b) := by
  have hrow : chenSelectedWeightedMassError N M T b w ≤
      C * ((∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)|) +
        chenSelectedCentreMass N T b) := by
    unfold chenSelectedWeightedMassError chenSelectedCentreMass
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    calc
      _ ≤ C * |chenQuotientMassError N M (b t)| :=
        mul_le_mul_of_nonneg_right (hw t ht) (abs_nonneg _)
      _ ≤ C * (|chenQuotientPrimeAPError N M (b t)| +
          chenCentrePrimeAPCount N N (b t)) :=
        mul_le_mul_of_nonneg_left (abs_chenQuotientMassError_le N M (b t)) hC
      _ = _ := by ring
  exact hrow.trans (mul_le_mul_of_nonneg_left (add_le_add
    (sum_chenQuotientPrimeAPError_base_le_primitive N Q M T b hbpos hbN hbinj hcap)
    le_rfl) hC)

/-- Literal weighted masses and reciprocal-totient main coefficient. -/
theorem chenSelectedWeightedMass_sub_main_eq {α : Type*}
    (N : ℕ) (M : ℝ) (T : Finset α) (b : α → ℕ) (w : α → ℝ) :
    (∑ t ∈ T, w t * ((chenQuotientPrimeSource N (b t)).card : ℝ)) -
      M * (∑ t ∈ T, w t / (Nat.totient (b t) : ℝ)) =
        ∑ t ∈ T, w t * chenQuotientMassError N M (b t) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  unfold chenQuotientMassError
  ring

theorem abs_chenSelectedWeightedMass_sub_main_le {α : Type*}
    (N : ℕ) (M : ℝ) (T : Finset α) (b : α → ℕ) (w : α → ℝ) :
    |(∑ t ∈ T, w t * ((chenQuotientPrimeSource N (b t)).card : ℝ)) -
      M * (∑ t ∈ T, w t / (Nat.totient (b t) : ℝ))| ≤
        chenSelectedWeightedMassError N M T b w := by
  rw [chenSelectedWeightedMass_sub_main_eq]
  simpa only [chenSelectedWeightedMassError, abs_mul] using
    (Finset.abs_sum_le_sum_abs (fun t => w t * chenQuotientMassError N M (b t)) T)

/-- Full all-selected cap; no row is silently removed when it is empty. -/
def ChenUpsilon36MultiplierCap (N Q : ℕ) : Prop :=
(∀ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))), p ≤ Q) ∧
  (∀ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), p ≤ Q) ∧
  (∀ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))), (t.1 * t.2) ≤ Q) ∧
  (∀ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), (t.1 * t.2) ≤ Q)

/-- A common finite coefficient bound; weights remain label-dependent. -/
def ChenUpsilon36MassWeightsBound (N : ℕ) (C : ℝ) (w₃ w₄ : ℕ → ℝ) (w₅ w₆ : (ℕ × ℕ) → ℝ) : Prop :=
  (∀ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))), |w₃ p| ≤ C) ∧
  (∀ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), |w₄ p| ≤ C) ∧
  (∀ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))), |w₅ t| ≤ C) ∧
  (∀ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), |w₆ t| ≤ C)

/-- The actual four weighted source masses. -/
def chenUpsilon36WeightedMass (N : ℕ) (w₃ w₄ : ℕ → ℝ) (w₅ w₆ : (ℕ × ℕ) → ℝ) : ℝ :=
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))), w₃ p * ((chenQuotientPrimeSource N p).card : ℝ)) +
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₄ p * ((chenQuotientPrimeSource N p).card : ℝ)) +
  (∑ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))), w₅ t * ((chenQuotientPrimeSource N (t.1 * t.2)).card : ℝ)) +
  (∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₆ t * ((chenQuotientPrimeSource N (t.1 * t.2)).card : ℝ))

/-- Reciprocal-totient coefficient without replacing Li by N/log N. -/
def chenUpsilon36WeightedMassMainCoefficient (N : ℕ) (w₃ w₄ : ℕ → ℝ) (w₅ w₆ : (ℕ × ℕ) → ℝ) : ℝ :=
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))), w₃ p / (Nat.totient p : ℝ)) +
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₄ p / (Nat.totient p : ℝ)) +
  (∑ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))), w₅ t / (Nat.totient (t.1 * t.2) : ℝ)) +
  (∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₆ t / (Nat.totient (t.1 * t.2) : ℝ))

/-- Four L1 weighted errors, stronger than absolute total replacement. -/
def chenUpsilon36WeightedMassError (N : ℕ) (M : ℝ) (w₃ w₄ : ℕ → ℝ) (w₅ w₆ : (ℕ × ℕ) → ℝ) : ℝ :=
  chenSelectedWeightedMassError N M (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) id w₃ +
  chenSelectedWeightedMassError N M (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) id w₄ +
  chenSelectedWeightedMassError N M (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))) (fun t : ℕ × ℕ => t.1 * t.2) w₅ +
  chenSelectedWeightedMassError N M (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) (fun t : ℕ × ℕ => t.1 * t.2) w₆

/-- The primitive-centre mass cost, with all four original labels. -/
def chenUpsilon36CentreMass (N : ℕ) : ℝ :=
  chenSelectedCentreMass N (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) id +
  chenSelectedCentreMass N (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) id +
  chenSelectedCentreMass N (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))) (fun t : ℕ × ℕ => t.1 * t.2) +
  chenSelectedCentreMass N (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) (fun t : ℕ × ℕ => t.1 * t.2)

/-- The all-four finite bound has precisely four primitive AP pools.
There is no outer-cardinality factor, and no centre term is discarded. -/
theorem chenUpsilon36WeightedMassError_le_primitive_add_centre
    (N Q : ℕ) (M C : ℝ) (w₃ w₄ : ℕ → ℝ) (w₅ w₆ : (ℕ × ℕ) → ℝ)
    (hC : 0 ≤ C) (hw : ChenUpsilon36MassWeightsBound N C w₃ w₄ w₅ w₆)
    (hcap : ChenUpsilon36MultiplierCap N Q) :
    chenUpsilon36WeightedMassError N M w₃ w₄ w₅ w₆ ≤
      C * (4 * (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k|) + chenUpsilon36CentreMass N) := by
  obtain ⟨hw₃, hw₄, hw₅, hw₆⟩ := hw
  obtain ⟨hc₃, hc₄, hc₅, hc₆⟩ := hcap
  have h3 := chenSelectedWeightedMassError_le_primitive_add_centre
    N Q M C (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) id w₃ hC hw₃
    (fun t ht => lt_trans Nat.zero_lt_one (chenSinglePrimeSelector_sieve_data ht).1)
    (fun t ht => (chenSinglePrimeSelector_sieve_data ht).2.1) (fun _ _ _ _ h => h) hc₃
  have h4 := chenSelectedWeightedMassError_le_primitive_add_centre
    N Q M C (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) id w₄ hC hw₄
    (fun t ht => lt_trans Nat.zero_lt_one (chenSinglePrimeSelector_sieve_data ht).1)
    (fun t ht => (chenSinglePrimeSelector_sieve_data ht).2.1) (fun _ _ _ _ h => h) hc₄
  have h5 := chenSelectedWeightedMassError_le_primitive_add_centre
    N Q M C (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))) (fun t : ℕ × ℕ => t.1 * t.2) w₅ hC hw₅
    (fun t ht => lt_trans Nat.zero_lt_one (chenY5PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY5PrimeSelector_sieve_data ht).2.1) (chenY5PrimeSelector_multiplier_injOn N _ _) hc₅
  have h6 := chenSelectedWeightedMassError_le_primitive_add_centre
    N Q M C (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) (fun t : ℕ × ℕ => t.1 * t.2) w₆ hC hw₆
    (fun t ht => lt_trans Nat.zero_lt_one (chenY6PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY6PrimeSelector_sieve_data ht).2.1) (chenY6PrimeSelector_multiplier_injOn N _ _ _) hc₆
  unfold chenUpsilon36WeightedMassError chenUpsilon36CentreMass
  nlinarith only [h3, h4, h5, h6]

/-- Absolute error in the total actual mass follows from the rowwise L1 bound. -/
theorem abs_chenUpsilon36WeightedMass_sub_main_le
    (N : ℕ) (M : ℝ) (w₃ w₄ : ℕ → ℝ) (w₅ w₆ : (ℕ × ℕ) → ℝ) :
    |chenUpsilon36WeightedMass N w₃ w₄ w₅ w₆ -
      M * chenUpsilon36WeightedMassMainCoefficient N w₃ w₄ w₅ w₆| ≤
        chenUpsilon36WeightedMassError N M w₃ w₄ w₅ w₆ := by
  have h3 := abs_chenSelectedWeightedMass_sub_main_le N M (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) id w₃
  have h4 := abs_chenSelectedWeightedMass_sub_main_le N M (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) id w₄
  have h5 := abs_chenSelectedWeightedMass_sub_main_le N M (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))) (fun t : ℕ × ℕ => t.1 * t.2) w₅
  have h6 := abs_chenSelectedWeightedMass_sub_main_le N M (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) (fun t : ℕ × ℕ => t.1 * t.2) w₆
  let e3 : ℝ := (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))), w₃ p * ((chenQuotientPrimeSource N p).card : ℝ)) -
    M * (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))), w₃ p / (Nat.totient p : ℝ))
  let e4 : ℝ := (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₄ p * ((chenQuotientPrimeSource N p).card : ℝ)) -
    M * (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₄ p / (Nat.totient p : ℝ))
  let e5 : ℝ := (∑ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))), w₅ t * ((chenQuotientPrimeSource N (t.1 * t.2)).card : ℝ)) -
    M * (∑ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))), w₅ t / (Nat.totient (t.1 * t.2) : ℝ))
  let e6 : ℝ := (∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₆ t * ((chenQuotientPrimeSource N (t.1 * t.2)).card : ℝ)) -
    M * (∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))), w₆ t / (Nat.totient (t.1 * t.2) : ℝ))
  have heq : chenUpsilon36WeightedMass N w₃ w₄ w₅ w₆ -
      M * chenUpsilon36WeightedMassMainCoefficient N w₃ w₄ w₅ w₆ =
        e3 + e4 + e5 + e6 := by
    dsimp [chenUpsilon36WeightedMass, chenUpsilon36WeightedMassMainCoefficient,
      e3, e4, e5, e6]
    ring
  rw [heq]
  have h34 := abs_add_le e3 e4
  have h345 := abs_add_le (e3 + e4) e5
  have h3456 := abs_add_le (e3 + e4 + e5) e6
  change |e3| ≤ _ at h3
  change |e4| ≤ _ at h4
  change |e5| ≤ _ at h5
  change |e6| ≤ _ at h6
  unfold chenUpsilon36WeightedMassError
  linarith only [h3, h4, h5, h6, h34, h345, h3456]

/-- The mass-only centre budget is polylogarithmic: no Q or row-count factor. -/
theorem chenUpsilon36CentreMass_le_four_log_cube {N : ℕ}
    (hN : Even N) (hN4 : 4 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    chenUpsilon36CentreMass N ≤ 4 * (Real.log (N : ℝ) / Real.log 2) ^ 3 := by
  have hpos : 0 < N := by omega
  have hNP := chen_not_prime_of_even_four_le hN hN4
  let L : ℝ := Real.log (N : ℝ) / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hL : 1 ≤ L := (le_div_iff₀ htwo).mpr (by simpa using htwo1.trans hlog)
  have hpow : L ^ 2 ≤ L ^ 3 := by
    have h := mul_nonneg (sub_nonneg.mpr hL) (sq_nonneg L)
    nlinarith
  have h3 := chenSinglePrimeSelector_centreMass_le_log_sq hpos hNP
    ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
  have h4 := chenSinglePrimeSelector_centreMass_le_log_sq hpos hNP ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))
  have h5 := chenY5PrimeSelector_centreMass_le_log_cube hpos hNP ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))
  have h6 := chenY6PrimeSelector_centreMass_le_log_cube hpos hNP ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))
  change _ ≤ L ^ 2 at h3 h4
  change _ ≤ L ^ 3 at h5 h6
  change _ ≤ 4 * L ^ 3
  unfold chenUpsilon36CentreMass
  linarith only [h3, h4, h5, h6, hpow]

/-- Every fixed bounded weight pays its actual centre error at arbitrary
logarithmic accuracy, with no distribution premise. C is fixed before N. -/
theorem eventually_mul_chenUpsilon36CentreMass_le_logAccuracy
    (K : ℕ) (C : ℝ) (hC : 0 ≤ C) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ hN : Even N,
      C * chenUpsilon36CentreMass N ≤
        epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  filter_upwards
    [eventually_powerLog_le_logAccuracy (4 * C / (Real.log 2) ^ 3) 0 3 K
      (by norm_num) epsilon hepsilon,
      eventually_one_le_nat_log, eventually_ge_atTop (4 : ℕ)]
    with N hpower hlog hN4
  intro hN
  calc
    _ ≤ C * (4 * (Real.log (N : ℝ) / Real.log 2) ^ 3) :=
      mul_le_mul_of_nonneg_left (chenUpsilon36CentreMass_le_four_log_cube hN hN4 hlog) hC
    _ = (4 * C / (Real.log 2) ^ 3) * (N : ℝ) ^ (0 : ℝ) *
        (Real.log (N : ℝ)) ^ 3 := by rw [Real.rpow_zero, div_pow]; ring
    _ ≤ _ := hpower

end
end ImbalancedChen
