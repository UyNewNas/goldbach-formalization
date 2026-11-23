import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# Finite Brun brackets for the long slots

The divisor of a subset is its actual product of primes. The rank truncation
keeps the sign of every included divisor and its one-step gap is nonnegative.
-/

namespace ImbalancedChen.Part3

open Classical Finset
open scoped BigOperators

/-- The truncated alternating divisor sum over a finite set of primes. -/
noncomputable def brunProjector (P : Finset ℕ) (h n : ℕ) : ℤ :=
  ∑ j ∈ range (h + 1), ∑ s ∈ P.powersetCard j,
    if (∏ p ∈ s, p) ∣ n then (-1) ^ j else 0

/-- The indicator of integers free of the primes in `P`. -/
noncomputable def brunRoughIndicator (P : Finset ℕ) (n : ℕ) : ℤ :=
  if (P.filter fun p => p ∣ n).card = 0 then 1 else 0

private theorem brunProduct_dvd_iff (s : Finset ℕ) (n : ℕ)
    (hs : ∀ p ∈ s, p.Prime) : (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  exact ⟨fun h p hp => (dvd_prod_of_mem id hp).trans h,
    fun h => prod_primes_dvd n (fun p hp => (hs p hp).prime) h⟩

/-- The divisor sum is the rank-truncated alternating binomial sum on the
small primes that divide `n`. -/
theorem brunProjector_eq_sum_choose (P : Finset ℕ) (h n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    brunProjector P h n = ∑ j ∈ range (h + 1),
      (-1) ^ j * ((P.filter fun p => p ∣ n).card.choose j : ℤ) := by
  unfold brunProjector
  apply sum_congr rfl
  intro j _
  have hfilter : (P.powersetCard j).filter (fun s => (∏ p ∈ s, p) ∣ n) =
      (P.filter fun p => p ∣ n).powersetCard j := by
    ext s
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hs, hj⟩, hdvd⟩
      have hmem := (brunProduct_dvd_iff s n fun p hp => hP p (hs hp)).mp hdvd
      exact ⟨fun p hp => mem_filter.mpr ⟨hs hp, hmem p hp⟩, hj⟩
    · rintro ⟨hs, hj⟩
      have hsub : s ⊆ P := hs.trans (filter_subset _ _)
      exact ⟨⟨hsub, hj⟩, (brunProduct_dvd_iff s n fun p hp => hP p (hsub hp)).mpr
        (fun p hp => (mem_filter.mp (hs hp)).2)⟩
  rw [← sum_filter, hfilter, sum_const, card_powersetCard, nsmul_eq_mul, mul_comm]

/-- The upper and lower Brun weights bracket the actual rough indicator.
The gap is precisely the next rank. -/
theorem brunProjector_brackets (P : Finset ℕ) (h n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hh : Even h) :
    brunProjector P (h + 1) n ≤ brunRoughIndicator P n ∧
    brunRoughIndicator P n ≤ brunProjector P h n ∧
    brunProjector P h n - brunProjector P (h + 1) n =
      ((P.filter fun p => p ∣ n).card.choose (h + 1) : ℤ) := by
  have hsign : (-1 : ℤ) ^ (h + 1) = -1 := by rw [pow_succ, hh.neg_one_pow, one_mul]
  have hgap : brunProjector P h n - brunProjector P (h + 1) n =
      ((P.filter fun p => p ∣ n).card.choose (h + 1) : ℤ) := by
    rw [brunProjector_eq_sum_choose P h n hP, brunProjector_eq_sum_choose P (h + 1) n hP]
    nth_rw 2 [sum_range_succ]
    rw [hsign]
    ring
  refine ⟨?_, ?_, hgap⟩ <;>
    rw [brunProjector_eq_sum_choose _ _ _ hP, brunRoughIndicator] <;>
    cases he : (P.filter fun p => p ∣ n).card with
    | zero => simp [sum_range_succ']
    | succ k =>
      rw [if_neg (Nat.succ_ne_zero _), Int.alternating_sum_range_choose_eq_choose]
      first
      | rw [hsign, neg_one_mul]
        exact neg_nonpos.mpr (Int.natCast_nonneg _)
      | rw [hh.neg_one_pow, one_mul]
        exact Int.natCast_nonneg _

/-- The product gap uses nonnegativity of the upper weights and the two
rough indicators. The lower weights may be negative. -/
theorem brunProjector_product_gap (P : Finset ℕ) (h n₁ n₂ : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hh : Even h) :
    0 ≤ brunProjector P h n₁ * brunProjector P h n₂ -
        brunRoughIndicator P n₁ * brunRoughIndicator P n₂ ∧
    brunProjector P h n₁ * brunProjector P h n₂ -
        brunRoughIndicator P n₁ * brunRoughIndicator P n₂ ≤
      (brunProjector P h n₁ - brunProjector P (h + 1) n₁) * brunProjector P h n₂ +
      brunProjector P h n₁ * (brunProjector P h n₂ - brunProjector P (h + 1) n₂) := by
  obtain ⟨hL₁, hU₁, _⟩ := brunProjector_brackets P h n₁ hP hh
  obtain ⟨hL₂, hU₂, _⟩ := brunProjector_brackets P h n₂ hP hh
  have hr₁ : 0 ≤ brunRoughIndicator P n₁ := by simp only [brunRoughIndicator]; split_ifs <;> decide
  have hr₂ : 0 ≤ brunRoughIndicator P n₂ := by simp only [brunRoughIndicator]; split_ifs <;> decide
  constructor
  · exact sub_nonneg.mpr (mul_le_mul hU₁ hU₂ hr₂ (hr₁.trans hU₁))
  · calc
      _ = (brunProjector P h n₁ - brunRoughIndicator P n₁) * brunProjector P h n₂ +
          brunRoughIndicator P n₁ * (brunProjector P h n₂ - brunRoughIndicator P n₂) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (sub_le_sub_left hL₁ _) (hr₂.trans hU₂))
        (mul_le_mul hU₁ (sub_le_sub_left hL₂ _) (sub_nonneg.mpr hU₂) (hr₁.trans hU₁))

/-- Positive divisors indexed by subsets of rank at most `h`. -/
def brunDivisors (P : Finset ℕ) (h : ℕ) : Finset ℕ :=
  ((range (h + 1)).sigma fun j => P.powersetCard j).image (fun u => ∏ p ∈ u.2, p)

/-- The fresh next-rank divisors, each with coefficient one in the gap. -/
def brunGapDivisors (P : Finset ℕ) (h : ℕ) : Finset ℕ :=
  (P.powersetCard (h + 1)).image (fun s => ∏ p ∈ s, p)

private theorem brunProduct_mem_box (s : Finset ℕ) (z h : ℕ) (hz : 1 ≤ z)
    (hs : ∀ p ∈ s, 0 < p ∧ p ≤ z) (hcard : s.card ≤ h) :
    (∏ p ∈ s, p) ∈ Icc 1 (z ^ h) := by
  apply mem_Icc.mpr
  refine ⟨Finset.prod_pos (fun p hp => (hs p hp).1), ?_⟩
  calc
    _ ≤ ∏ _p ∈ s, z := prod_le_prod' (fun p hp => (hs p hp).2)
    _ = z ^ s.card := by simp
    _ ≤ _ := pow_le_pow_right₀ hz hcard

/-- The genuine upper divisor support has the rank power cap. -/
theorem brunDivisors_subset_Icc (P : Finset ℕ) (z h : ℕ) (hz : 1 ≤ z)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) : brunDivisors P h ⊆ Icc 1 (z ^ h) := by
  intro d hd
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hd
  obtain ⟨hr, ht⟩ := mem_sigma.mp hu
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp ht
  exact brunProduct_mem_box u.2 z h hz
    (fun p hp => let hprime := hP p (hsub hp); ⟨hprime.1.pos, hprime.2⟩)
    (hcard.trans_le (Nat.lt_succ_iff.mp (mem_range.mp hr)))

/-- The nonnegative gap expansion has the next-rank power cap. -/
theorem brunGapDivisors_subset_Icc (P : Finset ℕ) (z h : ℕ) (hz : 1 ≤ z)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) : brunGapDivisors P h ⊆ Icc 1 (z ^ (h + 1)) := by
  intro d hd
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
  exact brunProduct_mem_box s z (h + 1) hz
    (fun p hp => let hprime := hP p (hsub hp); ⟨hprime.1.pos, hprime.2⟩) hcard.le

/-- The alternating subset sum is an actual divisor expansion. No
multiplicity is lost when the prime subsets are replaced by products. -/
theorem brunProjector_eq_divisor_sum (P : Finset ℕ) (h n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    brunProjector P h n = ∑ d ∈ brunDivisors P h,
      if d ∣ n then (-1 : ℤ) ^ d.primeFactors.card else 0 := by
  let labels := (range (h + 1)).sigma fun j => P.powersetCard j
  have hfactor (u : Σ _ : ℕ, Finset ℕ) (hu : u ∈ labels) :
      (∏ p ∈ u.2, p).primeFactors = u.2 :=
    Nat.primeFactors_prod fun p hp => hP p ((mem_powersetCard.mp (mem_sigma.mp hu).2).1 hp)
  have hinj : Set.InjOn (fun u : Σ _ : ℕ, Finset ℕ => ∏ p ∈ u.2, p) (↑labels) := by
    intro u hu v hv huv
    have hs : u.2 = v.2 := (hfactor u hu).symm.trans
      ((congrArg Nat.primeFactors huv).trans (hfactor v hv))
    have huRank := (mem_powersetCard.mp (mem_sigma.mp hu).2).2
    have hvRank := (mem_powersetCard.mp (mem_sigma.mp hv).2).2
    apply Sigma.ext (huRank.symm.trans ((congrArg Finset.card hs).trans hvRank))
    exact heq_of_eq hs
  unfold brunProjector brunDivisors
  rw [sum_image hinj, sum_sigma']
  apply sum_congr rfl
  intro u hu
  rw [hfactor u hu, (mem_powersetCard.mp (mem_sigma.mp hu).2).2]

/-- The gap of the two expansions is a nonnegative divisor expansion. -/
theorem brunProjector_gap_eq_divisor_sum (P : Finset ℕ) (h n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hh : Even h) :
    brunProjector P h n - brunProjector P (h + 1) n =
      ∑ d ∈ brunGapDivisors P h, if d ∣ n then (1 : ℤ) else 0 := by
  have hinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) (↑(P.powersetCard (h + 1))) := by
    intro s hs t ht he
    have hsFactor := Nat.primeFactors_prod fun p hp => hP p ((mem_powersetCard.mp hs).1 hp)
    have htFactor := Nat.primeFactors_prod fun p hp => hP p ((mem_powersetCard.mp ht).1 hp)
    exact hsFactor.symm.trans ((congrArg Nat.primeFactors he).trans htFactor)
  unfold brunProjector brunGapDivisors
  nth_rw 2 [sum_range_succ]
  rw [sum_image hinj, sub_add_cancel_left, ← sum_neg_distrib]
  apply sum_congr rfl
  intro s _
  have hsign : (-1 : ℤ) ^ (h + 1) = -1 := by rw [pow_succ, hh.neg_one_pow, one_mul]
  by_cases hd : (∏ p ∈ s, p) ∣ n <;> simp [hd, hsign]

private theorem sum_powersetCard_product_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S)
    (w : ℕ → ℝ) (k : ℕ) :
    (∑ t ∈ (insert a S).powersetCard (k + 1), ∏ p ∈ t, w p) =
      (∑ t ∈ S.powersetCard (k + 1), ∏ p ∈ t, w p) +
        w a * ∑ t ∈ S.powersetCard k, ∏ p ∈ t, w p := by
  have hdisjoint : Disjoint (S.powersetCard (k + 1)) ((S.powersetCard k).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hi
    obtain ⟨u, _, rfl⟩ := mem_image.mp hi
    exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))
  have hinj : Set.InjOn (insert a : Finset ℕ → Finset ℕ) (↑(S.powersetCard k)) := by
    intro s hs t ht he
    have has : a ∉ s := fun hs' => ha ((mem_powersetCard.mp hs).1 hs')
    have hat : a ∉ t := fun ht' => ha ((mem_powersetCard.mp ht).1 ht')
    simpa only [erase_insert has, erase_insert hat] using congrArg (fun u : Finset ℕ => u.erase a) he
  rw [powersetCard_succ_insert ha, sum_union hdisjoint, sum_image hinj, mul_sum]
  congr 1
  apply sum_congr rfl
  intro t ht
  exact prod_insert (fun h => ha ((mem_powersetCard.mp ht).1 h))

private theorem pow_add_ge_linear {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    a ^ (k + 1) + ((k : ℝ) + 1) * a ^ k * b ≤ (a + b) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ (a + b) (k + 1)]
    apply le_trans _ (mul_le_mul_of_nonneg_right hk (add_nonneg ha hb))
    push_cast
    have hpos : 0 ≤ ((k : ℝ) + 1) * a ^ k * b ^ 2 := by positivity
    calc
      _ ≤ _ + ((k : ℝ) + 1) * a ^ k * b ^ 2 := le_add_of_nonneg_right hpos
      _ = _ := by simp only [pow_succ a (k + 1), pow_succ a k]; ring

/-- The elementary symmetric sum of nonnegative weights is bounded by the
corresponding power of their total mass divided by the factorial. -/
theorem sum_powersetCard_product_le_pow_div_factorial (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ S, 0 ≤ w p) (k : ℕ) :
    (∑ t ∈ S.powersetCard k, ∏ p ∈ t, w p) ≤ (∑ p ∈ S, w p) ^ k / k.factorial := by
  induction S using Finset.induction generalizing k with
  | empty =>
    cases k with
    | zero => simp
    | succ k =>
      rw [show (∅ : Finset ℕ).powersetCard (k + 1) = ∅ by simp]
      simp
  | @insert a S ha ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hwS (p : ℕ) (hp : p ∈ S) : 0 ≤ w p := hw p (mem_insert_of_mem hp)
      have hwa := hw a (mem_insert_self _ _)
      let A := ∑ p ∈ S, w p
      have hA : 0 ≤ A := sum_nonneg hwS
      have hfac : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
      rw [sum_powersetCard_product_insert ha, sum_insert ha]
      calc
        _ ≤ A ^ (k + 1) / ((k + 1).factorial : ℝ) + w a * (A ^ k / k.factorial) :=
          add_le_add (ih hwS _) (mul_le_mul_of_nonneg_left (ih hwS _) hwa)
        _ = (A ^ (k + 1) + ((k : ℝ) + 1) * A ^ k * w a) / ((k + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
          have hknz : (k : ℝ) + 1 ≠ 0 := by positivity
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_right
          (by simpa only [add_comm A (w a), A] using pow_add_ge_linear hA hwa k) (by positivity)

/-- The sum of reciprocal gap divisors has the Brun factorial saving.
This upper bound is uniform after removing any subset of primes. -/
theorem brunGapDivisors_sum_reciprocal_le (P : Finset ℕ) (h : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ d ∈ brunGapDivisors P h, (d : ℝ)⁻¹) ≤
      (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial := by
  have hinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) (↑(P.powersetCard (h + 1))) := by
    intro s hs t ht he
    have hsFactor := Nat.primeFactors_prod fun p hp => hP p ((mem_powersetCard.mp hs).1 hp)
    have htFactor := Nat.primeFactors_prod fun p hp => hP p ((mem_powersetCard.mp ht).1 hp)
    exact hsFactor.symm.trans ((congrArg Nat.primeFactors he).trans htFactor)
  unfold brunGapDivisors
  rw [sum_image hinj]
  simp only [Nat.cast_prod, ← prod_inv_distrib]
  exact sum_powersetCard_product_le_pow_div_factorial P (fun p => (p : ℝ)⁻¹)
    (fun _ _ => by positivity) _

end ImbalancedChen.Part3
