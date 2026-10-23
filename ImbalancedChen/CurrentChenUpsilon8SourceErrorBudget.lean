import ImbalancedChen.CurrentChenUpsilon8ProductPan

/-!
# The actual eighth unit and small Goldbach-prime errors

Here P is the original Goldbach prime N-p1*p2*r; r is the prime
multiplicative quotient. Both new carriers filter the literal eighth
PrimeTriples, so its inclusive p2 lower endpoint, strict square-root
wall, target-prime exclusions and r>=p2 remain present.

Actual pair-product injectivity and the strict receiver bound pay an
injection into (p1*p2,P). Positive P permits the exact floor endpoint
for P<=N^(1/5). Units cost N^(2/3), and the small original Goldbach-prime
triples cost N^(13/15), with coefficient one. The proved power-error
budget then gives zero normalized ordinary cost. No count envelope or
analytic supplier is a premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

def currentChenUpsilon8SmallGoldbachPrimeTriples (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (currentChenUpsilon8PrimeTriples N).filter fun x =>
    ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ)

def currentChenUpsilon8LargeGoldbachPrimeTriples (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (currentChenUpsilon8PrimeTriples N).filter fun x =>
    (N : ℝ) ^ (1 / 5 : ℝ) < ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ)

theorem currentChenUpsilon8_prefixProducts_subset_positive_pan_interval {N : ℕ}
    (hN : 1 ≤ N) :
    currentChenUpsilon8PrefixProducts N ⊆ Finset.Ioc 0 (currentChenUpsilon8PanUpper N) := by
  intro a ha
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact Finset.mem_Ioc.mpr ⟨(currentChenUpsilon8PrefixProducts_data ha).1,
    (Finset.mem_Ioc.mp (currentChenUpsilon8PrefixProducts_subset_pan_interval hNr ha)).2⟩

theorem currentChenUpsilon8_prefixProducts_card_le_panUpper {N : ℕ} (hN : 1 ≤ N) :
    (currentChenUpsilon8PrefixProducts N).card ≤ currentChenUpsilon8PanUpper N := by
  have hcard := Finset.card_le_card
    (currentChenUpsilon8_prefixProducts_subset_positive_pan_interval hN)
  simpa only [Nat.card_Ioc, Nat.sub_zero] using hcard

theorem currentChenUpsilon8_unitFibres_card_le_prefixProducts (N : ℕ) :
    (currentChenUpsilon8UnitFibres N).card ≤ (currentChenUpsilon8PrefixProducts N).card := by
  apply Finset.card_le_card_of_injOn (fun t : ℕ × ℕ => t.1 * t.2)
  · intro t ht
    exact Finset.mem_image.mpr ⟨t, (Finset.mem_filter.mp ht).1, rfl⟩
  · intro t ht u hu heq
    exact chenY8PrimeSelector_multiplier_injOn N _ _
      (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp hu).1 heq

theorem currentChenUpsilon8_unitFibres_card_le_power {N : ℕ} (hN : 1 ≤ N) :
    ((currentChenUpsilon8UnitFibres N).card : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (Nat.cast_le.mpr (currentChenUpsilon8_unitFibres_card_le_prefixProducts N)).trans
    ((Nat.cast_le.mpr (currentChenUpsilon8_prefixProducts_card_le_panUpper hN)).trans
      (currentChenUpsilon8_panUpper_le_two_thirds hNr))

/-- Every actual triple is recovered from its prefix product and its
original Goldbach prime. The strict actual product bound prevents every
Nat-subtraction truncation before the final quotient is cancelled. -/
theorem currentChenUpsilon8PrimeTriples_product_goldbachPrime_injOn (N : ℕ) :
    Set.InjOn (fun x : Σ _ : ℕ × ℕ, ℕ =>
      (x.1.1 * x.1.2, N - x.1.1 * x.1.2 * x.2))
      (currentChenUpsilon8PrimeTriples N) := by
  intro x hx y hy heq
  rcases x with ⟨⟨p₁, p₂⟩, r⟩
  rcases y with ⟨⟨q₁, q₂⟩, s⟩
  change (p₁ * p₂, N - p₁ * p₂ * r) = (q₁ * q₂, N - q₁ * q₂ * s) at heq
  have hxp : (p₁, p₂) ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) := (Finset.mem_sigma.mp hx).1
  have hyp : (q₁, q₂) ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) := (Finset.mem_sigma.mp hy).1
  have hpq := chenY8PrimeSelector_multiplier_injOn N _ _ hxp hyp (congrArg Prod.fst heq)
  have hp₁ : p₁ = q₁ := congrArg Prod.fst hpq
  have hp₂ : p₂ = q₂ := congrArg Prod.snd hpq
  subst q₁
  subst q₂
  obtain ⟨h₁, h₂, _hA, _hfirst, _hsecond, _hcap, _hr, hrN, _hP, _hcut⟩ :=
    mem_currentChenUpsilon8PrimeTriples_iff.mp hx
  obtain ⟨_h₁, _h₂, _hA, _hfirst, _hsecond, _hcap, _hs, hsN, _hQ, _hcut⟩ :=
    mem_currentChenUpsilon8PrimeTriples_iff.mp hy
  have ha : 0 < p₁ * p₂ := mul_pos
    (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
    (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
  have hP : N - p₁ * p₂ * r = N - p₁ * p₂ * s := congrArg Prod.snd heq
  have hmul : (p₁ * p₂) * r = (p₁ * p₂) * s := by omega
  have hrs : r = s := Nat.eq_of_mul_eq_mul_left ha hmul
  subst s
  rfl

theorem currentChenUpsilon8_smallGoldbachPrimeTriples_card_le_rectangle {N : ℕ}
    (hN : 1 ≤ N) :
    (currentChenUpsilon8SmallGoldbachPrimeTriples N).card ≤
      currentChenUpsilon8PanUpper N * Nat.floor ((N : ℝ) ^ (1 / 5 : ℝ)) := by
  have hcard : (currentChenUpsilon8SmallGoldbachPrimeTriples N).card ≤
      (Finset.Ioc 0 (currentChenUpsilon8PanUpper N) ×ˢ
        Finset.Ioc 0 (Nat.floor ((N : ℝ) ^ (1 / 5 : ℝ)))).card := by
    apply Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ × ℕ, ℕ =>
      (x.1.1 * x.1.2, N - x.1.1 * x.1.2 * x.2))
    · intro x hx
      obtain ⟨hxt, hsmall⟩ := Finset.mem_filter.mp hx
      rcases x with ⟨⟨p₁, p₂⟩, r⟩
      have hap : p₁ * p₂ ∈ currentChenUpsilon8PrefixProducts N :=
        Finset.mem_image.mpr ⟨(p₁, p₂), (Finset.mem_sigma.mp hxt).1, rfl⟩
      obtain ⟨_h₁, _h₂, _hA, _hfirst, _hsecond, _hcap, _hr, _hrN, hP, _hcut⟩ :=
        mem_currentChenUpsilon8PrimeTriples_iff.mp hxt
      have hPpos : 0 < N - p₁ * p₂ * r :=
        (mem_chenAdditivePrimeCarrier.mp hP).2.1.pos
      have hPfloor : N - p₁ * p₂ * r ≤ Nat.floor ((N : ℝ) ^ (1 / 5 : ℝ)) :=
        (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)).mpr hsmall
      exact Finset.mem_product.mpr
        ⟨currentChenUpsilon8_prefixProducts_subset_positive_pan_interval hN hap,
          Finset.mem_Ioc.mpr ⟨hPpos, hPfloor⟩⟩
    · intro x hx y hy heq
      exact currentChenUpsilon8PrimeTriples_product_goldbachPrime_injOn N
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 heq
  simpa only [Finset.card_product, Nat.card_Ioc, Nat.sub_zero] using hcard

theorem currentChenUpsilon8_smallGoldbachPrimeTriples_card_le_power {N : ℕ}
    (hN : 1 ≤ N) :
    ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) ≤
      (N : ℝ) ^ (13 / 15 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  calc
    _ ≤ (currentChenUpsilon8PanUpper N : ℝ) *
        (Nat.floor ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) := by
      exact_mod_cast currentChenUpsilon8_smallGoldbachPrimeTriples_card_le_rectangle hN
    _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) :=
      mul_le_mul (currentChenUpsilon8_panUpper_le_two_thirds hNr)
        (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
        (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by
      rw [← Real.rpow_add hNp, show (2 / 3 : ℝ) + 1 / 5 = 13 / 15 by norm_num]

/-- This is the original current eighth count, with every actual outer
pair label and the inclusive small-Goldbach-prime endpoint retained. -/
theorem currentChenUpsilon8_eq_largeGoldbachPrimeTriples_add_errors (N : ℕ) :
    currentChenUpsilon8 N = ((currentChenUpsilon8LargeGoldbachPrimeTriples N).card : ℝ) +
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  have hpart : (currentChenUpsilon8PrimeTriples N).card =
      (currentChenUpsilon8SmallGoldbachPrimeTriples N).card +
        (currentChenUpsilon8LargeGoldbachPrimeTriples N).card := by
    simpa only [currentChenUpsilon8SmallGoldbachPrimeTriples,
      currentChenUpsilon8LargeGoldbachPrimeTriples, not_le] using
      (Finset.card_filter_add_card_filter_not (s := currentChenUpsilon8PrimeTriples N)
        (fun x => ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ) ≤
          (N : ℝ) ^ (1 / 5 : ℝ))).symm
  have hpartR : ((currentChenUpsilon8PrimeTriples N).card : ℝ) =
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8LargeGoldbachPrimeTriples N).card : ℝ) := by exact_mod_cast hpart
  rw [currentChenUpsilon8_eq_primeTriples_add_unitFibres, hpartR]
  ring

theorem eventually_currentChenUpsilon8_sourceErrors_le_singularNormalization
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ) ≤ ε * singularNormalization N := by
  have hsmall := eventually_powerLog_le_singularNormalization 1 (13 / 15) 0
    (by norm_num) (ε / 2) (half_pos hε)
  have hunit := eventually_powerLog_le_singularNormalization 1 (2 / 3) 0
    (by norm_num) (ε / 2) (half_pos hε)
  filter_upwards [hsmall, hunit, eventually_ge_atTop (1 : ℕ)] with N hs hu hN
  have hs' : ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) ≤
      (ε / 2) * singularNormalization N :=
    (currentChenUpsilon8_smallGoldbachPrimeTriples_card_le_power hN).trans
      (by simpa only [one_mul, pow_zero, mul_one] using hs)
  have hu' : ((currentChenUpsilon8UnitFibres N).card : ℝ) ≤
      (ε / 2) * singularNormalization N :=
    (currentChenUpsilon8_unitFibres_card_le_power hN).trans
      (by simpa only [one_mul, pow_zero, mul_one] using hu)
  linarith only [hs', hu']

theorem tendsto_currentChenUpsilon8_sourceErrors_normalized :
    Tendsto (fun N : ℕ =>
      (((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ)) / singularNormalization N)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_singularNormalization_pos] with N hpos
    exact ha.trans_le (div_nonneg (by positivity) hpos.le)
  · intro b hb
    filter_upwards [eventually_currentChenUpsilon8_sourceErrors_le_singularNormalization
      (b / 2) (half_pos hb), eventually_singularNormalization_pos] with N hbound hpos
    have hquot :
        (((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
          ((currentChenUpsilon8UnitFibres N).card : ℝ)) / singularNormalization N ≤ b / 2 :=
      (div_le_iff₀ hpos).mpr hbound
    exact hquot.trans_lt (by linarith)

/-- The difference between the literal ordinary eighth count and its
literal large-Goldbach-prime triples has zero normalized mean. -/
theorem tendsto_currentChenUpsilon8_sub_largeGoldbachPrimeTriples_normalized :
    Tendsto (fun N : ℕ =>
      (currentChenUpsilon8 N - ((currentChenUpsilon8LargeGoldbachPrimeTriples N).card : ℝ)) /
        singularNormalization N) atTop (𝓝 0) := by
  apply tendsto_currentChenUpsilon8_sourceErrors_normalized.congr'
  exact Filter.Eventually.of_forall (fun N => by
    change
      (((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ)) / singularNormalization N =
        (currentChenUpsilon8 N -
          ((currentChenUpsilon8LargeGoldbachPrimeTriples N).card : ℝ)) / singularNormalization N
    rw [currentChenUpsilon8_eq_largeGoldbachPrimeTriples_add_errors]
    ring)

end

end ImbalancedChen