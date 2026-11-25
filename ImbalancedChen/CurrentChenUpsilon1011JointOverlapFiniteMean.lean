import ImbalancedChen.CurrentChenUpsilon10OverlapDivisorSplit

/-!
# Literal joint U10/U11 finite mean with the common overlapping density

The actual joint selector owns the low fourth-prime band without a mask
and the entire [N^(19/125),N^(59/250)) band with the original complement
on the last pair. All four increasing prime labels are retained.

At every such tuple gcd(b,P_N(p₂))=p₁. The exact signed effective-weight
dictionary therefore applies to the whole joint source, yielding one
finite same-Rosser main/AP/centre bound for U10+U11. No separate scalar
endpoints, numerical kernel estimate or analytic mean is assumed.

SOURCE-WRITTEN, UNCOMPILED.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical
open P5U10OriginalMean

namespace P5U1011JointOverlap

def jointSelector (N : ℕ) (E : ℕ × ℕ → Prop) : Finset Label :=
  chenY1011JointPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)) E

/-- The actual selector supplies the complete prime carrier and all
three strict order relations, including p₃<p₄ on the full U11 band. -/
theorem joint_carrier_order {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) :
    t.1.1 ∈ chenAdditivePrimeCarrier N ∧ t.1.2 ∈ chenAdditivePrimeCarrier N ∧
      t.2.1 ∈ chenAdditivePrimeCarrier N ∧ t.2.2 ∈ chenAdditivePrimeCarrier N ∧
      t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 := by
  obtain ⟨hc, _, h12, h23, h34, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hfirst, hlast⟩ := Finset.mem_product.mp hc
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hfirst
  obtain ⟨h3, h4⟩ := Finset.mem_product.mp hlast
  exact ⟨h1, h2, h3, h4, h12, h23, h34⟩

/-- The full original upper endpoint and the same complement E on the
last pair are visible in the native joint support. -/
theorem joint_band_and_mask {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) :
    (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (t.1.1 : ℝ) ∧
      (t.2.1 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) ∧
      (t.2.2 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ) ∧
      ((t.2.2 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) ∨ ¬ E t.2) := by
  obtain ⟨_, hA, _, _, _, h3H, h4D, hmask⟩ := Finset.mem_filter.mp ht
  exact ⟨hA, h3H, h4D, hmask⟩

theorem jointSelector_eq_original_union (N : ℕ) (E : ℕ × ℕ → Prop)
    (hN : 1 ≤ (N : ℝ)) :
    jointSelector N E = selector N ∪
      (chenY11FullPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
          (fun t => ¬ E t.2) := by
  exact chenY1011JointPrimeSelector_eq_union N _ _ _ E
    (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))

/-- Literal original U11 complement tuples inject into the common
source without shortening their last-prime interval. -/
theorem originalU11_mem_joint {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (hN : 1 ≤ (N : ℝ))
    (ht : t ∈ (chenY11FullPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
        (fun t => ¬ E t.2)) : t ∈ jointSelector N E := by
  rw [jointSelector_eq_original_union N E hN]
  exact Finset.mem_union_right _ ht

theorem joint_multiplier_pos {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) : 0 < multiplier t := by
  obtain ⟨h1, h2, h3, h4, _⟩ := joint_carrier_order ht
  exact mul_pos (mul_pos (mul_pos
    (mem_chenAdditivePrimeCarrier.mp h1).2.1.pos
    (mem_chenAdditivePrimeCarrier.mp h2).2.1.pos)
    (mem_chenAdditivePrimeCarrier.mp h3).2.1.pos)
    (mem_chenAdditivePrimeCarrier.mp h4).2.1.pos

theorem joint_first_mem_sievePrimes {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) : t.1.1 ∈ sievePrimes N t.1.2 := by
  obtain ⟨h1, _, _, _, h12, _⟩ := joint_carrier_order ht
  obtain ⟨_, hp, hcop⟩ := mem_chenAdditivePrimeCarrier.mp h1
  exact mem_sievePrimes.mpr ⟨h12, hp, hp.coprime_iff_not_dvd.mp hcop⟩

theorem joint_first_dvd_sieveProduct {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) : t.1.1 ∣ sieveProduct N t.1.2 := by
  unfold sieveProduct
  exact Finset.dvd_prod_of_mem id (joint_first_mem_sievePrimes ht)

theorem joint_remainingMultiplier_coprime_sieveProduct
    {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label} (ht : t ∈ jointSelector N E) :
    Nat.Coprime (t.1.2 * t.2.1 * t.2.2) (sieveProduct N t.1.2) := by
  obtain ⟨_, h2, h3, h4, _, h23, h34⟩ := joint_carrier_order ht
  have hp2 := (mem_chenAdditivePrimeCarrier.mp h2).2.1
  have hp3 := (mem_chenAdditivePrimeCarrier.mp h3).2.1
  have hp4 := (mem_chenAdditivePrimeCarrier.mp h4).2.1
  have h2P : Nat.Coprime t.1.2 (sieveProduct N t.1.2) := by
    simpa using chen_prime_coprime_sieveProduct_of_real_lower (N := N) hp2
      (le_rfl : (t.1.2 : ℝ) ≤ (t.1.2 : ℝ))
  have h3P : Nat.Coprime t.2.1 (sieveProduct N t.1.2) := by
    simpa using chen_prime_coprime_sieveProduct_of_real_lower (N := N) hp3
      (show (t.1.2 : ℝ) ≤ (t.2.1 : ℝ) by exact_mod_cast h23.le)
  have h4P : Nat.Coprime t.2.2 (sieveProduct N t.1.2) := by
    simpa using chen_prime_coprime_sieveProduct_of_real_lower (N := N) hp4
      (show (t.1.2 : ℝ) ≤ (t.2.2 : ℝ) by exact_mod_cast (h23.trans h34).le)
  exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr ⟨h2P, h3P⟩, h4P⟩

theorem joint_gcd_multiplier_sieveProduct {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) :
    Nat.gcd (multiplier t) (sieveProduct N t.1.2) = t.1.1 := by
  have hmul : multiplier t = (t.1.2 * t.2.1 * t.2.2) * t.1.1 := by
    unfold multiplier
    ring
  rw [hmul]
  exact Nat.gcd_mul_of_coprime_of_dvd (joint_remainingMultiplier_coprime_sieveProduct ht)
    (joint_first_dvd_sieveProduct ht)

theorem joint_first_mul_residualProduct {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) :
    t.1.1 * residualProduct N t = sieveProduct N t.1.2 :=
  Nat.mul_div_cancel' (joint_first_dvd_sieveProduct ht)

theorem joint_residualProduct_ne_zero {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) : residualProduct N t ≠ 0 := by
  intro hzero
  have hmul := joint_first_mul_residualProduct ht
  rw [hzero, mul_zero] at hmul
  exact (sieveProduct_squarefree N t.1.2).ne_zero hmul.symm

theorem joint_multiplier_coprime_residualProduct
    {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label} (ht : t ∈ jointSelector N E) :
    Nat.Coprime (multiplier t) (residualProduct N t) := by
  have h := Nat.coprime_div_gcd_of_squarefree (sieveProduct_squarefree N t.1.2)
    (Nat.ne_of_gt (joint_multiplier_pos ht))
  rw [Nat.gcd_comm (sieveProduct N t.1.2) (multiplier t),
    joint_gcd_multiplier_sieveProduct ht] at h
  exact h.symm

/-- The same exact signed effective-weight formula now applies to every
joint tuple, independent of which original row owns its fourth prime. -/
theorem joint_signed_overlap_divisor_sum {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) (rho : ℕ → ℝ) :
    (∑ d ∈ (sieveProduct N t.1.2).divisors,
      rho d / (Nat.totient (multiplier t * d) : ℝ)) =
      1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          (rho e + rho (t.1.1 * e) / (t.1.1 : ℝ)) / (Nat.totient e : ℝ) := by
  have hp := (mem_sievePrimes.mp (joint_first_mem_sievePrimes ht)).2.1
  have hpb : t.1.1 ∣ multiplier t :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  calc
    _ = ∑ d ∈ (t.1.1 * residualProduct N t).divisors,
        rho d / (Nat.totient (multiplier t * d) : ℝ) := by
      rw [joint_first_mul_residualProduct ht]
    _ = _ := signed_overlap_divisor_sum hp (joint_residualProduct_ne_zero ht)
      (joint_multiplier_coprime_residualProduct ht) hpb rho

theorem joint_overlapDensity_eq_effectiveCoefficient_sum
    {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label} (ht : t ∈ jointSelector N E) (L : ℝ) :
    overlapDensity N t L =
      1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t L e / (Nat.totient e : ℝ) := by
  unfold overlapDensity effectiveCoefficient
  rw [support_eq_sieveProduct_divisors]
  exact joint_signed_overlap_divisor_sum ht (coefficient N t L)

/-- Native original U11-complement tuples have exactly the same gcd
and effective density, including equality at the lower fourth-prime wall. -/
theorem originalU11_overlap_dictionary {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (hN : 1 ≤ (N : ℝ))
    (ht : t ∈ (chenY11FullPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
        (fun t => ¬ E t.2)) (L : ℝ) :
    Nat.gcd (multiplier t) (sieveProduct N t.1.2) = t.1.1 ∧
      overlapDensity N t L = 1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t L e / (Nat.totient e : ℝ) := by
  have hjoint := originalU11_mem_joint hN ht
  exact ⟨joint_gcd_multiplier_sieveProduct hjoint,
    joint_overlapDensity_eq_effectiveCoefficient_sum hjoint L⟩

/-- One original joint finite upper mean. The main term, AP error and
centre correction all use the same tuple-dependent Rosser coefficient. -/
theorem currentChenUpsilon1011_joint_upper (N : ℕ) (E : ℕ × ℕ → Prop)
    (hN : 1 ≤ (N : ℝ)) (M : ℝ) (L : Label → ℝ)
    (hL : ∀ t ∈ jointSelector N E, 1 < L t)
    (hpL : ∀ t ∈ jointSelector N E, (t.1.2 : ℝ) ≤ L t) :
    currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
      M * (∑ t ∈ jointSelector N E, overlapDensity N t (L t)) +
        (∑ t ∈ jointSelector N E, signedAPError N M t (L t)) -
        ∑ t ∈ jointSelector N E, signedCentre N t (L t) := by
  rw [currentChenUpsilon10_add_11_eq_joint_source N E hN]
  change (∑ t ∈ jointSelector N E,
    ((chenSiftedQuotientPrimeSource N (multiplier t) (t.1.2 : ℝ)).card : ℝ)) ≤ _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  exact row_upper N M t (L t) (hL t ht) (hpL t ht)

/-- The exact overlap split feeds the whole joint mean without separate
numerical endpoints for the original tenth and eleventh rows. -/
theorem currentChenUpsilon1011_joint_upper_effective (N : ℕ) (E : ℕ × ℕ → Prop)
    (hN : 1 ≤ (N : ℝ)) (M : ℝ) (L : Label → ℝ)
    (hL : ∀ t ∈ jointSelector N E, 1 < L t)
    (hpL : ∀ t ∈ jointSelector N E, (t.1.2 : ℝ) ≤ L t) :
    currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
      M * (∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t (L t) e / (Nat.totient e : ℝ)) +
        (∑ t ∈ jointSelector N E, signedAPError N M t (L t)) -
        ∑ t ∈ jointSelector N E, signedCentre N t (L t) := by
  have h := currentChenUpsilon1011_joint_upper N E hN M L hL hpL
  have hmain : (∑ t ∈ jointSelector N E, overlapDensity N t (L t)) =
      ∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t (L t) e / (Nat.totient e : ℝ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact joint_overlapDensity_eq_effectiveCoefficient_sum ht (L t)
  rwa [hmain] at h

/-- A concrete legal level gives a joint finite bound with no row-level
legality hypothesis; this is not an analytic coefficient estimate. -/
theorem currentChenUpsilon1011_joint_upper_maxLevel (N : ℕ) (E : ℕ × ℕ → Prop)
    (hN : 1 ≤ (N : ℝ)) (M : ℝ) :
    currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
      M * (∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t (max 2 (t.1.2 : ℝ)) e / (Nat.totient e : ℝ)) +
        (∑ t ∈ jointSelector N E, signedAPError N M t (max 2 (t.1.2 : ℝ))) -
        ∑ t ∈ jointSelector N E, signedCentre N t (max 2 (t.1.2 : ℝ)) := by
  exact currentChenUpsilon1011_joint_upper_effective N E hN M
    (fun t => max 2 (t.1.2 : ℝ))
    (fun t _ => lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _))
    (fun t _ => le_max_right _ _)

end P5U1011JointOverlap

end

end ImbalancedChen
