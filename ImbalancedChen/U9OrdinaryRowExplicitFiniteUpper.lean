import ImbalancedChen.U9CentreMoebiusRowRemainder

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The coefficient budget is proved for the ACTUAL lambda-square coefficient:
base weights bounded by one and supported through L give total coefficient
absolute mass at most L². Rho itself is not assumed bounded by one.
Together with the proved original-centre remainder this yields the genuine
original p₂-row upper bound mass/G + 2*tau(N)*L² + z, with no opaque AP norm.
This finite estimate does not establish the strong coupled analytic saving.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

/-- Finite lcm fibres pay every lambda-square coefficient once. This
bound uses the true base coefficient bound, not a false |rho(e)|≤1 claim. -/
theorem lambdaSquared_l1_le_level_sq (P L : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n, |w n| ≤ 1) (hcut : ∀ n, L < n → w n = 0) :
    (∑ e ∈ P.divisors, |BoundingSieve.lambdaSquared w e|) ≤ (L : ℝ) ^ 2 := by
  let U := P.divisors.filter fun n => n ≤ L
  let pairs := U ×ˢ U
  have hpoint (e : ℕ) (he : e ∈ P.divisors) :
      |BoundingSieve.lambdaSquared w e| ≤
        (((pairs.filter fun x => Nat.lcm x.1 x.2 = e)).card : ℝ) := by
    let T := (e.divisors ×ˢ e.divisors).filter
      (fun x => x.1 ≤ L ∧ x.2 ≤ L ∧ e = Nat.lcm x.1 x.2)
    have hs : T ⊆ pairs.filter (fun x => Nat.lcm x.1 x.2 = e) := by
      intro x hx
      obtain ⟨hxdiv, hxL, hyL, hxe⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxdiv
      have heP := Nat.dvd_of_mem_divisors he
      have hP0 := (Nat.mem_divisors.mp he).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hxe.symm⟩
      · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors hx).trans heP, hP0⟩, hxL⟩
      · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors hy).trans heP, hP0⟩, hyL⟩
    calc
      _ ≤ ∑ a ∈ e.divisors, ∑ b ∈ e.divisors,
          |if e = Nat.lcm a b then w a * w b else 0| := by
        unfold BoundingSieve.lambdaSquared
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro a _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ e.divisors, ∑ b ∈ e.divisors,
          if a ≤ L ∧ b ≤ L ∧ e = Nat.lcm a b then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        by_cases ha : a ≤ L
        · by_cases hb : b ≤ L
          · by_cases hab : e = Nat.lcm a b
            · simp only [ha, hb, hab, and_self, if_true, abs_mul]
              simpa only [one_mul] using mul_le_mul (hw a) (hw b) (abs_nonneg _) zero_le_one
            · simp [hab]
          · rw [hcut b (Nat.lt_of_not_ge hb)]
            simp [hb]
        · rw [hcut a (Nat.lt_of_not_ge ha)]
          simp [ha]
      _ = (T.card : ℝ) := by
        rw [← Finset.sum_product, ← Finset.sum_filter]
        simp only [T, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hs
  have hmap : ∀ x ∈ pairs, Nat.lcm x.1 x.2 ∈ P.divisors := by
    intro x hx
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hx
    have hxP := (Finset.mem_filter.mp hx).1
    have hyP := (Finset.mem_filter.mp hy).1
    exact Nat.mem_divisors.mpr
      ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hxP) (Nat.dvd_of_mem_divisors hyP),
        (Nat.mem_divisors.mp hxP).2⟩
  have hf := Finset.card_eq_sum_card_fiberwise (s := pairs)
    (f := fun x => Nat.lcm x.1 x.2) (t := P.divisors) hmap
  have hU : U.card ≤ L := by
    calc
      _ ≤ (Finset.Icc 1 L).card := by
        apply Finset.card_le_card
        intro n hn
        obtain ⟨hnP, hnL⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hnP, hnL⟩
      _ = L := by simp
  calc
    _ ≤ ∑ e ∈ P.divisors,
        (((pairs.filter fun x => Nat.lcm x.1 x.2 = e)).card : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (pairs.card : ℝ) := by exact_mod_cast hf.symm
    _ = (U.card : ℝ) ^ 2 := by simp only [pairs, Finset.card_product, Nat.cast_mul, pow_two]
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hU) 2

theorem ordinaryRho_l1_le (N d z L : ℕ) (hL : 1 ≤ L) :
    (∑ e ∈ (sieveProduct (d * N) z).divisors, |ordinaryRho N d z L e|) ≤ (L : ℝ) ^ 2 :=
  lambdaSquared_l1_le_level_sq _ _ _
    (fun n => abs_finiteSelbergWeight_le_one (ordinarySkeleton (d * N) z) hL n)
    (fun n hn => finiteSelbergWeight_eq_zero_of_level (ordinarySkeleton (d * N) z) L n hn)

/-- The actual ordinary row error has no remaining progression-count norm. -/
theorem ordinaryRow_errSum_le_explicit (N d z L : ℕ) (hL : 1 ≤ L)
    (X : ℝ) (p q : ℕ) (hf : factorAllowed N p q) (hX : 0 ≤ X)
    (hd : 0 < d) (hNd : Nat.Coprime N d) :
    (ordinaryRowSieve N d z X p q).errSum
      (BoundingSieve.lambdaSquared (finiteSelbergWeight (ordinaryRowSieve N d z X p q) L)) ≤
      2 * (N.divisors.card : ℝ) * (L : ℝ) ^ 2 := by
  unfold BoundingSieve.errSum
  rw [ordinaryRow_weight_eq]
  change (∑ e ∈ (sieveProduct (d * N) z).divisors,
    |ordinaryRho N d z L e| * |(ordinaryRowSieve N d z X p q).rem e|) ≤ _
  calc
    _ ≤ ∑ e ∈ (sieveProduct (d * N) z).divisors,
        |ordinaryRho N d z L e| * (2 * (N.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left
        (ordinaryRow_abs_remainder_le_divisorCost hf hX hd hNd (Nat.dvd_of_mem_divisors he))
        (abs_nonneg _)
    _ = 2 * (N.divisors.card : ℝ) *
        (∑ e ∈ (sieveProduct (d * N) z).divisors, |ordinaryRho N d z L e|) := by
      rw [Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ordinaryRho_l1_le N d z L hL) (by positivity)

/-- Explicit finite upper bound on the ORIGINAL second-prime AP row,
uniform in both factor labels and the unchanged strict near-cap parameter.
The coefficient choice (N,d,z,L) precedes the selected row (X,p,q). -/
theorem actualPrimeRowAP_le_explicit_finite
    (N d z L : ℕ) (hL : 1 ≤ L) (X : ℝ) (p q : ℕ)
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) (hNd : Nat.Coprime N d) :
    ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      endpointMass N X p q d 1 / ordinaryG (d * N) z L +
        2 * (N.divisors.card : ℝ) * (L : ℝ) ^ 2 + (z : ℝ) := by
  have hs := siftedSum_le_finiteSelbergNormalizer_add_errSum
    (ordinaryRowSieve N d z X p q) hL
  rw [ordinaryRow_siftedSum, ordinaryRow_normalizer] at hs
  change ((siftedPreprimeRow N d z X p q).card : ℝ) ≤
    ((rowAPDiv N X p q d 1).card : ℝ) / ordinaryG (d * N) z L +
      (ordinaryRowSieve N d z X p q).errSum
        (BoundingSieve.lambdaSquared (finiteSelbergWeight (ordinaryRowSieve N d z X p q) L)) at hs
  rw [rowAPDiv_card_real_eq_endpointMass hf hX hd zero_lt_one] at hs
  have he := ordinaryRow_errSum_le_explicit N d z L hL X p q hf hX hd hNd
  have hp := actualPrimeRowAP_card_le_sifted_add_cap N d z X p q
  linarith

end
end ImbalancedChen.U9SemiprimeSwitch
