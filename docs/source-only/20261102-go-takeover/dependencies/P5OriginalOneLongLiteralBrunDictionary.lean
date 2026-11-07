import ImbalancedChen.P5OriginalOneLongE5FiniteBudget
import ImbalancedChen.Part3TwoLongDivisorAxisClosure
import Mathlib.Data.Nat.GCD.BigOperators

-- UNCOMPILED_ZERO_CREDIT. Original literal B1/B2 divisor dictionary.
-- S is the actual IMAGE of truncated prime subsets, not a postulated carrier.

namespace ImbalancedChen
namespace OriginalOneLongLiteralBrunDictionary

noncomputable section
open Finset
open scoped BigOperators
open OriginalOneLongFiniteBrun OriginalOneLongSharpBrun OriginalOneLongE5FiniteBudget
open Part3.TwoLongActualBrunProfile Part3.TwoLongBrunLiteralDensity
open Part3.TwoLongDivisorAxisClosure

def truncated (P : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun A => A.card ≤ r)

def divisorSupport (P : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (truncated P r).image chartDivisor

def layerSupport (P : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (P.powersetCard r).image chartDivisor

def upperCoefficient (P : Finset ℕ) (h d : ℕ) : ℝ :=
  if d ∈ divisorSupport P h then (-1 : ℝ) ^ d.primeFactors.card else 0

def gapCoefficient (P : Finset ℕ) (r d : ℕ) : ℝ :=
  if d ∈ layerSupport P r then 1 else 0

theorem chartDivisor_positive (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    0 < chartDivisor A := by
  unfold chartDivisor
  exact Finset.prod_pos (fun p hp => (hA p hp).pos)

theorem chartDivisor_squarefree (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    Squarefree (chartDivisor A) := by
  unfold chartDivisor
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (hA p hp).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hA p hp) (hA q hq)).mpr hpq

-- The sign coefficient is the ORDINARY Mobius function on this actual
-- squarefree carrier, not a reweighted or independently normalized sieve.
theorem upperCoefficient_eq_moebius_on_support (P : Finset ℕ) (h r d : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hd : d ∈ divisorSupport P r) :
    upperCoefficient P h d =
      if d ∈ divisorSupport P h then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hd
  have hAP := mem_powerset.mp (mem_filter.mp hA).1
  have hs := chartDivisor_squarefree A (fun p hp => hP p (hAP hp))
  have hc : ArithmeticFunction.cardFactors (chartDivisor A) = (chartDivisor A).primeFactors.card := by
    rw [ArithmeticFunction.cardFactors_apply]
    simpa [Nat.primeFactors] using (List.toFinset_card_of_nodup hs.nodup_primeFactorsList).symm
  unfold upperCoefficient
  split_ifs
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hs, hc]
    norm_cast
  · rfl

theorem coefficient_bounds (P : Finset ℕ) (h r d : ℕ) :
    |upperCoefficient P h d| ≤ 1 ∧ 0 ≤ gapCoefficient P r d ∧ gapCoefficient P r d ≤ 1 := by
  constructor
  · unfold upperCoefficient
    split_ifs <;> simp
  · unfold gapCoefficient
    split_ifs <;> norm_num

theorem mem_support_product_iff (P A : Finset ℕ) (r : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) :
    chartDivisor A ∈ divisorSupport P r ↔ A.card ≤ r := by
  constructor
  · intro h
    obtain ⟨B, hB, he⟩ := mem_image.mp h
    obtain ⟨hBP, hBr⟩ := mem_filter.mp hB
    have hBA := chartDivisor_injective_on P B A hP (mem_powerset.mp hBP) hA he
    simpa [hBA] using hBr
  · intro h
    exact mem_image.mpr ⟨A, mem_filter.mpr ⟨mem_powerset.mpr hA, h⟩, rfl⟩

theorem mem_layer_product_iff (P A : Finset ℕ) (r : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) :
    chartDivisor A ∈ layerSupport P r ↔ A.card = r := by
  constructor
  · intro h
    obtain ⟨B, hB, he⟩ := mem_image.mp h
    have hBA := chartDivisor_injective_on P B A hP (mem_powersetCard.mp hB).1 hA he
    simpa [hBA] using (mem_powersetCard.mp hB).2
  · intro h
    exact mem_image.mpr ⟨A, mem_powersetCard.mpr ⟨hA, h⟩, rfl⟩

theorem upperCoefficient_product (P A : Finset ℕ) (h : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) :
    upperCoefficient P h (chartDivisor A) =
      if A.card ≤ h then (-1 : ℝ) ^ A.card else 0 := by
  unfold upperCoefficient
  rw [chartDivisor_primeFactors A (fun p hp => hP p (hA hp))]
  simp only [mem_support_product_iff P A h hP hA]

theorem gapCoefficient_product (P A : Finset ℕ) (r : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) :
    gapCoefficient P r (chartDivisor A) = if A.card = r then 1 else 0 := by
  unfold gapCoefficient
  rw [mem_layer_product_iff P A r hP hA]

theorem support_mono (P : Finset ℕ) {r s : ℕ} (hrs : r ≤ s) :
    divisorSupport P r ⊆ divisorSupport P s := by
  intro d hd
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hd
  exact mem_image.mpr ⟨A, mem_filter.mpr
    ⟨(mem_filter.mp hA).1, (mem_filter.mp hA).2.trans hrs⟩, rfl⟩

theorem layer_subset_support (P : Finset ℕ) (r : ℕ) :
    layerSupport P r ⊆ divisorSupport P r := by
  intro d hd
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hd
  obtain ⟨hAP, hcard⟩ := mem_powersetCard.mp hA
  exact mem_image.mpr ⟨A, mem_filter.mpr ⟨mem_powerset.mpr hAP, hcard.le⟩, rfl⟩

-- Products of DISTINCT chart primes divide n exactly when each prime does.
-- The n=0 case is retained, rather than being lost through primeFactors(0).
theorem chartDivisor_dvd_iff (A : Finset ℕ) (n : ℕ)
    (hA : ∀ p ∈ A, p.Prime) :
    chartDivisor A ∣ n ↔ ∀ p ∈ A, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    · have hsub : A ⊆ n.primeFactors := by
        intro p hp
        exact Nat.mem_primeFactors.mpr ⟨hA p hp, h p hp, hn⟩
      exact (Finset.prod_dvd_prod_of_subset A n.primeFactors id hsub).trans n.prod_primeFactors_dvd

theorem chartDivisor_coprime_iff (A : Finset ℕ) (q : ℕ)
    (hA : ∀ p ∈ A, p.Prime) :
    (chartDivisor A).Coprime q ↔ ∀ p ∈ A, ¬p ∣ q := by
  rw [chartDivisor, Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    exact (hA p hp).coprime_iff_not_dvd.mp (h p hp)
  · intro h p hp
    exact (hA p hp).coprime_iff_not_dvd.mpr (h p hp)

theorem sum_support_image (P : Finset ℕ) (r : ℕ) (f : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ d ∈ divisorSupport P r, f d) = ∑ A ∈ truncated P r, f (chartDivisor A) := by
  unfold divisorSupport
  rw [Finset.sum_image]
  intro A hA B hB he
  exact chartDivisor_injective_on P A B hP
    (mem_powerset.mp (mem_filter.mp hA).1) (mem_powerset.mp (mem_filter.mp hB).1) he

theorem sum_layer_image (P : Finset ℕ) (r : ℕ) (f : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ d ∈ layerSupport P r, f d) = ∑ A ∈ P.powersetCard r, f (chartDivisor A) := by
  unfold layerSupport
  rw [Finset.sum_image]
  intro A hA B hB he
  exact chartDivisor_injective_on P A B hP
    (mem_powersetCard.mp hA).1 (mem_powersetCard.mp hB).1 he

-- Exact upper-polynomial dictionary. The finite fiber count is by the
-- ORIGINAL subset cardinality, not a renamed unrestricted coefficient.
theorem upper_polynomial_literal (P : Finset ℕ) (h n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    polynomial (divisorSupport P (h + 1)) divisorMask (upperCoefficient P h) n =
      (subsetBrunPolynomial P n h : ℝ) := by
  have hs := support_mono P (Nat.le_succ h)
  have hprune :
      polynomial (divisorSupport P (h + 1)) divisorMask (upperCoefficient P h) n =
        ∑ d ∈ divisorSupport P h, (-1 : ℝ) ^ d.primeFactors.card * divisorMask d n := by
    unfold polynomial
    calc
      _ = ∑ d ∈ divisorSupport P h, upperCoefficient P h d * divisorMask d n :=
        (Finset.sum_subset hs (by
          intro d hd hnot
          simp [upperCoefficient, hnot])).symm
      _ = _ := Finset.sum_congr rfl (fun d hd => by simp [upperCoefficient, hd])
  rw [hprune, sum_support_image P h _ hP]
  have hterm : (∑ A ∈ truncated P h,
      (-1 : ℝ) ^ (chartDivisor A).primeFactors.card * divisorMask (chartDivisor A) n) =
      ∑ A ∈ truncated P h, if chartDivisor A ∣ n then (-1 : ℝ) ^ A.card else 0 := by
    apply Finset.sum_congr rfl
    intro A hA
    have hAP := mem_powerset.mp (mem_filter.mp hA).1
    rw [chartDivisor_primeFactors A (fun p hp => hP p (hAP hp))]
    by_cases hd : chartDivisor A ∣ n <;> simp [divisorMask, hd]
  rw [hterm]
  calc
    _ = ∑ k ∈ range (h + 1), ∑ A ∈ (truncated P h).filter (fun A => A.card = k),
        if chartDivisor A ∣ n then (-1 : ℝ) ^ A.card else 0 := by
      refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
      intro A hA
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hA).2)
    _ = ∑ k ∈ range (h + 1), ∑ A ∈ (P.filter (fun p => p ∣ n)).powersetCard k,
        (-1 : ℝ) ^ A.card := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext A
      simp only [mem_filter, truncated, mem_powerset, mem_powersetCard]
      constructor
      · rintro ⟨⟨⟨hAP, hAh⟩, hAk⟩, hd⟩
        refine ⟨?_, hAk⟩
        intro p hp
        exact mem_filter.mpr ⟨hAP hp,
          (chartDivisor_dvd_iff A n (fun p hp => hP p (hAP hp))).mp hd p hp⟩
      · rintro ⟨hAR, hAk⟩
        have hAP : A ⊆ P := fun p hp => (mem_filter.mp (hAR hp)).1
        refine ⟨⟨⟨hAP, by have := mem_range.mp hk; omega⟩, hAk⟩, ?_⟩
        exact (chartDivisor_dvd_iff A n (fun p hp => hP p (hAP hp))).mpr
          (fun p hp => (mem_filter.mp (hAR hp)).2)
    _ = _ := by simp [subsetBrunPolynomial]

theorem coefficient_gap_identity (j : ℕ) (P : Finset ℕ) (d : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hd : d ∈ divisorSupport P (2 * j + 1)) :
    gapCoefficient P (2 * j + 1) d = upperCoefficient P (2 * j) d -
      upperCoefficient P (2 * j + 1) d := by
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hd
  have hAP := mem_powerset.mp (mem_filter.mp hA).1
  have hAr := (mem_filter.mp hA).2
  rw [gapCoefficient_product P A _ hP hAP,
    upperCoefficient_product P A _ hP hAP, upperCoefficient_product P A _ hP hAP]
  by_cases hcard : A.card ≤ 2 * j
  · have hne : A.card ≠ 2 * j + 1 := by omega
    simp [hcard, hne, hAr]
  · have he : A.card = 2 * j + 1 := by omega
    simp [he, pow_add, pow_mul]

theorem rough_literal (P : Finset ℕ) (n : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    actualRough (chartDivisor P) n = (roughIndicator P n : ℝ) := by
  have hc : n.Coprime (chartDivisor P) ↔ (P.filter (fun p => p ∣ n)).card = 0 := by
    rw [Nat.coprime_comm, chartDivisor_coprime_iff P n hP]
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [actualRough, roughIndicator, smallDivisorCount, hc]

-- Exact reciprocal-density dictionary on the same physical integer support.
-- It includes the unit divisor and arbitrary deletion sets of q-primes.
theorem compatible_gap_literal (j : ℕ) (P : Finset ℕ) (q m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    compatibleGapDensity (divisorSupport P (2 * j + 1)) (gapCoefficient P (2 * j + 1)) q m =
      if m.Coprime q then reciprocalUpper j P q - reciprocalLower j P q else 0 := by
  by_cases hm : m.Coprime q
  · rw [if_pos hm, reciprocalBrunGap_eq]
    unfold compatibleGapDensity
    have hunit (d : ℕ) : (m * d).Coprime q ↔ d.Coprime q := by
      simp [Nat.coprime_mul_iff_left, hm]
    simp_rw [hunit]
    have hprune :
        (∑ d ∈ divisorSupport P (2 * j + 1),
          if d.Coprime q then gapCoefficient P (2 * j + 1) d / (d : ℝ) else 0) =
        ∑ d ∈ layerSupport P (2 * j + 1), if d.Coprime q then 1 / (d : ℝ) else 0 := by
      calc
        _ = ∑ d ∈ layerSupport P (2 * j + 1),
            if d.Coprime q then gapCoefficient P (2 * j + 1) d / (d : ℝ) else 0 :=
          (Finset.sum_subset (layer_subset_support P _) (by
            intro d hd hnot
            simp [gapCoefficient, hnot])).symm
        _ = _ := Finset.sum_congr rfl (fun d hd => by simp [gapCoefficient, hd])
    rw [hprune, sum_layer_image P (2 * j + 1) _ hP]
    have hfilter : (P.powersetCard (2 * j + 1)).filter (fun A => (chartDivisor A).Coprime q) =
        (survivingPrimes P q).powersetCard (2 * j + 1) := by
      ext A
      simp only [mem_filter, mem_powersetCard]
      constructor
      · rintro ⟨⟨hAP, hAr⟩, hc⟩
        refine ⟨?_, hAr⟩
        intro p hp
        exact mem_filter.mpr ⟨hAP hp,
          (chartDivisor_coprime_iff A q (fun p hp => hP p (hAP hp))).mp hc p hp⟩
      · rintro ⟨hAR, hAr⟩
        have hAP : A ⊆ P := fun p hp => (mem_filter.mp (hAR hp)).1
        exact ⟨⟨hAP, hAr⟩,
          (chartDivisor_coprime_iff A q (fun p hp => hP p (hAP hp))).mpr
            (fun p hp => (mem_filter.mp (hAR hp)).2)⟩
    rw [← Finset.sum_filter, hfilter]
    unfold reciprocalSymmetric
    apply Finset.sum_congr rfl
    intro A hA
    simp [reciprocalSubsetMass, chartDivisor, one_div, Finset.prod_inv_distrib, Nat.cast_prod]
  · rw [if_neg hm]
    unfold compatibleGapDensity
    apply Finset.sum_eq_zero
    intro d hd
    have hmd : ¬(m * d).Coprime q := fun h => hm (Nat.coprime_mul_iff_left.mp h).1
    simp [hmd]

-- Closes the pointwise B1 dictionary needed by the actual one-long theorem.
theorem actual_B1 (j : ℕ) (P : Finset ℕ) (n : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 ≤ polynomial (divisorSupport P (2 * j + 1)) divisorMask
      (upperCoefficient P (2 * j)) n - actualRough (chartDivisor P) n ∧
    polynomial (divisorSupport P (2 * j + 1)) divisorMask (upperCoefficient P (2 * j)) n -
      actualRough (chartDivisor P) n ≤
      polynomial (divisorSupport P (2 * j + 1)) divisorMask (gapCoefficient P (2 * j + 1)) n := by
  have hupper : polynomial (divisorSupport P (2 * j + 1)) divisorMask
      (upperCoefficient P (2 * j)) n = (brunUpper j P n : ℝ) := by
    rw [upper_polynomial_literal P (2 * j) n hP, subsetBrunPolynomial_eq]
    rfl
  have hlower : polynomial (divisorSupport P (2 * j + 1)) divisorMask
      (upperCoefficient P (2 * j + 1)) n = (brunLower j P n : ℝ) := by
    have he : polynomial (divisorSupport P (2 * j + 1)) divisorMask
        (upperCoefficient P (2 * j + 1)) n =
      polynomial (divisorSupport P (2 * j + 1 + 1)) divisorMask
        (upperCoefficient P (2 * j + 1)) n := by
      unfold polynomial
      exact Finset.sum_subset (support_mono P (Nat.le_succ (2 * j + 1))) (by
        intro d hd hnot
        simp [upperCoefficient, hnot])
    rw [he, upper_polynomial_literal P (2 * j + 1) n hP, subsetBrunPolynomial_eq]
    rfl
  have hgap : polynomial (divisorSupport P (2 * j + 1)) divisorMask
      (gapCoefficient P (2 * j + 1)) n =
      ((smallDivisorCount P n).choose (2 * j + 1) : ℝ) := by
    have he : polynomial (divisorSupport P (2 * j + 1)) divisorMask
        (gapCoefficient P (2 * j + 1)) n =
      polynomial (divisorSupport P (2 * j + 1)) divisorMask (upperCoefficient P (2 * j)) n -
      polynomial (divisorSupport P (2 * j + 1)) divisorMask (upperCoefficient P (2 * j + 1)) n := by
      unfold polynomial
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [coefficient_gap_identity j P d hP hd]
      ring
    rw [he, hupper, hlower, ← Int.cast_sub, brunGap_eq_choose, Int.cast_natCast]
  exact pointwise_B1_shared j P (divisorSupport P (2 * j + 1))
    (upperCoefficient P (2 * j)) (gapCoefficient P (2 * j + 1)) (chartDivisor P) n
    hupper (rough_literal P n hP) hgap

theorem actual_B2 (j : ℕ) (P : Finset ℕ) (q m : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    compatibleGapDensity (divisorSupport P (2 * j + 1)) (gapCoefficient P (2 * j + 1)) q m ≤
      brunEpsilon j P :=
  compatibleGapDensity_sharedB2 j P (divisorSupport P (2 * j + 1))
    (gapCoefficient P (2 * j + 1)) q m (compatible_gap_literal j P q m hP)

theorem support_positive_and_cap (P : Finset ℕ) (r Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hZ : 1 ≤ Z) (hcap : ∀ p ∈ P, p ≤ Z) :
    ∀ d ∈ divisorSupport P r, 0 < d ∧ d ≤ Z ^ r := by
  intro d hd
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hd
  have hAP := mem_powerset.mp (mem_filter.mp hA).1
  have hAr := (mem_filter.mp hA).2
  refine ⟨chartDivisor_positive A (fun p hp => hP p (hAP hp)), ?_⟩
  calc
    _ ≤ Z ^ A.card := by
      unfold chartDivisor
      calc
        _ ≤ ∏ _p ∈ A, Z := Finset.prod_le_prod' (fun p hp => hcap p (hAP hp))
        _ = _ := by simp
    _ ≤ Z ^ r := by gcongr

end
end OriginalOneLongLiteralBrunDictionary
end ImbalancedChen
