import ImbalancedChen.Part3TwoLongSmooth
import ImbalancedChen.Part3BrunDensity

namespace ImbalancedChen.Part3

noncomputable section

open Finset
open scoped BigOperators SchwartzMap FourierTransform

private theorem quotient_sum (S : Finset ℕ) {d : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ n ∈ twoLongQuotientCarrier S d, f (d * n)) =
      ∑ n ∈ S.filter (d ∣ ·), f n := by
  refine sum_bij (fun n _ => d * n) ?_ ?_ ?_ ?_
  · intro n hn
    exact mem_filter.mpr ⟨(mem_twoLongQuotientCarrier S hd).mp hn, dvd_mul_right d n⟩
  · intro n _ m _ h
    exact Nat.mul_left_cancel hd h
  · intro n hn
    obtain ⟨hnS, k, rfl⟩ := mem_filter.mp hn
    exact ⟨k, (mem_twoLongQuotientCarrier S hd).mpr hnS, rfl⟩
  · intros
    rfl

private theorem primitive_expansion_eq_sum
    (q : ℕ) (S D : Finset ℕ) (c : ℕ → ℂ) (F : ℝ → ℂ) (U : ℝ)
    (hD : ∀ d ∈ D, 0 < d) :
    (∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * part3DivisorExpansion D c n else 0) =
      ∑ d ∈ D with d.Coprime q, c d *
        ∑ n ∈ twoLongQuotientCarrier S d, if n.Coprime q then F ((n : ℝ) / (U / (d : ℝ))) else 0 := by
  classical
  have hexp (n : ℕ) : (if n.Coprime q then F ((n : ℝ) / U) * part3DivisorExpansion D c n else 0) =
      ∑ d ∈ D, if d ∣ n then c d * (if n.Coprime q then F ((n : ℝ) / U) else 0) else 0 := by
    by_cases hnq : n.Coprime q
    · simp only [if_pos hnq, part3DivisorExpansion, mul_sum]
      apply sum_congr rfl
      intro d _
      split_ifs <;> simp [mul_comm]
    · simp [hnq]
  simp only [hexp]
  rw [sum_comm, sum_filter]
  apply sum_congr rfl
  intro d hd
  by_cases hdq : d.Coprime q
  · rw [if_pos hdq, ← sum_filter, ← quotient_sum S (hD d hd), mul_sum]
    apply sum_congr rfl
    intro n _
    have hcop : (d * n).Coprime q ↔ n.Coprime q :=
      Nat.coprime_mul_iff_left.trans (and_iff_right hdq)
    simp only [hcop, Nat.cast_mul,
      div_div_eq_mul_div, mul_comm (d : ℝ) (n : ℝ)]
  · rw [if_neg hdq]
    apply sum_eq_zero
    intro n _
    by_cases hdn : d ∣ n
    · have hnq : ¬ n.Coprime q := fun hn => hdq (hn.coprime_dvd_left hdn)
      simp [hdn, hnq]
    · simp [hdn]

/-- Finite primitive mean with its exact signed reciprocal divisor density.
Every divisor term uses the original quotient carrier and its rescaled mesh. -/
theorem smoothProfile_primitiveDivisorMean_norm_le
    (q : ℕ) [NeZero q] (S D : Finset ℕ) (c : ℕ → ℂ) (F : 𝓢(ℝ, ℂ))
    {U : ℝ} (hU : 0 < U) (hD : ∀ d ∈ D, 0 < d)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2) :
    ‖(∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * part3DivisorExpansion D c n else 0) -
      ((q.totient : ℂ) * ((U / (q : ℝ)) • (𝓕 F) 0)) *
        (∑ d ∈ D with d.Coprime q, c d / (d : ℂ))‖ ≤
      (∑ d ∈ D with d.Coprime q, ‖c d‖) * (2 * C * (q.divisors.card : ℝ)) := by
  classical
  rw [primitive_expansion_eq_sum q S D c F U hD, mul_sum, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ d ∈ D with d.Coprime q, ‖c d‖ * (2 * C * (q.divisors.card : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 := hD d (mem_filter.mp hd).1
      have hsupport (n : ℕ) (hn : F ((n : ℝ) / (U / (d : ℝ))) ≠ 0) :
          n ∈ twoLongQuotientCarrier S d := by
        apply (mem_twoLongQuotientCarrier S hd0).mpr
        apply hS
        rwa [Nat.cast_mul, mul_comm (d : ℝ), ← div_div_eq_mul_div]
      have hmain : (q.totient : ℂ) * ((U / (q : ℝ)) • (𝓕 F) 0) * (c d / (d : ℂ)) =
          c d * ((q.totient : ℂ) * (((U / (d : ℝ)) / (q : ℝ)) • (𝓕 F) 0)) := by
        simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
        ring
      rw [hmain, ← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (smoothProfile_primitiveMean_norm_le q _ F (div_pos hU (Nat.cast_pos.mpr hd0))
          hFneg hsupport hC hF) (norm_nonneg _)
    _ = _ := by rw [sum_mul]

private theorem brunDivisors_filter_coprime (P : Finset ℕ) (h q : ℕ) :
    (brunDivisors P h).filter (fun d => d.Coprime q) =
      brunDivisors (P.filter fun p => p.Coprime q) h := by
  ext d
  constructor
  · intro hd
    obtain ⟨hd, hc⟩ := mem_filter.mp hd
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hd
    obtain ⟨hj, hu⟩ := mem_sigma.mp hu
    obtain ⟨hs, hcard⟩ := mem_powersetCard.mp hu
    exact mem_image.mpr ⟨u, mem_sigma.mpr ⟨hj, mem_powersetCard.mpr
      ⟨fun p hp => mem_filter.mpr ⟨hs hp, Nat.coprime_prod_left_iff.mp hc p hp⟩, hcard⟩⟩, rfl⟩
  · intro hd
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hd
    obtain ⟨hj, hu⟩ := mem_sigma.mp hu
    obtain ⟨hs, hcard⟩ := mem_powersetCard.mp hu
    exact mem_filter.mpr ⟨mem_image.mpr ⟨u, mem_sigma.mpr ⟨hj, mem_powersetCard.mpr
      ⟨fun p hp => (mem_filter.mp (hs hp)).1, hcard⟩⟩, rfl⟩,
      Nat.coprime_prod_left_iff.mpr fun p hp => (mem_filter.mp (hs hp)).2⟩

private theorem brunGapDivisors_filter_coprime (P : Finset ℕ) (h q : ℕ) :
    (brunGapDivisors P h).filter (fun d => d.Coprime q) =
      brunGapDivisors (P.filter fun p => p.Coprime q) h := by
  ext d
  constructor
  · intro hd
    obtain ⟨hd, hc⟩ := mem_filter.mp hd
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
    exact mem_image.mpr ⟨s, mem_powersetCard.mpr
      ⟨fun p hp => mem_filter.mpr ⟨hsub hp, Nat.coprime_prod_left_iff.mp hc p hp⟩, hcard⟩, rfl⟩
  · intro hd
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
    exact mem_filter.mpr ⟨mem_image.mpr ⟨s, mem_powersetCard.mpr
      ⟨fun p hp => (mem_filter.mp (hsub hp)).1, hcard⟩, rfl⟩,
      Nat.coprime_prod_left_iff.mpr fun p hp => (mem_filter.mp (hsub hp)).2⟩

private theorem smoothProfile_primitiveBrunMass_norm_le_of_density
    (q : ℕ) [NeZero q] (S D : Finset ℕ) (c : ℕ → ℂ) (F : 𝓢(ℝ, ℂ))
    {U : ℝ} (hU : 0 < U) {Y : ℕ} (hD : D ⊆ Icc 1 Y)
    (hc : ∀ d ∈ D, ‖c d‖ ≤ 1)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    {C G : ℝ} (hC : 0 ≤ C) (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ‖∑ d ∈ D with d.Coprime q, c d / (d : ℂ)‖ ≤ G) :
    ‖∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * part3DivisorExpansion D c n else 0‖ ≤
      (q.totient : ℝ) * (U / (q : ℝ)) * ‖(𝓕 F) 0‖ * G +
        (Y : ℝ) * (2 * C * (q.divisors.card : ℝ)) := by
  let s := ∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * part3DivisorExpansion D c n else 0
  let M := ((q.totient : ℂ) * ((U / (q : ℝ)) • (𝓕 F) 0)) *
    (∑ d ∈ D with d.Coprime q, c d / (d : ℂ))
  have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hnorm : (∑ d ∈ D with d.Coprime q, ‖c d‖) ≤ (Y : ℝ) := by
    have hcard : ((D.filter fun d => d.Coprime q).card : ℝ) ≤ Y := by
      exact_mod_cast (card_filter_le D (fun d => d.Coprime q)).trans
        ((card_le_card hD).trans_eq (by simp))
    calc
      _ ≤ ∑ d ∈ D with d.Coprime q, (1 : ℝ) :=
        sum_le_sum fun d hd => hc d (mem_filter.mp hd).1
      _ = ((D.filter fun d => d.Coprime q).card : ℝ) := by simp
      _ ≤ _ := hcard
  have hmain : ‖M‖ ≤ (q.totient : ℝ) * (U / (q : ℝ)) * ‖(𝓕 F) 0‖ * G := by
    dsimp only [M]
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_smul_of_nonneg (div_nonneg hU.le hqpos.le),
      ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hG (by positivity)
  have herr : ‖s - M‖ ≤ (Y : ℝ) * (2 * C * (q.divisors.card : ℝ)) :=
    (smoothProfile_primitiveDivisorMean_norm_le q S D c F hU
      (fun d hd => (mem_Icc.mp (hD hd)).1) hFneg hS hC hF).trans
      (mul_le_mul_of_nonneg_right hnorm (by positivity))
  change ‖s‖ ≤ _
  calc
    ‖s‖ = ‖(s - M) + M‖ := by rw [sub_add_cancel]
    _ ≤ ‖s - M‖ + ‖M‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [add_comm ‖s - M‖ ‖M‖]
      exact add_le_add hmain herr

/-- For one smooth factor, the primitive mass with the upper Brun weight and
its gap are controlled by the exact reciprocal densities after deleting the
primes dividing the physical modulus. -/
theorem smoothProfile_primitiveBrunFactors_norm_le
    (q : ℕ) [NeZero q] (S P : Finset ℕ) (z h : ℕ) (F : 𝓢(ℝ, ℂ))
    {U : ℝ} (hU : 0 < U) (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2) :
    let E := (∑ p ∈ P with p.Coprime q, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial
    let M := (q.totient : ℝ) * (U / (q : ℝ)) * ‖(𝓕 F) 0‖
    ‖∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * (brunProjector P h n : ℂ) else 0‖ ≤
        M * (1 + E) + (z : ℝ) ^ h * (2 * C * (q.divisors.card : ℝ)) ∧
    ‖∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) *
        ((brunProjector P h n - brunProjector P (h + 1) n : ℤ) : ℂ) else 0‖ ≤
        M * E + (z : ℝ) ^ (h + 1) * (2 * C * (q.divisors.card : ℝ)) := by
  let Pq := P.filter fun p => p.Coprime q
  have hprime (p : ℕ) (hp : p ∈ Pq) := (hP p (mem_filter.mp hp).1).1
  have hPprime (p : ℕ) (hp : p ∈ P) := (hP p hp).1
  let E := (∑ p ∈ Pq, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial
  have hupper (n : ℕ) : (brunProjector P h n : ℂ) =
      part3DivisorExpansion (brunDivisors P h) (fun d => (-1 : ℂ) ^ d.primeFactors.card) n := by
    simp only [brunProjector_eq_divisor_sum P h n hPprime, part3DivisorExpansion, Int.cast_sum,
      apply_ite ((↑) : ℤ → ℂ), Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_zero]
  have hgap (n : ℕ) : ((brunProjector P h n - brunProjector P (h + 1) n : ℤ) : ℂ) =
      part3DivisorExpansion (brunGapDivisors P h) (fun _ => (1 : ℂ)) n := by
    simp only [brunProjector_gap_eq_divisor_sum P h n hPprime hh, part3DivisorExpansion,
      Int.cast_sum, apply_ite ((↑) : ℤ → ℂ), Int.cast_one, Int.cast_zero]
  have hA : ‖∑ d ∈ brunDivisors P h with d.Coprime q, (-1 : ℂ) ^ d.primeFactors.card / (d : ℂ)‖ ≤
      1 + E := by
    rw [brunDivisors_filter_coprime]
    have hb := brunDensity_nonneg_le Pq h hprime hh
    let A : ℝ := ∑ d ∈ brunDivisors Pq h, (-1 : ℝ) ^ d.primeFactors.card / (d : ℝ)
    have heq : (A : ℂ) =
        ∑ d ∈ brunDivisors Pq h, (-1 : ℂ) ^ d.primeFactors.card / (d : ℂ) := by
      simp only [A, Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_pow,
        Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast]
    change ‖∑ d ∈ brunDivisors Pq h, (-1 : ℂ) ^ d.primeFactors.card / (d : ℂ)‖ ≤ 1 + E
    have hA0 : 0 ≤ A := hb.1
    rw [← heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
    exact hb.2
  have hB : ‖∑ d ∈ brunGapDivisors P h with d.Coprime q, (1 : ℂ) / (d : ℂ)‖ ≤ E := by
    rw [brunGapDivisors_filter_coprime]
    let B : ℝ := ∑ d ∈ brunGapDivisors Pq h, (d : ℝ)⁻¹
    have heq : (B : ℂ) =
        ∑ d ∈ brunGapDivisors Pq h, (1 : ℂ) / (d : ℂ) := by
      simp only [B, Complex.ofReal_sum, Complex.ofReal_inv, Complex.ofReal_natCast, one_div]
    change ‖∑ d ∈ brunGapDivisors Pq h, (1 : ℂ) / (d : ℂ)‖ ≤ E
    have hB0 : 0 ≤ B := sum_nonneg fun _ _ => by positivity
    rw [← heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0]
    exact brunGapDivisors_sum_reciprocal_le Pq h hprime
  dsimp only
  simp only [hupper, hgap]
  constructor
  · simpa only [Nat.cast_pow] using smoothProfile_primitiveBrunMass_norm_le_of_density q S _
      (fun d => (-1 : ℂ) ^ d.primeFactors.card) F hU (brunDivisors_subset_Icc P z h hz hP)
      (fun _ _ => by simp) hFneg hS hC hF hA
  · simpa only [Nat.cast_pow] using smoothProfile_primitiveBrunMass_norm_le_of_density q S _
      (fun _ => (1 : ℂ)) F hU (brunGapDivisors_subset_Icc P z h hz hP)
      (fun _ _ => by simp) hFneg hS hC hF hB

/-- A real nonnegative profile gives nonnegative primitive masses for both
Brun factors. The same conclusion holds for the real part of a profile. -/
theorem smoothProfile_primitiveBrunFactors_re_nonneg
    (q : ℕ) (S P : Finset ℕ) (h : ℕ) (F : ℝ → ℂ) (U : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hh : Even h)
    (hF : ∀ n ∈ S, 0 ≤ (F ((n : ℝ) / U)).re) :
    0 ≤ (∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * (brunProjector P h n : ℂ) else 0).re ∧
    0 ≤ (∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) *
      ((brunProjector P h n - brunProjector P (h + 1) n : ℤ) : ℂ) else 0).re := by
  have hweight (b : ℕ → ℤ) (hb : ∀ n ∈ S, 0 ≤ b n) :
      0 ≤ (∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * (b n : ℂ) else 0).re := by
    rw [Complex.re_sum]
    apply sum_nonneg
    intro n hn
    by_cases hnq : n.Coprime q
    · simp only [if_pos hnq, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero]
      exact mul_nonneg (hF n hn) (by exact_mod_cast hb n hn)
    · simp only [if_neg hnq, Complex.zero_re, le_refl]
  refine ⟨hweight _ fun n _ => ?_, hweight _ fun n _ => ?_⟩
  · have hR : 0 ≤ brunRoughIndicator P n := by
      unfold brunRoughIndicator
      split_ifs <;> norm_num
    exact hR.trans (brunProjector_brackets P h n hP hh).2.1
  · obtain ⟨hL, hU, _⟩ := brunProjector_brackets P h n hP hh
    exact sub_nonneg.mpr (hL.trans hU)

end

end ImbalancedChen.Part3
