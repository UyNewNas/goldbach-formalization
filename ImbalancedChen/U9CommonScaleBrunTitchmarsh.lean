import ImbalancedChen.U9PrimitiveAPNoCentreUpper
import Mathlib.Data.Nat.Find

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A common external scale H=d*K^3 fixes z=K and L=K-1 BEFORE interval,
residue, original factors and near-cap mask. The genuine finite AP sieve
then gives a Brun--Titchmarsh-type upper with explicit constant15. A scale
bracket transfers this to a prescribed common H with constant120; that
bracket is a numerical pre-family choice, never a prime-count premise.
All original row endpoints remain literal and centre deletion is only an
upper inclusion. No strong currentK aggregation is asserted.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

private theorem primitiveAP_mass_le_common_cube (d K A B a : ℕ)
    (hd : 0 < d) (hwidth : (B : ℝ) - (A : ℝ) ≤ (d : ℝ) * (K : ℝ) ^ 3) :
    ((primitiveAPInterval A B d a).card : ℝ) ≤ (K : ℝ) ^ 3 + 1 := by
  by_cases hAB : A ≤ B
  · have h := divisorAPCount_discrepancy A B d a 1 hAB hd zero_lt_one (Nat.coprime_one_right d)
    have hraw : divisorAPCount A B d a 1 = ((primitiveAPInterval A B d a).card : ℝ) := by
      simp only [divisorAPCount, primitiveAPInterval, one_dvd, and_true]
    rw [hraw, Nat.cast_one, mul_one] at h
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hlength : ((B : ℝ) - A) / (d : ℝ) ≤ (K : ℝ) ^ 3 := by
      apply (div_le_iff₀ hdR).mpr
      nlinarith only [hwidth]
    have hi := (abs_le.mp h).2
    linarith
  · have hempty : Finset.Ico A B = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp only [primitiveAPInterval, hempty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The coefficient/cap choice depends only on the common scale K,d.
The bound is simultaneous in every interval and every moving residue. -/
theorem primitiveAPPrimes_common_cube_upper (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (A B a : ℕ) (hwidth : (B : ℝ) - (A : ℝ) ≤ (d : ℝ) * (K : ℝ) ^ 3) :
    ((primitiveAPPrimes A B d a).card : ℝ) ≤
      15 * ((d : ℝ) * (K : ℝ) ^ 3) /
        ((Nat.totient d : ℝ) * Real.log ((K : ℝ) ^ 3)) := by
  have hL : 1 ≤ K - 1 := by omega
  have hLz : K - 1 < K := by omega
  have hK1 : 1 ≤ K := by omega
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hlog : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith)
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : 1 ≤ (d : ℝ) / (Nat.totient d : ℝ) := by
    apply (le_div_iff₀ hphi).mpr
    simpa only [one_mul] using (show (Nat.totient d : ℝ) ≤ d by exact_mod_cast Nat.totient_le d)
  have hmain := primitiveAPPrimes_le_euler_log d K (K - 1) hd hL hLz A B a
  rw [Nat.sub_add_cancel hK1] at hmain
  have hmass := primitiveAP_mass_le_common_cube d K A B a hd hwidth
  have hcube : (1 : ℝ) ≤ (K : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hmass2 : ((primitiveAPInterval A B d a).card : ℝ) ≤ 2 * (K : ℝ) ^ 3 := by linarith
  have hmain2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass2 (div_nonneg hdR.le hphi.le)) hlog.le
  have hKm1 : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
  have hKm10 : (0 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq := pow_le_pow_left₀ hKm10 hKm1 2
  have hKsq : (K : ℝ) ≤ (K : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ K by linarith) hKpos.le
    nlinarith only [hmul]
  have herr : 2 * (((K - 1 : ℕ) : ℝ)) ^ 2 + (K : ℝ) ≤ 3 * (K : ℝ) ^ 2 := by linarith
  have hlogle : Real.log (K : ℝ) ≤ K :=
    (Real.log_le_sub_one_of_pos hKpos).trans (by linarith)
  have herr2 : 3 * (K : ℝ) ^ 2 ≤ 3 * (K : ℝ) ^ 3 / Real.log (K : ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogle (show 0 ≤ 3 * (K : ℝ) ^ 2 by positivity)]
  have herr3 : 3 * (K : ℝ) ^ 3 / Real.log (K : ℝ) ≤
      3 * ((d : ℝ) / (Nat.totient d : ℝ)) * (K : ℝ) ^ 3 / Real.log (K : ℝ) := by
    apply div_le_div_of_nonneg_right _ hlog.le
    nlinarith [mul_le_mul_of_nonneg_right hratio (show 0 ≤ 3 * (K : ℝ) ^ 3 by positivity)]
  calc
    _ ≤ 5 * ((d : ℝ) / (Nat.totient d : ℝ)) * (K : ℝ) ^ 3 / Real.log (K : ℝ) := by
      nlinarith [hmain, hmain2, herr, herr2, herr3]
    _ = _ := by
      rw [Real.log_pow]
      norm_num
      field_simp [hphi.ne', hlog.ne'] <;> ring

/-- An external common interval scale H admits the same pre-family
choice whenever H≤d*K³≤8H. No level is chosen after seeing a row mask. -/
theorem primitiveAPPrimes_common_scale_upper (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (H : ℝ) (hH : (d : ℝ) < H)
    (hscale : H ≤ (d : ℝ) * (K : ℝ) ^ 3 ∧ (d : ℝ) * (K : ℝ) ^ 3 ≤ 8 * H)
    (A B a : ℕ) (hwidth : (B : ℝ) - (A : ℝ) ≤ H) :
    ((primitiveAPPrimes A B d a).card : ℝ) ≤
      120 * H / ((Nat.totient d : ℝ) * Real.log (H / (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hHpos : 0 < H := hdR.trans hH
  have hY : 1 < H / (d : ℝ) := (lt_div_iff₀ hdR).mpr (by simpa using hH)
  have hlog : 0 < Real.log (H / (d : ℝ)) := Real.log_pos hY
  have hYle : H / (d : ℝ) ≤ (K : ℝ) ^ 3 := by
    apply (div_le_iff₀ hdR).mpr
    nlinarith only [hscale.1]
  have hlogle := Real.log_le_log (zero_lt_one.trans hY) hYle
  have hden : (Nat.totient d : ℝ) * Real.log (H / (d : ℝ)) ≤
      (Nat.totient d : ℝ) * Real.log ((K : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hlogle hphi.le
  have hbase := primitiveAPPrimes_common_cube_upper d K hd hK A B a (hwidth.trans hscale.1)
  have hdiv := div_le_div_of_nonneg_left
    (show 0 ≤ 15 * ((d : ℝ) * (K : ℝ) ^ 3) by positivity) (mul_pos hphi hlog) hden
  have hnum := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale.2 (by norm_num : (0 : ℝ) ≤ 15)) (mul_pos hphi hlog).le
  calc
    _ ≤ 15 * ((d : ℝ) * (K : ℝ) ^ 3) /
        ((Nat.totient d : ℝ) * Real.log (H / (d : ℝ))) := hbase.trans hdiv
    _ ≤ _ := by simpa only [← mul_assoc, show (15 : ℝ) * 8 = 120 by norm_num] using hnum

/-- An actual common-scale choice exists for EVERY H>d. Minimality of
the cube scale gives the factor-eight bracket, before any interval or
original factor family is quantified. No cube-root approximation is used. -/
theorem exists_common_scale_choice (d : ℕ) (hd : 0 < d) (H : ℝ) (hH : (d : ℝ) < H) :
    ∃ K : ℕ, 2 ≤ K ∧ H ≤ (d : ℝ) * (K : ℝ) ^ 3 ∧
      (d : ℝ) * (K : ℝ) ^ 3 ≤ 8 * H := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (H / (d : ℝ)))
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans hn.le
  have hnY : H / (d : ℝ) < n := (le_max_right _ _).trans_lt hn
  have hn3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    have hmul := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
    nlinarith only [hmul]
  have hex : ∃ k : ℕ, H ≤ (d : ℝ) * (k : ℝ) ^ 3 := by
    refine ⟨n, ?_⟩
    have hY : H / (d : ℝ) ≤ (n : ℝ) ^ 3 := hnY.le.trans hn3
    have hh := (div_le_iff₀ hdR).mp hY
    nlinarith only [hh]
  let K := Nat.find hex
  have hbound : H ≤ (d : ℝ) * (K : ℝ) ^ 3 := Nat.find_spec hex
  have hK : 2 ≤ K := by
    by_contra hnK
    have hc : K = 0 ∨ K = 1 := by omega
    rcases hc with hc | hc <;> norm_num [hc] at hbound <;> linarith
  have hprev : ¬ H ≤ (d : ℝ) * (((K - 1 : ℕ) : ℝ)) ^ 3 :=
    Nat.find_min hex (show K - 1 < K by omega)
  have hK2 : (K : ℝ) ≤ 2 * (((K - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show K ≤ 2 * (K - 1) by omega)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg K) hK2 3
  have hmul := mul_le_mul_of_nonneg_left hpow hdR.le
  refine ⟨K, hK, hbound, ?_⟩
  have hp := lt_of_not_ge hprev
  nlinarith [hmul]

/-- The bound is an upper inclusion on the literal original row; its
coupled square-root and strict near-cap endpoints are never replaced. -/
theorem originalPrimeRow_common_scale_upper (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (H : ℝ) (hH : (d : ℝ) < H)
    (hscale : H ≤ (d : ℝ) * (K : ℝ) ^ 3 ∧ (d : ℝ) * (K : ℝ) ^ 3 ≤ 8 * H)
    (N : ℕ) (X : ℝ) (p q : ℕ) (hf : factorAllowed N p q) (hX : 0 ≤ X)
    (hNd : Nat.Coprime N d)
    (hwidth : (rowUpper N p q : ℝ) - (rowLower N X p q : ℝ) ≤ H) :
    ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      120 * H / ((Nat.totient d : ℝ) * Real.log (H / (d : ℝ))) := by
  have hsub : ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      ((primitiveAPPrimes (rowLower N X p q) (rowUpper N p q) d
        (residue N (p * q) d)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (originalPrimeRow_subset_unmasked hf hX hd hNd)
  exact hsub.trans (primitiveAPPrimes_common_scale_upper d K hd hK H hH hscale
    (rowLower N X p q) (rowUpper N p q) (residue N (p * q) d) hwidth)

/-- One choice z=K,L=K-1 works simultaneously for the whole original
factor family at a prescribed common scale H (dyadic or otherwise). -/
theorem exists_level_before_original_row_family (d : ℕ) (hd : 0 < d)
    (H : ℝ) (hH : (d : ℝ) < H) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (N : ℕ) (X : ℝ) (p q : ℕ),
      factorAllowed N p q → 0 ≤ X → Nat.Coprime N d →
      (rowUpper N p q : ℝ) - (rowLower N X p q : ℝ) ≤ H →
      ((actualPrimeRowAP N X p q d).card : ℝ) ≤
        120 * H / ((Nat.totient d : ℝ) * Real.log (H / (d : ℝ))) := by
  obtain ⟨K, hK, hscale⟩ := exists_common_scale_choice d hd H hH
  refine ⟨K, hK, ?_⟩
  intro N X p q hf hX hNd hwidth
  exact originalPrimeRow_common_scale_upper d K hd hK H hH hscale N X p q hf hX hNd hwidth

end
end ImbalancedChen.U9SemiprimeSwitch
