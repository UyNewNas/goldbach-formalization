import ImbalancedChen.Part3DistributionTargets
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWLarge

/-!
# Removing auxiliary coprimality from an actual rough slot

This is the auxiliary-`k` removal step in section 5 of the frozen
`distribution-prime-product-completion-20261010.txt`.  Its error has no
Siegel--Walfisz premise.  The actual common carrier and complex coefficient
remain fixed on both sides.  A nonzero rough coefficient can be removed by
`(n,k)=1` only at a multiple of a prime divisor of `k` exceeding `z`.
Counting those positive multiples gives the explicit cost `2*tau(k)*H/z`.

The proof is simultaneous in the carrier, coefficient, both moduli and
residue.  It also allows every real Mellin frequency in this removal step.
The `k=1` rough-slot SW estimate is still a separate analytic obligation;
in particular no unrestricted rough coefficient is declared to satisfy SW.
The final large-modulus bound counts the actual progression directly and
uses the existing reciprocal-totient bound only to pay its exact mean.

This module is a proof candidate pending successful kernel validation.
Source-level API checks do not replace a Lean build or axiom inspection.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

/-- The auxiliary-coprimality discrepancy on one common finite carrier.
The main term is the literal coprime coefficient mass divided by `phi(q)`. -/
def auxiliarySWError (S : Finset ℕ) (α : ℕ → ℂ) (k q b : ℕ) : ℂ :=
  (∑ n ∈ S, if Nat.ModEq q n b ∧ Nat.Coprime n k then α n else 0) -
  (∑ n ∈ S, if Nat.Coprime n (k * q) then α n else 0) / (Nat.totient q : ℂ)

theorem MediumAtom.auxSWError_eq_auxiliarySWError (d : MediumAtom) (k q b : ℕ) :
    d.auxSWError k q b = auxiliarySWError d.alphaCarrier d.alpha k q b := by
  rfl

private theorem norm_sum_ite_and_not_coprime_le
    (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ‖∑ n ∈ S, if P n ∧ ¬Nat.Coprime n k then α n else 0‖ ≤
      ∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖ := by
  rw [Finset.sum_filter]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro n _
  by_cases hP : P n <;> by_cases hk : Nat.Coprime n k <;> simp [hP, hk]

/-- Abstract filter stability: the only possible change is the mass of
coefficients removed by the auxiliary coprimality filter.  No arithmetic
distribution estimate, roughness or coefficient bound is assumed here. -/
theorem auxiliarySWError_sub_one_norm_le_bad_mass
    (S : Finset ℕ) (α : ℕ → ℂ) (k q b : ℕ) (hq : 0 < q) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) := by
  let A : ℂ := ∑ n ∈ S,
    if Nat.ModEq q n b ∧ ¬Nat.Coprime n k then α n else 0
  let B : ℂ := ∑ n ∈ S,
    if Nat.Coprime n q ∧ ¬Nat.Coprime n k then α n else 0
  have hAP : (∑ n ∈ S, if Nat.ModEq q n b ∧ Nat.Coprime n k then α n else 0) =
      (∑ n ∈ S, if Nat.ModEq q n b then α n else 0) - A := by
    dsimp only [A]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hb : Nat.ModEq q n b <;> by_cases hk : Nat.Coprime n k <;> simp [hb, hk]
  have hmean : (∑ n ∈ S, if Nat.Coprime n (k * q) then α n else 0) =
      (∑ n ∈ S, if Nat.Coprime n q then α n else 0) - B := by
    dsimp only [B]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hqn : Nat.Coprime n q <;> by_cases hkn : Nat.Coprime n k <;>
      simp [Nat.coprime_mul_iff_right, hqn, hkn]
  have heq : auxiliarySWError S α k q b - auxiliarySWError S α 1 q b =
      -A + B / (Nat.totient q : ℂ) := by
    unfold auxiliarySWError
    rw [hAP, hmean]
    simp only [Nat.coprime_one_right_eq_true, and_true, one_mul]
    ring
  have hphi : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    have hphiNat : 1 ≤ Nat.totient q := Nat.totient_pos.mpr hq
    exact_mod_cast hphiNat
  have hA : ‖A‖ ≤ ∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖ :=
    norm_sum_ite_and_not_coprime_le S α k (fun n => Nat.ModEq q n b)
  have hB : ‖B / (Nat.totient q : ℂ)‖ ≤
      ∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖ := by
    calc
      _ = ‖B‖ / (Nat.totient q : ℝ) := by rw [norm_div, Complex.norm_natCast]
      _ ≤ ‖B‖ := div_le_self (norm_nonneg _) hphi
      _ ≤ _ := norm_sum_ite_and_not_coprime_le S α k (fun n => Nat.Coprime n q)
  rw [heq]
  calc
    _ ≤ ‖A‖ + ‖B / (Nat.totient q : ℂ)‖ := by
      simpa only [norm_neg] using norm_add_le (-A) (B / (Nat.totient q : ℂ))
    _ ≤ (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) +
        (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) := add_le_add hA hB
    _ = _ := by ring

/-- The removed mass is small for every one-bounded rough coefficient.
Only nonzero coefficients require rough support; the common carrier can
therefore remain the original full interval. -/
theorem sum_norm_not_coprime_le_rough
    (S : Finset ℕ) (α : ℕ → ℂ) (H k : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) ≤
      (k.primeFactors.card : ℝ) * (H : ℝ) / z := by
  let T := (S.filter (fun n => ¬Nat.Coprime n k)).filter (fun n => α n ≠ 0)
  let P := k.primeFactors.filter (fun p => z < (p : ℝ))
  have hmass : (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) =
      ∑ n ∈ T, ‖α n‖ := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnot
    have heq : α n = 0 := by
      by_contra hne
      exact hnot (mem_filter.mpr ⟨hn, hne⟩)
    simp only [heq, norm_zero]
  have hTS : T ⊆ S := by
    intro n hn
    exact (mem_filter.mp (mem_filter.mp hn).1).1
  have hcover : T ⊆ P.biUnion (fun p => (Finset.Ioc 0 H).filter (fun n => p ∣ n)) := by
    intro n hn
    obtain ⟨hnK, hne⟩ := mem_filter.mp hn
    obtain ⟨hnS, hnk⟩ := mem_filter.mp hnK
    obtain ⟨p, hp, hpn, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnk
    exact mem_biUnion.mpr ⟨p,
      mem_filter.mpr ⟨hp.mem_primeFactors hpk hk.ne', hrough n hnS hne p hp hpn⟩,
      mem_filter.mpr ⟨hS hnS, hpn⟩⟩
  have hcard : T.card ≤ ∑ p ∈ P, H / p := by
    calc
      _ ≤ (P.biUnion (fun p => (Finset.Ioc 0 H).filter (fun n => p ∣ n))).card :=
        card_le_card hcover
      _ ≤ ∑ p ∈ P, ((Finset.Ioc 0 H).filter (fun n => p ∣ n)).card := card_biUnion_le
      _ = _ := by simp only [Nat.Ioc_filter_dvd_card_eq_div]
  have hcardR : (T.card : ℝ) ≤ ∑ p ∈ P, ((H / p : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hPc : (P.card : ℝ) ≤ (k.primeFactors.card : ℝ) := by
    exact_mod_cast card_le_card (show P ⊆ k.primeFactors from filter_subset _ _)
  rw [hmass]
  calc
    _ ≤ ∑ _n ∈ T, (1 : ℝ) := sum_le_sum (fun n hn => hα n (hTS hn))
    _ = (T.card : ℝ) := by simp
    _ ≤ ∑ p ∈ P, ((H / p : ℕ) : ℝ) := hcardR
    _ ≤ ∑ _p ∈ P, (H : ℝ) / z := by
      apply sum_le_sum
      intro p hp
      exact (Nat.cast_div_le (m := H) (n := p)).trans
        (div_le_div_of_nonneg_left (Nat.cast_nonneg H) hz (mem_filter.mp hp).2.le)
    _ = (P.card : ℝ) * ((H : ℝ) / z) := by simp
    _ ≤ (k.primeFactors.card : ℝ) * ((H : ℝ) / z) :=
      mul_le_mul_of_nonneg_right hPc (div_nonneg (Nat.cast_nonneg H) hz.le)
    _ = _ := by ring

/-- The finite arithmetic removal bound, with the number of distinct
prime divisors retained before replacing it by the divisor count. -/
theorem auxiliarySWError_sub_one_norm_le_primeFactors
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.primeFactors.card : ℝ) * (H : ℝ) / z := by
  calc
    _ ≤ 2 * (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) :=
      auxiliarySWError_sub_one_norm_le_bad_mass S α k q b hq
    _ ≤ 2 * ((k.primeFactors.card : ℝ) * (H : ℝ) / z) :=
      mul_le_mul_of_nonneg_left (sum_norm_not_coprime_le_rough S α H k z hS hz hk hα hrough)
        (by norm_num)
    _ = _ := by ring

/-- A fixed divisor order `C0=1` pays the auxiliary `k`, uniformly in
every positive `k,q`, every residue, carrier and legal coefficient. -/
theorem auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z := by
  have hcard : (k.primeFactors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast card_le_card (show k.primeFactors ⊆ k.divisors by
      rw [Nat.primeFactors_eq_to_filter_divisors_prime]
      exact filter_subset _ _)
  refine (auxiliarySWError_sub_one_norm_le_primeFactors S α H k q b z
    hS hz hk hq hα hrough).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num))
      (Nat.cast_nonneg H)) hz.le

/-- Quantitative filter stability in the exact coprime-mean normalization.
The `k=1` error stays on the right; it is not inserted into admissibility. -/
theorem auxiliarySWError_norm_le_one_add
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b‖ ≤ ‖auxiliarySWError S α 1 q b‖ +
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z := by
  calc
    _ = ‖auxiliarySWError S α 1 q b +
        (auxiliarySWError S α k q b - auxiliarySWError S α 1 q b)‖ := by
      congr 1
      ring
    _ ≤ ‖auxiliarySWError S α 1 q b‖ +
        ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_left
      (auxiliarySWError_sub_one_norm_le S α H k q b z hS hz hk hq hα hrough) _

/-- The literal rough integer slot. -/
def roughOneSlot (z : ℝ) (n : ℕ) : ℂ := by
  classical
  exact if ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ) then 1 else 0

/-- The literal rough Möbius slot, with its sign retained. -/
def roughMoebiusSlot (z : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) * roughOneSlot z n

theorem roughOneSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughOneSlot z n‖ ≤ 1 := by
  unfold roughOneSlot
  split_ifs <;> norm_num

theorem roughOneSlot_support (z : ℝ) (n : ℕ) (hn : roughOneSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ) := by
  by_contra h
  exact hn (by simp [roughOneSlot, h])

theorem roughMoebiusSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughMoebiusSlot z n‖ ≤ 1 := by
  have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  unfold roughMoebiusSlot
  rw [norm_mul]
  simpa only [one_mul] using
    mul_le_mul hmu (roughOneSlot_norm_le z n) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem roughMoebiusSlot_support (z : ℝ) (n : ℕ) (hn : roughMoebiusSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ) := by
  apply roughOneSlot_support z n
  intro h
  apply hn
  simp only [roughMoebiusSlot, h, mul_zero]

theorem roughOneSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughOneSlot z) k q b -
      auxiliarySWError S (roughOneSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z :=
  auxiliarySWError_sub_one_norm_le S (roughOneSlot z) H k q b z hS hz hk hq
    (fun n _ => roughOneSlot_norm_le z n) (fun n _ hn => roughOneSlot_support z n hn)

theorem roughMoebiusSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughMoebiusSlot z) k q b -
      auxiliarySWError S (roughMoebiusSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z :=
  auxiliarySWError_sub_one_norm_le S (roughMoebiusSlot z) H k q b z hS hz hk hq
    (fun n _ => roughMoebiusSlot_norm_le z n)
    (fun n _ hn => roughMoebiusSlot_support z n hn)

/-- The removal estimate permits arbitrary real Mellin frequency.  Its
unit norm preserves the actual rough support; no frequency-dependent
threshold or constant appears in this finite estimate. -/
theorem auxiliarySWError_sub_one_norm_le_mellin
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z t : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) k q b -
      auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z := by
  apply auxiliarySWError_sub_one_norm_le S _ H k q b z hS hz hk hq
  · intro n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (mem_Ioc.mp (hS hn)).1
    have htwist : ‖(n : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos hnpos (Complex.I * (t : ℂ))
    simpa only [norm_mul, htwist, mul_one] using hα n hn
  · intro n hn hne p hp hpn
    apply hrough n hn _ p hp hpn
    intro hzero
    apply hne
    simp only [hzero, zero_mul]

private theorem card_filter_modEq_le_prefix
    (S : Finset ℕ) (H q b : ℕ) (hS : S ⊆ Finset.Ioc 0 H) (hq : 0 < q) :
    ((S.filter (fun n => Nat.ModEq q n b)).card : ℝ) ≤ (H : ℝ) / q + 2 := by
  have hsub : S.filter (fun n => Nat.ModEq q n b) ⊆
      (range (H + 1)).filter (fun n => Nat.ModEq q n b) := by
    intro n hn
    obtain ⟨hnS, hnb⟩ := mem_filter.mp hn
    exact mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (mem_Ioc.mp (hS hnS)).2), hnb⟩
  have hprefix : ((range (H + 1)).filter (fun n => Nat.ModEq q n b)).card ≤
      (H + 1) / q + 1 := by
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card (H + 1) hq b]
    split_ifs <;> omega
  have hcard : ((S.filter (fun n => Nat.ModEq q n b)).card : ℝ) ≤
      (((H + 1) / q : ℕ) : ℝ) + 1 := by
    exact_mod_cast (card_le_card hsub).trans hprefix
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have hqNat : 1 ≤ q := hq
    exact_mod_cast hqNat
  have hinv : (1 : ℝ) / q ≤ 1 := div_le_self zero_le_one hq1
  calc
    _ ≤ (((H + 1) / q : ℕ) : ℝ) + 1 := hcard
    _ ≤ ((H + 1 : ℕ) : ℝ) / q + 1 := add_le_add_right Nat.cast_div_le 1
    _ = (H : ℝ) / q + 1 / q + 1 := by rw [Nat.cast_add, Nat.cast_one, add_div]
    _ ≤ (H : ℝ) / q + 2 := by linarith only [hinv]

/-- A genuine large-modulus estimate for every one-bounded complex
coefficient on the same positive carrier.  In particular it applies to
rough one/Möbius slots and their unit twists.  The reciprocal-totient
supplier includes `q > H`; there is no upper modulus restriction and no
SW, roughness, or primitive-residue assumption in this bound. -/
theorem auxiliarySWError_norm_le_large_modulus
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ)
    (hS : S ⊆ Finset.Ioc 0 H) (hH : 3 ≤ H) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1) :
    ‖auxiliarySWError S α k q b‖ ≤ (H : ℝ) / q + 2 +
      (H : ℝ) * MathlibNt.SieveTheory.Richert1969.richertReciprocalTotientConstant *
        Real.log (H : ℝ) / (min q H : ℕ) := by
  have hAP : ‖∑ n ∈ S,
      if Nat.ModEq q n b ∧ Nat.Coprime n k then α n else 0‖ ≤ (H : ℝ) / q + 2 := by
    calc
      _ ≤ ∑ n ∈ S, ‖if Nat.ModEq q n b ∧ Nat.Coprime n k then α n else 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ S, if Nat.ModEq q n b then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro n hn
        by_cases hb : Nat.ModEq q n b <;> by_cases hk : Nat.Coprime n k <;>
          simp [hb, hk, hα n hn]
      _ = ((S.filter (fun n => Nat.ModEq q n b)).card : ℝ) := by
        rw [← sum_filter]
        simp
      _ ≤ _ := card_filter_modEq_le_prefix S H q b hS hq
  have hmass : ‖∑ n ∈ S, if Nat.Coprime n (k * q) then α n else 0‖ ≤ (H : ℝ) := by
    calc
      _ ≤ ∑ n ∈ S, ‖if Nat.Coprime n (k * q) then α n else 0‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ S, (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        by_cases h : Nat.Coprime n (k * q) <;> simp [h, hα n hn]
      _ = (S.card : ℝ) := by simp
      _ ≤ (H : ℝ) := by
        have hcard : S.card ≤ H := (card_le_card hS).trans_eq (by simp)
        exact_mod_cast hcard
  have hphi :=
    MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeSW_reciprocal_totient hH hq
  have hmean : ‖(∑ n ∈ S, if Nat.Coprime n (k * q) then α n else 0) /
      (Nat.totient q : ℂ)‖ ≤ (H : ℝ) *
        (MathlibNt.SieveTheory.Richert1969.richertReciprocalTotientConstant *
          Real.log (H : ℝ) / (min q H : ℕ)) := by
    rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
    exact mul_le_mul hmass hphi
      (div_nonneg zero_le_one (Nat.cast_nonneg _)) (Nat.cast_nonneg H)
  unfold auxiliarySWError
  calc
    _ ≤ ‖∑ n ∈ S, if Nat.ModEq q n b ∧ Nat.Coprime n k then α n else 0‖ +
        ‖(∑ n ∈ S, if Nat.Coprime n (k * q) then α n else 0) /
          (Nat.totient q : ℂ)‖ := norm_sub_le _ _
    _ ≤ (H : ℝ) / q + 2 + (H : ℝ) *
        (MathlibNt.SieveTheory.Richert1969.richertReciprocalTotientConstant *
          Real.log (H : ℝ) / (min q H : ℕ)) := add_le_add hAP hmean
    _ = _ := by ring

end

end ImbalancedChen.Part3
