import ImbalancedChen.Part3SmoothProgressionError
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Actual coprime and mixed progression gates for the common cutoff

These finite Mobius identities and CRT constructions are namespace-local
extractions of fixed goldbach 09b97db5764ade1246bfb77206baa1b124760958:
LiLiuPrereqFouvryMainTerm, CoprimeCount, Dispersion, ArithmeticPoisson and SmoothMainTerm.
No provider module from that smoothing chain is imported. All uniform
bounds use the proved local progression bound and local cutoffMass.

The scale, finite support, both moduli, invertible multiplier and reduced
signed residue are arbitrary. No error or coefficient budget is assumed.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

namespace CommonSmoothCutoff

theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
  simpa only [ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h

theorem coprime_indicator_eq_moebius {q : ℕ} (hq : q ≠ 0) (m : ℕ) :
    (if m.Coprime q then (1 : ℝ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  have hg : m.gcd q ≠ 0 :=
    (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hq)).ne'
  have hd : q.divisors.filter (fun d => d ∣ m) = (m.gcd q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq, hg, Nat.dvd_gcd_iff, and_comm]
  rw [← Finset.sum_filter, hd, sum_moebius_divisors]

theorem coprime_weight_eq_moebius
    (S : Finset ℕ) (w : ℕ → ℝ) {q : ℕ} (hq : q ≠ 0) :
    (∑ m ∈ S, if m.Coprime q then w m else 0) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ∑ m ∈ S, if d ∣ m then w m else 0 := by
  calc
    _ = ∑ m ∈ S,
        (∑ d ∈ q.divisors, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0) *
          w m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [← coprime_indicator_eq_moebius hq]
      split_ifs <;> simp
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> simp

def coprimePrefix (H q : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 H, if m.Coprime q then 1 else 0

theorem coprimePrefix_eq_divisor_sum (H : ℕ) {q : ℕ} (hq : q ≠ 0) :
    coprimePrefix H q =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (H / d : ℕ) := by
  rw [coprimePrefix, coprime_weight_eq_moebius (Ioc 0 H) (fun _ => 1) hq]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp [Nat.Ioc_filter_dvd_card_eq_div]

theorem coprimePrefix_period (q : ℕ) :
    coprimePrefix q q = (q.totient : ℝ) := by
  have hI : Ioc 0 q = Ico 1 (1 + q) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  unfold coprimePrefix
  simp_rw [Nat.coprime_comm]
  rw [← Finset.sum_filter, hI]
  simp [Nat.filter_coprime_Ico_eq_totient]

theorem moebius_density {q : ℕ} (hq : q ≠ 0) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      (q.totient : ℝ) / (q : ℝ) := by
  rw [← coprimePrefix_period, coprimePrefix_eq_divisor_sum q hq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  field_simp

theorem scaledDyadicCutoff_finset_coprime_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, q ≠ 0 →
      |(∑ m ∈ S, if m.Coprime q then scaledDyadicCutoff M m else 0) -
          (M * cutoffMass) * (q.totient : ℝ) / q| ≤ C * q.divisors.card := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_multiples_uniform_error
  refine ⟨C, hC, fun M hM S hS q hq ↦ ?_⟩
  calc
    _ = |∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ S, if d ∣ m then scaledDyadicCutoff M m else 0) -
          (M / d) * cutoffMass)| := by
      rw [coprime_weight_eq_moebius S _ hq, mul_div_assoc, ← moebius_density hq,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ S, if d ∣ m then scaledDyadicCutoff M m else 0) -
          (M / d) * cutoffMass)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, C := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa using mul_le_mul hmu (hbound M hM S hS d (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp [mul_comm]

theorem coprime_of_product_congruent {a : ℤ} {q m n : ℕ}
    (ha : Int.gcd a q = 1) (h : Int.ModEq q ((m : ℤ) * n) a) :
    m.Coprime q ∧ n.Coprime q := by
  have hg : Int.gcd ((m : ℤ) * n) q = 1 := by
    rw [← Int.gcd_emod ((m : ℤ) * n) q, h.eq, Int.gcd_emod, ha]
  have hmn : (m * n).Coprime q := by
    simpa [Int.gcd, Int.natAbs_mul] using hg
  exact Nat.coprime_mul_iff_left.mp hmn

theorem exists_progression_for_divisor_congruence {q d n : ℕ}
    (hd : d.Coprime q) (hn : n.Coprime q) (a : ℤ) :
    ∃ b : ℤ, ∀ m : ℕ,
      (d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a) ↔ Int.ModEq (q * d : ℕ) (m : ℤ) b := by
  obtain ⟨y, hy⟩ := Int.mod_coprime (Nat.coprime_mul_iff_left.mpr ⟨hd, hn⟩)
  obtain ⟨v, hv⟩ := Int.mod_coprime hn
  let b : ℤ := d * y * a
  have hb : Int.ModEq q (b * n) a := by
    simpa only [b, Nat.cast_mul, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm]
      using hy.mul_right a
  have hb0 : Int.ModEq d b 0 := Int.modEq_zero_iff_dvd.mpr ⟨y * a, by dsimp [b]; ring⟩
  refine ⟨b, fun m ↦ ?_⟩
  have hc : Int.ModEq q ((m : ℤ) * n) a ↔ Int.ModEq q (m : ℤ) b := by
    constructor
    · intro h
      have h' := (h.trans hb.symm).mul_right v
      have hm' : Int.ModEq q ((m : ℤ) * n * v) m := by
        simpa only [mul_assoc, mul_one] using hv.mul_left (m : ℤ)
      have hb' : Int.ModEq q (b * n * v) b := by
        simpa only [mul_assoc, mul_one] using hv.mul_left b
      exact hm'.symm.trans (h'.trans hb')
    · intro h
      exact (h.mul_right n).trans hb
  have hd' : d ∣ m ↔ Int.ModEq d (m : ℤ) b := by
    rw [← Int.natCast_dvd_natCast, ← Int.modEq_zero_iff_dvd]
    exact ⟨fun h ↦ h.trans hb0.symm, fun h ↦ h.trans hb0⟩
  rw [hc, hd', and_comm]
  exact Int.modEq_and_modEq_iff_modEq_mul (by simpa using hd.symm)

/-- A mixed divisibility/congruence sum is estimated using its constructed
residue class modulo `q * d`, not an assumed progression-count formula. -/
theorem scaledDyadicCutoff_finset_divisor_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q d n : ℕ, 0 < q → 0 < d → d.Coprime q → n.Coprime q → ∀ a : ℤ,
      |(∑ m ∈ S,
          if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then scaledDyadicCutoff M m else 0) -
        (M * cutoffMass / q) / d| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_progression_uniform_error
  refine ⟨C, hC, fun M hM S hS q d n hq hd hdq hn a ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_progression_for_divisor_congruence hdq hn a
  have h := hbound M hM S hS (q * d) (Nat.mul_pos hq hd) b
  simp_rw [← hb] at h
  have he : (M * cutoffMass / q) / d = M / (q * d : ℕ) * cutoffMass := by
    push_cast
    ring
  rw [he]
  exact h

/-- Finite Mobius inversion for the mixed term. Divisors sharing a factor with
`q` cannot occur because the product is congruent to a reduced residue. -/
theorem coprime_product_progression_weight_eq_moebius
    (S : Finset ℕ) (w : ℕ → ℝ) {q r n : ℕ} (hr : r ≠ 0)
    {a : ℤ} (ha : Int.gcd a q = 1) :
    (∑ m ∈ S, if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0) =
      ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q), (ArithmeticFunction.moebius d : ℝ) *
        ∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0 := by
  classical
  calc
    _ = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0 := by
      simp only [ite_and]
      exact coprime_weight_eq_moebius S
        (fun m ↦ if Int.ModEq q ((m : ℤ) * n) a then w m else 0) hr
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hdq : d.Coprime q
      · simp only [if_pos hdq]
      · rw [if_neg hdq]
        have hz : (∑ m ∈ S,
            if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro m _
          apply if_neg
          intro hm
          exact hdq (Nat.Coprime.of_dvd_left hm.1 (coprime_of_product_congruent ha hm.2).1)
        rw [hz, mul_zero]

/-- The smooth arithmetic V estimate, uniformly in the scale, both moduli,
the reduced residue, the invertible multiplier, and the finite support set. -/
theorem scaledDyadicCutoff_finset_coprime_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q r n : ℕ, 0 < q → r ≠ 0 → n.Coprime q → ∀ a : ℤ, Int.gcd a q = 1 →
      |(∑ m ∈ S, if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a
          then scaledDyadicCutoff M m else 0) -
        (M * cutoffMass / q) *
          ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
            (ArithmeticFunction.moebius d : ℝ) / d| ≤ C * r.divisors.card := by
  classical
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_divisor_progression_uniform_error
  refine ⟨C, hC, fun M hM S hS q r n hq hr hn a ha ↦ ?_⟩
  calc
    _ = |∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
        (ArithmeticFunction.moebius d : ℝ) *
          ((∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) - (M * cutoffMass / q) / d)| := by
      rw [coprime_product_progression_weight_eq_moebius S _ hr ha,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
        |(ArithmeticFunction.moebius d : ℝ) *
          ((∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) - (M * cutoffMass / q) / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ r.divisors.filter (fun d ↦ d.Coprime q), C := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdr, hdq⟩ := Finset.mem_filter.mp hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa using mul_le_mul hmu
        (hbound M hM S hS q d n hq (Nat.pos_of_mem_divisors hdr) hdq hn a)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = C * (r.divisors.filter (fun d ↦ d.Coprime q)).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_filter_le r.divisors (fun d ↦ d.Coprime q)) hC.le

private theorem totient_real_prod (n : ℕ) :
    (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (algebraMap ℚ ℝ) (Nat.totient_eq_mul_prod_factors n)
  simpa only [map_natCast, map_mul, map_sub, map_one, map_inv₀, map_prod] using h

/-- Only the squarefree divisors supported on primes coprime to `q` contribute. -/
theorem restricted_moebius_density_prod (q : ℕ) {r : ℕ} (hr : r ≠ 0) :
    (∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
      (ArithmeticFunction.moebius d : ℝ) / d) =
        ∏ p ∈ r.primeFactors.filter (fun p ↦ p.Coprime q), (1 - (p : ℝ)⁻¹) := by
  let t := r.primeFactors.filter (fun p ↦ p.Coprime q)
  let k := ∏ p ∈ t, p
  have ht : ∀ p ∈ t, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hk : k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦ (ht p hp).ne_zero
  have hkr : k ∣ r :=
    (Finset.prod_dvd_prod_of_subset t r.primeFactors id (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd r)
  have hkq : k.Coprime q :=
    Nat.Coprime.prod_left fun p hp ↦ (Finset.mem_filter.mp hp).2
  have hsub : k.divisors ⊆ r.divisors.filter (fun d ↦ d.Coprime q) := by
    intro d hd
    have hdk := Nat.dvd_of_mem_divisors hd
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdk.trans hkr, hr⟩, hkq.of_dvd_left hdk⟩
  have hsum :
      (∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
        (ArithmeticFunction.moebius d : ℝ) / d) =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) / d := by
    symm
    apply Finset.sum_subset hsub
    intro d hd hdk
    have hsf : ¬Squarefree d := by
      intro hsf
      apply hdk
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hk⟩
      rw [← Nat.prod_primeFactors_of_squarefree hsf]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hp,
            hpd.trans (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1), hr⟩,
          (Finset.mem_filter.mp hd).2.of_dvd_left hpd⟩
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  rw [hsum, moebius_density hk, totient_real_prod, Nat.primeFactors_prod ht]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  exact mul_div_cancel_left₀ _ hkR

/-- The exact finite arithmetic identity identifying the U and V zero modes. -/
theorem restricted_moebius_density {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    (∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
      (ArithmeticFunction.moebius d : ℝ) / d) / q =
        ((q * r).totient : ℝ) / ((q.totient : ℝ) * (q * r : ℕ)) := by
  have hfilter : r.primeFactors.filter (fun p ↦ p.Coprime q) =
      r.primeFactors \ q.primeFactors := by
    ext p
    by_cases hp : p ∈ r.primeFactors
    · simp only [Finset.mem_filter, Finset.mem_sdiff, hp, true_and,
        (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd,
        Nat.mem_primeFactors_of_ne_zero hq, Nat.prime_of_mem_primeFactors hp]
    · simp [hp]
  have hprod :
      (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) *
          (∏ p ∈ r.primeFactors \ q.primeFactors, (1 - (p : ℝ)⁻¹)) =
        ∏ p ∈ (q * r).primeFactors, (1 - (p : ℝ)⁻¹) := by
    rw [Nat.primeFactors_mul hq hr, ← Finset.prod_union
      (Finset.disjoint_left.mpr fun p hp hpd ↦ (Finset.mem_sdiff.mp hpd).2 hp),
      Finset.union_sdiff_self_eq_union]
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hqrR : ((q * r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero hq hr)
  have hphi : (q.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  rw [restricted_moebius_density_prod q hr, hfilter]
  apply (div_eq_div_iff hqR (mul_ne_zero hphi hqrR)).mpr
  rw [totient_real_prod q, totient_real_prod (q * r)]
  calc
    _ = ((q : ℝ) * (q * r : ℕ)) *
        ((∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ r.primeFactors \ q.primeFactors, (1 - (p : ℝ)⁻¹)) := by ring
    _ = _ := by rw [hprod]; ring

end CommonSmoothCutoff

end

end ImbalancedChen.Part3
