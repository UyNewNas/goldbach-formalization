import ImbalancedChen.Part3ActualRamanujanSinglePrimeLevelSplit
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic

/-!
# Actual finite-prime Euler modification for a restricted Ramanujan Dirichlet series

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

A finite set S records the primes already excluded from the remaining
integer variable. The actual single-prime integer bijection preserves all
these exclusions when p is not in S. It therefore extracts the actual
local tail while inserting p into S. Finite induction over the actual
prime divisors of N gives a product of the restricted local tails times
the literal Dirichlet series on integers coprime to N.

The real/complex summability bounds remain the proved actual ones:
Re(w)>1 when n is nonzero and Re(w)>2 at zero frequency. All restrictions
and product rearrangements are dominated by those actual absolute series.
No local factor is divided out or assumed nonzero, and no infinite Euler
product or analytic continuation is asserted.
-/

namespace ImbalancedChen.Part3.ActualRamanujanFiniteLevelEulerSplit

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Finset Complex
open scoped BigOperators
open ImbalancedChen.Part3.ActualLevelDirichletFactors
open ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit

/-- The actual remaining integer is coprime to every previously extracted prime. -/
def avoids (S : Finset ℕ) (c : ℕ) : Prop := ∀ q ∈ S, q.Coprime c

@[simp] theorem avoids_empty (c : ℕ) : avoids ∅ c := by simp [avoids]

@[simp] theorem avoids_insert (S : Finset ℕ) (p c : ℕ) :
    avoids (insert p S) c ↔ p.Coprime c ∧ avoids S c := by simp [avoids]

/-- The actual prime-power multiplication preserves every accumulated
coprimality restriction; distinct prime factors are paid internally. -/
theorem avoids_prime_power_mul_iff {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hp : p.Prime) (hpS : p ∉ S)
    (k m : ℕ) : avoids S (p ^ k * m) ↔ avoids S m := by
  constructor
  · intro h q hq
    exact (Nat.coprime_mul_iff_right.mp (h q hq)).2
  · intro h q hq
    have hne : q ≠ p := by
      intro heq
      subst q
      exact hpS hq
    have hqp : q.Coprime p := (Nat.coprime_primes (hS q hq) hp).mpr hne
    exact Nat.coprime_mul_iff_right.mpr ⟨hqp.pow_right k, h q hq⟩

/-- Literal restricted arithmetic series with the accumulated exclusions. -/
def excludedSeries (S : Finset ℕ) (N : ℕ) (n : ℤ) (w : ℂ) : ℂ :=
  ∑' c : ℕ, if N ∣ c ∧ avoids S c then actualTerm n w c else 0

@[simp] theorem excludedSeries_empty (N : ℕ) (n : ℤ) (w : ℂ) :
    excludedSeries ∅ N n w = restrictedSeries N n w := by
  simp only [excludedSeries, avoids_empty, and_true, restrictedSeries]

theorem excludedSeries_norm_summable (S : Finset ℕ) (N : ℕ) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    Summable (fun c : ℕ => ‖if N ∣ c ∧ avoids S c then actualTerm n w c else 0‖) := by
  apply (actualTerm_norm_summable n w hw).of_nonneg_of_le (fun c => norm_nonneg _) ?_
  intro c
  split_ifs <;> simp only [norm_zero, le_rfl, norm_nonneg]

private theorem complement_sum_eq_excluded_insert
    (S : Finset ℕ) (p M : ℕ) (n : ℤ) (w : ℂ) :
    (∑' m : PrimeComplement p,
      if M ∣ m.1 ∧ avoids S m.1 then actualTerm n w m.1 else 0) =
        excludedSeries (insert p S) M n w := by
  let G : ℕ → ℂ := fun c => if M ∣ c ∧ avoids (insert p S) c then actualTerm n w c else 0
  have hsupport : Function.support G ⊆ {c : ℕ | p.Coprime c} := by
    intro c hc
    have hgood : M ∣ c ∧ avoids (insert p S) c := by
      by_contra hbad
      exact hc (by simp only [G, if_neg hbad])
    exact ((avoids_insert S p c).mp hgood.2).1
  have hpoint (m : PrimeComplement p) : G m.1 =
      (if M ∣ m.1 ∧ avoids S m.1 then actualTerm n w m.1 else 0) := by
    simp only [G, avoids_insert, m.2, true_and]
  calc
    _ = ∑' m : PrimeComplement p, G m.1 := tsum_congr (fun m => (hpoint m).symm)
    _ = ∑' c : ℕ, G c := tsum_subtype_eq_of_support_subset hsupport
    _ = _ := rfl

/-- Genuine one-prime extraction retaining all accumulated exclusions.
The bijection, coefficient multiplication and absolute product convergence
are each supplied, so this is an iteration identity without local division. -/
theorem excludedSeries_single_prime_split {S : Finset ℕ} {p M : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hp : p.Prime) (hpS : p ∉ S) (hM : p.Coprime M)
    (e : ℕ) (n : ℤ) (w : ℂ) (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    excludedSeries S (p ^ e * M) n w =
      localTail p n e ((p : ℂ) ^ (-w)) * excludedSeries (insert p S) M n w := by
  let F : ℕ → ℂ := fun c =>
    if p ^ e * M ∣ c ∧ avoids S c then actualTerm n w c else 0
  have hsupport : Function.support F ⊆ {c : ℕ | c ≠ 0 ∧ p ^ e ∣ c} := by
    intro c hc
    have hc0 : c ≠ 0 := by
      intro hzero
      apply hc
      simp [F, hzero]
    have hd : p ^ e * M ∣ c ∧ avoids S c := by
      by_contra hd
      exact hc (by simp only [F, if_neg hd])
    exact ⟨hc0, dvd_trans (dvd_mul_right (p ^ e) M) hd.1⟩
  have hraw := actualTerm_norm_summable n w hw
  have hlocal : Summable (fun j : ℕ => ‖actualTerm n w (p ^ (j + e))‖) :=
    hraw.comp_injective (fun a b hab => Nat.add_right_cancel ((Nat.pow_right_injective hp.one_lt) hab))
  have hcomplement : Summable (fun m : PrimeComplement p =>
      ‖if M ∣ m.1 ∧ avoids S m.1 then actualTerm n w m.1 else 0‖) := by
    apply (hraw.subtype (fun m : ℕ => p.Coprime m)).of_nonneg_of_le (fun m => norm_nonneg _) ?_
    intro m
    split_ifs <;> simp only [norm_zero, le_rfl, norm_nonneg]
  have hsub : (∑' c : PrimePowerCarrier p e, F c.1) = ∑' c : ℕ, F c :=
    tsum_subtype_eq_of_support_subset hsupport
  calc
    _ = ∑' c : PrimePowerCarrier p e, F c.1 := hsub.symm
    _ = ∑' t : ℕ × PrimeComplement p, F ((primePowerLevelEquiv hp e) t).1 :=
      ((primePowerLevelEquiv hp e).tsum_eq (fun c : PrimePowerCarrier p e => F c.1)).symm
    _ = ∑' t : ℕ × PrimeComplement p,
        actualTerm n w (p ^ (t.1 + e)) *
          (if M ∣ t.2.1 ∧ avoids S t.2.1 then actualTerm n w t.2.1 else 0) := by
      apply tsum_congr
      intro t
      rw [primePowerLevelEquiv_value]
      dsimp only [F]
      rw [level_constraint_iff hp hM e t.1 t.2,
        avoids_prime_power_mul_iff hS hp hpS (t.1 + e) t.2.1]
      by_cases hm : M ∣ t.2.1 ∧ avoids S t.2.1
      · rw [if_pos hm, if_pos hm]
        exact actualTerm_mul_of_coprime n w (t.2.2.pow_left (t.1 + e))
      · simp only [if_neg hm, mul_zero]
    _ = (∑' j : ℕ, actualTerm n w (p ^ (j + e))) *
        (∑' m : PrimeComplement p,
          if M ∣ m.1 ∧ avoids S m.1 then actualTerm n w m.1 else 0) :=
      (tsum_mul_tsum_of_summable_norm hlocal hcomplement).symm
    _ = localTail p n e ((p : ℂ) ^ (-w)) * excludedSeries (insert p S) M n w := by
      rw [complement_sum_eq_excluded_insert S p M n w]
      congr 1
      unfold localTail
      apply tsum_congr
      intro j
      exact actualTerm_prime_power n w p (j + e)

/-- Finite extraction theorem with an arbitrary disjoint accumulated
prime set. Zero exponents are allowed; no local factor needs to be nonzero. -/
theorem excludedSeries_finite_prime_extraction
    (E : ℕ → ℕ) (n : ℤ) (w : ℂ) (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) →
    ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → Disjoint S T →
      excludedSeries S (∏ p ∈ T, p ^ E p) n w =
        (∏ p ∈ T, localTail p n (E p) ((p : ℂ) ^ (-w))) * excludedSeries (S ∪ T) 1 n w := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro hT S hS hST
    simp only [prod_empty, union_empty, one_mul]
  | @insert p T hpT ih =>
    intro hT S hS hST
    have hp : p.Prime := hT p (mem_insert_self p T)
    have hTrest : ∀ q ∈ T, q.Prime := fun q hq => hT q (mem_insert_of_mem hq)
    have hpS : p ∉ S := by
      intro hpS
      exact (Finset.disjoint_left.mp hST hpS) (mem_insert_self p T)
    have hM : p.Coprime (∏ q ∈ T, q ^ E q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      have hne : p ≠ q := by intro heq; subst q; exact hpT hq
      exact ((Nat.coprime_primes hp (hTrest q hq)).mpr hne).pow_right (E q)
    have hSinsert : ∀ q ∈ insert p S, q.Prime := by
      intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hS q hq
    have hSTinsert : Disjoint (insert p S) T := by
      apply Finset.disjoint_left.mpr
      intro q hqS hqT
      rcases mem_insert.mp hqS with rfl | hqS
      · exact hpT hqT
      · exact (Finset.disjoint_left.mp hST hqS) (mem_insert_of_mem hqT)
    have hunion : insert p S ∪ T = S ∪ insert p T := by
      ext q
      simp only [mem_union, mem_insert]
      tauto
    calc
      _ = excludedSeries S (p ^ E p * ∏ q ∈ T, q ^ E q) n w := by rw [prod_insert hpT]
      _ = localTail p n (E p) ((p : ℂ) ^ (-w)) *
          excludedSeries (insert p S) (∏ q ∈ T, q ^ E q) n w :=
        excludedSeries_single_prime_split hS hp hpS hM (E p) n w hw
      _ = localTail p n (E p) ((p : ℂ) ^ (-w)) *
          ((∏ q ∈ T, localTail q n (E q) ((q : ℂ) ^ (-w))) *
            excludedSeries (insert p S ∪ T) 1 n w) := by
        rw [ih hTrest (insert p S) hSinsert hSTinsert]
      _ = (∏ q ∈ insert p T, localTail q n (E q) ((q : ℂ) ^ (-w))) *
          excludedSeries (S ∪ insert p T) 1 n w := by
        rw [hunion, prod_insert hpT]
        ring

/-- The accumulated actual prime exclusions equal ordinary coprimality
to the original positive level N, including the empty level-one case. -/
theorem avoids_primeFactors_iff_coprime (N : ℕ) (hN : N ≠ 0) (c : ℕ) :
    avoids N.primeFactors c ↔ N.Coprime c := by
  constructor
  · intro h
    rw [Nat.prod_primeFactors_pow_factorization hN]
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    exact (h p hp).pow_left (N.factorization p)
  · intro h p hp
    exact h.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)

/-- The literal complementary Dirichlet series, without an Euler quotient. -/
def coprimeSeries (N : ℕ) (n : ℤ) (w : ℂ) : ℂ :=
  ∑' c : ℕ, if N.Coprime c then actualTerm n w c else 0

/-- Absolute convergence of the literal coprime-complement series, with
the same actual frequency-dependent abscissa. -/
theorem coprimeSeries_norm_summable (N : ℕ) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    Summable (fun c : ℕ => ‖if N.Coprime c then actualTerm n w c else 0‖) := by
  apply (actualTerm_norm_summable n w hw).of_nonneg_of_le (fun c => norm_nonneg _) ?_
  intro c
  split_ifs <;> simp only [norm_zero, le_rfl, norm_nonneg]

theorem excludedSeries_primeFactors_one (N : ℕ) (hN : N ≠ 0) (n : ℤ) (w : ℂ) :
    excludedSeries N.primeFactors 1 n w = coprimeSeries N n w := by
  unfold excludedSeries coprimeSeries
  apply tsum_congr
  intro c
  simp only [one_dvd, true_and, avoids_primeFactors_iff_coprime N hN c]

/-- The true finite Euler modification at every positive level. The local
tails are the previously evaluated actual prime-power sums. The complement
is the actual coprime-to-N series, and no local factor is divided out. -/
theorem restrictedSeries_finite_level_product
    (N : ℕ) (hN : N ≠ 0) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    restrictedSeries N n w =
      (∏ p ∈ N.primeFactors, localTail p n (padicValNat p N) ((p : ℂ) ^ (-w))) *
        coprimeSeries N n w := by
  have hprod : (∏ p ∈ N.primeFactors, p ^ padicValNat p N) = N := by
    calc
      _ = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
        apply prod_congr rfl
        intro p hp
        rw [Nat.factorization_def N (Nat.prime_of_mem_primeFactors hp)]
      _ = N := (Nat.prod_primeFactors_pow_factorization hN).symm
  have h := excludedSeries_finite_prime_extraction (fun p => padicValNat p N) n w hw
    N.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    ∅ (by simp) (by simp)
  rw [hprod, excludedSeries_empty, empty_union, excludedSeries_primeFactors_one N hN n w] at h
  exact h

end

end ImbalancedChen.Part3.ActualRamanujanFiniteLevelEulerSplit