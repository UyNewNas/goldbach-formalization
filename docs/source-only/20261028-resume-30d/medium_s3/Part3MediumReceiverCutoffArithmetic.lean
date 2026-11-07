import ImbalancedChen.Part3MediumCanonicalFixedBlock
import ImbalancedChen.Part3MediumGlobalDyadicOwnership
import ImbalancedChen.Part3OriginalCanonicalS2Stages
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original rough convention is p>z, hence smooth p<=z. The earlier
strict-small receiver uses p<c, rough p>=c. They are EXACTLY compatible
at c=floor(z)+1/2, without a no-boundary-prime hypothesis and without
changing the original numerical z in any estimate. Prime powers remain
on their original side, even when z itself is a prime dividing a label.
-/
namespace ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3OriginalCanonicalS2Stages

/-- A receiver threshold between the two consecutive integer locations.
This translates integer support predicates; it is not a new analytic z. -/
def strictReceiverCutoff (z : ℝ) : ℝ := (Nat.floor z : ℝ) + 1 / 2

theorem nat_le_original_iff_lt_receiver (z : ℝ) (hz : 0 ≤ z) (p : ℕ) :
    (p : ℝ) ≤ z ↔ (p : ℝ) < strictReceiverCutoff z := by
  constructor
  · intro hp
    have hpNat : p ≤ Nat.floor z := Nat.le_floor hp
    have hpReal : (p : ℝ) ≤ (Nat.floor z : ℝ) := by exact_mod_cast hpNat
    dsimp [strictReceiverCutoff]
    linarith
  · intro hp
    have hpNat : p ≤ Nat.floor z := by
      by_contra hn
      have hsucc : Nat.floor z + 1 ≤ p := by omega
      have hsuccReal : (Nat.floor z : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hsucc
      dsimp [strictReceiverCutoff] at hp
      linarith
    exact (show (p : ℝ) ≤ (Nat.floor z : ℝ) by exact_mod_cast hpNat).trans (Nat.floor_le hz)

theorem original_lt_nat_iff_receiver_le (z : ℝ) (hz : 0 ≤ z) (p : ℕ) :
    z < (p : ℝ) ↔ strictReceiverCutoff z ≤ (p : ℝ) := by
  have h := not_congr (nat_le_original_iff_lt_receiver z hz p)
  simpa only [not_le, not_lt] using h

theorem receiver_ne_nat (z : ℝ) (p : ℕ) : (p : ℝ) ≠ strictReceiverCutoff z := by
  intro h
  rcases le_or_lt p (Nat.floor z) with hlo | hhi
  · have hloR : (p : ℝ) ≤ (Nat.floor z : ℝ) := by exact_mod_cast hlo
    dsimp [strictReceiverCutoff] at h
    linarith
  · have hhi' : Nat.floor z + 1 ≤ p := by omega
    have hhiR : (Nat.floor z : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hhi'
    dsimp [strictReceiverCutoff] at h
    linarith

private theorem prime_dvd_power_base {p a : ℕ} (hp : p.Prime) (e : ℕ)
    (h : p ∣ a ^ e) : p ∣ a := by
  revert h
  induction e with
  | zero =>
      intro h
      exact False.elim (hp.not_dvd_one h)
  | succ e ih =>
      intro h
      rw [pow_succ] at h
      rcases hp.dvd_mul.mp h with he | ha
      · exact ih he
      · exact ha

private theorem prime_dvd_finset_product {α : Type*} [DecidableEq α]
    (p : ℕ) (hp : p.Prime) (S : Finset α) (f : α → ℕ)
    (h : p ∣ ∏ a ∈ S, f a) : ∃ a ∈ S, p ∣ f a := by
  revert h
  induction S using Finset.induction_on with
  | empty =>
      intro h
      exact False.elim (hp.not_dvd_one h)
  | @insert a S ha ih =>
      intro h
      rw [prod_insert ha] at h
      rcases hp.dvd_mul.mp h with hpa | hpS
      · exact ⟨a, mem_insert_self _ _, hpa⟩
      · obtain ⟨b, hb, hpb⟩ := ih hpS
        exact ⟨b, mem_insert_of_mem hb, hpb⟩

/-- Every prime of a prime-power product comes from its displayed
prime support. Exponents may have arbitrary multiplicity. -/
private theorem prime_factor_of_prime_power_product
    (S : Finset ℕ) (e : ℕ → ℕ) (hS : ∀ r ∈ S, r.Prime)
    {p : ℕ} (hp : p ∈ (∏ r ∈ S, r ^ e r).primeFactors) : p ∈ S := by
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨r, hr, hpr⟩ := prime_dvd_finset_product p hpPrime S
    (fun r => r ^ e r) (Nat.dvd_of_mem_primeFactors hp)
  have hbase : p ∣ r := prime_dvd_power_base hpPrime (e r) hpr
  have heq : p = r := ((Nat.dvd_prime (hS r hr)).mp hbase).resolve_left hpPrime.ne_one
  exact heq.symm ▸ hr

/-- The original inclusive smooth factor satisfies the strict receiver
support, including the original boundary prime p=z. -/
theorem originalSmooth_supported_receiver (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    SmallPrimeSupportedAt (strictReceiverCutoff z) (zSmoothPart z n) := by
  let S := n.primeFactors.filter (fun p => (p : ℝ) ≤ z)
  have hS : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  constructor
  · exact prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)
  · intro p hp
    have hpS := prime_factor_of_prime_power_product S n.factorization hS hp
    exact (nat_le_original_iff_lt_receiver z hz p).mp (mem_filter.mp hpS).2

/-- The original strict rough factor satisfies the inclusive receiver
rough support. No original boundary prime can leak to the rough side. -/
theorem originalRough_supported_receiver (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    RoughPrimeSupportedAt (strictReceiverCutoff z) (zRoughPart z n) := by
  let S := n.primeFactors.filter (fun p => z < (p : ℝ))
  have hS : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  constructor
  · exact prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)
  · intro p hp
    have hpS := prime_factor_of_prime_power_product S n.factorization hS hp
    exact (original_lt_nat_iff_receiver_le z hz p).mp (mem_filter.mp hpS).2

/-- Exact bridge from original finite prime-power products to the earlier
primeFactorsList receiver, even when the original cutoff is a prime. -/
theorem original_pair_eq_strictReceiver (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    (zSmoothPart z n, zRoughPart z n) =
      (smoothPart (strictReceiverCutoff z) n, roughPart (strictReceiverCutoff z) n) := by
  by_cases hn : n = 0
  · subst n
    simp [zSmoothPart, zRoughPart, smoothPart, roughPart]
  · apply smallRough_factorization_unique
      (originalSmooth_supported_receiver z hz n)
      (originalRough_supported_receiver z hz n)
      (smoothPart_supported (strictReceiverCutoff z) n)
      (roughPart_supported (strictReceiverCutoff z) n)
    exact (zSmoothPart_mul_zRoughPart (Nat.pos_of_ne_zero hn) z).trans
      (smooth_mul_rough (strictReceiverCutoff z) hn).symm

theorem originalSmooth_eq_receiver (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    zSmoothPart z n = smoothPart (strictReceiverCutoff z) n :=
  congrArg Prod.fst (original_pair_eq_strictReceiver z hz n)

theorem originalRough_eq_receiver (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    zRoughPart z n = roughPart (strictReceiverCutoff z) n :=
  congrArg Prod.snd (original_pair_eq_strictReceiver z hz n)

/-- Original d,w labels are the same actual labels used by the global
canonical owner at the translated receiver threshold. -/
theorem originalLabelDW_eq_receiver (z : ℝ) (hz : 0 ≤ z) (q : ℕ × ℕ) :
    labelDW z q =
      (MediumGlobalDyadicOwnership20261028.actualD (strictReceiverCutoff z) q,
       MediumGlobalDyadicOwnership20261028.actualW (strictReceiverCutoff z) q) := by
  simp only [labelDW, originalSmooth_eq_receiver z hz, originalRough_eq_receiver z hz,
    MediumGlobalDyadicOwnership20261028.actualD,
    MediumGlobalDyadicOwnership20261028.actualW, canonicalFactor]

end
end ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
