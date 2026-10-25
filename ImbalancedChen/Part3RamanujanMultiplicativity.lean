import ImbalancedChen.Part3CoprimeKloostermanCRT
import ImbalancedChen.P3FiniteKloostermanUnitScaling
import ImbalancedChen.Part3RamanujanSpecialCase
import ImbalancedChen.Part3PrimePowerRamanujanExact
import Mathlib.Data.Nat.Factorization.Induction

/-!
Source-only, 2026-10-25. UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual Ramanujan sum is invariant under multiplying its frequency by a
unit. This removes both genuine inverse twists in the coprime Kloosterman
CRT theorem and proves ordinary coprime multiplicativity. Pinned natural
factorization induction then evaluates every nonzero modulus as the
product of the explicit prime-power divisibility factors already proved.
No multiplicativity, Ramanujan, Mobius or gcd formula is an input.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.PrimePowerRamanujanSourceOnly

/-- Multiplication of the Ramanujan frequency by an actual unit permutes
the complete unit residues. The proof reuses actual Kloosterman scaling. -/
theorem ramanujan_unit_scaling {c : ℕ} [NeZero c]
    (n a : ℤ) (ha : IsUnit (a : ZMod c)) :
    ramanujan c (a * n) = ramanujan c n := by
  unfold ramanujan
  simpa only [mul_zero, zero_mul, mul_comm] using kloosterman_unit_scaling n 0 a ha

/-- Both canonical inverse twists in the CRT formula disappear from the
Ramanujan special case because each is an actual local unit. -/
theorem ramanujan_coprime_mul_nonzero {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (n : ℤ) :
    ramanujan (q * r) n = ramanujan q n * ramanujan r n := by
  have hleft : IsUnit (Nat.gcdB q r : ZMod q) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨(r : ZMod q), canonical_crt_twist_left h⟩
  have hright : IsUnit (Nat.gcdA q r : ZMod r) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨(q : ZMod r), canonical_crt_twist_right h⟩
  have hcrt := kloosterman_coprime_crt h n 0
  simp only [mul_zero] at hcrt
  change ramanujan (q * r) n =
    ramanujan q (Nat.gcdB q r * n) * ramanujan r (Nat.gcdA q r * n) at hcrt
  rw [ramanujan_unit_scaling n (Nat.gcdB q r) hleft,
    ramanujan_unit_scaling n (Nat.gcdA q r) hright] at hcrt
  exact hcrt

/-- Ordinary coprime multiplicativity, including the original empty
range convention at modulus zero. -/
theorem ramanujan_coprime_mul {q r : ℕ} (h : q.Coprime r) (n : ℤ) :
    ramanujan (q * r) n = ramanujan q n * ramanujan r n := by
  by_cases hq : q = 0
  · subst q
    simp [ramanujan, kloosterman]
  by_cases hr : r = 0
  · subst r
    simp [ramanujan, kloosterman]
  letI : NeZero q := ⟨hq⟩
  letI : NeZero r := ⟨hr⟩
  exact ramanujan_coprime_mul_nonzero h n

/-- Actual prime-power factorization of the Ramanujan sum at every
nonzero modulus, proved by pinned factorization induction. -/
theorem ramanujan_factorization (c : ℕ) (hc : c ≠ 0) (n : ℤ) :
    ramanujan c n = c.factorization.prod (fun p k => ramanujan (p ^ k) n) := by
  exact Nat.multiplicative_factorization (fun d => ramanujan d n)
    (fun q r h => ramanujan_coprime_mul h n) (ramanujan_modulus_one n) hc

/-- The exact local factor, written entirely with integer divisibility
and ordinary powers. It is p^(k-1)*(p-1), -p^(k-1), or zero. -/
def ramanujanPrimeFactor (n : ℤ) (p k : ℕ) : ℂ :=
  if ((p ^ k : ℕ) : ℤ) ∣ n then
    ((p ^ (k - 1) : ℕ) : ℂ) * ((p : ℂ) - 1)
  else if ((p ^ (k - 1) : ℕ) : ℤ) ∣ n then -((p ^ (k - 1) : ℕ) : ℂ) else 0

/-- Arbitrary-modulus explicit evaluation as a product of evaluated
prime-power factors. Every factor corresponds to a genuine positive
factorization exponent; no proposed gcd/Mobius formula is assumed. -/
theorem ramanujan_eq_explicit_primeFactor_product (c : ℕ) (hc : c ≠ 0) (n : ℤ) :
    ramanujan c n = c.factorization.prod (ramanujanPrimeFactor n) := by
  rw [ramanujan_factorization c hc n]
  apply Finsupp.prod_congr
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hp)
  have hk : c.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hexp : c.factorization p - 1 + 1 = c.factorization p :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
  unfold ramanujan ramanujanPrimeFactor
  simpa only [hexp] using
    primePower_ramanujan_exact p hprime (c.factorization p - 1) n

end ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
