import ImbalancedChen.Part3FixedMarkPrimeWeilBridge
import ImbalancedChen.Part3CoprimeKloostermanCRT
import ImbalancedChen.Part3TwoLongInternalP2Modes
import ImbalancedChen.DivisorMomentBudget
import ImbalancedChen.P4BOriginalFiniteSmoothCount
import Mathlib.Data.Nat.Factorization.Induction

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The exact complete Kloosterman sum at the ORIGINAL physical modulus has
a squarefree Weil bound from the existing prime theorem and literal CRT.
Both integer frequencies, including zero, retain their common gcd.
No prime-power Weil theorem or CompositeWeilInput is asserted.
The final specialization derives squarefreeness from the actual P4 Q.
This must not be used at a transformed modulus c^2*d without its own proof.
-/
namespace ImbalancedChen.P4BOriginalSquarefreeWeil
noncomputable section
open Classical
open scoped BigOperators
open Part3.OriginalSmoothPoissonTail
open Part3.FixedMarkHalfTail20261115
open Part3.TwoLongInternalP2Modes (primitive_center_gcd)
open P4BOriginalFiniteSmoothCount (Q)

def budget (q : ℕ) (m n : ℤ) : ℝ :=
  (q.divisors.card : ℝ) * Real.sqrt (q : ℝ) *
    Real.sqrt (Nat.gcd (Nat.gcd m.natAbs n.natAbs) q : ℝ)

theorem budget_nonneg (q : ℕ) (m n : ℤ) : 0 ≤ budget q m n := by
  unfold budget
  positivity

theorem prime_budget {p : ℕ} (hp : p.Prime) (m n : ℤ) :
    ‖kloosterman p m n‖ ≤ budget p m n := by
  have hcard : (p.divisors.card : ℝ) = 2 := by
    simp [hp.divisors, hp.ne_one, hp.ne_one.symm]
  have hgpos : 0 < Nat.gcd (Nat.gcd m.natAbs n.natAbs) p :=
    Nat.gcd_pos_of_pos_right _ hp.pos
  have hgOne : 1 ≤ Real.sqrt (Nat.gcd (Nat.gcd m.natAbs n.natAbs) p : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hgpos)
  by_cases hm : (p : ℤ) ∣ m
  · by_cases hn : (p : ℤ) ∣ n
    · have hmN : p ∣ m.natAbs := by
        have hcast : (p : ℤ) ∣ m ↔ p ∣ m.natAbs := by
          rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
        exact hcast.mp hm
      have hnN : p ∣ n.natAbs := by
        have hcast : (p : ℤ) ∣ n ↔ p ∣ n.natAbs := by
          rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
        exact hcast.mp hn
      have hg : Nat.gcd (Nat.gcd m.natAbs n.natAbs) p = p :=
        Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
          (Nat.dvd_gcd (Nat.dvd_gcd hmN hnN) (dvd_refl _))
      have ht := kloosterman_norm_le p m n
      have hs := Real.mul_self_sqrt (Nat.cast_nonneg p)
      unfold budget
      rw [hcard, hg]
      nlinarith
    · have hswap : kloosterman p m n = kloosterman p n m := by
        letI : Fact p.Prime := ⟨hp⟩
        rw [physical_eq_prime, physical_eq_prime]
        exact KloostermanWeil.kloostermanSumPrime_comm p _ _
      rw [hswap]
      exact (prime_physical_sqrt hp n m hn).trans (by
        unfold budget
        rw [hcard]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hgOne (by positivity : 0 ≤ 2 * Real.sqrt (p : ℝ)))
  · exact (prime_physical_sqrt hp m n hm).trans (by
      unfold budget
      rw [hcard]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hgOne (by positivity : 0 ≤ 2 * Real.sqrt (p : ℝ)))

theorem budget_unit_twist {q : ℕ} (hq : 0 < q) (u m n : ℤ)
    (hu : IsUnit (u : ZMod q)) : budget q (u*m) (u*n) = budget q m n := by
  unfold budget
  rw [primitive_center_gcd hq u m (u*n) hu,
    Nat.gcd_comm m.natAbs (u*n).natAbs,
    primitive_center_gcd hq u n m hu,
    Nat.gcd_comm n.natAbs m.natAbs]

theorem budget_coprime {q r : ℕ} (hsq : Squarefree (q*r)) (hc : q.Coprime r)
    (m n : ℤ) : budget (q*r) m n = budget q m n * budget r m n := by
  have hq := hsq.of_mul_left
  have hr := hsq.of_mul_right
  have htau : ((q*r).divisors.card : ℝ) =
      (q.divisors.card : ℝ) * (r.divisors.card : ℝ) := by
    rw [squarefree_divisors_card_eq_prod_two hsq,
      squarefree_divisors_card_eq_prod_two hq,
      squarefree_divisors_card_eq_prod_two hr,
      Nat.primeFactors_mul hq.ne_zero hr.ne_zero,
      Finset.prod_union hc.disjoint_primeFactors]
  have hg := hc.gcd_mul (Nat.gcd m.natAbs n.natAbs)
  unfold budget
  rw [htau, hg]
  simp only [Nat.cast_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg q),
    Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd (Nat.gcd m.natAbs n.natAbs) q))]
  ring

/-- All squarefree moduli, with no parity or nonzero-frequency exclusions.
In particular q=1 and p=2 are included. -/
theorem squarefree_weil (q : ℕ) (hsq : Squarefree q) (m n : ℤ) :
    ‖kloosterman q m n‖ ≤ budget q m n := by
  revert hsq m n
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero =>
      intro hsq
      exact (hsq.ne_zero rfl).elim
  | one =>
      intro _ m n
      simpa [budget] using kloosterman_norm_le 1 m n
  | prime_pow p j hp hj =>
      intro hsq m n
      have hj1 : j = 1 := by
        by_contra hj1
        have htwo : 2 ≤ j := by omega
        have hdiv : p*p ∣ p^j := by
          simpa only [pow_two] using pow_dvd_pow p htwo
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hdiv
      subst j
      simpa only [pow_one] using prime_budget hp m n
  | coprime q r hq hr hc ihq ihr =>
      intro hsq m n
      letI : NeZero q := ⟨by omega⟩
      letI : NeZero r := ⟨by omega⟩
      let u : ℤ := Nat.gcdB q r
      let v : ℤ := Nat.gcdA q r
      have hu : IsUnit (u : ZMod q) :=
        .of_mul_eq_one _ (CoprimeCRTSourceOnly.canonical_crt_twist_left hc)
      have hv : IsUnit (v : ZMod r) :=
        .of_mul_eq_one _ (CoprimeCRTSourceOnly.canonical_crt_twist_right hc)
      rw [CoprimeCRTSourceOnly.kloosterman_coprime_crt hc, norm_mul,
        budget_coprime hsq hc]
      change ‖kloosterman q (u*m) (u*n)‖ * ‖kloosterman r (v*m) (v*n)‖ ≤ _
      have hQ := ihq hsq.of_mul_left (u*m) (u*n)
      have hR := ihr hsq.of_mul_right (v*m) (v*n)
      rw [budget_unit_twist (by omega) u m n hu] at hQ
      rw [budget_unit_twist (by omega) v m n hv] at hR
      exact mul_le_mul hQ hR (norm_nonneg _) (budget_nonneg _ _ _)

/-- This is the original sieve modulus itself. Nothing is inferred about
the squarefreeness of any Poisson modulus outside this Q. -/
theorem actual_Q_weil (omega : ℝ) (N : ℕ) {q : ℕ} (hq : q ∈ Q omega N)
    (m n : ℤ) : ‖kloosterman q m n‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q : ℝ) *
        Real.sqrt (Nat.gcd (Nat.gcd m.natAbs n.natAbs) q : ℝ) :=
  squarefree_weil q (P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hq) m n

end
end ImbalancedChen.P4BOriginalSquarefreeWeil
