import ImbalancedChen.P0RamanujanPrimePowerValues
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual Ramanujan sum is identified with the Dirichlet convolution of
Moebius and the divisor-gated identity function. The gate is proved
multiplicative from coprime divisibility. Mathlib's multiplicative-function
convolution theorem and prime-power induction then supply the quantitative
bound |ramanujan(c,n)| <= gcd(c,|n|) for every modulus c, including zero.
No CRT, assumed multiplicativity, or assumed final bound is used.
-/

namespace ImbalancedChen.Part3.RamanujanMultiplicativeGcdBound20261025a

noncomputable section

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanGeneralGcdIdentity20261025a
open ImbalancedChen.Part3.RamanujanPrimePowerValues20261025a

/-- The exact identity function restricted to divisors of the fixed
absolute integer frequency. Its value at zero is always zero. -/
def divisorGatedId (N : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d ∣ N then (d : ℂ) else 0, by simp⟩

/-- Coprime divisibility makes the gate multiplicative, including N=0. -/
theorem divisorGatedId_isMultiplicative (N : ℕ) :
    (divisorGatedId N).IsMultiplicative := by
  classical
  constructor
  · simp [divisorGatedId]
  · intro a b hab
    have hdiv : a * b ∣ N ↔ a ∣ N ∧ b ∣ N := by
      constructor
      · intro h
        have ha : a ∣ a * b := ⟨b, rfl⟩
        have hb : b ∣ a * b := ⟨a, by ring⟩
        exact ⟨dvd_trans ha h, dvd_trans hb h⟩
      · intro h
        exact hab.mul_dvd_of_dvd_of_dvd h.1 h.2
    change (if a * b ∣ N then ((a * b : ℕ) : ℂ) else 0) =
      (if a ∣ N then (a : ℂ) else 0) *
        (if b ∣ N then (b : ℂ) else 0)
    by_cases ha : a ∣ N <;> by_cases hb : b ∣ N <;>
      simp [hdiv, ha, hb, Nat.cast_mul]

/-- A concrete arithmetic function, rather than an assumed supplier of
the Ramanujan sum or its multiplicativity. -/
def ramanujanArithmetic (N : ℕ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ) * divisorGatedId N

theorem ramanujanArithmetic_isMultiplicative (N : ℕ) :
    (ramanujanArithmetic N).IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.mul
    ArithmeticFunction.isMultiplicative_moebius.intCast
    (divisorGatedId_isMultiplicative N)

/-- The convolution evaluates to the literal project Ramanujan sum.
At c=0 both sides vanish; all positive levels use the established exact
divisor formula, with signed divisibility converted through natAbs. -/
theorem ramanujanArithmetic_apply (c : ℕ) (n : ℤ) :
    ramanujanArithmetic n.natAbs c = ramanujan c n := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [ramanujanArithmetic, ramanujan, kloosterman]
  letI : NeZero c := ⟨hc⟩
  rw [ramanujanArithmetic, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal', ramanujan_eq_moebius_divisor_sum]
  apply sum_congr rfl
  intro d _hd
  have hdiv : (d : ℤ) ∣ n ↔ d ∣ n.natAbs := by
    rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
  simp only [divisorGatedId, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, hdiv]
  by_cases hd : d ∣ n.natAbs <;> simp [hd]

/-- Actual coprime-modulus multiplicativity derived via finite Dirichlet
convolution. The proof does not invoke the separate CRT source. -/
theorem ramanujan_mul_of_coprime (n : ℤ) {a b : ℕ} (hab : a.Coprime b) :
    ramanujan (a * b) n = ramanujan a n * ramanujan b n := by
  calc
    ramanujan (a * b) n = ramanujanArithmetic n.natAbs (a * b) :=
      (ramanujanArithmetic_apply (a * b) n).symm
    _ = ramanujanArithmetic n.natAbs a * ramanujanArithmetic n.natAbs b :=
      (ramanujanArithmetic_isMultiplicative n.natAbs).map_mul_of_coprime hab
    _ = _ := by rw [ramanujanArithmetic_apply, ramanujanArithmetic_apply]

/-- General quantitative Ramanujan gcd bound for the actual finite sum,
including c=0, c=1, n=0, and negative integer frequencies. -/
theorem norm_ramanujan_le_gcd (c : ℕ) (n : ℤ) :
    ‖ramanujan c n‖ ≤ (c.gcd n.natAbs : ℝ) := by
  induction c using Nat.recOnPosPrimePosCoprime with
  | zero =>
      simp [ramanujan, kloosterman]
  | one =>
      rw [ramanujan_modulus_one]
      simp
  | prime_pow p j hp hj =>
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 :=
        Nat.exists_eq_succ_of_ne_zero hj.ne'
      exact norm_ramanujan_prime_pow_le_gcd hp k n
  | coprime a b _ha _hb hab hA hB =>
      rw [ramanujan_mul_of_coprime n hab, norm_mul]
      have hproduct :
          ‖ramanujan a n‖ * ‖ramanujan b n‖ ≤
            (a.gcd n.natAbs : ℝ) * (b.gcd n.natAbs : ℝ) :=
        mul_le_mul hA hB (norm_nonneg _) (Nat.cast_nonneg _)
      have hgcd : (a * b).gcd n.natAbs =
          a.gcd n.natAbs * b.gcd n.natAbs := by
        simpa only [Nat.gcd_comm] using hab.gcd_mul n.natAbs
      calc
        ‖ramanujan a n‖ * ‖ramanujan b n‖ ≤
            (a.gcd n.natAbs : ℝ) * (b.gcd n.natAbs : ℝ) := hproduct
        _ = ((a * b).gcd n.natAbs : ℝ) := by
          rw [hgcd, Nat.cast_mul]

end
end ImbalancedChen.Part3.RamanujanMultiplicativeGcdBound20261025a