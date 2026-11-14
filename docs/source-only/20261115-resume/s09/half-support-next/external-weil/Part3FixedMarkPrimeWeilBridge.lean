import LeanPool.KloostermanWeil.Weil.PrimeKloosterman
import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import Mathlib.Tactic

/-! Source-only, uncompiled adapter.  The imported theorem is the actual
Stepanov-Carlitz proof from LeanPool/lean-pool at
5dd712603d49049c7a5198e5dd725f768c5a510b, not a Weil-bound hypothesis.
The upstream 34-module closure and its toolchain require separate acceptance.
This file changes neither the physical sum nor its positive phase convention. -/

noncomputable section
namespace ImbalancedChen.Part3.FixedMarkHalfTail20261115
open Classical Finset OriginalSmoothPoissonTail
open scoped BigOperators

/-- The physical range sum is exactly the external prime sum, with the
external definition's inverse coefficient placed first. -/
theorem physical_eq_prime (p : ℕ) [Fact p.Prime] (m n : ℤ) :
    kloosterman p m n =
      KloostermanWeil.kloostermanSumPrime p (n : ZMod p) (m : ZMod p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Physical.kloosterman_eq_zmod]
  unfold KloostermanWeil.kloostermanSumPrime
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0 <;> simp [hx, isUnit_iff_ne_zero]

/-- Conventional coefficient order; no conjugation, sign change, scalar,
or normalization factor is lost. -/
theorem physical_eq_weil (p : ℕ) [Fact p.Prime] (m n : ℤ) :
    kloosterman p m n =
      KloostermanWeil.weilKloostermanPrime p (m : ZMod p) (n : ZMod p) := by
  rw [physical_eq_prime,
    KloostermanWeil.kloostermanSumPrime_eq_weilKloostermanPrime]

/-- Uniform in the second mark, including zero.  Only p not dividing the
fixed first mark is needed; the degenerate sum is exactly -1. -/
theorem prime_physical_sqrt {p : ℕ} (hp : p.Prime) (m n : ℤ)
    (hm : ¬(p : ℤ) ∣ m) :
    ‖kloosterman p m n‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm' : (m : ZMod p) ≠ 0 :=
    mt (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp hm
  rw [physical_eq_prime]
  by_cases hn : (n : ZMod p) = 0
  · rw [hn, KloostermanWeil.kloostermanSumPrime_zero_left p _ hm']
    have hs : 1 ≤ Real.sqrt (p : ℝ) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_le)
    simpa only [norm_neg, norm_one] using
      (show (1 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) by linarith)
  · exact KloostermanWeil.prime_bound p (n : ZMod p) (m : ZMod p) hn hm'

theorem prime_physical_le {p : ℕ} (hp : p.Prime) (m n : ℤ)
    (hm : ¬(p : ℤ) ∣ m) :
    ‖kloosterman p m n‖ ≤ 2 * (p : ℝ) ^ (1/2 : ℝ) := by
  simpa only [Real.sqrt_eq_rpow] using prime_physical_sqrt hp m n hm

end ImbalancedChen.Part3.FixedMarkHalfTail20261115
