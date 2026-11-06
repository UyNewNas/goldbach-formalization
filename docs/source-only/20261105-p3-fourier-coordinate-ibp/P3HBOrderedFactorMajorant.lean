import ImbalancedChen.P3ShiftedDivisorFiniteMoment
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-!
P3.6, fixed manuscript 9731290, §§2 and 4.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

A genuine finite HB input for the nonzero shifted-divisor moment:
ordered one-bounded factor slots with ONE explicitly marked logarithm
have a pointwise coefficient majorant L * tau(n)^g at complete product n.

The finite source here consists of DISTINCT ordered integer slot tuples.
It is NOT the still-unproved full labelled HB compiler: its external scalar
multiplicities, all original prime labels, log-slot choices, rough projection,
and the fixed kappa/exponent payment must be attached separately.
In particular this file neither assumes nor proves the analytic near-linear
mixed divisor moment, nor the same-rho PP conclusion.  It is an internal
elementary counting step, not a replacement external input.
-/

namespace ImbalancedChen.P3HBOrderedFactorMajorant

noncomputable section
open scoped Classical BigOperators

/-- Every coordinate of an ordered integer factorization divides the
complete product (including the zero-dimensional empty product). -/
theorem coordinate_dvd_complete {g : ℕ}
    (p : Fin g → ℕ) (i : Fin g) :
    p i ∣ ∏ j, p j := by
  exact Finset.dvd_prod_of_mem (Finset.mem_univ i)

/-- The actual finite set of distinct ordered g-slot factorizations
of a nonzero n; no arbitrary source labels or multiplicities are inserted. -/
def orderedFactorTuples (g n : ℕ) : Finset (Fin g → ℕ) :=
  (Fintype.piFinset (fun _ : Fin g => n.divisors)).filter
    (fun p => (∏ j, p j) = n)

/-- On a nonzero product, the divisor-box construction is exactly the
full ordered-factorization fiber, not an additional arithmetic filter. -/
theorem mem_orderedFactorTuples_iff {g n : ℕ}
    (hn : n ≠ 0) (p : Fin g → ℕ) :
    p ∈ orderedFactorTuples g n ↔ (∏ j, p j) = n := by
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro j
      apply Nat.mem_divisors.mpr
      exact ⟨hp ▸ coordinate_dvd_complete p j, hn⟩
    · exact hp

/-- Genuine finite ordered-factor counting. The power g is deliberately
not misreported as g-1; no final-slot uniqueness saving is used here. -/
theorem orderedFactorTuples_card_le_tau_pow (g n : ℕ) :
    (orderedFactorTuples g n).card ≤ (n.divisors.card) ^ g := by
  unfold orderedFactorTuples
  calc
    ((Fintype.piFinset (fun _ : Fin g => n.divisors)).filter
        (fun p => (∏ j, p j) = n)).card
        ≤ (Fintype.piFinset (fun _ : Fin g => n.divisors)).card := by
          exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (n.divisors.card) ^ g := by
          exact Fintype.card_piFinset_const n.divisors g

/-- A single marked HB log slot remains separate from the one-bounded
raw factors (including the marked slot's own one-bounded factor). -/
def markedHBWeight {g : ℕ}
    (a : Fin g → ℕ → ℝ) (logSlot : ℕ → ℝ)
    (marked : Fin g) (p : Fin g → ℕ) : ℝ :=
  logSlot (p marked) * ∏ j, a j (p j)

/-- Product of literal one-bounded HB slot weights: no estimated PP
coefficient or distribution theorem occurs among its hypotheses. -/
theorem oneBoundedProduct_le_one {g : ℕ}
    (a : Fin g → ℕ → ℝ) (p : Fin g → ℕ)
    (ha : ∀ j x, |a j x| ≤ 1) :
    |∏ j, a j (p j)| ≤ 1 := by
  rw [Finset.abs_prod]
  calc
    (∏ j : Fin g, |a j (p j)|)
        ≤ ∏ _j : Fin g, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro j hj
            exact abs_nonneg _
          · intro j hj
            exact ha j (p j)
    _ = 1 := by simp

/-- Exactly one log marking costs L, not an unproved extra power of
the full product or an arbitrary Fourier norm. -/
theorem markedHBWeight_le {g : ℕ}
    (a : Fin g → ℕ → ℝ) (logSlot : ℕ → ℝ)
    (marked : Fin g) (p : Fin g → ℕ) (L : ℝ)
    (ha : ∀ j x, |a j x| ≤ 1)
    (hL : ∀ x, |logSlot x| ≤ L) (hL0 : 0 ≤ L) :
    |markedHBWeight a logSlot marked p| ≤ L := by
  rw [markedHBWeight, abs_mul]
  calc
    |logSlot (p marked)| * |∏ j, a j (p j)|
        ≤ L * |∏ j, a j (p j)| :=
          mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)
    _ ≤ L * 1 :=
          mul_le_mul_of_nonneg_left (oneBoundedProduct_le_one a p ha) hL0
    _ = L := by ring

/-- Absolute coefficient mass of all DISTINCT ordered HB tuples with
one marked log; this is a concrete finite convolution, not a surrogate
for the entire labelled HB source. -/
def markedHBCoefficientMass {g : ℕ}
    (n : ℕ) (a : Fin g → ℕ → ℝ)
    (logSlot : ℕ → ℝ) (marked : Fin g) : ℝ :=
  ∑ p ∈ orderedFactorTuples g n, |markedHBWeight a logSlot marked p|

/-- Elementary HB divisor-power bound, retaining the actual number of
ordered slots g and exactly one marked logarithm. -/
theorem markedHBCoefficientMass_le_tau_pow {g : ℕ}
    (n : ℕ) (a : Fin g → ℕ → ℝ)
    (logSlot : ℕ → ℝ) (marked : Fin g) (L : ℝ)
    (ha : ∀ j x, |a j x| ≤ 1)
    (hL : ∀ x, |logSlot x| ≤ L) (hL0 : 0 ≤ L) :
    markedHBCoefficientMass n a logSlot marked ≤
      L * ((n.divisors.card : ℝ) ^ g) := by
  unfold markedHBCoefficientMass
  calc
    (∑ p ∈ orderedFactorTuples g n, |markedHBWeight a logSlot marked p|)
        ≤ ∑ _p ∈ orderedFactorTuples g n, L := by
          apply Finset.sum_le_sum
          intro p hp
          exact markedHBWeight_le a logSlot marked p L ha hL hL0
    _ = L * ((orderedFactorTuples g n).card : ℝ) := by simp [mul_comm]
    _ ≤ L * ((n.divisors.card : ℝ) ^ g) := by
          apply mul_le_mul_of_nonneg_left _ hL0
          exact_mod_cast orderedFactorTuples_card_le_tau_pow g n

/-- Only nonzero, nonexceptional FULL products enter a shifted divisor
moment; in particular no tau(0) term is used. -/
def offProducts (T : ℕ) (ns : Finset ℕ) : Finset ℕ :=
  ns.filter (fun n => n ≠ 0 ∧ n ≠ T)

/-- A finite, explicitly nonzero integer shift. It is evaluated in the
following theorem only for n != T, not as an estimate at zero shift. -/
def offShiftTau (T n : ℕ) : ℕ :=
  (((T : ℤ) - (n : ℤ)).natAbs).divisors.card

/-- Actual elementary HB-to-mixed-divisor reduction, BEFORE any analytic
near-linear estimate, complete rho modulus payment or label multiplicity
compiler. The right side still needs an independent arithmetic moment. -/
theorem markedHB_off_shifted_le_mixed_tau {g : ℕ}
    (T : ℕ) (ns : Finset ℕ)
    (a : Fin g → ℕ → ℝ) (logSlot : ℕ → ℝ)
    (marked : Fin g) (L : ℝ)
    (ha : ∀ j x, |a j x| ≤ 1)
    (hL : ∀ x, |logSlot x| ≤ L) (hL0 : 0 ≤ L) :
    (∑ n ∈ offProducts T ns,
      markedHBCoefficientMass n a logSlot marked * (offShiftTau T n : ℝ))
      ≤ L * (∑ n ∈ offProducts T ns,
        ((n.divisors.card : ℝ) ^ g) * (offShiftTau T n : ℝ)) := by
  calc
    _ ≤ ∑ n ∈ offProducts T ns,
          (L * ((n.divisors.card : ℝ) ^ g)) * (offShiftTau T n : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          apply mul_le_mul_of_nonneg_right
            (markedHBCoefficientMass_le_tau_pow n a logSlot marked L ha hL hL0)
          exact Nat.cast_nonneg _
    _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring

end
end ImbalancedChen.P3HBOrderedFactorMajorant
