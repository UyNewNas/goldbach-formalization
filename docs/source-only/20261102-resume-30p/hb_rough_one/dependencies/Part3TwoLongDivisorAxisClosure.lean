import Mathlib
import ImbalancedChen.Part3TwoLongBrunLiteralDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Elementary phase-four source for the original two-long branch:
the squarefree prime-subset/integer-divisor dictionary and both exact
zero-axis identities of the genuine finite unit Kloosterman sum.

The factorial estimate e_r(w) <= H^r/r! has a complete elementary
ordered-tuple proof in the accompanying note. It is NOT declared as a
theorem in this source until its ordered-tuple count is formalized.
-/

namespace ImbalancedChen.Part3.TwoLongDivisorAxisClosure

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongBrunLiteralDensity

noncomputable section

/-- Integer represented by a finite subset of distinct chart primes. -/
def chartDivisor (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

/-- Unique prime factorization recovers the literal subset. This is the
injective half of the squarefree divisor dictionary. -/
theorem chartDivisor_primeFactors (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (chartDivisor S).primeFactors = S := by
  exact Nat.primeFactors_prod hS

theorem chartDivisor_injective_on
    (P S T : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : chartDivisor S = chartDivisor T) : S = T := by
  have hprimeS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact hP p (hS hp)
  have hprimeT : ∀ p ∈ T, p.Prime := by
    intro p hp
    exact hP p (hT hp)
  calc
    S = (chartDivisor S).primeFactors :=
      (chartDivisor_primeFactors S hprimeS).symm
    _ = (chartDivisor T).primeFactors := by rw [heq]
    _ = T := chartDivisor_primeFactors T hprimeT

/-- A squarefree integer is reconstructed from its prime subset. -/
theorem squarefree_chartDivisor_inverse (d : ℕ)
    (hd : Squarefree d) :
    chartDivisor d.primeFactors = d := by
  exact Nat.prod_primeFactors_of_squarefree hd

/-- For a squarefree d supported on P, the literal subset is inside P
and its chart product is d. This is the surjective half of the
squarefree divisor dictionary. -/
theorem squarefree_supported_chartDivisor
    (P d : ℕ) (hd : Squarefree d)
    (hP : d.primeFactors ⊆ Nat.primeFactors P) :
    ∃ S : Finset ℕ, S ⊆ Nat.primeFactors P ∧ chartDivisor S = d := by
  exact ⟨d.primeFactors, hP, squarefree_chartDivisor_inverse d hd⟩

/-- The literal squarefree divisors of the chart primorial are precisely
products of chart-prime subsets. -/
theorem squarefree_divisor_chartDivisor
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ) (hd : Squarefree d) (hdiv : d ∣ chartDivisor P) :
    ∃ S : Finset ℕ, S ⊆ P ∧ chartDivisor S = d := by
  have hprod : chartDivisor P ≠ 0 := by
    unfold chartDivisor
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (hP p hp).ne_zero
  have hsubset : d.primeFactors ⊆ P := by
    rw [← chartDivisor_primeFactors P hP]
    exact Nat.primeFactors_mono hdiv hprod
  exact ⟨d.primeFactors, hsubset, squarefree_chartDivisor_inverse d hd⟩

theorem chartDivisor_subset_dvd
    (P S : Finset ℕ) (hS : S ⊆ P) :
    chartDivisor S ∣ chartDivisor P := by
  exact Finset.prod_dvd_prod_of_subset S P id hS

/-- Inversion permutes the finite unit alphabet. This proves the left
zero Fourier axis S(0,k;q)=c_q(k) independently of Weil. -/
theorem unitKloosterman_left_axis {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (n : ZMod q) :
    unitKloosterman psi 0 n = unitRamanujan psi n := by
  simp only [unitKloosterman, unitRamanujan, zero_mul, zero_add]
  apply Finset.sum_bij (fun u _ => u⁻¹)
  · intro u hu
    exact Finset.mem_univ _
  · intro u hu v hv huv
    exact inv_injective huv
  · intro v hv
    refine ⟨v⁻¹, Finset.mem_univ _, ?_⟩
    simp
  · intro u hu
    rfl

/-- Multiplication by a primitive residue permutes the same unit
alphabet, hence c_q(bj)=c_q(j). -/
theorem unitRamanujan_unit_scaling {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (b : (ZMod q)ˣ) (j : ZMod q) :
    unitRamanujan psi ((b : ZMod q) * j) = unitRamanujan psi j := by
  simp only [unitRamanujan]
  apply Finset.sum_bij (fun u _ => b * u)
  · intro u hu
    exact Finset.mem_univ _
  · intro u hu v hv huv
    exact mul_left_cancel huv
  · intro v hv
    refine ⟨b⁻¹ * v, Finset.mem_univ _, ?_⟩
    simp
  · intro u hu
    congr 1
    simp only [Units.val_mul]
    ring

/-- The two identities needed for zero-axis cancellation against the
exact c_q(j)c_q(k)/phi(q) coprime mean. -/
theorem unitKloosterman_both_axes {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (b : (ZMod q)ˣ) (j k : ZMod q) :
    unitKloosterman psi 0 k = unitRamanujan psi k ∧
      unitKloosterman psi ((b : ZMod q) * j) 0 =
        unitRamanujan psi j := by
  constructor
  · exact unitKloosterman_left_axis psi k
  · rw [unitKloosterman_right_axis, unitRamanujan_unit_scaling]

/-- For the standard additive character, psi(0)=1, so c_q(0)=phi(q). -/
theorem unitRamanujan_zero {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (hpsi : psi 0 = 1) :
    unitRamanujan psi 0 = (Nat.totient q : ℂ) := by
  unfold unitRamanujan
  simp [hpsi, ZMod.card_units_eq_totient]

/-- The complete zero-axis bracket in P1 vanishes term by term.
No bound or frequency truncation is used. -/
theorem unitKloosterman_zero_axis_bracket {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (hpsi : psi 0 = 1)
    (b : (ZMod q)ˣ) (j k : ZMod q) :
    (j = 0 ∨ k = 0) →
      unitKloosterman psi ((b : ZMod q) * j) k -
        (Nat.totient q : ℂ)⁻¹ *
          (unitRamanujan psi j * unitRamanujan psi k) = 0 := by
  intro haxis
  have hphiNat : 0 < Nat.totient q := Nat.totient_pos.mpr (NeZero.pos q)
  have hphi : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hphiNat)
  obtain hj | hk := haxis
  · subst j
    simp only [mul_zero, unitKloosterman_left_axis, unitRamanujan_zero psi hpsi]
    simp [hphi]
  · subst k
    rw [unitKloosterman_right_axis, unitRamanujan_unit_scaling,
      unitRamanujan_zero psi hpsi]
    simp [hphi]

end

end ImbalancedChen.Part3.TwoLongDivisorAxisClosure
