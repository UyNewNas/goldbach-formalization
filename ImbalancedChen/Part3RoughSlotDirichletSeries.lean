import ImbalancedChen.Part3RoughSlotCharacterLift
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact absolutely convergent twisted Dirichlet series of the ACTUAL rough
one and Mobius slots. The finite correction contains p<=z because the
literal rough predicate is z<p. Principal characters are included. If p
divides the original character modulus, its finite correction is exactly1.
Only Re(s)>1 is used; no SW or further zero-free region is assumed.
-/

namespace ImbalancedChen.Part3.RoughSlotDirichletSeries20261026b
noncomputable section
open Classical Finset Complex
open scoped BigOperators LSeries.notation ArithmeticFunction.Moebius
open RoughSlotCharacterLift20261026b

def finiteCorrection {q : ℕ} (chi : DirichletCharacter ℂ q) (z : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ smallPrimes z, (1-chi p*(p : ℂ)^(-s))

theorem correction_factor_eq_one_of_dvd_level {q p : ℕ}
    (chi : DirichletCharacter ℂ q) (hp : p.Prime) (hpq : p ∣ q) (s : ℂ) :
    1-chi p*(p : ℂ)^(-s) = 1 := by
  have hzero : chi p = 0 := MulChar.map_nonunit _ (by
    intro hu
    exact ((ZMod.isUnit_prime_iff_not_dvd hp).mp hu) hpq)
  simp only [hzero,zero_mul,sub_zero]

private theorem joined_primeFactors_product {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (z : ℝ) (s : ℂ) :
    (∏ p ∈ (q*smallProduct z).primeFactors, (1-chi p*(p : ℂ)^(-s))) =
      finiteCorrection chi z s := by
  rw [Nat.primeFactors_mul (NeZero.ne q) (smallProduct_ne_zero z),
    smallProduct_primeFactors]
  unfold finiteCorrection
  symm
  apply Finset.prod_subset Finset.subset_union_right
  intro p hp hnot
  have hpq : p ∈ q.primeFactors := (Finset.mem_union.mp hp).resolve_right hnot
  exact correction_factor_eq_one_of_dvd_level chi
    (Nat.mem_primeFactors.mp hpq).1 (Nat.mem_primeFactors.mp hpq).2.1 s

/-- Character Euler-product removal at the exact enlarged arithmetic
level, simplified to the actual finite small-prime set. -/
theorem roughCharacter_LSeries {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (z : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => roughCharacter chi z n) s =
      chi.LFunction s*finiteCorrection chi z s := by
  letI : NeZero (q*smallProduct z) :=
    ⟨mul_ne_zero (NeZero.ne q) (smallProduct_ne_zero z)⟩
  have h := DirichletCharacter.LSeries_changeLevel (dvd_mul_right q (smallProduct z)) chi hs
  change LSeries (fun n : ℕ => roughCharacter chi z n) s =
    LSeries (fun n : ℕ => chi n) s*
      (∏ p ∈ (q*smallProduct z).primeFactors, (1-chi p*(p : ℂ)^(-s))) at h
  rw [joined_primeFactors_product,← DirichletCharacter.LFunction_eq_LSeries chi hs] at h
  exact h

theorem roughOne_LSeries {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => chi n*roughOneSlot z n) s =
      chi.LFunction s*finiteCorrection chi z s := by
  have heq : (fun n : ℕ => chi n*roughOneSlot z n) =
      (fun n : ℕ => roughCharacter chi z n) :=
    funext (fun n => (roughCharacter_apply chi hz n).symm)
  rw [heq]
  exact roughCharacter_LSeries chi z hs

/-- The actual Mobius series is the reciprocal of the changed-character
L-series. The nonvanishing used here is the pinned theorem in Re(s)>1. -/
theorem roughMoebius_LSeries {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => chi n*roughMoebiusSlot z n) s =
      (chi.LFunction s)⁻¹*
        (∏ p ∈ smallPrimes z, (1-chi p*(p : ℂ)^(-s))⁻¹) := by
  have hfun : (fun n : ℕ => roughCharacter chi z n*
      ((ArithmeticFunction.moebius n : ℤ) : ℂ)) =
      (fun n : ℕ => chi n*roughMoebiusSlot z n) :=
    funext (fun n => (roughMoebius_twist_eq chi hz n).symm)
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one (roughCharacter chi z) hs
  change LSeries (fun n : ℕ => roughCharacter chi z n) s*
    LSeries (fun n : ℕ => roughCharacter chi z n*
      ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 at hmul
  rw [hfun] at hmul
  have hnonzero : LSeries (fun n : ℕ => roughCharacter chi z n) s ≠ 0 :=
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re (roughCharacter chi z) hs
  have hinverse : LSeries (fun n : ℕ => chi n*roughMoebiusSlot z n) s =
      (LSeries (fun n : ℕ => roughCharacter chi z n) s)⁻¹ := by
    apply mul_left_cancel₀ hnonzero
    rw [hmul,mul_inv_cancel₀ hnonzero]
  rw [hinverse,roughCharacter_LSeries chi z hs,Finset.prod_inv_distrib]
  simp only [finiteCorrection,mul_inv_rev,mul_comm]

/-- Literal positive-integer-series spellings. The zero summand vanishes
because Re(s)>1, even in the principal modulus-one endpoint. -/
theorem actual_rough_slot_Dirichlet_series {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, chi n*roughOneSlot z n/(n : ℂ)^s) =
        chi.LFunction s*finiteCorrection chi z s ∧
      (∑' n : ℕ, chi n*roughMoebiusSlot z n/(n : ℂ)^s) =
        (chi.LFunction s)⁻¹*
          (∏ p ∈ smallPrimes z, (1-chi p*(p : ℂ)^(-s))⁻¹) := by
  constructor
  · simpa only [LSeries,LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hs)] using
      roughOne_LSeries chi hz hs
  · simpa only [LSeries,LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hs)] using
      roughMoebius_LSeries chi hz hs

end
end ImbalancedChen.Part3.RoughSlotDirichletSeries20261026b
