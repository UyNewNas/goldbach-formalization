import ImbalancedChen.P2OriginalSixthSimplexMoments
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Original G7 seven-node Dirichlet-mixture moments in degrees0..6.
The extra copy of node i gives EIGHT nodes, denominator choose(7+k,k).
Universal polynomial guards retain arbitrary vertex values; no archived
row, finite producer or numerical checking was executed while authoring.
-/
namespace ImbalancedChen.P2OriginalSixthHigherMoments
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSixthSimplexMoments

/-- Newton's complete-homogeneous recurrence. Its power sum contains
all seven nodes AND a second occurrence of node `i`. The division is by
the current positive degree; it is not the barycentric normalization. -/
def duplicateH {A : Type*} [CommRing A] [Algebra ℚ A]
    (y : Fin 7 → A) (i : Fin 7) : ℕ → A
  | 0 => 1
  | k + 1 => ((k + 1 : ℚ)⁻¹) •
      ∑ j : Fin (k + 1),
        ((∑ r : Fin 7, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
          duplicateH y i (k - j.val)
termination_by k => k
decreasing_by omega

theorem duplicateH_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B)
    (y : Fin 7 → A) (i : Fin 7) (k : ℕ) :
    f (duplicateH y i k) = duplicateH (fun r => f (y r)) i k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [duplicateH]
    | succ k =>
      simp only [duplicateH, map_smul, map_sum, map_mul, map_add, map_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (k - j.val) (by omega)]

/-- Rational mixture before any common-denominator representation. -/
def rationalMoment (g y : Fin 7 → ℚ) (k : ℕ) : ℚ :=
  (∑ i : Fin 7, g i * duplicateH y i k) /
    ((∑ i : Fin 7, g i) * ((7 + k).choose k : ℚ))

def realMoment (g y : Fin 7 → ℝ) (k : ℕ) : ℝ :=
  (∑ i : Fin 7, g i * duplicateH y i k) /
    ((∑ i : Fin 7, g i) * ((7 + k).choose k : ℝ))

theorem rationalMoment_cast (g y : Fin 7 → ℚ) (k : ℕ) :
    (rationalMoment g y k : ℝ) =
      realMoment (fun i => (g i : ℝ)) (fun i => (y i : ℝ)) k := by
  unfold rationalMoment realMoment
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hmap := duplicateH_map (Algebra.ofId ℚ ℝ) y i k
  change ((duplicateH y i k : ℚ) : ℝ) = duplicateH (fun r => (y r : ℝ)) i k at hmap
  rw [hmap]

/-- The exact rational coefficient already proved by the held K
Lebesgue monomial theorem, including the residual coordinate 0. -/
def baryCoefficient (e : Fin 7 → ℕ) : ℚ :=
  (((e 0).factorial *
      P2Winner9NestedEightSimplexMoment.factorialProduct
        (List.ofFn (fun r : Fin 6 => e r.succ)) : ℕ) : ℚ) /
    (((e 0) + (List.ofFn (fun r : Fin 6 => e r.succ)).sum + 6).factorial : ℚ)

theorem baryCoefficient_cast (e : Fin 7 → ℕ) :
    (baryCoefficient e : ℝ) = baryMoment e := by
  rw [baryMoment_eq]
  simp [baryCoefficient]

def bumped (e : Fin 7 → ℕ) (i : Fin 7) : Fin 7 → ℕ :=
  fun r => e r + unitExponent i r

theorem bary_bumped (e : Fin 7 → ℕ) (i : Fin 7) (x : Point) :
    (∏ r : Fin 7, bary r x ^ bumped e i r) =
      bary i x * ∏ r : Fin 7, bary r x ^ e r := by
  simp only [bumped, pow_add, Finset.prod_mul_distrib, prod_unitExponent]
  ring

/-- The complete, untruncated multinomial expansion in degree `k`,
integrated against barycentric weight i. No row values occur here. -/
def integratedPower (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ) : ℝ :=
  ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 7)) k,
    ((Nat.multinomial Finset.univ e : ℝ) * (baryCoefficient (bumped e i) : ℝ)) *
        ∏ r : Fin 7, y r ^ e r

/-- CLOSED FINITE GUARD; UNEVALUATED.

Each side is a polynomial with rational coefficients and seven arbitrary
real arguments; the arguments are NOT enumerated or specialized to
archive values. `piAntidiag_univ_fin_eq_antidiagonalTuple` switches
the abstract finite enumeration to Mathlib's explicit tuple recursion.
There is no native evaluator, stored-answer literal or archive oracle.
The factor 7! is the integral of one barycentric coordinate inverted;
the additional binomial is precisely (7+k)!/(7! k!). -/
private theorem ofFn_seven {A : Type*} (f : Fin 7 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6] := by rfl

private theorem ofFn_six {A : Type*} (f : Fin 6 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5] := by rfl

private theorem rational_smul_self (q x : ℚ) : q • x = q * x := by rfl

private theorem rational_smul_real (q : ℚ) (x : ℝ) : q • x = (q : ℝ) * x := by rfl

/-- Same factorial-product rewrite as P2Winner9PowerMoment, specialized to
seven barycentric coordinates of the manuscript's six-dimensional simplex. -/
private theorem baryCoefficient_eq_product (e : Fin 7 → ℕ) :
    baryCoefficient e =
      ((∏ r, (e r).factorial : ℕ) : ℚ) / (((∑ r, e r) + 6).factorial : ℚ) := by
  rw [baryCoefficient, P2Winner9NestedEightSimplexMoment.factorialProduct,
    List.map_ofFn, List.prod_ofFn, List.sum_ofFn,
    Fin.prod_univ_succ (fun r : Fin 7 => (e r).factorial),
    Fin.sum_univ_succ (fun r : Fin 7 => e r)]
  rfl

/-- The existing multinomial_shifted_factorial proof, with Fin 7 and the
already defined unitExponent. No finite numerical certificate is introduced. -/
private theorem multinomial_bumped_factorial {k : ℕ} {e : Fin 7 → ℕ}
    (he : e ∈ Finset.piAntidiag Finset.univ k) (i : Fin 7) :
    Nat.multinomial Finset.univ e * (∏ r, (bumped e i r).factorial) =
      k.factorial * (e i + 1) := by
  classical
  have hprod : (∏ r, (bumped e i r).factorial) =
      (∏ r, (e r).factorial) * (e i + 1) := by
    calc
      _ = ∏ r, ((e r).factorial * if r = i then e i + 1 else 1) := by
        refine Finset.prod_congr rfl (fun r _ => ?_)
        by_cases h : r = i
        · subst r
          simp [bumped, unitExponent, Nat.factorial_succ, mul_comm]
        · simp [bumped, unitExponent, h]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hprod, ← mul_assoc, mul_comm (Nat.multinomial _ _), Nat.multinomial_spec,
    (Finset.mem_piAntidiag.mp he).1]

/-- Cancel multinomial and Dirichlet factorials before enumerating the 924
sixth-degree exponent tuples. This is num:simplex-moment's exact coefficient. -/
private theorem integratedPower_eq_factored (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ) :
    integratedPower y i k =
      ((k.factorial : ℝ) / ((k + 7).factorial : ℝ)) *
        ∑ e ∈ Finset.piAntidiag Finset.univ k,
          ((e i + 1 : ℕ) : ℝ) * ∏ r : Fin 7, y r ^ e r := by
  classical
  rw [integratedPower, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hu : (∑ r : Fin 7, unitExponent i r) = 1 := by
    simp [unitExponent, Finset.sum_ite_eq']
  have hsum : (∑ r : Fin 7, bumped e i r) + 6 = k + 7 := by
    simp only [bumped, Finset.sum_add_distrib, hu, (Finset.mem_piAntidiag.mp he).1]
    <;> omega
  have hprod : (Nat.multinomial Finset.univ e : ℝ) *
      ((∏ r, (bumped e i r).factorial : ℕ) : ℝ) =
        (k.factorial : ℝ) * ((e i + 1 : ℕ) : ℝ) := by
    exact_mod_cast multinomial_bumped_factorial he i
  rw [baryCoefficient_eq_product]
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [hsum]
  calc
    _ = ((Nat.multinomial Finset.univ e : ℝ) *
          ((∏ r, (bumped e i r).factorial : ℕ) : ℝ)) *
        ((∏ r : Fin 7, y r ^ e r) / ((k + 7).factorial : ℝ)) := by ring
    _ = _ := by rw [hprod]; ring

private theorem integratedPower_newton_guard_0_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 0 = duplicateH y 0 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_0_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 0 = duplicateH y 1 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_0_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 0 = duplicateH y 2 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_0_3 (y : Fin 7 → ℝ) :
    integratedPower y 3 0 = duplicateH y 3 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_0_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 0 = duplicateH y 4 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_0_5 (y : Fin 7 → ℝ) :
    integratedPower y 5 0 = duplicateH y 5 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_0_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 0 = duplicateH y 6 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_1_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 1 = duplicateH y 0 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_1_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 1 = duplicateH y 1 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_1_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 1 = duplicateH y 2 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_1_3 (y : Fin 7 → ℝ) :
    integratedPower y 3 1 = duplicateH y 3 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_1_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 1 = duplicateH y 4 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_1_5 (y : Fin 7 → ℝ) :
    integratedPower y 5 1 = duplicateH y 5 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_1_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 1 = duplicateH y 6 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_2_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 2 = duplicateH y 0 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_2_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 2 = duplicateH y 1 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_2_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 2 = duplicateH y 2 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_2_3 (y : Fin 7 → ℝ) :
    integratedPower y 3 2 = duplicateH y 3 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_2_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 2 = duplicateH y 4 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_2_5 (y : Fin 7 → ℝ) :
    integratedPower y 5 2 = duplicateH y 5 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_2_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 2 = duplicateH y 6 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_3_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 3 = duplicateH y 0 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_3_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 3 = duplicateH y 1 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_3_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 3 = duplicateH y 2 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_3_3 (y : Fin 7 → ℝ) :
    integratedPower y 3 3 = duplicateH y 3 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_3_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 3 = duplicateH y 4 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_3_5 (y : Fin 7 → ℝ) :
    integratedPower y 5 3 = duplicateH y 5 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_3_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 3 = duplicateH y 6 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_4_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 4 = duplicateH y 0 4 /
      ((Nat.factorial 7 : ℝ) * ((7 + 4).choose 4 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_4_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 4 = duplicateH y 1 4 /
      ((Nat.factorial 7 : ℝ) * ((7 + 4).choose 4 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_4_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 4 = duplicateH y 2 4 /
      ((Nat.factorial 7 : ℝ) * ((7 + 4).choose 4 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_4_3 (y : Fin 7 → ℝ) :
    integratedPower y 3 4 = duplicateH y 3 4 /
      ((Nat.factorial 7 : ℝ) * ((7 + 4).choose 4 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_4_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 4 = duplicateH y 4 4 /
      ((Nat.factorial 7 : ℝ) * ((7 + 4).choose 4 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_4_5 (y : Fin 7 → ℝ) :
    integratedPower y 5 4 = duplicateH y 5 4 /
      ((Nat.factorial 7 : ℝ) * ((7 + 4).choose 4 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_4_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 4 = duplicateH y 6 4 /
      ((Nat.factorial 7 : ℝ) * ((7 + 4).choose 4 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_5_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 5 = duplicateH y 0 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_5_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 5 = duplicateH y 1 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_5_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 5 = duplicateH y 2 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_5_3 (y : Fin 7 → ℝ) :
    integratedPower y 3 5 = duplicateH y 3 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_5_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 5 = duplicateH y 4 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_5_5 (y : Fin 7 → ℝ) :
    integratedPower y 5 5 = duplicateH y 5 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_5_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 5 = duplicateH y 6 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_6_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 6 = duplicateH y 0 6 /
      ((Nat.factorial 7 : ℝ) * ((7 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_6_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 6 = duplicateH y 1 6 /
      ((Nat.factorial 7 : ℝ) * ((7 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_6_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 6 = duplicateH y 2 6 /
      ((Nat.factorial 7 : ℝ) * ((7 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_6_3 (y : Fin 7 → ℝ) :
    integratedPower y 3 6 = duplicateH y 3 6 /
      ((Nat.factorial 7 : ℝ) * ((7 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_6_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 6 = duplicateH y 4 6 /
      ((Nat.factorial 7 : ℝ) * ((7 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_6_5 (y : Fin 7 → ℝ) :
    integratedPower y 5 6 = duplicateH y 5 6 /
      ((Nat.factorial 7 : ℝ) * ((7 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

private theorem integratedPower_newton_guard_6_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 6 = duplicateH y 6 6 /
      ((Nat.factorial 7 : ℝ) * ((7 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

theorem integratedPower_newton_guard (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    integratedPower y i k = duplicateH y i k /
      ((Nat.factorial 7 : ℝ) * ((7 + k).choose k : ℝ)) := by
  interval_cases k
  · fin_cases i
    · exact integratedPower_newton_guard_0_0 y
    · exact integratedPower_newton_guard_0_1 y
    · exact integratedPower_newton_guard_0_2 y
    · exact integratedPower_newton_guard_0_3 y
    · exact integratedPower_newton_guard_0_4 y
    · exact integratedPower_newton_guard_0_5 y
    · exact integratedPower_newton_guard_0_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_1_0 y
    · exact integratedPower_newton_guard_1_1 y
    · exact integratedPower_newton_guard_1_2 y
    · exact integratedPower_newton_guard_1_3 y
    · exact integratedPower_newton_guard_1_4 y
    · exact integratedPower_newton_guard_1_5 y
    · exact integratedPower_newton_guard_1_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_2_0 y
    · exact integratedPower_newton_guard_2_1 y
    · exact integratedPower_newton_guard_2_2 y
    · exact integratedPower_newton_guard_2_3 y
    · exact integratedPower_newton_guard_2_4 y
    · exact integratedPower_newton_guard_2_5 y
    · exact integratedPower_newton_guard_2_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_3_0 y
    · exact integratedPower_newton_guard_3_1 y
    · exact integratedPower_newton_guard_3_2 y
    · exact integratedPower_newton_guard_3_3 y
    · exact integratedPower_newton_guard_3_4 y
    · exact integratedPower_newton_guard_3_5 y
    · exact integratedPower_newton_guard_3_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_4_0 y
    · exact integratedPower_newton_guard_4_1 y
    · exact integratedPower_newton_guard_4_2 y
    · exact integratedPower_newton_guard_4_3 y
    · exact integratedPower_newton_guard_4_4 y
    · exact integratedPower_newton_guard_4_5 y
    · exact integratedPower_newton_guard_4_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_5_0 y
    · exact integratedPower_newton_guard_5_1 y
    · exact integratedPower_newton_guard_5_2 y
    · exact integratedPower_newton_guard_5_3 y
    · exact integratedPower_newton_guard_5_4 y
    · exact integratedPower_newton_guard_5_5 y
    · exact integratedPower_newton_guard_5_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_6_0 y
    · exact integratedPower_newton_guard_6_1 y
    · exact integratedPower_newton_guard_6_2 y
    · exact integratedPower_newton_guard_6_3 y
    · exact integratedPower_newton_guard_6_4 y
    · exact integratedPower_newton_guard_6_5 y
    · exact integratedPower_newton_guard_6_6 y

/-- Coefficients of the product of the geometric series of the nodes.
This is the complete-homogeneous polynomial, expressed without a
distinct-node or nonzero-node restriction. -/
def completeH {A : Type*} [CommRing A] : List A → ℕ → A
  | [], k => if k = 0 then 1 else 0
  | a :: as, k => ∑ j : Fin (k + 1), a ^ j.val * completeH as (k - j.val)

theorem completeH_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (as : List A) (k : ℕ) :
    f (completeH as k) = completeH (as.map f) k := by
  induction as generalizing k with
  | nil => by_cases hk : k = 0 <;> simp [completeH, hk]
  | cons a as ih => simp [completeH, map_sum, map_mul, map_pow, ih]

/-- Exactly the author's in-place update h[k] += y*h[k-1], with old
coefficients on the right for the shorter node list. -/
theorem completeH_cons_succ {A : Type*} [CommRing A]
    (a : A) (as : List A) (k : ℕ) :
    completeH (a :: as) (k + 1) =
      completeH as (k + 1) + a * completeH (a :: as) k := by
  simp only [completeH]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero, one_mul, Fin.val_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : k + 1 - (j.val + 1) = k - j.val := by omega
  rw [hs, pow_succ]
  ring

/-- CLOSED UNIVERSAL POLYNOMIAL GUARD; UNEVALUATED.
The seven-node geometric-series recurrence convolved with the extra
copy of node i equals the eight-node Newton recurrence. Only i and the
degree are enumerated; all seven rational nodes remain arbitrary. -/
private theorem completeH_nil {A : Type*} [CommRing A] (k : ℕ) :
    completeH ([] : List A) k = (if k = 0 then 1 else 0) := by rfl

private theorem completeH_zero {A : Type*} [CommRing A] (as : List A) :
    completeH as 0 = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [completeH, Fin.sum_univ_succ, ih]

private theorem duplicateH_author_guard_0 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 0 = ∑ j : Fin (0 + 1),
      completeH (List.ofFn y) (0 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

private theorem duplicateH_author_guard_1 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 1 = ∑ j : Fin (1 + 1),
      completeH (List.ofFn y) (1 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

private theorem duplicateH_author_guard_2 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 2 = ∑ j : Fin (2 + 1),
      completeH (List.ofFn y) (2 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

private theorem duplicateH_author_guard_3 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 3 = ∑ j : Fin (3 + 1),
      completeH (List.ofFn y) (3 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

private theorem duplicateH_author_guard_4 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 4 = ∑ j : Fin (4 + 1),
      completeH (List.ofFn y) (4 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

private theorem duplicateH_author_guard_5 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 5 = ∑ j : Fin (5 + 1),
      completeH (List.ofFn y) (5 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

private theorem duplicateH_author_guard_6 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 6 = ∑ j : Fin (6 + 1),
      completeH (List.ofFn y) (6 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

theorem duplicateH_author_guard (y : Fin 7 → ℚ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    duplicateH y i k = ∑ j : Fin (k + 1),
      completeH (List.ofFn y) (k - j.val) * y i ^ j.val := by
  interval_cases k
  · exact duplicateH_author_guard_0 y i
  · exact duplicateH_author_guard_1 y i
  · exact duplicateH_author_guard_2 y i
  · exact duplicateH_author_guard_3 y i
  · exact duplicateH_author_guard_4 y i
  · exact duplicateH_author_guard_5 y i
  · exact duplicateH_author_guard_6 y i

/-- The actual frozen author engine's numerator h*gp, before Q80 and
Q96. It is distinct from the independent duplicated-node algorithm. -/
def authorMoment (g y : Fin 7 → ℚ) (k : ℕ) : ℚ :=
  (∑ j : Fin (k + 1), completeH (List.ofFn y) (k - j.val) *
    ∑ i : Fin 7, g i * y i ^ j.val) /
      ((∑ i : Fin 7, g i) * ((7 + k).choose k : ℚ))

theorem authorMoment_eq_rationalMoment (g y : Fin 7 → ℚ) (k : ℕ)
    (hk : k ≤ 6) : authorMoment g y k = rationalMoment g y k := by
  unfold authorMoment rationalMoment
  congr 1
  simp_rw [duplicateH_author_guard y _ k hk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Integral-coefficient realization of the eight-node polynomial. -/
def integerDuplicateH (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ) : ℤ :=
  completeH (z i :: List.ofFn z) k

theorem integerDuplicateH_cast (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    (integerDuplicateH z i k : ℚ) = duplicateH (fun r => (z r : ℚ)) i k := by
  have hm := completeH_map (Int.castRingHom ℚ) (z i :: List.ofFn z) k
  have he : (integerDuplicateH z i k : ℚ) =
      completeH ((z i : ℚ) :: List.ofFn (fun r => (z r : ℚ))) k := by
    simpa [integerDuplicateH, List.map_ofFn] using hm
  rw [he, completeH, duplicateH_author_guard _ i k hk]
  apply Finset.sum_congr rfl
  intro j _
  ring

def integerNewtonNumerator (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ) : ℤ :=
  ∑ j : Fin (k + 1),
    ((∑ r : Fin 7, z r ^ (j.val + 1)) + z i ^ (j.val + 1)) *
      integerDuplicateH z i (k - j.val)

/-- The divisibility required by the independent engine's z//k
operation follows from its integer complete-homogeneous polynomial;
it is not a numerical assertion about a particular archived node set. -/
theorem integerNewtonNumerator_spec (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ)
    (hk : k + 1 ≤ 6) :
    integerNewtonNumerator z i k = (k + 1 : ℤ) * integerDuplicateH z i (k + 1) := by
  have hc (j : Fin (k + 1)) :
      (integerDuplicateH z i (k - j.val) : ℚ) =
        duplicateH (fun r => (z r : ℚ)) i (k - j.val) :=
    integerDuplicateH_cast z i _ (by omega)
  have hQ : (integerNewtonNumerator z i k : ℚ) =
      (k + 1 : ℚ) * (integerDuplicateH z i (k + 1) : ℚ) := by
    rw [integerDuplicateH_cast z i (k + 1) hk, duplicateH]
    simp only [integerNewtonNumerator, Int.cast_sum, Int.cast_mul, Int.cast_add,
      Int.cast_pow, hc, smul_eq_mul]
    have hne : (k + 1 : ℚ) ≠ 0 := by positivity
    field_simp [hne]
  exact_mod_cast hQ

theorem integerNewtonNumerator_divisible (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ)
    (hk : k + 1 ≤ 6) : (k + 1 : ℤ) ∣ integerNewtonNumerator z i k :=
  ⟨integerDuplicateH z i (k + 1), integerNewtonNumerator_spec z i k hk⟩

theorem binomial_normalization (k : ℕ) :
    ((7 + k).choose k : ℚ) * k.factorial * (Nat.factorial 7) =
      ((7 + k).factorial : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 7 + k) (k := k) (by omega)
  have hs : 7 + k - k = 7 := by omega
  rw [hs] at h
  exact_mod_cast h

theorem integral_bary_interpolate_power (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    (∫ x in canonical, bary i x * interpolate y x ^ k) =
      duplicateH y i k /
        (((Nat.factorial 7) : ℝ) * ((7 + k).choose k : ℝ)) := by
  classical
  let S := Finset.piAntidiag (Finset.univ : Finset (Fin 7)) k
  let term (e : Fin 7 → ℕ) (x : Point) :=
    ((Nat.multinomial Finset.univ e : ℝ) * ∏ r : Fin 7, y r ^ e r) *
      ∏ r : Fin 7, bary r x ^ bumped e i r
  have hi (e : Fin 7 → ℕ) : IntegrableOn (term e) canonical := by
    apply ContinuousOn.integrableOn_compact canonical_compact
    apply Continuous.continuousOn
    apply continuous_const.mul
    exact continuous_finsetProd _ fun r _ => (bary_continuous r).pow _
  have he (x : Point) : bary i x * interpolate y x ^ k = ∑ e ∈ S, term e x := by
    rw [interpolate, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [term, mul_pow, Finset.prod_mul_distrib, bary_bumped]
    ring
  have hint : (∫ x in canonical, bary i x * interpolate y x ^ k) =
      ∑ e ∈ S, ((Nat.multinomial Finset.univ e : ℝ) *
        (baryCoefficient (bumped e i) : ℝ)) * ∏ r : Fin 7, y r ^ e r := by
    simp_rw [he]
    rw [integral_finsetSum S (fun e _ => hi e)]
    apply Finset.sum_congr rfl
    intro e _
    rw [show term e = fun x =>
        ((Nat.multinomial Finset.univ e : ℝ) * ∏ r : Fin 7, y r ^ e r) *
          ∏ r : Fin 7, bary r x ^ bumped e i r from rfl,
      integral_const_mul]
    rw [show (∫ x in canonical, ∏ r : Fin 7, bary r x ^ bumped e i r) =
      baryMoment (bumped e i) from rfl, ← baryCoefficient_cast]
    ring
  rw [hint]
  exact integratedPower_newton_guard y i k hk

/-- The actual gap-weighted degree-k polynomial integral; the original
seven-vertex gap weights are retained independently of the node values. -/
theorem integral_interpolate_mul_power (g y : Fin 7 → ℝ) (k : ℕ) (hk : k ≤ 6) :
    (∫ x in canonical, interpolate g x * interpolate y x ^ k) =
      (∑ i : Fin 7, g i * duplicateH y i k) /
        (((Nat.factorial 7) : ℝ) * ((7 + k).choose k : ℝ)) := by
  have hi (i : Fin 7) : IntegrableOn
      (fun x => g i * (bary i x * interpolate y x ^ k)) canonical :=
    (continuous_const.mul ((bary_continuous i).mul
      ((interpolate_continuous y).pow k))).continuousOn.integrableOn_compact
        canonical_compact
  have he (x : Point) : interpolate g x * interpolate y x ^ k =
      ∑ i : Fin 7, g i * (bary i x * interpolate y x ^ k) := by
    simp only [interpolate, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [integral_const_mul, integral_bary_interpolate_power y _ k hk]
  simp [mul_div_assoc, Finset.sum_div]

end
end ImbalancedChen.P2OriginalSixthHigherMoments
