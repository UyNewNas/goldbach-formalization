import ImbalancedChen.P2OriginalSixthSimplexMoments
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
namespace ImbalancedChen.P2OriginalSixthHigherMomentsFactoredLowBoundaryProbe
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSixthSimplexMoments
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

private theorem rational_smul_real (q : ℚ) (x : ℝ) : q • x = (q : ℝ) * x := by rfl

/-- Previously failing or previously untested universal polynomial leaf.
All seven real node values remain arbitrary; this is not an archive evaluator. -/
theorem integrated_0_0 (y : Fin 7 → ℝ) :
    integratedPower y 0 0 = duplicateH y 0 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Degree zero was already enumerated by the preceding norm_num.
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

/-- Previously failing or previously untested universal polynomial leaf.
All seven real node values remain arbitrary; this is not an archive evaluator. -/
theorem integrated_0_1 (y : Fin 7 → ℝ) :
    integratedPower y 1 0 = duplicateH y 1 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Degree zero was already enumerated by the preceding norm_num.
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

/-- Previously failing or previously untested universal polynomial leaf.
All seven real node values remain arbitrary; this is not an archive evaluator. -/
theorem integrated_1_0 (y : Fin 7 → ℝ) :
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

/-- Previously failing or previously untested universal polynomial leaf.
All seven real node values remain arbitrary; this is not an archive evaluator. -/
theorem integrated_1_1 (y : Fin 7 → ℝ) :
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

/-- Previously failing or previously untested universal polynomial leaf.
All seven real node values remain arbitrary; this is not an archive evaluator. -/
theorem integrated_2_0 (y : Fin 7 → ℝ) :
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

end
end ImbalancedChen.P2OriginalSixthHigherMomentsFactoredLowBoundaryProbe
