import ImbalancedChen.P2OriginalSixthSimplexMoments
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
namespace ImbalancedChen.P2OriginalSixthHigherMomentsReductionProbe
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

def completeH {A : Type*} [CommRing A] : List A → ℕ → A
  | [], k => if k = 0 then 1 else 0
  | a :: as, k => ∑ j : Fin (k + 1), a ^ j.val * completeH as (k - j.val)

theorem completeH_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (as : List A) (k : ℕ) :
    f (completeH as k) = completeH (as.map f) k := by
  induction as generalizing k with
  | nil => by_cases hk : k = 0 <;> simp [completeH, hk]
  | cons a as ih => simp [completeH, map_sum, map_mul, map_pow, ih]


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

private theorem ofFn_seven {A : Type*} (f : Fin 7 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6] := by rfl

private theorem ofFn_six {A : Type*} (f : Fin 6 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5] := by rfl

private theorem completeH_nil {A : Type*} [CommRing A] (k : ℕ) :
    completeH ([] : List A) k = (if k = 0 then 1 else 0) := by rfl

private theorem completeH_zero {A : Type*} [CommRing A] (as : List A) :
    completeH as 0 = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [completeH, Fin.sum_univ_succ, ih]

private theorem self_smul (q x : ℚ) : q • x = q * x := by rfl
private theorem real_smul (q : ℚ) (x : ℝ) : q • x = (q : ℝ) * x := by rfl

theorem integrated_0_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 0 = duplicateH y 2 0 /
      ((Nat.factorial 7 : ℝ) * ((7 + 0).choose 0 : ℝ)) := by
  norm_num [integratedPower,
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    baryCoefficient, bumped, unitExponent,
    P2Winner9NestedEightSimplexMoment.factorialProduct, ofFn_seven, ofFn_six,
    List.range_succ, List.range_zero,
    Nat.multinomial, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial,
    duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    real_smul]
  <;> first | rfl | ring1!

theorem integrated_1_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 1 = duplicateH y 2 1 /
      ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  norm_num [integratedPower,
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    baryCoefficient, bumped, unitExponent,
    P2Winner9NestedEightSimplexMoment.factorialProduct, ofFn_seven, ofFn_six,
    List.range_succ, List.range_zero,
    Nat.multinomial, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial,
    duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    real_smul]
  <;> first | rfl | ring1!

theorem integrated_2_2 (y : Fin 7 → ℝ) :
    integratedPower y 2 2 = duplicateH y 2 2 /
      ((Nat.factorial 7 : ℝ) * ((7 + 2).choose 2 : ℝ)) := by
  norm_num [integratedPower,
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    baryCoefficient, bumped, unitExponent,
    P2Winner9NestedEightSimplexMoment.factorialProduct, ofFn_seven, ofFn_six,
    List.range_succ, List.range_zero,
    Nat.multinomial, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial,
    duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    real_smul]
  <;> first | rfl | ring1!

theorem integrated_3_6 (y : Fin 7 → ℝ) :
    integratedPower y 6 3 = duplicateH y 6 3 /
      ((Nat.factorial 7 : ℝ) * ((7 + 3).choose 3 : ℝ)) := by
  norm_num [integratedPower,
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    baryCoefficient, bumped, unitExponent,
    P2Winner9NestedEightSimplexMoment.factorialProduct, ofFn_seven, ofFn_six,
    List.range_succ, List.range_zero,
    Nat.multinomial, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial,
    duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    real_smul]
  <;> first | rfl | ring1!

theorem author_3 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 3 = ∑ j : Fin (3 + 1),
      completeH (List.ofFn y) (3 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero,
    ofFn_seven, ofFn_six, Fin.sum_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    self_smul]
  <;> first | rfl | ring1!

end
end ImbalancedChen.P2OriginalSixthHigherMomentsReductionProbe
