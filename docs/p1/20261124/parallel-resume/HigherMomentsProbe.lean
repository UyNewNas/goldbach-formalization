import ImbalancedChen.P2OriginalSixthSimplexMoments
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
namespace ImbalancedChen.P2OriginalSixthHigherMomentsProbe
noncomputable section
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


private theorem self_smul (q x : ℚ) : q • x = q * x := by rfl
private theorem real_smul (q : ℚ) (x : ℝ) : q • x = (q : ℝ) * x := by rfl

theorem author_one (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 1 = ∑ j : Fin 2,
      completeH (List.ofFn y) (1 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH, List.ofFn_succ, List.ofFn_zero, Fin.sum_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    self_smul]
  <;> first | rfl | ring1!

theorem integrated_one (y : Fin 7 → ℝ) :
    integratedPower y 0 1 = duplicateH y 0 1 / ((Nat.factorial 7 : ℝ) * ((7 + 1).choose 1 : ℝ)) := by
  norm_num [integratedPower,
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    baryCoefficient, bumped, unitExponent,
    P2Winner9NestedEightSimplexMoment.factorialProduct, List.ofFn_succ, List.ofFn_zero,
    List.range_succ, List.range_zero,
    Nat.multinomial, duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    real_smul]
  <;> first | rfl | ring1!
end
end ImbalancedChen.P2OriginalSixthHigherMomentsProbe
