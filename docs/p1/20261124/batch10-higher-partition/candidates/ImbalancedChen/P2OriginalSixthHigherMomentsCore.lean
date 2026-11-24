import ImbalancedChen.P2OriginalSixthSimplexMoments
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-! SOURCE_ONLY / UNCOMPILED.
Shared definitions and the existing complete-homogeneous successor law.
The existing a9a4e532 proof bodies are retained; this file changes only
compilation organization. No numerical row or new evaluator is introduced.
-/
namespace ImbalancedChen.P2OriginalSixthHigherMoments
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2OriginalSixthSimplexMoments

def duplicateH {A : Type*} [CommRing A] [Algebra ℚ A]
    (y : Fin 7 → A) (i : Fin 7) : ℕ → A
  | 0 => 1
  | k + 1 => ((k + 1 : ℚ)⁻¹) •
      ∑ j : Fin (k + 1),
        ((∑ r : Fin 7, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
          duplicateH y i (k - j.val)
termination_by k => k
decreasing_by omega

def baryCoefficient (e : Fin 7 → ℕ) : ℚ :=
  (((e 0).factorial *
      P2Winner9NestedEightSimplexMoment.factorialProduct
        (List.ofFn (fun r : Fin 6 => e r.succ)) : ℕ) : ℚ) /
    (((e 0) + (List.ofFn (fun r : Fin 6 => e r.succ)).sum + 6).factorial : ℚ)

def bumped (e : Fin 7 → ℕ) (i : Fin 7) : Fin 7 → ℕ :=
  fun r => e r + unitExponent i r

def integratedPower (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ) : ℝ :=
  ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 7)) k,
    ((Nat.multinomial Finset.univ e : ℝ) * (baryCoefficient (bumped e i) : ℝ)) *
        ∏ r : Fin 7, y r ^ e r

def completeH {A : Type*} [CommRing A] : List A → ℕ → A
  | [], k => if k = 0 then 1 else 0
  | a :: as, k => ∑ j : Fin (k + 1), a ^ j.val * completeH as (k - j.val)

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


namespace ProofPieces

theorem ofFn_seven {A : Type*} (f : Fin 7 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6] := by rfl

theorem ofFn_six {A : Type*} (f : Fin 6 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5] := by rfl

theorem rational_smul_self (q x : ℚ) : q • x = q * x := by rfl

theorem rational_smul_real (q : ℚ) (x : ℝ) : q • x = (q : ℝ) * x := by rfl

private theorem baryCoefficient_eq_product (e : Fin 7 → ℕ) :
    baryCoefficient e =
      ((∏ r, (e r).factorial : ℕ) : ℚ) / (((∑ r, e r) + 6).factorial : ℚ) := by
  rw [baryCoefficient, P2Winner9NestedEightSimplexMoment.factorialProduct,
    List.map_ofFn, List.prod_ofFn, List.sum_ofFn,
    Fin.prod_univ_succ (fun r : Fin 7 => (e r).factorial),
    Fin.sum_univ_succ (fun r : Fin 7 => e r)]
  rfl

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

theorem integratedPower_eq_factored (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ) :
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

theorem completeH_nil {A : Type*} [CommRing A] (k : ℕ) :
    completeH ([] : List A) k = (if k = 0 then 1 else 0) := by rfl

theorem completeH_zero {A : Type*} [CommRing A] (as : List A) :
    completeH as 0 = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [completeH, Fin.sum_univ_succ, ih]

end ProofPieces
end
end ImbalancedChen.P2OriginalSixthHigherMoments
