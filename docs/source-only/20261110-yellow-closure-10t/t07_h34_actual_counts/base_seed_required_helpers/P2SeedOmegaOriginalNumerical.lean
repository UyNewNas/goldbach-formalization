import ImbalancedChen.P2SeedOriginalQ80Darboux
import ImbalancedChen.P2SeedOmegaLiteralFunctional

/-!
SOURCE ONLY / UNCOMPILED / ALL FINITE BODIES UNEVALUATED.

Direct real binding of certify_second_seed_omega_envelope.py and its
8192-cell Q80 certificate. The final theorem is an inequality for the
already defined actualJ2omega, not a definition of a surrogate gain.
No saved endpoint is a hypothesis. The closed endpoint identity and all
integer guards below are proof bodies submitted for remote evaluation.
This numerical theorem supplies no enhanced arithmetic count licence.
-/

namespace ImbalancedChen.P2SeedOmegaOriginalNumerical

noncomputable section
open Set MeasureTheory
open scoped Interval BigOperators
open P2SeedOriginalQ80Darboux
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2DirectedLogRounding
open P2SeedOmegaLiteralFibre
open P2SeedOmegaLiteralFunctional

local notation "X" => Expr.var
local notation "R" => Expr.rat
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.div

def power (x : Expr) : ℕ → Expr
  | 0 => R 1
  | n+1 => power x n *ₑ x

theorem power_real (x : Expr) (n : ℕ) (u : ℝ) :
    (power x n).real u = x.real u ^ n := by
  induction n with
  | zero => simp [power,Expr.real]
  | succ n ih => simp [power,Expr.real,ih,pow_succ]

def corrExpr : Expr := (X -ₑ R 1).log /ₑ X
def negativeExpr : Expr := ((R (227/50) *ₑ (R 1 -ₑ X)) -ₑ R 1).log /ₑ
  (X *ₑ (R 1 -ₑ X))
def triangleExpr (top : ℚ) : Expr :=
  ((R top *ₑ (R 1 -ₑ (R 2 *ₑ X))) /ₑ
    (X *ₑ ((R 1 -ₑ X) -ₑ R top))).log /ₑ (X *ₑ (R 1 -ₑ X))
def rectangleExpr (lo hi : ℚ) : Expr :=
  ((R hi *ₑ ((R 1 -ₑ X) -ₑ R lo)) /ₑ
    (R lo *ₑ ((R 1 -ₑ X) -ₑ R hi))).log /ₑ (X *ₑ (R 1 -ₑ X))
def badOldFirstExpr : Expr :=
  ((R (10/29) *ₑ X) /ₑ
    ((R 1 -ₑ (R 2 *ₑ X)) *ₑ ((R 1 -ₑ X) -ₑ R (10/29)))).log /ₑ
      (X *ₑ (R 1 -ₑ X))
def badMassFirstExpr : Expr :=
  (R (10/29) /ₑ (R 1 -ₑ (R 2 *ₑ X))).log /ₑ X
def badMassSecondExpr : Expr := (R (10/29) /ₑ X).log /ₑ X

def kernel : Fin 13 → Expr := ![
  corrExpr,corrExpr,negativeExpr,negativeExpr,negativeExpr,
  triangleExpr (10/29),rectangleExpr (10/29) (25/61),
  triangleExpr (100/353),rectangleExpr (100/353) (10/29),
  badOldFirstExpr,triangleExpr (10/29),badMassFirstExpr,badMassSecondExpr]
def left : Fin 13 → ℚ := ![
  2,2,50/227,50/227,50/227,50/227,50/227,50/227,50/227,
  19/58,1/3,19/58,1/3]
def right : Fin 13 → ℚ := ![
  177/50,253/100,5/11,10/29,25/61,10/29,100/353,100/353,100/353,
  1/3,10/29,1/3,10/29]
def integralValue (i : Fin 13) : ℝ :=
  ∫ u in (left i:ℝ)..(right i:ℝ),(kernel i).real u
def integralBound (i : Fin 13) : I80 := darboux (kernel i) (left i) (right i) 8192

theorem original_piece_order (i : Fin 13) : left i < right i := by
  fin_cases i <;> norm_num [left,right]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem original_piece_guards (i : Fin 13) :
    CellsValid (kernel i) (left i) (right i) 8192 := by
  fin_cases i <;> decide

theorem integralBound_contains (i : Fin 13) :
    (integralBound i).Contains (integralValue i) :=
  darboux_contains (kernel i) (left i) (right i) 8192
    (original_piece_order i) (by norm_num) (original_piece_guards i)

def e01 : Expr := (R ((227/50)/(353/100))).log
def e12 : Expr := (R ((353/100)/(29/10))).log
def e23 : Expr := (R ((29/10)/(61/25))).log
def e3b : Expr := (R ((61/25)/(11/5))).log
def e2b : Expr := (R ((29/10)/(11/5))).log
def omega : Expr := R (70893/125000)

/-- Literal source Γ9--21 mass envelopes, including both final units. -/
def massExpr : Fin 13 → Expr := ![
  omega *ₑ (R (353/100+61/25) *ₑ (R ((353/100)/(61/25))).log -ₑ
    R (2*(353/100-61/25))),
  (omega *ₑ (R (353/100) -ₑ R (29/10) *ₑ (R 1 +ₑ e12))) *ₑ e2b,
  (omega *ₑ e12) *ₑ (R (29/10) *ₑ (e23 -ₑ R 1) +ₑ R (61/25)),
  (omega *ₑ (R (227/50) -ₑ R (353/100) *ₑ (R 1 +ₑ e01))) *ₑ e3b,
  ((omega *ₑ e01) *ₑ R (353/100-29/10)) *ₑ e2b,
  (omega *ₑ e01) *ₑ (R (29/10) *ₑ (e2b -ₑ R 1) +ₑ R (11/5)),
  ((omega *ₑ e12) *ₑ R (29/10-61/25)) *ₑ e3b,
  (R (29/10) *ₑ power e23 4) /ₑ R 24,
  ((R (29/10) *ₑ power e23 3) *ₑ e3b) /ₑ R 6,
  ((R (61/25) *ₑ power e23 2) *ₑ power e3b 2) /ₑ R 4,
  ((R (61/25) *ₑ e12) *ₑ power e3b 3) /ₑ R 6,
  (((R (61/25) *ₑ e23) *ₑ power e3b 4) /ₑ R 24) +ₑ
    ((R (29/10) *ₑ power e3b 4) /ₑ R 24),
  ((R (61/25) *ₑ power e3b 6) /ₑ R 720) +ₑ
    ((R (61/25) *ₑ power e3b 5) /ₑ R 120)]

def massSum : ℕ → Expr
  | 0 => R 0
  | n+1 => massSum n +ₑ massExpr ⟨n % 13,Nat.mod_lt _ (by norm_num)⟩
def switchExpr : Expr := R ((681/100)/4) *ₑ massSum 13

theorem massExpr_real (i : Fin 13) : (massExpr i).real 0 = switchedMass i := by
  fin_cases i <;>
    norm_num [massExpr,Expr.real,power_real,switchedMass,e01,e12,e23,e3b,e2b,omega,
      l01,l12,l23,l3b,omegaCap,s0,phi1,phi2,phi3,s]

theorem switchExpr_real : switchExpr.real 0 = switchCost := by
  simp only [switchExpr,Expr.real,massSum]
  norm_num only
  rw [massExpr_real,massExpr_real,massExpr_real,massExpr_real,massExpr_real,
    massExpr_real,massExpr_real,massExpr_real,massExpr_real,massExpr_real,
    massExpr_real,massExpr_real,massExpr_real]
  norm_num [switchCost,K,Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem switchExpr_guards : switchExpr.Valid (I80.point 0) := by decide

def switchBound : I80 := switchExpr.eval (I80.point 0)
theorem switchBound_contains : switchBound.Contains switchCost := by
  rw [← switchExpr_real]
  exact switchExpr.eval_contains (I80.point_contains 0) switchExpr_guards

def sourceValue : ℝ :=
  (-(4*integralValue 0+integralValue 1)+
    (integralValue 2+integralValue 3+integralValue 4)-
    (integralValue 5+integralValue 6+integralValue 7+integralValue 8)-
    (((681/100)*(70893/125000)*(227/50)/4)*(integralValue 11+integralValue 12)-
      (integralValue 9+integralValue 10))-switchCost)/5

theorem sourceValue_eq_actual : sourceValue = actualJ2omega := by
  rw [actualJ2omega_eq_original_expression]
  norm_num [sourceValue,integralValue,kernel,left,right,corrExpr,negativeExpr,
    triangleExpr,rectangleExpr,badOldFirstExpr,badMassFirstExpr,badMassSecondExpr,
    Expr.real,originalOneDimensionalExpression,correction,negative,
    triangleLogIntegral,rectangleLogIntegral,badMassLog,badOldLog,
    s0,phi1,phi2,phi3,a0,a1,a2,a3,b,corner,K,omegaCap]

def sourceBound : I80 :=
  let baseline := ((I80.point 4).mul (integralBound 0)).add (integralBound 1)
  let lower := ((integralBound 2).add (integralBound 3)).add (integralBound 4)
  let ordinary := (((integralBound 5).add (integralBound 6)).add (integralBound 7)).add
    (integralBound 8)
  let repair := ((I80.point ((681/100)*(70893/125000)*(227/50)/4)).mul
    ((integralBound 11).add (integralBound 12))).sub
    ((integralBound 9).add (integralBound 10))
  ((((baseline.neg.add lower).sub ordinary).sub repair).sub switchBound).div (I80.point 5)

theorem sourceBound_contains : sourceBound.Contains actualJ2omega := by
  rw [← sourceValue_eq_actual]
  have hb := I80.neg_contains (I80.add_contains
    (I80.mul_contains (I80.point_contains 4) (integralBound_contains 0))
    (integralBound_contains 1))
  have hn := I80.add_contains
    (I80.add_contains (integralBound_contains 2) (integralBound_contains 3))
    (integralBound_contains 4)
  have ho := I80.add_contains (I80.add_contains
    (I80.add_contains (integralBound_contains 5) (integralBound_contains 6))
    (integralBound_contains 7)) (integralBound_contains 8)
  have hr := I80.sub_contains (I80.mul_contains
    (I80.point_contains ((681/100)*(70893/125000)*(227/50)/4))
    (I80.add_contains (integralBound_contains 11) (integralBound_contains 12)))
    (I80.add_contains (integralBound_contains 9) (integralBound_contains 10))
  have h := I80.div_contains
    (I80.sub_contains (I80.sub_contains (I80.sub_contains
      (I80.add_contains hb hn) ho) hr) switchBound_contains)
    (I80.point_contains 5) (by norm_num [I80.point,I80.ofEnclosure,Enclosure.point,Q])
  convert h using 1 <;> norm_num [sourceBound,sourceValue]

/-- Exact published endpoint; this is an unevaluated proof body, not an
assumption read from JSON and not evidence of a successful kernel run. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem original_8192_lower_endpoint : sourceBound.lo = 24479824718463837928127 := by
  decide

theorem actualJ2omega_gt_safe_base : (20249/1000000:ℝ) < actualJ2omega := by
  have h := sourceBound_contains.1
  change ((sourceBound.lo:ℚ)/Q:ℝ) ≤ actualJ2omega at h
  rw [original_8192_lower_endpoint] at h
  have hsafe : (20249/1000000:ℝ) <
      ((24479824718463837928127:ℚ)/Q:ℝ) := by norm_num [Q]
  exact hsafe.trans_le h

theorem actualJ2omega_required_lower_bound : RequiredLowerBound :=
  actualJ2omega_gt_safe_base.le

theorem actualJ2omega_gt_one_fiftieth : (1/50:ℝ) < actualJ2omega :=
  (by norm_num : (1/50:ℝ) < 20249/1000000).trans actualJ2omega_gt_safe_base

end
end ImbalancedChen.P2SeedOmegaOriginalNumerical
