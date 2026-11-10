import ImbalancedChen.P2SeedOriginalQ80Darboux
import ImbalancedChen.P2EnhancedSeedActualSevenLogIdentity

/-!
SOURCE ONLY / UNCOMPILED / FINITE BODIES UNEVALUATED.

Literal 4096-cell certificate for the actual seven-term feedback at J=1/50.
The eleven affine pieces are exactly the original three singleton pieces
and 3+1+2+2 pair pieces. In particular D5- is absent and D6 is untruncated.
This pays a numerical real-functional obligation only. No analytic
adopted-count licence, predecessor licence or original root estimate is
assumed or asserted.
-/

namespace ImbalancedChen.P2SeedFeedbackOriginalNumerical

noncomputable section
open Set MeasureTheory
open scoped Interval
open P2SeedOriginalQ80Darboux
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2DirectedLogRounding
open P2EnhancedSeedActualFeedbackAssembly
open P2EnhancedSeedActualSevenLogIdentity

local notation "X" => Expr.var
local notation "R" => Expr.rat
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.div

def singleRatio : Expr := R (11/5) /ₑ ((R (227/50) *ₑ (R 1 -ₑ X)) -ₑ R 1)
def pairRatio (lo hi : Expr) : Expr :=
  (hi *ₑ ((R 1 -ₑ X) -ₑ lo)) /ₑ (lo *ₑ ((R 1 -ₑ X) -ₑ hi))
def ratio : Fin 11 → Expr := ![
  singleRatio,singleRatio,singleRatio,
  pairRatio (R (117/227) -ₑ X) (R (10/29)),
  pairRatio X (R (10/29)),
  pairRatio X (R 1 -ₑ R 2 *ₑ X),
  pairRatio (R (10/29)) (R (25/61)),
  pairRatio (R 1 -ₑ R (16/5) *ₑ X) (R (100/353)),
  pairRatio X (R (100/353)),
  pairRatio (R 1 -ₑ R (16/5) *ₑ X) (R (10/29)),
  pairRatio (R (100/353)) (R (10/29))]
def kernel (i : Fin 11) : Expr :=
  (R (1/50) *ₑ (ratio i).log) /ₑ (X *ₑ (R 1 -ₑ X))
def left : Fin 11 → ℚ := ![
  67/227,67/227,67/227,50/227,117/454,19/58,50/227,
  1265/5648,5/21,50/227,1265/5648]
def right : Fin 11 → ℚ := ![
  5/11,10/29,25/61,117/454,19/58,1/3,100/353,
  5/21,100/353,1265/5648,100/353]
def unweightedKernel (i : Fin 11) (u : ℝ) : ℝ :=
  Real.log ((ratio i).real u)/(u*(1-u))
def unweightedValue (i : Fin 11) : ℝ :=
  ∫ u in (left i:ℝ)..(right i:ℝ),unweightedKernel i u
def integralValue (i : Fin 11) : ℝ :=
  ∫ u in (left i:ℝ)..(right i:ℝ),(kernel i).real u
def integralBound (i : Fin 11) : I80 := darboux (kernel i) (left i) (right i) 4096

theorem original_piece_order (i : Fin 11) : left i < right i := by
  fin_cases i <;> norm_num [left,right]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem original_piece_guards (i : Fin 11) :
    CellsValid (kernel i) (left i) (right i) 4096 := by
  fin_cases i <;> decide

theorem integralBound_contains (i : Fin 11) :
    (integralBound i).Contains (integralValue i) :=
  darboux_contains (kernel i) (left i) (right i) 4096
    (original_piece_order i) (by norm_num) (original_piece_guards i)

theorem integralValue_eq_scale (i : Fin 11) :
    integralValue i = (1/50:ℝ)*unweightedValue i := by
  have he : (kernel i).real = fun u => (1/50:ℝ)*unweightedKernel i u := by
    funext u
    simp only [kernel,Expr.real,unweightedKernel,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    ring
  rw [integralValue,he,intervalIntegral.integral_const_mul]
  rfl

theorem singleton_values (j : Fin 3) :
    unweightedValue ⟨j.val,by omega⟩ = singletonCoefficient j := by
  unfold singletonCoefficient
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (show P2EnhancedSeedSingletonPrimitive.uStar ≤ P2EnhancedSeedSingletonPrimitive.cap j by
      fin_cases j <;> norm_num [P2EnhancedSeedSingletonPrimitive.uStar,
        P2EnhancedSeedSingletonPrimitive.cap])]
  fin_cases j <;>
    norm_num [unweightedValue,unweightedKernel,ratio,singleRatio,left,right,Expr.real,
      P2EnhancedSeedSingletonPrimitive.singletonLogKernel,P2EnhancedSeedSingletonPrimitive.S,
      P2EnhancedSeedSingletonPrimitive.profile,P2EnhancedSeedSingletonPrimitive.s0,
      P2EnhancedSeedSingletonPrimitive.uStar,P2EnhancedSeedSingletonPrimitive.cap]

theorem d5_values : d5Logs = unweightedValue 3+unweightedValue 4+unweightedValue 5 := by
  norm_num [d5Logs,unweightedValue,unweightedKernel,ratio,pairRatio,left,right,Expr.real,
    P2EnhancedSeedD5PlusLogFubini.logSlice,P2EnhancedSeedSingletonPrimitive.a0,
    P2EnhancedSeedD5PlusGeometry.cutOne,P2EnhancedSeedD5PlusGeometry.cutTwo,
    P2EnhancedSeedD5PlusGeometry.top,P2EnhancedSeedD5PlusGeometry.supportSum,
    P2EnhancedSeedD5PlusGeometry.cap]

theorem d6_value : d6Log = unweightedValue 6 := by
  rw [d6Log,integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (show P2EnhancedSeedPairD6Primitive.uLo ≤ P2EnhancedSeedPairD6Primitive.uHi by
      norm_num [P2EnhancedSeedPairD6Primitive.uLo,P2EnhancedSeedPairD6Primitive.uHi])]
  norm_num [unweightedValue,unweightedKernel,ratio,pairRatio,left,right,Expr.real,
    P2EnhancedSeedPairD6Primitive.uLo,P2EnhancedSeedPairD6Primitive.uHi,
    P2EnhancedSeedPairD6Primitive.vLo,P2EnhancedSeedPairD6Primitive.vHi,
    P2EnhancedSeedInheritedCellBounds.d6OuterSlice,
    P2EnhancedSeedInheritedCellBounds.d6LogArgument]

/-- The missing source-level D7 affine split, retaining its exact support
start and the switch at5/21. Only null integral endpoints are changed. -/
theorem d7_values : d7Log = unweightedValue 7+unweightedValue 8 := by
  let a : ℝ := P2EnhancedSeedPairD7Domain.supportStart
  let c : ℝ := P2EnhancedSeedPairD7Domain.boundaryCut
  let b : ℝ := P2EnhancedSeedPairD7Domain.uHi
  have hac : a ≤ c := by norm_num [a,c,P2EnhancedSeedPairD7Domain.supportStart,
    P2EnhancedSeedPairD7Domain.boundaryCut]
  have hcb : c ≤ b := by norm_num [c,b,P2EnhancedSeedPairD7Domain.boundaryCut,
    P2EnhancedSeedPairD7Domain.uHi]
  have hc := P2EnhancedSeedPairD7Integral.continuousOn_outerSlice
  have hiac : IntervalIntegrable P2EnhancedSeedPairD7Integral.outerSlice volume a c :=
    (hc.mono (fun u hu => ⟨hu.1,hu.2.trans hcb⟩)).intervalIntegrable_of_Icc hac
  have hicb : IntervalIntegrable P2EnhancedSeedPairD7Integral.outerSlice volume c b :=
    (hc.mono (fun u hu => ⟨hac.trans hu.1,hu.2⟩)).intervalIntegrable_of_Icc hcb
  unfold d7Log
  rw [integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le (hac.trans hcb),
    ← intervalIntegral.integral_add_adjacent_intervals hiac hicb]
  congr 1
  · change (∫ u in a..c,P2EnhancedSeedPairD7Integral.outerSlice u)=unweightedValue 7
    unfold unweightedValue
    change (∫ u in a..c,P2EnhancedSeedPairD7Integral.outerSlice u)=
      ∫ u in a..c,unweightedKernel 7 u
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hac] at hu
    rw [P2EnhancedSeedPairD7Integral.outerSlice,P2EnhancedSeedPairD7Integral.logArgument,
      P2EnhancedSeedPairD7Domain.lowerEndpoint_first hu.2]
    norm_num [unweightedKernel,ratio,pairRatio,Expr.real,
      P2EnhancedSeedPairD7Domain.supportLine,P2EnhancedSeedPairD7Domain.uHi]
  · change (∫ u in c..b,P2EnhancedSeedPairD7Integral.outerSlice u)=unweightedValue 8
    unfold unweightedValue
    change (∫ u in c..b,P2EnhancedSeedPairD7Integral.outerSlice u)=
      ∫ u in c..b,unweightedKernel 8 u
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hcb] at hu
    rw [P2EnhancedSeedPairD7Integral.outerSlice,P2EnhancedSeedPairD7Integral.logArgument,
      P2EnhancedSeedPairD7Domain.lowerEndpoint_second hu.1]
    norm_num [unweightedKernel,ratio,pairRatio,Expr.real,P2EnhancedSeedPairD7Domain.uHi]

theorem d8_values : d8Logs = unweightedValue 9+unweightedValue 10 := by
  unfold d8Logs
  rw [← intervalIntegral.integral_of_le
    (show P2EnhancedSeedPairD8Geometry.uLo ≤ P2EnhancedSeedPairD8Geometry.cut by
      norm_num [P2EnhancedSeedPairD8Geometry.uLo,P2EnhancedSeedPairD8Geometry.cut]),
    integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (show P2EnhancedSeedPairD8Geometry.cut ≤ P2EnhancedSeedPairD8Geometry.uHi by
      norm_num [P2EnhancedSeedPairD8Geometry.cut,P2EnhancedSeedPairD8Geometry.uHi])]
  norm_num [unweightedValue,unweightedKernel,ratio,pairRatio,left,right,Expr.real,
    P2EnhancedSeedPairD8Integral.firstSlice,P2EnhancedSeedPairD8Integral.secondSlice,
    P2EnhancedSeedPairD8Integral.logSlice,P2EnhancedSeedPairD8Geometry.uLo,
    P2EnhancedSeedPairD8Geometry.uHi,P2EnhancedSeedPairD8Geometry.cut,
    P2EnhancedSeedPairD8Geometry.vLo,P2EnhancedSeedPairD8Geometry.vHi,
    P2EnhancedSeedPairD8Geometry.supportLine]

def sourceValue : ℝ :=
  (integralValue 0+integralValue 1+integralValue 2+
    integralValue 3+integralValue 4+integralValue 5+integralValue 6+
    integralValue 7+integralValue 8+integralValue 9+integralValue 10)/5

theorem sourceValue_eq_actual : sourceValue = actualFeedback (1/50) := by
  rw [actualFeedback_eq_mul_lambda,lambda_exact_seven_logs,
    ← singleton_values 0,← singleton_values 1,← singleton_values 2,
    d5_values,d6_value,d7_values,d8_values]
  simp only [sourceValue,integralValue_eq_scale]
  ring

def sourceBound : I80 :=
  let sum := ((((((((((integralBound 0).add (integralBound 1)).add (integralBound 2)).add
    (integralBound 3)).add (integralBound 4)).add (integralBound 5)).add
    (integralBound 6)).add (integralBound 7)).add (integralBound 8)).add
    (integralBound 9)).add (integralBound 10)
  sum.div (I80.point 5)

theorem sourceBound_contains : sourceBound.Contains (actualFeedback (1/50)) := by
  rw [← sourceValue_eq_actual]
  unfold sourceBound sourceValue
  apply I80.div_contains ?_ (I80.point_contains 5)
    (by norm_num [I80.point,I80.ofEnclosure,Enclosure.point,Q])
  repeat' first | apply I80.add_contains | exact integralBound_contains _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem original_4096_lower_endpoint : sourceBound.lo = 3152244426576931077198 := by
  decide

theorem actualFeedback_one_fiftieth_gt : (13/5000:ℝ) < actualFeedback (1/50) := by
  have h := sourceBound_contains.1
  change ((sourceBound.lo:ℚ)/Q:ℝ) ≤ actualFeedback (1/50) at h
  rw [original_4096_lower_endpoint] at h
  have hsafe : (13/5000:ℝ) < ((3152244426576931077198:ℚ)/Q:ℝ) := by norm_num [Q]
  exact hsafe.trans_le h

theorem actual_lambda_gt_thirteen_hundredths : (13/100:ℝ) < lambda := by
  have h := actualFeedback_one_fiftieth_gt
  rw [actualFeedback_one_fiftieth] at h
  linarith

end
end ImbalancedChen.P2SeedFeedbackOriginalNumerical
