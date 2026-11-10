import ImbalancedChen.P5OldFifthFiveCoordinateTree
import ImbalancedChen.LogPrimeBoxIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
SOURCE ONLY / UNCOMPILED / READY=false / ZERO FORMAL CREDIT.

Exact 32-leaf expansion of the Phase10 five-coordinate tree and the
Lebesgue Ico product moment for each of its actual grid1600 child
barycentric weights. The 32-term expansion is displayed as five nested
Bool sums, with no vertex-average or integral identity postulated.
The script's saved parent picks, d, A/B and floor payload are outside
this source and are not assumed or claimed.
-/

namespace ImbalancedChen.P5OldFifthFiveCoordinateBarycentric

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateTree

abbrev Point := Fin 5 → ℝ

def endpoint (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5)
    (e : Bool) (t : Point) : Point :=
  if e then upperEndpointPoint raw c i t else lowerEndpointPoint raw c i t

def factor (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5)
    (e : Bool) (t : Point) : ℝ :=
  if e then coordinateFraction raw c i t
  else 1 - coordinateFraction raw c i t

theorem fraction_endpoint_other (raw : FifthWireRow) (c : ChildIndex)
    (i j : Fin 5) (hij : i ≠ j) (e : Bool) (t : Point) :
    coordinateFraction raw c j (endpoint raw c i e t) =
      coordinateFraction raw c j t := by
  cases e <;>
    simp [endpoint, coordinateFraction, lowerEndpointPoint,
      upperEndpointPoint, hij, hij.symm]

theorem factor_endpoint_other (raw : FifthWireRow) (c : ChildIndex)
    (i j : Fin 5) (hij : i ≠ j) (e f : Bool) (t : Point) :
    factor raw c j f (endpoint raw c i e t) =
      factor raw c j f t := by
  simp [factor, fraction_endpoint_other raw c i j hij e t]

def corner (raw : FifthWireRow) (c : ChildIndex)
    (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) : Point :=
  endpoint raw c 4 e₄
    (endpoint raw c 3 e₃
      (endpoint raw c 2 e₂
        (endpoint raw c 1 e₁
          (endpoint raw c 0 e₀ t))))

def wordWeight (raw : FifthWireRow) (c : ChildIndex)
    (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) : ℝ :=
  factor raw c 0 e₀ t * factor raw c 1 e₁ t *
    factor raw c 2 e₂ t * factor raw c 3 e₃ t *
      factor raw c 4 e₄ t

/-- The recursive tree is literally the sum of its 2^5=32 endpoint
branches. The five sums retain the exact branch order of Phase10. -/
theorem weightedVertexTree_eq_32_words (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) (t : Point) :
    weightedVertexTree picks raw c allFiveCoordinates t =
      ∑ e₀ : Bool, ∑ e₁ : Bool, ∑ e₂ : Bool,
        ∑ e₃ : Bool, ∑ e₄ : Bool,
          wordWeight raw c e₀ e₁ e₂ e₃ e₄ t *
            frozenGap picks raw (corner raw c e₀ e₁ e₂ e₃ e₄ t) := by
  classical
  simp [weightedVertexTree, allFiveCoordinates, Fintype.sum_bool,
    wordWeight, corner, factor, endpoint,
    coordinateFraction, lowerEndpointPoint, upperEndpointPoint,
    Function.update]
  ring

/-- The nested endpoint updates are exactly the corresponding closure
vertex, independent of the starting point. -/
theorem corner_eq_vertexPoint (raw : FifthWireRow) (c : ChildIndex)
    (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) :
    corner raw c e₀ e₁ e₂ e₃ e₄ t =
      vertexPoint raw c (![e₀, e₁, e₂, e₃, e₄]) := by
  funext i
  fin_cases i <;>
    simp [corner, endpoint, vertexPoint, lowerEndpointPoint,
      upperEndpointPoint, Function.update]

theorem integral_fraction_Ico {a b : ℝ} (hab : a < b) :
    (∫ x in Ico a b, (x - a) / (b - a)) = (b - a) / 2 := by
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_div,
    intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  have hne : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  field_simp [hne]
  ring

theorem integral_one_sub_fraction_Ico {a b : ℝ} (hab : a < b) :
    (∫ x in Ico a b, 1 - (x - a) / (b - a)) = (b - a) / 2 := by
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le]
  have hq : IntervalIntegrable (fun x : ℝ => (x - a) / (b - a))
      volume a b :=
    ((continuous_id.sub continuous_const).div_const _).intervalIntegrable a b
  rw [intervalIntegral.integral_sub intervalIntegrable_const hq,
    intervalIntegral.integral_const]
  have hf := integral_fraction_Ico hab
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le] at hf
  rw [hf]
  ring

def childVolume (raw : FifthWireRow) (c : ChildIndex) : ℝ :=
  ∏ i : Fin 5, childRight raw c i - childLeft raw c i

/-- The actual half-open five-box has one thirty-second of its product
volume in each of the 32 barycentric product weights. -/
theorem integral_vertexWeight_eq_childVolume_div_32
    (raw : FifthWireRow) (c : ChildIndex) (ε : VertexChoice) :
    (∫ t in childBox raw c, vertexWeight raw c ε t) =
      childVolume raw c / 32 := by
  have hbox : childBox raw c =
      logPrimeBox (childLeft raw c) (childRight raw c) := by
    ext t
    simp [childBox, mem_logPrimeBox, childLeft, childRight]
  rw [hbox]
  unfold vertexWeight logPrimeBox coordinateFraction
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hmoment : ∀ i : Fin 5,
      (∫ x in Ico (childLeft raw c i) (childRight raw c i),
        if ε i then (x - childLeft raw c i) /
            (childRight raw c i - childLeft raw c i)
        else 1 - (x - childLeft raw c i) /
            (childRight raw c i - childLeft raw c i)) =
      (childRight raw c i - childLeft raw c i) / 2 := by
    intro i
    have hab := child_span_pos raw c i
    by_cases he : ε i
    · simpa [he] using integral_fraction_Ico hab
    · simpa [he] using integral_one_sub_fraction_Ico hab
  simp_rw [hmoment]
  simp [childVolume, Finset.prod_div_distrib, Fin.prod_univ_succ]

theorem wordWeight_eq_vertexWeight (raw : FifthWireRow) (c : ChildIndex)
    (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) :
    wordWeight raw c e₀ e₁ e₂ e₃ e₄ t =
      vertexWeight raw c (![e₀, e₁, e₂, e₃, e₄]) t := by
  simp [wordWeight, vertexWeight, factor, Fin.prod_univ_succ]
  ring

end
end ImbalancedChen.P5OldFifthFiveCoordinateBarycentric
