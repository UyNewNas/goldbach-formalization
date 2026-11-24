import ImbalancedChen.P2Winner9Row21Arithmetic
import ImbalancedChen.P2Winner9CurvatureFullExactAssembly
import Mathlib.Order.Interval.Finset.Nat

/-! The kernel-checked project arithmetic agrees with the original row21
T10 plus ten D2 fraction assembly and both rounding predicates. -/

namespace ImbalancedChen.P2Winner9Row21SourceBridge

open scoped BigOperators
open ImbalancedChen.P2Winner9Row21Arithmetic

private theorem sumNat_eq_finset (f : Fin n → ℕ) :
    sumNat f = ∑ i, f i :=
  Fin.sum_ofFn f

private theorem sumInt_eq_finset (f : Fin n → ℤ) :
    sumInt f = ∑ i, f i :=
  Fin.sum_ofFn f

private theorem range_sum_eq_finset {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [Finset.sum_eq_multiset_sum]
  rfl

private theorem t10_range_sum_eq_finset {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ((List.range' 2 9).map f).sum = ∑ i ∈ Finset.Icc 2 10, f i := by
  rw [Finset.sum_eq_multiset_sum, Nat.Icc_eq_range']
  rfl

private theorem gap_total_g : P2Winner9CurvatureExactMomentFloor.gapTotal g = G :=
  (sumNat_eq_finset g).symm

def row21 : P2Winner9CurvatureFullExactAssembly.SimplexData where
  gaps := g
  y := y
  L := L
  U := U
  deviations := b
  maxima := v
  jensenNum := reconstructedJensen.num.toNat
  jensenDen := reconstructedJensen.den
  gapsPos := gap_total_g.symm ▸ row21_positive_primitives.1
  LPos := row21_positive_primitives.2.1
  UPos := row21_positive_primitives.2.2.1
  maximaPos := row21_positive_primitives.2.2.2.1
  jensenDenPos := row21_positive_primitives.2.2.2.2

private theorem row_gapTotal_eq : P2Winner9CurvatureExactMomentFloor.gapTotal row21.gaps = G :=
  gap_total_g

private theorem homogeneous_eq (k : ℕ) (hk : k ≤ 10) :
    P2Winner9CurvatureFullExactAssembly.homogeneous row21.y k = homogeneous k :=
  (coefficient_eq_source k hk).symm

private theorem powerMoment_eq (k : ℕ) :
    P2Winner9CurvatureFullExactAssembly.powerMoment row21 k = powerMoment k :=
  (sumNat_eq_finset (fun i : Fin 9 => g i * (y i)^k)).symm

theorem weightedMoment_eq (k : ℕ) (hk : k ≤ 10) :
    P2Winner9CurvatureFullExactAssembly.weightedMoment row21 k = weightedMoment k := by
  rw [P2Winner9CurvatureFullExactAssembly.weightedMoment, weightedMoment, range_sum_eq_finset]
  apply Finset.sum_congr rfl
  intro j _
  rw [homogeneous_eq _ (Nat.le_trans (Nat.sub_le k j) hk), powerMoment_eq]

private theorem H_eq : P2Winner9CurvatureFullExactAssembly.H row21 = H := by
  rw [P2Winner9CurvatureFullExactAssembly.H, H, row_gapTotal_eq]

private theorem meanNumerator_eq :
    P2Winner9CurvatureFullExactAssembly.meanNumerator row21 = t10MeanNumerator := by
  simp only [P2Winner9CurvatureFullExactAssembly.meanNumerator, row_gapTotal_eq, t10MeanNumerator,
    sumNat_eq_finset]
  rfl

private theorem D_eq : P2Winner9CurvatureFullExactAssembly.D row21 = D := by
  rw [P2Winner9CurvatureFullExactAssembly.D, D, H_eq]
  rfl

private theorem z_eq (k : ℕ) (hk : k ≤ 10) :
    P2Winner9CurvatureFullExactAssembly.z row21 k = z k := by
  rw [P2Winner9CurvatureFullExactAssembly.z, z, weightedMoment_eq k hk, H_eq, row_gapTotal_eq, meanNumerator_eq]

theorem t10_numerator_eq : P2Winner9CurvatureFullExactAssembly.t10Numerator row21 = t10Numerator := by
  rw [P2Winner9CurvatureFullExactAssembly.t10Numerator, t10Numerator, t10_range_sum_eq_finset]
  refine congrArg (fun t : ℤ => t * (L : ℤ)^10) ?_
  apply Finset.sum_congr rfl
  intro k hk
  rw [z_eq k (Finset.mem_Icc.mp hk).2, D_eq]

private theorem t10_denominator_eq :
    P2Winner9CurvatureFullExactAssembly.t10Denominator row21 = t10Denominator := by
  rw [P2Winner9CurvatureFullExactAssembly.t10Denominator, t10Denominator, row_gapTotal_eq, D_eq]
  rfl

private theorem curvature_numerator_eq (j : Fin 10) :
    P2Winner9CurvatureExactMomentFloor.curvatureNumerator row21.gaps (row21.deviations j) row21.L =
      curvatureNumerator j := by
  simp only [P2Winner9CurvatureExactMomentFloor.curvatureNumerator, P2Winner9CurvatureExactMomentFloor.signedMomentNumerator,
    curvatureNumerator, signedMomentNumerator, row_gapTotal_eq, sumInt_eq_finset]
  rfl

private theorem curvature_denominator_eq (j : Fin 10) :
    P2Winner9CurvatureExactMomentFloor.curvatureDenominator row21.gaps row21.U (row21.maxima j) =
      curvatureDenominator j := by
  rw [P2Winner9CurvatureExactMomentFloor.curvatureDenominator, curvatureDenominator, row_gapTotal_eq]
  rfl

/-- Retain the original unreduced numerator and denominator. -/
def erase (p : P2Winner9CurvatureFullExactAssembly.ExactFraction) : ExactFraction :=
  ⟨p.num, p.den⟩

private theorem erase_add (p q : P2Winner9CurvatureFullExactAssembly.ExactFraction) :
    erase (P2Winner9CurvatureFullExactAssembly.add p q) = addFrac (erase p) (erase q) := rfl

private theorem erase_sumFractions (ps : List P2Winner9CurvatureFullExactAssembly.ExactFraction) :
    erase (P2Winner9CurvatureFullExactAssembly.sumFractions ps) = sumFractions (ps.map erase) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [P2Winner9CurvatureFullExactAssembly.sumFractions, erase_add, ih, List.map_cons, sumFractions,
      List.foldr_cons]

private theorem erase_t10 :
    erase (P2Winner9CurvatureFullExactAssembly.t10 row21) = ⟨t10Numerator, t10Denominator⟩ := by
  change (⟨P2Winner9CurvatureFullExactAssembly.t10Numerator row21, P2Winner9CurvatureFullExactAssembly.t10Denominator row21⟩ :
    ExactFraction) = _
  rw [t10_numerator_eq, t10_denominator_eq]

private theorem erase_transverse (j : Fin 10) :
    erase (P2Winner9CurvatureFullExactAssembly.transverse row21 j) =
      ⟨curvatureNumerator j, curvatureDenominator j⟩ := by
  change (⟨P2Winner9CurvatureExactMomentFloor.curvatureNumerator row21.gaps (row21.deviations j) row21.L,
    P2Winner9CurvatureExactMomentFloor.curvatureDenominator row21.gaps row21.U (row21.maxima j)⟩ :
    ExactFraction) = _
  rw [curvature_numerator_eq, curvature_denominator_eq]

private theorem erase_transverseTerms :
    (P2Winner9CurvatureFullExactAssembly.transverseTerms row21).map erase =
      List.ofFn (fun j : Fin 10 => (⟨curvatureNumerator j, curvatureDenominator j⟩ : ExactFraction)) := by
  rw [P2Winner9CurvatureFullExactAssembly.transverseTerms, List.map_ofFn]
  exact congrArg List.ofFn (funext erase_transverse)

theorem total_numerator_denominator_eq :
    erase (P2Winner9CurvatureFullExactAssembly.total row21) = total := by
  rw [P2Winner9CurvatureFullExactAssembly.total, total, erase_add, erase_t10, erase_sumFractions, erase_transverseTerms]

private theorem jensen_floor_eq (num den t raw : ℕ) :
    P2Winner9CurvatureExactMomentFloor.jensenProductFloorQ96 num den t raw =
      jensenProductFloorQ96 num den t raw := rfl

theorem row21_original_rounding :
    P2Winner9CurvatureExactMomentFloor.curvatureFloorQ80 (P2Winner9CurvatureFullExactAssembly.total row21).num
      (P2Winner9CurvatureFullExactAssembly.total row21).den observedTotalTFloorQ80 ∧
    P2Winner9CurvatureExactMomentFloor.jensenProductFloorQ96 row21.jensenNum row21.jensenDen
      observedTotalTFloorQ80 observedCurvatureRawQ96 := by
  constructor
  · change curvatureFloorQ80 (erase (P2Winner9CurvatureFullExactAssembly.total row21)).num
      (erase (P2Winner9CurvatureFullExactAssembly.total row21)).den observedTotalTFloorQ80
    rw [total_numerator_denominator_eq]
    exact row21_exact_total_rounding
  · rw [jensen_floor_eq, show row21.jensenNum = reconstructedJensen.num.toNat from rfl,
      show row21.jensenDen = reconstructedJensen.den from rfl]
    exact row21_exact_jensen_rounding

/-- The original row21 Q96 floor is directed below its exact curvature price. -/
theorem row21_raw_arithmetic_lower :
    (observedCurvatureRawQ96 : ℚ) / P2Winner9CurvatureExactMomentFloor.q96 ≤
      ((row21.jensenNum : ℚ) / row21.jensenDen) *
        (1 + P2Winner9CurvatureFullExactAssembly.value
          (P2Winner9CurvatureFullExactAssembly.total row21)) :=
  P2Winner9CurvatureFullExactAssembly.total_directed_floor_semantics
    row21 observedTotalTFloorQ80 observedCurvatureRawQ96
    row21_original_rounding.1 row21_original_rounding.2

end ImbalancedChen.P2Winner9Row21SourceBridge
