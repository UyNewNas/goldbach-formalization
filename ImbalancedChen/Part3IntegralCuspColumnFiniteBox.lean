import ImbalancedChen.Part3CuspColumnRectangleBudget
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Quantitative finite raw-column box for actual integral cusp horoballs
meeting a fixed bounded physical rectangle.  Both integer column entries
(a,c) have square budgets inherited from actual inverse Mobius height.
The output is a literal finite integer box, with cardinal (2*n+1)^2.
This is finiteness of RAW COLUMNS, not matrices: their translation fibers
remain infinite.  No Gamma0 cusp enumeration or quotient injection follows.
-/
namespace ImbalancedChen.Part3.IntegralCuspColumnFiniteBox20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b CuspColumnRectangleBudget20261026b
open Gamma0GeneralCuspUnitPeriod20261025a

def columnBox (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).product (Finset.Icc (-(n : ℤ)) (n : ℤ))

theorem columnBox_card (n : ℕ) : (columnBox n).card = (2*n+1)^2 := by
  have hc : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp only [columnBox, Finset.card_product, hc, pow_two]

/-- Real square budgets produce an actual finite integer box, even when
the supplied real bounds are negative and the candidate set is empty. -/
theorem integer_pair_square_budget_box (A C : ℝ) :
    ∃ n : ℕ, ∀ p : ℤ × ℤ,
      ((p.1 : ℝ)^2 ≤ A ∧ (p.2 : ℝ)^2 ≤ C) → p ∈ columnBox n := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1 : ℝ) (max A C))
  have hn1 : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hA : A < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_left A C).trans (le_max_right _ _)) hn
  have hC : C < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_right A C).trans (le_max_right _ _)) hn
  have hnsq : (n : ℝ) ≤ (n : ℝ)^2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1.le)]
  refine ⟨n, ?_⟩
  intro p hp
  have haSq : (p.1 : ℝ)^2 ≤ (n : ℝ)^2 := hp.1.trans (hA.le.trans hnsq)
  have hcSq : (p.2 : ℝ)^2 ≤ (n : ℝ)^2 := hp.2.trans (hC.le.trans hnsq)
  have haAbsR : |(p.1 : ℝ)| ≤ (n : ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg n)).mp
    simpa only [sq_abs] using haSq
  have hcAbsR : |(p.2 : ℝ)| ≤ (n : ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg n)).mp
    simpa only [sq_abs] using hcSq
  have haAbs : |p.1| ≤ (n : ℤ) := by exact_mod_cast haAbsR
  have hcAbs : |p.2| ≤ (n : ℤ) := by exact_mod_cast hcAbsR
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (abs_le.mp haAbs), Finset.mem_Icc.mpr (abs_le.mp hcAbs)⟩

/-- Actual integral columns whose high cusp image meets the literal
coordinate rectangle; no chosen representatives or cusp classes occur. -/
def rectangleColumnHits (H eps X M : ℝ) : Set (ℤ × ℤ) :=
  {p | ∃ g : SL(2, ℤ), p = (g 0 0,g 1 0) ∧ ∃ z : UpperHalfPlane,
    z ∈ g • heightHalfSpace H ∧ |z.re| ≤ X ∧ eps ≤ z.im ∧ z.im ≤ M}

/-- Explicit column-square budgets are retained before taking finiteness. -/
theorem rectangleColumnHits_square_budgets {H eps X M : ℝ}
    (hH : 0 < H) (heps : 0 < eps) (hX : 0 ≤ X)
    {p : ℤ × ℤ} (hp : p ∈ rectangleColumnHits H eps X M) :
    (p.1 : ℝ)^2 ≤ 2*X^2/(H*eps)+2*M/H ∧ (p.2 : ℝ)^2 ≤ 1/(H*eps) := by
  obtain ⟨g,rfl,z,hz,hx,hylo,hyhi⟩ := hp
  have hzR : z ∈ integralReal g • heightHalfSpace H := by
    simpa only [Set.mem_smul_set,integralReal_smul] using hz
  have hb := rectangle_column_square_bounds (integralReal g) hH heps hX hzR hx hylo hyhi
  simpa [integralReal,Matrix.SpecialLinearGroup.map_apply_coe] using (And.intro hb.2 hb.1)

/-- A produced literal finite raw-column box and its exact cardinal
budget.  Infinite translation fibers of full matrices are not counted. -/
theorem rectangleColumnHits_finite_box {H eps X M : ℝ}
    (hH : 0 < H) (heps : 0 < eps) (hX : 0 ≤ X) :
    ∃ n : ℕ, rectangleColumnHits H eps X M ⊆ (columnBox n : Set (ℤ × ℤ)) ∧
      (rectangleColumnHits H eps X M).Finite ∧
      (rectangleColumnHits H eps X M).ncard ≤ (2*n+1)^2 := by
  obtain ⟨n,hn⟩ := integer_pair_square_budget_box
    (2*X^2/(H*eps)+2*M/H) (1/(H*eps))
  have hsub : rectangleColumnHits H eps X M ⊆ (columnBox n : Set (ℤ × ℤ)) := by
    intro p hp
    exact hn p (rectangleColumnHits_square_budgets hH heps hX hp)
  have hfin : (rectangleColumnHits H eps X M).Finite := (columnBox n).finite_toSet.subset hsub
  refine ⟨n,hsub,hfin,?_⟩
  have hcard := Set.ncard_le_ncard hsub (columnBox n).finite_toSet
  simpa only [Set.ncard_coe_finset,columnBox_card] using hcard

end
end ImbalancedChen.Part3.IntegralCuspColumnFiniteBox20261026b
