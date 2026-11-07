import ImbalancedChen.P5ZU1011OriginalW16NativeGridCells

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Physical completion for every actual original tuple in each W-active
native grid cell. Cell data are fixed before N and before tuple/atom;
the same actual natural factors work for every residue in the cell's
fixed interval. A genuine active small-beta factor attaches to the same
third natural factor. Primitive residual well/rough support remains an
explicit arithmetic input; no factorization/monomial or uniform-family
conclusion is an input. This does not produce beta coefficient unit
regrouping or the analytic W/AP policy licence.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NativeGridFactors
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16NativeGridCells
open U1011OriginalW16AttachedWellSupport (specified)
open U1011OriginalW16SmallBetaMonomials (SmallBetaActive)
open P5U1011JointOverlap

def completedFactors {n : ℕ} (c : WActiveCell n) (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) : ℕ×ℕ×ℕ :=
  U1011OriginalW16FixedCellFactors.completedFactors (nativeBox c) N t A tail
def attachedFactors {n : ℕ} (c : WActiveCell n) (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) (e : ℕ) : ℕ×ℕ×ℕ :=
  U1011OriginalW16FixedCellSmallBeta.attachedFactors (nativeBox c) N t A tail e

/-- True fixed-level full-vector support, exact natural product, and
all three monomials for the finite W native family. The full specified
four-prime support is DERIVED and never assumed. -/
theorem active_cell_physical_data {n N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop)
    (c : WActiveCell n) {t : Four} (ht : t∈cellTuples n N E c.val)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (fixedD c N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<fixedZ c N) :
    actualDwellSupport ((N:ℝ)^((fixedNu c:ℝ)-2*(fixedDelta c:ℝ))) (specified t++tail) ∧
      let abc := completedFactors c N t A tail
      abc.1*abc.2.1*abc.2.2=fullPrefix t*tail.prod ∧
        0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
        ∀kappa:ℝ,0≤kappa → kappa≤(fixedDelta c:ℝ) →
          A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-4*(fixedDelta c:ℝ)) ∧
          (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
            (N:ℝ)^(2-4*(fixedDelta c:ℝ)) ∧
          (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*
            (abc.2.2:ℝ)^2≤(N:ℝ)^(2-39*(fixedDelta c:ℝ)/8) := by
  have hsource := (Finset.mem_filter.mp ht).1
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hjoint := originalU11_mem_joint hn.le hsource
  refine ⟨?_,?_⟩
  · exact U1011OriginalW16FixedCellSupport.attached_well_support hN hjoint (nativeBox c)
      (active_box_valid c) (active_box_positive c) (active_certificate c) (cellTuples_box c ht) tail hresidual
  · exact U1011OriginalW16FixedCellFactors.fixed_factors_uniform_residue hN hsource
      (nativeBox c) (active_box_valid c) (active_box_positive c) (active_certificate c)
      (cellTuples_box c ht) A hA hAupper tail hresidual hrough

/-- The actual beta integer is used in the literal modulus. This is one
box's fixed family, uniformly over all its source tuples and atoms, not
a pointwise midpoint coefficient or a selected-product surrogate for W. -/
theorem active_cell_beta_physical_data {n N enumeration e : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop)
    (c : WActiveCell n) {t : Four} (ht : t∈cellTuples n N E c.val)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (fixedD c N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<fixedZ c N)
    (w ell : ℝ) (hell : 0<ell) (hellsmall : ell≤(fixedDelta c:ℝ)/2)
    (he : SmallBetaActive N enumeration e w ell) :
    let abc := attachedFactors c N t A tail e
    abc.1*abc.2.1*abc.2.2=e*(fullPrefix t*tail.prod) ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0≤kappa → kappa≤(fixedDelta c:ℝ) →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-3*(fixedDelta c:ℝ)) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-3*(fixedDelta c:ℝ)) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*
          (abc.2.2:ℝ)^2≤(N:ℝ)^(2-2*(fixedDelta c:ℝ)) := by
  exact U1011OriginalW16FixedCellSmallBeta.fixed_beta_attached_monomials hN
    (Finset.mem_filter.mp ht).1 (nativeBox c) (active_box_valid c) (active_box_positive c)
    (active_certificate c) (cellTuples_box c ht) A hA hAupper tail hresidual hrough
    w ell hell hellsmall he

end
end ImbalancedChen.P5Z.U1011OriginalW16NativeGridFactors
