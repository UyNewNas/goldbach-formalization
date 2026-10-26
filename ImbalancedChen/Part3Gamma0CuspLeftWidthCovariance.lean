import ImbalancedChen.Part3Gamma0GeneralCuspWidth

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Native Gamma0 LEFT covariance of the actual integral cusp width. The
proof transfers genuine conjugated-translation membership by subgroup
conjugation and compares the TWO true least positive widths. It does
not infer cusp equivalence from equal-looking c-entry expressions.
-/

namespace ImbalancedChen.Part3.Gamma0CuspLeftWidthCovariance20261026b

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup UpperHalfPlane
open Gamma0GeneralCuspWidth20261025a

theorem gamma0_conjugate_mem_iff (N : ℕ) (delta x : SL(2, ℤ))
    (hdelta : delta ∈ CongruenceSubgroup.Gamma0 N) :
    delta * x * delta⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      x ∈ CongruenceSubgroup.Gamma0 N := by
  constructor
  · intro hx
    have hm := (CongruenceSubgroup.Gamma0 N).mul_mem
      ((CongruenceSubgroup.Gamma0 N).mul_mem
        ((CongruenceSubgroup.Gamma0 N).inv_mem hdelta) hx) hdelta
    have heq : delta⁻¹ * (delta * x * delta⁻¹) * delta = x := by group
    rwa [heq] at hm
  · intro hx
    exact (CongruenceSubgroup.Gamma0 N).mul_mem
      ((CongruenceSubgroup.Gamma0 N).mul_mem hdelta hx)
      ((CongruenceSubgroup.Gamma0 N).inv_mem hdelta)

/-- The left Gamma0 factor conjugates the actual integral stabilizer;
the direction of multiplication is explicit and is not a coset premise. -/
theorem conjugated_translation_left_iff (N : ℕ) (delta r : SL(2, ℤ))
    (hdelta : delta ∈ CongruenceSubgroup.Gamma0 N) (k : ℤ) :
    (delta * r) * ModularGroup.T ^ k * (delta * r)⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      r * ModularGroup.T ^ k * r⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  have heq : (delta * r) * ModularGroup.T ^ k * (delta * r)⁻¹ =
      delta * (r * ModularGroup.T ^ k * r⁻¹) * delta⁻¹ := by group
  rw [heq]
  exact gamma0_conjugate_mem_iff N delta _ hdelta

/-- Positive levels: each genuine least positive period divides every
other period after the exact membership transfer. -/
theorem cuspWidth_left_mul_of_pos (N : ℕ) (hN : 0 < N) (delta r : SL(2, ℤ))
    (hdelta : delta ∈ CongruenceSubgroup.Gamma0 N) :
    cuspWidth N (delta * r) = cuspWidth N r := by
  apply Nat.le_antisymm
  · apply cuspWidth_minimal N hN (delta * r) (cuspWidth N r) (cuspWidth_pos N hN r)
    apply (conjugated_translation_left_iff N delta r hdelta _).mpr
    exact (conjugated_translation_mem_iff_width_dvd N hN r _).mpr dvd_rfl
  · apply cuspWidth_minimal N hN r (cuspWidth N (delta * r))
      (cuspWidth_pos N hN (delta * r))
    apply (conjugated_translation_left_iff N delta r hdelta _).mp
    exact (conjugated_translation_mem_iff_width_dvd N hN (delta * r) _).mpr dvd_rfl

/-- The native formula also gives width zero at level zero, so the
covariance identity itself is valid without a positive-level restriction. -/
theorem cuspWidth_left_mul (N : ℕ) (delta r : SL(2, ℤ))
    (hdelta : delta ∈ CongruenceSubgroup.Gamma0 N) :
    cuspWidth N (delta * r) = cuspWidth N r := by
  by_cases hN : 0 < N
  · exact cuspWidth_left_mul_of_pos N hN delta r hdelta
  · have hz : N = 0 := by omega
    subst N
    simp [cuspWidth]

end
end ImbalancedChen.Part3.Gamma0CuspLeftWidthCovariance20261026b
