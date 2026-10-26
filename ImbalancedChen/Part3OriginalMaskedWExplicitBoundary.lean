import ImbalancedChen.Part3OriginalMaskedWCoefficientMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 3.

A complete boundary estimate for the actual ORIGINAL both-small nonzero
source, with no unnamed coefficient mass left on the RHS. The original
physical cap is 8*Q1*Q2*Q3. The power-saving subrange below is an explicit
inequality on original U,V,Q1,Q2,Q3 and x=UV, not a bound assumed for W.
It is a proper boundary subrange; full retained spectral 7/32 stays OPEN.
-/

namespace ImbalancedChen.Part3.OriginalMaskedWExplicitBoundary20261026b
noncomputable section
open Classical OriginalBothSmallMaskedW20261026b
open OriginalMaskedWShortModulusBound20261026b OriginalMaskedWCoefficientMass20261026b

theorem original_bothSmall_nonzero_explicit_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D : ℝ,
        ‖d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D false‖ ≤
          C*d.U^2*d.physicalFactorCap^4/d.V := by
  obtain ⟨C,hC,hbound⟩ := original_bothSmall_nonzero_physicalCap_bound
  refine ⟨4*C,by positivity,fun B sigma kappa c0 d hd Y D => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  calc
    _ ≤ (C*(d.physicalFactorCap^2/d.V))*retainedMass d.transposedAtom Y D :=
      hbound B sigma kappa c0 d hd Y D
    _ ≤ (C*(d.physicalFactorCap^2/d.V))*(4*d.U^2*d.physicalFactorCap^2) :=
      mul_le_mul_of_nonneg_left (actual_retainedMass_le hd Y D) (by positivity)
    _ = (4*C)*d.U^2*d.physicalFactorCap^4/d.V := by field_simp [hV.ne']; ring

theorem original_maskedW_sub_rawZero_explicit_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D : ℝ,
        ‖wholeW d.transposedAtom Y D - rawZero d.transposedAtom Y D‖ ≤
          C*d.U^2*d.physicalFactorCap^4/d.V := by
  obtain ⟨C,hC,hbound⟩ := original_bothSmall_nonzero_explicit_boundary
  refine ⟨C,hC,fun B sigma kappa c0 d hd Y D => ?_⟩
  rw [← original_nonzero_eq_maskedW_sub_rawZero hd]
  exact hbound B sigma kappa c0 d hd Y D

/-- A legal original boundary gives an actual power saving at scale U^2.
No coefficient, Fourier, Kuznetsov or W-bound premise appears. -/
theorem original_bothSmall_nonzero_boundary_power_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D delta : ℝ,
        0 < delta →
        d.physicalFactorCap^4 ≤ d.V*d.scale^(-delta) →
        ‖d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D false‖ ≤
          C*d.U^2*d.scale^(-delta) := by
  obtain ⟨C,hC,hbound⟩ := original_bothSmall_nonzero_explicit_boundary
  refine ⟨C,hC,fun B sigma kappa c0 d hd Y D delta _hdelta hrange => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hratio : d.physicalFactorCap^4/d.V ≤ d.scale^(-delta) :=
    (div_le_iff₀ hV).mpr (by simpa only [mul_comm] using hrange)
  calc
    _ ≤ C*d.U^2*d.physicalFactorCap^4/d.V := hbound B sigma kappa c0 d hd Y D
    _ = (C*d.U^2)*(d.physicalFactorCap^4/d.V) := by ring
    _ ≤ (C*d.U^2)*d.scale^(-delta) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalMaskedWExplicitBoundary20261026b
