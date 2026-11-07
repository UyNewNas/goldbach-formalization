import ImbalancedChen.Part3ActualOuterPrincipalScalePayment
import ImbalancedChen.Part3OriginalS1NativeMain
import ImbalancedChen.Part3MediumActualS3ZeroCentering
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Consume independent S1 and physical CRT-zero identities first, then
insert the derived original principal variance estimate in the complete
outer Cauchy. Every q,d,alpha,Lambda and outside L2 weight is unchanged.
The genuine rough-clean replacement and all remaining S2/S3 source
differences are displayed; no correction is assumed small or zero.
-/

namespace ImbalancedChen.Part3.OriginalPrincipalVarianceInOuterCauchy20261028

noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumActualPreliminaryCauchy20261028 MediumLiteralS3Stages20261028
open MediumNativePrincipalSource20261028 MediumActualS3ZeroCentering20261028
open ActualMediumVarianceAtomBindingSourceOnly ActualOuterPrincipalScalePayment20261028
open OriginalS1OuterCauchy20261028 OriginalS1NativeMain20261028
open OriginalPrimitiveS1Atlas

/-- Both source identities precede this algebra. S1 contributes the
same native MT; actual CRT zero contributes MT+P+rough correction.
The three principal terms leave P, rather than canceling to zero. -/
theorem actual_principal_combination_eq_P
    {B : ℕ} {sigma kappa c0 : ℝ} (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (hA : MediumAdmissible B sigma kappa c0 atom) :
    (genuineOffDiagonalZero atom receiver y k).re -
        (roughReplacementCorrection atom receiver y k).re -
        2*(nativeMT atom receiver y k).re +
        (genuineDiagonalZero atom receiver y k).re +
        (primitiveAtlasMain atom receiver y k hA).re =
      nativeP atom receiver y k := by
  rw [primitiveAtlasMain_eq_nativeMT]
  rw [genuineOffDiagonalZero_re_eq_MT_P_corrections hA receiver y k]
  ring

/-- These are the literal original S3 and S2 differences after the
actual full-CRT zero has been separated. The rough correction remains
with its exact sign; diagonal, close-pair, single-zero and frequency
differences have not been dropped or declared negligible. -/
def actualResidualFunctional (atom : MediumAtom) (z : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      ((primitiveS3 atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
          (genuineOffDiagonalZero atom (strictReceiverCutoff z)
            (originalSmoothTrim atom) k).re +
          (roughReplacementCorrection atom (strictReceiverCutoff z)
            (originalSmoothTrim atom) k).re -
          (genuineDiagonalZero atom (strictReceiverCutoff z)
            (originalSmoothTrim atom) k).re) -
        2*(primitiveS2 atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
          (nativeMT atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re))

/-- An exact identity on the real actual preliminary source. No
asymptotic source-to-zero comparison is taken as a hypothesis. -/
theorem nativePrincipalFunctional_eq_residual_add_principal
    {B : ℕ} {sigma kappa c0 : ℝ} (atom : MediumAtom) (z : ℝ)
    (hA : MediumAdmissible B sigma kappa c0 atom) :
    nativePrincipalFunctional atom (strictReceiverCutoff z) (originalSmoothTrim atom) =
      actualResidualFunctional atom z + actualOuterPrincipalBudget atom z := by
  unfold nativePrincipalFunctional actualResidualFunctional actualOuterPrincipalBudget
  rw [← mul_add, ← sum_add_distrib]
  apply congrArg (fun v : ℝ => ((originalNumericKeys atom z).card : ℝ)*v)
  apply sum_congr rfl
  intro k hk
  rw [genuineOffDiagonalZero_re_eq_MT_P_corrections hA (strictReceiverCutoff z)
    (originalSmoothTrim atom) k]
  ring

/-- The exact weighted principal combination of original S1 and
actual physical CRT zero, with the genuine rough correction retained. -/
def actualPrincipalCombinationBudget {B : ℕ} {sigma kappa c0 : ℝ}
    (atom : MediumAtom) (z : ℝ) (hA : MediumAdmissible B sigma kappa c0 atom) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      ((genuineOffDiagonalZero atom (strictReceiverCutoff z)
          (originalSmoothTrim atom) k).re -
        (roughReplacementCorrection atom (strictReceiverCutoff z)
          (originalSmoothTrim atom) k).re -
        2*(nativeMT atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
        (genuineDiagonalZero atom (strictReceiverCutoff z)
          (originalSmoothTrim atom) k).re +
        (primitiveAtlasMain atom (strictReceiverCutoff z)
          (originalSmoothTrim atom) k hA).re)

theorem actualPrincipalCombinationBudget_eq_P
    {B : ℕ} {sigma kappa c0 : ℝ} (atom : MediumAtom) (z : ℝ)
    (hA : MediumAdmissible B sigma kappa c0 atom) :
    actualPrincipalCombinationBudget atom z hA = actualOuterPrincipalBudget atom z := by
  unfold actualPrincipalCombinationBudget actualOuterPrincipalBudget
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [actual_principal_combination_eq_P atom _ _ k hA]

/-- The requested original S1/S3 principal combination, including all
actual outside weights, is paid at the unchanged x^2 scale. -/
theorem uniformAuxiliarySW_actual_principal_combination
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ,
        actualPrincipalCombinationBudget (F i) z (hadmissible i) ≤
          C*(F i).scale^2/(Real.log (F i).scale)^A := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_actual_outer_principal_scale F B C0 sigma kappa c0
      hadmissible hSW hsigma A hA
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx z
  rw [actualPrincipalCombinationBudget_eq_P]
  exact hbound i hx z

/-- The actual retained original source with the complete S1 error
and principal P paid uniformly. Only the literal S2/S3 residual budget
remains. This is the variance/error step, not the final medium theorem. -/
theorem uniformAuxiliarySW_original_source_sq_le_residual_add_log_error
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, 0 ≤ z →
        ‖originalRetainedSource (F i) z (originalSmoothTrim (F i))‖^2 ≤
          actualResidualFunctional (F i) z +
            C*(F i).scale^2/(Real.log (F i).scale)^A := by
  obtain ⟨Cp,hCp,xp,hxp,hP⟩ :=
    uniformAuxiliarySW_actual_outer_principal_scale F B C0 sigma kappa c0
      hadmissible hSW hsigma A hA
  obtain ⟨Cs,hCs,xs,hxs,hS⟩ :=
    original_numeric_source_norm_sq_le_native_main_add_log_error B A
  refine ⟨Cp+Cs,add_pos hCp hCs,max xp xs,hxp.trans_le (le_max_left _ _),?_⟩
  intro i hx z hz
  have hpx : xp ≤ (F i).scale := (le_max_left _ _).trans hx
  have hsx : xs ≤ (F i).scale := (le_max_right _ _).trans hx
  have hsource := hS sigma kappa c0 (F i) z (originalSmoothTrim (F i))
    (hadmissible i) hz hsigma hsx
  rw [nativePrincipalFunctional_eq_residual_add_principal (F i) z
    (hadmissible i)] at hsource
  have hprincipal := hP i hpx z
  calc
    _ ≤ actualResidualFunctional (F i) z + actualOuterPrincipalBudget (F i) z +
        Cs*(F i).scale^2/(Real.log (F i).scale)^A := hsource
    _ ≤ actualResidualFunctional (F i) z +
        Cp*(F i).scale^2/(Real.log (F i).scale)^A +
        Cs*(F i).scale^2/(Real.log (F i).scale)^A :=
      add_le_add_right (add_le_add_left hprincipal _) _
    _ = actualResidualFunctional (F i) z +
        (Cp+Cs)*(F i).scale^2/(Real.log (F i).scale)^A := by ring

end
end ImbalancedChen.Part3.OriginalPrincipalVarianceInOuterCauchy20261028
