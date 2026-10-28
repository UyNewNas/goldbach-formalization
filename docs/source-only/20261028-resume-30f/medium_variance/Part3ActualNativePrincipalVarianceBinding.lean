import ImbalancedChen.Part3MediumNativePrincipalSource
import ImbalancedChen.Part3ActualPrimitivePrincipalRestriction
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The independently defined original primitive MT+P source is connected to
the already derived actual weighted Gram estimate. Only the numeric
receiver translation and the original smooth trim are specialized here.
The independent centering identity is consumed before any bound; the
unfiltered positive envelope is never identified with the source P.
-/

namespace ImbalancedChen.Part3.ActualNativePrincipalVarianceBinding20261028

noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumNativePrincipalSource20261028 OriginalSamePsiS1OwnedAtlas
open ActualMediumVarianceAtomBindingSourceOnly ActualLambdaPrincipalDivisorBindingSourceOnly
open ActualPrimitivePrincipalRestrictionSourceOnly

/-- The source product has exactly the original primitive q gate and
the same active d gate as the independently proved variance caller. -/
theorem nativeQD_eq_primitiveQD (atom : MediumAtom) (k : Key) :
    nativeQD atom k = primitiveQD atom k := by
  ext p
  simp only [nativeQD, primitiveQD, actualQD, mem_product, mem_filter]
  tauto

/-- An equality of the two independently defined literal P formulae,
not an equality with the larger unfiltered positive envelope. -/
theorem nativeP_eq_primitivePrincipalRemainder (atom : MediumAtom)
    (z : ℝ) (k : Key) :
    nativeP atom (strictReceiverCutoff z) (originalSmoothTrim atom) k =
      primitivePrincipalRemainder atom z k := by
  simp only [nativeP, primitivePrincipalRemainder, primitivePrincipalCore,
    nativeQD_eq_primitiveQD, originalLambda]

/-- The independently proved finite source centering retains P. Its
MT and P have the actual same q,d,alpha,Lambda weights. -/
theorem originalRestoredZero_re_eq_MT_add_primitiveP
    (atom : MediumAtom) (z : ℝ) (k : Key) (hQ : 0 < atom.Q1) :
    (nativeRestoredZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re =
      (nativeMT atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
        primitivePrincipalRemainder atom z k := by
  rw [← nativeP_eq_primitivePrincipalRemainder]
  exact nativeRestoredZero_re_eq_MT_add_P atom _ _ k hQ

/-- Positivity is finite exact Gram positivity, independent of SW and
the subsequent numerical estimate. -/
theorem originalRestoredZero_sub_MT_abs_eq_P
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key) :
    |(nativeRestoredZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
      (nativeMT atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re| =
      nativeP atom (strictReceiverCutoff z) (originalSmoothTrim atom) k := by
  have hQ : 0 < atom.Q1 := lt_of_lt_of_le zero_lt_one hA.2.2.1
  have hV : 0 ≤ atom.V := zero_le_one.trans hA.2.1
  rw [nativeRestoredZero_re_eq_MT_add_P atom _ _ k hQ, add_sub_cancel_left]
  exact abs_of_nonneg (nativeP_nonneg atom _ _ k hQ hV)

/-- Uniform (15), now for the independent original primitive source P.
No zero-mode comparison is a hypothesis of this theorem. The r-dependent
SW loss has already been paid by the ordinary divisor MEAN in E. -/
theorem uniformAuxiliarySW_nativeP
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, ∀ k ∈ originalNumericKeys (F i) z,
        nativeP (F i) (strictReceiverCutoff z) (originalSmoothTrim (F i)) k ≤
          C*(F i).V*(F i).U^2/(keyY (F i) k*(Real.log (F i).scale)^A) := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_primitive_principalRemainder F B C0 sigma kappa c0
      hadmissible hSW hsigma A hA
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx z k hk
  rw [nativeP_eq_primitivePrincipalRemainder]
  exact hbound i hx z k hk

/-- The MT+P comparison follows from the independent finite identity
and the derived bound. It is not an assumed source-comparison port. -/
theorem uniformAuxiliarySW_originalRestoredZero_sub_MT
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, ∀ k ∈ originalNumericKeys (F i) z,
        |(nativeRestoredZero (F i) (strictReceiverCutoff z)
            (originalSmoothTrim (F i)) k).re -
          (nativeMT (F i) (strictReceiverCutoff z) (originalSmoothTrim (F i)) k).re| ≤
          C*(F i).V*(F i).U^2/(keyY (F i) k*(Real.log (F i).scale)^A) := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_nativeP F B C0 sigma kappa c0 hadmissible hSW hsigma A hA
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx z k hk
  rw [originalRestoredZero_sub_MT_abs_eq_P (hadmissible i)]
  exact hbound i hx z k hk

end
end ImbalancedChen.Part3.ActualNativePrincipalVarianceBinding20261028
