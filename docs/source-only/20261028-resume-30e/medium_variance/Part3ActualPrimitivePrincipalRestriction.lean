import ImbalancedChen.Part3ActualPrincipalRoughMean
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual primitive q gate is retained independently of the full positive
q-envelope. PSD positivity proves the subset upper bound; no equality
between a primitive-filtered S3 principal term and the unfiltered envelope
is asserted or supplied as a premise.
-/

namespace ImbalancedChen.Part3.ActualPrimitivePrincipalRestrictionSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open MediumActualPsiPreliminaryDispersion20261028 OriginalMediumPrincipalFiniteCRT
open ActualPrincipalGramVarianceBoundSourceOnly ActualMediumVarianceAtomBindingSourceOnly
open ActualLambdaPrincipalDivisorBindingSourceOnly ActualPrincipalRoughMeanSourceOnly
open OriginalGevreyFinalPsi20261028 OriginalPaperPsiCoprimeCount

/-- Primitive q is an original arithmetic support gate, defined before
Gram estimates and retained in the actual principal formula. -/
def primitiveQD (atom : MediumAtom) (k : Key) : Finset (ℕ × ℕ) :=
  (actualQD atom k).filter (fun p => p.1.Coprime atom.residue.natAbs)

def primitivePrincipalCore (atom : MediumAtom) (z : ℝ) (k : Key) : ℝ :=
  ∑ p ∈ primitiveQD atom k, paperQWeight atom p.1*((p.1*p.2).totient : ℝ)*
    paperPrincipalVariance atom.alphaCarrier atom.alpha (p.1*p.2)
      (dyadicWindow k.w) (originalLambda atom z k p.2)

/-- The exact original Gram kernel is positive on each actual q,d fibre. -/
theorem principalTerm_nonneg {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key)
    {p : ℕ × ℕ} (hp : p ∈ actualQD atom k) :
    0 ≤ paperQWeight atom p.1*((p.1*p.2).totient : ℝ)*
      paperPrincipalVariance atom.alphaCarrier atom.alpha (p.1*p.2)
        (dyadicWindow k.w) (originalLambda atom z k p.2) := by
  let ell := p.1*p.2
  let R := dyadicWindow k.w
  have he : 0 < ell := (actualQD_geometry hA k hp).2.2.1
  have hR : ∀ r ∈ R, 0 < r := fun r hr => (rough_window_bounds k hr).1
  have hL : 0 < actualCommonPeriod ell R :=
    Nat.mul_pos he (Finset.prod_pos (fun r hr => hR r hr))
  have hcommon : ∀ r ∈ R, ell*r ∣ actualCommonPeriod ell R := by
    intro r hr
    obtain ⟨s,hs⟩ := Finset.dvd_prod_of_mem (fun r : ℕ => r) hr
    refine ⟨s,?_⟩
    unfold actualCommonPeriod
    rw [hs]
    ring
  have hP := paper_principal_variance_nonneg atom.alphaCarrier atom.alpha hL he R hR hcommon
    (originalLambda atom z k p.2)
  exact mul_nonneg (mul_nonneg (paperPsi_nonneg _) (Nat.cast_nonneg _)) hP

/-- Dropping the primitive q gate is a proved positive upper envelope,
not an identification of distinct source carriers. -/
theorem primitivePrincipalCore_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key) :
    primitivePrincipalCore atom z k ≤ principalCore atom z k := by
  unfold primitivePrincipalCore primitiveQD principalCore
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p hp _ => principalTerm_nonneg hA z k hp)

/-- The primitive-filtered literal P that the actual S3 zero-mode
centering binder must identify. -/
def primitivePrincipalRemainder (atom : MediumAtom) (z : ℝ) (k : Key) : ℝ :=
  atom.V*paperMass*primitivePrincipalCore atom z k

/-- Manuscript (15) with the actual (q,a)=1 source gate kept. The existing
unfiltered positive return is consumed only via the proved subset bound. -/
theorem uniformAuxiliarySW_primitive_principalRemainder
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, ∀ k ∈ originalNumericKeys (F i) z,
        primitivePrincipalRemainder (F i) z k ≤
          C*(F i).V*(F i).U^2/(keyY (F i) k*(Real.log (F i).scale)^A) := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_actual_principalRemainder F B C0 sigma kappa c0 hadmissible hSW
      hsigma A hA
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx z k hk
  have hV : 0 ≤ (F i).V := zero_le_one.trans (hadmissible i).2.1
  have hsubset : primitivePrincipalRemainder (F i) z k ≤ actualPrincipalRemainder (F i) z k :=
    mul_le_mul_of_nonneg_left (primitivePrincipalCore_le (hadmissible i) z k)
      (mul_nonneg hV paperMass_nonneg)
  exact hsubset.trans (hbound i hx z k hk)

end
end ImbalancedChen.Part3.ActualPrimitivePrincipalRestrictionSourceOnly
