import ImbalancedChen.Part3ActualNativePrincipalVarianceBinding
import ImbalancedChen.Part3OriginalS1OuterScalePayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the original outside coefficient L2 and both genuine owner-key
multiplicities on the actual primitive principal P. The beta moment is
the original ordinary divisor-square mean, not an added one-bound.
All constants and thresholds precede the varying atom and receiver.
-/

namespace ImbalancedChen.Part3.ActualOuterPrincipalScalePayment20261028

noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumNativePrincipalSource20261028 OriginalSamePsiS1OwnedAtlas
open ActualMediumVarianceAtomBindingSourceOnly ActualNativePrincipalVarianceBinding20261028
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028
open OriginalS1KeyMultiplicityPayment

/-- The same outside Cauchy energy and the same twice-counted original
key bank as the signed retained-source inequality. -/
def actualOuterPrincipalBudget (atom : MediumAtom) (z : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      nativeP atom (strictReceiverCutoff z) (originalSmoothTrim atom) k

/-- The source expression before inserting the centered Gram bound. -/
def actualOuterCenteredBudget (atom : MediumAtom) (z : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      |(nativeRestoredZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
        (nativeMT atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re|

/-- The source identity is used before the numerical estimate and is
proved independently of auxiliary SW / BDH. -/
theorem actualOuterCenteredBudget_eq_principal
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) :
    actualOuterCenteredBudget atom z = actualOuterPrincipalBudget atom z := by
  unfold actualOuterCenteredBudget actualOuterPrincipalBudget
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [originalRestoredZero_sub_MT_abs_eq_P hA]

/-- Both appearances of the actual owner-bank cardinality have the
proved fixed logarithmic cost. -/
theorem originalNumericKeys_card_sq_le_scale_log
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (hsigma : 0 ≤ sigma)
    (z : ℝ) (hlog : 1 ≤ Real.log atom.scale) :
    (((originalNumericKeys atom z).card : ℝ))^2 ≤
      (2*keyLogConstant)^12*(Real.log atom.scale)^12 := by
  have hc := actual_keyBank_card_le_log atom (strictReceiverCutoff z)
    (originalSmoothTrim atom) hA hsigma
  have ht : 0 ≤ Real.log atom.scale := by linarith
  have hbase : 1+Real.log atom.scale ≤ 2*Real.log atom.scale := by linarith
  have hC := keyLogConstant_pos
  have hcard : ((originalNumericKeys atom z).card : ℝ) ≤
      (2*keyLogConstant)^6*(Real.log atom.scale)^6 := by
    refine hc.trans ?_
    have h := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log atom.scale) hbase 6)
      (pow_nonneg hC.le 6)
    convert h using 1 <;> ring
  calc
    _ ≤ ((2*keyLogConstant)^6*(Real.log atom.scale)^6)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    _ = _ := by ring

/-- The actual variance contribution after the COMPLETE outside
Cauchy is O_A(x^2/log(x)^A). The exponent requested from (15) is
increased by precisely the fixed beta moment and two key costs.
No source zero-mode comparison or whole-variance bound is a premise. -/
theorem uniformAuxiliarySW_actual_outer_principal_scale
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ,
        actualOuterPrincipalBudget (F i) z ≤
          C*(F i).scale^2/(Real.log (F i).scale)^A := by
  let p : ℕ := betaMomentOrder B
  let e : ℕ := p+12
  let D : ℝ := A+(e : ℝ)
  have hD : 0 < D := by dsimp only [D]; positivity
  obtain ⟨C,hC,x1,hx1,hP⟩ :=
    uniformAuxiliarySW_nativeP F B C0 sigma kappa c0 hadmissible hSW hsigma D hD
  let Cout := 12*C*betaLogConstant^p*(2*keyLogConstant)^12
  have hCout : 0 < Cout := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp only [Cout]
    positivity
  refine ⟨Cout,hCout,max x1 (Real.exp 1),hx1.trans_le (le_max_left _ _),?_⟩
  intro i hx z
  have hx1' : x1 ≤ (F i).scale := (le_max_left _ _).trans hx
  have hexp : Real.exp 1 ≤ (F i).scale := (le_max_right _ _).trans hx
  have hlog : 1 ≤ Real.log (F i).scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  let t := Real.log (F i).scale
  let K := originalNumericKeys (F i) z
  have ht : 0 < t := by dsimp only [t]; linarith
  have hV : 0 ≤ (F i).V := zero_le_one.trans (hadmissible i).2.1
  have hQ : 0 < (F i).Q1 := lt_of_lt_of_le zero_lt_one (hadmissible i).2.2.1
  have hbeta0 := betaL2_nonneg (F i)
  have hkeyC := keyLogConstant_pos
  have hbeta := actual_betaL2_le_scale_log (F i) (hadmissible i) hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log (hadmissible i) hsigma.le z hlog
  let E := 6*C*betaL2 (F i)*(F i).V*(F i).U^2/t^D
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg (by positivity)
      (Real.rpow_nonneg ht.le D)
  have hterm : ∀ k ∈ K,
      outerL2 (F i) k * nativeP (F i) (strictReceiverCutoff z)
        (originalSmoothTrim (F i)) k ≤ E := by
    intro k hk
    have hY : 0 < keyY (F i) k := by
      dsimp only [keyY,keyD]
      positivity
    have hP0 := nativeP_nonneg (F i) (strictReceiverCutoff z)
      (originalSmoothTrim (F i)) k hQ hV
    calc
      _ ≤ (6*keyY (F i) k*betaL2 (F i))*
          (C*(F i).V*(F i).U^2/(keyY (F i) k*t^D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 (F i) k (hadmissible i))
          (hP i hx1' z k hk) hP0 (by positivity)
      _ = E := by
        dsimp only [E]
        field_simp [hY.ne',(Real.rpow_pos_of_pos ht D).ne']
        <;> ring
  calc
    actualOuterPrincipalBudget (F i) z ≤ (K.card : ℝ)^2*E := by
      unfold actualOuterPrincipalBudget
      change (K.card : ℝ)*(∑ k ∈ K, _) ≤ _
      calc
        _ ≤ (K.card : ℝ)*(∑ _k ∈ K, E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
        _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ ((2*keyLogConstant)^12*t^12)*
        (6*C*(2*(F i).V*betaLogConstant^p*t^p)*(F i).V*(F i).U^2/t^D) := by
      have hEupper : E ≤
          6*C*(2*(F i).V*betaLogConstant^p*t^p)*(F i).V*(F i).U^2/t^D := by
        dsimp only [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have h := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 6*C*(F i).V*(F i).U^2 by positivity)
        convert h using 1 <;> ring
      exact mul_le_mul hcard hEupper hE (by positivity)
    _ = Cout*(F i).scale^2/t^A := by
      dsimp only [Cout,D,e]
      rw [Real.rpow_add ht A ((p+12 : ℕ) : ℝ),Real.rpow_natCast,pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne',(Real.rpow_pos_of_pos ht A).ne',pow_ne_zero p ht.ne']
      <;> ring

/-- This is the identical scale bound on the independent centered
source expression. The source identity is proved, never assumed. -/
theorem uniformAuxiliarySW_actual_outer_centered_scale
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ,
        actualOuterCenteredBudget (F i) z ≤
          C*(F i).scale^2/(Real.log (F i).scale)^A := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_actual_outer_principal_scale F B C0 sigma kappa c0
      hadmissible hSW hsigma A hA
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx z
  rw [actualOuterCenteredBudget_eq_principal (hadmissible i)]
  exact hbound i hx z

end
end ImbalancedChen.Part3.ActualOuterPrincipalScalePayment20261028
