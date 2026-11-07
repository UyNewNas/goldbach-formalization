import ImbalancedChen.P5ZU1011OriginalFifteenJointKappaMonomials
import ImbalancedChen.P5ZU1011OriginalSixteenNearCapCommonSmallParameters

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The SAME actual plus/minus small Rosser atom is attached only to group3 of
the constructed original15 JOINT factors. Its real costs are e^2,e^2 and
e^(39/16); ell<=kappa/8 pays them from the proved rough-factor reserves.
The common beta exponent is explicitly shrunk BEFORE N/tuple. No old
native-delta bound is silently treated as a kappa bound. This finite product
statement is not an assertion that an arbitrary extra beta is already a
factor of the original native coefficient. Exact small/rough coefficient
regrouping, physical AP/PP and native density/H248 licenses remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenJointSmallBeta
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenNearCapBoxProfiles (delta)
open U1011OriginalSixteenJointNearCapCompiler (rowCoefficient)
open U1011OriginalFifteenJointSelectedCompletion
open U1011OriginalFifteenJointKappaMonomials
open U1011OriginalW16SmallBetaMonomials (SmallBetaActive active_small_beta_data)

def betaRange (n : ℕ) (eta : ℚ) (kappa : ℝ) : ℝ :=
  min (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ) (kappa/8)

theorem betaRange_bounds (n : ℕ) (eta : ℚ) (heta : 0<eta) {kappa : ℝ} (hk0 : 0<kappa) :
    0<betaRange n eta kappa ∧ betaRange n eta kappa≤
      (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ) ∧
      betaRange n eta kappa≤kappa/8 := by
  have hell : (0:ℝ)<(U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ) := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.ellMax_pos n eta heta
  exact ⟨lt_min hell (by linarith),min_le_left _ _,min_le_right _ _⟩

def attachedFactors (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) (A : ℝ) (t : Four) (d e : ℕ) : ℕ×ℕ×ℕ :=
  let abc:=factors p B eta N A t d
  (abc.1,abc.2.1,e*abc.2.2)

theorem actual_beta_attached_monomials {N d enumeration e : ℕ} (hN : 1<N)
    {E : ℕ×ℕ→Prop} {t : Four} (ht : t∈jointSelector N E)
    (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B eta N d≠0)
    {kappa A : ℝ} (hk0 : 0<kappa) (hk : kappa≤(delta p B eta:ℝ)/64)
    (hAlower : (N:ℝ)^kappa≤A) (hAupper : A≤(N:ℝ)^(1/3-kappa/2))
    (w ell : ℝ) (hellsmall : ell≤kappa/8) (he : SmallBetaActive N enumeration e w ell) :
    let abc:=attachedFactors p B eta N A t d e
    abc.1*abc.2.1*abc.2.2=e*(fullPrefix t*d) ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-kappa) ∧
      (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-kappa) ∧
      (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-kappa/2) := by
  let abc:=factors p B eta N A t d
  obtain ⟨hprod,haA,hfirst,hsecond,hthird⟩:=
    actual_completed_kappa_monomials hN ht p hp B eta heta hv hw hc hb hd hk0 hk hAlower hAupper
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hL : 0<Real.log (N:ℝ) := Real.log_pos hn
  have hA : 1≤A := (Real.one_le_rpow hn.le hk0.le).trans hAlower
  have hApos : 0<A := zero_lt_one.trans_le hA
  have hAup0 : A≤(N:ℝ)^(1/3:ℝ) := hAupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
  obtain ⟨haNat,hbNat,hcNat⟩:=completed_factors_positive hN ht p hp B eta heta hv hw hc hb hd A hA hAup0
  have ha : (0:ℝ)<abc.1 := by exact_mod_cast haNat
  have hb' : (0:ℝ)<abc.2.1 := by exact_mod_cast hbNat
  have hc' : (0:ℝ)<abc.2.2 := by exact_mod_cast hcNat
  obtain ⟨heNat,hePower,heSupport⟩:=active_small_beta_data he
  have hePos : (0:ℝ)<e := by exact_mod_cast heNat
  have he2 : (e:ℝ)^2≤(N:ℝ)^(2*ell) := by
    calc
      _ ≤ ((N:ℝ)^ell)^2 := pow_le_pow_left₀ hePos.le hePower.le 2
      _ = _ := by rw [←Real.rpow_mul_natCast hn0.le];congr 1;norm_num;ring
  have heLog:=(Real.le_rpow_iff_log_le hePos hn0).mp hePower.le
  have hellL:=mul_le_mul_of_nonneg_right hellsmall hL.le
  have hkL:=mul_pos hk0 hL
  change abc.1*abc.2.1*(e*abc.2.2)=e*(fullPrefix t*d) ∧
    0<abc.1 ∧ 0<abc.2.1 ∧ 0<e*abc.2.2 ∧ (abc.1:ℝ)≤A ∧ _
  refine ⟨?_,haNat,hbNat,Nat.mul_pos heNat hcNat,haA,?_,?_,?_⟩
  · calc
      abc.1*abc.2.1*(e*abc.2.2)=e*(abc.1*abc.2.1*abc.2.2) := by ring
      _ = _ := by rw [hprod]
  · simp only [Nat.cast_mul]
    calc
      A^2*(abc.2.1:ℝ)*((e:ℝ)*(abc.2.2:ℝ))^2=(e:ℝ)^2*(A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2) := by ring
      _ ≤ (N:ℝ)^(2*ell)*(N:ℝ)^(1-3*kappa/2) :=
        mul_le_mul he2 hfirst (by positivity) (Real.rpow_nonneg hn0.le _)
      _ = (N:ℝ)^(2*ell+(1-3*kappa/2)) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
  · simp only [Nat.cast_mul]
    calc
      (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*((e:ℝ)*(abc.2.2:ℝ))^2=
          (e:ℝ)^2*((N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2) := by ring
      _ ≤ (N:ℝ)^(2*ell)*(N:ℝ)^(2-3*kappa/2) :=
        mul_le_mul he2 hsecond (by positivity) (Real.rpow_nonneg hn0.le _)
      _ = (N:ℝ)^(2*ell+(2-3*kappa/2)) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
  · have hthirdLog:=(Real.le_rpow_iff_log_le (by positivity : (0:ℝ)<
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2) hn0).mp hthird
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hApos.ne',
      Real.log_rpow (div_pos (mul_pos hApos hc') hb'),
      Real.log_div (mul_ne_zero hApos.ne' hc'.ne') hb'.ne',Real.log_mul hApos.ne' hc'.ne'] at hthirdLog
    simp only [Real.log_pow] at hthirdLog
    simp only [Nat.cast_mul]
    apply Real.le_rpow_of_log_le hn0
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hApos.ne',
      Real.log_rpow (div_pos (mul_pos hApos (mul_pos hePos hc')) hb'),
      Real.log_div (mul_ne_zero hApos.ne' (mul_ne_zero hePos.ne' hc'.ne')) hb'.ne',
      Real.log_mul hApos.ne' (mul_ne_zero hePos.ne' hc'.ne')]
    simp only [Real.log_pow,Real.log_mul hePos.ne' hc'.ne']
    nlinarith only [hthirdLog,heLog,hellL,hkL]

end
end ImbalancedChen.P5Z.U1011OriginalFifteenJointSmallBeta
