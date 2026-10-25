import ImbalancedChen.P5ZU1011OriginalW16FixedCellFactors
import ImbalancedChen.P5ZU1011OriginalW16SmallBetaMonomials

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

An actual active small Rosser beta factor is attached to the third factor
of the FIXED W16 box family. The box chooses rational nu/delta/xi/rho
before N and every tuple. The natural factors are fixed before kappa;
the same third-factor attachment pays all three original monomial losses
uniformly for 0<=kappa<=the box delta. Primitive residual provenance and
analytic W/AP licences remain explicit OPEN obligations.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16FixedCellSmallBeta
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16FixedCellNative U1011OriginalW16FixedCellFactors
open U1011OriginalW16SmallBetaMonomials (SmallBetaActive active_small_beta_data)
open P5U1011JointOverlap

def attachedFactors (B : Box) (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) (e : ℕ) : ℕ×ℕ×ℕ :=
  let abc := completedFactors B N t A tail
  (abc.1,abc.2.1,e*abc.2.2)

/-- The actual beta integer belongs to the same physical modulus and
costs exactly e²,e²,e^(39/16) in the three budgets. There is no beta-size,
monomial, factorization or uniform-family target premise. -/
theorem fixed_beta_attached_monomials {N enumeration e : ℕ} (hN : 1<N)
    {E : ℕ×ℕ → Prop} {t : Four} (ht : t∈U11Adaptive.source N E)
    (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (D B N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<Z B N)
    (w ell : ℝ) (hell : 0<ell) (hellsmall : ell≤(delta B:ℝ)/2)
    (he : SmallBetaActive N enumeration e w ell) :
    let abc := attachedFactors B N t A tail e
    let delta := (delta B:ℝ)
    abc.1*abc.2.1*abc.2.2=e*(fullPrefix t*tail.prod) ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0≤kappa → kappa≤delta →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-3*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-3*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*
          (abc.2.2:ℝ)^2≤(N:ℝ)^(2-2*delta) := by
  let abc := completedFactors B N t A tail
  let delta := (U1011OriginalW16FixedCellNative.delta B:ℝ)
  obtain ⟨hprod,haNat,hbNat,hcNat,haA,huniform⟩ :=
    fixed_factors_uniform_residue hN ht B hvalid hpositive htest hbox A hA hAupper tail hresidual hrough
  obtain ⟨heNat,hePower,heSupport⟩ := active_small_beta_data he
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hL : 0<Real.log (N:ℝ) := Real.log_pos hn
  have hApos : 0<A := zero_lt_one.trans_le hA
  have ha : (0:ℝ)<abc.1 := by exact_mod_cast haNat
  have hb : (0:ℝ)<abc.2.1 := by exact_mod_cast hbNat
  have hc : (0:ℝ)<abc.2.2 := by exact_mod_cast hcNat
  have hePos : (0:ℝ)<e := by exact_mod_cast heNat
  have he2 : (e:ℝ)^2≤(N:ℝ)^(2*ell) := by
    calc
      (e:ℝ)^2≤((N:ℝ)^ell)^2 := pow_le_pow_left₀ hePos.le hePower.le 2
      _ = _ := by rw [←Real.rpow_mul_natCast hn0.le]; congr 1; norm_num; ring
  have heLog := (Real.le_rpow_iff_log_le hePos hn0).1 hePower.le
  have hdQ := (rational_parameters B hvalid hpositive htest).2.2.1
  have hd : 0≤delta := by exact_mod_cast hdQ.le
  have hellL := mul_le_mul_of_nonneg_right hellsmall hL.le
  have hdL := mul_nonneg hd hL.le
  change abc.1*abc.2.1*(e*abc.2.2)=e*(fullPrefix t*tail.prod) ∧
    0<abc.1 ∧ 0<abc.2.1 ∧ 0<e*abc.2.2 ∧ (abc.1:ℝ)≤A ∧ _
  refine ⟨?_,haNat,hbNat,Nat.mul_pos heNat hcNat,haA,?_⟩
  · calc
      abc.1*abc.2.1*(e*abc.2.2)=e*(abc.1*abc.2.1*abc.2.2) := by ring
      _ = _ := by rw [hprod]
  · intro kappa hk0 hk
    obtain ⟨hfirst,hsecond,hthird⟩ := huniform kappa hk0 hk
    simp only [Nat.cast_mul]
    refine ⟨?_,?_,?_⟩
    · calc
        A^2*(abc.2.1:ℝ)*((e:ℝ)*(abc.2.2:ℝ))^2 =
            (e:ℝ)^2*(A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2) := by ring
        _ ≤ (N:ℝ)^(2*ell)*(N:ℝ)^(1-4*delta) :=
          mul_le_mul he2 hfirst (by positivity) (Real.rpow_nonneg hn0.le _)
        _ = (N:ℝ)^(1-4*delta+2*ell) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
    · calc
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*((e:ℝ)*(abc.2.2:ℝ))^2 =
            (e:ℝ)^2*((N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2) := by ring
        _ ≤ (N:ℝ)^(2*ell)*(N:ℝ)^(2-4*delta) :=
          mul_le_mul he2 hsecond (by positivity) (Real.rpow_nonneg hn0.le _)
        _ = (N:ℝ)^(2-4*delta+2*ell) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
    · have hthirdLog := (Real.le_rpow_iff_log_le (by positivity : (0:ℝ)<
          (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2) hn0).1 hthird
      rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hApos.ne',
        Real.log_rpow (div_pos (mul_pos hApos hc) hb),
        Real.log_div (mul_ne_zero hApos.ne' hc.ne') hb.ne',Real.log_mul hApos.ne' hc.ne'] at hthirdLog
      simp only [Real.log_pow] at hthirdLog
      apply Real.le_rpow_of_log_le hn0
      rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hApos.ne',
        Real.log_rpow (div_pos (mul_pos hApos (mul_pos hePos hc)) hb),
        Real.log_div (mul_ne_zero hApos.ne' (mul_ne_zero hePos.ne' hc.ne')) hb.ne',
        Real.log_mul hApos.ne' (mul_ne_zero hePos.ne' hc.ne')]
      simp only [Real.log_pow,Real.log_mul hePos.ne' hc.ne']
      nlinarith only [hthirdLog,heLog,hellL,hdL]

end
end ImbalancedChen.P5Z.U1011OriginalW16FixedCellSmallBeta

