import ImbalancedChen.P5ZU1011OriginalW16ResidueUniform
import ImbalancedChen.ActualSmallRosser

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
An ACTUAL active plus/minus small Rosser coefficient supplies its positive
natural factor e and its physical bound e<N^ell. Attach exactly that e to
the SAME original W16 third natural factor. The exact physical product
and all three original buffered factor-size budgets are proved uniformly
for the same alpha=1+3*kappa interval. No target monomial or small-factor
size licence is assumed. Unique small/rough coefficient regrouping, unit
bounds, common endpoint-box assignment and the signed PP/AP estimate are
separate existing/new obligations, not consequences claimed here.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16SmallBetaMonomials
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16NativeInitialization U1011OriginalW16FactorMonomials
open U1011OriginalW16ResidueUniform
open P5U1011JointOverlap

def SmallBetaActive (N enumeration e : ℕ) (w ell : ℝ) : Prop :=
  actualSmallRosserPlus N enumeration w ((N:ℝ)^ell) e≠0 ∨
    actualSmallRosserMinus N enumeration w ((N:ℝ)^ell) e≠0

theorem active_small_beta_data {N enumeration e : ℕ} {w ell : ℝ}
    (he : SmallBetaActive N enumeration e w ell) :
    0<e ∧ (e:ℝ)<(N:ℝ)^ell ∧ SmallPrimeSupportedAt w e := by
  have hs : e ∈ actualSmallRosserSupport N enumeration w ∧
      (e:ℝ)<(N:ℝ)^ell ∧ SmallPrimeSupportedAt w e := by
    rcases he with hp | hm
    · exact actualSmallRosserPlus_active hp
    · exact actualSmallRosserMinus_active hm
  exact ⟨Nat.pos_of_mem_divisors hs.1,hs.2⟩

def attachedFactors (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) (e : ℕ) : ℕ×ℕ×ℕ :=
  let abc := completedFactors N t A tail
  (abc.1,abc.2.1,e*abc.2.2)

/-- The genuine active beta block, without changing the first two factors,
preserves the exact original modulus and pays the explicit losses e²,e²,
e^(39/16). All factors are fixed before the moving residue parameter. -/
theorem actual_W16_beta_attached_monomials {N enumeration e : ℕ} (hN : 1<N)
    {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (heW : TypedEligible wPolicy (coordinates N t))
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport ((N:ℝ)^residualExponent (coordinates N t)) tail)
    (hrough : ∀ q ∈ tail, Nat.Prime q ∧ (q:ℝ)<(N:ℝ)^cutoffExponent (coordinates N t))
    (w ell : ℝ) (hell : 0<ell) (hellsmall : ell≤buffer (coordinates N t)/2)
    (he : SmallBetaActive N enumeration e w ell) :
    let abc := attachedFactors N t A tail e
    let delta := buffer (coordinates N t)
    abc.1*abc.2.1*abc.2.2=e*(fullPrefix t*tail.prod) ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀ kappa : ℝ, 0≤kappa → kappa≤delta →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-3*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-3*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*
          (abc.2.2:ℝ)^2≤(N:ℝ)^(2-2*delta) := by
  let abc := completedFactors N t A tail
  let delta := buffer (coordinates N t)
  obtain ⟨hprod,haNat,hbNat,hcNat,haA,huniform⟩ :=
    actual_W16_factors_uniform_residue hN ht heW A hA hAupper tail hresidual hrough
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
  have hd : 0≤delta := (buffer_bounds _ heW).1.le
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
end ImbalancedChen.P5Z.U1011OriginalW16SmallBetaMonomials
