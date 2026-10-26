import ImbalancedChen.Part3OriginalSharedPAllPowers

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 6.

For each fixed delta>0 choose k=ceil(4/delta) BEFORE x or coefficients.
The actual original range is only
  32*Q1*Q2^2*Q3^2 <= V*x^(-delta), x=UV.
The proved kth Schwartz power pays the explicit x^4 coefficient/outside
budget; the original beta moment logarithm costs at most x eventually.
Actual zero covariance and primitive U/V payment then give the linear
signed-error conclusion. Long moduli outside this range are NOT paid:
their full 7/32 return still requires a genuine spectral supplier.
-/

namespace ImbalancedChen.Part3.OriginalSharedShortLcmFamily20261026b
noncomputable section
open Classical Finset Filter TransposedPrimitiveUPayment
open OriginalSharedResidualBoundary20261026b OriginalSharedWeightedBoundary20261026b
open OriginalSharedPAllPowers20261026b
open scoped BigOperators Topology

theorem actual_original_shortLcm_weighted_log_payment
    (B : ℕ) (sigma kappa c0 A delta : ℝ) (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      sharedPhysicalLcmCap d ≤ d.V*d.scale^(-delta) →
        originalOutside d * ‖sharedResidual d‖ ≤ d.scale^2/(Real.log d.scale)^A := by
  let k : ℕ := Nat.ceil (4/delta)
  have hk : 4 ≤ delta*(k : ℝ) := by
    have hh : 4/delta ≤ (k : ℝ) := Nat.le_ceil _
    have he := (div_le_iff₀ hdelta).mp hh
    nlinarith
  obtain ⟨C,hC,hbound⟩ := original_shared_weighted_allpowers_scale k
  obtain ⟨xL,hxL,hlogs⟩ := eventually_actual_log_cost_le_rpow
    ((2^B)^2-1) 0 sigma hsigma (by norm_num : (0 : ℝ) < 1)
  obtain ⟨xP,hpay⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le (delta := 1) (by norm_num))
  refine ⟨max xL xP,hxL.trans_le (le_max_left _ _),fun d hd hx hrange => ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hx1 : 1 ≤ d.scale := one_le_scale hd
  have hxpos : 0 < d.scale := zero_lt_one.trans_le hx1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hQ2 : 0 < d.Q2 := zero_lt_one.trans_le hd.2.2.2.1
  have hQ3 : 0 < d.Q3 := zero_lt_one.trans_le hd.2.2.2.2.1
  have hratio0 : 0 ≤ sharedPhysicalLcmCap d/d.V := by unfold sharedPhysicalLcmCap; positivity
  have hratio : sharedPhysicalLcmCap d/d.V ≤ d.scale^(-delta) :=
    (div_le_iff₀ hV).mpr (by simpa only [mul_comm] using hrange)
  have hratioPow : (sharedPhysicalLcmCap d/d.V)^k ≤ d.scale^(-4 : ℝ) := by
    calc
      _ ≤ (d.scale^(-delta))^k := pow_le_pow_left₀ hratio0 hratio k
      _ = d.scale^((-delta)*(k : ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hxpos.le]
      _ ≤ d.scale^(-4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [hk])
  have hlog : originalBetaLogCost B d ≤ d.scale := by
    simpa only [pow_zero,mul_one,Real.rpow_one,originalBetaLogCost] using
      hlogs B kappa c0 d hd ((le_max_left xL xP).trans hx)
  have hscale : d.scale^4*d.scale*d.scale^(-4 : ℝ) = d.scale := by
    calc
      _ = d.scale^(4 : ℝ)*d.scale^(1 : ℝ)*d.scale^(-4 : ℝ) := by
        rw [Real.rpow_natCast,Real.rpow_one]
      _ = d.scale^((4 : ℝ)+1+(-4)) := by
        rw [← Real.rpow_add hxpos,← Real.rpow_add hxpos]
      _ = d.scale := by norm_num
  have hpower : originalOutside d * ‖sharedResidual d‖ ≤ C*d.scale := by
    calc
      _ ≤ C*d.scale^4*originalBetaLogCost B d*(sharedPhysicalLcmCap d/d.V)^k :=
        hbound B sigma kappa c0 d hsigma hd
      _ ≤ C*d.scale^4*d.scale*d.scale^(-4 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlog (by positivity)) hratioPow
          (pow_nonneg hratio0 k) (by positivity)
      _ = C*(d.scale^4*d.scale*d.scale^(-4 : ℝ)) := by ring
      _ = C*d.scale := by rw [hscale]
  have hpay' := hpay d.scale ((le_max_right xL xP).trans hx)
  exact hpower.trans (by simpa only [show (2 : ℝ)-1 = 1 by norm_num,Real.rpow_one] using hpay')

theorem uniformAuxiliarySW_original_shortLcm_signedError_sq
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 delta : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1/100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma/100)
    (hdelta : 0 < delta)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale →
        sharedPhysicalLcmCap (F i) ≤ (F i).V*(F i).scale^(-delta) →
        ‖(F i).signedError‖^2 ≤ C*(F i).scale^2/(Real.log (F i).scale)^A := by
  intro A hA
  obtain ⟨CE,hCE,xE,hxE,henergy⟩ :=
    uniformAuxiliarySW_sharedFirstFactor_signedError_sq_le_nonzero_add_log_payment
      F B C0 sigma kappa c0 hsigma hsigma_small hc0 hkappa hkappa_small hadmissible hSW A hA
  obtain ⟨xN,hxN,hnonzero⟩ := actual_original_shortLcm_weighted_log_payment
    B sigma kappa c0 A delta hsigma hdelta
  refine ⟨CE+1,by linarith,max xE xN,hxE.trans_le (le_max_left _ _),?_⟩
  intro i hx hrange
  have hE := henergy i ((le_max_left xE xN).trans hx)
  have hN := hnonzero (F i) (hadmissible i) ((le_max_right xE xN).trans hx) hrange
  change ‖(F i).signedError‖^2 ≤ originalOutside (F i)*(sharedResidual (F i)).re +
    CE*(F i).scale^2/(Real.log (F i).scale)^A at hE
  have hout : 0 ≤ originalOutside (F i) := by unfold originalOutside; positivity
  calc
    _ ≤ originalOutside (F i)*(sharedResidual (F i)).re +
        CE*(F i).scale^2/(Real.log (F i).scale)^A := hE
    _ ≤ originalOutside (F i)*‖sharedResidual (F i)‖ +
        CE*(F i).scale^2/(Real.log (F i).scale)^A :=
      add_le_add (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (Complex.abs_re_le_norm _)) hout) le_rfl
    _ ≤ (F i).scale^2/(Real.log (F i).scale)^A +
        CE*(F i).scale^2/(Real.log (F i).scale)^A := add_le_add hN le_rfl
    _ = (CE+1)*(F i).scale^2/(Real.log (F i).scale)^A := by ring

theorem uniformAuxiliarySW_original_shortLcm_signedError
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 delta : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1/100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma/100)
    (hdelta : 0 < delta)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale →
        sharedPhysicalLcmCap (F i) ≤ (F i).V*(F i).scale^(-delta) →
        ‖(F i).signedError‖ ≤ C*(F i).scale/(Real.log (F i).scale)^A := by
  intro A hA
  obtain ⟨C,hC,x0,hx0,hbound⟩ := uniformAuxiliarySW_original_shortLcm_signedError_sq
    F B C0 sigma kappa c0 delta hsigma hsigma_small hc0 hkappa hkappa_small
    hdelta hadmissible hSW (2*A) (by linarith)
  refine ⟨C+1,by linarith,x0,hx0,fun i hx hrange => ?_⟩
  have hx1 : 1 < (F i).scale := hx0.trans_le hx
  have hlog : 0 < Real.log (F i).scale := Real.log_pos hx1
  have hpow : (Real.log (F i).scale)^(2*A) = ((Real.log (F i).scale)^A)^2 := by
    rw [show 2*A = A+A by ring,Real.rpow_add hlog]
    ring
  let L : ℝ := (F i).scale/(Real.log (F i).scale)^A
  have hL : 0 ≤ L := div_nonneg (zero_lt_one.trans hx1).le (Real.rpow_nonneg hlog.le _)
  have hsq : ‖(F i).signedError‖^2 ≤ C*L^2 := by
    have h := hbound i hx hrange
    simpa only [L,hpow,div_pow,mul_div_assoc] using h
  have hCpow : C ≤ (C+1)^2 := by nlinarith
  have hsq' : ‖(F i).signedError‖^2 ≤ ((C+1)*L)^2 := by
    calc
      _ ≤ C*L^2 := hsq
      _ ≤ (C+1)^2*L^2 := mul_le_mul_of_nonneg_right hCpow (sq_nonneg _)
      _ = _ := by ring
  have hlin : ‖(F i).signedError‖ ≤ (C+1)*L :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hL)).mp hsq'
  simpa only [L,mul_div_assoc] using hlin

end
end ImbalancedChen.Part3.OriginalSharedShortLcmFamily20261026b
