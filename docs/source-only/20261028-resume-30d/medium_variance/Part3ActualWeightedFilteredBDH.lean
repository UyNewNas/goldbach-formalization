import ImbalancedChen.Part3ActualLowConductorLogChoice
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium appendix (14), actual uniform weighted filtered variance.
The power separation is a scalar support gate Q<=floor(2U)*x^(-delta).
The SW/large-sieve/orthogonality deductions are previous proved sources;
no variance, medium output or principal remainder estimate is a premise.
-/

namespace ImbalancedChen.Part3.ActualWeightedFilteredBDHSourceOnly

noncomputable section
open Classical
open scoped BigOperators
open ActualFilteredPrimitiveSWSourceOnly
open ActualLowConductorQuotientSumSourceOnly
open ActualHighConductorFixedQuotientSourceOnly
open ActualCrudeWeightedVarianceSourceOnly
open ActualHighConductorLogMarginSourceOnly
open ActualLowConductorLogChoiceSourceOnly

/-- Unweighted arbitrarily strong log saving on the actual r-filtered
alpha. The same natural conductor cutoff is used by low and high returns. -/
theorem uniformAuxiliarySW_unweighted_log_saving
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) {delta : ℝ} (hdelta : 0 < delta)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ Q r : ℕ, 1 ≤ Q → 1 ≤ r →
        (Q : ℝ) ≤ (F i).scale →
        (Q : ℝ) ≤ (Nat.floor (2*(F i).U) : ℝ)*(F i).scale^(-delta) →
          (∑ ell ∈ Finset.Icc 1 Q, filteredVariance (F i) ell r) ≤
            C*tau r^(2*C0)*(Nat.floor (2*(F i).U) : ℝ)^2 /
              (Real.log (F i).scale)^A := by
  obtain ⟨C,hC,xsw,hxsw,hlow⟩ :=
    uniformAuxiliarySW_lowEnergy_log_choice F B C0 sigma kappa c0 hadmissible hSW A hA
  obtain ⟨xm,hxm,hmargin⟩ := exists_log_margin_threshold (A+3) hdelta
  let K : ℝ := 16*(2*chen1973Lemma6Eq19SharpConstant)*(1+(Real.log 2)⁻¹)
  have hK : 0 < K := by
    dsimp only [K]
    have hc := chen1973Lemma6_eq19SharpConstant_pos
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ)<2)
    positivity
  let D : ℝ := C^2*(2 : ℝ)^(2*(2^(2*C0)))+K
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D,hD,max xsw xm,lt_of_lt_of_le hxsw (le_max_left _ _),?_⟩
  intro i hx Q r hQ hr hQX hscale
  have hxsw' : xsw ≤ (F i).scale := (le_max_left _ _).trans hx
  have hxm' : xm ≤ (F i).scale := (le_max_right _ _).trans hx
  obtain ⟨ht,hpay⟩ := hmargin _ hxm'
  have hX : 0 < (F i).scale := (zero_lt_one.trans hxm).trans_le hxm'
  let t := Real.log (F i).scale
  let N : ℝ := Nat.floor (2*(F i).U)
  let T : ℝ := tau r^(2*C0)
  let R := logCutoff t (cutoffExponent A)
  obtain ⟨hU,_,_,_,_,_,_,_,_,_,_,_,halpha,_⟩ := hadmissible i
  have hU0 : 0 ≤ (F i).U := by linarith
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hUN : (F i).U ≤ N := U_le_actual_prefix hU
  have hUNsq : (F i).U^2 ≤ N^2 := pow_le_pow_left₀ hU0 hUN 2
  have hT : 1 ≤ T := one_le_pow₀ (one_le_tau hr)
  have htpos : 0 < t := by dsimp only [t]; linarith
  have hden : 0 < t^A := Real.rpow_pos_of_pos htpos A
  have hlo := hlow i hxsw' ht Q r hQ hr hQX
  have hhi := actual_highEnergy_log_margin hU halpha hX ht
    (cutoffExponent A) Q r (cutoffExponent_ge A) hQ hQX hscale hpay
  have hlo' : lowEnergy (F i) Q R r ≤
      (C^2*(2 : ℝ)^(2*(2^(2*C0))))*T*N^2/t^A := by
    refine hlo.trans ?_
    apply div_le_div_of_nonneg_right _ hden.le
    have hconst : 0 ≤ C^2*(2 : ℝ)^(2*(2^(2*C0)))*T := by positivity
    have h := mul_le_mul_of_nonneg_left hUNsq hconst
    simpa only [T,mul_assoc,mul_comm,mul_left_comm] using h
  have hhi' : highEnergy (F i) Q R r ≤ K*T*N^2/t^A := by
    refine hhi.trans ?_
    change K*N^2/t^A ≤ K*T*N^2/t^A
    apply div_le_div_of_nonneg_right _ hden.le
    have h := mul_le_mul_of_nonneg_left hT (mul_nonneg hK.le (sq_nonneg N))
    simpa only [mul_one,mul_assoc,mul_comm,mul_left_comm] using h
  calc
    _ = lowEnergy (F i) Q R r+highEnergy (F i) Q R r :=
      (low_add_high_eq_actual_variance (F i) Q R r).symm
    _ ≤ (C^2*(2 : ℝ)^(2*(2^(2*C0))))*T*N^2/t^A+K*T*N^2/t^A :=
      add_le_add hlo' hhi'
    _ = _ := by dsimp only [D,T,N,t]; ring

/-- Actual fixed-order weighted filtered BDH statement (14). Constants
and threshold are selected before the varying atom, Q and auxiliary r.
The only analytic premise is the original UniformAuxiliarySW; the native
primitive large sieve is invoked inside the recorded high-return source. -/
theorem uniformAuxiliarySW_weighted_filtered_BDH
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) {delta : ℝ} (hdelta : 0 < delta)
    (A : ℝ) (hA : 0 < A) (w : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ Q r : ℕ, 1 ≤ Q → 1 ≤ r →
        Q ≤ Nat.floor (2*(F i).U) → (Q : ℝ) ≤ (F i).scale →
        (Q : ℝ) ≤ (Nat.floor (2*(F i).U) : ℝ)*(F i).scale^(-delta) →
          weightedVariance (F i) Q r w ≤
            C*tau r^(2*C0)*(Nat.floor (2*(F i).U) : ℝ)^2 /
              (Real.log (F i).scale)^A := by
  let E : ℕ := 2^(2*w)
  let P : ℝ := 2*A+(E : ℝ)
  have hP : 0 < P := by dsimp only [P]; positivity
  obtain ⟨C,hC,x1,hx1,hunweighted⟩ :=
    uniformAuxiliarySW_unweighted_log_saving F B C0 sigma kappa c0 hadmissible hSW
      hdelta P hP
  let D : ℝ := 2*C*(2 : ℝ)^E
  let Cout : ℝ := 1+D
  have hD : 0 < D := by dsimp only [D]; positivity
  have hCout : 0 < Cout := by dsimp only [Cout]; positivity
  refine ⟨Cout,hCout,max x1 (Real.exp 2),lt_of_lt_of_le hx1 (le_max_left _ _),?_⟩
  intro i hx Q r hQ hr hQN hQX hscale
  have hx1' : x1 ≤ (F i).scale := (le_max_left _ _).trans hx
  have hexp : Real.exp 2 ≤ (F i).scale := (le_max_right _ _).trans hx
  have hX : 0 < (F i).scale := (Real.exp_pos 2).trans_le hexp
  let t := Real.log (F i).scale
  let N : ℝ := Nat.floor (2*(F i).U)
  let T : ℝ := tau r^(2*C0)
  have ht : 2 ≤ t := by
    have h := Real.log_le_log (Real.exp_pos 2) hexp
    simpa only [Real.log_exp] using h
  have htpos : 0 < t := by linarith
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hT : 1 ≤ T := one_le_pow₀ (one_le_tau hr)
  have hT0 : 0 ≤ T := by linarith
  have hqpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : Real.log (Q : ℝ) ≤ t := Real.log_le_log hqpos hQX
  have ha : 0 ≤ 1+Real.log (Q : ℝ) := by
    have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith [Real.log_nonneg hq1]
  have hlogpow : (1+Real.log (Q : ℝ))^E ≤ (2*t)^E :=
    pow_le_pow_left₀ ha (by linarith) E
  obtain ⟨hU,_,_,_,_,_,_,_,_,_,_,_,halpha,_⟩ := hadmissible i
  have hu := hunweighted i hx1' Q r hQ hr hQX hscale
  have hw := actual_weighted_variance_interpolation hU halpha Q 1 r w hQ hQN
  rw [low_add_high_eq_actual_variance] at hw
  have hden : t^P = (t^A)^2*t^E := by
    have heq : P = (A+A)+(E : ℝ) := by dsimp only [P]; ring
    rw [heq,Real.rpow_add htpos (A+A) (E : ℝ),Real.rpow_add htpos A A,
      Real.rpow_natCast,pow_two]
  have hrough : weightedVariance (F i) Q r w ^ 2 ≤
      D*T*N^4/(t^A)^2 := by
    refine hw.trans ?_
    calc
      _ ≤ (C*T*N^2/t^P)*(2*N^2*(2*t)^E) :=
        mul_le_mul hu (mul_le_mul_of_nonneg_left hlogpow (by positivity))
          (by positivity) (by positivity)
      _ = _ := by
        rw [hden,mul_pow]
        dsimp only [D]
        field_simp [(Real.rpow_pos_of_pos htpos A).ne',pow_ne_zero E htpos.ne']
        <;> ring
  have hDsq : D ≤ Cout^2 := by dsimp only [Cout]; nlinarith [sq_nonneg D]
  have hTsq : T ≤ T^2 := by nlinarith
  have hcoef : D*T ≤ Cout^2*T^2 := mul_le_mul hDsq hTsq hT0 (sq_nonneg Cout)
  have hsq : weightedVariance (F i) Q r w ^ 2 ≤ (Cout*T*N^2/t^A)^2 := by
    refine hrough.trans ?_
    have h := mul_le_mul_of_nonneg_right hcoef
      (div_nonneg (pow_nonneg hN 4) (sq_nonneg (t^A)))
    convert h using 1 <;> ring
  have hout : 0 ≤ Cout*T*N^2/t^A :=
    div_nonneg (mul_nonneg (mul_nonneg hCout.le hT0) (sq_nonneg N))
      (Real.rpow_pos_of_pos htpos A).le
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) hout hsq

end
end ImbalancedChen.Part3.ActualWeightedFilteredBDHSourceOnly
