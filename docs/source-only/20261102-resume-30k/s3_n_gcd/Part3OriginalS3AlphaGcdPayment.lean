import ImbalancedChen.Part3OriginalS3AlphaGcdCount
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original roughZ of alpha pays the inverse-gcd tail, including when
the independent Lambda receiver is larger. Both original outside
key multiplicities and the actual beta square norm are retained.
-/
namespace ImbalancedChen.Part3.OriginalS3AlphaGcdPayment20261102
noncomputable section
open Classical Finset Filter
open scoped BigOperators
open OriginalS3AlphaGcdCount20261102 OriginalS3RoughPairGcdPayment20261102
open OriginalS3ClosePairPayment20261102
open MediumActualDiagonalDivisorPayment20261028 MediumActualRestorationPayment20261028
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumOriginalAllKeyRestorationPayment20261102
open OriginalSamePsiS1OwnedAtlas OriginalS1KeyMultiplicityPayment
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028
open ActualMediumVarianceAtomBindingSourceOnly ActualOuterPrincipalScalePayment20261028
open OriginalPrincipalVarianceInOuterCauchy20261028 ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2RoughZLargeXGate

theorem alphaBadDeleted_log_main_and_endpoint {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (c T : ℝ)
    (hlog : 1 ≤ Real.log atom.scale) (hz : 2 ≤ roughZ atom.scale) :
    ‖alphaBadDeleted atom z y k (shiftCutoff atom c) T‖ ≤
      48*actualVScale atom k*Real.log atom.scale^(6*c+1)/roughZ atom.scale +
        36*atom.scale*Real.log atom.scale^(6*c+1) := by
  have ht : 0 < Real.log atom.scale := zero_lt_one.trans_le hlog
  have hzpos : 0 < roughZ atom.scale := by linarith
  have hU : 0 < atom.U := zero_lt_one.trans_le hAdm.1
  have hx : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hAdm.1,hAdm.2.1]
  have hUx : atom.U ≤ atom.scale := by unfold MediumAtom.scale; nlinarith [hAdm.2.1]
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    simpa using h
  have hlogU : 1+Real.log (2*atom.U) ≤ 3*Real.log atom.scale := by
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hU.ne']
    have hu := Real.log_le_log hU hUx
    linarith
  have hpow : (shiftCutoff atom c)^6 = Real.log atom.scale^(6*c) := by
    unfold shiftCutoff
    rw [← Real.rpow_mul_natCast ht.le,
      show c*((6 : ℕ) : ℝ)=6*c by norm_num; ring]
  have hstep : Real.log atom.scale^(6*c) ≤ Real.log atom.scale^(6*c+1) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  have hY := keyY_positive hAdm k
  have hM : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hV : 0 ≤ actualVScale atom k := by unfold actualVScale; positivity
  have hsource := alphaBadDeleted_le hAdm z y k (shiftCutoff atom c) T
    (by unfold shiftCutoff; positivity) hz
  rw [hpow] at hsource
  calc
    _ ≤ (48*actualVScale atom k/roughZ atom.scale+
        12*atom.scale*(1+Real.log (2*atom.U)))*Real.log atom.scale^(6*c) := hsource
    _ ≤ (48*actualVScale atom k/roughZ atom.scale)*Real.log atom.scale^(6*c+1)+
        (12*atom.scale*(3*Real.log atom.scale))*Real.log atom.scale^(6*c) := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hstep (by positivity))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogU (by positivity))
          (Real.rpow_nonneg ht.le _))
    _ = _ := by rw [Real.rpow_add_one ht.ne']; ring

/-- A single threshold, before all atoms/keys/receivers, pays the actual
n-gcd correction. The whole endpoint is absorbed by original occupied
Y/N geometry; no correction estimate is supplied by the caller. -/
theorem exists_alphaBadDeleted_log_payment (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ z : ℝ, roughZ atom.scale ≤ z → ∀ (k : Key),
        k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) → ∀ T : ℝ,
        ‖alphaBadDeleted atom (strictReceiverCutoff z) (roughY atom.scale) k
          (shiftCutoff atom c) T‖ ≤ 84*actualVScale atom k/Real.log atom.scale^A := by
  obtain ⟨xg,hxg,hgeom⟩ := exists_original_occupied_key_geometry σ hσ hσsmall
  obtain ⟨xp,hpay⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow 1 (A+6*c+1)
      (by norm_num) (show 0 < σ/2 by positivity))
  obtain ⟨xz,hrough⟩ := eventually_atTop.mp
    (eventually_log_power_le_roughZ (max 0 (A+6*c+1)) (le_max_left _ _))
  refine ⟨max xg (max xp (max xz (Real.exp 2))),hxg.trans_le (le_max_left _ _),?_⟩
  intro B c0 atom hAdm hc0 hx z hzr k hk T
  have hxg' := (le_max_left xg _).trans hx
  have hxp' := (le_max_left xp _).trans ((le_max_right xg _).trans hx)
  have htail := (le_max_right xp _).trans ((le_max_right xg _).trans hx)
  have hxz' := (le_max_left xz _).trans htail
  have he := (le_max_right xz _).trans htail
  have hlog2 : 2 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) he
  have hlog1 : 1 ≤ Real.log atom.scale := by linarith
  have ht : 0 < Real.log atom.scale := by linarith
  have hscale : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hAdm.1,hAdm.2.1]
  have hrough' : Real.log atom.scale^(A+(6*c+1)) ≤ roughZ atom.scale :=
    (Real.rpow_le_rpow_of_exponent_le hlog1
      (by linarith [le_max_right (0:ℝ) (A+6*c+1)])).trans (hrough _ hxz')
  have hz2 : 2 ≤ roughZ atom.scale := by
    have hh : Real.log atom.scale^(1:ℝ) ≤
        Real.log atom.scale^(max 0 (A+6*c+1)+1) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith [le_max_left (0:ℝ) (A+6*c+1)])
    rw [Real.rpow_one] at hh
    exact hlog2.trans (hh.trans (hrough _ hxz'))
  have hmain : Real.log atom.scale^(6*c+1)/roughZ atom.scale ≤ 1/Real.log atom.scale^A := by
    apply (div_le_div_iff₀ (by linarith : 0 < roughZ atom.scale)
      (Real.rpow_pos_of_pos ht A)).mpr
    simpa only [Real.rpow_add ht A (6*c+1),one_mul,mul_comm] using hrough'
  have hpow : Real.log atom.scale^(A+(6*c+1)) ≤ atom.scale^(σ/2) := by
    simpa only [one_mul,show A+6*c+1=A+(6*c+1) by ring] using hpay _ hxp'
  have hV : atom.scale^(1+σ/2) ≤ actualVScale atom k :=
    diagonal_scale_ge_power hAdm (σ/2) k (hgeom B κ c0 atom hAdm hc0 hxg' _ k hk).1
  have hend : atom.scale*Real.log atom.scale^(6*c+1) ≤
      actualVScale atom k/Real.log atom.scale^A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos ht A)).mpr
    calc
      _ = atom.scale*Real.log atom.scale^(A+(6*c+1)) := by
        rw [Real.rpow_add ht A (6*c+1)]; ring
      _ ≤ atom.scale*atom.scale^(σ/2) := mul_le_mul_of_nonneg_left hpow hscale.le
      _ = atom.scale^(1+σ/2) := by
        rw [show 1+σ/2=σ/2+1 by ring,Real.rpow_add_one hscale.ne']; ring
      _ ≤ _ := hV
  have hY := keyY_positive hAdm k
  have hM : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hV0 : 0 ≤ actualVScale atom k := by unfold actualVScale; positivity
  have hm := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 48*actualVScale atom k by positivity)
  have he36 := mul_le_mul_of_nonneg_left hend (show (0:ℝ) ≤ 36 by norm_num)
  have hlocal := alphaBadDeleted_log_main_and_endpoint hAdm
    (strictReceiverCutoff z) (roughY atom.scale) k c T hlog1 hz2
  calc
    _ ≤ 48*actualVScale atom k*Real.log atom.scale^(6*c+1)/roughZ atom.scale+
        36*atom.scale*Real.log atom.scale^(6*c+1) := hlocal
    _ ≤ 84*actualVScale atom k/Real.log atom.scale^A := by
      convert add_le_add hm he36 using 1 <;> ring

def actualOuterAlphaGcdBudget (B : ℕ) (atom : MediumAtom) (z c A : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      ‖alphaBadDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))‖

/-- Actual beta-square norm and BOTH key multiplicities, with precision
D=A+betaMomentOrder(B)+12. No new outside-weight premise appears. -/
theorem exists_actualOuterAlphaGcdBudget_payment (B : ℕ) (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, roughZ atom.scale ≤ z →
          actualOuterAlphaGcdBudget B atom z c A ≤ C*atom.scale^2/Real.log atom.scale^A := by
  let p : ℕ := betaMomentOrder B
  let D : ℝ := outerPrecision B A
  obtain ⟨x1,hx1,hgcd⟩ := exists_alphaBadDeleted_log_payment σ κ c D hσ hσsmall
  let Cout : ℝ := 1008*betaLogConstant^p*(2*keyLogConstant)^12
  have hCout : 0 < Cout := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp only [Cout]; positivity
  refine ⟨Cout,hCout,max x1 (Real.exp 1),hx1.trans_le (le_max_left _ _),?_⟩
  intro c0 atom hAdm hc0 hx z hzr
  have hx1' : x1 ≤ atom.scale := (le_max_left _ _).trans hx
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans hx)
  let t := Real.log atom.scale
  let K := originalNumericKeys atom z
  have ht : 0 < t := by dsimp only [t]; linarith
  have hV : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hQ : 0 < atom.Q1 := zero_lt_one.trans_le hAdm.2.2.1
  have hbeta0 := betaL2_nonneg atom
  have hbeta := actual_betaL2_le_scale_log atom hAdm hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log hAdm hσ.le z hlog
  have hkeyC := keyLogConstant_pos
  have hbetaC := betaLogConstant_pos
  let E : ℝ := 504*betaL2 atom*atom.V*atom.U^2/t^D
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ k ∈ K, outerL2 atom k *
      ‖alphaBadDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c D)‖ ≤ E := by
    intro k hk
    have hY := keyY_positive hAdm k
    have hk' : k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) := by
      simpa only [K,originalNumericKeys,originalSmoothTrim,roughY] using hk
    have hr := hgcd B c0 atom hAdm hc0 hx1' z hzr k hk' (closeWidth atom c D)
    have hr' : ‖alphaBadDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c D)‖ ≤
        84*atom.V*atom.U^2/(keyY atom k*t^D) := by
      convert hr using 1 <;>
        simp only [originalSmoothTrim,roughY,actualVScale,t,div_eq_mul_inv,mul_inv_rev] <;> ring
    calc
      _ ≤ (6*keyY atom k*betaL2 atom)*(84*atom.V*atom.U^2/(keyY atom k*t^D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 atom k hAdm) hr' (norm_nonneg _) (by positivity)
      _ = E := by
        dsimp only [E]
        field_simp [hY.ne',(Real.rpow_pos_of_pos ht D).ne'] <;> ring
  calc
    actualOuterAlphaGcdBudget B atom z c A ≤ (K.card : ℝ)^2*E := by
      unfold actualOuterAlphaGcdBudget
      change (K.card : ℝ)*(∑ k ∈ K, _) ≤ _
      calc
        _ ≤ (K.card : ℝ)*(∑ _k ∈ K,E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
        _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ ((2*keyLogConstant)^12*t^12)*
        (504*(2*atom.V*betaLogConstant^p*t^p)*atom.V*atom.U^2/t^D) := by
      have hEupper : E ≤ 504*(2*atom.V*betaLogConstant^p*t^p)*atom.V*atom.U^2/t^D := by
        dsimp only [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have hh := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 504*atom.V*atom.U^2 by positivity)
        convert hh using 1 <;> ring
      exact mul_le_mul hcard hEupper hE (by positivity)
    _ = Cout*atom.scale^2/t^A := by
      dsimp only [Cout,D,outerPrecision]
      change _ = 1008*betaLogConstant^p*(2*keyLogConstant)^12*atom.scale^2/t^A
      rw [Real.rpow_add ht A ((p+12 : ℕ) : ℝ),Real.rpow_natCast,pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne',(Real.rpow_pos_of_pos ht A).ne',pow_ne_zero p ht.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalS3AlphaGcdPayment20261102

