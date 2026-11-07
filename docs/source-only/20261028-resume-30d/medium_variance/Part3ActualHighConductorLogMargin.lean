import ImbalancedChen.Part3ActualCrudeWeightedVariance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original strict power margin pays the explicit fixed logarithms in
the actual third-batch high-conductor return. The cutoff is constructed
as a natural ceiling, not supplied as a desired energy estimate.
-/

namespace ImbalancedChen.Part3.ActualHighConductorLogMarginSourceOnly

noncomputable section
open Classical Filter
open scoped Topology BigOperators
open ActualHighConductorFixedQuotientSourceOnly
open ActualCrudeWeightedVarianceSourceOnly

def logCutoff (t : ℝ) (b : ℕ) : ℕ := Nat.ceil (t^b)

theorem logCutoff_bounds {t : ℝ} (ht : 2 ≤ t) (b : ℕ) :
    0 < logCutoff t b ∧ t^b ≤ (logCutoff t b : ℝ) ∧
      (logCutoff t b : ℝ) ≤ t^(b+1) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow : 1 ≤ t^b := one_le_pow₀ (by linarith : 1 ≤ t)
  have hlo : t^b ≤ (logCutoff t b : ℝ) := Nat.le_ceil _
  have hhi : (logCutoff t b : ℝ) ≤ t^b+1 := (Nat.ceil_lt_add_one (pow_nonneg ht0 b)).le
  have hR : (0 : ℝ) < logCutoff t b := by linarith
  refine ⟨by exact_mod_cast hR,hlo,?_⟩
  calc
    _ ≤ t^b+1 := hhi
    _ ≤ 2*t^b := by linarith
    _ ≤ t*t^b := mul_le_mul_of_nonneg_right ht (pow_nonneg ht0 b)
    _ = _ := by rw [pow_succ]; ring

/-- The explicit integer window count has a fixed logarithmic cost. -/
theorem log2_windows_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ((Nat.log2 Q+1 : ℕ) : ℝ) ≤
      (1+(Real.log 2)⁻¹)*(1+Real.log (Q : ℝ)) := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ Real.log (Q : ℝ)/Real.log 2+1 := by
      have h := Real.log2_le_logb Q
      simpa only [Nat.cast_add,Nat.cast_one,Real.logb,add_comm] using add_le_add_right h 1
    _ ≤ _ := by
      have hp : 0 ≤ (Real.log 2)⁻¹*Real.log (Q : ℝ) :=
        mul_nonneg (inv_nonneg.mpr hlog2.le) hlogQ
      have hi : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlog2.le
      rw [div_eq_mul_inv]
      nlinarith

/-- Exact scalar payment for the high-return power remainder. -/
theorem power_margin_log_payment {X t delta A : ℝ}
    (hX : 0 < X) (ht : 0 < t) (hpay : t^(A+3) ≤ X^delta) :
    t^3*X^(-delta) ≤ 1/t^A := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht A)).mpr
  calc
    _ = (t^A*t^3)*X^(-delta) := by ring
    _ = t^(A+3)*X^(-delta) := by
      rw [Real.rpow_add ht A 3,Real.rpow_natCast]
    _ ≤ X^delta*X^(-delta) :=
      mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hX.le _)
    _ = 1 := by rw [← Real.rpow_add hX,add_neg_cancel,Real.rpow_zero]

/-- The natural logarithmic cutoff has the reciprocal saving needed by
all high-conductor windows, with the cutoff exponent chosen first. -/
theorem cutoff_log_payment {t A : ℝ} (ht : 2 ≤ t) (b : ℕ)
    (hb : A+3 ≤ (b : ℝ)) :
    t^3/(logCutoff t b : ℝ) ≤ 1/t^A := by
  have htpos : 0 < t := by linarith
  obtain ⟨hR,hlo,hhi⟩ := logCutoff_bounds ht b
  have hRR : (0 : ℝ) < logCutoff t b := by exact_mod_cast hR
  have hexp : t^(A+3) ≤ t^b := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ t) hb
  apply (div_le_div_iff₀ hRR (Real.rpow_pos_of_pos htpos A)).mpr
  calc
    t^3*t^A = t^(A+3) := by
      rw [Real.rpow_add htpos A 3,Real.rpow_natCast]
      ring
    _ ≤ t^b := hexp
    _ ≤ _ := by simpa only [one_mul] using hlo

/-- Actual high-conductor logarithmic saving after the original strict
power margin. Q<=X and Q<=floor(2U)*X^(-delta) are numerical support gates,
not discrepancy or variance conclusions. -/
theorem actual_highEnergy_log_margin {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    {X A delta : ℝ} (hX : 0 < X) (ht : 2 ≤ Real.log X)
    (b Q r : ℕ) (hb : A+3 ≤ (b : ℝ)) (hQ : 1 ≤ Q)
    (hQX : (Q : ℝ) ≤ X)
    (hQscale : (Q : ℝ) ≤ (Nat.floor (2*d.U) : ℝ)*X^(-delta))
    (hpay : (Real.log X)^(A+3) ≤ X^delta) :
    highEnergy d Q (logCutoff (Real.log X) b) r ≤
      (16*(2*chen1973Lemma6Eq19SharpConstant)*(1+(Real.log 2)⁻¹)) *
        (Nat.floor (2*d.U) : ℝ)^2/(Real.log X)^A := by
  let t := Real.log X
  let N : ℝ := Nat.floor (2*d.U)
  let K : ℝ := 2*chen1973Lemma6Eq19SharpConstant
  let H : ℝ := 1+(Real.log 2)⁻¹
  let R := logCutoff t b
  have htpos : 0 < t := by dsimp only [t]; linarith
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hK : 0 < K := by dsimp only [K]; exact mul_pos (by norm_num) chen1973Lemma6_eq19SharpConstant_pos
  have hH : 0 < H := by dsimp only [H]; have hlog2 := Real.log_pos (by norm_num : (1 : ℝ)<2); positivity
  have hR : 0 < R := (logCutoff_bounds ht b).1
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : Real.log (Q : ℝ) ≤ t := Real.log_le_log hQpos hQX
  have ha : 0 ≤ 1+Real.log (Q : ℝ) := by
    have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith [Real.log_nonneg hq1]
  have hat : 1+Real.log (Q : ℝ) ≤ 2*t := by dsimp only [t] at *; linarith
  have hw : ((Nat.log2 Q+1 : ℕ) : ℝ)*(1+Real.log (Q : ℝ))^2 ≤ 8*H*t^3 := by
    calc
      _ ≤ (H*(1+Real.log (Q : ℝ)))*(1+Real.log (Q : ℝ))^2 :=
        mul_le_mul_of_nonneg_right (log2_windows_le Q hQ) (sq_nonneg _)
      _ = H*(1+Real.log (Q : ℝ))^3 := by ring
      _ ≤ H*(2*t)^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hat 3) hH.le
      _ = _ := by ring
  have hpower : t^3*X^(-delta) ≤ 1/t^A := power_margin_log_payment hX htpos hpay
  have hcut : t^3/(R : ℝ) ≤ 1/t^A := cutoff_log_payment ht b hb
  have hscale : (Q : ℝ)+N/(R : ℝ) ≤ N*(X^(-delta)+1/(R : ℝ)) := by
    dsimp only [N]
    nlinarith [hQscale]
  refine (actual_highEnergy_le_native_sieve hU halpha Q R r hQ hR).trans ?_
  change K*N*((Q : ℝ)+N/(R : ℝ))*((Nat.log2 Q+1 : ℕ) : ℝ)*
    (1+Real.log (Q : ℝ))^2 ≤ (16*K*H)*N^2/t^A
  calc
    _ = K*N*((Q : ℝ)+N/(R : ℝ))*
        (((Nat.log2 Q+1 : ℕ) : ℝ)*(1+Real.log (Q : ℝ))^2) := by ring
    _ ≤ K*N*(N*(X^(-delta)+1/(R : ℝ)))*(8*H*t^3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hscale (mul_nonneg hK.le hN)) hw
        (by positivity) (by positivity)
    _ = (8*K*H*N^2)*(t^3*X^(-delta)+t^3/(R : ℝ)) := by ring
    _ ≤ (8*K*H*N^2)*(2/t^A) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- Mathlib's logarithm-versus-power theorem chooses a common real threshold
for the original strict margin. No convergence premise on an atom is used. -/
theorem exists_log_margin_threshold (P : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ X : ℝ, x0 ≤ X →
      2 ≤ Real.log X ∧ (Real.log X)^P ≤ X^delta := by
  have hb := (isLittleO_log_rpow_rpow_atTop P hdelta).bound (by norm_num : (0 : ℝ)<1)
  have hevent : ∀ᶠ X : ℝ in atTop,
      2 ≤ Real.log X ∧ (Real.log X)^P ≤ X^delta := by
    filter_upwards [hb,eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with X hx hX hlog
    refine ⟨hlog,?_⟩
    simpa only [Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log X) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _)] using hx
  obtain ⟨x1,hx1⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 x1,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro X hX
  exact hx1 X ((le_max_right 2 x1).trans hX)

end
end ImbalancedChen.Part3.ActualHighConductorLogMarginSourceOnly
