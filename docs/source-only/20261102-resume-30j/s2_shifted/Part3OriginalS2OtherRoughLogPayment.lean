import ImbalancedChen.Part3OriginalS2RoughPrimeTail
import ImbalancedChen.Part3OriginalS2RoughZLargeXGate
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the fixed logarithmic numerator at the literal original roughZ.
The only external port is PrimitiveShiuTauBoundary 12 (1/400) (1/400).
Constants and thresholds precede all moving original medium data.
-/

namespace ImbalancedChen.Part3OriginalS2OtherRoughLogPayment

noncomputable section
open Classical Filter
open scoped BigOperators Topology
open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2ShiftedTwelve
open ImbalancedChen.Part3OriginalS2RoughPrimeTail
open ImbalancedChen.Part3OriginalS2RoughZLargeXGate
open ImbalancedChen.Part3OriginalS2OtherRoughConsumer
open ImbalancedChen.Part3OriginalS2SingleZeroPayment
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3.MediumPrimitiveShiuSigned20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuTwoSigns20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3.ActualMediumVarianceAtomBindingSourceOnly

def largeLogConstant (hShiu : S2PrimitiveShiu) : ℝ :=
  ((64 * hShiu.A * uniformEulerConstant 12 * 5) / ((1 / 5 : ℝ) * Real.log 2)) *
    (5 : ℝ) ^ (2 ^ 12 : ℕ)

def smallLogConstant : ℝ :=
  uniformTwoSmallConstant 12 (by norm_num : (0 : ℝ) < 1 / 5)
    (by norm_num : (0 : ℝ) < 3 + 1)

def logMultiplier : ℝ := 2 + Real.log 8

def roughLogConstant (hShiu : S2PrimitiveShiu) : ℝ :=
  96 * logMultiplier ^ 3 *
    (20 * logMultiplier ^ 3 + 5 * (2 : ℝ) ^ (13 : ℕ) *
      (smallLogConstant + 2 * largeLogConstant hShiu)) + 1

theorem largeLogConstant_pos (hShiu : S2PrimitiveShiu) : 0 < largeLogConstant hShiu := by
  have hA := hShiu.A_pos
  have hE := uniformEulerConstant_pos 12
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold largeLogConstant
  positivity

theorem smallLogConstant_pos : 0 < smallLogConstant :=
  uniformTwoSmallConstant_pos 12 (by norm_num) (by norm_num)

theorem logMultiplier_pos : 0 < logMultiplier := by
  unfold logMultiplier
  linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]

theorem roughLogConstant_pos (hShiu : S2PrimitiveShiu) : 0 < roughLogConstant hShiu := by
  have hS := smallLogConstant_pos
  have hT := largeLogConstant_pos hShiu
  have hD := logMultiplier_pos
  unfold roughLogConstant
  positivity

theorem largeLogFactor_eq (hShiu : S2PrimitiveShiu) (x : ℝ) :
    largeLogFactor 12 x (1 / 5) 3 hShiu.A =
      largeLogConstant hShiu * (Real.log x) ^ (2 ^ 12 : ℕ) := by
  unfold largeLogFactor largeLogConstant
  rw [show (2 : ℝ) ^ (12 : ℕ) = ((2 ^ 12 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  simp only [show (3 : ℝ) + 2 = 5 by norm_num]
  rw [mul_pow]
  ring

/-- An explicit fixed exponent, 2^12+3=4099, controls the whole actual
numerator. The moment order is independent of requested precision A. -/
theorem roughLogNumerator_le_polylog (hShiu : S2PrimitiveShiu)
    {x : ℝ} (hx : 0 < x) (hL : 1 ≤ Real.log x) :
    roughLogNumerator hShiu x ≤
      roughLogConstant hShiu * (Real.log x) ^ (2 ^ 12 + 3 : ℕ) := by
  have hD := logMultiplier_pos
  have hS := smallLogConstant_pos
  have hT := largeLogConstant_pos hShiu
  have hL0 : 0 ≤ Real.log x := by linarith
  have hbase {y : ℝ} (hy : 0 < y) (hyX : y ≤ 8 * x) :
      1 + Real.log y ≤ logMultiplier * Real.log x := by
    have hlog := Real.log_le_log hy hyX
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hx.ne'] at hlog
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    unfold logMultiplier
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) hlog8]
  have h5pos : 0 ≤ 1 + Real.log (5 * x) := by
    have hx1 : 1 ≤ x := by
      have hlogx : 0 ≤ Real.log x := by linarith
      exact (Real.log_nonneg_iff hx).mp hlogx
    linarith [Real.log_nonneg (show 1 ≤ 5 * x by linarith)]
  have h8pos : 0 ≤ 1 + Real.log (8 * x) := by
    have hlog := Real.log_le_log hx (show x ≤ 8 * x by linarith)
    linarith
  have h5 := pow_le_pow_left₀ h5pos (hbase (by positivity) (by linarith)) 3
  have h8 := pow_le_pow_left₀ h8pos (hbase (by positivity) le_rfl) 3
  rw [mul_pow] at h5 h8
  have hLE : 1 ≤ (Real.log x) ^ (2 ^ 12 : ℕ) := one_le_pow₀ hL
  have hL3E : (Real.log x) ^ (3 : ℕ) ≤ (Real.log x) ^ (2 ^ 12 : ℕ) :=
    pow_le_pow_right₀ hL (by norm_num)
  have hF : shiftedLogBudget hShiu x ≤
      (smallLogConstant + 2 * largeLogConstant hShiu) *
        (Real.log x) ^ (2 ^ 12 : ℕ) := by
    unfold shiftedLogBudget
    rw [largeLogFactor_eq]
    change smallLogConstant + 2 * (largeLogConstant hShiu * (Real.log x) ^ (2 ^ 12 : ℕ)) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hLE hS.le]
  let M : ℝ := 20 * logMultiplier ^ 3 + 5 * (2 : ℝ) ^ (13 : ℕ) *
    (smallLogConstant + 2 * largeLogConstant hShiu)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmixed : mixedLogBudget hShiu x ≤ M * (Real.log x) ^ (2 ^ 12 : ℕ) := by
    have hfirst : 20 * (1 + Real.log (5 * x)) ^ 3 ≤
        (20 * logMultiplier ^ 3) * (Real.log x) ^ (2 ^ 12 : ℕ) := by
      calc
        _ ≤ 20 * (logMultiplier ^ 3 * (Real.log x) ^ 3) :=
          mul_le_mul_of_nonneg_left h5 (by norm_num)
        _ ≤ 20 * (logMultiplier ^ 3 * (Real.log x) ^ (2 ^ 12 : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hL3E (pow_nonneg hD.le _)) (by norm_num)
        _ = _ := by ring
    have hsecond := mul_le_mul_of_nonneg_left hF
      (show 0 ≤ 5 * (2 : ℝ) ^ (13 : ℕ) by positivity)
    unfold mixedLogBudget
    dsimp [M]
    nlinarith [hfirst, hsecond]
  have hx1 : 1 ≤ x := by
    exact (Real.log_nonneg_iff hx).mp hL0
  have hmixed0 := mixedLogBudget_nonneg hShiu hx1
  calc
    _ ≤ 96 * (logMultiplier ^ 3 * (Real.log x) ^ 3) *
        (M * (Real.log x) ^ (2 ^ 12 : ℕ)) := by
      unfold roughLogNumerator
      exact mul_le_mul (mul_le_mul_of_nonneg_left h8 (by norm_num)) hmixed
        hmixed0 (by positivity)
    _ = (96 * logMultiplier ^ 3 * M) * (Real.log x) ^ (2 ^ 12 + 3 : ℕ) := by
      rw [pow_add]
      ring
    _ ≤ _ := by
      unfold roughLogConstant
      dsimp [M]
      nlinarith [pow_nonneg hL0 (2 ^ 12 + 3 : ℕ)]

theorem exists_roughLogNumerator_payment (hShiu : S2PrimitiveShiu)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ X : ℝ, Real.exp (Real.exp 1) < X ∧
      ∀ x : ℝ, X ≤ x → shiuThreshold hShiu ≤ x ∧ 2 ≤ roughZ x ∧
        roughLogNumerator hShiu x / roughZ x ≤
          roughLogConstant hShiu * (Real.log x) ^ (-A) := by
  have hrough := eventually_log_power_le_roughZ
    (A + (2 ^ 12 + 3 : ℕ)) (by positivity)
  have hrough1 := eventually_log_power_le_roughZ 0 (by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (hrough.and (hrough1.and hlog))
  let X := max X0 (max (shiuThreshold hShiu) (Real.exp (Real.exp 1) + 1))
  refine ⟨X, ?_, ?_⟩
  · dsimp [X]
    exact lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans (le_max_right _ _))
  intro x hx
  have hth : shiuThreshold hShiu ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  obtain ⟨hzbig, hz1, hL2⟩ := hX0 x ((le_max_left _ _).trans hx)
  have hz1' : Real.log x ≤ roughZ x := by
    simpa only [zero_add, Real.rpow_one] using hz1
  have hz2 : 2 ≤ roughZ x := hL2.trans hz1'
  have hxpos : 0 < x := by
    have hh := shiuThreshold_large hShiu hth
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ)) hh
  have hL1 : 1 ≤ Real.log x := by linarith
  have hLpos : 0 < Real.log x := by linarith
  have hmain := roughLogNumerator_le_polylog hShiu hxpos hL1
  have hpow : (Real.log x) ^ (A + (2 ^ 12 + 3 : ℕ)) ≤ roughZ x :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)).trans hzbig
  have hcross : (Real.log x) ^ (2 ^ 12 + 3 : ℕ) * (Real.log x) ^ A ≤ roughZ x := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
    convert hpow using 1 <;> ring
  have hratio : (Real.log x) ^ (2 ^ 12 + 3 : ℕ) / roughZ x ≤ (Real.log x) ^ (-A) := by
    rw [Real.rpow_neg hLpos.le]
    apply (div_le_iff₀ (show 0 < roughZ x by linarith)).mpr
    have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hLpos A)).mpr hcross
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  refine ⟨hth, hz2, ?_⟩
  calc
    _ ≤ (roughLogConstant hShiu * (Real.log x) ^ (2 ^ 12 + 3 : ℕ)) / roughZ x :=
      div_le_div_of_nonneg_right hmain (by linarith)
    _ = roughLogConstant hShiu * ((Real.log x) ^ (2 ^ 12 + 3 : ℕ) / roughZ x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (roughLogConstant_pos hShiu).le

/-- Original S2 otherRough payment. A and the genuine fixed Shiu input
come first; the bound is uniform before every original atom and key. -/
theorem exists_actual_S2_otherRough_arbitrary_log (hShiu : S2PrimitiveShiu)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → kappa ≤ 1 →
        k ∈ originalNumericKeys d (roughZ d.scale) → X ≤ d.scale →
        ‖otherRoughCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨X, hX, hpay⟩ := exists_roughLogNumerator_payment hShiu A hA
  refine ⟨roughLogConstant hShiu, X, roughLogConstant_pos hShiu, hX, ?_⟩
  intro B sigma kappa c0 d k hd hsigma hc0 hkappa hk hx
  obtain ⟨hth, hz, hscalar⟩ := hpay d.scale hx
  have hk' : k ∈ keyBank d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) := by
    simpa only [originalNumericKeys, originalSmoothTrim, roughY] using hk
  have hscale : 0 ≤ fixedDScale d ((2 : ℝ) ^ k.d) := by
    unfold fixedDScale
    have hU := hd.1
    have hV := hd.2.1
    have hQ := hd.2.2.1
    positivity
  calc
    _ ≤ fixedDScale d ((2 : ℝ) ^ k.d) * roughLogNumerator hShiu d.scale / roughZ d.scale :=
      actual_otherRough_le_log_over_z hShiu hd hsigma hc0 hkappa (roughZ d.scale) hz k hk' hth
    _ = fixedDScale d ((2 : ℝ) ^ k.d) *
        (roughLogNumerator hShiu d.scale / roughZ d.scale) := by ring
    _ ≤ fixedDScale d ((2 : ℝ) ^ k.d) *
        (roughLogConstant hShiu * (Real.log d.scale) ^ (-A)) :=
      mul_le_mul_of_nonneg_left hscalar hscale
    _ = _ := by ring

/-- The manuscript's exact sigma/kappa gates discharge the deliberately
weaker polynomial-location condition used above. No new kappa cap is
imposed on the original family. -/
theorem exists_actual_S2_otherRough_original_ranges (hShiu : S2PrimitiveShiu)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d →
        0 < sigma → sigma < 1 / 100 → 0 < c0 → 0 ≤ kappa → kappa ≤ sigma / 100 →
        k ∈ originalNumericKeys d (roughZ d.scale) → X ≤ d.scale →
        ‖otherRoughCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C, X, hC, hX, hpay⟩ := exists_actual_S2_otherRough_arbitrary_log hShiu A hA
  refine ⟨C, X, hC, hX, ?_⟩
  intro B sigma kappa c0 d k hd hsigma hsigmaUp hc0 hkappa0 hkappa hk hx
  exact hpay B sigma kappa c0 d k hd hsigma.le hc0 (by linarith) hk hx

/-- The actual primitive S2-MT-complete-nonzero residual now has no
otherRoughCorrection term. The complete nonzero source is unchanged. -/
theorem exists_original_S2_centered_except_nonzero
    (hShiu : S2PrimitiveShiu) (kappa A : ℝ) (hkappa : kappa ≤ 1) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 →
        k ∈ originalNumericKeys d (roughZ d.scale) → X ≤ d.scale →
        |primitiveS2 d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k -
            (nativeMT d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re -
            (actualS2NonzeroModes d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re| ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C0, X0, hC0, hX0, hpaid⟩ :=
    exists_original_S2_centered_except_rough_and_nonzero kappa A hA
  obtain ⟨C1, X1, hC1, hX1, hrough⟩ := exists_actual_S2_otherRough_arbitrary_log hShiu A hA
  refine ⟨C0 + C1, max X0 X1, by linarith, hX0.trans_le (le_max_left _ _), ?_⟩
  intro B sigma c0 d k hd hsigma hc0 hk hx
  have h0 := hpaid B sigma c0 d k hd hsigma hc0 hk ((le_max_left _ _).trans hx)
  have h1 := (Complex.abs_re_le_norm
    (otherRoughCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k)).trans
      (hrough B sigma kappa c0 d k hd hsigma hc0 hkappa hk ((le_max_right _ _).trans hx))
  have hab (a b : ℝ) : |a| ≤ |a + b| + |b| := by
    calc
      |a| = |(a + b) - b| := by ring_nf
      _ ≤ _ := abs_sub _ _
  simpa only [add_mul] using (hab _ _).trans (add_le_add h0 h1)

end
end ImbalancedChen.Part3OriginalS2OtherRoughLogPayment
