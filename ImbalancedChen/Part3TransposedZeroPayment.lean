import ImbalancedChen.Part3TransposedZeroCovariance
import ImbalancedChen.Part3TransposedPrimitiveUPayment

/-!
# Actual logarithmic payment of the transposed zero covariance

The owned covariance theorem permits every positive SW exponent. Both
actual fixed logarithm costs are bounded by a fixed constant times a power
of log X. Choosing the SW exponent before the family member absorbs those
costs, and two further logarithms absorb the fixed coefficient and the
absolute value of the local Fourier-zero mass.

There is no power saving available in the raw zero estimate before SW is
used. This proof therefore spends additional SW logarithms, rather than an
unavailable spare power of X. All constants and thresholds precede every
family member; the original B, C0, alpha, beta, gamma labels and scales are
retained. No remaining error budget or mass normalization is assumed.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Filter Topology
open scoped BigOperators
open TransposedZeroCovariance TransposedPrimitiveUPayment

namespace TransposedZeroPayment

/-- Fixed logarithm costs on the actual original lengths and physical cap.
The logarithmic lower gate is supplied by the final uniform threshold. -/
theorem actual_log_cost_le_log_pow (p s : ℕ)
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d)
    (hlog : 1 ≤ Real.log d.scale) :
    (1 + Real.log (2 * d.V)) ^ p *
      (1 + Real.log d.physicalFactorCap) ^ s ≤
        (2 + Real.log 8) ^ (p + s) * Real.log d.scale ^ (p + s) := by
  let D : ℝ := 2 + Real.log 8
  have hD : 0 < D := by
    dsimp [D]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  have hx0 : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hbase (y : ℝ) (hy : 0 < y) (hyX : y ≤ 8 * d.scale) :
      1 + Real.log y ≤ D * Real.log d.scale := by
    have hh := Real.log_le_log hy hyX
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hx0.ne'] at hh
    have hprod : 0 ≤ (1 + Real.log 8) * (Real.log d.scale - 1) :=
      mul_nonneg
        (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)])
        (sub_nonneg.mpr hlog)
    dsimp [D]
    nlinarith
  have hlogV : 1 + Real.log (2 * d.V) ≤ D * Real.log d.scale := by
    apply hbase _ (by linarith [hd.2.1])
    calc
      2 * d.V ≤ 2 * d.scale := mul_le_mul_of_nonneg_left (V_le_scale hd) (by norm_num)
      _ ≤ _ := by nlinarith [hx0]
  have hlogCap : 1 + Real.log d.physicalFactorCap ≤ D * Real.log d.scale :=
    hbase _ (zero_lt_one.trans_le (d.one_le_physicalFactorCap hd))
      (physicalFactorCap_le_eight_scale hsigma hd)
  have hV0 : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hcap0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  calc
    _ ≤ (D * Real.log d.scale) ^ p * (D * Real.log d.scale) ^ s :=
      mul_le_mul (pow_le_pow_left₀ hV0 hlogV p) (pow_le_pow_left₀ hcap0 hlogCap s)
        (pow_nonneg hcap0 s) (by positivity)
    _ = _ := by rw [← pow_add, mul_pow]

/-- The actual beta moment times the complete raw-zero discrepancy is paid
at every requested logarithmic order, uniformly before the family member. -/
theorem actual_betaL2_mul_rawZero_log_payment {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (sigma kappa c0 A : ℝ) (hA : 0 < A) (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
        ‖(F i).transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain (F i)‖ ≤
          (F i).scale ^ 2 / Real.log (F i).scale ^ A := by
  let p : ℕ := (2 ^ B) ^ 2 - 1
  let s : ℕ := 2 * (3 * (2 ^ C0 + 1)) ^ 2 + 1
  let n : ℕ := p + s
  let R : ℝ := A + (n : ℝ) + 2
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨C, hC, xSW, hxSW, hbound⟩ :=
    actual_betaL2_mul_rawZero_SW_bound F B C0 sigma kappa c0 R hR hadmissible hSW
  let D : ℝ := 2 + Real.log 8
  have hD : 0 < D := by
    dsimp [D]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  let K : ℝ := C * |CommonSmoothCutoff.cutoffMass| * D ^ n
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨xLog, hxLog⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (max 1 K))
  refine ⟨max xSW xLog, lt_of_lt_of_le hxSW (le_max_left _ _), fun i hx ↦ ?_⟩
  let x : ℝ := (F i).scale
  let L : ℝ := Real.log x
  have hL : max 1 K ≤ L := hxLog (F i).scale ((le_max_right _ _).trans hx)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hKsq : K ≤ L ^ 2 := by
    have hKL : K ≤ L := (le_max_right _ _).trans hL
    have hLsq : L ≤ L ^ 2 := by nlinarith
    exact hKL.trans hLsq
  have hcost :
      (1 + Real.log (2 * (F i).V)) ^ p *
        (1 + Real.log (F i).physicalFactorCap) ^ s ≤ D ^ n * L ^ n := by
    exact actual_log_cost_le_log_pow p s hsigma (hadmissible i) hL1
  have hpay :
      C * |CommonSmoothCutoff.cutoffMass| * x ^ 2 *
          (1 + Real.log (2 * (F i).V)) ^ p *
            (1 + Real.log (F i).physicalFactorCap) ^ s / L ^ R ≤ x ^ 2 / L ^ A := by
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos R)
      (Real.rpow_pos_of_pos hLpos A)).mpr
    calc
      _ = C * |CommonSmoothCutoff.cutoffMass| * x ^ 2 *
          ((1 + Real.log (2 * (F i).V)) ^ p *
            (1 + Real.log (F i).physicalFactorCap) ^ s) * L ^ A := by ring
      _ ≤ C * |CommonSmoothCutoff.cutoffMass| * x ^ 2 * (D ^ n * L ^ n) * L ^ A :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcost (by positivity))
          (Real.rpow_nonneg hLpos.le A)
      _ = K * x ^ 2 * (L ^ n * L ^ A) := by dsimp [K]; ring
      _ ≤ L ^ 2 * x ^ 2 * (L ^ n * L ^ A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKsq (sq_nonneg x)) (by positivity)
      _ = x ^ 2 * L ^ R := by
        dsimp [R]
        simp only [Real.rpow_add hLpos, Real.rpow_natCast, Real.rpow_two]
        ring
  exact (hbound i ((le_max_left _ _).trans hx)).trans hpay

end TransposedZeroPayment

end

end ImbalancedChen.Part3
