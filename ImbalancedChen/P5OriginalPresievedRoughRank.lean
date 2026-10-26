import ImbalancedChen.P5OriginalPresievedActiveDeltaFactors
import ImbalancedChen.P4ASpliceDifferenceLowerModulus
import ImbalancedChen.ActualRoughVectorEndpointBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual NEW ordinary presieved coefficient's rough residual has a rank
bound fixed by nu0,betaEta BEFORE N and the original tuple. The support
bound is proved through the actual ORIGINAL near-cap native mark and its
153/256 full-modulus cap, not through a postulated rough-vector envelope.
-/
namespace ImbalancedChen.P5Z.OriginalPresievedRoughRank
noncomputable section
open Classical
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalOrdinaryResidualArithmeticFactor OriginalPresievedActiveDeltaFactors
open U1011OriginalSixteenArithmeticProducts

def roughExponent (nu0 betaEta : ℝ) : ℝ := nu0 * betaEta ^ 2

def rankBound (nu0 betaEta : ℝ) : ℕ := actualRoughVectorRankBound (roughExponent nu0 betaEta)

/-- Every retained rough d is active in the genuine native row. Its
integer product is therefore below the ORIGINAL physical cap. -/
theorem actual_rough_modulus_bound {n N d : ℕ} {eta : ℚ} {E : ℕ × ℕ → Prop}
    (hN : 1 < N) (heta : 0 < eta) {t : Four} (ht : t ∈ tuples n N E)
    {w : ℝ} (hw : w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hd : d ∈ fixedRoughSupport
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) :
    (d : ℝ) < (N : ℝ) ^ (153 / 256 : ℝ) := by
  have hto := (Finset.mem_filter.mp ht).1
  have hj := (Finset.mem_filter.mp hto).1
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta hto
  have hdNative := ordinary_rough_supported_native_active hlegal.2.1 hw hd
  have hdSupport := (actualSmallRosserPlus_active hdNative).1
  have hm : (⟨t, d⟩ : U1011OriginalSixteenJointNearCapModulusConvolution.Mark) ∈
      U1011OriginalSixteenJointNearCapModulusConvolution.marks n N eta E := by
    apply Finset.mem_sigma.mpr
    exact ⟨hto, Finset.mem_filter.mpr ⟨hdSupport, hdNative⟩⟩
  have hcap := U1011OriginalSixteenJointNearCapModulusConvolution.mark_modulus_cap hN heta hm
  have hpref : 0 < fullPrefix t := by
    rw [fullPrefix_eq_multiplier]
    exact P5U1011JointOverlap.joint_multiplier_pos hj
  have hnat : d ≤ fullPrefix t * d := by nlinarith
  have hreal : (d : ℝ) ≤ ((fullPrefix t * d : ℕ) : ℝ) := by exact_mod_cast hnat
  exact hreal.trans_lt hcap

/-- Actual original residual rank at w=N^(nu0*betaEta^2). Nil/d=1 is
included, and no tuple-dependent rank is selected after seeing N. -/
theorem actual_rough_rank_bound {n N d : ℕ} {eta : ℚ} {E : ℕ × ℕ → Prop}
    (hN : 1 < N) (heta : 0 < eta) (nu0 betaEta : ℝ)
    (hrho : 0 < roughExponent nu0 betaEta) {t : Four} (ht : t ∈ tuples n N E)
    (hw : (N : ℝ) ^ roughExponent nu0 betaEta ≤
      U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hd : d ∈ fixedRoughSupport
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      ((N : ℝ) ^ roughExponent nu0 betaEta) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) :
    d.primeFactors.card ≤ rankBound nu0 betaEta := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans hn
  have hlo := P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    (Real.rpow_nonneg hnpos.le _) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) hd
  have hhi := actual_rough_modulus_bound hN heta ht hw hd
  have hpow : (N : ℝ) ^ (roughExponent nu0 betaEta * (d.primeFactors.card : ℝ)) ≤
      (N : ℝ) ^ (5 / 8 : ℝ) := by
    rw [Real.rpow_mul hnpos.le, Real.rpow_natCast]
    exact hlo.trans (hhi.le.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by norm_num)))
  have hcard := (Real.rpow_le_rpow_left_iff hn).mp hpow
  unfold rankBound actualRoughVectorRankBound
  apply (Nat.le_floor_iff (div_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8) hrho.le)).mpr
  apply (le_div_iff₀ hrho).mpr
  simpa only [mul_comm] using hcard

end
end ImbalancedChen.P5Z.OriginalPresievedRoughRank
