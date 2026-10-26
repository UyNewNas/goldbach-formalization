import ImbalancedChen.P5JointNativeSignedRegroup
import ImbalancedChen.P5OriginalOrdinaryBetaRegroup
import ImbalancedChen.P5ZU1011OriginalSixteenNativeRelativeCutoff

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Original JOINT low-unmasked/high-same-E native disintegration. The common
small cutoff w is fixed before the tuple. The native coefficient still depends
on BOTH e and d through lambda+(e*d), including every original Rosser test.
This is not an independent beta-times-rough identity. It feeds the already
constructed signed +U6-JOINT physical sigma without changing its coefficient.
-/

namespace ImbalancedChen.P5JointNativeConditionalBeta
noncomputable section
open Classical
open scoped BigOperators
open P5JointNativeSignedRegroup
open P5Z.U1011OriginalSixteenArithmeticProducts
open P5Z.U1011OriginalSixteenJointNearCapCompiler
open P5Z.OriginalOrdinaryBetaRegroup (roughSupport nativeSupport_eq_products native_sum_split roughSupport_rough)

/-- One small-prime exponent can be fixed before ALL actual joint tuples.
The lower bound is produced by the actual selected native grid certificate. -/
theorem common_small_cutoff_le_Z {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) {E : ℕ × ℕ → Prop}
    {t : P5Z.U11Adaptive.Four} (ht : t ∈ ordinaryTuples n N E)
    {b : ℝ} (hb : b ≤ (417 / 5000 : ℝ) / 3) : (N : ℝ) ^ b ≤ Z n N eta t := by
  let j := P5Z.U1011OriginalFifteenNativeGridCells.owner n (coordinates N t)
  have htag := (Finset.mem_filter.mp ht).2
  have hcert := (P5Z.U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate
    (P5Z.U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) htag).2
  have hzQ := (P5Z.U1011OriginalSixteenNativeRelativeCutoff.near_grid_dictionary n j
    (P5Z.U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t) eta heta hcert).2.1
  have hzR : (417 / 5000 : ℝ) / 3 ≤
      (P5Z.U1011OriginalSixteenNativeRelativeCutoff.nearZeta
        (P5Z.U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (P5Z.U1011OriginalFifteenNativeGridCells.gridBox n j) eta : ℝ) := by
    exact_mod_cast hzQ
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Nat.le_of_lt hN)) (hb.trans hzR)

def conditionalRow (n N : ℕ) (eta : ℚ) (w : ℝ) (t : P5Z.U11Adaptive.Four)
    (F : ℕ → ℝ) : ℝ :=
  ∑ e ∈ actualSmallRosserSupport N (Nat.ceil (Z n N eta t)) w,
    ∑ d ∈ roughSupport N (Nat.ceil (Z n N eta t)) w (Z n N eta t),
      coefficient n N eta t (e * d) * F (fullPrefix t * (e * d))

theorem joint_row_conditional_test (n N : ℕ) (eta : ℚ) {w : ℝ}
    (t : P5Z.U11Adaptive.Four) (hw : w ≤ Z n N eta t) (F : ℕ → ℝ) :
    (∑ q ∈ P5Z.U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      coefficient n N eta t q * F (fullPrefix t * q)) = conditionalRow n N eta w t F := by
  exact native_sum_split N (Nat.ceil (Z n N eta t)) hw (D n N eta t)
    (fun q => F (fullPrefix t * q))

/-- This is the original native sigma, not a new beta-convolved sigma. It
includes both original bands and W without an artificial ordinary15 guard. -/
theorem joint_conditional_same_sigma (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop)
    {w : ℝ} (hw : ∀ t ∈ ordinaryTuples n N E, w ≤ Z n N eta t) (F : ℕ → ℝ) :
    (∑ t ∈ ordinaryTuples n N E, conditionalRow n N eta w t F) =
      ∑ q ∈ P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport n N eta E,
        P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q * F q := by
  rw [← P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.exact_pushforward]
  apply Finset.sum_congr rfl
  intro t ht
  exact (joint_row_conditional_test n N eta t (hw t ht) F).symm

/-- The entire signed original expression has the SAME physical sigma after
the joint beta/rough disintegration. Its small-factor dependence is retained. -/
theorem signed_conditional_same_sigma (B : LowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) {w : ℝ}
    (hw : ∀ t ∈ ordinaryTuples n N E, w ≤ Z n N eta t) (F : ℕ → ℝ) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors B N t,
      lowerRho B N t d * F ((t.1 * t.2) * d)) -
      (∑ t ∈ ordinaryTuples n N E, conditionalRow n N eta w t F) =
      ∑ q ∈ P5JointNativeSignedRegroup.support B n N eta E,
        P5JointNativeSignedRegroup.sigma B n N eta E q * F q := by
  rw [joint_conditional_same_sigma n N eta E hw F]
  rw [← P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.exact_pushforward]
  exact signed_pushforward B n N eta E F

/-- No tuple-cutoff supplier is needed at a common small exponent. Both the
arbitrary original mask and native sigma are unchanged by the regrouping. -/
theorem signed_conditional_common_exponent (B : LowerData) {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    {b : ℝ} (hb : b ≤ (417 / 5000 : ℝ) / 3) (F : ℕ → ℝ) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors B N t,
      lowerRho B N t d * F ((t.1 * t.2) * d)) -
      (∑ t ∈ ordinaryTuples n N E, conditionalRow n N eta ((N : ℝ) ^ b) t F) =
      ∑ q ∈ P5JointNativeSignedRegroup.support B n N eta E,
        P5JointNativeSignedRegroup.sigma B n N eta E q * F q :=
  signed_conditional_same_sigma B n N eta E
    (fun t ht => common_small_cutoff_le_Z hN heta ht hb) F

/-- Actual source legality gives the physical coprimality required to strip
the small factor. The old p2 cutoff is not declared coprime to the prefix. -/
theorem joint_small_factor_coprime {n N e d : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) {E : ℕ × ℕ → Prop}
    {t : P5Z.U11Adaptive.Four} (ht : t ∈ ordinaryTuples n N E)
    {w : ℝ} (hw : w ≤ Z n N eta t)
    (he : e ∈ actualSmallRosserSupport N (Nat.ceil (Z n N eta t)) w)
    (hd : d ∈ roughSupport N (Nat.ceil (Z n N eta t)) w (Z n N eta t)) :
    Nat.Coprime (fullPrefix t * d) e := by
  have hprod : e * d ∈ actualSmallRosserSupport N (Nat.ceil (Z n N eta t)) (Z n N eta t) := by
    rw [nativeSupport_eq_products N _ hw]
    exact Finset.mem_image.mpr ⟨(e, d), Finset.mem_product.mpr ⟨he, hd⟩, rfl⟩
  have hdiv : e * d ∣ sieveProduct N (Nat.ceil (Z n N eta t)) := by
    have h := (Nat.mem_divisors.mp hprod).1
    rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N _ _ (Nat.le_ceil _)] at h
  have hl := compiled_legality hN heta ht
  have hZ : Z n N eta t ≤ (slots t 3 : ℝ) := by
    simpa only [slots, Matrix.cons_val_three] using hl.2.2.1
  have hprefix := fullPrefix_coprime_lowered_sieve (Finset.mem_filter.mp ht).1 hZ
  have hcop := chenQuotient_allowed_coprime hprefix hdiv
  have hcross := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N _ w he) (roughSupport_rough hd)
  exact Nat.coprime_mul_iff_left.mpr ⟨(Nat.coprime_mul_iff_right.mp hcop).1, hcross.symm⟩

theorem joint_phi_peeling {n N e d : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) {E : ℕ × ℕ → Prop}
    {t : P5Z.U11Adaptive.Four} (ht : t ∈ ordinaryTuples n N E)
    {w : ℝ} (hw : w ≤ Z n N eta t)
    (he : e ∈ actualSmallRosserSupport N (Nat.ceil (Z n N eta t)) w)
    (hd : d ∈ roughSupport N (Nat.ceil (Z n N eta t)) w (Z n N eta t)) :
    Nat.totient (fullPrefix t * (e * d)) = Nat.totient (fullPrefix t * d) * Nat.totient e := by
  rw [show fullPrefix t * (e * d) = (fullPrefix t * d) * e by ring,
    Nat.totient_mul (joint_small_factor_coprime hN heta ht hw he hd)]

/-- Exact native row main after common-factor stripping. The denominator
uses the FULL four-prime prefix and retains lambda+(e*d) in the numerator. -/
theorem joint_conditional_totient {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) {E : ℕ × ℕ → Prop}
    {t : P5Z.U11Adaptive.Four} (ht : t ∈ ordinaryTuples n N E)
    {w : ℝ} (hw : w ≤ Z n N eta t) (M : ℝ) :
    (∑ q ∈ P5Z.U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      coefficient n N eta t q * (M / (Nat.totient (fullPrefix t * q) : ℝ))) =
      ∑ e ∈ actualSmallRosserSupport N (Nat.ceil (Z n N eta t)) w,
      ∑ d ∈ roughSupport N (Nat.ceil (Z n N eta t)) w (Z n N eta t),
      coefficient n N eta t (e * d) *
        (M / ((Nat.totient (fullPrefix t * d) : ℝ) * (Nat.totient e : ℝ))) := by
  rw [joint_row_conditional_test n N eta t hw]
  unfold conditionalRow
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro d hd
  rw [joint_phi_peeling hN heta ht hw he hd, Nat.cast_mul]

/-- In particular the original same-sigma AP and centre expression uses
this exact conditional row, with no coefficient or density match input. -/
theorem signed_conditional_estimator (B : LowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) {w : ℝ}
    (hw : ∀ t ∈ ordinaryTuples n N E, w ≤ Z n N eta t) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors B N t,
      lowerRho B N t d * (chenPrimeAPCount N N ((t.1 * t.2) * d) -
        chenCentrePrimeAPCount N N ((t.1 * t.2) * d))) -
      (∑ t ∈ ordinaryTuples n N E, conditionalRow n N eta w t
        (fun q => chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) =
      P5JointNativeSignedRegroup.estimator B n N eta E :=
  signed_conditional_same_sigma B n N eta E hw _

/-- Before AP norms or density estimates, the concrete conditional native
compiler is a lower estimator for the ORIGINAL paired prime sum. The fallback
is its actual count, and the positive lower row keeps its actual minorant. -/
theorem original_paired_conditional_lower (B : LowerData) {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    {b : ℝ} (hb : b ≤ (417 / 5000 : ℝ) / 3)
    (hgates : ∀ t ∈ lowerRows N E,
      1 < B.L t ∧ B.w t ≤ B.L t ∧ B.w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    otherRows N +
      ((∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors B N t,
        lowerRho B N t d * (chenPrimeAPCount N N ((t.1 * t.2) * d) -
          chenCentrePrimeAPCount N N ((t.1 * t.2) * d))) -
        (∑ t ∈ ordinaryTuples n N E, conditionalRow n N eta ((N : ℝ) ^ b) t
          (fun q => chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q))) -
      P5JointNativeSignedRegroup.fallback n N E ≤ currentChenPairedPrimeSum N E := by
  have heq := signed_conditional_estimator B n N eta E
    (fun t ht => common_small_cutoff_le_Z hN heta ht hb)
  rw [heq]
  have h := original_joint_signed_lower B hN heta E hgates
  rw [currentChenPairedPrimeSum_eq_upsilon]
  unfold otherRows
  linarith only [h]

end
end ImbalancedChen.P5JointNativeConditionalBeta
