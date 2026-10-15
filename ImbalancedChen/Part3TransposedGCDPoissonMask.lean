import ImbalancedChen.Part3TransposedZeroCovariance
import ImbalancedChen.Part3SignedDivisorDeletion

/-!
# One actual paired-gcd mask in whole W, raw zero and full Fourier remainder

The same original-alpha pair and real cutoff are retained in all three
terms of the transposed Poisson identity. Bounding whole W alone is not
asserted to bound its Fourier remainder: the raw zero under the same
mask is kept and paid separately below.

The actual paired coefficient is original alpha extended by zero, so its
large-gcd mass uses the already proved finite estimate at order one and
T=2U. The raw zero pays the actual complex factor fibers through tau_3
and the existing lcm moment, with logarithm exponent nineteen. Its common
scalar remains original V times the local Fourier-zero cutoffMass.

Only the two already owned local parents are imported. No new foreign
module, transposed MediumAdmissible assertion or analytical budget premise
is used. The whole-W large-gcd payment and its genuine alpha cleaning are
separate from this finite Poisson and raw-zero leaf.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def MediumAtom.commonFactorPairZeroWeight (d : MediumAtom) (n₁ n₂ : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
        ((d.U / (complexFactorModulus a).lcm (complexFactorModulus b)) *
          CommonSmoothCutoff.cutoffMass : ℝ) else 0 : ℝ)

def MediumAtom.commonFactorPairNonzeroWeight (d : MediumAtom) (n₁ n₂ : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
        (∑' h : ℤ, CommonSmoothCutoff.poissonNonzeroFrequency
          (d.U / (complexFactorModulus a).lcm (complexFactorModulus b))
          ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
            n₁ n₂ d.residue : ℝ) /
              (complexFactorModulus a).lcm (complexFactorModulus b)) h).re else 0 : ℝ)

def MediumAtom.commonLargeBetaGCDZeroPart (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then
      d.beta n₁ * star (d.beta n₂) * d.commonFactorPairZeroWeight n₁ n₂ else 0

def MediumAtom.commonLargeBetaGCDNonzeroPart (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then
      d.beta n₁ * star (d.beta n₂) * d.commonFactorPairNonzeroWeight n₁ n₂ else 0

def MediumAtom.commonSmallBetaGCDNonzeroPart (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then 0 else
      d.beta n₁ * star (d.beta n₂) * d.commonFactorPairNonzeroWeight n₁ n₂

def MediumAtom.transposedLargePairMass (d : MediumAtom) (Y : ℝ) : ℝ :=
  ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then
      ‖d.transposedAtom.beta n₁‖ * ‖d.transposedAtom.beta n₂‖ else 0

namespace TransposedGCDPoissonMask

private theorem factor_modulus_pos
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {a : ℕ × ℕ × ℕ}
    (ha : a ∈ d.complexFactorLabels) : 0 < complexFactorModulus a :=
  (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
    (Finset.mem_image_of_mem _ ha))).1

theorem transposedDispersionW_eq_betaPairs
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.transposedAtom.complexDispersionW d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight : ℂ) =
      ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
        d.transposedAtom.beta n₁ * star (d.transposedAtom.beta n₂) *
          d.transposedAtom.commonFactorPairWeight n₁ n₂ := by
  rw [d.transposedDispersionW_eq_constructedCRT hd]
  simp only [MediumAtom.complexRowLabels, Finset.sum_product,
    MediumAtom.complexBetaCoefficient, star_mul]
  simp_rw [Finset.sum_comm
    (s := d.transposedAtom.complexFactorLabels) (t := d.transposedAtom.betaCarrier)]
  simp only [MediumAtom.commonFactorPairWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show d.transposedAtom.residue = d.residue from rfl]
  ring

/-- The masked whole W is a literal part of the actual transposed W. -/
theorem transposedDispersionW_eq_large_add_small
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    (d.transposedAtom.complexDispersionW d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight : ℂ) =
      d.transposedAtom.commonLargeBetaGCDW Y + d.transposedAtom.commonSmallBetaGCDW Y := by
  rw [transposedDispersionW_eq_betaPairs hd]
  unfold MediumAtom.commonLargeBetaGCDW MediumAtom.commonSmallBetaGCDW
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₂ _
  split_ifs <;> simp only [add_zero, zero_add]

/-- The actual original-V smoothing is used on each complete physical lcm.
No beta coefficient, gcd mask or frequency is discarded in this identity. -/
theorem transposed_factorPair_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n₁ n₂ : ℕ) :
    d.transposedAtom.commonFactorPairWeight n₁ n₂ =
      d.transposedAtom.commonFactorPairZeroWeight n₁ n₂ +
        d.transposedAtom.commonFactorPairNonzeroWeight n₁ n₂ := by
  unfold MediumAtom.commonFactorPairWeight MediumAtom.commonFactorPairZeroWeight
    MediumAtom.commonFactorPairNonzeroWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  change d.complexFactorGamma a * star (d.complexFactorGamma b) *
    (ComplexCRT.constructedProgressionWeight d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight d.residue
        (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ : ℂ) = _
  unfold ComplexCRT.constructedProgressionWeight
  by_cases hc : ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂
  · simp only [hc, if_true]
    have hD : 0 < (complexFactorModulus a).lcm (complexFactorModulus b) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (factor_modulus_pos hd ha).ne'
        (factor_modulus_pos hd hb).ne')
    have he := CommonSmoothCutoff.scaledDyadicCutoff_finset_progression_eq_main_add_fourier
      (lt_of_lt_of_le zero_lt_one hd.2.1) d.transposedAtom.commonSmoothCarrier
      (fun m hm ↦ d.transposedSmoothWeight_support_subset hd.2.1 hm) hD
      (ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ d.residue)
    simp only [MediumAtom.commonSmoothWeight, MediumAtom.transposedAtom,
      MediumAtom.complexFactorGamma] at he ⊢
    rw [he, Complex.ofReal_add]
    ring
  · simp only [hc, if_false, Complex.ofReal_zero, mul_zero, add_zero]

/-- Whole W and raw zero have exactly the same actual gcd mask. -/
theorem transposed_largeW_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    d.transposedAtom.commonLargeBetaGCDW Y =
      d.transposedAtom.commonLargeBetaGCDZeroPart Y +
        d.transposedAtom.commonLargeBetaGCDNonzeroPart Y := by
  unfold MediumAtom.commonLargeBetaGCDW MediumAtom.commonLargeBetaGCDZeroPart
    MediumAtom.commonLargeBetaGCDNonzeroPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₂ _
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy, transposed_factorPair_eq_zero_add_nonzero hd, mul_add]
  · simp only [if_neg hy, add_zero]

theorem complexCRTSmoothNonzeroPart_eq_betaPairs (d : MediumAtom) :
    d.complexCRTSmoothNonzeroPart =
      ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
        d.beta n₁ * star (d.beta n₂) * d.commonFactorPairNonzeroWeight n₁ n₂ := by
  unfold MediumAtom.complexCRTSmoothNonzeroPart
  simp only [MediumAtom.complexRowLabels, Finset.sum_product,
    MediumAtom.complexBetaCoefficient, star_mul]
  simp_rw [Finset.sum_comm (s := d.complexFactorLabels) (t := d.betaCarrier)]
  simp only [MediumAtom.commonFactorPairNonzeroWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The complementary piece has the explicit gcd<=Y branch, and the
full signed Poisson remainder is exactly their sum. -/
theorem complexCRTSmoothNonzeroPart_eq_large_add_small (d : MediumAtom) (Y : ℝ) :
    d.complexCRTSmoothNonzeroPart =
      d.commonLargeBetaGCDNonzeroPart Y + d.commonSmallBetaGCDNonzeroPart Y := by
  rw [complexCRTSmoothNonzeroPart_eq_betaPairs]
  unfold MediumAtom.commonLargeBetaGCDNonzeroPart MediumAtom.commonSmallBetaGCDNonzeroPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₂ _
  split_ifs <;> simp only [add_zero, zero_add]

/-- The actual primitive V/U terms stay literal when the full Fourier
remainder is partitioned by this paired gcd. -/
theorem transposed_centered_identity_with_large_small
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    ((∑ n ∈ d.transposedAtom.commonSmoothCarrier,
      d.transposedAtom.commonSmoothWeight n * ‖d.transposedAtom.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (d.transposedAtom.complexCRTSmoothZeroPart -
        2 * (d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) +
        (d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ)) +
        (d.transposedAtom.commonLargeBetaGCDNonzeroPart Y +
          d.transposedAtom.commonSmallBetaGCDNonzeroPart Y) := by
  rw [d.transposed_dispersion_identity_with_commonPoisson hd,
    complexCRTSmoothNonzeroPart_eq_large_add_small d.transposedAtom Y]

/-- The masked Fourier remainder is bounded only after subtracting the
raw zero under that same mask. This is not a whole-W substitution. -/
theorem transposed_largeNonzero_norm_le_W_add_zero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    ‖d.transposedAtom.commonLargeBetaGCDNonzeroPart Y‖ ≤
      ‖d.transposedAtom.commonLargeBetaGCDW Y‖ +
        ‖d.transposedAtom.commonLargeBetaGCDZeroPart Y‖ := by
  have he : d.transposedAtom.commonLargeBetaGCDNonzeroPart Y =
      d.transposedAtom.commonLargeBetaGCDW Y - d.transposedAtom.commonLargeBetaGCDZeroPart Y := by
    rw [transposed_largeW_eq_zero_add_nonzero hd]
    ring
  rw [he]
  exact norm_sub_le _ _

private theorem lcm_weight_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
      ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ / (q.lcm r : ℝ)) ≤
        (1 + Real.log d.physicalFactorCap) ^ 19 := by
  have hh := MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_abs_lcm_weight_le_log
    3 (d.one_le_physicalFactorCap hd) d.physicalFactorModuli
    (d.physicalFactorModuli_subset_cap hd) (fun q ↦ ‖d.groupedFactorGamma q‖)
    (fun q _ ↦ by simpa only [abs_norm] using d.groupedFactorGamma_norm_le_tauThree hd q)
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    exact (abs_of_nonneg (by positivity)).symm
  · norm_num

/-- The complete original complex factor convolution is grouped exactly
before its norm. No multiplicity-one or modulus coprimality is assumed. -/
theorem transposed_factorPairZero_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n₁ n₂ : ℕ) :
    ‖d.transposedAtom.commonFactorPairZeroWeight n₁ n₂‖ ≤
      |d.V * CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19 := by
  unfold MediumAtom.commonFactorPairZeroWeight
  change ‖∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
        ((d.V / (complexFactorModulus a).lcm (complexFactorModulus b)) *
          CommonSmoothCutoff.cutoffMass : ℝ) else 0 : ℝ)‖ ≤ _
  rw [TransposedZeroCovariance.factor_pair_sum_eq_grouped d (fun q r ↦
    ((if ComplexCRT.Compatible q r n₁ n₂ then
      (d.V / (q.lcm r : ℝ)) * CommonSmoothCutoff.cutoffMass else 0 : ℝ) : ℂ))]
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        |d.V * CommonSmoothCutoff.cutoffMass| *
          (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ / (q.lcm r : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r _
      by_cases hc : ComplexCRT.Compatible q r n₁ n₂
      · simp only [if_pos hc, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
          abs_mul, abs_div, abs_of_nonneg
            (show (0 : ℝ) ≤ (q.lcm r : ℝ) from Nat.cast_nonneg (q.lcm r))]
        exact le_of_eq (by ring)
      · simp only [if_neg hc, Complex.ofReal_zero, mul_zero, norm_zero]
        positivity
    _ = |d.V * CommonSmoothCutoff.cutoffMass| *
        ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
          ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ / (q.lcm r : ℝ) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lcm_weight_sum_le hd) (abs_nonneg _)

theorem transposed_largeZero_norm_le_pairMass
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    ‖d.transposedAtom.commonLargeBetaGCDZeroPart Y‖ ≤
      |d.V * CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19 *
        d.transposedLargePairMass Y := by
  unfold MediumAtom.commonLargeBetaGCDZeroPart MediumAtom.transposedLargePairMass
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₁ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₂ _
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy, norm_mul, norm_star]
    calc
      _ ≤ (‖d.transposedAtom.beta n₁‖ * ‖d.transposedAtom.beta n₂‖) *
          (|d.V * CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19) :=
        mul_le_mul_of_nonneg_left (transposed_factorPairZero_norm_le hd n₁ n₂)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  · simp only [if_neg hy, norm_zero, mul_zero, le_refl]

/-- The true original-alpha coefficient is one-bounded on its actual
paired carrier, including the zero padding of the original interval. -/
theorem transposed_largePairMass_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {Y : ℝ} (hY : 0 < Y) :
    d.transposedLargePairMass Y ≤
      (2 * d.U) ^ 2 * Real.sqrt ((1 + Real.log (2 * d.U)) / Y) := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  have hN := d.transposedAtom.betaCarrier_subset_twiceV hd.1
  have hbeta : ∀ n ∈ d.transposedAtom.betaCarrier,
      |‖d.transposedAtom.beta n‖| ≤ (fouvryTau 1 n : ℝ) := by
    intro n hn
    have hn0 := (Finset.mem_Ioc.mp (hN hn)).1
    rw [abs_norm, fouvryTau_order_one hn0.ne', Nat.cast_one]
    change ‖if n ∈ d.alphaCarrier then d.alpha n else 0‖ ≤ 1
    by_cases hm : n ∈ d.alphaCarrier
    · simpa only [if_pos hm] using hAlpha n hm
    · simp only [if_neg hm, norm_zero, zero_le_one]
  have hh := ActualLargeGCDBetaMass.sum_abs_largeGCDPairs_le (k := 1) (by norm_num)
    (show 1 ≤ 2 * d.U by linarith [hd.1]) hY d.transposedAtom.betaCarrier hN
    (fun n ↦ ‖d.transposedAtom.beta n‖) hbeta
  simpa only [MediumAtom.transposedLargePairMass, ActualLargeGCDBetaMass.largeGCDPairs,
    Finset.sum_filter, Finset.sum_product, abs_mul, abs_norm, one_pow,
    Nat.sub_self, pow_zero, mul_one] using hh

/-- Actual outside beta-L2 is paid at length 2V. The right side keeps
the original X=U*V, the local mass and both explicit logarithm costs. -/
theorem betaL2_mul_transposed_largeZero_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {Y : ℝ} (hY : 0 < Y) :
    (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
      ‖d.transposedAtom.commonLargeBetaGCDZeroPart Y‖ ≤
        8 * |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
            (1 + Real.log d.physicalFactorCap) ^ 19 *
              Real.sqrt ((1 + Real.log (2 * d.U)) / Y) := by
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hcapLog : 0 ≤ 1 + Real.log d.physicalFactorCap :=
    by linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  have hlogV : 0 ≤ 1 + Real.log (2 * d.V) :=
    by linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hz := (transposed_largeZero_norm_le_pairMass hd Y).trans
    (mul_le_mul_of_nonneg_left (transposed_largePairMass_le hd hY) (by positivity))
  calc
    _ ≤ (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (|d.V * CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19 *
          ((2 * d.U) ^ 2 * Real.sqrt ((1 + Real.log (2 * d.U)) / Y))) :=
      mul_le_mul (mediumAdmissible_beta_norm_sq_sum_le hd) hz (norm_nonneg _) (by positivity)
    _ = _ := by rw [abs_mul, abs_of_nonneg hV]; unfold MediumAtom.scale; ring

end TransposedGCDPoissonMask

end

end ImbalancedChen.Part3
