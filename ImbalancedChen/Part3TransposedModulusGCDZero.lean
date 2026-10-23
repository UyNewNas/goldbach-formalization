import ImbalancedChen.Part3PairedAlphaDeletion
import ImbalancedChen.Part3TransposedGCDPoissonMask

/-!
# A second actual gcd mask and its raw-zero payment

After keeping the original-alpha pair gcd at most Y, this leaf masks the
common physical modulus gcd above D. Whole W, raw zero and the complete
signed Fourier remainder use exactly that same mask. The complementary
Fourier piece retains both small gcd conditions explicitly.

The raw-zero estimate keeps compatibility until its natural congruence
n1 = n2 modulo gcd(q,r) has been counted on the actual paired carrier.
Original alpha is one-bounded there, including the actual zero padding.
The resulting count is 2U(2U/gcd(q,r)+1). Thus the diagonal is retained
in the honest O(U) term; no divisor set of a zero difference is formed.
The complete physical Gamma convolution pays tau_3 and H(cap)^19.

Multiplication by the original beta-L2 gives an actual X^2 bound with
cost (1/D+1/U). At D=X^delta, the original U>=X^sigma gate pays every
fixed requested logarithm. This pays raw zero under this mask, not the
masked whole W or its Fourier difference. Those whole-W progression
and subsequent small-gcd estimates remain separate obligations.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def MediumAtom.commonLargeModulusGCDWeight (d : MediumAtom) (D : ℝ) (n₁ n₂ : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then
        (ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
          d.residue (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ : ℂ) else 0)

def MediumAtom.commonLargeModulusGCDZeroWeight (d : MediumAtom) (D : ℝ) (n₁ n₂ : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then
        ((if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
          (d.U / (complexFactorModulus a).lcm (complexFactorModulus b)) *
            CommonSmoothCutoff.cutoffMass else 0 : ℝ) : ℂ) else 0)

def MediumAtom.commonModulusGCDNonzeroWeight (d : MediumAtom) (D : ℝ) (large : Bool)
    (n₁ n₂ : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if decide (D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ)) = large then
        ((if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
          (∑' h : ℤ, CommonSmoothCutoff.poissonNonzeroFrequency
            (d.U / (complexFactorModulus a).lcm (complexFactorModulus b))
            ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
              n₁ n₂ d.residue : ℝ) /
                (complexFactorModulus a).lcm (complexFactorModulus b)) h).re else 0 : ℝ) : ℂ)
      else 0)

def MediumAtom.commonSmallBetaLargeModulusGCDW (d : MediumAtom) (Y D : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then 0 else
      d.beta n₁ * star (d.beta n₂) * d.commonLargeModulusGCDWeight D n₁ n₂

def MediumAtom.commonSmallBetaLargeModulusGCDZeroPart (d : MediumAtom) (Y D : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then 0 else
      d.beta n₁ * star (d.beta n₂) * d.commonLargeModulusGCDZeroWeight D n₁ n₂

def MediumAtom.commonSmallBetaModulusGCDNonzeroPart (d : MediumAtom) (Y D : ℝ)
    (large : Bool) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then 0 else
      d.beta n₁ * star (d.beta n₂) * d.commonModulusGCDNonzeroWeight D large n₁ n₂

/-- This is the exact signed alpha pair mass before any norm. -/
def MediumAtom.smallBetaCompatiblePairMass (d : MediumAtom) (Y : ℝ) (q r : ℕ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then 0 else
      if ComplexCRT.Compatible q r n₁ n₂ then d.beta n₁ * star (d.beta n₂) else 0

namespace TransposedModulusGCDZero

private theorem factor_modulus_pos
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {a : ℕ × ℕ × ℕ}
    (ha : a ∈ d.complexFactorLabels) : 0 < complexFactorModulus a :=
  (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
    (Finset.mem_image_of_mem _ ha))).1

/-- Poisson is applied on each complete original physical lcm. -/
theorem transposed_largeModulusWeight_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D : ℝ) (n₁ n₂ : ℕ) :
    d.transposedAtom.commonLargeModulusGCDWeight D n₁ n₂ =
      d.transposedAtom.commonLargeModulusGCDZeroWeight D n₁ n₂ +
        d.transposedAtom.commonModulusGCDNonzeroWeight D true n₁ n₂ := by
  unfold MediumAtom.commonLargeModulusGCDWeight MediumAtom.commonLargeModulusGCDZeroWeight
    MediumAtom.commonModulusGCDNonzeroWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hD : D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ)
  · have hmask : decide (D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ)) = true :=
      decide_eq_true hD
    simp only [if_pos hD, if_pos hmask]
    unfold ComplexCRT.constructedProgressionWeight
    by_cases hc : ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂
    · simp only [if_pos hc]
      have hL : 0 < (complexFactorModulus a).lcm (complexFactorModulus b) :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (factor_modulus_pos hd ha).ne'
          (factor_modulus_pos hd hb).ne')
      have he := CommonSmoothCutoff.scaledDyadicCutoff_finset_progression_eq_main_add_fourier
        (M := d.transposedAtom.U) (lt_of_lt_of_le zero_lt_one hd.2.1) d.transposedAtom.commonSmoothCarrier
        (fun m hm ↦ d.transposedSmoothWeight_support_subset hd.2.1 hm) hL
        (ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
          n₁ n₂ d.transposedAtom.residue)
      simp only [MediumAtom.commonSmoothWeight]
      rw [he, Complex.ofReal_add]
      ring
    · simp only [if_neg hc, Complex.ofReal_zero, mul_zero, add_zero]
  · have hmask : decide (D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ)) ≠ true := by
      intro h
      exact hD (of_decide_eq_true h)
    simp only [if_neg hD, if_neg hmask, mul_zero, add_zero]

/-- The same two gcd gates occur in whole W, raw zero and full Fourier. -/
theorem transposed_smallBeta_largeModulusW_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y D : ℝ) :
    d.transposedAtom.commonSmallBetaLargeModulusGCDW Y D =
      d.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y D +
        d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D true := by
  unfold MediumAtom.commonSmallBetaLargeModulusGCDW
    MediumAtom.commonSmallBetaLargeModulusGCDZeroPart
    MediumAtom.commonSmallBetaModulusGCDNonzeroPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₂ _
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy, add_zero]
  · simp only [if_neg hy, transposed_largeModulusWeight_eq_zero_add_nonzero hd, mul_add]

theorem smallBeta_nonzero_eq_large_small_modulus (d : MediumAtom) (Y D : ℝ) :
    d.commonSmallBetaGCDNonzeroPart Y =
      d.commonSmallBetaModulusGCDNonzeroPart Y D true +
        d.commonSmallBetaModulusGCDNonzeroPart Y D false := by
  unfold MediumAtom.commonSmallBetaGCDNonzeroPart MediumAtom.commonSmallBetaModulusGCDNonzeroPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₂ _
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy, add_zero]
  · simp only [if_neg hy, ← mul_add]
    congr 1
    unfold MediumAtom.commonFactorPairNonzeroWeight MediumAtom.commonModulusGCDNonzeroWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hD : D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) <;>
      simp [hD]

theorem transposed_largeModulusNonzero_norm_le_W_add_zero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y D : ℝ) :
    ‖d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D true‖ ≤
      ‖d.transposedAtom.commonSmallBetaLargeModulusGCDW Y D‖ +
        ‖d.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y D‖ := by
  have he : d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D true =
      d.transposedAtom.commonSmallBetaLargeModulusGCDW Y D -
        d.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y D := by
    rw [transposed_smallBeta_largeModulusW_eq_zero_add_nonzero hd]
    ring
  rw [he]
  exact norm_sub_le _ _

/-- Both literal primitive terms and all three signed Fourier pieces
refer to the same actual atom and smoothing. -/
theorem transposed_centered_identity_with_two_gcd_masks
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y D : ℝ) :
    ((∑ n ∈ d.transposedAtom.commonSmoothCarrier,
      d.transposedAtom.commonSmoothWeight n * ‖d.transposedAtom.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (d.transposedAtom.complexCRTSmoothZeroPart -
        2 * (d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) +
        (d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ)) +
        (d.transposedAtom.commonLargeBetaGCDNonzeroPart Y +
          (d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D true +
            d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D false)) := by
  rw [TransposedGCDPoissonMask.transposed_centered_identity_with_large_small hd,
    smallBeta_nonzero_eq_large_small_modulus d.transposedAtom Y D]

private theorem transposed_beta_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.transposedAtom.beta n‖ ≤ 1 := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  change ‖if n ∈ d.alphaCarrier then d.alpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.alphaCarrier
  · simpa only [if_pos hn] using hAlpha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

/-- The progression count is on the actual original-alpha paired carrier.
The temporary record changes only the residue of the elementary counter. -/
private theorem transposed_betaCarrier_modEq_card_le
    {d : MediumAtom} (hU : 1 ≤ d.U) {delta : ℕ} (hdelta : 0 < delta) (b : ℕ) :
    ((d.transposedAtom.betaCarrier.filter (fun n : ℕ ↦ Nat.ModEq delta n b)).card : ℝ) ≤
      2 * d.U / delta + 1 := by
  have hh := PairedAlphaDeletion.betaCarrier_progression_card_le
    (d := { d.transposedAtom with residue := (b : ℤ) }) hU hdelta
    (show (1 : ℕ).Coprime delta by simp)
  change ((d.transposedAtom.betaCarrier.filter
    (fun n : ℕ ↦ Int.ModEq delta ((n : ℤ) * (1 : ℕ)) (b : ℤ))).card : ℝ) ≤
      2 * d.U / delta + 1 at hh
  simpa only [Nat.cast_one, mul_one, Int.natCast_modEq_iff] using hh

/-- Compatibility is used before taking the coarse count. The O(U)
diagonal cost remains and will be paid using the actual U lower gate. -/
theorem transposed_compatiblePairMass_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) {q r : ℕ}
    (hdelta : 0 < q.gcd r) :
    ‖d.transposedAtom.smallBetaCompatiblePairMass Y q r‖ ≤
      2 * d.U * (2 * d.U / (q.gcd r : ℝ) + 1) := by
  have hU0 : 0 ≤ d.U := by linarith [hd.1]
  unfold MediumAtom.smallBetaCompatiblePairMass
  have hcard : (d.transposedAtom.betaCarrier.card : ℝ) ≤ 2 * d.U := by
    have hc := Finset.card_le_card (d.transposedAtom.betaCarrier_subset_twiceV hd.1)
    simp only [Nat.card_Ioc, Nat.sub_zero] at hc
    exact (show (d.transposedAtom.betaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
      exact_mod_cast hc).trans (Nat.floor_le (by linarith [hd.1] : 0 ≤ 2 * d.U))
  calc
    _ ≤ ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
        if Nat.ModEq (q.gcd r) n₁ n₂ then (1 : ℝ) else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n₁ _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n₂ _
      by_cases hy : Y < (n₁.gcd n₂ : ℝ)
      · simp only [if_pos hy, norm_zero]
        split_ifs <;> norm_num
      · by_cases hc : ComplexCRT.Compatible q r n₁ n₂
        · simp only [if_neg hy, if_pos hc, if_pos hc.2.2, norm_mul, norm_star]
          simpa only [one_mul] using mul_le_mul
            (transposed_beta_norm_le_one hd n₁) (transposed_beta_norm_le_one hd n₂)
            (norm_nonneg _) zero_le_one
        · simp only [if_neg hy, if_neg hc, norm_zero]
          split_ifs <;> norm_num
    _ = ∑ n₂ ∈ d.transposedAtom.betaCarrier,
        ((d.transposedAtom.betaCarrier.filter
          (fun n₁ : ℕ ↦ Nat.ModEq (q.gcd r) n₁ n₂)).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n₂ _
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ _n₂ ∈ d.transposedAtom.betaCarrier, (2 * d.U / (q.gcd r : ℝ) + 1) :=
      Finset.sum_le_sum (fun n₂ _ ↦ transposed_betaCarrier_modEq_card_le hd.1 hdelta n₂)
    _ = (d.transposedAtom.betaCarrier.card : ℝ) * (2 * d.U / (q.gcd r : ℝ) + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

/-- Exact grouping precedes every norm. The complete physical Gamma is
not replaced by a one-bounded coefficient. -/
theorem transposed_largeModulusZero_eq_grouped
    (d : MediumAtom) (Y D : ℝ) :
    d.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y D =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
          (if D < (q.gcd r : ℝ) then
            ((d.V / (q.lcm r : ℝ)) * CommonSmoothCutoff.cutoffMass : ℝ) *
              d.transposedAtom.smallBetaCompatiblePairMass Y q r else 0) := by
  have hg (n₁ n₂ : ℕ) : d.transposedAtom.commonLargeModulusGCDZeroWeight D n₁ n₂ =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
          (if D < (q.gcd r : ℝ) then
            ((if ComplexCRT.Compatible q r n₁ n₂ then
              (d.V / (q.lcm r : ℝ)) * CommonSmoothCutoff.cutoffMass else 0 : ℝ) : ℂ) else 0) := by
    exact TransposedZeroCovariance.factor_pair_sum_eq_grouped d (fun q r ↦
      if D < (q.gcd r : ℝ) then
        ((if ComplexCRT.Compatible q r n₁ n₂ then
          (d.V / (q.lcm r : ℝ)) * CommonSmoothCutoff.cutoffMass else 0 : ℝ) : ℂ) else 0)
  have hterm (n₁ n₂ : ℕ) :
      (if Y < (n₁.gcd n₂ : ℝ) then 0 else
        d.transposedAtom.beta n₁ * star (d.transposedAtom.beta n₂) *
          d.transposedAtom.commonLargeModulusGCDZeroWeight D n₁ n₂) =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
          (if D < (q.gcd r : ℝ) then
            ((d.V / (q.lcm r : ℝ)) * CommonSmoothCutoff.cutoffMass : ℝ) *
              (if Y < (n₁.gcd n₂ : ℝ) then 0 else
                if ComplexCRT.Compatible q r n₁ n₂ then
                  d.transposedAtom.beta n₁ * star (d.transposedAtom.beta n₂) else 0) else 0) := by
    by_cases hy : Y < (n₁.gcd n₂ : ℝ)
    · simp [hy]
    · rw [if_neg hy, hg]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      by_cases hD : D < (q.gcd r : ℝ) <;>
        by_cases hc : ComplexCRT.Compatible q r n₁ n₂ <;>
        simp [hy, hD, hc]
      all_goals ring
  have hphysical (q r : ℕ) :
      d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
        (if D < (q.gcd r : ℝ) then
          ((d.V / (q.lcm r : ℝ)) * CommonSmoothCutoff.cutoffMass : ℝ) *
            d.transposedAtom.smallBetaCompatiblePairMass Y q r else 0) =
      ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
        d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
          (if D < (q.gcd r : ℝ) then
            ((d.V / (q.lcm r : ℝ)) * CommonSmoothCutoff.cutoffMass : ℝ) *
              (if Y < (n₁.gcd n₂ : ℝ) then 0 else
                if ComplexCRT.Compatible q r n₁ n₂ then
                  d.transposedAtom.beta n₁ * star (d.transposedAtom.beta n₂) else 0) else 0) := by
    by_cases hD : D < (q.gcd r : ℝ) <;>
      simp [hD, MediumAtom.smallBetaCompatiblePairMass, Finset.mul_sum]
  unfold MediumAtom.commonSmallBetaLargeModulusGCDZeroPart
  simp_rw [hterm, hphysical]
  simp_rw [Finset.sum_comm (s := d.transposedAtom.betaCarrier) (t := d.physicalFactorModuli)]

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
    exact (abs_of_nonneg (div_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (show (0 : ℝ) ≤ (q.lcm r : ℝ) from Nat.cast_nonneg (q.lcm r)))).symm
  · norm_num

/-- The entire masked raw zero, including its diagonal, has a genuine
1/D+1/U saving. Y is arbitrary because its mask is enlarged only here. -/
theorem transposed_largeModulusZero_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) {D : ℝ} (hD : 0 < D) :
    ‖d.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y D‖ ≤
      |d.V * CommonSmoothCutoff.cutoffMass| * (4 * d.U ^ 2 / D + 2 * d.U) *
        (1 + Real.log d.physicalFactorCap) ^ 19 := by
  have hU0 : 0 ≤ d.U := by linarith [hd.1]
  rw [transposed_largeModulusZero_eq_grouped]
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        |d.V * CommonSmoothCutoff.cutoffMass| * (4 * d.U ^ 2 / D + 2 * d.U) *
          (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ / (q.lcm r : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r _
      by_cases hdelta : D < (q.gcd r : ℝ)
      · have hdelta0 : 0 < q.gcd r := by exact_mod_cast hD.trans hdelta
        have hmass := transposed_compatiblePairMass_norm_le hd Y hdelta0
        have hcount : 2 * d.U * (2 * d.U / (q.gcd r : ℝ) + 1) ≤
            4 * d.U ^ 2 / D + 2 * d.U := by
          have hh := div_le_div_of_nonneg_left (show 0 ≤ 2 * d.U by positivity)
            hD hdelta.le
          calc
            _ ≤ 2 * d.U * (2 * d.U / D + 1) :=
              mul_le_mul_of_nonneg_left (add_le_add hh (le_refl (1 : ℝ))) (by positivity)
            _ = _ := by ring
        simp only [if_pos hdelta, norm_mul, norm_star, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg
            (show (0 : ℝ) ≤ (q.lcm r : ℝ) from Nat.cast_nonneg (q.lcm r))]
        calc
          _ ≤ (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖) *
              ((|d.V| / (q.lcm r : ℝ) * |CommonSmoothCutoff.cutoffMass|) *
                (4 * d.U ^ 2 / D + 2 * d.U)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hmass.trans hcount) (by positivity)) (by positivity)
          _ = _ := by ring
      · simp only [if_neg hdelta, mul_zero, norm_zero]
        positivity
    _ = (|d.V * CommonSmoothCutoff.cutoffMass| * (4 * d.U ^ 2 / D + 2 * d.U)) *
        ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
          ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ / (q.lcm r : ℝ) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lcm_weight_sum_le hd) (by positivity)

/-- This is the actual original-beta outside factor, not an assumed
energy budget. The diagonal's surviving reciprocal U is explicit. -/
theorem betaL2_mul_transposed_largeModulusZero_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) {D : ℝ} (hD : 0 < D) :
    (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
      ‖d.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y D‖ ≤
        8 * |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
            (1 + Real.log d.physicalFactorCap) ^ 19 * (1 / D + 1 / d.U) := by
  have hU0 : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV0 : 0 ≤ d.V := by linarith [hd.2.1]
  have hHV : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hHC : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  calc
    _ ≤ (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (|d.V * CommonSmoothCutoff.cutoffMass| * (4 * d.U ^ 2 / D + 2 * d.U) *
          (1 + Real.log d.physicalFactorCap) ^ 19) :=
      mul_le_mul (mediumAdmissible_beta_norm_sq_sum_le hd)
        (transposed_largeModulusZero_norm_le hd Y hD) (norm_nonneg _) (by positivity)
    _ = |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 *
        (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 19 * (8 / D + 4 / d.U) := by
      rw [abs_mul, abs_of_nonneg hV0]
      unfold MediumAtom.scale
      field_simp [hD.ne', hU0.ne']
      ring
    _ ≤ _ := by
      have hh : 8 / D + 4 / d.U ≤ 8 * (1 / D + 1 / d.U) := by
        calc
          8 / D + 4 / d.U ≤ 8 / D + 8 / d.U :=
            add_le_add le_rfl (div_le_div_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 8) hU0.le)
          _ = _ := by ring
      calc
        _ ≤ (|CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 *
            (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
              (1 + Real.log d.physicalFactorCap) ^ 19) * (8 * (1 / D + 1 / d.U)) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring

private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

private theorem log_bound_from_scale {x z : ℝ} (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (hz : 0 < z) (hzx : z ≤ 8 * x) :
    1 + Real.log z ≤ (2 + Real.log 8) * Real.log x := by
  have hh := Real.log_le_log hz hzx
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hx.ne'] at hh
  have hp := mul_nonneg
    (show 0 ≤ 1 + Real.log 8 by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)])
    (show 0 ≤ Real.log x - 1 by linarith)
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]

private theorem actual_log_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d)
    (hlog : 1 ≤ Real.log d.scale) :
    1 + Real.log (2 * d.V) ≤ (2 + Real.log 8) * Real.log d.scale ∧
      1 + Real.log d.physicalFactorCap ≤ (2 + Real.log 8) * Real.log d.scale := by
  have hx1 := one_le_scale hd
  have hx0 : 0 < d.scale := zero_lt_one.trans_le hx1
  have hVx : d.V ≤ d.scale := le_mul_of_one_le_left (by linarith [hd.2.1]) hd.1
  have hcapx : d.physicalFactorCap ≤ 8 * d.scale :=
    (PairedAlphaDeletion.actual_geometry_bounds hd).2.2.trans
      (mul_le_mul_of_nonneg_left (by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
          (show 1 - 10 * sigma ≤ 1 by linarith)) (by norm_num))
  refine ⟨log_bound_from_scale hx0 hlog (by linarith [hd.2.1]) ?_,
    log_bound_from_scale hx0 hlog (zero_lt_one.trans_le (d.one_le_physicalFactorCap hd)) hcapx⟩
  nlinarith

/-- A true arbitrary-log payment for the second masked raw zero.
The one scalar threshold precedes the atom, Y and moving signed residue.
No whole-W or nonzero-frequency budget is assumed in this theorem. -/
theorem betaL2_mul_transposed_largeModulusZero_log_payment
    (B : ℕ) (sigma kappa c0 A delta : ℝ) (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale → ∀ Y : ℝ,
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y (d.scale ^ delta)‖ ≤
            d.scale ^ 2 / Real.log d.scale ^ A := by
  let p : ℕ := (2 ^ B) ^ 2 - 1
  let N : ℕ := p + 19
  let C : ℝ := 2 + Real.log 8
  let E : ℝ := 16 * |CommonSmoothCutoff.cutoffMass| * C ^ N
  let z : ℝ := min sigma delta
  have hz : 0 < z := lt_min hsigma hdelta
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hevent : ∀ᶠ x : ℝ in atTop,
      E * Real.log x ^ (A + (N : ℝ)) ≤ x ^ z := by
    have hb := ((isLittleO_log_rpow_rpow_atTop (A + (N : ℝ)) hz).const_mul_left E).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (by positivity :
      0 ≤ E * Real.log x ^ (A + (N : ℝ))),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using hx
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp hevent
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    fun d hd hx Y ↦ ?_⟩
  have hxScale := one_le_scale hd
  have hx0 : 0 < d.scale := zero_lt_one.trans_le hxScale
  have hU0 : 0 < d.U := zero_lt_one.trans_le hd.1
  have hlog : 1 ≤ Real.log d.scale := hx2 d.scale ((le_max_right x1 x2).trans
    ((le_max_right 2 (max x1 x2)).trans hx))
  have hlog0 : 0 < Real.log d.scale := by linarith
  have hPow : 0 < d.scale ^ z := Real.rpow_pos_of_pos hx0 z
  have hD : 0 < d.scale ^ delta := Real.rpow_pos_of_pos hx0 delta
  have hInv : 1 / d.scale ^ delta + 1 / d.U ≤ 2 / d.scale ^ z := by
    have hzd : d.scale ^ z ≤ d.scale ^ delta :=
      Real.rpow_le_rpow_of_exponent_le hxScale (min_le_right _ _)
    have hzU : d.scale ^ z ≤ d.U :=
      (Real.rpow_le_rpow_of_exponent_le hxScale (min_le_left _ _)).trans
        (PairedAlphaDeletion.actual_geometry_bounds hd).1
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hPow hzd
    have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hPow hzU
    calc
      _ ≤ 1 / d.scale ^ z + 1 / d.scale ^ z := add_le_add h1 h2
      _ = _ := by ring
  let Q : ℝ := C * Real.log d.scale
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    simpa only [one_mul] using mul_le_mul hC hlog zero_le_one (by linarith : 0 ≤ C)
  have hQ0 : 0 ≤ Q := by linarith
  obtain ⟨hV, hcap⟩ := actual_log_bounds hsigma hd hlog
  change 1 + Real.log (2 * d.V) ≤ Q at hV
  change 1 + Real.log d.physicalFactorCap ≤ Q at hcap
  have hV0 : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hcap0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  have hLogs : (1 + Real.log (2 * d.V)) ^ p *
      (1 + Real.log d.physicalFactorCap) ^ 19 ≤ Q ^ p * Q ^ 19 :=
    mul_le_mul (pow_le_pow_left₀ hV0 hV p) (pow_le_pow_left₀ hcap0 hcap 19)
      (pow_nonneg hcap0 _) (pow_nonneg hQ0 _)
  have hPay : E * Real.log d.scale ^ N / d.scale ^ z ≤ 1 / Real.log d.scale ^ A := by
    apply (div_le_div_iff₀ hPow (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ = E * Real.log d.scale ^ (A + (N : ℝ)) := by
        rw [Real.rpow_add hlog0, Real.rpow_natCast]
        ring
      _ ≤ d.scale ^ z := hx1 d.scale ((le_max_left x1 x2).trans
        ((le_max_right 2 (max x1 x2)).trans hx))
      _ = _ := by ring
  have hCoefficient : 0 ≤ 8 * |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 := by positivity
  calc
    _ ≤ 8 * |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 *
        (1 + Real.log (2 * d.V)) ^ p *
          (1 + Real.log d.physicalFactorCap) ^ 19 *
            (1 / d.scale ^ delta + 1 / d.U) :=
      betaL2_mul_transposed_largeModulusZero_le hd Y hD
    _ ≤ (8 * |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2) *
        (Q ^ p * Q ^ 19) * (2 / d.scale ^ z) := by
      apply mul_le_mul _ hInv (by positivity) (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hLogs hCoefficient
    _ = d.scale ^ 2 * (E * Real.log d.scale ^ N / d.scale ^ z) := by
      rw [← pow_add]
      dsimp only [N, Q, E]
      rw [mul_pow]
      ring
    _ ≤ d.scale ^ 2 * (1 / Real.log d.scale ^ A) :=
      mul_le_mul_of_nonneg_left hPay (sq_nonneg _)
    _ = _ := by ring

end TransposedModulusGCDZero

end

end ImbalancedChen.Part3
