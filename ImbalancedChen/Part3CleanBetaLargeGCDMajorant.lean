import ImbalancedChen.Part3CommonSmoothCutoff
import ImbalancedChen.Part3FactorFiberDivisor
import ImbalancedChen.Part3ComplexCRTConsumer

/-!
# Actual beta cleaning and a finite large-gcd divisor majorant

The original beta is not assumed cleaned. The good coefficient removes
exactly the signed divisors of the original residue; the removed beta-pair
part remains an explicit complex exception. The original factor labels,
compatible CRT branches and one common smooth weight are retained.

After taking the norm of the complete complex sum, the original absolute
factor fibers cost tau_3. Divisibility of a nonzero difference then costs
tau_4. A good nonzero beta coefficient proves that its difference cannot
vanish. This finite majorant is not a subpower estimate, logarithmic
payment, estimate for the exception, or cancellation with primitive V/U.

The finite divisor-sum step follows pinned goldbach 09b97db5764ade1246bfb77206baa1b124760958,
LiLiuPrereqFouvryWLargeGCDOriginal.lean:21-49, source SHA256
5e16c36b74ea7e0d712b3b2b2e19fb57c71bbd3396e7fa09ad1aee2066e21008,
compared byte-for-byte with the pinned blob. No unbuilt raw-estimate module
or new analytic supplier is imported.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def MediumAtom.cleanedBeta (d : MediumAtom) (n : ℕ) : ℂ :=
  if (n : ℤ) ∣ d.residue then 0 else d.beta n

def MediumAtom.cleanedBetaAtom (d : MediumAtom) : MediumAtom :=
  { d with beta := d.cleanedBeta }

theorem MediumAtom.cleanedBeta_ne_zero_not_dvd {d : MediumAtom} {n : ℕ}
    (hn : d.cleanedBeta n ≠ 0) : ¬(n : ℤ) ∣ d.residue := by
  intro h
  exact hn (by simp only [MediumAtom.cleanedBeta, if_pos h])

/-- This factor part has no beta coefficient; it retains the literal CRT mask. -/
def MediumAtom.commonFactorPairWeight (d : MediumAtom) (n₁ n₂ : ℕ) : ℂ :=
  ∑ r ∈ d.complexFactorLabels, ∑ s ∈ d.complexFactorLabels,
    d.complexFactorGamma r * star (d.complexFactorGamma s) *
      (ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
        d.residue (complexFactorModulus r) (complexFactorModulus s) n₁ n₂ : ℂ)

theorem MediumAtom.complexDispersionW_commonSmooth_eq_betaPairs
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.complexDispersionW d.commonSmoothCarrier d.commonSmoothWeight : ℂ) =
      ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
        d.beta n₁ * star (d.beta n₂) * d.commonFactorPairWeight n₁ n₂ := by
  rw [MediumAtom.complexDispersionW_eq_constructedCRT hd]
  simp only [MediumAtom.complexRowLabels, Finset.sum_product,
    MediumAtom.complexBetaCoefficient, star_mul]
  simp_rw [Finset.sum_comm (s := d.complexFactorLabels) (t := d.betaCarrier)]
  simp only [MediumAtom.commonFactorPairWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

def MediumAtom.commonLargeBetaGCDW (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then
      d.beta n₁ * star (d.beta n₂) * d.commonFactorPairWeight n₁ n₂ else 0

def MediumAtom.commonSmallBetaGCDW (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then 0 else
      d.beta n₁ * star (d.beta n₂) * d.commonFactorPairWeight n₁ n₂

theorem MediumAtom.complexDispersionW_commonSmooth_eq_large_add_small
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    (d.complexDispersionW d.commonSmoothCarrier d.commonSmoothWeight : ℂ) =
      d.commonLargeBetaGCDW Y + d.commonSmallBetaGCDW Y := by
  rw [d.complexDispersionW_commonSmooth_eq_betaPairs hd]
  unfold MediumAtom.commonLargeBetaGCDW MediumAtom.commonSmallBetaGCDW
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₂ _
  split_ifs <;> simp only [add_zero, zero_add]

/-- The entire original pair survives when at least one beta index divides a. -/
def MediumAtom.commonLargeBetaGCDException (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then
      if (n₁ : ℤ) ∣ d.residue ∨ (n₂ : ℤ) ∣ d.residue then
        d.beta n₁ * star (d.beta n₂) * d.commonFactorPairWeight n₁ n₂ else 0
    else 0

/-- Exact preprocessing, with its unestimated exception still present. -/
theorem MediumAtom.commonLargeBetaGCDW_eq_clean_add_exception (d : MediumAtom) (Y : ℝ) :
    d.commonLargeBetaGCDW Y =
      d.cleanedBetaAtom.commonLargeBetaGCDW Y + d.commonLargeBetaGCDException Y := by
  have hN : d.cleanedBetaAtom.betaCarrier = d.betaCarrier := rfl
  have hF (n₁ n₂ : ℕ) : d.cleanedBetaAtom.commonFactorPairWeight n₁ n₂ =
      d.commonFactorPairWeight n₁ n₂ := rfl
  have hb (n : ℕ) : d.cleanedBetaAtom.beta n = d.cleanedBeta n := rfl
  unfold MediumAtom.commonLargeBetaGCDW MediumAtom.commonLargeBetaGCDException
  simp only [hN, hF, hb]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₂ _
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · by_cases h₁ : (n₁ : ℤ) ∣ d.residue <;>
      by_cases h₂ : (n₂ : ℤ) ∣ d.residue <;>
        simp [hy, h₁, h₂, MediumAtom.cleanedBeta]
  · simp only [if_neg hy, add_zero]

def MediumAtom.absoluteFactorFiber (d : MediumAtom) (q : ℕ) : ℝ :=
  ∑ r ∈ d.physicalFactorFiber q, ‖d.complexFactorGamma r‖

private theorem gamma_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {r : ℕ × ℕ × ℕ}
    (hr : r ∈ d.complexFactorLabels) : ‖d.complexFactorGamma r‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  obtain ⟨hr1, hr23⟩ := Finset.mem_product.mp hr
  obtain ⟨hr2, hr3⟩ := Finset.mem_product.mp hr23
  rw [MediumAtom.complexFactorGamma, norm_mul, norm_mul]
  calc
    ‖d.gamma1 r.1‖ * ‖d.gamma2 r.2.1‖ * ‖d.gamma3 r.2.2‖ ≤ 1 * 1 * 1 :=
      mul_le_mul (mul_le_mul (h1 _ hr1).1 (h2 _ hr2).1 (norm_nonneg _) zero_le_one)
        (h3 _ hr3).1 (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem MediumAtom.absoluteFactorFiber_le_tauThree
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (q : ℕ) :
    d.absoluteFactorFiber q ≤ (fouvryTau 3 q : ℝ) := by
  calc
    _ ≤ ∑ _r ∈ d.physicalFactorFiber q, (1 : ℝ) :=
      Finset.sum_le_sum (fun r hr ↦ gamma_norm_le_one hd (Finset.mem_filter.mp hr).1)
    _ = ((d.physicalFactorFiber q).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast d.card_physicalFactorFiber_le_tauThree hd q

def MediumAtom.absoluteFactorModulusRow (d : MediumAtom) (m n : ℕ) : ℝ :=
  ∑ r ∈ d.complexFactorLabels,
    if Int.ModEq (complexFactorModulus r) ((m : ℤ) * n) d.residue
      then ‖d.complexFactorGamma r‖ else 0

theorem MediumAtom.absoluteFactorModulusRow_nonneg (d : MediumAtom) (m n : ℕ) :
    0 ≤ d.absoluteFactorModulusRow m n := by
  apply Finset.sum_nonneg
  intro r _
  split_ifs <;> positivity

private theorem absoluteFactorModulusRow_eq_fibers (d : MediumAtom) (m n : ℕ) :
    d.absoluteFactorModulusRow m n = ∑ q ∈ d.physicalFactorModuli,
      if Int.ModEq q ((m : ℤ) * n) d.residue then d.absoluteFactorFiber q else 0 := by
  unfold MediumAtom.absoluteFactorModulusRow
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := d.complexFactorLabels) (t := d.physicalFactorModuli)
    (g := complexFactorModulus) (fun r hr ↦ Finset.mem_image_of_mem _ hr)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Int.ModEq q ((m : ℤ) * n) d.residue
  · rw [if_pos hq]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [(Finset.mem_filter.mp hr).2, if_pos hq]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro r hr
    simp only [(Finset.mem_filter.mp hr).2, if_neg hq]

/-- The good coefficient pays the nonzero-difference gate before tau_4 is used. -/
theorem MediumAtom.absoluteFactorModulusRow_le_tauFour
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m n : ℕ)
    (hn : d.cleanedBeta n ≠ 0) :
    d.absoluteFactorModulusRow m n ≤
      (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) := by
  have hne : (m : ℤ) * n - d.residue ≠ 0 := by
    intro h
    exact (d.cleanedBeta_ne_zero_not_dvd hn) ⟨m, by nlinarith⟩
  rw [absoluteFactorModulusRow_eq_fibers]
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli,
        if Int.ModEq q ((m : ℤ) * n) d.residue then (fouvryTau 3 q : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q _
      split_ifs
      · exact d.absoluteFactorFiber_le_tauThree hd q
      · exact le_rfl
    _ = ∑ q ∈ d.physicalFactorModuli.filter
        (fun q ↦ Int.ModEq q ((m : ℤ) * n) d.residue), (fouvryTau 3 q : ℝ) := by
      rw [Finset.sum_filter]
    _ ≤ ∑ q ∈ (((m : ℤ) * n - d.residue).natAbs).divisors,
        (fouvryTau 3 q : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have he := (Finset.mem_filter.mp hq).2
        apply Nat.mem_divisors.mpr
        refine ⟨?_, Int.natAbs_ne_zero.mpr hne⟩
        have hdiv : (q : ℤ) ∣ (m : ℤ) * n - d.residue :=
          Int.modEq_iff_dvd.mp he.symm
        exact_mod_cast Int.natAbs_dvd_natAbs.mpr hdiv
      · intro _ _ _
        positivity
    _ = _ := by rw [show 4 = 3 + 1 from rfl, fouvryTau_succ, Nat.cast_sum]

private theorem constructedWeight_nonneg (d : MediumAtom) (q r n₁ n₂ : ℕ) :
    0 ≤ ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
      d.residue q r n₁ n₂ := by
  unfold ComplexCRT.constructedProgressionWeight
  split_ifs
  · apply Finset.sum_nonneg
    intro m _
    split_ifs
    · exact d.commonSmoothWeight_nonneg m
    · exact le_rfl
  · exact le_rfl

private theorem constructedWeight_le_product (d : MediumAtom) (q r n₁ n₂ : ℕ) :
    ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
      d.residue q r n₁ n₂ ≤
        ComplexCRT.productProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
          d.residue q r n₁ n₂ := by
  unfold ComplexCRT.constructedProgressionWeight ComplexCRT.productProgressionWeight
  by_cases hc : ComplexCRT.Compatible q r n₁ n₂
  · rw [if_pos hc]
    apply le_of_eq
    simp_rw [← (ComplexCRT.residue_spec d.residue hc).2.2]
  · rw [if_neg hc]
    apply Finset.sum_nonneg
    intro m _
    split_ifs
    · exact d.commonSmoothWeight_nonneg m
    · exact le_rfl

/-- The complete complex factor-pair sum is normed before its absolute
modulus rows are introduced. The same smooth weight occurs in both rows. -/
theorem MediumAtom.commonFactorPairWeight_norm_le (d : MediumAtom) (n₁ n₂ : ℕ) :
    ‖d.commonFactorPairWeight n₁ n₂‖ ≤
      ∑ m ∈ d.commonSmoothCarrier, d.commonSmoothWeight m *
        d.absoluteFactorModulusRow m n₁ * d.absoluteFactorModulusRow m n₂ := by
  calc
    _ ≤ ∑ r ∈ d.complexFactorLabels, ∑ s ∈ d.complexFactorLabels,
        ‖d.complexFactorGamma r * star (d.complexFactorGamma s) *
          (ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
            d.residue (complexFactorModulus r) (complexFactorModulus s) n₁ n₂ : ℂ)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun _ _ ↦ norm_sum_le _ _)
    _ ≤ ∑ r ∈ d.complexFactorLabels, ∑ s ∈ d.complexFactorLabels,
        ‖d.complexFactorGamma r‖ * ‖d.complexFactorGamma s‖ *
          ComplexCRT.productProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
            d.residue (complexFactorModulus r) (complexFactorModulus s) n₁ n₂ := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
        abs_of_nonneg (constructedWeight_nonneg d _ _ _ _)]
      exact mul_le_mul_of_nonneg_left (constructedWeight_le_product d _ _ _ _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      unfold ComplexCRT.productProgressionWeight MediumAtom.absoluteFactorModulusRow
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := d.complexFactorLabels) (t := d.commonSmoothCarrier)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      by_cases h₁ : Int.ModEq (complexFactorModulus r) ((m : ℤ) * n₁) d.residue <;>
        by_cases h₂ : Int.ModEq (complexFactorModulus s) ((m : ℤ) * n₂) d.residue <;>
          simp [h₁, h₂, mul_comm, mul_left_comm, mul_assoc]

def MediumAtom.commonLargeBetaGCDDivisorMajorant (d : MediumAtom) (Y : ℝ) : ℝ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then
      ‖d.cleanedBeta n₁‖ * ‖d.cleanedBeta n₂‖ *
        ∑ m ∈ d.commonSmoothCarrier, d.commonSmoothWeight m *
          (fouvryTau 4 (((m : ℤ) * n₁ - d.residue).natAbs) : ℝ) *
            (fouvryTau 4 (((m : ℤ) * n₂ - d.residue).natAbs) : ℝ)
    else 0

/-- Both nonzero-difference gates are proved on the actual good-beta part.
The large-gcd mask and original common support/weight remain unchanged. -/
theorem MediumAtom.commonLargeBetaGCDW_clean_norm_le_divisorMajorant
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    ‖d.cleanedBetaAtom.commonLargeBetaGCDW Y‖ ≤
      d.commonLargeBetaGCDDivisorMajorant Y := by
  have hN : d.cleanedBetaAtom.betaCarrier = d.betaCarrier := rfl
  have hF (n₁ n₂ : ℕ) : d.cleanedBetaAtom.commonFactorPairWeight n₁ n₂ =
      d.commonFactorPairWeight n₁ n₂ := rfl
  have hb (n : ℕ) : d.cleanedBetaAtom.beta n = d.cleanedBeta n := rfl
  unfold MediumAtom.commonLargeBetaGCDW MediumAtom.commonLargeBetaGCDDivisorMajorant
  simp only [hN, hF, hb]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₁ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₂ _
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy]
    rw [norm_mul, norm_mul, norm_star]
    by_cases h₁ : d.cleanedBeta n₁ = 0
    · simp only [h₁, norm_zero, zero_mul]
    by_cases h₂ : d.cleanedBeta n₂ = 0
    · simp only [h₂, norm_zero, mul_zero, zero_mul]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply (d.commonFactorPairWeight_norm_le n₁ n₂).trans
    apply Finset.sum_le_sum
    intro m _
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (d.absoluteFactorModulusRow_le_tauFour hd m n₁ h₁)
        (d.commonSmoothWeight_nonneg m))
      (d.absoluteFactorModulusRow_le_tauFour hd m n₂ h₂)
      (d.absoluteFactorModulusRow_nonneg m n₂)
      (mul_nonneg (d.commonSmoothWeight_nonneg m) (Nat.cast_nonneg _))
  · simp only [if_neg hy, norm_zero, le_refl]

/-- A finite exclusion inequality for the ORIGINAL beta. The signed-divisor
exception is displayed and remains to be estimated in later analytic work. -/
theorem MediumAtom.commonLargeBetaGCDW_norm_le_majorant_add_exception
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    ‖d.commonLargeBetaGCDW Y‖ ≤ d.commonLargeBetaGCDDivisorMajorant Y +
      ‖d.commonLargeBetaGCDException Y‖ := by
  rw [d.commonLargeBetaGCDW_eq_clean_add_exception Y]
  exact (norm_add_le _ _).trans
    (add_le_add_right (d.commonLargeBetaGCDW_clean_norm_le_divisorMajorant hd Y) _)

end

end ImbalancedChen.Part3
