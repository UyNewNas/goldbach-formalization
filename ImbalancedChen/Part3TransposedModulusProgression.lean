import ImbalancedChen.Part3TransposedModulusGCDZero

/-!
# The actual product progression retained by a large physical gcd

This is the finite whole-W step for the same second gcd mask. A genuine
compatibility and actual product progression force the physical gcd to
divide the paired difference. On the off-diagonal it is a divisor of a
nonzero natural absolute difference and retains its own progression in m.

The elementary witness/count argument is a local namespace extraction of
the fixed goldbach WLargeDeltaOriginal source, SHA256
0498ebeecfc1d1ba71d76416864db8777f6213fca9c2a7647161b5adbbfb8c38.
Its unbuilt W chain is not imported. Here the weights, full complex labels,
signed residue and original-V smoothing are the actual local definitions.
No row-cap premise or already-paid whole-W budget is required below.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace TransposedModulusProgression

def LargeModulusWitness (D : ℝ) (a : ℤ) (n₁ n₂ m : ℕ) : Prop :=
  n₁ = n₂ ∨ ∃ delta ∈ ((n₁ : ℤ) - n₂).natAbs.divisors,
    D < (delta : ℝ) ∧ n₁.Coprime delta ∧ Int.ModEq delta ((m : ℤ) * n₁) a

theorem witness_of_compatible {D : ℝ} {a : ℤ} {q r n₁ n₂ m : ℕ}
    (hc : ComplexCRT.Compatible q r n₁ n₂) (hD : D < (q.gcd r : ℝ))
    (hm : Int.ModEq q ((m : ℤ) * n₁) a) :
    LargeModulusWitness D a n₁ n₂ m := by
  by_cases he : n₁ = n₂
  · exact Or.inl he
  · apply Or.inr
    refine ⟨q.gcd r, Nat.mem_divisors.mpr ⟨?_, ?_⟩, hD,
      hc.1.of_dvd_right (Nat.gcd_dvd_left q r), ?_⟩
    · have hd := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hc.2.2.symm)
      exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
    · apply Int.natAbs_ne_zero.mpr
      exact sub_ne_zero.mpr (by exact_mod_cast he)
    · exact hm.of_dvd (by exact_mod_cast Nat.gcd_dvd_left q r)

theorem transposed_sum_weight_product_modEq_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {delta n : ℕ}
    (hdelta : 0 < delta) (hn : n.Coprime delta) (a : ℤ) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      if Int.ModEq delta ((m : ℤ) * n) a then
        d.transposedAtom.commonSmoothWeight m else 0) ≤ 4 * d.V / delta + 1 := by
  have hdeltaR : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hceil : (Nat.ceil (3 * d.V) : ℝ) ≤ 4 * d.V := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ 3 * d.V)
    linarith
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq delta ((m : ℤ) * n) a then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro m _
      split_ifs
      · exact CommonSmoothCutoff.scaledDyadicCutoff_le_one _ _
      · exact le_rfl
    _ = (((Icc 0 (Nat.ceil (3 * d.V))).filter
        (fun m : ℕ ↦ Int.ModEq delta ((m : ℤ) * n) a)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [MediumAtom.commonSmoothCarrier, MediumAtom.transposedAtom]
    _ ≤ ((Nat.ceil (3 * d.V) / delta + 1 : ℕ) : ℝ) := by
      exact_mod_cast PairedAlphaDeletion.card_product_modEq_le (Nat.ceil (3 * d.V)) delta n a hn
    _ ≤ (Nat.ceil (3 * d.V) : ℝ) / delta + 1 := by
      push_cast
      have hh : ((Nat.ceil (3 * d.V) / delta : ℕ) : ℝ) ≤
          (Nat.ceil (3 * d.V) : ℝ) / (delta : ℝ) := Nat.cast_div_le
      exact add_le_add hh le_rfl
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hceil hdeltaR.le) le_rfl

/-- Every off-diagonal witness is paid with its own actual product
progression. The signed residue is unchanged and no zero divisor occurs. -/
theorem transposed_sum_weight_witness_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {D : ℝ} (hD : 0 < D)
    (n₁ n₂ : ℕ) (hne : n₁ ≠ n₂) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      if LargeModulusWitness D d.residue n₁ n₂ m then
        d.transposedAtom.commonSmoothWeight m else 0) ≤
      (4 * d.V / D + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ) := by
  have hV0 : 0 ≤ d.V := by linarith
  let S := ((n₁ : ℤ) - n₂).natAbs.divisors.filter
    (fun delta : ℕ ↦ D < (delta : ℝ) ∧ n₁.Coprime delta)
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier, ∑ delta ∈ S,
        if Int.ModEq delta ((m : ℤ) * n₁) d.residue then
          d.transposedAtom.commonSmoothWeight m else 0 := by
      apply Finset.sum_le_sum
      intro m _
      split_ifs with hw
      · obtain ⟨delta, hdelta, hDdelta, hndelta, hmdelta⟩ := hw.resolve_left hne
        have hs := Finset.single_le_sum (s := S)
          (f := fun delta : ℕ ↦
            if Int.ModEq delta ((m : ℤ) * n₁) d.residue then
              d.transposedAtom.commonSmoothWeight m else 0)
          (fun e _ ↦ by split_ifs <;>
            first | exact le_rfl | exact d.transposedAtom.commonSmoothWeight_nonneg m)
          (Finset.mem_filter.mpr ⟨hdelta, hDdelta, hndelta⟩)
        simpa only [if_pos hmdelta] using hs
      · exact Finset.sum_nonneg (fun delta _ ↦ by
          split_ifs <;> first | exact le_rfl | exact d.transposedAtom.commonSmoothWeight_nonneg m)
    _ = ∑ delta ∈ S, ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq delta ((m : ℤ) * n₁) d.residue then
          d.transposedAtom.commonSmoothWeight m else 0 := Finset.sum_comm
    _ ≤ ∑ _delta ∈ S, (4 * d.V / D + 1) := by
      apply Finset.sum_le_sum
      intro delta hdelta
      obtain ⟨_, hDdelta, hndelta⟩ := Finset.mem_filter.mp hdelta
      have hdeltaR : (0 : ℝ) < delta := hD.trans hDdelta
      exact (transposed_sum_weight_product_modEq_le hV (by exact_mod_cast hdeltaR)
        hndelta d.residue).trans
          (add_le_add (div_le_div_of_nonneg_left (by linarith : 0 ≤ 4 * d.V)
            hD hDdelta.le) le_rfl)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm, fouvryTau_two]
      exact mul_le_mul_of_nonneg_left
        (show (S.card : ℝ) ≤ (((n₁ : ℤ) - n₂).natAbs.divisors.card : ℝ) by
          exact_mod_cast Finset.card_filter_le _ _)
        (by positivity)

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

/-- The existence witness is kept before the two physical modulus rows
are enlarged independently. -/
private theorem constructedLargeWeight_le_witness (d : MediumAtom) (D : ℝ)
    (q r n₁ n₂ : ℕ) :
    (if D < (q.gcd r : ℝ) then
      ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
        d.residue q r n₁ n₂ else 0) ≤
      ∑ m ∈ d.commonSmoothCarrier,
        if Int.ModEq q ((m : ℤ) * n₁) d.residue ∧
            Int.ModEq r ((m : ℤ) * n₂) d.residue then
          d.commonSmoothWeight m *
            (if LargeModulusWitness D d.residue n₁ n₂ m then 1 else 0) else 0 := by
  have hrhs : 0 ≤ ∑ m ∈ d.commonSmoothCarrier,
      if Int.ModEq q ((m : ℤ) * n₁) d.residue ∧
          Int.ModEq r ((m : ℤ) * n₂) d.residue then
        d.commonSmoothWeight m *
          (if LargeModulusWitness D d.residue n₁ n₂ m then 1 else 0) else 0 := by
    apply Finset.sum_nonneg
    intro m _
    split_ifs <;> simp [d.commonSmoothWeight_nonneg]
  by_cases hD : D < (q.gcd r : ℝ)
  · rw [if_pos hD]
    unfold ComplexCRT.constructedProgressionWeight
    by_cases hc : ComplexCRT.Compatible q r n₁ n₂
    · rw [if_pos hc]
      apply le_of_eq
      simp_rw [← (ComplexCRT.residue_spec d.residue hc).2.2]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : Int.ModEq q ((m : ℤ) * n₁) d.residue ∧
          Int.ModEq r ((m : ℤ) * n₂) d.residue
      · simp only [if_pos hm, if_pos (witness_of_compatible hc hD hm.1), mul_one]
      · simp only [if_neg hm]
    · simpa only [if_neg hc] using hrhs
  · simpa only [if_neg hD] using hrhs

/-- A whole norm of the literal full complex factor labels is bounded
by the actual two absolute rows, with the large-gcd progression witness
still present. No one-bound is asserted for grouped Gamma. -/
theorem commonLargeModulusWeight_norm_le_witness (d : MediumAtom) (D : ℝ) (n₁ n₂ : ℕ) :
    ‖d.commonLargeModulusGCDWeight D n₁ n₂‖ ≤
      ∑ m ∈ d.commonSmoothCarrier, d.commonSmoothWeight m *
        d.absoluteFactorModulusRow m n₁ * d.absoluteFactorModulusRow m n₂ *
          (if LargeModulusWitness D d.residue n₁ n₂ m then 1 else 0) := by
  unfold MediumAtom.commonLargeModulusGCDWeight
  calc
    _ ≤ ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
        ‖d.complexFactorGamma a‖ * ‖d.complexFactorGamma b‖ *
          (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then
            ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
              d.residue (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ else 0) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      by_cases hD : D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ)
      · simp only [if_pos hD, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (constructedWeight_nonneg d _ _ _ _), le_refl]
      · simp only [if_neg hD, mul_zero, norm_zero, le_refl]
    _ ≤ ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
        ‖d.complexFactorGamma a‖ * ‖d.complexFactorGamma b‖ *
          ∑ m ∈ d.commonSmoothCarrier,
            if Int.ModEq (complexFactorModulus a) ((m : ℤ) * n₁) d.residue ∧
                Int.ModEq (complexFactorModulus b) ((m : ℤ) * n₂) d.residue then
              d.commonSmoothWeight m *
                (if LargeModulusWitness D d.residue n₁ n₂ m then 1 else 0) else 0 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (constructedLargeWeight_le_witness d D _ _ n₁ n₂)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      unfold MediumAtom.absoluteFactorModulusRow
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := d.complexFactorLabels) (t := d.commonSmoothCarrier)]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp_all
      all_goals ring

/-- Actual whole W under both masks, with every paired coefficient and
every required progression retained. This finite majorant has no
analytical row-cap premise. -/
theorem transposed_smallBeta_largeModulusW_norm_le_witness
    (d : MediumAtom) (Y D : ℝ) :
    ‖d.transposedAtom.commonSmallBetaLargeModulusGCDW Y D‖ ≤
      ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
        if Y < (n₁.gcd n₂ : ℝ) then 0 else
          ‖d.transposedAtom.beta n₁‖ * ‖d.transposedAtom.beta n₂‖ *
            ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
              d.transposedAtom.commonSmoothWeight m *
                d.transposedAtom.absoluteFactorModulusRow m n₁ *
                  d.transposedAtom.absoluteFactorModulusRow m n₂ *
                    (if LargeModulusWitness D d.residue n₁ n₂ m then 1 else 0) := by
  unfold MediumAtom.commonSmallBetaLargeModulusGCDW
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₁ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₂ _
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy, norm_zero, le_refl]
  · simp only [if_neg hy, norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left
      (commonLargeModulusWeight_norm_le_witness d.transposedAtom D n₁ n₂)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private def unitBetaAtom (d : MediumAtom) : MediumAtom :=
  { d with beta := fun _ ↦ 1 }

private theorem unitBetaAtom_admissible
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    MediumAdmissible 0 sigma kappa c0 (unitBetaAtom d) := by
  obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, _hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, ?_, hGamma1, hGamma2, hGamma3⟩
  intro n _
  change ‖(1 : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 0
  norm_num

/-- The absolute modulus row has no beta argument. A genuine original
geometry atom with beta=1 exposes its existing nonzero-difference bound. -/
private theorem absoluteRow_le_tauFour_of_not_dvd
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m n : ℕ)
    (hn : ¬(n : ℤ) ∣ d.residue) :
    d.absoluteFactorModulusRow m n ≤
      (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) := by
  have hgood : (unitBetaAtom d).cleanedBeta n ≠ 0 := by
    change (if (n : ℤ) ∣ d.residue then (0 : ℂ) else 1) ≠ 0
    simp only [if_neg hn, one_ne_zero]
  exact (unitBetaAtom d).absoluteFactorModulusRow_le_tauFour
    (unitBetaAtom_admissible hd) m n hgood

private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

private theorem actual_difference_le_polynomial
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {m n : ℕ}
    (hn : n ∈ d.transposedAtom.betaCarrier)
    (hm : d.transposedAtom.commonSmoothWeight m ≠ 0) :
    (((m : ℤ) * n - d.residue).natAbs : ℝ) ≤
      7 * d.scale ^ (max 1 (1 + kappa)) := by
  have hx := one_le_scale hd
  obtain ⟨hU, hV, _, _, _, _, _, ha, _⟩ := hd
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (le_max_left (1 : ℝ) (1 + kappa))
  have haK : |(d.residue : ℝ)| ≤ d.scale ^ (max 1 (1 + kappa)) := by
    have ha' : |(d.residue : ℝ)| ≤ d.scale ^ (1 + kappa) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using ha
    exact ha'.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  have hms : (m : ℝ) ∈ tsupport (CommonSmoothCutoff.scaledDyadicCutoff d.V) :=
    subset_closure hm
  have hmhi := (CommonSmoothCutoff.scaledDyadicCutoff_tsupport_subset
    (lt_of_lt_of_le zero_lt_one hV) hms).2
  have hnhi : (n : ℝ) ≤ 2 * d.U :=
    (show (n : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
      exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
        (Nat.floor_le (by linarith : 0 ≤ 2 * d.U))
  have hmn : (m : ℝ) * n ≤ 6 * d.scale := by
    calc
      _ ≤ (3 * d.V) * (2 * d.U) :=
        mul_le_mul hmhi hnhi (Nat.cast_nonneg _) (by linarith)
      _ = _ := by unfold MediumAtom.scale; ring
  calc
    _ = |(m : ℝ) * n - d.residue| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rfl
    _ ≤ |(m : ℝ) * n| + |(d.residue : ℝ)| := abs_sub _ _
    _ ≤ 6 * d.scale + d.scale ^ (max 1 (1 + kappa)) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * n)]
      exact add_le_add hmn haK
    _ ≤ _ := by linarith

private theorem tauFour_difference_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ m n : ℕ,
        n ∈ d.transposedAtom.betaCarrier → d.transposedAtom.commonSmoothWeight m ≠ 0 →
          ¬(n : ℤ) ∣ d.residue →
            (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) ≤
              C * d.scale ^ (epsilon / 2) := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let eta : ℝ := epsilon / (2 * K)
  have heta : 0 < eta := div_pos hepsilon (mul_pos (by norm_num) hKpos)
  have hKeta : K * eta = epsilon / 2 := by dsimp [eta]; field_simp [hKpos.ne']
  obtain ⟨D, hD, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 4) (by norm_num) heta
  refine ⟨D * (7 : ℝ) ^ eta, by positivity, fun B sigma c0 d hd m n hn hm hndiv ↦ ?_⟩
  have hne : (m : ℤ) * n - d.residue ≠ 0 := by
    intro h
    exact hndiv ⟨m, by nlinarith⟩
  have hx := one_le_scale hd
  calc
    _ ≤ D * (((m : ℤ) * n - d.residue).natAbs : ℝ) ^ eta :=
      hbound _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
    _ ≤ D * (7 * d.scale ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (actual_difference_le_polynomial hd hn hm) heta.le) hD.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) (Real.rpow_nonneg (by linarith) _),
        ← Real.rpow_mul (by linarith : 0 ≤ d.scale), hKeta]
      ring

private theorem transposed_smoothWeight_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier, d.transposedAtom.commonSmoothWeight m) ≤
      5 * d.V := by
  calc
    _ ≤ ∑ _m ∈ d.transposedAtom.commonSmoothCarrier, (1 : ℝ) :=
      Finset.sum_le_sum (fun _ _ ↦ CommonSmoothCutoff.scaledDyadicCutoff_le_one _ _)
    _ = (Nat.ceil (3 * d.V) : ℝ) + 1 := by
      simp [MediumAtom.commonSmoothCarrier, MediumAtom.transposedAtom]
    _ ≤ _ := by
      have := Nat.ceil_lt_add_one (by linarith [hd.2.1] : 0 ≤ 3 * d.V)
      linarith [hd.2.1]

/-- Genuine original geometry and a nondivisor paired index pay both
actual modulus rows on their real support. The progression witness is
kept when the rows are bounded and the actual cutoff is counted. -/
theorem transposed_largeModulusWeight_divisor_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ D : ℝ, 0 < D → ∀ n₁ n₂ : ℕ,
        n₁ ∈ d.transposedAtom.betaCarrier → n₂ ∈ d.transposedAtom.betaCarrier →
          ¬(n₁ : ℤ) ∣ d.residue → ¬(n₂ : ℤ) ∣ d.residue →
            ‖d.transposedAtom.commonLargeModulusGCDWeight D n₁ n₂‖ ≤
              C * d.scale ^ epsilon *
                (if n₁ = n₂ then 5 * d.V else
                  (4 * d.V / D + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := tauFour_difference_subpower kappa hepsilon
  refine ⟨C ^ 2, by positivity, fun B sigma c0 d hd D hD n₁ n₂ hn₁ hn₂ hnd₁ hnd₂ ↦ ?_⟩
  have hx0 : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier, d.transposedAtom.commonSmoothWeight m *
        d.transposedAtom.absoluteFactorModulusRow m n₁ *
          d.transposedAtom.absoluteFactorModulusRow m n₂ *
            (if LargeModulusWitness D d.residue n₁ n₂ m then 1 else 0) :=
      commonLargeModulusWeight_norm_le_witness d.transposedAtom D n₁ n₂
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        (C ^ 2 * d.scale ^ epsilon) *
          (if LargeModulusWitness D d.residue n₁ n₂ m then
            d.transposedAtom.commonSmoothWeight m else 0) := by
      apply Finset.sum_le_sum
      intro m _
      by_cases hw : LargeModulusWitness D d.residue n₁ n₂ m
      · simp only [if_pos hw, mul_one]
        by_cases hm : d.transposedAtom.commonSmoothWeight m = 0
        · simp only [hm, zero_mul, mul_zero, le_refl]
        · have hrow₁ := (absoluteRow_le_tauFour_of_not_dvd hd m n₁ hnd₁).trans
            (hbound B sigma c0 d hd m n₁ hn₁ hm hnd₁)
          have hrow₂ := (absoluteRow_le_tauFour_of_not_dvd hd m n₂ hnd₂).trans
            (hbound B sigma c0 d hd m n₂ hn₂ hm hnd₂)
          have hp : d.absoluteFactorModulusRow m n₁ * d.absoluteFactorModulusRow m n₂ ≤
              C ^ 2 * d.scale ^ epsilon := by
            calc
              _ ≤ (C * d.scale ^ (epsilon / 2)) * (C * d.scale ^ (epsilon / 2)) :=
                mul_le_mul hrow₁ hrow₂ (d.absoluteFactorModulusRow_nonneg m n₂) (by positivity)
              _ = _ := by
                rw [mul_mul_mul_comm, ← Real.rpow_add hx0,
                  show epsilon / 2 + epsilon / 2 = epsilon by ring, pow_two]
          change d.transposedAtom.commonSmoothWeight m *
            d.absoluteFactorModulusRow m n₁ * d.absoluteFactorModulusRow m n₂ ≤ _
          calc
            _ = d.transposedAtom.commonSmoothWeight m *
                (d.absoluteFactorModulusRow m n₁ * d.absoluteFactorModulusRow m n₂) := by ring
            _ ≤ d.transposedAtom.commonSmoothWeight m * (C ^ 2 * d.scale ^ epsilon) :=
              mul_le_mul_of_nonneg_left hp (d.transposedAtom.commonSmoothWeight_nonneg m)
            _ = _ := by ring
      · simp only [if_neg hw, mul_zero, le_refl]
    _ = (C ^ 2 * d.scale ^ epsilon) *
        ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
          if LargeModulusWitness D d.residue n₁ n₂ m then
            d.transposedAtom.commonSmoothWeight m else 0 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases he : n₁ = n₂
      · simpa only [LargeModulusWitness, he, true_or, if_true] using transposed_smoothWeight_sum_le hd
      · simpa only [if_neg he] using transposed_sum_weight_witness_le hd.2.1 hD n₁ n₂ he

/-- The real alpha-clean support supplies both nondivisor conditions.
The diagonal and actual off-diagonal difference cost are kept separately;
this is a concrete whole-W estimate with no supplied row-cap premise. -/
theorem cleanedAlpha_transposed_smallBeta_largeModulusW_divisor_bound
    (kappa : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D : ℝ, 0 < D →
        ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDW Y D‖ ≤
          C * d.scale ^ epsilon *
            ∑ n₁ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
              ∑ n₂ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
                if Y < (n₁.gcd n₂ : ℝ) then 0 else
                  ‖d.cleanedAlphaAtom.transposedAtom.beta n₁‖ *
                    ‖d.cleanedAlphaAtom.transposedAtom.beta n₂‖ *
                      (if n₁ = n₂ then 5 * d.V else
                        (4 * d.V / D + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := transposed_largeModulusWeight_divisor_bound kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y D hD ↦ ?_⟩
  have hclean := mediumAdmissible_cleanedAlphaAtom hd
  unfold MediumAtom.commonSmallBetaLargeModulusGCDW
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₁ hn₁
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₂ hn₂
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy, norm_zero, mul_zero, le_refl]
  · simp only [if_neg hy, norm_mul, norm_star]
    by_cases h1 : d.cleanedAlphaAtom.transposedAtom.beta n₁ = 0
    · simp only [h1, norm_zero, zero_mul, mul_zero, le_refl]
    by_cases h2 : d.cleanedAlphaAtom.transposedAtom.beta n₂ = 0
    · simp only [h2, norm_zero, mul_zero, zero_mul, le_refl]
    calc
      _ ≤ (‖d.cleanedAlphaAtom.transposedAtom.beta n₁‖ *
          ‖d.cleanedAlphaAtom.transposedAtom.beta n₂‖) *
            (C * d.scale ^ epsilon * (if n₁ = n₂ then 5 * d.V else
              (4 * d.V / D + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (hbound B sigma c0 d.cleanedAlphaAtom hclean D hD n₁ n₂ hn₁ hn₂
            (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h1)
            (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h2))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring

/-- The actual same-mask raw zero is already paid. The remaining
quantity is this explicit whole-W progression majorant, with the
original outside beta-L2, not a presumed Fourier or energy budget. -/
theorem betaL2_mul_largeModulusNonzero_le_witness_add_log_payment
    (B : ℕ) (sigma kappa c0 A delta : ℝ) (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale → ∀ Y : ℝ,
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y (d.scale ^ delta) true‖ ≤
            (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
              (∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
                if Y < (n₁.gcd n₂ : ℝ) then 0 else
                  ‖d.transposedAtom.beta n₁‖ * ‖d.transposedAtom.beta n₂‖ *
                    ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
                      d.transposedAtom.commonSmoothWeight m *
                        d.transposedAtom.absoluteFactorModulusRow m n₁ *
                          d.transposedAtom.absoluteFactorModulusRow m n₂ *
                            (if LargeModulusWitness (d.scale ^ delta) d.residue n₁ n₂ m
                              then 1 else 0)) +
              d.scale ^ 2 / Real.log d.scale ^ A := by
  obtain ⟨x0, hx0, hzero⟩ :=
    TransposedModulusGCDZero.betaL2_mul_transposed_largeModulusZero_log_payment
      B sigma kappa c0 A delta hsigma hdelta
  refine ⟨x0, hx0, fun d hd hx Y ↦ ?_⟩
  have hbeta : 0 ≤ ∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  apply (mul_le_mul_of_nonneg_left
    (TransposedModulusGCDZero.transposed_largeModulusNonzero_norm_le_W_add_zero
      hd Y (d.scale ^ delta)) hbeta).trans
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (transposed_smallBeta_largeModulusW_norm_le_witness d Y (d.scale ^ delta)) hbeta)
    (hzero d hd hx Y)

end TransposedModulusProgression

end

end ImbalancedChen.Part3
