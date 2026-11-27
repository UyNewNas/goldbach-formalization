import ImbalancedChen.Part3SharedFirstFactorSmallPairedSupportedReduction

/-!
# Row-adaptive truncation of the actual small supported nonzero core

The Fourier window is attached to the exact physical lcm of each row.
The elementary shifted Poisson majorant retains both frequency signs and
its reciprocal endpoint. All actual complex coefficients and CRT labels
are kept before taking norms. The final payment includes the original
beta/gamma1 outside moments exactly once. No spectral cancellation is
asserted by this truncation result.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter Topology
open scoped BigOperators SchwartzMap FourierTransform
open CommonSmoothCutoff TransposedPrimitiveUPayment

def CommonSmoothCutoff.poissonNonzeroFrequencyWindow (H : ℕ) : Finset ℤ :=
  ((Finset.Icc 1 H).image (fun n : ℕ => (n : ℤ))) ∪
    ((Finset.Icc 1 H).image (fun n : ℕ => -(n : ℤ)))

def CommonSmoothCutoff.poissonFrequencyCutoff (Z M : ℝ) (L : ℕ) : ℕ :=
  Nat.ceil (Z * (L : ℝ) / M)

def MediumAtom.commonFactorPairNonzeroWeightTruncated (d : MediumAtom)
    (Z : ℝ) (n₁ n₂ : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
        (∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
            (CommonSmoothCutoff.poissonFrequencyCutoff Z d.U
              ((complexFactorModulus a).lcm (complexFactorModulus b))),
          CommonSmoothCutoff.poissonNonzeroFrequency
            (d.U / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ))
            ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
              n₁ n₂ d.residue : ℝ) /
                ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ)) h).re
      else 0 : ℝ)

def MediumAtom.sharedSmallPairedSmallSupportedNonzeroTruncated (d : MediumAtom)
    (Ybeta Ysupport Z : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ N1 ∈ d.transposedAtom.betaCarrier, ∑ N2 ∈ d.transposedAtom.betaCarrier,
      if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
          (CanonicalReciprocalData.supportedPart
            (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
        d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
          (d.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeightTruncated Z N1 N2
      else 0


namespace SharedFirstFactorSmallCoreFourierTruncation

private theorem mem_window_iff (H : ℕ) (h : ℤ) :
    h ∈ poissonNonzeroFrequencyWindow H ↔ h ≠ 0 ∧ h.natAbs ≤ H := by
  unfold poissonNonzeroFrequencyWindow
  rw [Finset.mem_union]
  constructor
  · rintro (hp | hnegImage)
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      exact ⟨by exact_mod_cast hn0, by simpa using (Finset.mem_Icc.mp hn).2⟩
    · obtain ⟨n, hnMem, rfl⟩ := Finset.mem_image.mp hnegImage
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hnMem).1; omega
      exact ⟨neg_ne_zero.mpr (by exact_mod_cast hn0), by simpa using (Finset.mem_Icc.mp hnMem).2⟩
  · rintro ⟨hne, hH⟩
    have hn : 1 ≤ h.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
    rcases le_total 0 h with hp | hm
    · left
      apply Finset.mem_image.mpr
      refine ⟨h.natAbs, Finset.mem_Icc.mpr ⟨hn, hH⟩, ?_⟩
      rw [Int.natCast_natAbs, abs_of_nonneg hp]
    · right
      apply Finset.mem_image.mpr
      refine ⟨h.natAbs, Finset.mem_Icc.mpr ⟨hn, hH⟩, ?_⟩
      rw [Int.natCast_natAbs, abs_of_nonpos hm, neg_neg]

private theorem shifted_decay_two {t : ℝ} (ht : 0 < t) (H : ℕ) :
    Summable (fun n : ℕ => t / (1 + t * ((H : ℝ) + n + 1)) ^ 2) ∧
      (∑' n : ℕ, t / (1 + t * ((H : ℝ) + n + 1)) ^ 2) ≤
        1 / (1 + t * H) := by
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range N, t / (1 + t * ((H : ℝ) + n + 1)) ^ 2) ≤
        1 / (1 + t * H) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          (1 / (1 + t * ((H : ℝ) + n)) -
            1 / (1 + t * ((H : ℝ) + n + 1))) := by
        apply Finset.sum_le_sum
        intro n _
        simpa only [Nat.cast_add] using poisson_decay_step ht (H + n)
      _ = 1 / (1 + t * H) - 1 / (1 + t * ((H : ℝ) + N)) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, add_assoc]
          using Finset.sum_range_sub'
            (fun n : ℕ => 1 / (1 + t * ((H : ℝ) + n))) N
      _ ≤ _ := sub_le_self _ (by positivity)
  exact ⟨summable_of_sum_range_le (fun _ => by positivity) hfinite,
    Real.tsum_le_of_sum_range_le (fun _ => by positivity) hfinite⟩

private theorem shifted_decay_order (r : ℕ) (hr : 2 ≤ r)
    {t : ℝ} (ht : 0 < t) (H : ℕ) :
    Summable (fun n : ℕ => t / (1 + t * ((H : ℝ) + n + 1)) ^ r) ∧
      (∑' n : ℕ, t / (1 + t * ((H : ℝ) + n + 1)) ^ r) ≤
        1 / (1 + t * H) ^ (r - 1) := by
  obtain ⟨hs, hb⟩ := shifted_decay_two ht H
  let A : ℝ := 1 + t * H
  have hA : 0 < A := by dsimp [A]; positivity
  have hpoint (n : ℕ) :
      t / (1 + t * ((H : ℝ) + n + 1)) ^ r ≤
        (1 / A ^ (r - 2)) * (t / (1 + t * ((H : ℝ) + n + 1)) ^ 2) := by
    let B : ℝ := 1 + t * ((H : ℝ) + n + 1)
    have hB : 0 < B := by dsimp [B]; positivity
    have hAB : A ≤ B := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      dsimp [A, B]
      nlinarith
    have hp : A ^ (r - 2) * B ^ 2 ≤ B ^ r := by
      calc
        _ ≤ B ^ (r - 2) * B ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA.le hAB _) (sq_nonneg B)
        _ = B ^ r := by
          rw [← pow_add, show (r - 2) + 2 = r by omega]
    calc
      _ ≤ t / (A ^ (r - 2) * B ^ 2) :=
        div_le_div_of_nonneg_left ht.le (by positivity) hp
      _ = _ := by dsimp [B]; field_simp [hA.ne', hB.ne']
  have hmajor : Summable (fun n : ℕ =>
      (1 / A ^ (r - 2)) * (t / (1 + t * ((H : ℝ) + n + 1)) ^ 2)) :=
    hs.mul_left _
  have hsmall : Summable (fun n : ℕ =>
      t / (1 + t * ((H : ℝ) + n + 1)) ^ r) :=
    hmajor.of_nonneg_of_le (fun _ => by positivity) hpoint
  refine ⟨hsmall, ?_⟩
  calc
    _ ≤ ∑' n : ℕ,
        (1 / A ^ (r - 2)) * (t / (1 + t * ((H : ℝ) + n + 1)) ^ 2) :=
      hsmall.tsum_le_tsum hpoint hmajor
    _ = (1 / A ^ (r - 2)) *
        (∑' n : ℕ, t / (1 + t * ((H : ℝ) + n + 1)) ^ 2) := tsum_mul_left
    _ ≤ (1 / A ^ (r - 2)) * (1 / A) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      change (1 / A ^ (r - 2)) * (1 / A) = 1 / A ^ (r - 1)
      rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
      field_simp [hA.ne']

private theorem signed_decay_tail (r : ℕ) (hr : 2 ≤ r)
    {t : ℝ} (ht : 0 < t) (H : ℕ) :
    Summable (fun h : ℤ => if H < h.natAbs then t / (1 + |t * h|) ^ r else 0) ∧
      (∑' h : ℤ, if H < h.natAbs then t / (1 + |t * h|) ^ r else 0) ≤
        2 / (1 + t * H) ^ (r - 1) := by
  let a : ℕ → ℝ := fun n => if H < n then t / (1 + t * n) ^ r else 0
  let D : ℤ → ℝ := fun h => if H < h.natAbs then t / (1 + |t * h|) ^ r else 0
  obtain ⟨hs, hb⟩ := shifted_decay_order r hr ht H
  have hshift (n : ℕ) : a (n + (H + 1)) =
      t / (1 + t * ((H : ℝ) + n + 1)) ^ r := by
    have hn : H < n + (H + 1) := by omega
    simp [a, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
  have has : Summable (fun n : ℕ => a (n + (H + 1))) :=
    hs.congr (fun n => (hshift n).symm)
  have ha : Summable a := (summable_nat_add_iff (H + 1)).mp has
  have hprefix : (∑ n ∈ Finset.range (H + 1), a n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnot : ¬H < n := by have := Finset.mem_range.mp hn; omega
    simp only [a, if_neg hnot]
  have hsum : (∑' n : ℕ, a n) =
      ∑' n : ℕ, t / (1 + t * ((H : ℝ) + n + 1)) ^ r := by
    have he := Summable.sum_add_tsum_nat_add (H + 1) ha
    rw [hprefix, zero_add] at he
    exact he.symm.trans (tsum_congr hshift)
  have hbound : (∑' n : ℕ, a n) ≤ 1 / (1 + t * H) ^ (r - 1) := by
    rw [hsum]
    exact hb
  have hnat (n : ℕ) : D (n : ℤ) = a n := by
    simp [D, a, abs_mul, abs_of_pos ht,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hneg (n : ℕ) : D (-((n : ℤ) + 1)) = a (n + 1) := by
    have he : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by simp
    rw [he]
    simpa only [D, Int.natAbs_neg, Int.cast_neg, mul_neg, abs_neg] using hnat (n + 1)
  have hpos : Summable (fun n : ℕ => D (n : ℤ)) :=
    ha.congr (fun n => (hnat n).symm)
  have hanext : Summable (fun n : ℕ => a (n + 1)) := (summable_nat_add_iff 1).mpr ha
  have hminus : Summable (fun n : ℕ => D (-((n : ℤ) + 1))) :=
    hanext.congr (fun n => (hneg n).symm)
  have hzero : a 0 = 0 := by simp [a]
  have hnext : (∑' n : ℕ, a (n + 1)) = ∑' n : ℕ, a n := by
    have he := Summable.sum_add_tsum_nat_add 1 ha
    simpa only [Finset.sum_range_one, hzero, zero_add] using he
  refine ⟨hpos.of_nat_of_neg_add_one hminus, ?_⟩
  change (∑' h : ℤ, D h) ≤ _
  calc
    _ = (∑' n : ℕ, a n) + ∑' n : ℕ, a (n + 1) := by
      rw [tsum_of_nat_of_neg_add_one hpos hminus]
      congr 1
      · exact tsum_congr hnat
      · exact tsum_congr hneg
    _ = 2 * ∑' n : ℕ, a n := by rw [hnext]; ring
    _ ≤ 2 * (1 / (1 + t * H) ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

private theorem poissonNonzeroFrequency_row_tail
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x Z : ℝ, 0 < Z →
      ‖(∑' h : ℤ, CommonSmoothCutoff.poissonNonzeroFrequency t x h) -
        ∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow (Nat.ceil (Z / t)),
          CommonSmoothCutoff.poissonNonzeroFrequency t x h‖ ≤ C / Z ^ (r - 1) := by
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) r
  refine ⟨2 * C, by positivity, fun t ht x Z hZ => ?_⟩
  let H : ℕ := Nat.ceil (Z / t)
  let W : Finset ℤ := poissonNonzeroFrequencyWindow H
  let f : ℤ → ℂ := poissonNonzeroFrequency t x
  let g : ℤ → ℂ := fun h => if h ∈ W then f h else 0
  let D : ℤ → ℝ := fun h => if H < h.natAbs then t / (1 + |t * h|) ^ r else 0
  have hH : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.ceil_pos.mpr (div_pos hZ ht)))
  have hZH : Z ≤ t * H := by
    have hh : Z / t ≤ (H : ℝ) := Nat.le_ceil (Z / t)
    have he := (div_le_iff₀ ht).mp hh
    nlinarith
  obtain ⟨hDs, hDb⟩ := signed_decay_tail r hr ht H
  have hf : Summable f := (poissonNonzeroFrequency_summable_norm ht x).of_norm
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := W)
    intro h hh
    simp only [g, if_neg hh]
  have hsumg : (∑' h : ℤ, g h) = ∑ h ∈ W, f h := by
    calc
      _ = ∑ h ∈ W, g h := tsum_eq_sum (fun h hh => by simp only [g, if_neg hh])
      _ = _ := Finset.sum_congr rfl (fun h hh => by simp only [g, if_pos hh])
  have hpoint (h : ℤ) : ‖f h - g h‖ ≤ C * D h := by
    by_cases hh : h ∈ W
    · simp only [g, if_pos hh, sub_self, norm_zero]
      dsimp only [D]
      split_ifs <;> positivity
    · by_cases hz : h = 0
      · subst h
        simp [f, g, D, poissonNonzeroFrequency]
      · have hgt : H < h.natAbs := by
          apply Nat.lt_of_not_ge
          intro hle
          exact hh ((mem_window_iff H h).mpr ⟨hz, hle⟩)
        simp only [g, if_neg hh, sub_zero, D, if_pos hgt]
        dsimp only [f]
        simp only [poissonNonzeroFrequency, if_neg hz, norm_mul, norm_smul,
          Real.norm_eq_abs, abs_of_pos ht, fourier_apply, Circle.norm_coe, mul_one]
        calc
          _ ≤ t * (C / (1 + |t * h|) ^ r) :=
            mul_le_mul_of_nonneg_left (hdecay (t * h)) ht.le
          _ = _ := by ring
  have hmajor : Summable (fun h : ℤ => C * D h) := hDs.mul_left C
  have hnorm : Summable (fun h : ℤ => ‖f h - g h‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have hA : 0 < 1 + t * (H : ℝ) := by
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  have hZA : Z ≤ 1 + t * (H : ℝ) := by linarith
  change ‖(∑' h : ℤ, f h) - ∑ h ∈ W, f h‖ ≤ _
  rw [← hsumg, ← hf.tsum_sub hg]
  calc
    _ ≤ ∑' h : ℤ, ‖f h - g h‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' h : ℤ, C * D h := hnorm.tsum_le_tsum hpoint hmajor
    _ = C * ∑' h : ℤ, D h := tsum_mul_left
    _ ≤ C * (2 / (1 + t * H) ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hDb hC.le
    _ = (2 * C) / (1 + t * H) ^ (r - 1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (pow_pos hZ _) (pow_le_pow_left₀ hZ.le hZA _)

private theorem norm_sum_sub_le_card {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    (E : ℝ) (h : ∀ i ∈ S, ‖f i - g i‖ ≤ E) :
    ‖(∑ i ∈ S, f i) - ∑ i ∈ S, g i‖ ≤ (S.card : ℝ) * E := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, ‖f i - g i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, E := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

private theorem coeff_real_tail_norm_le (a b z w : ℂ) (E : ℝ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (_hE : 0 ≤ E) (hzw : ‖z - w‖ ≤ E) :
    ‖a * star b * (z.re : ℂ) - a * star b * (w.re : ℂ)‖ ≤ E := by
  rw [← mul_sub, ← Complex.ofReal_sub, ← Complex.sub_re,
    norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (1 * 1) * E := mul_le_mul
      (mul_le_mul ha hb (norm_nonneg _) zero_le_one)
      ((Complex.abs_re_le_norm (z - w)).trans hzw) (abs_nonneg _) (by norm_num)
    _ = _ := by ring


private theorem pair_tail_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : MediumAtom, 0 < d.U →
      (∀ a ∈ d.complexFactorLabels, 0 < complexFactorModulus a) →
      (∀ a ∈ d.complexFactorLabels, ‖d.complexFactorGamma a‖ ≤ 1) →
      ∀ Z : ℝ, 0 < Z → ∀ n₁ n₂ : ℕ,
        ‖d.commonFactorPairNonzeroWeight n₁ n₂ -
          d.commonFactorPairNonzeroWeightTruncated Z n₁ n₂‖ ≤
            (d.complexFactorLabels.card : ℝ) ^ 2 * C / Z ^ (r - 1) := by
  obtain ⟨C, hC, hrow⟩ := poissonNonzeroFrequency_row_tail r hr
  refine ⟨C, hC, fun d hU hmod hgamma Z hZ n₁ n₂ => ?_⟩
  let E : ℝ := C / Z ^ (r - 1)
  let R : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℝ := fun a b =>
    if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
      (∑' h : ℤ, poissonNonzeroFrequency
        (d.U / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ))
        ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
          n₁ n₂ d.residue : ℝ) /
            ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ)) h).re else 0
  let T : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℝ := fun a b =>
    if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n₁ n₂ then
      (∑ h ∈ poissonNonzeroFrequencyWindow
          (poissonFrequencyCutoff Z d.U ((complexFactorModulus a).lcm (complexFactorModulus b))),
        poissonNonzeroFrequency
          (d.U / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ))
          ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
            n₁ n₂ d.residue : ℝ) /
              ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ)) h).re else 0
  have hterm (a : ℕ × ℕ × ℕ) (ha : a ∈ d.complexFactorLabels)
      (b : ℕ × ℕ × ℕ) (hb : b ∈ d.complexFactorLabels) :
      ‖d.complexFactorGamma a * star (d.complexFactorGamma b) * (R a b : ℂ) -
        d.complexFactorGamma a * star (d.complexFactorGamma b) * (T a b : ℂ)‖ ≤ E := by
    by_cases hc : ComplexCRT.Compatible
        (complexFactorModulus a) (complexFactorModulus b) n₁ n₂
    · let L : ℕ := (complexFactorModulus a).lcm (complexFactorModulus b)
      have hL : 0 < L := Nat.lcm_pos (hmod a ha) (hmod b hb)
      have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
      have hcut : poissonFrequencyCutoff Z d.U L = Nat.ceil (Z / (d.U / (L : ℝ))) := by
        unfold poissonFrequencyCutoff
        congr 1
        field_simp [hU.ne', hLreal.ne']
      have he := hrow (d.U / (L : ℝ)) (div_pos hU hLreal)
        ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
          n₁ n₂ d.residue : ℝ) / (L : ℝ)) Z hZ
      rw [← hcut] at he
      dsimp only [R, T]
      rw [if_pos hc, if_pos hc]
      exact coeff_real_tail_norm_le _ _ _ _ E (hgamma a ha) (hgamma b hb)
        (by dsimp [E]; positivity) he
    · simp only [R, T, if_neg hc, sub_self, norm_zero]
      dsimp only [E]
      positivity
  change ‖(∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
      d.complexFactorGamma a * star (d.complexFactorGamma b) * (R a b : ℂ)) -
    ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
      d.complexFactorGamma a * star (d.complexFactorGamma b) * (T a b : ℂ)‖ ≤ _
  calc
    _ ≤ (d.complexFactorLabels.card : ℝ) * ((d.complexFactorLabels.card : ℝ) * E) :=
      norm_sum_sub_le_card _ _ _ _ (fun a ha =>
        norm_sum_sub_le_card _ _ _ _ (fun b hb => hterm a ha b hb))
    _ = _ := by dsimp only [E]; ring

private theorem factorCarrier_prefix {Q : ℝ} (hQ : 1 ≤ Q) :
    factorCarrier Q ⊆ Finset.Ioc 0 (Nat.floor (2 * Q)) := by
  intro q hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
  have hc : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {q : ℕ}
    (hq : q ∈ factorCarrier Q) : 0 < q := by
  exact (Finset.mem_Ioc.mp (factorCarrier_prefix hQ hq)).1

private theorem card_factorCarrier_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ((factorCarrier Q).card : ℝ) ≤ 2 * Q := by
  have h := Finset.card_le_card (factorCarrier_prefix hQ)
  simp only [Nat.card_Ioc, Nat.sub_zero] at h
  exact (show ((factorCarrier Q).card : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by
    exact_mod_cast h).trans (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem betaCarrier_card_le {d : MediumAtom} (hV : 1 ≤ d.V) :
    (d.betaCarrier.card : ℝ) ≤ 2 * d.V := by
  have h := Finset.card_le_card (d.betaCarrier_subset_twiceV hV)
  simp only [Nat.card_Ioc, Nat.sub_zero] at h
  exact (show (d.betaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ) by
    exact_mod_cast h).trans (Nat.floor_le (by linarith : 0 ≤ 2 * d.V))

private theorem primitive_card_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2 * d.Q1 := by
  have hc : d.primitiveFirstFactorCarrier.card ≤ (factorCarrier d.Q1).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact (show (d.primitiveFirstFactorCarrier.card : ℝ) ≤
    ((factorCarrier d.Q1).card : ℝ) by exact_mod_cast hc).trans
      (card_factorCarrier_le hd.2.2.1)

private theorem label_card_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.complexFactorLabels.card : ℝ) ≤ 8 * d.Q1 * d.Q2 * d.Q3 := by
  change (((factorCarrier d.Q1) ×ˢ ((factorCarrier d.Q2) ×ˢ
    (factorCarrier d.Q3))).card : ℝ) ≤ _
  rw [Finset.card_product, Finset.card_product, Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ (2 * d.Q1) * ((2 * d.Q2) * (2 * d.Q3)) :=
      mul_le_mul (card_factorCarrier_le hd.2.2.1)
        (mul_le_mul (card_factorCarrier_le hd.2.2.2.1)
          (card_factorCarrier_le hd.2.2.2.2.1) (Nat.cast_nonneg _) (by linarith [hd.2.2.2.1]))
        (by positivity) (by linarith [hd.2.2.1])
    _ = _ := by ring

private theorem geometry_le_scale {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma) :
    d.U ≤ d.scale ∧ d.V ≤ d.scale ∧ d.Q1 ≤ d.scale ∧
      d.Q2 ≤ d.scale ∧ d.Q3 ≤ d.scale := by
  have hdKeep := hd
  obtain ⟨hU, hV, _hQ1, hQ2, hQ3, _, _, _, hg1, hg2, _⟩ := hdKeep
  have hX := one_le_scale hd
  have hUx : d.U ≤ d.scale := by unfold MediumAtom.scale; nlinarith
  have hVx : d.V ≤ d.scale := V_le_scale hd
  have hn : d.scale ^ (-sigma) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hX (by linarith : -sigma ≤ 0)
  have hQ1x : d.Q1 ≤ d.scale := by
    calc
      _ ≤ d.U * d.scale ^ (-sigma) := hg1.le
      _ ≤ d.U * 1 := mul_le_mul_of_nonneg_left hn (by linarith)
      _ = d.U := mul_one _
      _ ≤ _ := hUx
  have hpow : d.scale ^ (1 - 8 * sigma) ≤ d.scale := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by linarith : 1 - 8 * sigma ≤ 1)
  have hU2 : 1 ≤ d.U ^ 2 := by nlinarith
  have hQ32 : 1 ≤ d.Q3 ^ 2 := by nlinarith
  have hprod : 1 ≤ d.U ^ 2 * d.Q3 ^ 2 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ d.U ^ 2 * d.Q3 ^ 2 := mul_le_mul hU2 hQ32 zero_le_one (sq_nonneg _)
  have hQ2x : d.Q2 ≤ d.scale := by
    calc
      _ = d.Q2 * 1 := by ring
      _ ≤ d.Q2 * (d.U ^ 2 * d.Q3 ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (by linarith)
      _ = d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by ring
      _ ≤ d.scale ^ (1 - 8 * sigma) := hg2.le
      _ ≤ _ := hpow
  have hprod2 : 1 ≤ d.U ^ 2 * d.Q2 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ d.U ^ 2 * d.Q2 := mul_le_mul hU2 hQ2 zero_le_one (sq_nonneg _)
  have hQ3x : d.Q3 ≤ d.scale := by
    calc
      _ ≤ d.Q3 ^ 2 := by nlinarith
      _ = 1 * d.Q3 ^ 2 := by ring
      _ ≤ (d.U ^ 2 * d.Q2) * d.Q3 ^ 2 :=
        mul_le_mul_of_nonneg_right hprod2 (sq_nonneg _)
      _ ≤ d.scale ^ (1 - 8 * sigma) := hg2.le
      _ ≤ _ := hpow
  exact ⟨hUx, hVx, hQ1x, hQ2x, hQ3x⟩

private theorem slice_modulus_pos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (p : ℕ)
    {a : ℕ × ℕ × ℕ}
    (ha : a ∈ (d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.complexFactorLabels) :
    0 < complexFactorModulus a := by
  change a ∈ factorCarrier d.Q1 ×ˢ (factorCarrier d.Q2 ×ˢ factorCarrier d.Q3) at ha
  obtain ⟨ha1, ha23⟩ := Finset.mem_product.mp ha
  obtain ⟨ha2, ha3⟩ := Finset.mem_product.mp ha23
  exact Nat.mul_pos (Nat.mul_pos (factor_pos hd.2.2.1 ha1)
    (factor_pos hd.2.2.2.1 ha2)) (factor_pos hd.2.2.2.2.1 ha3)

private theorem slice_gamma_norm_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (p : ℕ)
    {a : ℕ × ℕ × ℕ}
    (ha : a ∈ (d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.complexFactorLabels) :
    ‖(d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.complexFactorGamma a‖ ≤ 1 := by
  change a ∈ factorCarrier d.Q1 ×ˢ (factorCarrier d.Q2 ×ˢ factorCarrier d.Q3) at ha
  obtain ⟨_, ha23⟩ := Finset.mem_product.mp ha
  obtain ⟨ha2, ha3⟩ := Finset.mem_product.mp ha23
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hGamma2, hGamma3⟩ := hd
  have h2 := (hGamma2 _ ha2).1
  have h3 := (hGamma3 _ ha3).1
  have h1 : ‖(if a.1 = p then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  change ‖(if a.1 = p then (1 : ℂ) else 0) * d.gamma2 a.2.1 * d.gamma3 a.2.2‖ ≤ 1
  rw [norm_mul, norm_mul]
  calc
    _ ≤ 1 * 1 * 1 := mul_le_mul
      (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

private theorem clean_transposed_beta_norm_le {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ :=
    mediumAdmissible_cleanedAlphaAtom hd
  change ‖if n ∈ d.alphaCarrier then d.cleanedAlpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.alphaCarrier
  · have hnBound := hAlpha n hn
    change ‖d.cleanedAlpha n‖ ≤ 1 at hnBound
    simpa only [if_pos hn] using hnBound
  · simp only [if_neg hn, norm_zero, zero_le_one]

private theorem cleaned_core_tail_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ), 0 < sigma →
      ∀ d : MediumAtom, MediumAdmissible B sigma kappa c0 d →
        ∀ Ybeta Ysupport Z : ℝ, 0 < Z →
          ‖d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzero Ybeta Ysupport -
            d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzeroTruncated Ybeta Ysupport Z‖ ≤
              512 * C * d.scale ^ 9 / Z ^ (r - 1) := by
  obtain ⟨C, hC, hpairs⟩ := pair_tail_bound r hr
  refine ⟨C, hC, fun B sigma kappa c0 hsigma d hd Ybeta Ysupport Z hZ => ?_⟩
  let e := d.cleanedAlphaAtom
  let E : ℝ := (d.complexFactorLabels.card : ℝ) ^ 2 * C / Z ^ (r - 1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpair (p N1 N2 : ℕ) :
      ‖(e.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2 -
        (e.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeightTruncated Z N1 N2‖ ≤ E := by
    have he := hpairs (e.q1SliceAtom p).transposedAtom
      (show 0 < (e.q1SliceAtom p).transposedAtom.U by change 0 < d.V; linarith [hd.2.1])
      (fun a ha => slice_modulus_pos hd p ha)
      (fun a ha => slice_gamma_norm_le hd p ha) Z hZ N1 N2
    exact he
  let f : ℕ → ℕ → ℕ → ℂ := fun p N1 N2 =>
    if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
      e.transposedAtom.beta N1 * star (e.transposedAtom.beta N2) *
        (e.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2 else 0
  let g : ℕ → ℕ → ℕ → ℂ := fun p N1 N2 =>
    if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
      e.transposedAtom.beta N1 * star (e.transposedAtom.beta N2) *
        (e.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeightTruncated Z N1 N2 else 0
  have hterm (p N1 N2 : ℕ) : ‖f p N1 N2 - g p N1 N2‖ ≤ E := by
    dsimp only [f, g]
    split_ifs with hmask
    · rw [← mul_sub, norm_mul, norm_mul, norm_star]
      calc
        _ ≤ (1 * 1) * E := mul_le_mul
          (mul_le_mul (clean_transposed_beta_norm_le hd N1)
            (clean_transposed_beta_norm_le hd N2) (norm_nonneg _) zero_le_one)
          (hpair p N1 N2) (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    · simpa only [sub_self, norm_zero] using hE
  have hfinite : ‖e.sharedSmallPairedSmallSupportedNonzero Ybeta Ysupport -
      e.sharedSmallPairedSmallSupportedNonzeroTruncated Ybeta Ysupport Z‖ ≤
      (e.primitiveFirstFactorCarrier.card : ℝ) *
        ((e.transposedAtom.betaCarrier.card : ℝ) *
          ((e.transposedAtom.betaCarrier.card : ℝ) * E)) := by
    change ‖(∑ p ∈ e.primitiveFirstFactorCarrier,
        ∑ N1 ∈ e.transposedAtom.betaCarrier, ∑ N2 ∈ e.transposedAtom.betaCarrier, f p N1 N2) -
      ∑ p ∈ e.primitiveFirstFactorCarrier,
        ∑ N1 ∈ e.transposedAtom.betaCarrier, ∑ N2 ∈ e.transposedAtom.betaCarrier, g p N1 N2‖ ≤ _
    exact norm_sum_sub_le_card _ _ _ _ (fun p _ =>
      norm_sum_sub_le_card _ _ _ _ (fun N1 _ =>
        norm_sum_sub_le_card _ _ _ _ (fun N2 _ => hterm p N1 N2)))
  obtain ⟨hUx, _hVx, hQ1x, hQ2x, hQ3x⟩ := geometry_le_scale hd hsigma
  have hX := one_le_scale hd
  have hX0 : 0 ≤ d.scale := zero_le_one.trans hX
  have hQ10 : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
  have hQ20 : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  have hQ30 : 0 ≤ d.Q3 := zero_le_one.trans hd.2.2.2.2.1
  have hP : (e.primitiveFirstFactorCarrier.card : ℝ) ≤ 2 * d.scale :=
    (primitive_card_le hd).trans (mul_le_mul_of_nonneg_left hQ1x (by norm_num))
  have hN : (e.transposedAtom.betaCarrier.card : ℝ) ≤ 2 * d.scale :=
    (betaCarrier_card_le (d := e.transposedAtom) hd.1).trans
      (mul_le_mul_of_nonneg_left hUx (by norm_num))
  have hLabels : (d.complexFactorLabels.card : ℝ) ≤ 8 * d.scale ^ 3 := by
    calc
      _ ≤ 8 * d.Q1 * d.Q2 * d.Q3 := label_card_le hd
      _ ≤ 8 * d.scale * d.scale * d.scale := by gcongr
      _ = _ := by ring
  have hmass : (e.primitiveFirstFactorCarrier.card : ℝ) *
      (e.transposedAtom.betaCarrier.card : ℝ) ^ 2 *
        (d.complexFactorLabels.card : ℝ) ^ 2 ≤ 512 * d.scale ^ 9 := by
    calc
      _ ≤ (2 * d.scale) * (2 * d.scale) ^ 2 * (8 * d.scale ^ 3) ^ 2 :=
        mul_le_mul
          (mul_le_mul hP (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2)
            (sq_nonneg _) (by positivity))
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hLabels 2) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (e.primitiveFirstFactorCarrier.card : ℝ) *
        ((e.transposedAtom.betaCarrier.card : ℝ) *
          ((e.transposedAtom.betaCarrier.card : ℝ) * E)) := hfinite
    _ = ((e.primitiveFirstFactorCarrier.card : ℝ) *
          (e.transposedAtom.betaCarrier.card : ℝ) ^ 2 *
            (d.complexFactorLabels.card : ℝ) ^ 2) * (C / Z ^ (r - 1)) := by
      dsimp only [E]
      ring
    _ ≤ (512 * d.scale ^ 9) * (C / Z ^ (r - 1)) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by ring

end SharedFirstFactorSmallCoreFourierTruncation

open SharedFirstFactorSmallCoreFourierTruncation

theorem actual_betaL2_gamma1L2_cleaned_smallSupported_FourierTail_log_payment
    (B : ℕ) (sigma kappa c0 A eta : ℝ)
    (hsigma : 0 < sigma) (heta : 0 < eta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
            ‖d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzero
                (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) -
              d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzeroTruncated
                (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) (d.scale ^ eta)‖ ≤
                  d.scale ^ 2 / (Real.log d.scale) ^ A := by
  let r : ℕ := Nat.ceil (11 / eta) + 1
  have hr : 2 ≤ r := by
    have hc : 0 < Nat.ceil (11 / eta) := Nat.ceil_pos.mpr (div_pos (by norm_num) heta)
    dsimp only [r]
    omega
  have horder : (11 : ℝ) ≤ eta * ((r - 1 : ℕ) : ℝ) := by
    have hc := (div_le_iff₀ heta).mp (Nat.le_ceil (11 / eta))
    have he : r - 1 = Nat.ceil (11 / eta) := by dsimp only [r]; omega
    rw [he]
    nlinarith
  obtain ⟨C, hC, htail⟩ := cleaned_core_tail_bound r hr
  obtain ⟨xL, _hxL, hlogs⟩ := eventually_actual_log_cost_le_rpow
    ((2 ^ B) ^ 2 - 1) 0 sigma hsigma (by norm_num : 0 < (1 : ℝ))
  obtain ⟨xP, hxP⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget (2048 * C) A
      (by positivity) (by norm_num : 0 < (1 : ℝ)))
  refine ⟨max 2 (max xL xP), (by norm_num : (1 : ℝ) < 2).trans_le
    (le_max_left _ _), fun d hd hx => ?_⟩
  have hX1 := one_le_scale hd
  have hX : 0 < d.scale := zero_lt_one.trans_le hX1
  have hZ : 0 < d.scale ^ eta := Real.rpow_pos_of_pos hX _
  have hxL' : xL ≤ d.scale :=
    (le_max_left xL xP).trans ((le_max_right 2 (max xL xP)).trans hx)
  have hxP' : xP ≤ d.scale :=
    (le_max_right xL xP).trans ((le_max_right 2 (max xL xP)).trans hx)
  have hlog : (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) ≤ d.scale := by
    simpa only [pow_zero, mul_one, Real.rpow_one] using hlogs B kappa c0 d hd hxL'
  obtain ⟨_, hVx, hQ1x, _, _⟩ := geometry_le_scale hd hsigma
  let W : ℝ := (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hcoef : 4 * d.V * d.Q1 ≤ 4 * d.scale ^ 2 := by
    calc
      _ ≤ (4 * d.scale) * d.scale := mul_le_mul
        (mul_le_mul_of_nonneg_left hVx (by norm_num)) hQ1x
        (by linarith [hd.2.2.1]) (by positivity)
      _ = _ := by ring
  have hH : 0 ≤ (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) := by
    have hh := Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])
    positivity
  have houtside : W ≤ 4 * d.scale ^ 3 := by
    calc
      _ ≤ 4 * d.V * d.Q1 *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) :=
        d.sharedFirstFactor_outside_le hd
      _ ≤ (4 * d.scale ^ 2) * d.scale := mul_le_mul hcoef hlog hH (by positivity)
      _ = _ := by ring
  have hden : (d.scale ^ eta) ^ (r - 1) =
      d.scale ^ (eta * ((r - 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
  have hdenLower : d.scale ^ 11 ≤ (d.scale ^ eta) ^ (r - 1) := by
    rw [hden, ← Real.rpow_natCast d.scale 11]
    exact Real.rpow_le_rpow_of_exponent_le hX1 horder
  have ht := htail B sigma kappa c0 hsigma d hd
    (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) (d.scale ^ eta) hZ
  have hweighted : W *
      ‖d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzero
          (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) -
        d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzeroTruncated
          (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) (d.scale ^ eta)‖ ≤
            (2048 * C) * d.scale := by
    calc
      _ ≤ W * (512 * C * d.scale ^ 9 / (d.scale ^ eta) ^ (r - 1)) :=
        mul_le_mul_of_nonneg_left ht hW
      _ ≤ (4 * d.scale ^ 3) *
          (512 * C * d.scale ^ 9 / (d.scale ^ eta) ^ (r - 1)) :=
        mul_le_mul_of_nonneg_right houtside (by positivity)
      _ = (2048 * C) * d.scale ^ 12 / (d.scale ^ eta) ^ (r - 1) := by ring
      _ ≤ (2048 * C) * d.scale ^ 12 / d.scale ^ 11 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hX _) hdenLower
      _ = _ := by field_simp [hX.ne']
  have hpayment : (2048 * C) * d.scale ≤ d.scale ^ 2 / (Real.log d.scale) ^ A := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      using hxP d.scale hxP'
  exact hweighted.trans hpayment

end

end ImbalancedChen.Part3
