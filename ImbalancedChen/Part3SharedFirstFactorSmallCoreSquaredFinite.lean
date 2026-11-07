import ImbalancedChen.Part3SharedFirstFactorSmallCoreSmoothFrequency

/-!
# Exact squared finite decomposition of the original smooth small core

The ordered original labels and signed frequencies are retained. The actual
small paired-gcd gate removes equal N labels, and CRT compatibility supplies
the original common first-factor congruence. The tail gcd is reindexed as a
unique positive divisor of the original right tail product.

The resonant union is the equality relation of the rational unsigned slopes
|h|/s. Its finite Gram sum is positive. The complementary block is retained
with its sign, and a single Cauchy inequality is applied only to the outer
labels. No spectral cancellation, resonance payment, auxiliary outside
moment or main theorem closure is asserted here.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset CommonSmoothCutoff
open scoped BigOperators

def MediumAtom.smallCoreSquaredOuterCarrier (d : MediumAtom) :
    Finset ((ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) :=
  let Pairs := (d.primitiveFirstFactorCarrier ×ˢ
    (d.transposedAtom.betaCarrier ×ˢ d.transposedAtom.betaCarrier)).filter
      (fun t => t.2.1 ≠ t.2.2 ∧ Nat.ModEq t.1 t.2.1 t.2.2)
  let Tails := (factorCarrier d.Q3) ×ˢ
    ((factorCarrier d.Q3) ×ˢ factorCarrier d.Q2)
  Pairs ×ˢ Tails.biUnion (fun t =>
    (t.2.1 * t.2.2).divisors.image (fun D => (t, D)))

def MediumAtom.smallCoreSquaredInnerCarrier (d : MediumAtom) (Z : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) : Finset (ℕ × ℤ) :=
  factorCarrier d.Q2 ×ˢ
    CommonSmoothCutoff.poissonNonzeroFrequencyWindow
      (d.sharedSmoothFrequencyBound Z o.2.2)

def MediumAtom.smallCoreSquaredRowTerm (d : MediumAtom) (Z : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) (u : ℕ × ℤ) : ℂ :=
  let p := o.1.1
  let N1 := o.1.2.1
  let N2 := o.1.2.2
  let v := o.2.1.1 * u.1
  let w := o.2.1.2.1 * o.2.1.2.2
  let D := o.2.2
  let q := p * v
  let q' := p * w
  let L := q.lcm q'
  if v.gcd w = D ∧ ComplexCRT.Compatible q q' N1 N2 then
    d.gamma2 u.1 *
      (((CommonSmoothCutoff.poissonSmoothLowPass
          ((d.V / (L : ℝ)) * (u.2 : ℝ) / Z) : ℂ) *
        CommonSmoothCutoff.poissonNonzeroFrequency (d.V / (L : ℝ))
          ((ComplexCRT.residue q q' N1 N2 d.residue : ℝ) / (L : ℝ)) u.2).re : ℂ)
  else 0

def MediumAtom.smallCoreSquaredOuterCoefficient (d : MediumAtom)
    (Ybeta Ysupport : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) : ℂ :=
  let N1 := o.1.2.1
  let N2 := o.1.2.2
  if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart
        (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
    d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
      d.gamma3 o.2.1.1 * star (d.gamma3 o.2.1.2.1) * star (d.gamma2 o.2.1.2.2)
  else 0

def MediumAtom.smallCoreSquaredBlock (d : MediumAtom) (Z : ℝ)
    (resonant : Bool) (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) : ℂ :=
  ∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
    ∑ v ∈ d.smallCoreSquaredInnerCarrier Z o,
      if decide (u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
          u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ))) = resonant then
        d.smallCoreSquaredRowTerm Z o u * star (d.smallCoreSquaredRowTerm Z o v)
      else 0

def MediumAtom.smallCoreSquaredCauchyMass (d : MediumAtom) (Z : ℝ)
    (resonant : Bool) : ℝ :=
  (d.smallCoreSquaredOuterCarrier.card : ℝ) *
    ∑ o ∈ d.smallCoreSquaredOuterCarrier, (d.smallCoreSquaredBlock Z resonant o).re

namespace SharedFirstFactorSmallCoreSquaredFinite

private def maskedBeta (d : MediumAtom) (Ybeta Ysupport : ℝ) (N1 N2 : ℕ) : ℂ :=
  if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart
        (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
    d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2)
  else 0

private def smoothFrequencyAtom (d : MediumAtom) (Z : ℝ)
    (p N1 N2 r s r' s' : ℕ) (h : ℤ) : ℂ :=
  let L := (p * (r * s)).lcm (p * (r' * s'))
  (poissonSmoothLowPass ((d.V / (L : ℝ)) * (h : ℝ) / Z) : ℂ) *
    poissonNonzeroFrequency (d.V / (L : ℝ))
      ((ComplexCRT.residue (p * (r * s)) (p * (r' * s')) N1 N2 d.residue : ℝ) /
        (L : ℝ)) h

private theorem factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) :
    0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hc : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  exact ⟨by omega, (Nat.le_ceil Q).trans (by exact_mod_cast hlo),
    (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * Q))⟩

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

private theorem outer_tail_memberships (d : MediumAtom)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (ho : o ∈ d.smallCoreSquaredOuterCarrier) :
    o.2.1.1 ∈ factorCarrier d.Q3 ∧
      o.2.1.2.1 ∈ factorCarrier d.Q3 ∧ o.2.1.2.2 ∈ factorCarrier d.Q2 := by
  change o ∈ ((d.primitiveFirstFactorCarrier ×ˢ
    (d.transposedAtom.betaCarrier ×ˢ d.transposedAtom.betaCarrier)).filter
      (fun t => t.2.1 ≠ t.2.2 ∧ Nat.ModEq t.1 t.2.1 t.2.2)) ×ˢ
    ((factorCarrier d.Q3) ×ˢ ((factorCarrier d.Q3) ×ˢ factorCarrier d.Q2)).biUnion
      (fun t => (t.2.1 * t.2.2).divisors.image (fun D => (t, D))) at ho
  obtain ⟨t, ht, hImage⟩ := Finset.mem_biUnion.mp (Finset.mem_product.mp ho).2
  obtain ⟨D, _hD, he⟩ := Finset.mem_image.mp hImage
  have het : t = o.2.1 := congrArg Prod.fst he
  rw [← het]
  exact ⟨(Finset.mem_product.mp ht).1,
    (Finset.mem_product.mp (Finset.mem_product.mp ht).2).1,
    (Finset.mem_product.mp (Finset.mem_product.mp ht).2).2⟩

private theorem cleaned_squared_outerCoefficient_norm_le_one
    (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom)
    (hd : MediumAdmissible B sigma kappa c0 d)
    (Ybeta Ysupport : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (ho : o ∈ d.cleanedAlphaAtom.smallCoreSquaredOuterCarrier) :
    ‖d.cleanedAlphaAtom.smallCoreSquaredOuterCoefficient Ybeta Ysupport o‖ ≤ 1 := by
  obtain ⟨hr, hr', hs'⟩ := outer_tail_memberships d.cleanedAlphaAtom o ho
  have hdKeep := hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hGamma2, hGamma3⟩ := hdKeep
  have h1 := clean_transposed_beta_norm_le hd o.1.2.1
  have h2 := clean_transposed_beta_norm_le hd o.1.2.2
  have h3 := (hGamma3 o.2.1.1 hr).1
  have h4 := (hGamma3 o.2.1.2.1 hr').1
  have h5 := (hGamma2 o.2.1.2.2 hs').1
  unfold MediumAtom.smallCoreSquaredOuterCoefficient
  dsimp only
  split_ifs
  · simp only [norm_mul, norm_star]
    exact mul_le_one₀
      (mul_le_one₀
        (mul_le_one₀
          (mul_le_one₀ h1 (norm_nonneg _) h2)
          (norm_nonneg _) h3)
        (norm_nonneg _) h4)
      (norm_nonneg _) h5
  · simp only [norm_zero, zero_le_one]

private theorem sum_divisor_images {T : Type*} [DecidableEq T]
    (S : Finset T) (w : T → ℕ) (f : T × ℕ → ℂ) :
    (∑ q ∈ S.biUnion (fun t => (w t).divisors.image (fun D => (t, D))), f q) =
      ∑ t ∈ S, ∑ D ∈ (w t).divisors, f (t, D) := by
  have hdisj : Set.PairwiseDisjoint (↑S)
      (fun t => (w t).divisors.image (fun D => (t, D))) := by
    intro t _ t' _ hne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨D, _hD, he⟩ := Finset.mem_image.mp hq
    obtain ⟨D', _hD', he'⟩ := Finset.mem_image.mp hq'
    exact hne (congrArg Prod.fst (he.trans he'.symm))
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_image]
  intro D _ D' _ he
  exact congrArg Prod.snd he

private theorem outer_sum_expansion (d : MediumAtom)
    (f : ((ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) → ℂ) :
    (∑ o ∈ d.smallCoreSquaredOuterCarrier, f o) =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        ∑ N1 ∈ d.transposedAtom.betaCarrier, ∑ N2 ∈ d.transposedAtom.betaCarrier,
          if N1 ≠ N2 ∧ Nat.ModEq p N1 N2 then
            ∑ r ∈ factorCarrier d.Q3, ∑ r' ∈ factorCarrier d.Q3,
              ∑ s' ∈ factorCarrier d.Q2, ∑ D ∈ (r' * s').divisors,
                f ((p, N1, N2), ((r, r', s'), D))
          else 0 := by
  unfold MediumAtom.smallCoreSquaredOuterCarrier
  rw [Finset.sum_product]
  simp_rw [sum_divisor_images]
  simp only [Finset.sum_filter, Finset.sum_product]

private theorem move_left_s_last (R S : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℂ) :
    (∑ r ∈ R, ∑ s ∈ S, ∑ r' ∈ R, ∑ s' ∈ S, f r s r' s') =
      ∑ r ∈ R, ∑ r' ∈ R, ∑ s' ∈ S, ∑ s ∈ S, f r s r' s' := by
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm (s := S) (t := R)]
  apply Finset.sum_congr rfl
  intro r' _
  exact Finset.sum_comm

private theorem outerCoefficient_factor (d : MediumAtom) (Ybeta Ysupport : ℝ)
    (p N1 N2 r r' s' D : ℕ) :
    d.smallCoreSquaredOuterCoefficient Ybeta Ysupport ((p, N1, N2), ((r, r', s'), D)) =
      maskedBeta d Ybeta Ysupport N1 N2 * d.gamma3 r * star (d.gamma3 r') *
        star (d.gamma2 s') := by
  unfold MediumAtom.smallCoreSquaredOuterCoefficient maskedBeta
  dsimp only
  split_ifs <;> ring

private theorem rowTerm_factor (d : MediumAtom) (Z : ℝ)
    (p N1 N2 r s r' s' D : ℕ) (h : ℤ) :
    d.smallCoreSquaredRowTerm Z ((p, N1, N2), ((r, r', s'), D)) (s, h) =
      if (r * s).gcd (r' * s') = D ∧
          ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 then
        d.gamma2 s * ((smoothFrequencyAtom d Z p N1 N2 r s r' s' h).re : ℂ)
      else 0 := rfl

private theorem divisor_frequency_sum (d : MediumAtom) (Z : ℝ)
    (p N1 N2 r s r' s' : ℕ) (hw : 0 < r' * s') :
    (∑ D ∈ (r' * s').divisors,
      ∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow (d.sharedSmoothFrequencyBound Z D),
        d.smallCoreSquaredRowTerm Z ((p, N1, N2), ((r, r', s'), D)) (s, h)) =
      d.gamma2 s *
        (if ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 then
          ((∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
              (d.sharedSmoothFrequencyBound Z ((r * s).gcd (r' * s'))),
            smoothFrequencyAtom d Z p N1 N2 r s r' s' h).re : ℂ)
        else 0) := by
  let D0 : ℕ := (r * s).gcd (r' * s')
  have hmem : D0 ∈ (r' * s').divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hw.ne'⟩
  rw [Finset.sum_eq_single D0]
  · simp_rw [rowTerm_factor]
    by_cases hc : ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2
    · simp only [D0, true_and, if_pos hc, Finset.mul_sum,
        Complex.re_sum, Complex.ofReal_sum]
    · simp only [D0, true_and, if_neg hc, Finset.sum_const_zero,
        mul_zero]
  · intro D _ hne
    apply Finset.sum_eq_zero
    intro h _
    rw [rowTerm_factor, if_neg]
    intro hc
    exact hne hc.1.symm
  · intro hnot
    exact (hnot hmem).elim

private theorem row_divisor_reindex (d : MediumAtom) (Z Ybeta Ysupport : ℝ)
    (p N1 N2 r r' s' : ℕ) (hw : 0 < r' * s') :
    (∑ D ∈ (r' * s').divisors,
      d.smallCoreSquaredOuterCoefficient Ybeta Ysupport ((p, N1, N2), ((r, r', s'), D)) *
        ∑ u ∈ d.smallCoreSquaredInnerCarrier Z ((p, N1, N2), ((r, r', s'), D)),
          d.smallCoreSquaredRowTerm Z ((p, N1, N2), ((r, r', s'), D)) u) =
      ∑ s ∈ factorCarrier d.Q2,
        (maskedBeta d Ybeta Ysupport N1 N2 * d.gamma3 r * star (d.gamma3 r') *
            star (d.gamma2 s')) *
          (d.gamma2 s *
            (if ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 then
              ((∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
                  (d.sharedSmoothFrequencyBound Z ((r * s).gcd (r' * s'))),
                smoothFrequencyAtom d Z p N1 N2 r s r' s' h).re : ℂ)
            else 0)) := by
  let C : ℂ := maskedBeta d Ybeta Ysupport N1 N2 * d.gamma3 r * star (d.gamma3 r') *
    star (d.gamma2 s')
  simp_rw [outerCoefficient_factor]
  simp only [MediumAtom.smallCoreSquaredInnerCarrier, Finset.sum_product]
  change (∑ D ∈ (r' * s').divisors, C *
      ∑ s ∈ factorCarrier d.Q2,
        ∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
            (d.sharedSmoothFrequencyBound Z D),
          d.smallCoreSquaredRowTerm Z ((p, N1, N2), ((r, r', s'), D)) (s, h)) = _
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [divisor_frequency_sum d Z p N1 N2 r s r' s' hw]

private theorem unfiltered_pair_reindex (d : MediumAtom)
    (hQ2 : 1 ≤ d.Q2) (hQ3 : 1 ≤ d.Q3)
    (Z Ybeta Ysupport : ℝ) (p N1 N2 : ℕ) :
    maskedBeta d Ybeta Ysupport N1 N2 * d.sharedSmallPairSmoothFrequencyKernel Z p N1 N2 =
      ∑ r ∈ factorCarrier d.Q3, ∑ r' ∈ factorCarrier d.Q3,
        ∑ s' ∈ factorCarrier d.Q2, ∑ D ∈ (r' * s').divisors,
          d.smallCoreSquaredOuterCoefficient Ybeta Ysupport ((p, N1, N2), ((r, r', s'), D)) *
            ∑ u ∈ d.smallCoreSquaredInnerCarrier Z ((p, N1, N2), ((r, r', s'), D)),
              d.smallCoreSquaredRowTerm Z ((p, N1, N2), ((r, r', s'), D)) u := by
  symm
  calc
    _ = ∑ r ∈ factorCarrier d.Q3, ∑ r' ∈ factorCarrier d.Q3,
        ∑ s' ∈ factorCarrier d.Q2, ∑ s ∈ factorCarrier d.Q2,
          (maskedBeta d Ybeta Ysupport N1 N2 * d.gamma3 r * star (d.gamma3 r') *
              star (d.gamma2 s')) *
            (d.gamma2 s *
              (if ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 then
                ((∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
                    (d.sharedSmoothFrequencyBound Z ((r * s).gcd (r' * s'))),
                  smoothFrequencyAtom d Z p N1 N2 r s r' s' h).re : ℂ)
              else 0)) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro r' hr'
      apply Finset.sum_congr rfl
      intro s' hs'
      exact row_divisor_reindex d Z Ybeta Ysupport p N1 N2 r r' s'
        (Nat.mul_pos (factor_bounds hQ3 hr').1 (factor_bounds hQ2 hs').1)
    _ = ∑ r ∈ factorCarrier d.Q3, ∑ s ∈ factorCarrier d.Q2,
        ∑ r' ∈ factorCarrier d.Q3, ∑ s' ∈ factorCarrier d.Q2,
          (maskedBeta d Ybeta Ysupport N1 N2 * d.gamma3 r * star (d.gamma3 r') *
              star (d.gamma2 s')) *
            (d.gamma2 s *
              (if ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 then
                ((∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
                    (d.sharedSmoothFrequencyBound Z ((r * s).gcd (r' * s'))),
                  smoothFrequencyAtom d Z p N1 N2 r s r' s' h).re : ℂ)
              else 0)) := (move_left_s_last _ _ _).symm
    _ = _ := by
      unfold MediumAtom.sharedSmallPairSmoothFrequencyKernel
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r' _
      apply Finset.sum_congr rfl
      intro s' _
      unfold smoothFrequencyAtom
      by_cases hc : ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2
      · simp only [if_pos hc, star_mul]
        ring
      · simp only [if_neg hc, Complex.ofReal_zero, mul_zero]

private theorem compatible_mod_firstFactor {p v w N1 N2 : ℕ}
    (hc : ComplexCRT.Compatible (p * v) (p * w) N1 N2) : Nat.ModEq p N1 N2 := by
  have he := hc.2.2
  rw [sharedFirstFactor_gcd] at he
  exact he.of_dvd (dvd_mul_right p (v.gcd w))

private theorem kernel_eq_zero_of_not_modEq (d : MediumAtom) (Z : ℝ)
    (p N1 N2 : ℕ) (hnot : ¬ Nat.ModEq p N1 N2) :
    d.sharedSmallPairSmoothFrequencyKernel Z p N1 N2 = 0 := by
  unfold MediumAtom.sharedSmallPairSmoothFrequencyKernel
  apply Finset.sum_eq_zero
  intro r _
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro r' _
  apply Finset.sum_eq_zero
  intro s' _
  have hc : ¬ ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 :=
    fun he => hnot (compatible_mod_firstFactor he)
  dsimp only
  rw [if_neg hc]
  simp only [Complex.ofReal_zero, mul_zero]

private theorem small_mask_ne_diagonal
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d)
    {N1 N2 : ℕ} (hN1 : N1 ∈ d.transposedAtom.betaCarrier)
    (hsmall : (N1.gcd N2 : ℝ) ≤ d.scale ^ (sigma / 4)) : N1 ≠ N2 := by
  have hx : 1 < d.scale :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos (1 : ℝ))).trans hd.2.2.2.2.2.1
  have hcut : d.scale ^ (sigma / 4) < d.U :=
    (Real.rpow_lt_rpow_of_exponent_lt hx (by linarith : sigma / 4 < sigma)).trans_le
      (PairedAlphaDeletion.actual_geometry_bounds hd).1
  change N1 ∈ factorCarrier d.U at hN1
  have hlo := (factor_bounds hd.1 hN1).2.1
  intro heq
  have hNsmall : (N1 : ℝ) ≤ d.scale ^ (sigma / 4) := by
    simpa only [heq, Nat.gcd_self] using hsmall
  linarith

private theorem pair_zero_outside
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d)
    {p N1 N2 : ℕ} (hN1 : N1 ∈ d.transposedAtom.betaCarrier)
    (hnot : ¬ (N1 ≠ N2 ∧ Nat.ModEq p N1 N2)) (Z : ℝ) :
    maskedBeta d (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) N1 N2 *
      d.sharedSmallPairSmoothFrequencyKernel Z p N1 N2 = 0 := by
  unfold maskedBeta
  split_ifs with hmask
  · have hne := small_mask_ne_diagonal hsigma hd hN1 hmask.1
    have hmod : ¬ Nat.ModEq p N1 N2 := fun hm => hnot ⟨hne, hm⟩
    rw [kernel_eq_zero_of_not_modEq d Z p N1 N2 hmod, mul_zero]
  · exact zero_mul _

private theorem cleaned_actualSmooth_squared_reindex
    (B : ℕ) (sigma kappa c0 : ℝ) (hsigma : 0 < sigma)
    (d : MediumAtom) (hd : MediumAdmissible B sigma kappa c0 d)
    (Z : ℝ) (_hZ : 0 < Z) :
          let e := d.cleanedAlphaAtom
          let Y := d.scale ^ (sigma / 4)
          (e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z =
              (∑ o ∈ e.smallCoreSquaredOuterCarrier,
                e.smallCoreSquaredOuterCoefficient Y Y o *
                  (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o,
                    e.smallCoreSquaredRowTerm Z o u))) := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let Y := d.scale ^ (sigma / 4)
  have he : MediumAdmissible B sigma kappa c0 e := mediumAdmissible_cleanedAlphaAtom hd
  rw [outer_sum_expansion]
  change (∑ p ∈ e.primitiveFirstFactorCarrier,
    ∑ N1 ∈ e.transposedAtom.betaCarrier, ∑ N2 ∈ e.transposedAtom.betaCarrier,
      if (N1.gcd N2 : ℝ) ≤ Y ∧
          (CanonicalReciprocalData.supportedPart (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Y then
        e.transposedAtom.beta N1 * star (e.transposedAtom.beta N2) *
          e.sharedSmallPairSmoothFrequencyKernel Z p N1 N2 else 0) = _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro N1 hN1
  apply Finset.sum_congr rfl
  intro N2 _
  have hmasked : (if (N1.gcd N2 : ℝ) ≤ Y ∧
      (CanonicalReciprocalData.supportedPart (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Y then
      e.transposedAtom.beta N1 * star (e.transposedAtom.beta N2) *
        e.sharedSmallPairSmoothFrequencyKernel Z p N1 N2 else 0) =
      maskedBeta e Y Y N1 N2 * e.sharedSmallPairSmoothFrequencyKernel Z p N1 N2 := by
    unfold maskedBeta
    split_ifs <;> simp only [zero_mul]
  rw [hmasked]
  by_cases hp : N1 ≠ N2 ∧ Nat.ModEq p N1 N2
  · rw [if_pos hp]
    exact unfiltered_pair_reindex e he.2.2.2.1 he.2.2.2.2.1 Z Y Y p N1 N2
  · rw [if_neg hp]
    exact pair_zero_outside hsigma he hN1 hp Z

private theorem unsigned_slope_eq_iff {s1 s2 : ℕ}
    (hs1 : 0 < s1) (hs2 : 0 < s2) (h1 h2 : ℤ) :
    (h1.natAbs : ℚ) / (s1 : ℚ) = (h2.natAbs : ℚ) / (s2 : ℚ) ↔
      h1 * (s2 : ℤ) = h2 * (s1 : ℤ) ∨ h1 * (s2 : ℤ) = -(h2 * (s1 : ℤ)) := by
  have hs1q : (s1 : ℚ) ≠ 0 := by exact_mod_cast hs1.ne'
  have hs2q : (s2 : ℚ) ≠ 0 := by exact_mod_cast hs2.ne'
  rw [div_eq_div_iff hs1q hs2q]
  constructor
  · intro he
    have hNat : h1.natAbs * s2 = h2.natAbs * s1 := by exact_mod_cast he
    apply Int.natAbs_eq_natAbs_iff.mp
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hNat
  · intro he
    have hAbs := Int.natAbs_eq_natAbs_iff.mpr he
    have hNat : h1.natAbs * s2 = h2.natAbs * s1 := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hAbs
    exact_mod_cast hNat

private theorem fiber_gram_nonnegative {T S : Type*}
    [DecidableEq T] [DecidableEq S] (I : Finset T) (f : T → S) (z : T → ℂ) :
    0 ≤ (∑ u ∈ I, ∑ v ∈ I, if f u = f v then z u * star (z v) else 0).re := by
  let J := I.image f
  have he : (∑ u ∈ I, ∑ v ∈ I, if f u = f v then z u * star (z v) else 0) =
      ∑ t ∈ J, ((‖∑ u ∈ I.filter (fun u => f u = t), z u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := I) (t := J) (g := f)
      (fun u hu => Finset.mem_image_of_mem f hu)
      (fun u => ∑ v ∈ I, if f u = f v then z u * star (z v) else 0)]
    apply Finset.sum_congr rfl
    intro t _
    rw [complex_norm_sq_sum_eq_double_star]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    have hfu := (Finset.mem_filter.mp hu).2
    by_cases hfv : f v = t
    · rw [if_pos (hfu.trans hfv.symm), if_pos hfv]
    · rw [if_neg (by intro h; exact hfv (h.symm.trans hfu)), if_neg hfv]
  rw [he]
  simp only [Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem squared_row_gram_partition
    (d : MediumAtom) (hQ2 : 1 ≤ d.Q2) (Z : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) :
    (0 ≤ (d.smallCoreSquaredBlock Z true o).re) ∧
      ((d.smallCoreSquaredBlock Z true o).re +
          (d.smallCoreSquaredBlock Z false o).re =
        ‖∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
            d.smallCoreSquaredRowTerm Z o u‖ ^ 2) := by
  let I := d.smallCoreSquaredInnerCarrier Z o
  let z := d.smallCoreSquaredRowTerm Z o
  let f : ℕ × ℤ → ℚ := fun u => (u.2.natAbs : ℚ) / (u.1 : ℚ)
  have hpos (u : ℕ × ℤ) (hu : u ∈ I) : 0 < u.1 := by
    change u ∈ factorCarrier d.Q2 ×ˢ
      CommonSmoothCutoff.poissonNonzeroFrequencyWindow
        (d.sharedSmoothFrequencyBound Z o.2.2) at hu
    exact (factor_bounds hQ2 (Finset.mem_product.mp hu).1).1
  have htrue : d.smallCoreSquaredBlock Z true o =
      ∑ u ∈ I, ∑ v ∈ I, if f u = f v then z u * star (z v) else 0 := by
    unfold MediumAtom.smallCoreSquaredBlock
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hiff : f u = f v ↔
        u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
          u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ)) :=
      unsigned_slope_eq_iff (hpos u hu) (hpos v hv) u.2 v.2
    by_cases h : f u = f v
    · have hp := hiff.mp h
      simp [h, hp, z]
    · have hp : ¬ (u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
          u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ))) := fun he => h (hiff.mpr he)
      simp [h, hp]
  have hcomplex : d.smallCoreSquaredBlock Z true o + d.smallCoreSquaredBlock Z false o =
      ∑ u ∈ I, ∑ v ∈ I, z u * star (z v) := by
    unfold MediumAtom.smallCoreSquaredBlock
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hp : u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
        u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ))
    · simp [hp, z]
    · simp [hp, z]
  refine ⟨?_, ?_⟩
  · rw [htrue]
    exact fiber_gram_nonnegative I f z
  · rw [← Complex.add_re, hcomplex]
    simpa only [Complex.ofReal_re] using
      (congrArg Complex.re (complex_norm_sq_sum_eq_double_star I z)).symm

private theorem cleaned_squared_outer_Cauchy
    (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom)
    (hd : MediumAdmissible B sigma kappa c0 d)
    (Ybeta Ysupport Z : ℝ) :
    let e := d.cleanedAlphaAtom
    ‖∑ o ∈ e.smallCoreSquaredOuterCarrier,
        e.smallCoreSquaredOuterCoefficient Ybeta Ysupport o *
          (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o,
            e.smallCoreSquaredRowTerm Z o u)‖ ^ 2 ≤
      e.smallCoreSquaredCauchyMass Z true +
        e.smallCoreSquaredCauchyMass Z false := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let O := e.smallCoreSquaredOuterCarrier
  let C := e.smallCoreSquaredOuterCoefficient Ybeta Ysupport
  let F := fun o => ∑ u ∈ e.smallCoreSquaredInnerCarrier Z o, e.smallCoreSquaredRowTerm Z o u
  have hC : ∑ o ∈ O, ‖C o‖ ^ 2 ≤ (O.card : ℝ) := by
    calc
      _ ≤ ∑ _o ∈ O, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro o ho
        have hbound := cleaned_squared_outerCoefficient_norm_le_one B sigma kappa c0 d hd
          Ybeta Ysupport o ho
        simpa only [one_pow] using
          (sq_le_sq₀ (norm_nonneg (C o)) (by norm_num : (0 : ℝ) ≤ 1)).2 hbound
      _ = _ := by simp
  have hF : 0 ≤ ∑ o ∈ O, ‖F o‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hGram : (∑ o ∈ O, ‖F o‖ ^ 2) =
      ∑ o ∈ O, ((e.smallCoreSquaredBlock Z true o).re +
        (e.smallCoreSquaredBlock Z false o).re) := by
    apply Finset.sum_congr rfl
    intro o _
    exact (squared_row_gram_partition e hd.2.2.2.1 Z o).2.symm
  calc
    _ ≤ (∑ o ∈ O, ‖C o‖ ^ 2) * ∑ o ∈ O, ‖F o‖ ^ 2 :=
      complex_finset_cauchy_norm_sq O C F
    _ ≤ (O.card : ℝ) * ∑ o ∈ O, ‖F o‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hC hF
    _ = _ := by
      rw [hGram, Finset.sum_add_distrib, mul_add]
      rfl

end SharedFirstFactorSmallCoreSquaredFinite

open SharedFirstFactorSmallCoreSquaredFinite

theorem actual_smallSupported_squared_resonance_Cauchy
    (B : ℕ) (sigma kappa c0 : ℝ) (hsigma : 0 < sigma)
    (d : MediumAtom) (hd : MediumAdmissible B sigma kappa c0 d) :
    ∀ Z : ℝ, 0 < Z →
          let e := d.cleanedAlphaAtom
          let Y := d.scale ^ (sigma / 4)
          (e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z =
              (∑ o ∈ e.smallCoreSquaredOuterCarrier,
                e.smallCoreSquaredOuterCoefficient Y Y o *
                  (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o,
                    e.smallCoreSquaredRowTerm Z o u))) ∧
            (0 ≤ e.smallCoreSquaredCauchyMass Z true) ∧
            (‖e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z‖ ^ 2 ≤
              e.smallCoreSquaredCauchyMass Z true +
                e.smallCoreSquaredCauchyMass Z false) := by
  intro Z hZ
  dsimp only
  let e := d.cleanedAlphaAtom
  let Y := d.scale ^ (sigma / 4)
  have heq : e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z =
      ∑ o ∈ e.smallCoreSquaredOuterCarrier,
        e.smallCoreSquaredOuterCoefficient Y Y o *
          (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o, e.smallCoreSquaredRowTerm Z o u) :=
    cleaned_actualSmooth_squared_reindex B sigma kappa c0 hsigma d hd Z hZ
  refine ⟨heq, ?_, ?_⟩
  · unfold MediumAtom.smallCoreSquaredCauchyMass
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun o _ => (squared_row_gram_partition e hd.2.2.2.1 Z o).1))
  · rw [heq]
    exact cleaned_squared_outer_Cauchy B sigma kappa c0 d hd Y Y Z

end

end ImbalancedChen.Part3
