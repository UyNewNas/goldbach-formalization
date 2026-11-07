import ImbalancedChen.Part3SharedFirstFactorSmallCoreFourierTruncation

/-!
# Smooth frequency support for the literal original small core

The fixed smooth low pass keeps the real projection before each complex
coefficient. Its omitted Schwartz tail is paid after the original outside
moments exactly once. For a fixed actual tail gcd D, all rows use one signed
frequency carrier, independent of the other row labels. The physical shared
first factor is an arbitrary positive integer, with no primality assumption.

This is a smooth approximation of the original full core. No equality with
its sharp row truncation, Mellin separation, root-phase operator estimate,
or reciprocal spectral cancellation is asserted here.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter Topology
open scoped BigOperators SchwartzMap FourierTransform ContDiff
open CommonSmoothCutoff TransposedPrimitiveUPayment

def CommonSmoothCutoff.poissonSmoothLowPass (u : ℝ) : ℝ :=
  CommonSmoothCutoff.dyadicBump (3 / 2 + u / 2)

def MediumAtom.sharedSmoothFrequencyBound (d : MediumAtom) (Z : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil (64 * Z * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 / ((D : ℝ) * d.V))

def MediumAtom.sharedSmallPairSmoothFrequencyKernel (d : MediumAtom)
    (Z : ℝ) (p N1 N2 : ℕ) : ℂ :=
  ∑ r ∈ factorCarrier d.Q3, ∑ s ∈ factorCarrier d.Q2,
    ∑ r' ∈ factorCarrier d.Q3, ∑ s' ∈ factorCarrier d.Q2,
      let v := r * s
      let w := r' * s'
      let D := v.gcd w
      let L := (p * v).lcm (p * w)
      d.gamma2 s * d.gamma3 r * star (d.gamma2 s' * d.gamma3 r') *
        (if ComplexCRT.Compatible (p * v) (p * w) N1 N2 then
          (∑ h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
              (d.sharedSmoothFrequencyBound Z D),
            (CommonSmoothCutoff.poissonSmoothLowPass
              ((d.V / (L : ℝ)) * (h : ℝ) / Z) : ℂ) *
              CommonSmoothCutoff.poissonNonzeroFrequency
                (d.V / (L : ℝ))
                ((ComplexCRT.residue (p * v) (p * w) N1 N2 d.residue : ℝ) /
                  (L : ℝ)) h).re
        else 0 : ℝ)

def MediumAtom.sharedSmallPairedSmallSupportedNonzeroSmooth (d : MediumAtom)
    (Ybeta Ysupport Z : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ N1 ∈ d.transposedAtom.betaCarrier, ∑ N2 ∈ d.transposedAtom.betaCarrier,
      if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
          (CanonicalReciprocalData.supportedPart
            (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
        d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
          d.sharedSmallPairSmoothFrequencyKernel Z p N1 N2
      else 0

namespace SharedFirstFactorSmallCoreSmoothFrequency

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

private theorem lowPass_contDiff : ContDiff ℝ ∞ poissonSmoothLowPass := by
  exact dyadicBump.contDiff.comp (contDiff_const.add (contDiff_id.div_const 2))

private theorem lowPass_nonneg (u : ℝ) : 0 ≤ poissonSmoothLowPass u :=
  dyadicBump.nonneg

private theorem lowPass_le_one (u : ℝ) : poissonSmoothLowPass u ≤ 1 :=
  dyadicBump.le_one

private theorem lowPass_eq_one {u : ℝ} (hu : |u| ≤ 1) :
    poissonSmoothLowPass u = 1 := by
  apply dyadicBump.one_of_mem_closedBall
  change |(3 / 2 + u / 2) - 3 / 2| ≤ 1 / 2
  rw [abs_le] at hu ⊢
  constructor <;> linarith [hu.1, hu.2]

private theorem lowPass_eq_zero {u : ℝ} (hu : 2 ≤ |u|) :
    poissonSmoothLowPass u = 0 := by
  apply dyadicBump.zero_of_le_dist
  change (1 : ℝ) ≤ |(3 / 2 + u / 2) - 3 / 2|
  have he : (3 / 2 + u / 2) - 3 / 2 = u / 2 := by ring
  rw [he, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)

private theorem lowPass_ne_zero_abs_lt_two {u : ℝ}
    (hu : poissonSmoothLowPass u ≠ 0) : |u| < 2 := by
  by_contra hn
  exact hu (lowPass_eq_zero (le_of_not_gt hn))

private theorem factor_le_twice {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : (n : ℝ) ≤ 2 * Q :=
  (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans
    (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem tail_gamma_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {r s : ℕ}
    (hr : r ∈ factorCarrier d.Q3) (hs : s ∈ factorCarrier d.Q2) :
    ‖d.gamma2 s * d.gamma3 r‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h2, h3⟩ := hd
  rw [norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (h2 s hs).1 (h3 r hr).1 (norm_nonneg _) zero_le_one
    _ = _ := by norm_num

private theorem gcd_mul_shared_lcm (p v w : ℕ) :
    v.gcd w * ((p * v).lcm (p * w)) = p * v * w := by
  rw [sharedFirstFactor_lcm]
  calc
    _ = p * (v.gcd w * v.lcm w) := by ring
    _ = _ := by rw [Nat.gcd_mul_lcm]; ring

private theorem gcd_mul_shared_lcm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {p r s r' s' : ℕ} (hp : p ∈ d.primitiveFirstFactorCarrier)
    (hr : r ∈ factorCarrier d.Q3) (hs : s ∈ factorCarrier d.Q2)
    (hr' : r' ∈ factorCarrier d.Q3) (hs' : s' ∈ factorCarrier d.Q2) :
    (((r * s).gcd (r' * s') : ℕ) : ℝ) *
        (((p * (r * s)).lcm (p * (r' * s')) : ℕ) : ℝ) ≤
      32 * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 := by
  have hpn := factor_le_twice hd.2.2.1 (Finset.mem_filter.mp hp).1
  have hrn := factor_le_twice hd.2.2.2.2.1 hr
  have hsn := factor_le_twice hd.2.2.2.1 hs
  have hrn' := factor_le_twice hd.2.2.2.2.1 hr'
  have hsn' := factor_le_twice hd.2.2.2.1 hs'
  have hQ10 : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
  have hQ20 : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  have hQ30 : 0 ≤ d.Q3 := zero_le_one.trans hd.2.2.2.2.1
  rw [← Nat.cast_mul, gcd_mul_shared_lcm]
  push_cast
  calc
    _ ≤ (2 * d.Q1) * ((2 * d.Q3) * (2 * d.Q2)) *
        ((2 * d.Q3) * (2 * d.Q2)) := by gcongr
    _ = _ := by ring

private theorem smooth_shared_frequency_support
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {Z : ℝ} (hZ : 0 < Z)
    {p r s r' s' : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier)
    (hr : r ∈ factorCarrier d.Q3) (hs : s ∈ factorCarrier d.Q2)
    (hr' : r' ∈ factorCarrier d.Q3) (hs' : s' ∈ factorCarrier d.Q2)
    (x : ℝ) (h : ℤ)
    (hactive :
      (CommonSmoothCutoff.poissonSmoothLowPass
        ((d.V / (((p * (r * s)).lcm (p * (r' * s')) : ℕ) : ℝ)) * (h : ℝ) / Z) : ℂ) *
        CommonSmoothCutoff.poissonNonzeroFrequency
          (d.V / (((p * (r * s)).lcm (p * (r' * s')) : ℕ) : ℝ)) x h ≠ 0) :
    h ∈ CommonSmoothCutoff.poissonNonzeroFrequencyWindow
      (d.sharedSmoothFrequencyBound Z ((r * s).gcd (r' * s'))) := by
  let D : ℕ := (r * s).gcd (r' * s')
  let L : ℕ := (p * (r * s)).lcm (p * (r' * s'))
  have hp0 := factor_pos hd.2.2.1 (Finset.mem_filter.mp hp).1
  have hr0 := factor_pos hd.2.2.2.2.1 hr
  have hs0 := factor_pos hd.2.2.2.1 hs
  have hr0' := factor_pos hd.2.2.2.2.1 hr'
  have hs0' := factor_pos hd.2.2.2.1 hs'
  have hD0 : 0 < D := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hr0 hs0)
  have hL0 : 0 < L := Nat.lcm_pos
    (Nat.mul_pos hp0 (Nat.mul_pos hr0 hs0))
    (Nat.mul_pos hp0 (Nat.mul_pos hr0' hs0'))
  have hD : 0 < (D : ℝ) := by exact_mod_cast hD0
  have hL : 0 < (L : ℝ) := by exact_mod_cast hL0
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have ht : 0 < d.V / (L : ℝ) := div_pos hV hL
  have hh0 : h ≠ 0 := by
    intro he
    subst h
    simp [poissonNonzeroFrequency] at hactive
  have hchi : poissonSmoothLowPass ((d.V / (L : ℝ)) * (h : ℝ) / Z) ≠ 0 := by
    intro he
    apply hactive
    change (poissonSmoothLowPass ((d.V / (L : ℝ)) * (h : ℝ) / Z) : ℂ) *
      poissonNonzeroFrequency (d.V / (L : ℝ)) x h = 0
    rw [he, Complex.ofReal_zero, zero_mul]
  have hsmall := lowPass_ne_zero_abs_lt_two hchi
  rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos hZ] at hsmall
  have hsmall' : d.V * |(h : ℝ)| < (2 * Z) * (L : ℝ) := by
    have he := mul_lt_mul_of_pos_right ((div_lt_iff₀ hZ).mp hsmall) hL
    have hid : (d.V / (L : ℝ) * |(h : ℝ)|) * (L : ℝ) =
        d.V * |(h : ℝ)| := by field_simp
    rw [hid] at he
    exact he
  have hDL := gcd_mul_shared_lcm_le hd hp hr hs hr' hs'
  change (D : ℝ) * (L : ℝ) ≤ 32 * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 at hDL
  have hbound : |(h : ℝ)| ≤
      64 * Z * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 / ((D : ℝ) * d.V) := by
    apply (le_div_iff₀ (mul_pos hD hV)).mpr
    have he := mul_lt_mul_of_pos_left hsmall' hD
    have hb := mul_le_mul_of_nonneg_left hDL (show 0 ≤ 2 * Z by positivity)
    nlinarith
  apply (mem_window_iff _ h).mpr
  refine ⟨hh0, ?_⟩
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hc : (h.natAbs : ℝ) ≤ (d.sharedSmoothFrequencyBound Z D : ℝ) := by
    rw [habs]
    exact hbound.trans (Nat.le_ceil _)
  exact_mod_cast hc

private theorem high_decay_le_product (r : ℕ) (hr : 2 ≤ r)
    {t C Z K : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hK : 0 < K) (hZK : Z ≤ K) :
    t * (C / K ^ (r + 1)) ≤
      (C / Z ^ (r - 1)) * (t / K ^ 2) := by
  have hpow : Z ^ (r - 1) * K ^ 2 ≤ K ^ (r + 1) := by
    calc
      _ ≤ K ^ (r - 1) * K ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hZ.le hZK _) (sq_nonneg _)
      _ = _ := by rw [← pow_add, show (r - 1) + 2 = r + 1 by omega]
  calc
    _ ≤ t * (C / (Z ^ (r - 1) * K ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (by positivity) hpow) ht
    _ = _ := by field_simp [hZ.ne', hK.ne']

private theorem smooth_row_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x Z : ℝ, 0 < Z →
      ∀ H : ℕ,
        (∀ h : ℤ,
          (poissonSmoothLowPass (t * (h : ℝ) / Z) : ℂ) *
              poissonNonzeroFrequency t x h ≠ 0 →
            h ∈ poissonNonzeroFrequencyWindow H) →
        ‖(∑' h : ℤ, poissonNonzeroFrequency t x h) -
          ∑ h ∈ poissonNonzeroFrequencyWindow H,
            (poissonSmoothLowPass (t * (h : ℝ) / Z) : ℂ) *
              poissonNonzeroFrequency t x h‖ ≤ C / Z ^ (r - 1) := by
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) (r + 1)
  refine ⟨2 * C, by positivity, fun t ht x Z hZ H hsupport => ?_⟩
  let f : ℤ → ℂ := poissonNonzeroFrequency t x
  let g : ℤ → ℂ := fun h => (poissonSmoothLowPass (t * (h : ℝ) / Z) : ℂ) * f h
  have hf : Summable f := (poissonNonzeroFrequency_summable_norm ht x).of_norm
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := poissonNonzeroFrequencyWindow H)
    intro h hh
    by_contra hne
    exact hh (hsupport h hne)
  have hsumg : (∑' h : ℤ, g h) =
      ∑ h ∈ poissonNonzeroFrequencyWindow H,
        (poissonSmoothLowPass (t * (h : ℝ) / Z) : ℂ) *
          poissonNonzeroFrequency t x h := by
    apply tsum_eq_sum
    intro h hh
    by_contra hne
    exact hh (hsupport h hne)
  obtain ⟨hmajor, hmajorBound⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (h : ℤ) : ‖f h - g h‖ ≤
      (C / Z ^ (r - 1)) * poissonNonzeroDecay t h := by
    by_cases hh0 : h = 0
    · subst h
      simp [f, g, poissonNonzeroFrequency, poissonNonzeroDecay]
    · by_cases hsmall : |t * (h : ℝ)| ≤ Z
      · have hone : poissonSmoothLowPass (t * (h : ℝ) / Z) = 1 := by
          apply lowPass_eq_one
          rw [abs_div, abs_of_pos hZ]
          exact (div_le_one hZ).mpr hsmall
        simp only [g, hone, Complex.ofReal_one, one_mul, sub_self, norm_zero]
        exact mul_nonneg (by positivity) (by rw [poissonNonzeroDecay, if_neg hh0]; positivity)
      · have hZK : Z ≤ 1 + |t * (h : ℝ)| := by linarith [lt_of_not_ge hsmall]
        have hchi0 := lowPass_nonneg (t * (h : ℝ) / Z)
        have hchi1 := lowPass_le_one (t * (h : ℝ) / Z)
        have hfactor : ‖(1 : ℂ) - (poissonSmoothLowPass (t * (h : ℝ) / Z) : ℂ)‖ ≤ 1 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg (by linarith : 0 ≤ 1 - poissonSmoothLowPass (t * (h : ℝ) / Z))]
          linarith
        have hnorm : ‖f h‖ ≤ t * (C / (1 + |t * (h : ℝ)|) ^ (r + 1)) := by
          dsimp only [f]
          simp only [poissonNonzeroFrequency, if_neg hh0, norm_mul, norm_smul,
            Real.norm_eq_abs, abs_of_pos ht, fourier_apply, Circle.norm_coe, mul_one]
          exact mul_le_mul_of_nonneg_left (hdecay (t * (h : ℝ))) ht.le
        calc
          _ = ‖((1 : ℂ) - (poissonSmoothLowPass (t * (h : ℝ) / Z) : ℂ)) * f h‖ := by
            congr 1
            dsimp only [g]
            ring
          _ ≤ 1 * (t * (C / (1 + |t * (h : ℝ)|) ^ (r + 1))) := by
            rw [norm_mul]
            exact mul_le_mul hfactor hnorm (norm_nonneg _) (by norm_num)
          _ = t * (C / (1 + |t * (h : ℝ)|) ^ (r + 1)) := one_mul _
          _ ≤ (C / Z ^ (r - 1)) * (t / (1 + |t * (h : ℝ)|) ^ 2) :=
            high_decay_le_product r hr ht.le hC.le hZ (by positivity) hZK
          _ = _ := by rw [poissonNonzeroDecay, if_neg hh0]
  have hmajorS : Summable (fun h : ℤ =>
      (C / Z ^ (r - 1)) * poissonNonzeroDecay t h) := hmajor.mul_left _
  have hnorm : Summable (fun h : ℤ => ‖f h - g h‖) :=
    hmajorS.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  rw [← hsumg, ← hf.tsum_sub hg]
  calc
    _ ≤ ∑' h : ℤ, ‖f h - g h‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' h : ℤ, (C / Z ^ (r - 1)) * poissonNonzeroDecay t h :=
      hnorm.tsum_le_tsum hpoint hmajorS
    _ = (C / Z ^ (r - 1)) * ∑' h : ℤ, poissonNonzeroDecay t h := tsum_mul_left
    _ ≤ (C / Z ^ (r - 1)) * 2 :=
      mul_le_mul_of_nonneg_left hmajorBound (by positivity)
    _ = _ := by ring

private theorem sum_slice_factor (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (f : (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      (d.q1SliceAtom p).transposedAtom.complexFactorGamma a * f a) =
      ∑ s ∈ factorCarrier d.Q2, ∑ r ∈ factorCarrier d.Q3,
        (d.gamma2 s * d.gamma3 r) * f (p, s, r) := by
  simp only [MediumAtom.complexFactorLabels, Finset.sum_product]
  change (∑ q ∈ factorCarrier d.Q1, ∑ s ∈ factorCarrier d.Q2,
    ∑ r ∈ factorCarrier d.Q3,
      ((if q = p then (1 : ℂ) else 0) * d.gamma2 s * d.gamma3 r) * f (q, s, r)) = _
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, one_mul]
  · intro q _ hqp
    simp only [if_neg hqp, zero_mul, Finset.sum_const_zero]
  · intro hn
    exact (hn hp).elim

private theorem sum_star_slice_factor (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (f : (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma a) * f a) =
      ∑ s ∈ factorCarrier d.Q2, ∑ r ∈ factorCarrier d.Q3,
        star (d.gamma2 s * d.gamma3 r) * f (p, s, r) := by
  calc
    _ = star (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a * star (f a)) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ s ∈ factorCarrier d.Q2, ∑ r ∈ factorCarrier d.Q3,
        (d.gamma2 s * d.gamma3 r) * star (f (p, s, r))) :=
      congrArg star (sum_slice_factor d hp _)
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem pair_sum_slice_factor (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1)
    (K : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a *
          star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * K a b) =
      ∑ s ∈ factorCarrier d.Q2, ∑ r ∈ factorCarrier d.Q3,
        ∑ s' ∈ factorCarrier d.Q2, ∑ r' ∈ factorCarrier d.Q3,
          (d.gamma2 s * d.gamma3 r) * star (d.gamma2 s' * d.gamma3 r') *
            K (p, s, r) (p, s', r') := by
  calc
    _ = ∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a *
          ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
            star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * K a b := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ s ∈ factorCarrier d.Q2, ∑ r ∈ factorCarrier d.Q3,
        (d.gamma2 s * d.gamma3 r) *
          ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
            star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * K (p, s, r) b :=
      sum_slice_factor d hp _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r _
      rw [sum_star_slice_factor d hp]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s' _
      apply Finset.sum_congr rfl
      intro r' _
      ring

private theorem slice_pair_eq_shared_series (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (N1 N2 : ℕ) :
    (d.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2 =
      ∑ r ∈ factorCarrier d.Q3, ∑ s ∈ factorCarrier d.Q2,
        ∑ r' ∈ factorCarrier d.Q3, ∑ s' ∈ factorCarrier d.Q2,
          d.gamma2 s * d.gamma3 r * star (d.gamma2 s' * d.gamma3 r') *
            (if ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 then
              (∑' h : ℤ, poissonNonzeroFrequency
                (d.V / (((p * (r * s)).lcm (p * (r' * s')) : ℕ) : ℝ))
                ((ComplexCRT.residue (p * (r * s)) (p * (r' * s')) N1 N2 d.residue : ℝ) /
                  (((p * (r * s)).lcm (p * (r' * s')) : ℕ) : ℝ)) h).re
            else 0 : ℝ) := by
  let K : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℂ := fun a b =>
    (if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) N1 N2 then
      (∑' h : ℤ, poissonNonzeroFrequency
        (d.V / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ))
        ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
          N1 N2 d.residue : ℝ) /
            ((complexFactorModulus a).lcm (complexFactorModulus b) : ℝ)) h).re
    else 0 : ℝ)
  change (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
    ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      (d.q1SliceAtom p).transposedAtom.complexFactorGamma a *
        star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * K a b) = _
  rw [pair_sum_slice_factor d hp]
  simp_rw [Finset.sum_comm (s := factorCarrier d.Q2) (t := factorCarrier d.Q3)]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro r' _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro s' _
  have hl : complexFactorModulus (p, s, r) = p * (r * s) := by
    unfold complexFactorModulus
    ring
  have hr : complexFactorModulus (p, s', r') = p * (r' * s') := by
    unfold complexFactorModulus
    ring
  dsimp only [K]
  rw [hl, hr]

private theorem pair_smooth_tail_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ p ∈ d.primitiveFirstFactorCarrier,
      ∀ Z : ℝ, 0 < Z → ∀ N1 N2 : ℕ,
        ‖(d.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2 -
          d.sharedSmallPairSmoothFrequencyKernel Z p N1 N2‖ ≤
            (((factorCarrier d.Q3).card : ℝ) * ((factorCarrier d.Q2).card : ℝ)) ^ 2 *
              C / Z ^ (r - 1) := by
  obtain ⟨C, hC, hrow⟩ := smooth_row_tail r hr
  refine ⟨C, hC, fun B sigma kappa c0 d hd p hp Z hZ N1 N2 => ?_⟩
  let E : ℝ := C / Z ^ (r - 1)
  let T : ℕ → ℕ → ℕ → ℕ → ℝ := fun a b a' b' =>
    if ComplexCRT.Compatible (p * (a * b)) (p * (a' * b')) N1 N2 then
      (∑ h ∈ poissonNonzeroFrequencyWindow
          (d.sharedSmoothFrequencyBound Z ((a * b).gcd (a' * b'))),
        (poissonSmoothLowPass
          ((d.V / (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ)) * (h : ℝ) / Z) : ℂ) *
          poissonNonzeroFrequency
            (d.V / (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ))
            ((ComplexCRT.residue (p * (a * b)) (p * (a' * b')) N1 N2 d.residue : ℝ) /
              (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ)) h).re
    else 0
  let F : ℕ → ℕ → ℕ → ℕ → ℝ := fun a b a' b' =>
    if ComplexCRT.Compatible (p * (a * b)) (p * (a' * b')) N1 N2 then
      (∑' h : ℤ, poissonNonzeroFrequency
        (d.V / (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ))
        ((ComplexCRT.residue (p * (a * b)) (p * (a' * b')) N1 N2 d.residue : ℝ) /
          (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ)) h).re
    else 0
  have hterm (a : ℕ) (ha : a ∈ factorCarrier d.Q3)
      (b : ℕ) (hb : b ∈ factorCarrier d.Q2)
      (a' : ℕ) (ha' : a' ∈ factorCarrier d.Q3)
      (b' : ℕ) (hb' : b' ∈ factorCarrier d.Q2) :
      ‖d.gamma2 b * d.gamma3 a * star (d.gamma2 b' * d.gamma3 a') * (F a b a' b' : ℂ) -
        d.gamma2 b * d.gamma3 a * star (d.gamma2 b' * d.gamma3 a') * (T a b a' b' : ℂ)‖ ≤ E := by
    by_cases hc : ComplexCRT.Compatible (p * (a * b)) (p * (a' * b')) N1 N2
    · have hp0 := factor_pos hd.2.2.1 (Finset.mem_filter.mp hp).1
      have hL : 0 < (p * (a * b)).lcm (p * (a' * b')) :=
        Nat.lcm_pos (Nat.mul_pos hp0 (Nat.mul_pos
          (factor_pos hd.2.2.2.2.1 ha) (factor_pos hd.2.2.2.1 hb)))
          (Nat.mul_pos hp0 (Nat.mul_pos
            (factor_pos hd.2.2.2.2.1 ha') (factor_pos hd.2.2.2.1 hb')))
      have hLreal : 0 < (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ) := by
        exact_mod_cast hL
      have he := hrow
        (d.V / (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ))
        (div_pos (zero_lt_one.trans_le hd.2.1) hLreal)
        ((ComplexCRT.residue (p * (a * b)) (p * (a' * b')) N1 N2 d.residue : ℝ) /
          (((p * (a * b)).lcm (p * (a' * b')) : ℕ) : ℝ)) Z hZ
        (d.sharedSmoothFrequencyBound Z ((a * b).gcd (a' * b')))
        (fun h hh => smooth_shared_frequency_support hd hZ hp ha hb ha' hb' _ h hh)
      dsimp only [F, T]
      rw [if_pos hc, if_pos hc]
      exact coeff_real_tail_norm_le _ _ _ _ E
        (tail_gamma_norm_le hd ha hb) (tail_gamma_norm_le hd ha' hb')
        (by dsimp [E]; positivity) he
    · simpa [F, T, hc] using (show (0 : ℝ) ≤ E by dsimp only [E]; positivity)
  rw [slice_pair_eq_shared_series d (Finset.mem_filter.mp hp).1]
  change ‖(∑ a ∈ factorCarrier d.Q3, ∑ b ∈ factorCarrier d.Q2,
      ∑ a' ∈ factorCarrier d.Q3, ∑ b' ∈ factorCarrier d.Q2,
        d.gamma2 b * d.gamma3 a * star (d.gamma2 b' * d.gamma3 a') * (F a b a' b' : ℂ)) -
    ∑ a ∈ factorCarrier d.Q3, ∑ b ∈ factorCarrier d.Q2,
      ∑ a' ∈ factorCarrier d.Q3, ∑ b' ∈ factorCarrier d.Q2,
        d.gamma2 b * d.gamma3 a * star (d.gamma2 b' * d.gamma3 a') * (T a b a' b' : ℂ)‖ ≤ _
  calc
    _ ≤ ((factorCarrier d.Q3).card : ℝ) * (((factorCarrier d.Q2).card : ℝ) *
        (((factorCarrier d.Q3).card : ℝ) * (((factorCarrier d.Q2).card : ℝ) * E))) :=
      norm_sum_sub_le_card _ _ _ _ (fun a ha =>
        norm_sum_sub_le_card _ _ _ _ (fun b hb =>
          norm_sum_sub_le_card _ _ _ _ (fun a' ha' =>
            norm_sum_sub_le_card _ _ _ _ (fun b' hb' => hterm a ha b hb a' ha' b' hb'))))
    _ = _ := by dsimp only [E]; ring

private theorem cleaned_core_smooth_tail_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ), 0 < sigma →
      ∀ d : MediumAtom, MediumAdmissible B sigma kappa c0 d →
        ∀ Ybeta Ysupport Z : ℝ, 0 < Z →
          ‖d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzero Ybeta Ysupport -
            d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzeroSmooth Ybeta Ysupport Z‖ ≤
              512 * C * d.scale ^ 9 / Z ^ (r - 1) := by
  obtain ⟨C, hC, hpairs⟩ := pair_smooth_tail_bound r hr
  refine ⟨C, hC, fun B sigma kappa c0 hsigma d hd Ybeta Ysupport Z hZ => ?_⟩
  let e := d.cleanedAlphaAtom
  let M : ℝ := ((factorCarrier d.Q3).card : ℝ) * ((factorCarrier d.Q2).card : ℝ)
  let E : ℝ := M ^ 2 * C / Z ^ (r - 1)
  have hE : 0 ≤ E := by dsimp only [E, M]; positivity
  have hpair (p : ℕ) (hp : p ∈ e.primitiveFirstFactorCarrier) (N1 N2 : ℕ) :
      ‖(e.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2 -
        e.sharedSmallPairSmoothFrequencyKernel Z p N1 N2‖ ≤ E := by
    exact hpairs B sigma kappa c0 e (mediumAdmissible_cleanedAlphaAtom hd) p hp Z hZ N1 N2
  let f : ℕ → ℕ → ℕ → ℂ := fun p N1 N2 =>
    if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
      e.transposedAtom.beta N1 * star (e.transposedAtom.beta N2) *
        (e.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2 else 0
  let g : ℕ → ℕ → ℕ → ℂ := fun p N1 N2 =>
    if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
      e.transposedAtom.beta N1 * star (e.transposedAtom.beta N2) *
        e.sharedSmallPairSmoothFrequencyKernel Z p N1 N2 else 0
  have hterm (p : ℕ) (hp : p ∈ e.primitiveFirstFactorCarrier) (N1 N2 : ℕ) :
      ‖f p N1 N2 - g p N1 N2‖ ≤ E := by
    dsimp only [f, g]
    split_ifs with hmask
    · rw [← mul_sub, norm_mul, norm_mul, norm_star]
      calc
        _ ≤ (1 * 1) * E := mul_le_mul
          (mul_le_mul (clean_transposed_beta_norm_le hd N1)
            (clean_transposed_beta_norm_le hd N2) (norm_nonneg _) zero_le_one)
          (hpair p hp N1 N2) (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    · simpa only [sub_self, norm_zero] using hE
  have hfinite : ‖e.sharedSmallPairedSmallSupportedNonzero Ybeta Ysupport -
      e.sharedSmallPairedSmallSupportedNonzeroSmooth Ybeta Ysupport Z‖ ≤
      (e.primitiveFirstFactorCarrier.card : ℝ) *
        ((e.transposedAtom.betaCarrier.card : ℝ) *
          ((e.transposedAtom.betaCarrier.card : ℝ) * E)) := by
    change ‖(∑ p ∈ e.primitiveFirstFactorCarrier,
        ∑ N1 ∈ e.transposedAtom.betaCarrier, ∑ N2 ∈ e.transposedAtom.betaCarrier, f p N1 N2) -
      ∑ p ∈ e.primitiveFirstFactorCarrier,
        ∑ N1 ∈ e.transposedAtom.betaCarrier, ∑ N2 ∈ e.transposedAtom.betaCarrier, g p N1 N2‖ ≤ _
    exact norm_sum_sub_le_card _ _ _ _ (fun p hp =>
      norm_sum_sub_le_card _ _ _ _ (fun N1 _ =>
        norm_sum_sub_le_card _ _ _ _ (fun N2 _ => hterm p hp N1 N2)))
  obtain ⟨hUx, _hVx, hQ1x, hQ2x, hQ3x⟩ := geometry_le_scale hd hsigma
  have hX := one_le_scale hd
  have hX0 : 0 ≤ d.scale := zero_le_one.trans hX
  have hP : (e.primitiveFirstFactorCarrier.card : ℝ) ≤ 2 * d.scale :=
    (primitive_card_le hd).trans (mul_le_mul_of_nonneg_left hQ1x (by norm_num))
  have hN : (e.transposedAtom.betaCarrier.card : ℝ) ≤ 2 * d.scale :=
    (betaCarrier_card_le (d := e.transposedAtom) hd.1).trans
      (mul_le_mul_of_nonneg_left hUx (by norm_num))
  have hQ20 : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  have hM : M ≤ 8 * d.scale ^ 3 := by
    calc
      _ ≤ (2 * d.Q3) * (2 * d.Q2) :=
        mul_le_mul (card_factorCarrier_le hd.2.2.2.2.1)
          (card_factorCarrier_le hd.2.2.2.1) (Nat.cast_nonneg _)
          (by linarith [hd.2.2.2.2.1])
      _ ≤ (2 * d.scale) * (2 * d.scale) := by gcongr
      _ = 4 * d.scale ^ 2 := by ring
      _ ≤ 4 * d.scale ^ 3 := by
        have he := mul_le_mul_of_nonneg_left hX (show 0 ≤ 4 * d.scale ^ 2 by positivity)
        nlinarith
      _ ≤ 8 * d.scale ^ 3 := mul_le_mul_of_nonneg_right
        (by norm_num : (4 : ℝ) ≤ 8) (pow_nonneg hX0 3)
  have hmass : (e.primitiveFirstFactorCarrier.card : ℝ) *
      (e.transposedAtom.betaCarrier.card : ℝ) ^ 2 * M ^ 2 ≤ 512 * d.scale ^ 9 := by
    calc
      _ ≤ (2 * d.scale) * (2 * d.scale) ^ 2 * (8 * d.scale ^ 3) ^ 2 :=
        mul_le_mul
          (mul_le_mul hP (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2)
            (sq_nonneg _) (by positivity))
          (pow_le_pow_left₀ (by dsimp only [M]; positivity) hM 2) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (e.primitiveFirstFactorCarrier.card : ℝ) *
        ((e.transposedAtom.betaCarrier.card : ℝ) *
          ((e.transposedAtom.betaCarrier.card : ℝ) * E)) := hfinite
    _ = ((e.primitiveFirstFactorCarrier.card : ℝ) *
          (e.transposedAtom.betaCarrier.card : ℝ) ^ 2 * M ^ 2) * (C / Z ^ (r - 1)) := by
      dsimp only [E]
      ring
    _ ≤ (512 * d.scale ^ 9) * (C / Z ^ (r - 1)) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by ring

end SharedFirstFactorSmallCoreSmoothFrequency

open SharedFirstFactorSmallCoreSmoothFrequency

theorem actual_smallSupported_smoothFiniteFrequency_log_payment
    (B : ℕ) (sigma kappa c0 A eta : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        let e := d.cleanedAlphaAtom
        let Y := d.scale ^ (sigma / 4)
        let Z := d.scale ^ eta
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
            ‖e.sharedSmallPairedSmallSupportedNonzero Y Y -
              e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z‖ ≤
                d.scale ^ 2 / (Real.log d.scale) ^ A := by
  dsimp only
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
  obtain ⟨C, hC, htail⟩ := cleaned_core_smooth_tail_bound r hr
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
        d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzeroSmooth
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
