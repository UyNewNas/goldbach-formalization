import ImbalancedChen.Part3SharedFirstFactorEnergyNonzeroReduction
import ImbalancedChen.Part3SharedFirstFactorLargePairedGCDNonzero
import ImbalancedChen.Part3SharedFirstFactorLargeSupportedDeletion

/-!
# The literal small paired-gcd, small-supported nonzero remainder

The full same-p complex nonzero sum is partitioned before any norm, with
the original ordered pairs, coefficients and real-projected kernel intact.
The two deleted parts are paid by the owned parents. An elementary finite
tau-four progression bound and the grouped tau-three/totient mean first
bound the cleaned signed error. This permits a unit-coefficient transfer
of its square to the original signed error.

The remaining core is not estimated here. The final constant is CE+3,
with all thresholds chosen before the varying atom and its signed residue.
A later linear error budget A requires the squared reduction and an actual
core estimate at budget 2*A.

The short local beta subpower and beta=1 row-transport arguments are
reproduced from the already owned Part3PairedAlphaDeletion and
Part3SharedFirstFactorLargePairedGCDW. No imported private name is used.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter Topology
open scoped BigOperators
open TransposedGCDPoissonMask TransposedPrimitiveUPayment
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def MediumAtom.sharedSmallPairedSmallSupportedNonzero (d : MediumAtom)
    (Ybeta Ysupport : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ N1 ∈ d.transposedAtom.betaCarrier, ∑ N2 ∈ d.transposedAtom.betaCarrier,
      if (N1.gcd N2 : ℝ) ≤ Ybeta ∧
          (CanonicalReciprocalData.supportedPart
            (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport then
        d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
          (d.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2
      else 0

/-- An exact complex partition for every real cutoff, including endpoints. -/
theorem MediumAtom.sharedFirstFactorNonzero_eq_threePairedSupportMasks
    (d : MediumAtom) (Ybeta Ysupport : ℝ) :
    (∑ p ∈ d.primitiveFirstFactorCarrier,
      (d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart) =
        d.sharedLargePairedGCDNonzero Ybeta +
          d.sharedSmallPairedLargeSupportedNonzero Ybeta Ysupport +
            d.sharedSmallPairedSmallSupportedNonzero Ybeta Ysupport := by
  unfold MediumAtom.sharedLargePairedGCDNonzero
    MediumAtom.sharedSmallPairedLargeSupportedNonzero
    MediumAtom.sharedSmallPairedSmallSupportedNonzero
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [complexCRTSmoothNonzeroPart_eq_betaPairs]
  unfold MediumAtom.commonLargeBetaGCDNonzeroPart
  have hcarrier : (d.q1SliceAtom p).transposedAtom.betaCarrier =
      d.transposedAtom.betaCarrier := rfl
  have hbeta (N : ℕ) : (d.q1SliceAtom p).transposedAtom.beta N =
      d.transposedAtom.beta N := rfl
  simp only [hcarrier, hbeta]
  change (∑ N1 ∈ d.transposedAtom.betaCarrier,
      ∑ N2 ∈ d.transposedAtom.betaCarrier,
        d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
          (d.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2) = _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N2 _
  by_cases hg : (N1.gcd N2 : ℝ) ≤ Ybeta
  · by_cases hs : (CanonicalReciprocalData.supportedPart
        (N1 / N1.gcd N2) (N1.gcd N2) : ℝ) ≤ Ysupport
    · simp only [smallPairedLargeSupportedMask, hg, hs, not_lt_of_ge hg,
        not_lt_of_ge hs, and_true, and_false, if_false, if_true, zero_add]
    · simp only [smallPairedLargeSupportedMask, hg, hs, not_lt_of_ge hg,
        lt_of_not_ge hs, and_true, and_false, if_false, if_true, zero_add, add_zero]
  · simp only [smallPairedLargeSupportedMask, hg, lt_of_not_ge hg,
      false_and, if_false, if_true, add_zero]

namespace SharedFirstFactorSmallPairedSupportedReduction

private theorem alphaCarrier_subset_prefix {d : MediumAtom} (hU : 1 ≤ d.U) :
    d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hceil : 1 ≤ Nat.ceil d.U := by exact_mod_cast hU.trans (Nat.le_ceil d.U)
  exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩

private theorem alphaCarrier_card_le {d : MediumAtom} (hU : 1 ≤ d.U) :
    (d.alphaCarrier.card : ℝ) ≤ 2 * d.U := by
  have hc := Finset.card_le_card (alphaCarrier_subset_prefix (d := d) hU)
  simp only [Nat.card_Ioc, Nat.sub_zero] at hc
  exact (show (d.alphaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
    exact_mod_cast hc).trans (Nat.floor_le (by linarith : 0 ≤ 2 * d.U))

private theorem betaCarrier_card_le {d : MediumAtom} (hV : 1 ≤ d.V) :
    (d.betaCarrier.card : ℝ) ≤ 2 * d.V := by
  have hc := Finset.card_le_card (d.betaCarrier_subset_twiceV hV)
  simp only [Nat.card_Ioc, Nat.sub_zero] at hc
  exact (show (d.betaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ) by
    exact_mod_cast hc).trans (Nat.floor_le (by linarith : 0 ≤ 2 * d.V))

private theorem beta_norm_subpower (B : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ m ∈ d.betaCarrier,
        ‖d.beta m‖ ≤ C * d.scale ^ epsilon := by
  obtain ⟨C, hC, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2 ^ B) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero B (by norm_num))) hepsilon
  refine ⟨C * (2 : ℝ) ^ epsilon, by positivity, fun sigma kappa c0 d hd m hm ↦ ?_⟩
  have hx := one_le_scale hd
  have hm' := Finset.mem_Ioc.mp (d.betaCarrier_subset_twiceV hd.2.1 hm)
  have hVx : d.V ≤ d.scale := V_le_scale hd
  have hm2 : (m : ℝ) ≤ 2 * d.scale :=
    (show (m : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ) by exact_mod_cast hm'.2).trans
      ((Nat.floor_le (by linarith [hd.2.1] : 0 ≤ 2 * d.V)).trans
        (mul_le_mul_of_nonneg_left hVx (by norm_num)))
  have hBeta : ‖d.beta m‖ ≤ (fouvryTau (2 ^ B) m : ℝ) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := hd
    exact (hb m hm).trans (by
      rw [← fouvryTau_two]
      exact_mod_cast fouvryTau_pow_le 2 B hm'.1.ne')
  calc
    _ ≤ (fouvryTau (2 ^ B) m : ℝ) := hBeta
    _ ≤ C * (m : ℝ) ^ epsilon := hbound m hm'.1
    _ ≤ C * (2 * d.scale) ^ epsilon :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hm2 hepsilon.le) hC.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ d.scale)]
      ring

private theorem absoluteRow_le_tauFour_of_not_dvd
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m n : ℕ)
    (hn : ¬(n : ℤ) ∣ d.residue) :
    d.absoluteFactorModulusRow m n ≤
      (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) := by
  let e : MediumAtom := { d with beta := fun _ ↦ 1 }
  have he : MediumAdmissible 0 sigma kappa c0 e := by
    obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
      hAlpha, hRough, _hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
    refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
      hAlpha, hRough, ?_, hGamma1, hGamma2, hGamma3⟩
    intro k _
    change ‖(1 : ℂ)‖ ≤ (k.divisors.card : ℝ) ^ 0
    norm_num
  have hgood : e.cleanedBeta n ≠ 0 := by
    change (if (n : ℤ) ∣ d.residue then (0 : ℂ) else 1) ≠ 0
    simpa only [if_neg hn] using (one_ne_zero : (1 : ℂ) ≠ 0)
  exact e.absoluteFactorModulusRow_le_tauFour he m n hgood

private theorem actual_difference_le_polynomial
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {m n : ℕ}
    (hm : m ∈ d.betaCarrier) (hn : n ∈ d.alphaCarrier) :
    (((m : ℤ) * n - d.residue).natAbs : ℝ) ≤
      7 * d.scale ^ (max 1 (1 + kappa)) := by
  have hx := one_le_scale hd
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (le_max_left (1 : ℝ) (1 + kappa))
  have haK : |(d.residue : ℝ)| ≤ d.scale ^ (max 1 (1 + kappa)) := by
    obtain ⟨_, _, _, _, _, _, _, ha, _⟩ := hd
    have ha' : |(d.residue : ℝ)| ≤ d.scale ^ (1 + kappa) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using ha
    exact ha'.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  have hm' := Finset.mem_Ioc.mp (d.betaCarrier_subset_twiceV hd.2.1 hm)
  have hn' := Finset.mem_Ioc.mp (alphaCarrier_subset_prefix hd.1 hn)
  have hmhi : (m : ℝ) ≤ 2 * d.V :=
    (show (m : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ) by exact_mod_cast hm'.2).trans
      (Nat.floor_le (by linarith [hd.2.1] : 0 ≤ 2 * d.V))
  have hnhi : (n : ℝ) ≤ 2 * d.U :=
    (show (n : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by exact_mod_cast hn'.2).trans
      (Nat.floor_le (by linarith [hd.1] : 0 ≤ 2 * d.U))
  have hmn : (m : ℝ) * n ≤ 4 * d.scale := by
    calc
      _ ≤ (2 * d.V) * (2 * d.U) :=
        mul_le_mul hmhi hnhi (Nat.cast_nonneg _) (by linarith [hd.2.1])
      _ = _ := by unfold MediumAtom.scale; ring
  calc
    _ = |(m : ℝ) * n - d.residue| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rfl
    _ ≤ |(m : ℝ) * n| + |(d.residue : ℝ)| := abs_sub _ _
    _ ≤ 4 * d.scale + d.scale ^ (max 1 (1 + kappa)) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * n)]
      exact add_le_add hmn haK
    _ ≤ _ := by linarith [Real.rpow_nonneg (zero_le_one.trans hx) (max 1 (1 + kappa))]

private theorem tauFour_difference_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ m n : ℕ,
        m ∈ d.betaCarrier → n ∈ d.alphaCarrier → ¬(n : ℤ) ∣ d.residue →
          (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) ≤
            C * d.scale ^ epsilon := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let eta : ℝ := epsilon / K
  have heta : 0 < eta := div_pos hepsilon hKpos
  have hKeta : K * eta = epsilon := by dsimp [eta]; field_simp [hKpos.ne']
  obtain ⟨D, hD, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 4) (by norm_num) heta
  refine ⟨D * (7 : ℝ) ^ eta, by positivity, fun B sigma c0 d hd m n hm hn hndiv ↦ ?_⟩
  have hne : (m : ℤ) * n - d.residue ≠ 0 := by
    intro h
    exact hndiv ⟨m, by nlinarith⟩
  have hx := one_le_scale hd
  calc
    _ ≤ D * (((m : ℤ) * n - d.residue).natAbs : ℝ) ^ eta :=
      hbound _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
    _ ≤ D * (7 * d.scale ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (actual_difference_le_polynomial hd hm hn) heta.le) hD.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7)
          (Real.rpow_nonneg (zero_le_one.trans hx) _),
        ← Real.rpow_mul (zero_le_one.trans hx), hKeta]
      ring

private theorem grouped_totient_mass_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ / q.totient) ≤
      (1 + Real.log d.physicalFactorCap) ^ 6 := by
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 3 q : ℝ) / q.totient :=
      Finset.sum_le_sum (fun q _ ↦ div_le_div_of_nonneg_right
        (d.groupedFactorGamma_norm_le_tauThree hd q) (Nat.cast_nonneg _))
    _ ≤ ∑ q ∈ Ioc 0 (Nat.floor d.physicalFactorCap), (fouvryTau 3 q : ℝ) / q.totient :=
      Finset.sum_le_sum_of_subset_of_nonneg (d.physicalFactorModuli_subset_cap hd)
        (fun _ _ _ ↦ by positivity)
    _ ≤ _ := by simpa using
      sum_fouvryTau_div_totient_le_real 3 (d.one_le_physicalFactorCap hd)

private theorem progressionRow_norm_le (d : MediumAtom) (n : ℕ)
    {A T : ℝ} (hA : 0 ≤ A)
    (hbeta : ∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ A)
    (hrow : ∀ m ∈ d.betaCarrier, d.absoluteFactorModulusRow m n ≤ T) :
    ‖d.complexProgressionRow n‖ ≤ (d.betaCarrier.card : ℝ) * A * T := by
  have he (r : ℕ × ℕ × ℕ) (m : ℕ) :
      (((n * m : ℕ) : ℤ) % (complexFactorModulus r : ℤ) =
        d.residue % (complexFactorModulus r : ℤ)) ↔
          Int.ModEq (complexFactorModulus r) ((m : ℤ) * n) d.residue := by
    simp only [Int.ModEq, Nat.cast_mul, mul_comm]
  have hterm (m : ℕ) :
      (∑ r ∈ d.complexFactorLabels,
        ‖d.complexFactorGamma r * d.beta m *
          (if (((n * m : ℕ) : ℤ) % (complexFactorModulus r : ℤ) =
            d.residue % (complexFactorModulus r : ℤ)) then (1 : ℂ) else 0)‖) =
        ‖d.beta m‖ * d.absoluteFactorModulusRow m n := by
    unfold MediumAtom.absoluteFactorModulusRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : Int.ModEq (complexFactorModulus r) ((m : ℤ) * n) d.residue
    · simp only [he r m, h, if_true, mul_one, norm_mul]
      ring
    · simp only [he r m, h, if_false, mul_zero, norm_zero]
  unfold MediumAtom.complexProgressionRow MediumAtom.complexRowLabels
  rw [Finset.sum_product, Finset.sum_comm]
  calc
    _ ≤ ∑ m ∈ d.betaCarrier, ∑ r ∈ d.complexFactorLabels,
        ‖d.complexFactorGamma r * d.beta m *
          (if (((n * m : ℕ) : ℤ) % (complexFactorModulus r : ℤ) =
            d.residue % (complexFactorModulus r : ℤ)) then (1 : ℂ) else 0)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun m _ ↦ norm_sum_le _ _)
    _ = ∑ m ∈ d.betaCarrier, ‖d.beta m‖ * d.absoluteFactorModulusRow m n :=
      Finset.sum_congr rfl (fun m _ ↦ hterm m)
    _ ≤ ∑ _m ∈ d.betaCarrier, A * T := Finset.sum_le_sum (fun m hm ↦
      mul_le_mul (hbeta m hm) (hrow m hm) (d.absoluteFactorModulusRow_nonneg m n) hA)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

private theorem principalRow_eq_grouped (d : MediumAtom) (n : ℕ) :
    d.complexPrincipalRow n =
      ∑ q ∈ d.physicalFactorModuli, d.groupedFactorGamma q *
        ((∑ m ∈ d.betaCarrier, if (n * m).Coprime q then d.beta m else 0) /
          (q.totient : ℂ)) := by
  rw [← d.sum_factorLabels_eq_grouped
    (fun q ↦ (∑ m ∈ d.betaCarrier,
      if (n * m).Coprime q then d.beta m else 0) / (q.totient : ℂ))]
  unfold MediumAtom.complexPrincipalRow MediumAtom.complexRowLabels
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : (n * m).Coprime (complexFactorModulus r)
  · simp only [if_pos h, mul_one, mul_div_assoc]
  · simp only [if_neg h, mul_zero, zero_div]

private theorem principalRow_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ)
    {A : ℝ} (hA : 0 ≤ A)
    (hbeta : ∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ A) :
    ‖d.complexPrincipalRow n‖ ≤ (d.betaCarrier.card : ℝ) * A *
      (1 + Real.log d.physicalFactorCap) ^ 6 := by
  have hmass (q : ℕ) :
      ‖∑ m ∈ d.betaCarrier, if (n * m).Coprime q then d.beta m else 0‖ ≤
        (d.betaCarrier.card : ℝ) * A := by
    calc
      _ ≤ ∑ m ∈ d.betaCarrier, ‖if (n * m).Coprime q then d.beta m else 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _m ∈ d.betaCarrier, A := by
        apply Finset.sum_le_sum
        intro m hm
        by_cases h : (n * m).Coprime q
        · simpa only [if_pos h] using hbeta m hm
        · simpa only [if_neg h, norm_zero] using hA
      _ = _ := by simp
  rw [principalRow_eq_grouped]
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli,
        ‖d.groupedFactorGamma q *
          ((∑ m ∈ d.betaCarrier, if (n * m).Coprime q then d.beta m else 0) /
            (q.totient : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ d.physicalFactorModuli,
        ‖d.groupedFactorGamma q‖ * ((d.betaCarrier.card : ℝ) * A / q.totient) := by
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul, norm_div, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hmass q) (Nat.cast_nonneg _)) (norm_nonneg _)
    _ = ((d.betaCarrier.card : ℝ) * A) *
        (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ / q.totient) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (grouped_totient_mass_le hd) (by positivity)

private theorem cleanedAlpha_signedError_finite_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {A T : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hbeta : ∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ A)
    (htau : ∀ n ∈ d.alphaCarrier, ¬(n : ℤ) ∣ d.residue →
      ∀ m ∈ d.betaCarrier,
        (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) ≤ T) :
    ‖d.cleanedAlphaAtom.signedError‖ ≤
      4 * d.scale * A * (T + (1 + Real.log d.physicalFactorCap) ^ 6) := by
  have hH : 0 ≤ (1 + Real.log d.physicalFactorCap) ^ 6 := by positivity
  have hrow (n : ℕ) (hn : n ∈ d.alphaCarrier) (hndiv : ¬(n : ℤ) ∣ d.residue) :
      ‖d.complexCenteredRow n‖ ≤ (d.betaCarrier.card : ℝ) * A *
        (T + (1 + Real.log d.physicalFactorCap) ^ 6) := by
    calc
      _ ≤ ‖d.complexProgressionRow n‖ + ‖d.complexPrincipalRow n‖ := norm_sub_le _ _
      _ ≤ (d.betaCarrier.card : ℝ) * A * T +
          (d.betaCarrier.card : ℝ) * A * (1 + Real.log d.physicalFactorCap) ^ 6 := by
        apply add_le_add (progressionRow_norm_le d n hA hbeta ?_)
          (principalRow_norm_le hd n hA hbeta)
        intro m hm
        exact (absoluteRow_le_tauFour_of_not_dvd hd m n hndiv).trans (htau n hn hndiv m hm)
      _ = _ := by ring
  rw [d.cleanedAlphaAtom.signedError_eq_complexCenteredRows]
  change ‖∑ n ∈ d.alphaCarrier, d.cleanedAlpha n * d.complexCenteredRow n‖ ≤ _
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier, ‖d.cleanedAlpha n‖ * ‖d.complexCenteredRow n‖ := by
      simpa only [norm_mul] using (norm_sum_le d.alphaCarrier
        (fun n ↦ d.cleanedAlpha n * d.complexCenteredRow n))
    _ ≤ ∑ _n ∈ d.alphaCarrier, (d.betaCarrier.card : ℝ) * A *
        (T + (1 + Real.log d.physicalFactorCap) ^ 6) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hz : d.cleanedAlpha n = 0
      · simp only [hz, norm_zero, zero_mul]
        positivity
      · have ha : ‖d.cleanedAlpha n‖ ≤ 1 := by
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ :=
            mediumAdmissible_cleanedAlphaAtom hd
          exact hAlpha n hn
        have hr := hrow n hn (d.cleanedAlpha_ne_zero_not_dvd hz)
        exact (mul_le_mul ha hr (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = ((d.alphaCarrier.card : ℝ) * (d.betaCarrier.card : ℝ)) * A *
        (T + (1 + Real.log d.physicalFactorCap) ^ 6) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((2 * d.U) * (2 * d.V)) * A *
        (T + (1 + Real.log d.physicalFactorCap) ^ 6) := by
      apply mul_le_mul_of_nonneg_right _ (add_nonneg hT hH)
      apply mul_le_mul_of_nonneg_right _ hA
      exact mul_le_mul (alphaCarrier_card_le hd.1) (betaCarrier_card_le hd.2.1)
        (Nat.cast_nonneg _) (by linarith [hd.1])
    _ = _ := by unfold MediumAtom.scale; ring

private theorem cleanedAlpha_signedError_crude_subpower
    (B : ℕ) (sigma kappa c0 : ℝ) (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        ‖d.cleanedAlphaAtom.signedError‖ ≤ C * d.scale ^ (1 + sigma / 4) := by
  have he : 0 < sigma / 8 := by linarith
  obtain ⟨Cb, hCb, hbeta⟩ := beta_norm_subpower B he
  obtain ⟨Ct, hCt, htau⟩ := tauFour_difference_subpower kappa he
  obtain ⟨x0, hx0, hlogs⟩ := eventually_actual_log_cost_le_rpow 0 6 sigma hsigma he
  refine ⟨4 * Cb * (Ct + 1), by positivity, x0, hx0, fun d hd hx ↦ ?_⟩
  have hX : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hlog : (1 + Real.log d.physicalFactorCap) ^ 6 ≤ d.scale ^ (sigma / 8) := by
    simpa only [pow_zero, one_mul] using hlogs B kappa c0 d hd hx
  calc
    _ ≤ 4 * d.scale * (Cb * d.scale ^ (sigma / 8)) *
        (Ct * d.scale ^ (sigma / 8) + (1 + Real.log d.physicalFactorCap) ^ 6) :=
      cleanedAlpha_signedError_finite_bound hd (by positivity) (by positivity)
        (hbeta sigma kappa c0 d hd)
        (fun n hn hndiv m hm ↦ htau B sigma c0 d hd m n hm hn hndiv)
    _ ≤ 4 * d.scale * (Cb * d.scale ^ (sigma / 8)) *
        (Ct * d.scale ^ (sigma / 8) + d.scale ^ (sigma / 8)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) (by positivity)
    _ = (4 * Cb * (Ct + 1)) *
        (d.scale ^ (1 : ℝ) * d.scale ^ (sigma / 8) * d.scale ^ (sigma / 8)) := by
      rw [Real.rpow_one]
      ring
    _ = _ := by
      rw [← Real.rpow_add hX, ← Real.rpow_add hX]
      congr 2
      ring

private theorem abs_norm_sq_sub_norm_sq_le (z w : ℂ) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ (2 * ‖w‖ + ‖z - w‖) * ‖z - w‖ := by
  have hz : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - w) w
  have hw : ‖w‖ ≤ ‖z - w‖ + ‖z‖ := by
    simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le (w - z) z
  have hdiff : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ = |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) := by
      rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ ‖z - w‖ * (‖z‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_right hdiff (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖z - w‖ * (2 * ‖w‖ + ‖z - w‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = _ := mul_comm _ _

end SharedFirstFactorSmallPairedSupportedReduction

open SharedFirstFactorSmallPairedSupportedReduction

/-- The original square differs from the cleaned square by one log budget.
The new finite crude bound is proved above, without any SW or core bound. -/
theorem actual_signedError_sq_cleanedAlpha_sq_difference_log_payment
    (B : ℕ) (sigma kappa c0 A : ℝ) (hsigma : 0 < sigma) (hc0 : 0 < c0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        |‖d.signedError‖ ^ 2 - ‖d.cleanedAlphaAtom.signedError‖ ^ 2| ≤
          d.scale ^ 2 / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, xC, hxC, hclean⟩ :=
    cleanedAlpha_signedError_crude_subpower B sigma kappa c0 hsigma
  obtain ⟨D, hD, xD, _hxD, hdelta⟩ :=
    PairedAlphaDeletion.signedError_sub_cleanAlpha_power_bound B sigma kappa c0 hsigma hc0
  obtain ⟨xP, hxP⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget (2 * C * D + D ^ 2) A
      (by positivity) (by linarith : 0 < sigma / 4))
  refine ⟨max xC (max xD xP), hxC.trans_le (le_max_left _ _), fun d hd hx ↦ ?_⟩
  have hX1 := one_le_scale hd
  have hX : 0 < d.scale := zero_lt_one.trans_le hX1
  have ht := hclean d hd ((le_max_left _ _).trans hx)
  have he := hdelta d hd
    ((le_max_left xD xP).trans ((le_max_right xC (max xD xP)).trans hx))
  have hpower : |‖d.signedError‖ ^ 2 - ‖d.cleanedAlphaAtom.signedError‖ ^ 2| ≤
      (2 * C * D + D ^ 2) * d.scale ^ (2 - sigma / 4) := by
    calc
      _ ≤ (2 * ‖d.cleanedAlphaAtom.signedError‖ +
          ‖d.signedError - d.cleanedAlphaAtom.signedError‖) *
            ‖d.signedError - d.cleanedAlphaAtom.signedError‖ :=
        abs_norm_sq_sub_norm_sq_le _ _
      _ ≤ (2 * (C * d.scale ^ (1 + sigma / 4)) +
          D * d.scale ^ (1 - sigma / 2)) * (D * d.scale ^ (1 - sigma / 2)) :=
        mul_le_mul
          (add_le_add (mul_le_mul_of_nonneg_left ht (by norm_num)) he)
          he (norm_nonneg _) (by positivity)
      _ = (2 * C * D) *
          (d.scale ^ (1 + sigma / 4) * d.scale ^ (1 - sigma / 2)) +
            D ^ 2 * (d.scale ^ (1 - sigma / 2) * d.scale ^ (1 - sigma / 2)) := by ring
      _ = (2 * C * D) * d.scale ^ (2 - sigma / 4) +
          D ^ 2 * d.scale ^ (2 - sigma) := by
        rw [← Real.rpow_add hX, ← Real.rpow_add hX,
          show 1 + sigma / 4 + (1 - sigma / 2) = 2 - sigma / 4 by ring,
          show 1 - sigma / 2 + (1 - sigma / 2) = 2 - sigma by ring]
      _ ≤ (2 * C * D) * d.scale ^ (2 - sigma / 4) +
          D ^ 2 * d.scale ^ (2 - sigma / 4) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : 2 - sigma ≤ 2 - sigma / 4))
          (sq_nonneg D))
      _ = _ := by ring
  exact hpower.trans (hxP d.scale
    ((le_max_right xD xP).trans ((le_max_right xC (max xD xP)).trans hx)))

/-- Both deleted nonzero aggregates are paid with the original outside L2
factors. The support parent pays all three of its separate norms. -/
theorem actual_betaL2_gamma1L2_cleaned_deletedPairedSupportedNonzero_log_payment
    (B : ℕ) (sigma kappa c0 A : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          (‖d.cleanedAlphaAtom.sharedLargePairedGCDNonzero
              (d.scale ^ (sigma / 4))‖ +
            ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero
              (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4))‖) ≤
                2 * (d.scale ^ 2 / (Real.log d.scale) ^ A) := by
  obtain ⟨xL, hxL, hlarge⟩ :=
    actual_betaL2_gamma1L2_cleaned_sharedLargePairedGCDNonzero_log_payment
      B sigma kappa c0 A hsigma
  obtain ⟨xS, _hxS, hsupported⟩ :=
    actual_betaL2_gamma1L2_cleaned_sharedLargeSupported_log_payment
      B sigma kappa c0 A hsigma
  refine ⟨max xL xS, hxL.trans_le (le_max_left _ _), fun d hd hx ↦ ?_⟩
  let W : ℝ := (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)
  let Y : ℝ := d.scale ^ (sigma / 4)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hL := hlarge d hd ((le_max_left _ _).trans hx)
  have hS := hsupported d hd ((le_max_right _ _).trans hx) Y
  have hN : W * ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero Y Y‖ ≤
      d.scale ^ 2 / (Real.log d.scale) ^ A := by
    calc
      _ ≤ W * (‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Y Y‖ +
          ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero Y Y‖ +
            ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero Y Y‖) :=
        mul_le_mul_of_nonneg_left (by
          linarith [norm_nonneg (d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Y Y),
            norm_nonneg (d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero Y Y)]) hW
      _ ≤ _ := hS
  calc
    _ = W * ‖d.cleanedAlphaAtom.sharedLargePairedGCDNonzero Y‖ +
        W * ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero Y Y‖ := mul_add _ _ _
    _ ≤ d.scale ^ 2 / (Real.log d.scale) ^ A +
        d.scale ^ 2 / (Real.log d.scale) ^ A := add_le_add hL hN
    _ = _ := by ring

/-- The original family reduces to the literal cleaned small core with
coefficient one. No spectral estimate of this core is a premise. -/
theorem uniformAuxiliarySW_signedError_sq_le_cleanedSmallPairedSupportedNonzero_add_log_payment
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1 / 100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma / 100)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i : ι, x0 ≤ (F i).scale →
          ‖(F i).signedError‖ ^ 2 ≤
            (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
              (∑ p ∈ (F i).primitiveFirstFactorCarrier, ‖(F i).gamma1 p‖ ^ 2) *
                ((F i).cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzero
                  ((F i).scale ^ (sigma / 4)) ((F i).scale ^ (sigma / 4))).re +
                    C * (F i).scale ^ 2 / (Real.log (F i).scale) ^ A := by
  intro A hA
  have hcleanAdmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i).cleanedAlphaAtom :=
    fun i ↦ mediumAdmissible_cleanedAlphaAtom (hadmissible i)
  have hcleanSW := PairedAlphaDeletion.uniformAuxiliarySW_cleanedAlphaAtom
    F B C0 sigma kappa c0 hsigma hc0 hadmissible hSW
  obtain ⟨CE, hCE, xE, hxE, henergy⟩ :=
    uniformAuxiliarySW_sharedFirstFactor_signedError_sq_le_nonzero_add_log_payment
      (fun i ↦ (F i).cleanedAlphaAtom) B C0 sigma kappa c0
      hsigma hsigma_small hc0 hkappa hkappa_small hcleanAdmissible hcleanSW A hA
  obtain ⟨xD, _hxD, hdeleted⟩ :=
    actual_betaL2_gamma1L2_cleaned_deletedPairedSupportedNonzero_log_payment
      B sigma kappa c0 A hsigma
  obtain ⟨xC, _hxC, hcleanSquare⟩ :=
    actual_signedError_sq_cleanedAlpha_sq_difference_log_payment
      B sigma kappa c0 A hsigma hc0
  refine ⟨CE + 3, by linarith, max xE (max xD xC),
    hxE.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  let d := F i
  let W : ℝ := (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)
  let Y : ℝ := d.scale ^ (sigma / 4)
  let L : ℂ := d.cleanedAlphaAtom.sharedLargePairedGCDNonzero Y
  let S : ℂ := d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero Y Y
  let K : ℂ := d.cleanedAlphaAtom.sharedSmallPairedSmallSupportedNonzero Y Y
  let P : ℝ := d.scale ^ 2 / (Real.log d.scale) ^ A
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hE := henergy i ((le_max_left _ _).trans hx)
  change ‖d.cleanedAlphaAtom.signedError‖ ^ 2 ≤
    W * (∑ p ∈ d.cleanedAlphaAtom.primitiveFirstFactorCarrier,
      (d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart).re +
        CE * d.scale ^ 2 / (Real.log d.scale) ^ A at hE
  rw [d.cleanedAlphaAtom.sharedFirstFactorNonzero_eq_threePairedSupportMasks Y Y,
    Complex.add_re, Complex.add_re] at hE
  have hD := hdeleted d (hadmissible i)
    ((le_max_left xD xC).trans ((le_max_right xE (max xD xC)).trans hx))
  have hC := hcleanSquare d (hadmissible i)
    ((le_max_right xD xC).trans ((le_max_right xE (max xD xC)).trans hx))
  have hRe : W * (L.re + S.re) ≤ 2 * P := by
    calc
      _ ≤ W * (‖L‖ + ‖S‖) := mul_le_mul_of_nonneg_left
        (add_le_add ((le_abs_self L.re).trans (Complex.abs_re_le_norm L))
          ((le_abs_self S.re).trans (Complex.abs_re_le_norm S))) hW
      _ ≤ _ := hD
  have hEC : ‖d.cleanedAlphaAtom.signedError‖ ^ 2 ≤
      W * K.re + CE * d.scale ^ 2 / (Real.log d.scale) ^ A + 2 * P := by
    calc
      _ ≤ W * (L.re + S.re + K.re) +
          CE * d.scale ^ 2 / (Real.log d.scale) ^ A := hE
      _ = (W * K.re + CE * d.scale ^ 2 / (Real.log d.scale) ^ A) +
          W * (L.re + S.re) := by ring
      _ ≤ _ := add_le_add le_rfl hRe
  have hOriginal : ‖d.signedError‖ ^ 2 ≤ ‖d.cleanedAlphaAtom.signedError‖ ^ 2 + P := by
    have hdiff := (le_abs_self
      (‖d.signedError‖ ^ 2 - ‖d.cleanedAlphaAtom.signedError‖ ^ 2)).trans hC
    linarith
  change ‖d.signedError‖ ^ 2 ≤ W * K.re +
    (CE + 3) * d.scale ^ 2 / (Real.log d.scale) ^ A
  calc
    _ ≤ ‖d.cleanedAlphaAtom.signedError‖ ^ 2 + P := hOriginal
    _ ≤ (W * K.re + CE * d.scale ^ 2 / (Real.log d.scale) ^ A + 2 * P) + P :=
      add_le_add hEC le_rfl
    _ = _ := by dsimp only [P]; ring

end

end ImbalancedChen.Part3
