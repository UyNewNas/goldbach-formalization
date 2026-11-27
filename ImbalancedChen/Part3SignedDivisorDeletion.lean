import ImbalancedChen.Part3ActualLargeGCDBetaMass

/-!
# Actual signed-error preprocessing before complex dispersion

The original beta is split into its signed-divisor part and the existing
cleanedBeta. This is an exact identity for the original signedError, with
the same complex factor labels, residue, interval and primitive center.

The finite deleted-mass argument follows fixed goldbach
09b97db5764ade1246bfb77206baa1b124760958,
LiLiuPrereqFouvryBetaClean.lean:73-95, SHA256
c4678d4d8bd0dbb2f014f8dfd0285a1995e3d5286fde9f8bf830a397f54b3891.
Only its finite divisor inclusion is adapted below; no unbuilt external
preprocessing or analytic-estimate chain is imported.

The actual medium geometry is stronger than needed for divisor deletion:
U*(Q1*Q2*Q3) < scale^(1-9*sigma). Thus a complete finite kernel norm
bound pays every exact product as well, without using a nonzero-difference
divisor bound at zero. Nonzero residue is proved from the genuine caller's
0<c0, not from MediumAdmissible with an arbitrary c0.

After this linear budget is paid, dispersion is applied to cleanedBetaAtom.
No estimate of the old quadratic commonLargeBetaGCDException is asserted.
The cleaned atom retains its own literal W-2V+U primitive center.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def MediumAtom.divisorBeta (d : MediumAtom) (n : ℕ) : ℂ :=
  if (n : ℤ) ∣ d.residue then d.beta n else 0

def MediumAtom.divisorBetaAtom (d : MediumAtom) : MediumAtom :=
  { d with beta := d.divisorBeta }

theorem MediumAtom.beta_eq_clean_add_divisorBeta (d : MediumAtom) (n : ℕ) :
    d.beta n = d.cleanedBeta n + d.divisorBeta n := by
  by_cases h : (n : ℤ) ∣ d.residue <;>
    simp [MediumAtom.cleanedBeta, MediumAtom.divisorBeta, h]

/-- Exact linear preprocessing on the original physical labels and center. -/
theorem MediumAtom.signedError_eq_clean_add_divisorBeta (d : MediumAtom) :
    d.signedError = d.cleanedBetaAtom.signedError + d.divisorBetaAtom.signedError := by
  conv_lhs =>
    unfold MediumAtom.signedError MediumAtom.discrepancy
    simp only [d.beta_eq_clean_add_divisorBeta]
  simp only [MediumAtom.signedError, MediumAtom.discrepancy,
    MediumAtom.cleanedBetaAtom, MediumAtom.divisorBetaAtom,
    MediumAtom.alphaCarrier, MediumAtom.betaCarrier,
    mul_add, add_mul, Finset.sum_add_distrib]
  rfl

theorem MediumAtom.signedError_sub_clean_eq_divisorBeta (d : MediumAtom) :
    d.signedError - d.cleanedBetaAtom.signedError = d.divisorBetaAtom.signedError := by
  rw [d.signedError_eq_clean_add_divisorBeta]
  ring

theorem mediumAdmissible_cleanedBetaAtom
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    MediumAdmissible B sigma kappa c0 d.cleanedBetaAtom := by
  obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, ?_, hGamma1, hGamma2, hGamma3⟩
  intro n hn
  change ‖d.cleanedBeta n‖ ≤ (n.divisors.card : ℝ) ^ B
  by_cases h : (n : ℤ) ∣ d.residue
  · simp only [MediumAtom.cleanedBeta, if_pos h, norm_zero]
    positivity
  · simpa only [MediumAtom.cleanedBeta, if_neg h] using hBeta n hn

theorem mediumAdmissible_divisorBetaAtom
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    MediumAdmissible B sigma kappa c0 d.divisorBetaAtom := by
  obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, ?_, hGamma1, hGamma2, hGamma3⟩
  intro n hn
  change ‖d.divisorBeta n‖ ≤ (n.divisors.card : ℝ) ^ B
  by_cases h : (n : ℤ) ∣ d.residue
  · simpa only [MediumAtom.divisorBeta, if_pos h] using hBeta n hn
  · simp only [MediumAtom.divisorBeta, if_neg h, norm_zero]
    positivity

/-- Alpha and its exact auxiliary primitive mean are untouched by cleaning. -/
theorem uniformAuxiliarySW_cleanedBetaAtom {ι : Type*} (F : ι → MediumAtom) (C0 : ℕ)
    (h : UniformAuxiliarySW F C0) :
    UniformAuxiliarySW (fun i ↦ (F i).cleanedBetaAtom) C0 := h

private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

/-- This uses the existing positive c0 of RestrictedMediumObligation. -/
theorem mediumAdmissible_residue_ne_zero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hc0 : 0 < c0) (hd : MediumAdmissible B sigma kappa c0 d) : d.residue ≠ 0 := by
  have hx : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  obtain ⟨_, _, _, _, _, _, ha, _⟩ := hd
  intro h
  rw [h, Int.natAbs_zero, Nat.cast_zero] at ha
  exact (not_le_of_gt (mul_pos hc0 hx)) ha

private theorem card_factorCarrier_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ((factorCarrier Q).card : ℝ) ≤ 2 * Q := by
  have hsub : factorCarrier Q ⊆ Ioc 0 (Nat.floor (2 * Q)) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
    exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show ((factorCarrier Q).card : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by
    exact_mod_cast hcard).trans (Nat.floor_le (by linarith))

private theorem card_alphaCarrier_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : (d.alphaCarrier.card : ℝ) ≤ 2 * d.U := by
  have hs : d.alphaCarrier ⊆ factorCarrier d.U := Finset.filter_subset _ _
  exact (show (d.alphaCarrier.card : ℝ) ≤ ((factorCarrier d.U).card : ℝ) by
    exact_mod_cast Finset.card_le_card hs).trans (card_factorCarrier_le hd.1)

private theorem card_complexFactorLabels_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.complexFactorLabels.card : ℝ) ≤ d.physicalFactorCap := by
  obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
  simp only [MediumAtom.complexFactorLabels, Finset.card_product, Nat.cast_mul]
  calc
    _ ≤ (2 * d.Q1) * ((2 * d.Q2) * (2 * d.Q3)) := by
      gcongr
      · exact card_factorCarrier_le hQ1
      · exact card_factorCarrier_le hQ2
      · exact card_factorCarrier_le hQ3
    _ = _ := by unfold MediumAtom.physicalFactorCap; ring

private theorem gamma_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {r : ℕ × ℕ × ℕ}
    (hr : r ∈ d.complexFactorLabels) : ‖d.complexFactorGamma r‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  obtain ⟨hr1, hr23⟩ := Finset.mem_product.mp hr
  obtain ⟨hr2, hr3⟩ := Finset.mem_product.mp hr23
  rw [MediumAtom.complexFactorGamma, norm_mul, norm_mul]
  calc
    _ ≤ 1 * 1 * 1 :=
      mul_le_mul (mul_le_mul (h1 _ hr1).1 (h2 _ hr2).1 (norm_nonneg _) zero_le_one)
        (h3 _ hr3).1 (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Total division also covers the unused modulus-zero convention. -/
private theorem primitiveKernel_norm_le_two (a : ℤ) (q m n : ℕ) :
    ‖complexPrimitiveKernel a q m n‖ ≤ 2 := by
  have hi : ‖(if (((m * n : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ))
      then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> norm_num
  have hj : ‖(if (m * n).Coprime q then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hdiv : ‖(if (m * n).Coprime q then (1 : ℂ) else 0) /
      (Nat.totient q : ℂ)‖ ≤ 1 := by
    by_cases hphi : q.totient = 0
    · simp only [hphi, Nat.cast_zero, div_zero, norm_zero, zero_le_one]
    · have hphiR : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hphi
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_self (norm_nonneg _) hphiR).trans hj
  exact (norm_sub_le _ _).trans (by linarith [add_le_add hi hdiv])

private theorem signedError_norm_le_finite_betaMass
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ≤ 2 * (d.alphaCarrier.card : ℝ) * (d.complexFactorLabels.card : ℝ) *
      ∑ n ∈ d.betaCarrier, ‖d.beta n‖ := by
  have hAlpha : ∀ m ∈ d.alphaCarrier, ‖d.alpha m‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  rw [d.signedError_eq_complexCenteredRows]
  calc
    _ ≤ ∑ m ∈ d.alphaCarrier, ‖d.alpha m * d.complexCenteredRow m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ d.alphaCarrier, ∑ l ∈ d.complexRowLabels, 2 * ‖d.beta l.2‖ := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, MediumAtom.complexCenteredRow_eq_sum]
      calc
        _ ≤ 1 * ∑ l ∈ d.complexRowLabels, ‖d.complexRowContribution m l‖ :=
          mul_le_mul (hAlpha m hm) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
        _ ≤ _ := by
          rw [one_mul]
          apply Finset.sum_le_sum
          intro l hl
          rw [MediumAtom.complexRowContribution, norm_mul, norm_mul]
          calc
            _ ≤ 1 * ‖d.beta l.2‖ * 2 :=
              mul_le_mul (mul_le_mul_of_nonneg_right
                (gamma_norm_le_one hd (Finset.mem_product.mp hl).1) (norm_nonneg _))
                (primitiveKernel_norm_le_two _ _ _ _) (norm_nonneg _) (by positivity)
            _ = _ := by ring
    _ = _ := by
      simp only [MediumAtom.complexRowLabels, Finset.sum_product, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring

/-- A literal finite norm budget for the original signed-error deletion. -/
theorem MediumAtom.signedError_sub_clean_norm_le_finite
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError - d.cleanedBetaAtom.signedError‖ ≤
      4 * d.U * d.physicalFactorCap * ∑ n ∈ d.betaCarrier, ‖d.divisorBeta n‖ := by
  rw [d.signedError_sub_clean_eq_divisorBeta]
  have hb := signedError_norm_le_finite_betaMass (mediumAdmissible_divisorBetaAtom hd)
  change ‖d.divisorBetaAtom.signedError‖ ≤ _ at hb
  calc
    _ ≤ 2 * (d.alphaCarrier.card : ℝ) * (d.complexFactorLabels.card : ℝ) *
        ∑ n ∈ d.betaCarrier, ‖d.divisorBeta n‖ := hb
    _ ≤ 2 * (2 * d.U) * d.physicalFactorCap *
        ∑ n ∈ d.betaCarrier, ‖d.divisorBeta n‖ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (card_alphaCarrier_le hd) (by norm_num))
        (card_complexFactorLabels_le hd) (Nat.cast_nonneg _) (by linarith [hd.1])
    _ = _ := by ring

/-- Finite divisor inclusion, on the original signed residue. -/
theorem MediumAtom.divisorBetaMass_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (ha : d.residue ≠ 0) :
    (∑ n ∈ d.betaCarrier, ‖d.divisorBeta n‖) ≤
      (fouvryTau (2 ^ B + 1) d.residue.natAbs : ℝ) := by
  have hBeta : ∀ n ∈ d.betaCarrier, ‖d.beta n‖ ≤ (fouvryTau (2 ^ B) n : ℝ) := by
    intro n hn
    have hnpos := (Finset.mem_Ioc.mp (d.betaCarrier_subset_twiceV hd.2.1 hn)).1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := hd
    exact (hb n hn).trans (by
      rw [← fouvryTau_two]
      exact_mod_cast fouvryTau_pow_le 2 B hnpos.ne')
  calc
    _ = ∑ n ∈ d.betaCarrier.filter (fun n : ℕ ↦ (n : ℤ) ∣ d.residue), ‖d.beta n‖ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : (n : ℤ) ∣ d.residue <;> simp [MediumAtom.divisorBeta, h]
    _ ≤ ∑ n ∈ d.betaCarrier.filter (fun n : ℕ ↦ (n : ℤ) ∣ d.residue),
        (fouvryTau (2 ^ B) n : ℝ) :=
      Finset.sum_le_sum (fun n hn ↦ hBeta n (Finset.mem_filter.mp hn).1)
    _ ≤ ∑ n ∈ d.residue.natAbs.divisors, (fouvryTau (2 ^ B) n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Nat.mem_divisors.mpr
          ⟨Int.natCast_dvd.mp (Finset.mem_filter.mp hn).2, Int.natAbs_ne_zero.mpr ha⟩
      · intro n _ _
        positivity
    _ = _ := by rw [fouvryTau_succ, Nat.cast_sum]

/-- The two actual medium monomials pay the complete label count times U. -/
theorem MediumAtom.U_mul_physicalFactorCap_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.U * d.physicalFactorCap ≤ 8 * d.scale ^ (1 - 9 * sigma) := by
  have hx : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  obtain ⟨hU, _, hQ1, hQ2, hQ3, _, _, _, hg1, hg2, _⟩ := hd
  have hQ3sq : d.Q3 ≤ d.Q3 ^ 2 := by nlinarith
  have hfirst : d.U * d.Q1 * d.Q2 * d.Q3 ^ 2 <
      (d.U ^ 2 * d.Q2 * d.Q3 ^ 2) * d.scale ^ (-sigma) := by
    calc
      _ = d.Q1 * (d.U * d.Q2 * d.Q3 ^ 2) := by ring
      _ < (d.U * d.scale ^ (-sigma)) * (d.U * d.Q2 * d.Q3 ^ 2) :=
        mul_lt_mul_of_pos_right hg1 (by positivity)
      _ = _ := by ring
  have hprod : d.U * d.Q1 * d.Q2 * d.Q3 ≤ d.scale ^ (1 - 9 * sigma) := by
    apply le_of_lt
    calc
      _ ≤ d.U * d.Q1 * d.Q2 * d.Q3 ^ 2 :=
        mul_le_mul_of_nonneg_left hQ3sq (by positivity)
      _ < (d.U ^ 2 * d.Q2 * d.Q3 ^ 2) * d.scale ^ (-sigma) := hfirst
      _ < d.scale ^ (1 - 8 * sigma) * d.scale ^ (-sigma) :=
        mul_lt_mul_of_pos_right hg2 (Real.rpow_pos_of_pos hx _)
      _ = d.scale ^ (1 - 9 * sigma) := by
        rw [← Real.rpow_add hx, show 1 - 8 * sigma + -sigma = 1 - 9 * sigma by ring]
  calc
    _ = 8 * (d.U * d.Q1 * d.Q2 * d.Q3) := by unfold MediumAtom.physicalFactorCap; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num)

/-- B is fixed before the subpower constant; the residue still moves through
the original polynomial range and kappa may be any fixed real number. -/
theorem divisorBetaMass_subpower (B : ℕ) (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma c0 : ℝ) (d : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 d →
        (∑ n ∈ d.betaCarrier, ‖d.divisorBeta n‖) ≤ C * d.scale ^ epsilon := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := by linarith
  let eta : ℝ := epsilon / K
  have heta : 0 < eta := div_pos hepsilon hKpos
  have hKeta : K * eta = epsilon := by dsimp [eta]; field_simp [hKpos.ne']
  obtain ⟨C, hC, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2 ^ B + 1) (by exact Nat.succ_le_succ (Nat.zero_le (2 ^ B))) heta
  refine ⟨C, hC, fun sigma c0 d hc0 hd ↦ ?_⟩
  have ha := mediumAdmissible_residue_ne_zero hc0 hd
  have hx := one_le_scale hd
  have hraw := d.divisorBetaMass_le_tau hd ha
  obtain ⟨_, _, _, _, _, _, _, hres, _⟩ := hd
  have haK : (d.residue.natAbs : ℝ) ≤ d.scale ^ K :=
    hres.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  calc
    _ ≤ (fouvryTau (2 ^ B + 1) d.residue.natAbs : ℝ) := hraw
    _ ≤ C * (d.residue.natAbs : ℝ) ^ eta := hbound _ (Int.natAbs_pos.mpr ha)
    _ ≤ C * (d.scale ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) haK heta.le) hC.le
    _ = C * d.scale ^ epsilon := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ d.scale), hKeta]

/-- The signed-divisor deletion has a true fixed power saving at the
original complete scale. It uses no SW or distribution estimate. -/
theorem signedError_sub_clean_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hc0 : 0 < c0) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d →
        ‖d.signedError - d.cleanedBetaAtom.signedError‖ ≤
          C * d.scale ^ (1 - 8 * sigma) := by
  obtain ⟨C, hC, hmass⟩ := divisorBetaMass_subpower B kappa hsigma
  refine ⟨32 * C, by positivity, fun d hd ↦ ?_⟩
  have hx : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  calc
    _ ≤ 4 * d.U * d.physicalFactorCap *
        ∑ n ∈ d.betaCarrier, ‖d.divisorBeta n‖ := d.signedError_sub_clean_norm_le_finite hd
    _ = 4 * (d.U * d.physicalFactorCap) *
        ∑ n ∈ d.betaCarrier, ‖d.divisorBeta n‖ := by ring
    _ ≤ 4 * (8 * d.scale ^ (1 - 9 * sigma)) * (C * d.scale ^ sigma) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (d.U_mul_physicalFactorCap_le hd) (by norm_num))
        (hmass sigma c0 d hc0 hd) (by positivity) (by positivity)
    _ = (32 * C) * (d.scale ^ (1 - 9 * sigma) * d.scale ^ sigma) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx, show 1 - 9 * sigma + sigma = 1 - 8 * sigma by ring]

private theorem eventually_const_rpow_le_logBudget (C A : ℝ) (hC : 0 ≤ C)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ x : ℝ in atTop, C * x ^ (1 - delta) ≤ x / (Real.log x) ^ A := by
  have hO := isLittleO_log_rpow_rpow_atTop A hdelta
  have hb := (hO.const_mul_left C).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hpay : C * (Real.log x) ^ A ≤ x ^ delta := by
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ C * (Real.log x) ^ A),
      abs_of_nonneg (Real.rpow_nonneg hx0.le delta)] using hx
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < Real.log x) A)).mpr
  calc
    _ = (C * (Real.log x) ^ A) * x ^ (1 - delta) := by ring
    _ ≤ x ^ delta * x ^ (1 - delta) :=
      mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hx0.le _)
    _ = x := by
      rw [← Real.rpow_add hx0, show delta + (1 - delta) = 1 by ring, Real.rpow_one]

/-- One threshold precedes every atom and its moving signed residue. -/
theorem signedError_sub_clean_log_payment (B : ℕ) (sigma kappa c0 A : ℝ)
    (hsigma : 0 < sigma) (hc0 : 0 < c0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        ‖d.signedError - d.cleanedBetaAtom.signedError‖ ≤
          d.scale / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, hbound⟩ := signedError_sub_clean_power_bound B sigma kappa c0 hsigma hc0
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp
    (eventually_const_rpow_le_logBudget C A hC.le (by linarith : 0 < 8 * sigma))
  refine ⟨max 2 x0, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro d hd hx
  exact (hbound d hd).trans (hx0 _ ((le_max_right _ _).trans hx))

/-- Dispersion is now run on the same cleaned atom. Its own literal W-2V+U
is retained; the only added term is the original linear deletion error. -/
theorem MediumAtom.signedError_norm_sq_le_cleanedDispersion_add_deletion
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ^ 2 ≤
      2 * (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ ^ 2) *
        (d.cleanedBetaAtom.complexDispersionW d.commonSmoothCarrier d.commonSmoothWeight -
          2 * d.cleanedBetaAtom.complexDispersionV d.commonSmoothCarrier d.commonSmoothWeight +
            d.cleanedBetaAtom.complexDispersionU d.commonSmoothCarrier d.commonSmoothWeight) +
        2 * ‖d.signedError - d.cleanedBetaAtom.signedError‖ ^ 2 := by
  have hclean := d.cleanedBetaAtom.signedError_norm_sq_le_commonSmoothDispersion
    (mediumAdmissible_cleanedBetaAtom hd)
  have htri : ‖d.signedError‖ ≤ ‖d.cleanedBetaAtom.signedError‖ +
      ‖d.signedError - d.cleanedBetaAtom.signedError‖ := by
    calc
      _ = ‖d.cleanedBetaAtom.signedError + (d.signedError - d.cleanedBetaAtom.signedError)‖ := by
        congr 1
        ring
      _ ≤ _ := norm_add_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  change ‖d.cleanedBetaAtom.signedError‖ ^ 2 ≤
    (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ ^ 2) *
      (d.cleanedBetaAtom.complexDispersionW d.commonSmoothCarrier d.commonSmoothWeight -
        2 * d.cleanedBetaAtom.complexDispersionV d.commonSmoothCarrier d.commonSmoothWeight +
          d.cleanedBetaAtom.complexDispersionU d.commonSmoothCarrier d.commonSmoothWeight) at hclean
  nlinarith [sq_nonneg (‖d.cleanedBetaAtom.signedError‖ -
    ‖d.signedError - d.cleanedBetaAtom.signedError‖)]

/-- A true caller bridge: proving the target for the actual cleaned family
proves it for the original family, with the deleted beta already paid. -/
theorem restrictedMediumTarget_of_cleanedBetaTarget {ι : Type*}
    (F : ι → MediumAtom) (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hc0 : 0 < c0)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hclean : RestrictedMediumTarget (fun i ↦ (F i).cleanedBetaAtom)) :
    RestrictedMediumTarget F := by
  intro A hA
  obtain ⟨C, hC, x1, hx1, hbound⟩ := hclean A hA
  obtain ⟨x2, _hx2, hdelete⟩ := signedError_sub_clean_log_payment B sigma kappa c0 A hsigma hc0
  refine ⟨C + 1, by linarith, max x1 x2, lt_of_lt_of_le hx1 (le_max_left _ _), ?_⟩
  intro i hx
  have hcleani := hbound i ((le_max_left _ _).trans hx)
  have hdeleti := hdelete (F i) (hadmissible i) ((le_max_right _ _).trans hx)
  calc
    ‖(F i).signedError‖ = ‖(F i).cleanedBetaAtom.signedError +
        ((F i).signedError - (F i).cleanedBetaAtom.signedError)‖ := by
      congr 1
      ring
    _ ≤ ‖(F i).cleanedBetaAtom.signedError‖ +
        ‖(F i).signedError - (F i).cleanedBetaAtom.signedError‖ := norm_add_le _ _
    _ ≤ C * (F i).scale / (Real.log (F i).scale) ^ A +
        (F i).scale / (Real.log (F i).scale) ^ A := add_le_add hcleani hdeleti
    _ = _ := by ring

/-- The quadratic union exception is exactly zero for the actual cleaned
atom. This makes no assertion about that exception for the original beta. -/
theorem MediumAtom.commonLargeBetaGCDException_cleanedBetaAtom_eq_zero
    (d : MediumAtom) (Y : ℝ) :
    d.cleanedBetaAtom.commonLargeBetaGCDException Y = 0 := by
  unfold MediumAtom.commonLargeBetaGCDException
  apply Finset.sum_eq_zero
  intro n₁ _
  apply Finset.sum_eq_zero
  intro n₂ _
  by_cases h : (n₁ : ℤ) ∣ d.residue ∨ (n₂ : ℤ) ∣ d.residue
  · rcases h with h | h
    · simp [MediumAtom.cleanedBetaAtom, MediumAtom.cleanedBeta, h]
    · simp [MediumAtom.cleanedBetaAtom, MediumAtom.cleanedBeta, h]
  · have hclean : ¬((n₁ : ℤ) ∣ d.cleanedBetaAtom.residue ∨
        (n₂ : ℤ) ∣ d.cleanedBetaAtom.residue) := by
      change ¬((n₁ : ℤ) ∣ d.residue ∨ (n₂ : ℤ) ∣ d.residue)
      exact h
    simp only [if_neg hclean, ite_self]

/-- The first gcd exclusion for the same cleaned W is now free of the
original union exception, at the original U,V and polynomial residue scale. -/
theorem commonLargeBetaGCDW_cleaned_polynomial_residue_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ, 0 < Y →
        ‖d.cleanedBetaAtom.commonLargeBetaGCDW Y‖ ≤
          C * d.U * d.scale ^ epsilon *
            ((2 * d.V) ^ 2 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
              Real.sqrt ((1 + Real.log (2 * d.V)) / Y)) := by
  obtain ⟨C, hC, hbound⟩ := commonLargeBetaGCDW_polynomial_residue_largeGCD_bound kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y hY ↦ ?_⟩
  have hb := hbound B sigma c0 d.cleanedBetaAtom (mediumAdmissible_cleanedBetaAtom hd) Y hY
  have hU : d.cleanedBetaAtom.U = d.U := rfl
  have hV : d.cleanedBetaAtom.V = d.V := rfl
  have hscale : d.cleanedBetaAtom.scale = d.scale := rfl
  simpa only [d.commonLargeBetaGCDException_cleanedBetaAtom_eq_zero Y,
    norm_zero, add_zero, hU, hV, hscale] using hb

end

end ImbalancedChen.Part3
