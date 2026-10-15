import ImbalancedChen.Part3PairedAlphaDeletion
import ImbalancedChen.Part3TransposedGCDPoissonMask

/-!
# Actual large paired gcd in the full transposed Fourier remainder

Original alpha is cleaned by the separately proved linear signed-error
budget. This makes every contributing paired index a nondivisor of the
original signed moving residue. Whole W and raw zero retain the same gcd
mask, and only their exact difference is called the Fourier remainder.

The auxiliary beta=1 atom below has the ORIGINAL U/V geometry, alpha and
gamma coefficients. It genuinely satisfies MediumAdmissible at B=0.
It is used only to consume the already proved absolute modulus-row bound,
which is independent of beta. No transposed admissibility is asserted.

Actual support gives m<=3V and n<=2U, so the differences are controlled
by 7*X^max(1,1+kappa). Fixed-order divisor subpower bounds therefore pay
the whole-W masked kernel. The raw-zero masked kernel and k=1 pair mass
come from the preceding actual finite leaf. The final inequality includes
the original outside beta-L2 and all remaining logarithm costs.

All imports are local; no unbuilt external Weil, phase or W-estimate
chain is imported. Local parents must be owned before runtime validation.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace TransposedLargeGCDFourier

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

/-- Whole factor-pair weight is normed first. The original geometry
supplies all row and polynomial-difference bounds at original V/U. -/
theorem transposed_factorPair_norm_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ n₁ n₂ : ℕ,
        n₁ ∈ d.transposedAtom.betaCarrier → n₂ ∈ d.transposedAtom.betaCarrier →
          ¬(n₁ : ℤ) ∣ d.residue → ¬(n₂ : ℤ) ∣ d.residue →
            ‖d.transposedAtom.commonFactorPairWeight n₁ n₂‖ ≤
              C * d.V * d.scale ^ epsilon := by
  obtain ⟨C, hC, hbound⟩ := tauFour_difference_subpower kappa hepsilon
  refine ⟨5 * C ^ 2, by positivity, fun B sigma c0 d hd n₁ n₂ hn₁ hn₂ hnd₁ hnd₂ ↦ ?_⟩
  have hx := one_le_scale hd
  have hrow (m n : ℕ) : d.transposedAtom.absoluteFactorModulusRow m n =
      d.absoluteFactorModulusRow m n := rfl
  apply (d.transposedAtom.commonFactorPairWeight_norm_le n₁ n₂).trans
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        d.transposedAtom.commonSmoothWeight m * (C ^ 2 * d.scale ^ epsilon) := by
      apply Finset.sum_le_sum
      intro m _
      rw [hrow, hrow]
      by_cases hm : d.transposedAtom.commonSmoothWeight m = 0
      · simp only [hm, zero_mul, le_refl]
      have h1 := (absoluteRow_le_tauFour_of_not_dvd hd m n₁ hnd₁).trans
        (hbound B sigma c0 d hd m n₁ hn₁ hm hnd₁)
      have h2 := (absoluteRow_le_tauFour_of_not_dvd hd m n₂ hnd₂).trans
        (hbound B sigma c0 d hd m n₂ hn₂ hm hnd₂)
      have hp : d.absoluteFactorModulusRow m n₁ * d.absoluteFactorModulusRow m n₂ ≤
          C ^ 2 * d.scale ^ epsilon := by
        calc
          _ ≤ (C * d.scale ^ (epsilon / 2)) * (C * d.scale ^ (epsilon / 2)) :=
            mul_le_mul h1 h2 (d.absoluteFactorModulusRow_nonneg m n₂) (by positivity)
          _ = _ := by
            rw [mul_mul_mul_comm, ← Real.rpow_add (by linarith : 0 < d.scale),
              show epsilon / 2 + epsilon / 2 = epsilon by ring, pow_two]
      exact (show _ = d.transposedAtom.commonSmoothWeight m *
        (d.absoluteFactorModulusRow m n₁ * d.absoluteFactorModulusRow m n₂) by ring).trans_le
          (mul_le_mul_of_nonneg_left hp (d.transposedAtom.commonSmoothWeight_nonneg m))
    _ = (∑ m ∈ d.transposedAtom.commonSmoothCarrier, d.transposedAtom.commonSmoothWeight m) *
        (C ^ 2 * d.scale ^ epsilon) := (Finset.sum_mul _ _ _).symm
    _ ≤ (5 * d.V) * (C ^ 2 * d.scale ^ epsilon) :=
      mul_le_mul_of_nonneg_right (transposed_smoothWeight_sum_le hd) (by positivity)
    _ = _ := by ring

/-- Actual alpha cleaning supplies BOTH nonzero-difference gates. There
is no quadratic signed-divisor exception left in this new masked W. -/
theorem cleanedAlpha_transposed_largeW_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ,
        ‖d.cleanedAlphaAtom.transposedAtom.commonLargeBetaGCDW Y‖ ≤
          C * d.V * d.scale ^ epsilon * d.cleanedAlphaAtom.transposedLargePairMass Y := by
  obtain ⟨C, hC, hbound⟩ := transposed_factorPair_norm_subpower kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y ↦ ?_⟩
  have hclean := mediumAdmissible_cleanedAlphaAtom hd
  unfold MediumAtom.commonLargeBetaGCDW MediumAtom.transposedLargePairMass
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₁ hn₁
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n₂ hn₂
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy, norm_mul, norm_star]
    by_cases h1 : d.cleanedAlphaAtom.transposedAtom.beta n₁ = 0
    · simp only [h1, norm_zero, zero_mul, mul_zero, le_refl]
    by_cases h2 : d.cleanedAlphaAtom.transposedAtom.beta n₂ = 0
    · simp only [h2, norm_zero, mul_zero, zero_mul, le_refl]
    calc
      _ ≤ (‖d.cleanedAlphaAtom.transposedAtom.beta n₁‖ *
          ‖d.cleanedAlphaAtom.transposedAtom.beta n₂‖) * (C * d.V * d.scale ^ epsilon) :=
        mul_le_mul_of_nonneg_left
          (hbound B sigma c0 d.cleanedAlphaAtom hclean n₁ n₂ hn₁ hn₂
            (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h1)
            (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h2))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  · simp only [if_neg hy, norm_zero, mul_zero, le_refl]

/-- Whole W and raw zero are paid under the same mask before the full
signed Fourier remainder is bounded. Every actual coefficient remains. -/
theorem cleanedAlpha_transposed_largeNonzero_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ, 0 < Y →
        ‖d.cleanedAlphaAtom.transposedAtom.commonLargeBetaGCDNonzeroPart Y‖ ≤
          (C * d.V * d.scale ^ epsilon +
            |d.V * CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19) *
              ((2 * d.U) ^ 2 * Real.sqrt ((1 + Real.log (2 * d.U)) / Y)) := by
  obtain ⟨C, hC, hbound⟩ := cleanedAlpha_transposed_largeW_bound kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y hY ↦ ?_⟩
  have hclean := mediumAdmissible_cleanedAlphaAtom hd
  have hx := one_le_scale hd
  have hmass := TransposedGCDPoissonMask.transposed_largePairMass_le hclean hY
  have hW := (hbound B sigma c0 d hd Y).trans
    (mul_le_mul_of_nonneg_left hmass (by positivity [hd.2.1]))
  have hZ := (TransposedGCDPoissonMask.transposed_largeZero_norm_le_pairMass hclean Y).trans
    (mul_le_mul_of_nonneg_left hmass (by
      have := Real.log_nonneg (d.one_le_physicalFactorCap hd)
      positivity))
  apply (TransposedGCDPoissonMask.transposed_largeNonzero_norm_le_W_add_zero hclean Y).trans
  calc
    _ ≤ (C * d.V * d.scale ^ epsilon) *
        ((2 * d.U) ^ 2 * Real.sqrt ((1 + Real.log (2 * d.U)) / Y)) +
        (|d.V * CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19) *
          ((2 * d.U) ^ 2 * Real.sqrt ((1 + Real.log (2 * d.U)) / Y)) := add_le_add hW hZ
    _ = _ := by ring

/-- The actual original beta second moment is outside Cauchy. Its full
fixed log cost is paid at original 2V; X remains U*V throughout. -/
theorem betaL2_mul_cleanedAlpha_largeNonzero_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ, 0 < Y →
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.cleanedAlphaAtom.transposedAtom.commonLargeBetaGCDNonzeroPart Y‖ ≤
            8 * (C * d.scale ^ epsilon +
              |CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19) *
                d.scale ^ 2 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
                  Real.sqrt ((1 + Real.log (2 * d.U)) / Y) := by
  obtain ⟨C, hC, hbound⟩ := cleanedAlpha_transposed_largeNonzero_bound kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y hY ↦ ?_⟩
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hlogV : 0 ≤ 1 + Real.log (2 * d.V) :=
    by linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  calc
    _ ≤ (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        ((C * d.V * d.scale ^ epsilon +
          |d.V * CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19) *
            ((2 * d.U) ^ 2 * Real.sqrt ((1 + Real.log (2 * d.U)) / Y))) :=
      mul_le_mul (mediumAdmissible_beta_norm_sq_sum_le hd)
        (hbound B sigma c0 d hd Y hY) (norm_nonneg _) (by positivity)
    _ = _ := by rw [abs_mul, abs_of_nonneg hV]; unfold MediumAtom.scale; ring

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
    1 + Real.log (2 * d.U) ≤ (2 + Real.log 8) * Real.log d.scale ∧
    1 + Real.log (2 * d.V) ≤ (2 + Real.log 8) * Real.log d.scale ∧
    1 + Real.log d.physicalFactorCap ≤ (2 + Real.log 8) * Real.log d.scale := by
  have hx1 := one_le_scale hd
  have hx0 : 0 < d.scale := zero_lt_one.trans_le hx1
  have hUx : d.U ≤ d.scale := le_mul_of_one_le_right (by linarith [hd.1]) hd.2.1
  have hVx : d.V ≤ d.scale := le_mul_of_one_le_left (by linarith [hd.2.1]) hd.1
  have hcapx : d.physicalFactorCap ≤ 8 * d.scale :=
    (PairedAlphaDeletion.actual_geometry_bounds hd).2.2.trans
      (mul_le_mul_of_nonneg_left (by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
          (show 1 - 10 * sigma ≤ 1 by linarith)) (by norm_num))
  refine ⟨log_bound_from_scale hx0 hlog (by linarith [hd.1]) ?_,
    log_bound_from_scale hx0 hlog (by linarith [hd.2.1]) ?_,
    log_bound_from_scale hx0 hlog (zero_lt_one.trans_le (d.one_le_physicalFactorCap hd)) hcapx⟩
  · nlinarith
  · nlinarith

/-- Choosing an actual positive-power gcd cutoff pays this entire full
Fourier piece after the real original beta-L2 factor. The threshold is
uniform in the atom and its polynomially moving signed residue. -/
theorem betaL2_mul_cleanedAlpha_largeNonzero_log_payment
    (B : ℕ) (sigma kappa c0 A delta : ℝ) (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.cleanedAlphaAtom.transposedAtom.commonLargeBetaGCDNonzeroPart (d.scale ^ delta)‖ ≤
            d.scale ^ 2 / Real.log d.scale ^ A := by
  obtain ⟨C, hC, hbound⟩ := betaL2_mul_cleanedAlpha_largeNonzero_bound kappa
    (by linarith : 0 < delta / 8)
  let p : ℕ := (2 ^ B) ^ 2 - 1
  let N : ℕ := p + 20
  let D : ℝ := 2 + Real.log 8
  let E : ℝ := 8 * (C + |CommonSmoothCutoff.cutoffMass|) * D ^ N
  have hD : 1 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hevent : ∀ᶠ x : ℝ in atTop,
      E * Real.log x ^ (A + (N : ℝ)) ≤ x ^ (3 * delta / 8) := by
    have hb := ((isLittleO_log_rpow_rpow_atTop (A + (N : ℝ))
      (by linarith : 0 < 3 * delta / 8)).const_mul_left E).bound
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
    fun d hd hx ↦ ?_⟩
  have hxScale := one_le_scale hd
  have hx0 : 0 < d.scale := zero_lt_one.trans_le hxScale
  have hlog : 1 ≤ Real.log d.scale := hx2 ((le_max_right x1 x2).trans
    ((le_max_right 2 (max x1 x2)).trans hx))
  have hlog0 : 0 < Real.log d.scale := by linarith
  let Q : ℝ := D * Real.log d.scale
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    simpa only [one_mul] using mul_le_mul hD hlog zero_le_one (by linarith : 0 ≤ D)
  have hQ0 : 0 ≤ Q := by linarith
  obtain ⟨hU, hV, hcap⟩ := actual_log_bounds hsigma hd hlog
  change 1 + Real.log (2 * d.U) ≤ Q at hU
  change 1 + Real.log (2 * d.V) ≤ Q at hV
  change 1 + Real.log d.physicalFactorCap ≤ Q at hcap
  have hU1 : 1 ≤ 1 + Real.log (2 * d.U) :=
    by linarith [Real.log_nonneg (show 1 ≤ 2 * d.U by linarith [hd.1])]
  have hV0 : 0 ≤ 1 + Real.log (2 * d.V) :=
    by linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hcap0 : 0 ≤ 1 + Real.log d.physicalFactorCap :=
    by linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  have hxEps : 1 ≤ d.scale ^ (delta / 8) := Real.one_le_rpow hxScale (by linarith)
  have hCoeff : C * d.scale ^ (delta / 8) +
      |CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19 ≤
        (C + |CommonSmoothCutoff.cutoffMass|) * d.scale ^ (delta / 8) * Q ^ 19 := by
    have h1 : C * d.scale ^ (delta / 8) ≤ C * d.scale ^ (delta / 8) * Q ^ 19 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hQ)
    have h2 : |CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19 ≤
        |CommonSmoothCutoff.cutoffMass| * d.scale ^ (delta / 8) * Q ^ 19 := by
      calc
        _ ≤ |CommonSmoothCutoff.cutoffMass| * Q ^ 19 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcap0 hcap 19) (abs_nonneg _)
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right (abs_nonneg _) hxEps) (pow_nonneg hQ0 19)
    nlinarith
  have hSqrt : Real.sqrt ((1 + Real.log (2 * d.U)) / d.scale ^ delta) ≤
      Q / d.scale ^ (delta / 2) := by
    have hs : Real.sqrt (d.scale ^ delta) = d.scale ^ (delta / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le,
        show delta * (1 / (2 : ℝ)) = delta / 2 by ring]
    rw [Real.sqrt_div (by linarith : 0 ≤ 1 + Real.log (2 * d.U)), hs]
    exact div_le_div_of_nonneg_right
      ((Real.sqrt_le_self_iff.mpr (Or.inr hU1)).trans hU)
      (Real.rpow_nonneg hx0.le _)
  have hBeta := pow_le_pow_left₀ hV0 hV p
  have hAB := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hCoeff (by norm_num : (0 : ℝ) ≤ 8)) (sq_nonneg d.scale)
  have hABBeta := mul_le_mul hAB hBeta (pow_nonneg hV0 p) (by positivity)
  have hQprod : Q ^ 19 * Q ^ p * Q = Q ^ N := by
    rw [← pow_add, ← pow_succ]
    congr 1
    dsimp [N]
    omega
  have hpay : E * d.scale ^ (delta / 8) * Real.log d.scale ^ N /
      d.scale ^ (delta / 2) ≤ 1 / Real.log d.scale ^ A := by
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hx0 _)
      (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ = d.scale ^ (delta / 8) * (E * Real.log d.scale ^ (A + (N : ℝ))) := by
        rw [Real.rpow_add hlog0, Real.rpow_natCast]
        ring
      _ ≤ d.scale ^ (delta / 8) * d.scale ^ (3 * delta / 8) :=
        mul_le_mul_of_nonneg_left (hx1 ((le_max_left x1 x2).trans
          ((le_max_right 2 (max x1 x2)).trans hx))) (by positivity)
      _ = _ := by rw [← Real.rpow_add hx0,
        show delta / 8 + 3 * delta / 8 = delta / 2 by ring, one_mul]
  calc
    _ ≤ 8 * (C * d.scale ^ (delta / 8) +
        |CommonSmoothCutoff.cutoffMass| * (1 + Real.log d.physicalFactorCap) ^ 19) *
        d.scale ^ 2 * (1 + Real.log (2 * d.V)) ^ p *
          Real.sqrt ((1 + Real.log (2 * d.U)) / d.scale ^ delta) :=
      hbound B sigma c0 d hd _ (Real.rpow_pos_of_pos hx0 delta)
    _ ≤ 8 * ((C + |CommonSmoothCutoff.cutoffMass|) * d.scale ^ (delta / 8) * Q ^ 19) *
        d.scale ^ 2 * Q ^ p * (Q / d.scale ^ (delta / 2)) :=
      mul_le_mul hABBeta hSqrt (Real.sqrt_nonneg _) (by positivity)
    _ = d.scale ^ 2 * (8 * (C + |CommonSmoothCutoff.cutoffMass|) *
        d.scale ^ (delta / 8) * (Q ^ 19 * Q ^ p * Q) / d.scale ^ (delta / 2)) := by ring
    _ = d.scale ^ 2 * (E * d.scale ^ (delta / 8) * Real.log d.scale ^ N /
        d.scale ^ (delta / 2)) := by
      rw [hQprod]
      dsimp only [Q, E]
      rw [mul_pow]
      ring
    _ ≤ d.scale ^ 2 * (1 / Real.log d.scale ^ A) :=
      mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
    _ = _ := by ring

end TransposedLargeGCDFourier

end

end ImbalancedChen.Part3
