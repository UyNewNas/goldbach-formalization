import ImbalancedChen.Part3SignedDivisorDeletion
import ImbalancedChen.Part3TransposedDispersion

/-!
# Actual original-alpha divisor deletion before transposed dispersion

The signed-divisor part is removed from original alpha, the paired
coefficient of the transposed dispersion. All original physical labels,
the signed moving residue, the common interval and primitive mean remain.

The finite progression count is adapted from fixed goldbach
09b97db5764ade1246bfb77206baa1b124760958,
LiLiuPrereqFouvryWLargeDeltaOriginal.card_product_modEq_le. Its elementary
injection is reproduced using the already imported public Nat.ModEq
coprime cancellation. The unbuilt original-W chain is not imported.
The fixed source SHA256 is
0498ebeecfc1d1ba71d76416864db8777f6213fca9c2a7647161b5adbbfb8c38.

Only a linear signed-error deletion budget is asserted here. It does not
bound the old quadratic union exception or identify any literal V/U term.
The actual grouped coefficient is bounded by tau_3, with reciprocal,
ordinary and reciprocal-totient costs H^3, cap*H^2 and H^6. Fixed-order
subpower bounds and the original medium gates pay X^(1-sigma/2), then
every requested logarithm. The positive c0 caller proves a is nonzero.
Each auxiliary SW error changes by at most twice the same deleted mass;
U>=X^sigma absorbs it while preserving the original fixed order C0.
The cleaned distribution target itself remains a separate obligation.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def MediumAtom.cleanedAlpha (d : MediumAtom) (n : ℕ) : ℂ :=
  if (n : ℤ) ∣ d.residue then 0 else d.alpha n

def MediumAtom.divisorAlpha (d : MediumAtom) (n : ℕ) : ℂ :=
  if (n : ℤ) ∣ d.residue then d.alpha n else 0

def MediumAtom.cleanedAlphaAtom (d : MediumAtom) : MediumAtom :=
  { d with alpha := d.cleanedAlpha }

def MediumAtom.divisorAlphaAtom (d : MediumAtom) : MediumAtom :=
  { d with alpha := d.divisorAlpha }

theorem MediumAtom.alpha_eq_clean_add_divisorAlpha (d : MediumAtom) (n : ℕ) :
    d.alpha n = d.cleanedAlpha n + d.divisorAlpha n := by
  by_cases h : (n : ℤ) ∣ d.residue <;>
    simp [MediumAtom.cleanedAlpha, MediumAtom.divisorAlpha, h]

theorem MediumAtom.signedError_eq_clean_add_divisorAlpha (d : MediumAtom) :
    d.signedError = d.cleanedAlphaAtom.signedError + d.divisorAlphaAtom.signedError := by
  conv_lhs =>
    unfold MediumAtom.signedError MediumAtom.discrepancy
    simp only [d.alpha_eq_clean_add_divisorAlpha]
  simp only [MediumAtom.signedError, MediumAtom.discrepancy,
    MediumAtom.cleanedAlphaAtom, MediumAtom.divisorAlphaAtom,
    MediumAtom.alphaCarrier, MediumAtom.betaCarrier,
    mul_add, add_mul, Finset.sum_add_distrib]
  rfl

theorem MediumAtom.signedError_sub_cleanAlpha_eq_divisorAlpha (d : MediumAtom) :
    d.signedError - d.cleanedAlphaAtom.signedError = d.divisorAlphaAtom.signedError := by
  rw [d.signedError_eq_clean_add_divisorAlpha]
  ring

theorem mediumAdmissible_cleanedAlphaAtom
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    MediumAdmissible B sigma kappa c0 d.cleanedAlphaAtom := by
  obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    ?_, ?_, hBeta, hGamma1, hGamma2, hGamma3⟩
  · intro n hn
    change ‖d.cleanedAlpha n‖ ≤ 1
    by_cases h : (n : ℤ) ∣ d.residue
    · simp only [MediumAtom.cleanedAlpha, if_pos h, norm_zero, zero_le_one]
    · simpa only [MediumAtom.cleanedAlpha, if_neg h] using hAlpha n hn
  · intro n hn hnz p hp hpn
    apply hRough n hn _ p hp hpn
    change d.cleanedAlpha n ≠ 0 at hnz
    by_cases h : (n : ℤ) ∣ d.residue
    · exact (hnz (by simp only [MediumAtom.cleanedAlpha, if_pos h])).elim
    · simpa only [MediumAtom.cleanedAlpha, if_neg h] using hnz

theorem MediumAtom.cleanedAlpha_ne_zero_not_dvd {d : MediumAtom} {n : ℕ}
    (hn : d.cleanedAlpha n ≠ 0) : ¬(n : ℤ) ∣ d.residue := by
  intro h
  exact hn (by simp only [MediumAtom.cleanedAlpha, if_pos h])

/-- This is the actual coefficient paired by the new dispersion. -/
theorem MediumAtom.cleanedAlpha_transposedBeta_ne_zero_not_dvd {d : MediumAtom} {n : ℕ}
    (hn : d.cleanedAlphaAtom.transposedAtom.beta n ≠ 0) : ¬(n : ℤ) ∣ d.residue := by
  change (if n ∈ d.alphaCarrier then d.cleanedAlpha n else 0) ≠ 0 at hn
  by_cases hm : n ∈ d.alphaCarrier
  · exact d.cleanedAlpha_ne_zero_not_dvd (by simpa only [if_pos hm] using hn)
  · exact (hn (by simp only [if_neg hm])).elim

namespace PairedAlphaDeletion

private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

/-- Positive product progressions occupy at most one point of each
quotient block; the residue remains an arbitrary signed integer. -/
theorem card_product_modEq_le (K q n : ℕ) (a : ℤ) (hn : n.Coprime q) :
    ((Icc 0 K).filter (fun m : ℕ ↦ Int.ModEq q ((m : ℤ) * n) a)).card ≤
      K / q + 1 := by
  calc
    _ ≤ (range (K / q + 1)).card := by
      apply card_le_card_of_injOn (fun m : ℕ ↦ m / q)
      · intro m hm
        exact mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hm).1).2))
      · intro m hm b hb he
        apply Nat.ext_div_modEq he
        apply Nat.ModEq.cancel_right_of_coprime hn.symm
        apply Int.natCast_modEq_iff.mp
        simpa only [Nat.cast_mul] using
          (mem_filter.mp hm).2.trans (mem_filter.mp hb).2.symm
    _ = _ := card_range _

theorem betaCarrier_progression_card_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {q n : ℕ} (hq : 0 < q) (hn : n.Coprime q) :
    ((d.betaCarrier.filter
      (fun m : ℕ ↦ Int.ModEq q ((m : ℤ) * n) d.residue)).card : ℝ) ≤
        2 * d.V / q + 1 := by
  have hsub : d.betaCarrier.filter
      (fun m : ℕ ↦ Int.ModEq q ((m : ℤ) * n) d.residue) ⊆
      (Icc 0 (Nat.floor (2 * d.V))).filter
        (fun m : ℕ ↦ Int.ModEq q ((m : ℤ) * n) d.residue) := by
    intro m hm
    obtain ⟨hm, hap⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, (mem_Icc.mp hm).2⟩, hap⟩
  calc
    _ ≤ (Nat.floor (2 * d.V) / q + 1 : ℕ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans
        (card_product_modEq_le (Nat.floor (2 * d.V)) q n d.residue hn)
    _ ≤ (Nat.floor (2 * d.V) : ℝ) / q + 1 := by
      push_cast
      exact add_le_add_right Nat.cast_div_le 1
    _ ≤ _ := add_le_add_right
      (div_le_div_of_nonneg_right (Nat.floor_le (by linarith : 0 ≤ 2 * d.V))
        (by exact_mod_cast hq.le)) 1

private theorem active_factor_coprime_residue
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {a : ℕ × ℕ × ℕ}
    (ha : a ∈ d.complexFactorLabels) (hgamma : d.complexFactorGamma a ≠ 0) :
    (complexFactorModulus a).Coprime d.residue.natAbs := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  obtain ⟨ha1, ha23⟩ := Finset.mem_product.mp ha
  obtain ⟨ha2, ha3⟩ := Finset.mem_product.mp ha23
  have hg : d.gamma1 a.1 * d.gamma2 a.2.1 * d.gamma3 a.2.2 ≠ 0 := hgamma
  obtain ⟨hg12, hg3⟩ := mul_ne_zero_iff.mp hg
  obtain ⟨hg1, hg2⟩ := mul_ne_zero_iff.mp hg12
  exact (((h1 a.1 ha1).2 hg1).mul_left ((h2 a.2.1 ha2).2 hg2)).mul_left
    ((h3 a.2.2 ha3).2 hg3)

private theorem active_grouped_coprime_residue
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {q : ℕ}
    (hg : d.groupedFactorGamma q ≠ 0) : q.Coprime d.residue.natAbs := by
  by_contra hc
  apply hg
  unfold MediumAtom.groupedFactorGamma
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha, hq⟩ := Finset.mem_filter.mp ha
  by_contra hga
  exact hc (hq ▸ active_factor_coprime_residue hd ha hga)

/-- The divisor part has actual finite alpha mass bounded by tau_2(a). -/
theorem divisorAlphaMass_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (ha : d.residue ≠ 0) :
    (∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖) ≤
      (fouvryTau 2 d.residue.natAbs : ℝ) := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  calc
    _ = ∑ n ∈ d.alphaCarrier.filter (fun n : ℕ ↦ (n : ℤ) ∣ d.residue), ‖d.alpha n‖ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : (n : ℤ) ∣ d.residue <;> simp [MediumAtom.divisorAlpha, h]
    _ ≤ ∑ _n ∈ d.alphaCarrier.filter (fun n : ℕ ↦ (n : ℤ) ∣ d.residue), (1 : ℝ) :=
      Finset.sum_le_sum (fun n hn ↦ hAlpha n (Finset.mem_filter.mp hn).1)
    _ ≤ ∑ _n ∈ d.residue.natAbs.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Nat.mem_divisors.mpr
          ⟨Int.natCast_dvd.mp (Finset.mem_filter.mp hn).2, Int.natAbs_ne_zero.mpr ha⟩
      · intro n _ _
        positivity
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, fouvryTau_two]

private theorem betaCarrier_card_le {d : MediumAtom} (hV : 1 ≤ d.V) :
    (d.betaCarrier.card : ℝ) ≤ 2 * d.V := by
  have hc := Finset.card_le_card (d.betaCarrier_subset_twiceV hV)
  simp only [Nat.card_Ioc, Nat.sub_zero] at hc
  exact (show (d.betaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ) by
    exact_mod_cast hc).trans (Nat.floor_le (by linarith : 0 ≤ 2 * d.V))

private theorem norm_sum_ite_le_card (S : Finset ℕ) (beta : ℕ → ℂ)
    (p : ℕ → Prop) [DecidablePred p] {A : ℝ}
    (hbeta : ∀ m ∈ S, ‖beta m‖ ≤ A) :
    ‖∑ m ∈ S, if p m then beta m else 0‖ ≤ A * ((S.filter p).card : ℝ) := by
  calc
    _ ≤ ∑ m ∈ S, if p m then A else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      by_cases hp : p m
      · simpa only [if_pos hp] using hbeta m hm
      · simp only [if_neg hp, norm_zero, le_refl]
    _ = _ := by rw [← Finset.sum_filter]; simp [mul_comm]

private theorem betaKernelMass_norm_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {q n : ℕ} (hq : 0 < q) (hn : n.Coprime q)
    {A : ℝ} (hA : 0 ≤ A) (hbeta : ∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ A) :
    ‖∑ m ∈ d.betaCarrier, d.beta m * complexPrimitiveKernel d.residue q n m‖ ≤
      A * (2 * d.V / q + 1 + 2 * d.V / q.totient) := by
  have hterm (m : ℕ) :
      d.beta m * complexPrimitiveKernel d.residue q n m =
      (if Int.ModEq q ((m : ℤ) * n) d.residue then d.beta m else 0) -
        (if (n * m).Coprime q then d.beta m else 0) / (q.totient : ℂ) := by
    have he : (((n * m : ℕ) : ℤ) % (q : ℤ) = d.residue % (q : ℤ)) ↔
        Int.ModEq q ((m : ℤ) * n) d.residue := by
      simp only [Int.ModEq, Nat.cast_mul, mul_comm]
    unfold complexPrimitiveKernel
    simp only [mul_sub, mul_div_assoc, mul_ite, mul_one, mul_zero]
    congr 1
    exact if_congr he rfl rfl
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_div]
  have hp := (norm_sum_ite_le_card d.betaCarrier d.beta
    (fun m : ℕ ↦ Int.ModEq q ((m : ℤ) * n) d.residue) hbeta).trans
      (mul_le_mul_of_nonneg_left (betaCarrier_progression_card_le hV hq hn) hA)
  have hm : ‖∑ m ∈ d.betaCarrier,
      if (n * m).Coprime q then d.beta m else 0‖ ≤ A * (2 * d.V) := by
    apply (norm_sum_ite_le_card d.betaCarrier d.beta
      (fun m : ℕ ↦ (n * m).Coprime q) hbeta).trans
    apply mul_le_mul_of_nonneg_left _ hA
    exact (show ((d.betaCarrier.filter (fun m : ℕ ↦ (n * m).Coprime q)).card : ℝ) ≤
      d.betaCarrier.card by exact_mod_cast Finset.card_filter_le _ _).trans
        (betaCarrier_card_le hV)
  calc
    _ ≤ ‖∑ m ∈ d.betaCarrier,
        if Int.ModEq q ((m : ℤ) * n) d.residue then d.beta m else 0‖ +
        ‖(∑ m ∈ d.betaCarrier, if (n * m).Coprime q then d.beta m else 0) /
          (q.totient : ℂ)‖ := norm_sub_le _ _
    _ ≤ A * (2 * d.V / q + 1) + A * (2 * d.V) / q.totient := by
      apply add_le_add hp
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right hm (Nat.cast_nonneg _)
    _ = _ := by ring

private theorem grouped_weight_sums
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ / q) ≤
        (1 + Real.log d.physicalFactorCap) ^ 3 ∧
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖) ≤
        d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2 ∧
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ / q.totient) ≤
        (1 + Real.log d.physicalFactorCap) ^ 6 := by
  have hsub := d.physicalFactorModuli_subset_cap hd
  have hcap := d.one_le_physicalFactorCap hd
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 3 q : ℝ) / q :=
        Finset.sum_le_sum (fun q _ ↦ div_le_div_of_nonneg_right
          (d.groupedFactorGamma_norm_le_tauThree hd q) (Nat.cast_nonneg _))
      _ ≤ ∑ q ∈ Ioc 0 (Nat.floor d.physicalFactorCap), (fouvryTau 3 q : ℝ) / q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
      _ ≤ _ := sum_fouvryTau_div_le_real 3 hcap
  · calc
      _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 3 q : ℝ) :=
        Finset.sum_le_sum (fun q _ ↦ d.groupedFactorGamma_norm_le_tauThree hd q)
      _ ≤ ∑ q ∈ Ioc 0 (Nat.floor d.physicalFactorCap), (fouvryTau 3 q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
      _ ≤ _ := by simpa using
        sum_fouvryTau_le_real (k := 3) (by norm_num) hcap
  · calc
      _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 3 q : ℝ) / q.totient :=
        Finset.sum_le_sum (fun q _ ↦ div_le_div_of_nonneg_right
          (d.groupedFactorGamma_norm_le_tauThree hd q) (Nat.cast_nonneg _))
      _ ≤ ∑ q ∈ Ioc 0 (Nat.floor d.physicalFactorCap), (fouvryTau 3 q : ℝ) / q.totient :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
      _ ≤ _ := by simpa using
        sum_fouvryTau_div_totient_le_real 3 hcap

/-- One deleted original-alpha divisor has a true progression saving;
the primitive coprime mean and every complex factor fiber stay present. -/
theorem centeredRow_norm_le_on_signed_divisor
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {n : ℕ}
    (hn : (n : ℤ) ∣ d.residue) {A : ℝ} (hA : 0 ≤ A)
    (hbeta : ∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ A) :
    ‖d.complexCenteredRow n‖ ≤ A *
      (2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 3 +
        d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2 +
          2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 6) := by
  rw [d.complexCenteredRow_eq_groupedFactorGamma]
  obtain ⟨hwq, hw, hwphi⟩ := grouped_weight_sums hd
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ *
        (A * (2 * d.V / q + 1 + 2 * d.V / q.totient)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      by_cases hg : d.groupedFactorGamma q = 0
      · simp only [hg, norm_zero, zero_mul, le_refl]
      · have hnq : n.Coprime q :=
          ((active_grouped_coprime_residue hd hg).of_dvd_right (Int.natCast_dvd.mp hn)).symm
        exact mul_le_mul_of_nonneg_left (betaKernelMass_norm_le hd.2.1
          (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd hq)).1 hnq hA hbeta)
            (norm_nonneg _)
    _ = A * (2 * d.V * (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ / q) +
        (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖) +
          2 * d.V * (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ / q.totient)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hwq (by linarith [hd.2.1])) hw)
        (mul_le_mul_of_nonneg_left hwphi (by linarith [hd.2.1]))) hA

/-- A finite linear budget for the original signed-error deletion. No
quadratic W exception, UV cancellation or analytic estimate is assumed. -/
theorem signedError_sub_cleanAlpha_norm_le_finite
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {A : ℝ} (hA : 0 ≤ A)
    (hbeta : ∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ A) :
    ‖d.signedError - d.cleanedAlphaAtom.signedError‖ ≤
      (∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖) * A *
        (2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 3 +
          d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2 +
            2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 6) := by
  rw [d.signedError_sub_cleanAlpha_eq_divisorAlpha,
    d.divisorAlphaAtom.signedError_eq_complexCenteredRows]
  change ‖∑ n ∈ d.alphaCarrier, d.divisorAlpha n * d.complexCenteredRow n‖ ≤ _
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖ * (A *
        (2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 3 +
          d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2 +
            2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 6)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul]
      by_cases hn : (n : ℤ) ∣ d.residue
      · exact mul_le_mul_of_nonneg_left
          (centeredRow_norm_le_on_signed_divisor hd hn hA hbeta) (norm_nonneg _)
      · simp only [MediumAtom.divisorAlpha, if_neg hn, norm_zero, zero_mul, le_refl]
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The true positive-c0 caller supplies a nonzero moving residue. The
constant depends only on the fixed polynomial exponent and epsilon. -/
theorem divisorAlphaMass_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 d →
        (∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖) ≤ C * d.scale ^ epsilon := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := by linarith
  let eta : ℝ := epsilon / K
  have heta : 0 < eta := div_pos hepsilon hKpos
  have hKeta : K * eta = epsilon := by dsimp [eta]; field_simp [hKpos.ne']
  obtain ⟨C, hC, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) heta
  refine ⟨C, hC, fun B sigma c0 d hc0 hd ↦ ?_⟩
  have ha := mediumAdmissible_residue_ne_zero hc0 hd
  have hx := one_le_scale hd
  obtain ⟨_, _, _, _, _, _, _, hres, _⟩ := hd
  have haK : (d.residue.natAbs : ℝ) ≤ d.scale ^ K :=
    hres.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  calc
    _ ≤ (fouvryTau 2 d.residue.natAbs : ℝ) := divisorAlphaMass_le_tau hd ha
    _ ≤ C * (d.residue.natAbs : ℝ) ^ eta := hbound _ (Int.natAbs_pos.mpr ha)
    _ ≤ C * (d.scale ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) haK heta.le) hC.le
    _ = C * d.scale ^ epsilon := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ d.scale), hKeta]

private theorem beta_norm_subpower (B : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ m ∈ d.betaCarrier,
        ‖d.beta m‖ ≤ C * d.scale ^ epsilon := by
  obtain ⟨C, hC, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2 ^ B) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero B (by norm_num))) hepsilon
  refine ⟨C * (2 : ℝ) ^ epsilon, by positivity, fun sigma kappa c0 d hd m hm ↦ ?_⟩
  have hx := one_le_scale hd
  have hm' := Finset.mem_Ioc.mp (d.betaCarrier_subset_twiceV hd.2.1 hm)
  have hVx : d.V ≤ d.scale := by
    exact le_mul_of_one_le_left (by linarith [hd.2.1]) hd.1
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
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith : 0 ≤ d.scale)]; ring

/-- These are the original medium monomials, with original U, V and cap.
No transposed MediumAdmissible claim is required or introduced. -/
theorem actual_geometry_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.scale ^ sigma ≤ d.U ∧ d.V ≤ d.scale ^ (1 - sigma) ∧
      d.physicalFactorCap ≤ 8 * d.scale ^ (1 - 10 * sigma) := by
  have hx1 := one_le_scale hd
  have hx : 0 < d.scale := zero_lt_one.trans_le hx1
  obtain ⟨hU, hV, hQ1, _, _, _, _, _, hg1, _⟩ := hd
  have hlow : d.scale ^ sigma ≤ d.U := by
    apply le_of_lt
    calc
      _ ≤ d.Q1 * d.scale ^ sigma := le_mul_of_one_le_left (by positivity) hQ1
      _ < (d.U * d.scale ^ (-sigma)) * d.scale ^ sigma :=
        mul_lt_mul_of_pos_right hg1 (Real.rpow_pos_of_pos hx _)
      _ = d.U := by
        rw [mul_assoc, ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, mul_one]
  have hpow : 0 < d.scale ^ sigma := Real.rpow_pos_of_pos hx _
  refine ⟨hlow, ?_, ?_⟩
  · calc
      d.V ≤ d.scale / d.scale ^ sigma := (le_div_iff₀ hpow).mpr (by
        calc
          _ = d.scale ^ sigma * d.V := mul_comm _ _
          _ ≤ d.U * d.V := mul_le_mul_of_nonneg_right hlow (by linarith)
          _ = d.scale := rfl)
      _ = _ := by rw [Real.rpow_sub hx, Real.rpow_one]
  · calc
      _ ≤ (8 * d.scale ^ (1 - 9 * sigma)) / d.scale ^ sigma :=
        (le_div_iff₀ hpow).mpr (by
          calc
            _ = d.scale ^ sigma * d.physicalFactorCap := mul_comm _ _
            _ ≤ d.U * d.physicalFactorCap := mul_le_mul_of_nonneg_right hlow
              (by linarith [d.one_le_physicalFactorCap hd])
            _ ≤ _ := d.U_mul_physicalFactorCap_le hd)
      _ = _ := by
        rw [mul_div_assoc, ← Real.rpow_sub hx,
          show 1 - 9 * sigma - sigma = 1 - 10 * sigma by ring]

private theorem eventually_const_log_rpow_le_rpow (C A : ℝ) (hC : 0 ≤ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ A ≤ x ^ epsilon := by
  have hb := ((isLittleO_log_rpow_rpow_atTop A hepsilon).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
  simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (by positivity :
    0 ≤ C * Real.log x ^ A), abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using hx

private theorem eventually_cap_log_cost_le (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        (1 + Real.log d.physicalFactorCap) ^ 6 ≤ d.scale ^ (sigma / 4) := by
  let D : ℝ := 2 + Real.log 8
  have hD : 0 < D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp
    (eventually_const_log_rpow_le_rpow (D ^ 6) 6 (by positivity)
      (by linarith : 0 < sigma / 4))
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro B kappa c0 d hd hx
  have hscale := one_le_scale hd
  have hscale0 : 0 < d.scale := zero_lt_one.trans_le hscale
  have hlog : 1 ≤ Real.log d.scale := hx2 ((le_max_right x1 x2).trans
    ((le_max_right 2 (max x1 x2)).trans hx))
  have hcapX : d.physicalFactorCap ≤ 8 * d.scale :=
    (actual_geometry_bounds hd).2.2.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hscale (show 1 - 10 * sigma ≤ 1 by linarith))
      (by norm_num))
  have hlogCap : 1 + Real.log d.physicalFactorCap ≤ D * Real.log d.scale := by
    have hp : 0 < d.physicalFactorCap := zero_lt_one.trans_le (d.one_le_physicalFactorCap hd)
    have hh := Real.log_le_log hp hcapX
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hscale0.ne'] at hh
    dsimp [D]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  calc
    _ ≤ (D * Real.log d.scale) ^ 6 :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]) hlogCap 6
    _ = D ^ 6 * Real.log d.scale ^ (6 : ℝ) := by rw [mul_pow, Real.rpow_natCast]
    _ ≤ _ := hx1 ((le_max_left x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))

/-- The finite progression budget has a genuine power saving on the
original complete convolution scale. No SW estimate enters this proof. -/
theorem signedError_sub_cleanAlpha_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hc0 : 0 < c0) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        ‖d.signedError - d.cleanedAlphaAtom.signedError‖ ≤
          C * d.scale ^ (1 - sigma / 2) := by
  have he : 0 < sigma / 8 := by linarith
  obtain ⟨Ca, hCa, hmass⟩ := divisorAlphaMass_subpower kappa he
  obtain ⟨Cb, hCb, hbeta⟩ := beta_norm_subpower B he
  obtain ⟨x0, hx0, hlogCost⟩ := eventually_cap_log_cost_le sigma hsigma
  refine ⟨12 * Ca * Cb, by positivity, x0, hx0, fun d hd hx ↦ ?_⟩
  have hscale := one_le_scale hd
  have hscale0 : 0 < d.scale := zero_lt_one.trans_le hscale
  have hH : 1 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  have hH0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by linarith
  have hH3 : (1 + Real.log d.physicalFactorCap) ^ 3 ≤
      (1 + Real.log d.physicalFactorCap) ^ 6 :=
    pow_le_pow_right₀ hH (by norm_num)
  have hH2 : (1 + Real.log d.physicalFactorCap) ^ 2 ≤
      (1 + Real.log d.physicalFactorCap) ^ 6 :=
    pow_le_pow_right₀ hH (by norm_num)
  have hV := (actual_geometry_bounds hd).2.1
  have hcap : d.physicalFactorCap ≤ 8 * d.scale ^ (1 - sigma) :=
    (actual_geometry_bounds hd).2.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hscale (by linarith : 1 - 10 * sigma ≤ 1 - sigma))
      (by norm_num))
  have hbracket :
      2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 3 +
        d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2 +
          2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 6 ≤
        12 * d.scale ^ (1 - sigma) * (1 + Real.log d.physicalFactorCap) ^ 6 := by
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 2))
      hH3 (pow_nonneg hH0 _) (by positivity)
    have h2 := mul_le_mul hcap hH2 (pow_nonneg hH0 _) (by positivity)
    have h3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 2)) (pow_nonneg hH0 6)
    nlinarith
  calc
    _ ≤ (∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖) * (Cb * d.scale ^ (sigma / 8)) *
        (2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 3 +
          d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2 +
            2 * d.V * (1 + Real.log d.physicalFactorCap) ^ 6) :=
      signedError_sub_cleanAlpha_norm_le_finite hd (by positivity)
        (hbeta sigma kappa c0 d hd)
    _ ≤ (Ca * d.scale ^ (sigma / 8)) * (Cb * d.scale ^ (sigma / 8)) *
        (12 * d.scale ^ (1 - sigma) * (1 + Real.log d.physicalFactorCap) ^ 6) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (hmass B sigma c0 d hc0 hd) (by positivity))
        hbracket (by positivity) (by positivity)
    _ = (12 * Ca * Cb) *
        (d.scale ^ (sigma / 8) * d.scale ^ (sigma / 8) * d.scale ^ (1 - sigma)) *
          (1 + Real.log d.physicalFactorCap) ^ 6 := by ring
    _ ≤ (12 * Ca * Cb) *
        (d.scale ^ (sigma / 8) * d.scale ^ (sigma / 8) * d.scale ^ (1 - sigma)) *
          d.scale ^ (sigma / 4) :=
      mul_le_mul_of_nonneg_left (hlogCost B kappa c0 d hd hx) (by positivity)
    _ = _ := by
      rw [mul_assoc (12 * Ca * Cb), ← Real.rpow_add hscale0,
        ← Real.rpow_add hscale0, ← Real.rpow_add hscale0,
        show sigma / 8 + sigma / 8 + (1 - sigma) + sigma / 4 = 1 - sigma / 2 by ring]

/-- One threshold precedes every atom and its moving signed residue. -/
theorem signedError_sub_cleanAlpha_log_payment (B : ℕ) (sigma kappa c0 A : ℝ)
    (hsigma : 0 < sigma) (hc0 : 0 < c0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        ‖d.signedError - d.cleanedAlphaAtom.signedError‖ ≤
          d.scale / Real.log d.scale ^ A := by
  obtain ⟨C, hC, x1, hx1, hbound⟩ :=
    signedError_sub_cleanAlpha_power_bound B sigma kappa c0 hsigma hc0
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_log_rpow_le_rpow C A hC.le (by linarith : 0 < sigma / 2))
  obtain ⟨x3, hx3⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max x1 (max x2 x3), hx1.trans_le (le_max_left _ _), fun d hd hx ↦ ?_⟩
  have hscale0 : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hlog : 1 ≤ Real.log d.scale := hx3 ((le_max_right x2 x3).trans
    ((le_max_right x1 (max x2 x3)).trans hx))
  apply (hbound d hd ((le_max_left _ _).trans hx)).trans
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < Real.log d.scale) A)).mpr
  calc
    _ = (C * Real.log d.scale ^ A) * d.scale ^ (1 - sigma / 2) := by ring
    _ ≤ d.scale ^ (sigma / 2) * d.scale ^ (1 - sigma / 2) :=
      mul_le_mul_of_nonneg_right (hx2 ((le_max_left x2 x3).trans
        ((le_max_right x1 (max x2 x3)).trans hx))) (by positivity)
    _ = _ := by rw [← Real.rpow_add hscale0,
      show sigma / 2 + (1 - sigma / 2) = 1 by ring, Real.rpow_one]

private theorem auxSWError_eq_clean_add_divisorAlpha (d : MediumAtom) (k q b : ℕ) :
    d.auxSWError k q b =
      d.cleanedAlphaAtom.auxSWError k q b + d.divisorAlphaAtom.auxSWError k q b := by
  have hAP :
      (∑ n ∈ d.alphaCarrier,
        if Nat.ModEq q n b ∧ Nat.Coprime n k then d.alpha n else 0) =
      (∑ n ∈ d.alphaCarrier,
        if Nat.ModEq q n b ∧ Nat.Coprime n k then d.cleanedAlpha n else 0) +
      (∑ n ∈ d.alphaCarrier,
        if Nat.ModEq q n b ∧ Nat.Coprime n k then d.divisorAlpha n else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : Nat.ModEq q n b ∧ Nat.Coprime n k
    · simpa only [if_pos hn] using d.alpha_eq_clean_add_divisorAlpha n
    · simp only [if_neg hn, add_zero]
  have hmean :
      (∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.alpha n else 0) =
      (∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.cleanedAlpha n else 0) +
      (∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.divisorAlpha n else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : Nat.Coprime n (k * q)
    · simpa only [if_pos hn] using d.alpha_eq_clean_add_divisorAlpha n
    · simp only [if_neg hn, add_zero]
  change
    (∑ n ∈ d.alphaCarrier,
      if Nat.ModEq q n b ∧ Nat.Coprime n k then d.alpha n else 0) -
    (∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.alpha n else 0) /
      (q.totient : ℂ) = _
  rw [hAP, hmean]
  change _ =
    ((∑ n ∈ d.alphaCarrier,
      if Nat.ModEq q n b ∧ Nat.Coprime n k then d.cleanedAlpha n else 0) -
      (∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.cleanedAlpha n else 0) /
        (q.totient : ℂ)) +
    ((∑ n ∈ d.alphaCarrier,
      if Nat.ModEq q n b ∧ Nat.Coprime n k then d.divisorAlpha n else 0) -
      (∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.divisorAlpha n else 0) /
        (q.totient : ℂ))
  ring

private theorem norm_sum_ite_le_l1 (S : Finset ℕ) (beta : ℕ → ℂ)
    (p : ℕ → Prop) [DecidablePred p] :
    ‖∑ n ∈ S, if p n then beta n else 0‖ ≤ ∑ n ∈ S, ‖beta n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : p n <;> simp only [hn, if_true, if_false, norm_zero, norm_nonneg, le_refl]

/-- Deleting original-alpha divisors changes every actual auxiliary SW
error by at most twice the same finite divisor mass, uniformly in k/q/b. -/
theorem auxSWError_sub_cleanAlpha_norm_le (d : MediumAtom) (k q b : ℕ) (hq : 0 < q) :
    ‖d.auxSWError k q b - d.cleanedAlphaAtom.auxSWError k q b‖ ≤
      2 * ∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖ := by
  have he : d.auxSWError k q b - d.cleanedAlphaAtom.auxSWError k q b =
      d.divisorAlphaAtom.auxSWError k q b := by
    rw [auxSWError_eq_clean_add_divisorAlpha]
    ring
  rw [he]
  change ‖(∑ n ∈ d.alphaCarrier,
      if Nat.ModEq q n b ∧ Nat.Coprime n k then d.divisorAlpha n else 0) -
    (∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.divisorAlpha n else 0) /
      (q.totient : ℂ)‖ ≤ _
  have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have h1 := norm_sum_ite_le_l1 d.alphaCarrier d.divisorAlpha
    (fun n : ℕ ↦ Nat.ModEq q n b ∧ Nat.Coprime n k)
  have h2 := norm_sum_ite_le_l1 d.alphaCarrier d.divisorAlpha
    (fun n : ℕ ↦ Nat.Coprime n (k * q))
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ (∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖) +
        (∑ n ∈ d.alphaCarrier, ‖d.divisorAlpha n‖) := by
      apply add_le_add h1
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right h2 (Nat.cast_nonneg _)).trans
        (div_le_self (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)) hphi)
    _ = _ := by ring

/-- The paired coefficient is cleaned without increasing its fixed
auxiliary divisor order C0. The genuine U lower gate absorbs the deleted
mass; constants and thresholds still precede i, k, q and b. -/
theorem uniformAuxiliarySW_cleanedAlphaAtom {ι : Type*}
    (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hc0 : 0 < c0)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    UniformAuxiliarySW (fun i ↦ (F i).cleanedAlphaAtom) C0 := by
  intro A hA
  obtain ⟨C, hC, x1, hx1, hbound⟩ := hSW A hA
  obtain ⟨D, hD, hmass⟩ := divisorAlphaMass_subpower kappa (by linarith : 0 < sigma / 2)
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_log_rpow_le_rpow (2 * D) A (by positivity)
      (by linarith : 0 < sigma / 2))
  obtain ⟨x3, hx3⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨C + 1, by positivity, max x1 (max x2 x3),
    hx1.trans_le (le_max_left _ _), ?_⟩
  intro i hx k q b hk hq hb
  change ‖(F i).cleanedAlphaAtom.auxSWError k q b‖ ≤
    (C + 1) * (F i).U * (k.divisors.card : ℝ) ^ C0 / Real.log (F i).scale ^ A
  have hxOrig : x1 ≤ (F i).scale := (le_max_left _ _).trans hx
  have hscale0 : 0 < (F i).scale := zero_lt_one.trans_le (one_le_scale (hadmissible i))
  have hU : 0 ≤ (F i).U := by linarith [(hadmissible i).1]
  have hlog : 1 ≤ Real.log (F i).scale := hx3 ((le_max_right x2 x3).trans
    ((le_max_right x1 (max x2 x3)).trans hx))
  have hchange : ‖(F i).auxSWError k q b - (F i).cleanedAlphaAtom.auxSWError k q b‖ ≤
      (F i).U / Real.log (F i).scale ^ A := by
    apply (auxSWError_sub_cleanAlpha_norm_le (F i) k q b (by omega)).trans
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < Real.log (F i).scale) A)).mpr
    calc
      _ ≤ (2 * (D * (F i).scale ^ (sigma / 2))) * Real.log (F i).scale ^ A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hmass B sigma c0 (F i) hc0 (hadmissible i)) (by norm_num)) (by positivity)
      _ = (2 * D * Real.log (F i).scale ^ A) * (F i).scale ^ (sigma / 2) := by ring
      _ ≤ (F i).scale ^ (sigma / 2) * (F i).scale ^ (sigma / 2) :=
        mul_le_mul_of_nonneg_right (hx2 ((le_max_left x2 x3).trans
          ((le_max_right x1 (max x2 x3)).trans hx))) (by positivity)
      _ = (F i).scale ^ sigma := by rw [← Real.rpow_add hscale0,
        show sigma / 2 + sigma / 2 = sigma by ring]
      _ ≤ _ := (actual_geometry_bounds (hadmissible i)).1
  have hkCard : 1 ≤ k.divisors.card := Finset.one_le_card.mpr
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd k, by omega⟩⟩
  have htau : (1 : ℝ) ≤ (k.divisors.card : ℝ) ^ C0 :=
    one_le_pow₀ (by exact_mod_cast hkCard)
  calc
    _ = ‖(F i).auxSWError k q b -
        ((F i).auxSWError k q b - (F i).cleanedAlphaAtom.auxSWError k q b)‖ := by congr 1; ring
    _ ≤ ‖(F i).auxSWError k q b‖ +
        ‖(F i).auxSWError k q b - (F i).cleanedAlphaAtom.auxSWError k q b‖ := norm_sub_le _ _
    _ ≤ C * (F i).U * (k.divisors.card : ℝ) ^ C0 / Real.log (F i).scale ^ A +
        (F i).U / Real.log (F i).scale ^ A := add_le_add
      (hbound i hxOrig k q b hk hq hb) hchange
    _ ≤ C * (F i).U * (k.divisors.card : ℝ) ^ C0 / Real.log (F i).scale ^ A +
        ((F i).U * (k.divisors.card : ℝ) ^ C0) / Real.log (F i).scale ^ A :=
      add_le_add_left (div_le_div_of_nonneg_right (le_mul_of_one_le_right hU htau)
        (by positivity)) _
    _ = _ := by ring

/-- Once distribution is proved for the cleaned paired coefficient, the
original target follows with the already paid linear deletion budget. -/
theorem restrictedMediumTarget_of_cleanedAlphaAtom {ι : Type*}
    (F : ι → MediumAtom) (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hc0 : 0 < c0)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hclean : RestrictedMediumTarget (fun i ↦ (F i).cleanedAlphaAtom)) :
    RestrictedMediumTarget F := by
  intro A hA
  obtain ⟨C, hC, x1, hx1, hbound⟩ := hclean A hA
  obtain ⟨x2, hx2, hdelete⟩ := signedError_sub_cleanAlpha_log_payment B sigma kappa c0 A hsigma hc0
  refine ⟨C + 1, by positivity, max x1 x2, hx1.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  have h1 := hbound i ((le_max_left x1 x2).trans hx)
  have h2 := hdelete (F i) (hadmissible i) ((le_max_right x1 x2).trans hx)
  change ‖(F i).cleanedAlphaAtom.signedError‖ ≤
    C * (F i).scale / Real.log (F i).scale ^ A at h1
  calc
    _ = ‖(F i).cleanedAlphaAtom.signedError +
        ((F i).signedError - (F i).cleanedAlphaAtom.signedError)‖ := by congr 1; ring
    _ ≤ ‖(F i).cleanedAlphaAtom.signedError‖ +
        ‖(F i).signedError - (F i).cleanedAlphaAtom.signedError‖ := norm_add_le _ _
    _ ≤ C * (F i).scale / Real.log (F i).scale ^ A +
        (F i).scale / Real.log (F i).scale ^ A := add_le_add h1 h2
    _ = _ := by ring

end PairedAlphaDeletion

end

end ImbalancedChen.Part3
