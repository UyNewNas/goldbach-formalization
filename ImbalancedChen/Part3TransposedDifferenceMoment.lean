import ImbalancedChen.Part3TransposedModulusProgression

/-!
# Actual full Fourier payment for large physical gcd after alpha cleanup

For each fixed original-alpha index, smaller and larger paired indices
are separately injected into positive differences at most 2U. The true
tau_2 off-diagonal moment costs one logarithm; the diagonal is paid as
10X and never becomes the divisor set of zero.

These actual finite costs pay the preceding whole-W progression estimate.
Original beta-L2 and original medium geometry give reciprocal U, D and V
savings, with U,V>=X^sigma derived from the original monomials. At D=X^delta
all fixed logarithms are paid with a threshold before d and Y. Whole W
minus the SAME masked raw zero therefore pays this entire full signed
Fourier region, including all frequencies and original complex labels.

The both-small gcd region, its slow/root phase and the remaining analytic
coordinates remain open. No new foreign module, distribution premise,
row cap or energy budget is imported or requested from the caller.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace TransposedDifferenceMoment

private theorem natAbs_difference_of_le {a b : ℕ} (h : b ≤ a) :
    ((a : ℤ) - b).natAbs = a - b := by
  rw [Int.natAbs_sub_of_nonneg_of_le
    (show (0 : ℤ) ≤ (b : ℤ) by omega) (show (b : ℤ) ≤ (a : ℤ) by exact_mod_cast h),
    Int.natAbs_natCast, Int.natAbs_natCast]

private theorem difference_row_le (N : Finset ℕ) (K n : ℕ)
    (hN : ∀ m ∈ N, m ≤ K) (hn : n ≤ K) :
    (∑ m ∈ N, if n = m then 0 else
      (fouvryTau 2 ((n : ℤ) - m).natAbs : ℝ)) ≤
      2 * ∑ v ∈ Ioc 0 K, (fouvryTau 2 v : ℝ) := by
  let L := N.filter (fun m ↦ m < n)
  let R := N.filter (fun m ↦ n < m)
  have hL : (∑ m ∈ L, (fouvryTau 2 (n - m) : ℝ)) ≤
      ∑ v ∈ Ioc 0 K, (fouvryTau 2 v : ℝ) := by
    have hi : Set.InjOn (fun m : ℕ ↦ n - m) (↑L : Set ℕ) := by
      intro a ha b hb he
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega
    calc
      _ = ∑ v ∈ L.image (fun m ↦ n - m), (fouvryTau 2 v : ℝ) := by
        rw [Finset.sum_image hi]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
        intro v hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_Ioc.mpr ⟨Nat.sub_pos_of_lt (Finset.mem_filter.mp hm).2,
          (Nat.sub_le n m).trans hn⟩) (fun _ _ _ ↦ Nat.cast_nonneg _)
  have hR : (∑ m ∈ R, (fouvryTau 2 (m - n) : ℝ)) ≤
      ∑ v ∈ Ioc 0 K, (fouvryTau 2 v : ℝ) := by
    have hi : Set.InjOn (fun m : ℕ ↦ m - n) (↑R : Set ℕ) := by
      intro a ha b hb he
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega
    calc
      _ = ∑ v ∈ R.image (fun m ↦ m - n), (fouvryTau 2 v : ℝ) := by
        rw [Finset.sum_image hi]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
        intro v hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_Ioc.mpr ⟨Nat.sub_pos_of_lt (Finset.mem_filter.mp hm).2,
          (Nat.sub_le m n).trans (hN m (Finset.mem_filter.mp hm).1)⟩)
        (fun _ _ _ ↦ Nat.cast_nonneg _)
  have heq : (∑ m ∈ N, if n = m then 0 else
      (fouvryTau 2 ((n : ℤ) - m).natAbs : ℝ)) =
      (∑ m ∈ L, (fouvryTau 2 (n - m) : ℝ)) +
        ∑ m ∈ R, (fouvryTau 2 (m - n) : ℝ) := by
    simp only [L, R, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rcases lt_trichotomy n m with h | h | h
    · have ha : ((n : ℤ) - m).natAbs = m - n := by
        rw [show (n : ℤ) - m = -((m : ℤ) - n) by ring, Int.natAbs_neg]
        exact natAbs_difference_of_le h.le
      simp only [if_neg h.ne, if_neg (not_lt.mpr h.le), if_pos h, ha, zero_add]
    · subst m
      simp
    · have ha := natAbs_difference_of_le h.le
      simp only [if_neg h.ne', if_pos h, if_neg (not_lt.mpr h.le), ha, add_zero]
  rw [heq]
  linarith

private theorem transposed_betaCarrier_card_le {d : MediumAtom} (hU : 1 ≤ d.U) :
    (d.transposedAtom.betaCarrier.card : ℝ) ≤ 2 * d.U := by
  have hc := Finset.card_le_card (d.transposedAtom.betaCarrier_subset_twiceV hU)
  simp only [Nat.card_Ioc, Nat.sub_zero] at hc
  exact (show (d.transposedAtom.betaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
    exact_mod_cast hc).trans (Nat.floor_le (by linarith : 0 ≤ 2 * d.U))

/-- The literal actual paired carrier pays its nonzero differences by
one true tau_2 moment, independently of the original signed residue. -/
theorem transposed_offDiagonal_tauTwo_sum_le {d : MediumAtom} (hU : 1 ≤ d.U) :
    (∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
      if n₁ = n₂ then 0 else (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ)) ≤
        8 * d.U ^ 2 * (1 + Real.log (2 * d.U)) := by
  have hU0 : 0 ≤ d.U := by linarith
  have hmean : (∑ v ∈ Ioc 0 (Nat.floor (2 * d.U)), (fouvryTau 2 v : ℝ)) ≤
      2 * d.U * (1 + Real.log (2 * d.U)) := by
    simpa using sum_fouvryTau_le_real (k := 2) (by norm_num)
      (show 1 ≤ 2 * d.U by linarith)
  have hN : ∀ n ∈ d.transposedAtom.betaCarrier, n ≤ Nat.floor (2 * d.U) :=
    fun n hn ↦ (Finset.mem_Icc.mp hn).2
  have hlog : 0 ≤ 1 + Real.log (2 * d.U) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.U by linarith)]
  calc
    _ ≤ ∑ _n₁ ∈ d.transposedAtom.betaCarrier,
        2 * ∑ v ∈ Ioc 0 (Nat.floor (2 * d.U)), (fouvryTau 2 v : ℝ) :=
      Finset.sum_le_sum (fun n hn ↦ difference_row_le _ _ n hN (hN n hn))
    _ ≤ ∑ _n₁ ∈ d.transposedAtom.betaCarrier,
        2 * (2 * d.U * (1 + Real.log (2 * d.U))) :=
      Finset.sum_le_sum (fun _ _ ↦ mul_le_mul_of_nonneg_left hmean (by norm_num))
    _ = (d.transposedAtom.betaCarrier.card : ℝ) *
        (2 * (2 * d.U * (1 + Real.log (2 * d.U)))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d.U) * (2 * (2 * d.U * (1 + Real.log (2 * d.U)))) :=
      mul_le_mul_of_nonneg_right (transposed_betaCarrier_card_le hU) (by positivity)
    _ = _ := by ring

/-- The diagonal has its actual cardinal cost. It is never included in
the off-diagonal natural divisor difference sum. -/
theorem transposed_diagonal_weight_sum_le {d : MediumAtom}
    (hU : 1 ≤ d.U) (hV : 0 ≤ d.V) :
    (∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
      if n₁ = n₂ then 5 * d.V else 0) ≤ 10 * d.scale := by
  calc
    _ = (d.transposedAtom.betaCarrier.card : ℝ) * (5 * d.V) := by simp
    _ ≤ (2 * d.U) * (5 * d.V) :=
      mul_le_mul_of_nonneg_right (transposed_betaCarrier_card_le hU) (by positivity)
    _ = _ := by unfold MediumAtom.scale; ring

private theorem cleanedAlpha_transposed_beta_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ≤ 1 := by
  have hclean := mediumAdmissible_cleanedAlphaAtom hd
  have hAlpha : ∀ n ∈ d.cleanedAlphaAtom.alphaCarrier, ‖d.cleanedAlphaAtom.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hclean
    exact hAlpha
  change ‖if n ∈ d.cleanedAlphaAtom.alphaCarrier then d.cleanedAlphaAtom.alpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.cleanedAlphaAtom.alphaCarrier
  · simpa only [if_pos hn] using hAlpha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

private theorem cleanedAlpha_pairDivisorBudget_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) {D : ℝ} (hD : 0 < D) :
    (∑ n₁ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
      ∑ n₂ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
        if Y < (n₁.gcd n₂ : ℝ) then 0 else
          ‖d.cleanedAlphaAtom.transposedAtom.beta n₁‖ *
            ‖d.cleanedAlphaAtom.transposedAtom.beta n₂‖ *
              (if n₁ = n₂ then 5 * d.V else
                (4 * d.V / D + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ))) ≤
      10 * d.scale + 8 * d.U ^ 2 * (4 * d.V / D + 1) * (1 + Real.log (2 * d.U)) := by
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hcoef : 0 ≤ 4 * d.V / D + 1 := by positivity
  calc
    _ ≤ ∑ n₁ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
        ∑ n₂ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
          if n₁ = n₂ then 5 * d.V else
            (4 * d.V / D + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ) := by
      apply Finset.sum_le_sum
      intro n₁ _
      apply Finset.sum_le_sum
      intro n₂ _
      have hcost : 0 ≤ (if n₁ = n₂ then 5 * d.V else
          (4 * d.V / D + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ)) := by
        split_ifs <;> positivity
      by_cases hy : Y < (n₁.gcd n₂ : ℝ)
      · simpa only [if_pos hy] using hcost
      · rw [if_neg hy]
        have hb : ‖d.cleanedAlphaAtom.transposedAtom.beta n₁‖ *
            ‖d.cleanedAlphaAtom.transposedAtom.beta n₂‖ ≤ 1 := by
          simpa only [one_mul] using mul_le_mul
            (cleanedAlpha_transposed_beta_norm_le_one hd n₁)
            (cleanedAlpha_transposed_beta_norm_le_one hd n₂) (norm_nonneg _) zero_le_one
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hb hcost
    _ = (∑ n₁ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
        ∑ n₂ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
          if n₁ = n₂ then 5 * d.V else 0) +
        (4 * d.V / D + 1) *
          ∑ n₁ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
            ∑ n₂ ∈ d.cleanedAlphaAtom.transposedAtom.betaCarrier,
              if n₁ = n₂ then 0 else (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      by_cases he : n₁ = n₂ <;> simp [he]
    _ ≤ 10 * d.scale + (4 * d.V / D + 1) *
        (8 * d.U ^ 2 * (1 + Real.log (2 * d.U))) :=
      add_le_add (transposed_diagonal_weight_sum_le (d := d.cleanedAlphaAtom) hd.1 hV)
        (mul_le_mul_of_nonneg_left
          (transposed_offDiagonal_tauTwo_sum_le (d := d.cleanedAlphaAtom) hd.1) hcoef)
    _ = _ := by ring

/-- The complete actual whole W in this second gcd region has now paid
its diagonal and the true off-diagonal divisor moment. -/
theorem cleanedAlpha_largeModulusW_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D : ℝ, 0 < D →
        ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDW Y D‖ ≤
          C * d.scale ^ epsilon *
            (10 * d.scale + 8 * d.U ^ 2 * (4 * d.V / D + 1) * (1 + Real.log (2 * d.U))) := by
  obtain ⟨C, hC, hbound⟩ :=
    TransposedModulusProgression.cleanedAlpha_transposed_smallBeta_largeModulusW_divisor_bound
      kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y D hD ↦ ?_⟩
  exact (hbound B sigma c0 d hd Y D hD).trans
    (mul_le_mul_of_nonneg_left (cleanedAlpha_pairDivisorBudget_le hd Y hD) (by positivity))

theorem betaL2_mul_cleanedAlpha_largeModulusW_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D : ℝ, 0 < D →
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDW Y D‖ ≤
            C * d.scale ^ epsilon * d.scale ^ 2 *
              (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
                (20 / d.U + 64 * (1 + Real.log (2 * d.U)) / D +
                  16 * (1 + Real.log (2 * d.U)) / d.V) := by
  obtain ⟨C, hC, hbound⟩ := cleanedAlpha_largeModulusW_bound kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y D hD ↦ ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hlogV : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  calc
    _ ≤ (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (C * d.scale ^ epsilon * (10 * d.scale +
          8 * d.U ^ 2 * (4 * d.V / D + 1) * (1 + Real.log (2 * d.U)))) :=
      mul_le_mul (mediumAdmissible_beta_norm_sq_sum_le hd)
        (hbound B sigma c0 d hd Y D hD) (norm_nonneg _) (by positivity)
    _ = _ := by
      unfold MediumAtom.scale
      field_simp [hU.ne', hV.ne', hD.ne']
      ring

private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

/-- Both lengths have an actual positive-power lower bound, derived
from the ORIGINAL medium monomials. No new bound on sigma is assumed. -/
private theorem both_lengths_lower_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.scale ^ sigma ≤ d.U ∧ d.scale ^ sigma ≤ d.V := by
  have hx1 := one_le_scale hd
  have hx : 0 < d.scale := zero_lt_one.trans_le hx1
  have hU0 : 0 ≤ d.U := by linarith [hd.1]
  have hV0 : 0 ≤ d.V := by linarith [hd.2.1]
  have hU := (PairedAlphaDeletion.actual_geometry_bounds hd).1
  have hdKeep := hd
  obtain ⟨_, _, _, hQ2, hQ3, _, _, _, _, hg2, _⟩ := hdKeep
  have hQ3sq : 1 ≤ d.Q3 ^ 2 := one_le_pow₀ hQ3
  have hU2 : d.U ^ 2 ≤ d.scale ^ (1 - 8 * sigma) := by
    calc
      _ ≤ d.U ^ 2 * d.Q2 := le_mul_of_one_le_right (sq_nonneg d.U) hQ2
      _ ≤ d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := le_mul_of_one_le_right
        (mul_nonneg (sq_nonneg d.U) (by linarith : 0 ≤ d.Q2)) hQ3sq
      _ ≤ _ := hg2.le
  have hU2' : d.U ^ 2 ≤ d.scale ^ (2 - 2 * sigma) := hU2.trans
    (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : 1 - 8 * sigma ≤ 2 - 2 * sigma))
  have hp : 0 < d.scale ^ (1 - sigma) := Real.rpow_pos_of_pos hx _
  have hsquare : (d.scale ^ (1 - sigma)) ^ 2 = d.scale ^ (2 - 2 * sigma) := by
    rw [← Real.rpow_natCast (d.scale ^ (1 - sigma)) 2, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hUupper : d.U ≤ d.scale ^ (1 - sigma) := by nlinarith [hU2', hsquare]
  refine ⟨hU, (mul_le_mul_left hp).mp ?_⟩
  calc
    _ = d.scale := by rw [← Real.rpow_add hx,
      show (1 - sigma) + sigma = 1 by ring, Real.rpow_one]
    _ = d.U * d.V := rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right hUupper hV0

private theorem log_bound_from_scale {x z : ℝ} (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (hz : 0 < z) (hzx : z ≤ 8 * x) :
    1 + Real.log z ≤ (2 + Real.log 8) * Real.log x := by
  have hh := Real.log_le_log hz hzx
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hx.ne'] at hh
  have hp := mul_nonneg
    (show 0 ≤ 1 + Real.log 8 by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)])
    (show 0 ≤ Real.log x - 1 by linarith)
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]

/-- The entire whole-W part for small paired gcd and large physical gcd
is paid after the actual original-beta L2. All thresholds precede d/Y. -/
theorem betaL2_mul_cleanedAlpha_largeModulusW_log_payment
    (B : ℕ) (sigma kappa c0 A delta : ℝ) (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale → ∀ Y : ℝ,
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDW Y (d.scale ^ delta)‖ ≤
            d.scale ^ 2 / Real.log d.scale ^ A := by
  let z : ℝ := min sigma delta
  have hz : 0 < z := lt_min hsigma hdelta
  obtain ⟨C, hC, hbound⟩ := betaL2_mul_cleanedAlpha_largeModulusW_bound kappa (half_pos hz)
  let p : ℕ := (2 ^ B) ^ 2 - 1
  let N : ℕ := p + 1
  let L : ℝ := 2 + Real.log 8
  let E : ℝ := 100 * C * L ^ N
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hevent : ∀ᶠ x : ℝ in atTop,
      E * Real.log x ^ (A + (N : ℝ)) ≤ x ^ (z / 2) := by
    have hb := ((isLittleO_log_rpow_rpow_atTop (A + (N : ℝ)) (half_pos hz)).const_mul_left E).bound
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
  have hV0 : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hlog : 1 ≤ Real.log d.scale := hx2 d.scale ((le_max_right x1 x2).trans
    ((le_max_right 2 (max x1 x2)).trans hx))
  have hlog0 : 0 < Real.log d.scale := by linarith
  have hPow : 0 < d.scale ^ z := Real.rpow_pos_of_pos hx0 _
  have hD : 0 < d.scale ^ delta := Real.rpow_pos_of_pos hx0 _
  obtain ⟨hUl, hVl⟩ := both_lengths_lower_bound hsigma hd
  have hzU : d.scale ^ z ≤ d.U :=
    (Real.rpow_le_rpow_of_exponent_le hxScale (min_le_left _ _)).trans hUl
  have hzV : d.scale ^ z ≤ d.V :=
    (Real.rpow_le_rpow_of_exponent_le hxScale (min_le_left _ _)).trans hVl
  have hzD : d.scale ^ z ≤ d.scale ^ delta :=
    Real.rpow_le_rpow_of_exponent_le hxScale (min_le_right _ _)
  let Q : ℝ := L * Real.log d.scale
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    simpa only [one_mul] using mul_le_mul hL hlog zero_le_one (by linarith : 0 ≤ L)
  have hQ0 : 0 ≤ Q := by linarith
  have hUx : d.U ≤ d.scale := le_mul_of_one_le_right hU0.le hd.2.1
  have hVx : d.V ≤ d.scale := le_mul_of_one_le_left hV0.le hd.1
  have hU : 1 + Real.log (2 * d.U) ≤ Q :=
    log_bound_from_scale hx0 hlog (by positivity) (by nlinarith)
  have hV : 1 + Real.log (2 * d.V) ≤ Q :=
    log_bound_from_scale hx0 hlog (by positivity) (by nlinarith)
  have hHU : 0 ≤ 1 + Real.log (2 * d.U) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.U by linarith [hd.1])]
  have hHV : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hUD : (1 + Real.log (2 * d.U)) / d.scale ^ delta ≤ Q / d.scale ^ z := by
    exact (div_le_div_of_nonneg_right hU hD.le).trans
      (div_le_div_of_nonneg_left hQ0 hPow hzD)
  have hUV : (1 + Real.log (2 * d.U)) / d.V ≤ Q / d.scale ^ z := by
    exact (div_le_div_of_nonneg_right hU hV0.le).trans
      (div_le_div_of_nonneg_left hQ0 hPow hzV)
  have hBracket : 20 / d.U + 64 * (1 + Real.log (2 * d.U)) / d.scale ^ delta +
      16 * (1 + Real.log (2 * d.U)) / d.V ≤ 100 * Q / d.scale ^ z := by
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 20) hPow hzU
    have h2 : 64 * (1 + Real.log (2 * d.U)) / d.scale ^ delta ≤ 64 * Q / d.scale ^ z := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hUD (by norm_num : (0 : ℝ) ≤ 64)
    have h3 : 16 * (1 + Real.log (2 * d.U)) / d.V ≤ 16 * Q / d.scale ^ z := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hUV (by norm_num : (0 : ℝ) ≤ 16)
    calc
      _ ≤ 20 / d.scale ^ z + 64 * Q / d.scale ^ z + 16 * Q / d.scale ^ z :=
        add_le_add (add_le_add h1 h2) h3
      _ = (20 + 80 * Q) / d.scale ^ z := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hPow.le
  have hPay : E * d.scale ^ (z / 2) * Real.log d.scale ^ N / d.scale ^ z ≤
      1 / Real.log d.scale ^ A := by
    apply (div_le_div_iff₀ hPow (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ = d.scale ^ (z / 2) * (E * Real.log d.scale ^ (A + (N : ℝ))) := by
        rw [Real.rpow_add hlog0, Real.rpow_natCast]
        ring
      _ ≤ d.scale ^ (z / 2) * d.scale ^ (z / 2) :=
        mul_le_mul_of_nonneg_left (hx1 d.scale ((le_max_left x1 x2).trans
          ((le_max_right 2 (max x1 x2)).trans hx))) (by positivity)
      _ = _ := by rw [← Real.rpow_add hx0, show z / 2 + z / 2 = z by ring, one_mul]
  have hBetaLog : (1 + Real.log (2 * d.V)) ^ p ≤ Q ^ p := pow_le_pow_left₀ hHV hV p
  have hCoefficient : 0 ≤ C * d.scale ^ (z / 2) * d.scale ^ 2 := by positivity
  calc
    _ ≤ C * d.scale ^ (z / 2) * d.scale ^ 2 *
        (1 + Real.log (2 * d.V)) ^ p *
          (20 / d.U + 64 * (1 + Real.log (2 * d.U)) / d.scale ^ delta +
            16 * (1 + Real.log (2 * d.U)) / d.V) := hbound B sigma c0 d hd Y _ hD
    _ ≤ C * d.scale ^ (z / 2) * d.scale ^ 2 * Q ^ p * (100 * Q / d.scale ^ z) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hBetaLog hCoefficient) hBracket
        (by positivity) (by positivity)
    _ = d.scale ^ 2 * (E * d.scale ^ (z / 2) * Real.log d.scale ^ N / d.scale ^ z) := by
      have hQN : Q ^ p * Q = Q ^ N := by rw [← pow_succ]; rfl
      calc
        _ = d.scale ^ 2 * (100 * C * d.scale ^ (z / 2) * (Q ^ p * Q) / d.scale ^ z) := by ring
        _ = _ := by rw [hQN]; dsimp only [E, Q]; rw [mul_pow]; ring
    _ ≤ d.scale ^ 2 * (1 / Real.log d.scale ^ A) :=
      mul_le_mul_of_nonneg_left hPay (sq_nonneg _)
    _ = _ := by ring

/-- The ENTIRE full signed Fourier remainder in this second gcd region
is now paid by whole W minus raw zero under the SAME mask. Original
beta-L2, gamma labels, signed residue, V/U and every frequency remain. -/
theorem betaL2_mul_cleanedAlpha_largeModulusNonzero_log_payment
    (B : ℕ) (sigma kappa c0 A delta : ℝ) (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale → ∀ Y : ℝ,
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaModulusGCDNonzeroPart
            Y (d.scale ^ delta) true‖ ≤ 2 * d.scale ^ 2 / Real.log d.scale ^ A := by
  obtain ⟨x1, hx1, hW⟩ := betaL2_mul_cleanedAlpha_largeModulusW_log_payment
    B sigma kappa c0 A delta hsigma hdelta
  obtain ⟨x2, hx2, hZero⟩ :=
    TransposedModulusGCDZero.betaL2_mul_transposed_largeModulusZero_log_payment
      B sigma kappa c0 A delta hsigma hdelta
  refine ⟨max x1 x2, hx1.trans_le (le_max_left _ _), fun d hd hx Y ↦ ?_⟩
  have hclean := mediumAdmissible_cleanedAlphaAtom hd
  have hbeta : 0 ≤ ∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hz := hZero d.cleanedAlphaAtom hclean ((le_max_right x1 x2).trans hx) Y
  change (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
    ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y (d.scale ^ delta)‖ ≤
      d.scale ^ 2 / Real.log d.scale ^ A at hz
  calc
    _ ≤ (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDW Y (d.scale ^ delta)‖ +
          ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y (d.scale ^ delta)‖) :=
      mul_le_mul_of_nonneg_left
        (TransposedModulusGCDZero.transposed_largeModulusNonzero_norm_le_W_add_zero
          hclean Y (d.scale ^ delta)) hbeta
    _ = (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDW Y (d.scale ^ delta)‖ +
        (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          ‖d.cleanedAlphaAtom.transposedAtom.commonSmallBetaLargeModulusGCDZeroPart Y (d.scale ^ delta)‖ := by
      rw [mul_add]
    _ ≤ d.scale ^ 2 / Real.log d.scale ^ A + d.scale ^ 2 / Real.log d.scale ^ A :=
      add_le_add (hW d hd ((le_max_left x1 x2).trans hx) Y) hz
    _ = _ := by ring

end TransposedDifferenceMoment

end

end ImbalancedChen.Part3
