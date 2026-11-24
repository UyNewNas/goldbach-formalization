import ImbalancedChen.Part3CommonIntervalFourier

/-!
# Exceptional weights on the common completed interval

This is the manuscript-internal continuation after `ana:exceptional-average`
in the frozen 2026-11-06 manuscript, used in `ana:spectral-polynomial`.
It takes a full-block quadratic bound, uniform in the one common additive
phase, as an explicit input. It does not prove Pascadi's Theorem J or the
Kim--Sarnak eigenvalue bound and does not assert the full spectral polynomial.

The scalar threshold transport and eigenvalue normalization are extracted
from `Part3ZExceptionalParameter.lean`; the threshold comparisons are
extracted from `Part3ZExceptionalThresholdGeometry.lean`, both preserved in
Goldbach archive commit `fa22a56829ee880404516a36d498ce27dcb32f92`.
The common-interval Fourier proof is reused from the current verified P3
baseline. In particular, the phase is never chosen separately by level.
-/

namespace ImbalancedChen.Part3.ExceptionalWeightExtension

noncomputable section

open scoped BigOperators
open CommonIntervalFourier ActualIntervalGeometricSumSourceOnly

/-- The doubled exceptional parameter, extended by zero on the regular range. -/
def tau (lambda : ℝ) : ℝ :=
  2 * Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0)

theorem tau_nonneg (lambda : ℝ) : 0 ≤ tau lambda := by
  unfold tau
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- This converts a supplied lower eigenvalue bound; it does not supply it. -/
theorem tau_le_seven_thirtyseconds {lambda : ℝ}
    (hlower : (975 : ℝ) / 4096 ≤ lambda) :
    tau lambda ≤ (7 : ℝ) / 32 := by
  have hradicand : max ((1 : ℝ) / 4 - lambda) 0 ≤ ((7 : ℝ) / 64) ^ 2 := by
    apply max_le
    · linarith
    · norm_num
  have hsqrt : Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0) ≤ (7 : ℝ) / 64 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, hradicand⟩
  unfold tau
  linarith

/-- Only the ratio above the threshold uses the cap; the threshold retains
the actual exponent for the full-block mean estimate. -/
theorem rpow_le_threshold_multiplier {W T exponent cap : ℝ}
    (hW : 0 < W) (hT : 0 < T)
    (hexponent : 0 ≤ exponent) (hcap : exponent ≤ cap) :
    W ^ exponent ≤ max 1 ((W / T) ^ cap) * T ^ exponent := by
  have hratio_nonneg : 0 ≤ W / T := div_nonneg hW.le hT.le
  have hratio : (W / T) ^ exponent ≤ max 1 ((W / T) ^ cap) := by
    by_cases hsmall : W / T ≤ 1
    · exact (Real.rpow_le_one hratio_nonneg hsmall hexponent).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hsmall)) hcap).trans
        (le_max_right _ _)
  have hsplit : (W / T) ^ exponent * T ^ exponent = W ^ exponent := by
    rw [← Real.mul_rpow hratio_nonneg hT.le, div_mul_cancel₀ _ hT.ne']
  calc
    W ^ exponent = (W / T) ^ exponent * T ^ exponent := hsplit.symm
    _ ≤ max 1 ((W / T) ^ cap) * T ^ exponent :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hT.le exponent)

/-- One finite spectral truncation. The index can contain the level, basis
label and multiplicity label; all indices use the same interval and phase. -/
def weightedEnergy {ι : Type*} [Fintype ι] (S : Finset ℕ) (ω W : ℝ)
    (exponent : ι → ℝ) (a : ι → ℕ → ℂ) : ℝ :=
  ∑ i, W ^ exponent i * ‖∑ m ∈ S, phaseAt ω m * a i m‖ ^ 2

theorem weightedEnergy_nonneg {ι : Type*} [Fintype ι]
    (S : Finset ℕ) (ω : ℝ) {W : ℝ} (hW : 0 ≤ W)
    (exponent : ι → ℝ) (a : ι → ℕ → ℂ) :
    0 ≤ weightedEnergy S ω W exponent a := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Real.rpow_nonneg hW _) (sq_nonneg _)

/-- The pointwise weight comparison is summed over the complete positive
quadratic form, without altering its coefficient array or its phase. -/
theorem weightedEnergy_le_threshold {ι : Type*} [Fintype ι]
    (S : Finset ℕ) (ω : ℝ) {W T cap : ℝ}
    (hW : 0 < W) (hT : 0 < T) (exponent : ι → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (a : ι → ℕ → ℂ) :
    weightedEnergy S ω W exponent a ≤
      max 1 ((W / T) ^ cap) * weightedEnergy S ω T exponent a := by
  unfold weightedEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (rpow_le_threshold_multiplier hW hT (hexponent i) (hcap i))
    (sq_nonneg ‖∑ m ∈ S, phaseAt ω m * a i m‖)

/-- A full-block bound at `T`, uniform in the common phase, supplies the
actual clipped-block bound at any positive weight `W`. -/
theorem commonBlock_weightedEnergy_le {ι : Type*} [Fintype ι]
    (J j : ℕ) (ω bound : ℝ) {W T cap : ℝ}
    (hW : 0 < W) (hT : 0 < T) (exponent : ι → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ, weightedEnergy (fullBlock j) ρ T exponent a ≤ bound) :
    weightedEnergy (commonBlock J j) ω W exponent a ≤
      (2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound := by
  have hfull (ρ : ℝ) : weightedEnergy (fullBlock j) ρ W exponent a ≤
      max 1 ((W / T) ^ cap) * bound :=
    (weightedEnergy_le_threshold (fullBlock j) ρ hW hT exponent hexponent hcap a).trans
      (mul_le_mul_of_nonneg_left (full_uniform ρ) (le_trans zero_le_one (le_max_left _ _)))
  simpa only [weightedEnergy, mul_assoc] using
    commonBlock_weighted_energy_le_uniform_bound J j ω
      (max 1 ((W / T) ^ cap) * bound) (fun i => W ^ exponent i)
      (fun i => Real.rpow_nonneg hW.le _) a hfull

/-- The full weight range of the classical level-average input. -/
def threshold (V Z : ℝ) : ℝ := max V (Z ^ 2 / V)

def comparisonThreshold (V Z : ℝ) : ℝ := (V + Z) ^ 2 / V

theorem threshold_pos {V Z : ℝ} (hV : 0 < V) : 0 < threshold V Z := by
  exact lt_of_lt_of_le hV (le_max_left _ _)

theorem comparisonThreshold_pos {V Z : ℝ} (hV : 0 < V) (hZ : 0 < Z) :
    0 < comparisonThreshold V Z := by
  unfold comparisonThreshold
  positivity

theorem threshold_le_comparison {V Z : ℝ} (hV : 0 < V) (hZ : 0 < Z) :
    threshold V Z ≤ comparisonThreshold V Z := by
  unfold threshold comparisonThreshold
  apply max_le
  · apply (le_div_iff₀ hV).mpr
    have hcross : 0 ≤ V * Z := mul_nonneg hV.le hZ.le
    nlinarith only [hcross, sq_nonneg Z]
  · apply (div_le_iff₀ hV).mpr
    rw [div_mul_cancel₀ _ hV.ne']
    have hcross : 0 ≤ V * Z := mul_nonneg hV.le hZ.le
    nlinarith only [hcross, sq_nonneg V]

theorem comparison_le_four_threshold {V Z : ℝ} (hV : 0 < V) (_hZ : 0 < Z) :
    comparisonThreshold V Z ≤ 4 * threshold V Z := by
  have hVM : V ≤ threshold V Z := le_max_left _ _
  have hZM : Z ^ 2 / V ≤ threshold V Z := le_max_right _ _
  have hV2 : V ^ 2 ≤ threshold V Z * V := by
    have h := mul_le_mul_of_nonneg_right hVM hV.le
    nlinarith only [h]
  have hZ2 : Z ^ 2 ≤ threshold V Z * V := (div_le_iff₀ hV).mp hZM
  unfold comparisonThreshold
  apply (div_le_iff₀ hV).mpr
  nlinarith only [hV2, hZ2, sq_nonneg (V - Z)]

/-- The precise elementary continuation factor in the manuscript, before
absorbing the fixed constant and the interval-completion logarithm. -/
theorem threshold_multiplier_le {V Z W cap : ℝ}
    (hV : 0 < V) (hZ : 0 < Z) (hW : 0 < W) (hcap : 0 ≤ cap) :
    max 1 ((W / threshold V Z) ^ cap) ≤
      (4 : ℝ) ^ cap * (1 + (V * W / (V + Z) ^ 2) ^ cap) := by
  have hT : 0 < threshold V Z := threshold_pos hV
  have hQ : 0 < comparisonThreshold V Z := comparisonThreshold_pos hV hZ
  have hcomparison := comparison_le_four_threshold hV hZ
  have hratio : W / threshold V Z ≤ 4 * (W / comparisonThreshold V Z) := by
    calc
      _ ≤ (4 * W) / comparisonThreshold V Z :=
        (div_le_div_iff₀ hT hQ).mpr (by
          nlinarith only [mul_le_mul_of_nonneg_left hcomparison hW.le])
      _ = _ := by ring
  have hid : W / comparisonThreshold V Z = V * W / (V + Z) ^ 2 := by
    unfold comparisonThreshold
    field_simp [hV.ne', (add_pos hV hZ).ne']
  have hfour : 1 ≤ (4 : ℝ) ^ cap := Real.one_le_rpow (by norm_num) hcap
  have hpower := Real.rpow_nonneg (div_nonneg hW.le hQ.le) cap
  rw [← hid]
  apply max_le
  · nlinarith only [hfour, hpower, mul_nonneg (le_trans zero_le_one hfour) hpower]
  · calc
      _ ≤ (4 * (W / comparisonThreshold V Z)) ^ cap :=
        Real.rpow_le_rpow (div_nonneg hW.le hT.le) hratio hcap
      _ = (4 : ℝ) ^ cap * (W / comparisonThreshold V Z) ^ cap :=
        Real.mul_rpow (by norm_num) (div_nonneg hW.le hQ.le)
      _ ≤ _ := by nlinarith only [hfour]

/-- Common interval and arbitrary exceptional weight with the manuscript's
polynomial continuation factor. The full-block input still uses the actual
exponents, not their common upper bound. -/
theorem commonBlock_weightedEnergy_le_polynomial {ι : Type*} [Fintype ι]
    (J j : ℕ) (ω bound : ℝ) {V Z W cap : ℝ}
    (hV : 0 < V) (hZ : 0 < Z) (hW : 0 < W) (hcap : 0 ≤ cap)
    (exponent : ι → ℝ) (hexponent : ∀ i, 0 ≤ exponent i)
    (hexponent_cap : ∀ i, exponent i ≤ cap) (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ,
      weightedEnergy (fullBlock j) ρ (threshold V Z) exponent a ≤ bound) :
    weightedEnergy (commonBlock J j) ω W exponent a ≤
      (2 + Real.log (period j)) ^ 2 * (4 : ℝ) ^ cap *
        (1 + (V * W / (V + Z) ^ 2) ^ cap) * bound := by
  have hbound : 0 ≤ bound :=
    (weightedEnergy_nonneg (fullBlock j) 0 (threshold_pos hV).le exponent a).trans
      (full_uniform 0)
  refine (commonBlock_weightedEnergy_le J j ω bound hW (threshold_pos hV)
    exponent hexponent hexponent_cap a full_uniform).trans ?_
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (threshold_multiplier_le hV hZ hW hcap)
      (sq_nonneg (2 + Real.log (period j)))) hbound
  simpa only [mul_assoc] using h

/-- The eigenvalue-normalized version uses only the supplied lower bound
and the full-block estimate on that same coefficient array. -/
theorem commonBlock_tauEnergy_le {ι : Type*} [Fintype ι]
    (J j : ℕ) (ω bound : ℝ) {V Z W : ℝ}
    (hV : 0 < V) (hZ : 0 < Z) (hW : 0 < W)
    (lambda : ι → ℝ) (hlambda : ∀ i, (975 : ℝ) / 4096 ≤ lambda i)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ,
      weightedEnergy (fullBlock j) ρ (threshold V Z) (fun i => tau (lambda i)) a ≤ bound) :
    weightedEnergy (commonBlock J j) ω W (fun i => tau (lambda i)) a ≤
      (2 + Real.log (period j)) ^ 2 * (4 : ℝ) ^ (7 / 32 : ℝ) *
        (1 + (V * W / (V + Z) ^ 2) ^ (7 / 32 : ℝ)) * bound := by
  exact commonBlock_weightedEnergy_le_polynomial J j ω bound hV hZ hW (by norm_num)
    (fun i => tau (lambda i)) (fun i => tau_nonneg _)
    (fun i => tau_le_seven_thirtyseconds (hlambda i)) a full_uniform

/-- A bound uniform in finite spectral truncations proves convergence of
the complete exceptional energy as well as its estimate. This avoids the
zero-by-convention value of a nonsummable real `tsum`. -/
theorem commonBlock_tsum_weightedEnergy_le {ι : Type*}
    (J j : ℕ) (ω bound : ℝ) {W T cap : ℝ}
    (hW : 0 < W) (hT : 0 < T) (exponent : ι → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ (ρ : ℝ) (s : Finset ι),
      (∑ i ∈ s, T ^ exponent i * ‖∑ m ∈ fullBlock j, phaseAt ρ m * a i m‖ ^ 2) ≤ bound) :
    Summable (fun i => W ^ exponent i *
      ‖∑ m ∈ commonBlock J j, phaseAt ω m * a i m‖ ^ 2) ∧
    (∑' i, W ^ exponent i * ‖∑ m ∈ commonBlock J j, phaseAt ω m * a i m‖ ^ 2) ≤
      (2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound := by
  classical
  have hnonneg (i : ι) : 0 ≤ W ^ exponent i *
      ‖∑ m ∈ commonBlock J j, phaseAt ω m * a i m‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hW.le _) (sq_nonneg _)
  have hfinite (s : Finset ι) :
      (∑ i ∈ s, W ^ exponent i * ‖∑ m ∈ commonBlock J j, phaseAt ω m * a i m‖ ^ 2) ≤
        (2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound := by
    have hsum (S : Finset ℕ) (ρ X : ℝ) :
        weightedEnergy S ρ X (fun i : s => exponent i) (fun i : s => a i) =
          ∑ i ∈ s, X ^ exponent i * ‖∑ m ∈ S, phaseAt ρ m * a i m‖ ^ 2 :=
      Finset.sum_coe_sort s
        (fun i : ι => X ^ exponent i * ‖∑ m ∈ S, phaseAt ρ m * a i m‖ ^ 2)
    have hfull (ρ : ℝ) :
        weightedEnergy (fullBlock j) ρ T (fun i : s => exponent i) (fun i : s => a i) ≤ bound := by
      rw [hsum]
      exact full_uniform ρ s
    simpa only [hsum] using
      commonBlock_weightedEnergy_le J j ω bound hW hT (fun i : s => exponent i)
        (fun i => hexponent i) (fun i => hcap i) (fun i : s => a i) hfull
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

/-- A common subinterval of the original full positive integer block. -/
def commonIoc (lo hi j : ℕ) : Finset ℕ := fullBlock j ∩ Finset.Ioc lo hi

theorem commonIoc_eq_sdiff (lo hi j : ℕ) :
    commonIoc lo hi j = commonBlock hi j \ commonBlock lo j := by
  ext m
  simp only [commonIoc, commonBlock, fullBlock, Finset.mem_inter,
    Finset.mem_Ioc, Finset.mem_Ico, Finset.mem_sdiff, lt_min_iff]
  omega

theorem commonBlock_mono {lo hi : ℕ} (h : lo ≤ hi) (j : ℕ) :
    commonBlock lo j ⊆ commonBlock hi j := by
  intro m hm
  simp only [commonBlock, Finset.mem_Ico, lt_min_iff] at hm ⊢
  omega

/-- The interval sum is a difference of two prefixes with the same phase
and the same coefficient array at every level. -/
theorem commonIoc_sum_eq_sub {lo hi : ℕ} (h : lo ≤ hi) (j : ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ commonIoc lo hi j, f m) =
      (∑ m ∈ commonBlock hi j, f m) - ∑ m ∈ commonBlock lo j, f m := by
  rw [commonIoc_eq_sdiff]
  exact Finset.sum_sdiff_eq_sub (commonBlock_mono h j)

/-- Squared Hilbert energy for the difference of the two common prefixes. -/
theorem commonIoc_weightedEnergy_le_prefixes {ι : Type*} [Fintype ι]
    {lo hi : ℕ} (h : lo ≤ hi) (j : ℕ) (ω : ℝ) {W : ℝ} (hW : 0 ≤ W)
    (exponent : ι → ℝ) (a : ι → ℕ → ℂ) :
    weightedEnergy (commonIoc lo hi j) ω W exponent a ≤
      2 * (weightedEnergy (commonBlock hi j) ω W exponent a +
        weightedEnergy (commonBlock lo j) ω W exponent a) := by
  unfold weightedEnergy
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [commonIoc_sum_eq_sub h]
  have hsq (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have hp := pow_le_pow_left₀ (norm_nonneg (x - y)) (norm_sub_le x y) 2
    nlinarith only [hp, sq_nonneg (‖x‖ - ‖y‖)]
  have hp := mul_le_mul_of_nonneg_left
    (hsq (∑ m ∈ commonBlock hi j, phaseAt ω m * a i m)
      (∑ m ∈ commonBlock lo j, phaseAt ω m * a i m))
    (Real.rpow_nonneg hW (exponent i))
  nlinarith only [hp]

/-- Any common `Ioc` subinterval has at most four times the squared
completion cost of a prefix. No interval is chosen separately by level. -/
theorem commonIoc_weightedEnergy_le {ι : Type*} [Fintype ι]
    {lo hi : ℕ} (h : lo ≤ hi) (j : ℕ) (ω bound : ℝ) {W T cap : ℝ}
    (hW : 0 < W) (hT : 0 < T) (exponent : ι → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ, weightedEnergy (fullBlock j) ρ T exponent a ≤ bound) :
    weightedEnergy (commonIoc lo hi j) ω W exponent a ≤
      4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound) := by
  have hhi := commonBlock_weightedEnergy_le hi j ω bound hW hT
    exponent hexponent hcap a full_uniform
  have hlo := commonBlock_weightedEnergy_le lo j ω bound hW hT
    exponent hexponent hcap a full_uniform
  have hinterval := commonIoc_weightedEnergy_le_prefixes h j ω hW.le exponent a
  linarith

/-- Zero endpoints are harmless because every original block is positive. -/
theorem fullBlock_inter_Ico_eq_commonIoc (lo hi j : ℕ) :
    fullBlock j ∩ Finset.Ico lo hi = commonIoc (lo - 1) (hi - 1) j := by
  ext m
  have hpos : 0 < (2 : ℕ) ^ j := by positivity
  simp only [commonIoc, fullBlock, Finset.mem_inter, Finset.mem_Ico, Finset.mem_Ioc]
  omega

theorem commonIco_weightedEnergy_le {ι : Type*} [Fintype ι]
    {lo hi : ℕ} (h : lo ≤ hi) (j : ℕ) (ω bound : ℝ) {W T cap : ℝ}
    (hW : 0 < W) (hT : 0 < T) (exponent : ι → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ, weightedEnergy (fullBlock j) ρ T exponent a ≤ bound) :
    weightedEnergy (fullBlock j ∩ Finset.Ico lo hi) ω W exponent a ≤
      4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound) := by
  rw [fullBlock_inter_Ico_eq_commonIoc]
  exact commonIoc_weightedEnergy_le (Nat.sub_le_sub_right h 1) j ω bound hW hT
    exponent hexponent hcap a full_uniform

end

end ImbalancedChen.Part3.ExceptionalWeightExtension
