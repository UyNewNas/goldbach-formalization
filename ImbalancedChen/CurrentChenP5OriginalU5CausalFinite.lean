import ImbalancedChen.CurrentChenP5CausalRhoQuotientBridge
import ImbalancedChen.Part5OriginalUpsilon5CausalDictionary

/-!
# Actual original U5 count entrance with genuine even-exit lower rho

The full original U5 selector and enhanced max-level dictionary are used.
A common small-weight presieve scale nu0=34/125 lies below every genuine
U5 residual. It is only an attachment reserve: it does not replace the
original enhanced V or R of the rough policy. This common choice permits
the actual full-density projection supplier to choose one epsilon and
threshold before all original pair labels and retention policies.

The signed primitive discrepancies and literal prime/centre costs remain
finite actual sums. No ordinary BV, enhanced total-support license, h248
count semantics or integral coefficient is supplied or assumed.

SOURCE ONLY: uncompiled; companion draft imports remain source-only.
-/

namespace ImbalancedChen.P5OriginalU5CausalFinite

open scoped BigOperators
open Classical

noncomputable section

abbrev cutoff (N : ℕ) : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)
abbrev pairSupport (N : ℕ) : Finset (ℕ × ℕ) :=
  chenY5PrimeSelector N (cutoff N) ((N : ℝ) ^ (19 / 125 : ℝ))

def coordinates (N : ℕ) (t : ℕ × ℕ) : Fin 2 → ℝ :=
  actualPrimeTupleLog N ![t.1, t.2]

theorem coordinates_mem_triangle {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    coordinates N t ∈ Part5OriginalUpsilon5CausalDictionary.triangle := by
  obtain ⟨hc, hA, horder, hH⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  have hp0 := (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq0 := (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  have hpos : ∀ i : Fin 2, 0 < (![t.1, t.2] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i <;> assumption
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpow := actualPrimeTupleLog_rpow (by omega : 1 < N) ![t.1, t.2] hpos
  rw [Part5OriginalUpsilon5CausalDictionary.mem_triangle]
  constructor
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    change (N : ℝ) ^ (417 / 5000 : ℝ) ≤
      (N : ℝ) ^ actualPrimeTupleLog N ![t.1, t.2] 0
    rw [hpow 0]
    exact hA
  constructor
  · apply (Real.rpow_lt_rpow_left_iff hNr).mp
    change (N : ℝ) ^ actualPrimeTupleLog N ![t.1, t.2] 0 <
      (N : ℝ) ^ actualPrimeTupleLog N ![t.1, t.2] 1
    rw [hpow 0, hpow 1]
    exact_mod_cast horder
  · apply (Real.rpow_lt_rpow_left_iff hNr).mp
    change (N : ℝ) ^ actualPrimeTupleLog N ![t.1, t.2] 1 <
      (N : ℝ) ^ (19 / 125 : ℝ)
    rw [hpow 1]
    exact hH

def originalResidual (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  Part5OriginalUpsilon5CausalDictionary.residual (coordinates N t)

def attachmentNu : ℝ := 34 / 125
def attachmentR : ℝ := (417 / 5000 : ℝ) / attachmentNu

theorem attachmentNu_mul_attachmentR : attachmentNu * attachmentR = (417 / 5000 : ℝ) := by
  norm_num [attachmentNu, attachmentR]

/-- All enhanced V/R/s/alpha gates are supplied by the original U5
dictionary on the literal selector, not assumed as target mean inputs. -/
theorem original_geometry {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    attachmentNu ≤ originalResidual N t ∧ 0 < originalResidual N t ∧
      (417 / 5000 : ℝ) < originalResidual N t / 2 ∧
      Part5OriginalUpsilon5CausalDictionary.argument (coordinates N t) ∈ Set.Icc (2 : ℝ) 5 ∧
      2 ≤ Part5OriginalUpsilon5CausalDictionary.alpha (coordinates N t) := by
  have hx := coordinates_mem_triangle hN ht
  obtain ⟨hu, hut, hh⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp hx
  have hb := Part5OriginalUpsilon5CausalDictionary.residual_bounds hu hut.le hh.le
  have hcut := Part5OriginalUpsilon5CausalDictionary.cutoff_square hx
  refine ⟨hb.1, Part5OriginalUpsilon5CausalDictionary.residual_pos hx, ?_,
    Part5OriginalUpsilon5CausalDictionary.argument_mem hx,
    Part5OriginalUpsilon5CausalDictionary.alpha_ge_two hx⟩
  dsimp [Part5OriginalUpsilon5CausalDictionary.residual,
    Part5OriginalUpsilon5CausalDictionary.a] at hcut ⊢
  change (417 / 5000 : ℝ) <
    Part5OriginalUpsilon5CausalDictionary.residual (coordinates N t) / 2
  unfold Part5OriginalUpsilon5CausalDictionary.residual
  linarith

def smallCutoff (N : ℕ) (epsilon : ℝ) : ℝ :=
  (N : ℝ) ^ (attachmentNu * epsilon ^ 2)

def smallLevel (N : ℕ) (epsilon : ℝ) : ℝ :=
  (N : ℝ) ^ (attachmentNu * epsilon)

theorem attachment_gates {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8) :
    1 < smallLevel N epsilon ∧ smallCutoff N epsilon ≤ smallLevel N epsilon ∧
      smallCutoff N epsilon ≤ cutoff N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hnu : 0 < attachmentNu := by norm_num [attachmentNu]
  have hsq : epsilon ^ 2 ≤ epsilon := by nlinarith
  have hsq64 : epsilon ^ 2 ≤ 1 / 64 := by nlinarith
  have hcut : attachmentNu * epsilon ^ 2 ≤ (417 / 5000 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hsq64 hnu.le
    norm_num [attachmentNu] at hm
    linarith only [hm]
  refine ⟨Real.one_lt_rpow hNr (mul_pos hnu heps), ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hNr.le
      (mul_le_mul_of_nonneg_left hsq hnu.le)
  · exact Real.rpow_le_rpow_of_exponent_le hNr.le hcut

/-- Reducing the small attachment level does not alter the enhanced V.
It leaves a genuine per-pair residual reserve for the historical policy. -/
theorem smallLevel_le_originalResidualPower {N : ℕ} (hN : 2 ≤ N)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    smallLevel N epsilon ≤ (N : ℝ) ^ (originalResidual N t * epsilon) := by
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega))
    (mul_le_mul_of_nonneg_right (original_geometry hN ht).1 heps)

def support (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool) : Finset ℕ :=
  actualLowerSmallRoughModuli policy N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N)

def rho (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool) (k : ℕ) : ℝ :=
  actualLowerSmallRoughRho policy N (Nat.ceil (cutoff N))
    (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) k

def density (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool) : ℝ :=
  physicalDensitySum (support N epsilon policy) (rho N epsilon policy)

def fullDensity (N : ℕ) (policy : List ℕ → Bool) : ℝ :=
  reciprocalTotientDensity (fixedEvenRoughSupport policy N (Nat.ceil (cutoff N)) 0 (cutoff N))
    (fixedEvenRoughCoefficient policy N (Nat.ceil (cutoff N)) 0 (cutoff N))

def rowMain (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  ((chenPrimePrefix N).card : ℝ) / (Nat.totient (t.1 * t.2) : ℝ) * density N epsilon policy

def rowSignedPrimitive (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ support N epsilon policy, rho N epsilon policy k *
    finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((t.1 * t.2) * k)

def rowPrimeCost (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ support N epsilon policy,
    chenPrimeDivisorCount N ((t.1 * t.2) * k) / (Nat.totient ((t.1 * t.2) * k) : ℝ)

def rowCentreCost (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ support N epsilon policy, chenCentrePrimeAPCount N N ((t.1 * t.2) * k)

def rowSignedPrimeCorrection (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool)
    (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ support N epsilon policy, rho N epsilon policy k *
    (chenPrimeDivisorCount N ((t.1 * t.2) * k) / (Nat.totient ((t.1 * t.2) * k) : ℝ))

def rowSignedCentreCorrection (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool)
    (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ support N epsilon policy, rho N epsilon policy k *
    chenCentrePrimeAPCount N N ((t.1 * t.2) * k)

def rowDivisorEstimator (N : ℕ) (epsilon : ℝ) (policy : List ℕ → Bool)
    (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ support N epsilon policy, rho N epsilon policy k *
    (chenPrimeAPCount N N ((t.1 * t.2) * k) - chenCentrePrimeAPCount N N ((t.1 * t.2) * k))

def rowAPMain (N : ℕ) (epsilon M : ℝ) (policy : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  M / (Nat.totient (t.1 * t.2) : ℝ) * density N epsilon policy

def rowSignedAP (N : ℕ) (epsilon M : ℝ) (policy : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ support N epsilon policy, rho N epsilon policy k *
    chenQuotientPrimeAPError N M ((t.1 * t.2) * k)

theorem row_multiplier_rough {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    ChenPrimeRough (cutoff N) (t.1 * t.2) := by
  have hb := chenY5PrimeSelector_sieve_data ht
  exact (chenPrimeRough_iff_coprime_sieveProduct (cutoff N) hb.2.1).mpr hb.2.2

/-- Arbitrary comparison mass includes true li(N); the genuine rho is
identical in the finite AP decomposition and its pointwise minorant. -/
theorem rowDivisorEstimator_eq_main_AP {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8) (M : ℝ)
    (policy : List ℕ → Bool) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    rowDivisorEstimator N epsilon policy t = rowAPMain N epsilon M policy t +
      rowSignedAP N epsilon M policy t - rowSignedCentreCorrection N epsilon policy t := by
  exact P5CausalRhoQuotientBridge.quotient_main_and_AP_errors policy N
    (Nat.ceil (cutoff N)) (t.1 * t.2) (smallCutoff N epsilon) (cutoff N)
    (smallLevel N epsilon) M (attachment_gates hN heps heps8).2.2 (row_multiplier_rough ht)

/-- Actual enhanced causal coefficient lower bound, carrying the signed
P3 discrepancy and paying both exceptional prime sets by proved costs. -/
theorem row_lower {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8)
    (policy : List ℕ → Bool) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    rowMain N epsilon policy t + rowSignedPrimitive N epsilon policy t -
      rowPrimeCost N epsilon policy t - rowCentreCost N epsilon policy t ≤
      ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (cutoff N)).card : ℝ) := by
  have hg := attachment_gates hN heps heps8
  have hlo := P5CausalRhoQuotientBridge.quotient_signed_sum_le_sifted policy N
    (t.1 * t.2) (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N)
    (smallLevel N epsilon) hg.1 hg.2.1 hg.2.2 (Nat.le_ceil _)
  rw [P5CausalRhoQuotientBridge.quotient_main_primitive_and_prime_corrections
    policy N (Nat.ceil (cutoff N)) (t.1 * t.2) (smallCutoff N epsilon) (cutoff N)
    (smallLevel N epsilon) hg.2.2 (row_multiplier_rough ht)] at hlo
  have hprime : rowSignedPrimeCorrection N epsilon policy t ≤
      rowPrimeCost N epsilon policy t := by
    apply Finset.sum_le_sum
    intro k hk
    have hrho := (le_abs_self (rho N epsilon policy k)).trans
      (actualLowerSmallRoughRho_abs_le_one policy N (Nat.ceil (cutoff N))
        (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) k)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrho
      (div_nonneg (chenPrimeDivisorCount_nonneg N _) (Nat.cast_nonneg _))
  have hcentre : rowSignedCentreCorrection N epsilon policy t ≤ rowCentreCost N epsilon policy t := by
    apply Finset.sum_le_sum
    intro k hk
    have hrho := (le_abs_self (rho N epsilon policy k)).trans
      (actualLowerSmallRoughRho_abs_le_one policy N (Nat.ceil (cutoff N))
        (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) k)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrho
      (chenCentrePrimeAPCount_nonneg N N ((t.1 * t.2) * k))
  change rowMain N epsilon policy t + rowSignedPrimitive N epsilon policy t -
    rowSignedPrimeCorrection N epsilon policy t - rowSignedCentreCorrection N epsilon policy t ≤ _ at hlo
  linarith only [hlo, hprime, hcentre]

def mainSum (N : ℕ) (epsilon : ℝ) (policy : (ℕ × ℕ) → List ℕ → Bool) : ℝ :=
  ∑ t ∈ pairSupport N, rowMain N epsilon (policy t) t

def signedPrimitiveSum (N : ℕ) (epsilon : ℝ) (policy : (ℕ × ℕ) → List ℕ → Bool) : ℝ :=
  ∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon (policy t) t

def primeCostSum (N : ℕ) (epsilon : ℝ) (policy : (ℕ × ℕ) → List ℕ → Bool) : ℝ :=
  ∑ t ∈ pairSupport N, rowPrimeCost N epsilon (policy t) t

def centreCostSum (N : ℕ) (epsilon : ℝ) (policy : (ℕ × ℕ) → List ℕ → Bool) : ℝ :=
  ∑ t ∈ pairSupport N, rowCentreCost N epsilon (policy t) t

theorem originalU5_causal_lower {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8)
    (policy : (ℕ × ℕ) → List ℕ → Bool) :
    mainSum N epsilon policy + signedPrimitiveSum N epsilon policy -
      primeCostSum N epsilon policy - centreCostSum N epsilon policy ≤ currentChenUpsilon5 N := by
  rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
  have hsum := Finset.sum_le_sum (fun t ht => row_lower hN heps heps8 (policy t) ht)
  simpa only [mainSum, signedPrimitiveSum, primeCostSum, centreCostSum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] using hsum

def fullProjectedMainSum (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool) : ℝ :=
  ∑ t ∈ pairSupport N,
    ((chenPrimePrefix N).card : ℝ) / (Nat.totient (t.1 * t.2) : ℝ) * fullDensity N (policy t)

def projectionReserve (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ pairSupport N,
    ((chenPrimePrefix N).card : ℝ) / (Nat.totient (t.1 * t.2) : ℝ) *
      (eta * singularSeries N / Real.log (N : ℝ))

/-- Actual full-policy projection is uniform before all marked pairs and
policies. The finite signed discrepancies and prime costs remain actual,
with no enhanced-level BV assertion. -/
theorem exists_originalU5_full_density_causal_lower
    (eta epsilonMax : ℝ) (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
          fullProjectedMainSum N policy - projectionReserve N eta +
            signedPrimitiveSum N epsilon policy - primeCostSum N epsilon policy -
            centreCostSum N epsilon policy ≤ currentChenUpsilon5 N := by
  obtain ⟨epsilon, heps, heps8, hepsMax, _hepsr, N₀, hN₀, hproj⟩ :=
    exists_actualLowerSmallRoughRho_density_ge_full_reserve
      attachmentNu attachmentR eta epsilonMax
      (by norm_num [attachmentNu]) (by norm_num [attachmentR, attachmentNu]) heta hepsilonMax
  refine ⟨epsilon, heps, heps8, hepsMax, N₀, hN₀, ?_⟩
  intro N hN hEven policy
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hmain : fullProjectedMainSum N policy - projectionReserve N eta ≤
      mainSum N epsilon policy := by
    rw [fullProjectedMainSum, projectionReserve, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have hcap : (N : ℝ) ^ (attachmentNu * attachmentR) ≤ (Nat.ceil (cutoff N) : ℝ) := by
      rw [attachmentNu_mul_attachmentR]
      exact Nat.le_ceil _
    have h := hproj N hN hEven (Nat.ceil (cutoff N)) hcap (policy t)
    dsimp only at h
    rw [attachmentNu_mul_attachmentR] at h
    have hscaled := mul_le_mul_of_nonneg_left h
      (div_nonneg (Nat.cast_nonneg (chenPrimePrefix N).card)
        (Nat.cast_nonneg (Nat.totient (t.1 * t.2))))
    change _ ≤ rowMain N epsilon (policy t) t
    simpa only [rowMain, density, fullDensity, rho, support, smallCutoff, smallLevel, mul_sub] using hscaled
  have hfinite := originalU5_causal_lower hN2 heps heps8 policy
  linarith only [hmain, hfinite]

end

end ImbalancedChen.P5OriginalU5CausalFinite
