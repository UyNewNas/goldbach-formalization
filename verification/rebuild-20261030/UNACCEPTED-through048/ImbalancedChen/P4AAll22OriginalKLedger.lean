import ImbalancedChen.CurrentUpperEighteenBudget
import ImbalancedChen.Certificates.AboveMuSecondCoarse
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve
import ImbalancedChen.SourceDensityScale
import Mathlib.Tactic.Ring

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Original all22 arithmetic, with actual tail and coarse-chart suppliers consumed.
The manuscript's four positive / twenty-two saving expression is in C_N/log N
units. Slots 21 and 22 are increments; slot 5 is replaced, never added twice.
The first-integral and compact-third endpoints and the other 21 saving endpoints
remain quoted. Therefore the closed two-supplier ledger below is NOT the full
actual integral functional, a density, or a numerical certificate for all22.
No final-density, raw-K, component-enclosure, or equivalent-total premise occurs.
The second consumer retains the actual compact-third integral, consumes the
actual finite-third approximation, and records precisely its u/4 expenditure.
-/
namespace ImbalancedChen.P4AAll22OriginalKLedger20261024zSourceOnly

noncomputable section
open MeasureTheory
open scoped BigOperators

def finalFourGains : Fin 4 → ℝ :=
  ![283388722705335806564439 / 2^96,
    14750615007945677662815 / 2^95,
    77410436074156865471 / 2^96,
    481322793305152847935 / 2^96]

/-- Whole adopted endpoint, with the refined estimates retained literally. -/
def quotedAll22Raw : ℝ :=
  currentUpperEighteenRaw - ∑ i, finalFourGains i

/-- Density approximation and compilation are different expenditures. -/
def densityReserve : ℝ :=
  145007961227048312210593427530128000784681 /
    11807308407697609823574244952794825721118720000

def compilerReserve : ℝ :=
  145007961227048312210593427530128000784681 /
    11807308407697609823574244952794825721118720000

def exactSlack : ℝ :=
  71229286727542131248758574547050908572431 /
    737956775481100613973390309549676607569920000000

theorem ordinary_root_normalization :
    4 / thirdPrefixTheta = (2000 / 299 : ℝ) := by
  norm_num [thirdPrefixTheta]

theorem fifth_saving_slot_is_coarse_endpoint :
    currentUpperEighteenGains 4 = (640339 / 15210735000 : ℝ) := by
  rfl

theorem finalFourGains_sum :
    (∑ i, finalFourGains i) = 313448685950606471603475 / 2^96 := by
  norm_num [finalFourGains, Fin.sum_univ_succ]

theorem quotedAll22Raw_eq :
    quotedAll22Raw =
      9979702576710911234850619807816847864907359959 /
        1475913550962201227946780619099353215139840000 := by
  unfold quotedAll22Raw
  rw [currentUpperEighteenRaw_eq, finalFourGains_sum]
  norm_num

theorem exact_original_budget_identity :
    quotedAll22Raw + densityReserve + compilerReserve + exactSlack = currentK := by
  rw [quotedAll22Raw_eq]
  norm_num [densityReserve, compilerReserve, exactSlack, currentK]

theorem densityReserve_pos : 0 < densityReserve := by
  norm_num [densityReserve]

theorem compilerReserve_pos : 0 < compilerReserve := by
  norm_num [compilerReserve]

theorem exactSlack_pos : 0 < exactSlack := by
  norm_num [exactSlack]

theorem quotedAll22Raw_with_original_reserves_lt_K :
    quotedAll22Raw + densityReserve + compilerReserve < currentK := by
  linarith only [exact_original_budget_identity, exactSlack_pos]

/-- The actual integral, with the literal original ordering and ideal cap. -/
def actualOriginalThirdTail : ℝ :=
  ∫ t in actualExtendedThirdManuscriptTailRegion 0 (1 / 100),
    actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)

/-- The genuine two-chart integral. Domain identification with the physical
policy remains a distinct obligation; its real integral bound is already proved. -/
def actualCoarseSecondSaving : ℝ :=
  Certificates.AboveMuSecondCoarse.totalChartIntegral

theorem actualOriginalThirdTail_le :
    actualOriginalThirdTail ≤ 319683857488126290909150567 / 2^111 := by
  exact OriginalThirdTailActualIdealSourceOnly.original_manuscript_tail_integral_le_Tnew

theorem actualCoarseSecondSaving_ge :
    (640339 / 15210735000 : ℝ) ≤ actualCoarseSecondSaving := by
  exact Certificates.AboveMuSecondCoarse.adopted_coarse_lower

/-- Replace the tail and fifth saving slot once. The other entries are quoted.
The `+ slot 5 - actual chart` form makes the replacement explicit. -/
def twoSupplierLedger : ℝ :=
  (2000 / 299 + 7179974843999672947 / 2^73 +
    144590669409566793572719 / 2^80 + actualOriginalThirdTail) -
    (∑ i, currentUpperEighteenGains i) - (∑ i, finalFourGains i) +
    640339 / 15210735000 - actualCoarseSecondSaving

theorem twoSupplierLedger_replacement_identity :
    twoSupplierLedger = quotedAll22Raw +
      (actualOriginalThirdTail - 319683857488126290909150567 / 2^111) -
      (actualCoarseSecondSaving - 640339 / 15210735000) := by
  have hp : (∑ i, currentUpperEighteenPositive i) =
      (2000 / 299 + 7179974843999672947 / 2^73 +
        144590669409566793572719 / 2^80 +
        319683857488126290909150567 / 2^111 : ℝ) := by
    norm_num [currentUpperEighteenPositive, Fin.sum_univ_succ]
  unfold twoSupplierLedger quotedAll22Raw currentUpperEighteenRaw
  rw [hp]
  ring

/-- Closed consumption of two named suppliers; no enclosure hypothesis. -/
theorem twoSupplierLedger_le_quotedAll22Raw :
    twoSupplierLedger ≤ quotedAll22Raw := by
  rw [twoSupplierLedger_replacement_identity]
  linarith only [actualOriginalThirdTail_le, actualCoarseSecondSaving_ge]

theorem twoSupplierLedger_with_reserves_and_slack_le_K :
    twoSupplierLedger + densityReserve + compilerReserve + exactSlack ≤ currentK := by
  linarith only [twoSupplierLedger_le_quotedAll22Raw, exact_original_budget_identity]

theorem twoSupplierLedger_with_original_reserves_lt_K :
    twoSupplierLedger + densityReserve + compilerReserve < currentK := by
  linarith only [twoSupplierLedger_with_reserves_and_slack_le_K, exactSlack_pos]

theorem original_third_reserve_is_density_reserve :
    OriginalThirdFiniteReserveSourceOnly.originalDensityReserve = densityReserve := by
  rfl

/-- All other density approximation errors still have only 3u/4 available. -/
theorem original_density_reserve_split :
    densityReserve / 4 + 3 * densityReserve / 4 = densityReserve := by
  ring

theorem original_budget_after_quarter_payment :
    quotedAll22Raw + densityReserve / 4 + 3 * densityReserve / 4 +
      compilerReserve + exactSlack = currentK := by
  calc
    _ = quotedAll22Raw + densityReserve + compilerReserve + exactSlack := by ring
    _ = currentK := exact_original_budget_identity

theorem three_quarters_densityReserve_pos : 0 < 3 * densityReserve / 4 := by
  linarith only [densityReserve_pos]

/-- Actual finite third functional, with the other entries still explicitly
quoted. There is no compact-third certificate hidden in this definition. -/
def finiteThirdPartialLedger (e : ℝ) (m : ℕ) : ℝ :=
  (2000 / 299 + 7179974843999672947 / 2^73 +
    actualExtendedThirdFiniteFunctional e m) -
    (∑ i, currentUpperEighteenGains i) - (∑ i, finalFourGains i) +
    640339 / 15210735000 - actualCoarseSecondSaving

/-- The actual compact integral is retained on the right. It is not replaced
by the unproved quoted compact endpoint. -/
def compactThirdPartialLedger : ℝ :=
  (2000 / 299 + 7179974843999672947 / 2^73 +
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection +
    319683857488126290909150567 / 2^111) -
    (∑ i, currentUpperEighteenGains i) - (∑ i, finalFourGains i) +
    640339 / 15210735000 - actualCoarseSecondSaving

/-- One actual uniform approximation supplier; precisely u/4 is spent. -/
theorem finiteThirdPartialLedger_le_compact_plus_quarter :
    ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
        finiteThirdPartialLedger e m ≤ compactThirdPartialLedger + densityReserve / 4 := by
  obtain ⟨e₀, he₀, hcap, m₀, hfinite⟩ :=
    OriginalThirdFiniteReserveSourceOnly.finiteFunctional_le_compact_add_Tnew_add_original_density_quarter
  refine ⟨e₀, he₀, hcap, m₀, ?_⟩
  intro e he0 he m hm
  have h := hfinite e he0 he m hm
  rw [original_third_reserve_is_density_reserve] at h
  unfold finiteThirdPartialLedger compactThirdPartialLedger
  linarith only [h]

/-- Exact normalization of the remaining budget; this is an identity, not
an asymptotic claim about the physical density of a compiled policy. -/
theorem original_budget_in_manuscript_units (N : ℕ) :
    (quotedAll22Raw + densityReserve + compilerReserve + exactSlack) *
        (singularSeries N / Real.log (N : ℝ)) =
      currentK * (singularSeries N / Real.log (N : ℝ)) := by
  rw [exact_original_budget_identity]

theorem source_mass_times_original_budget (N : ℕ) :
    ((N : ℝ) / Real.log (N : ℝ)) *
        ((quotedAll22Raw + densityReserve + compilerReserve + exactSlack) *
          (singularSeries N / Real.log (N : ℝ))) =
      currentK * singularNormalization N := by
  rw [exact_original_budget_identity]
  calc
    _ = currentK * (((N : ℝ) / Real.log (N : ℝ)) *
        (singularSeries N / Real.log (N : ℝ))) := by ring
    _ = _ := by rw [sourceMassScale_mul_densityScale]

end
end ImbalancedChen.P4AAll22OriginalKLedger20261024zSourceOnly
