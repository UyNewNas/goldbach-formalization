import ImbalancedChen.Certificates.PairedV2Data

/-!
# The first actual row of the adopted same-mask-v2 certificate

Source row 0 is E0, t-index 422, u-index 510. The deterministic importer
checks the complete frozen source hash and emits this row's exact rational
coordinates. This file checks its geometry and a numerical certificate in
Lean, then concludes bounds on its genuine fourfold integral.

The bounds are deliberately independent, weaker rational enclosures. No
claim is made here that the source's much tighter Q160 interval, all 17572
row integrals, or the complete lower-count coefficient have been proved.
-/

namespace ImbalancedChen.Certificates.PairedV2

open MeasureTheory Set
open scoped Interval

theorem first_coordinates :
    tLower firstTIndex = (937361 / 4096000 : ℚ) ∧
    tUpper firstTIndex = (1875373 / 8192000 : ℚ) ∧
    uLower firstUIndex = (194217 / 1280000 : ℚ) ∧
    uUpper firstUIndex = (388777 / 2560000 : ℚ) := by
  norm_num [tLower, tUpper, uLower, uUpper, firstTIndex, firstUIndex, a, h, d, mu]

/-- The decoded cutoff is exactly the currently adopted 7/3 cutoff. -/
theorem first_cutoff_definition :
    firstZ = min (uLower firstUIndex)
      (3 * (1 - tUpper firstTIndex - uUpper firstUIndex) / 13) := by
  norm_num [firstZ, tUpper, uLower, uUpper, firstTIndex, firstUIndex, a, h, d, mu]

/-- Finite, exact checks on the actual imported cell. -/
theorem first_geometry_checked :
    0 < a ∧ a < firstZ ∧ firstZ ≤ uLower firstUIndex ∧
    uLower firstUIndex < uUpper firstUIndex ∧ uUpper firstUIndex < h ∧
    h < tLower firstTIndex ∧ tLower firstTIndex < tUpper firstTIndex ∧
    tUpper firstTIndex < d ∧
    (13 / 3 : ℚ) * firstZ ≤ 1 - tUpper firstTIndex - uUpper firstUIndex ∧
    (57 / 64 : ℚ) - (5 / 2) * tLower firstTIndex - uLower firstUIndex ≤ 2 * a ∧
    firstDiscardedQ80 = 0 := by
  norm_num [firstZ, tLower, tUpper, uLower, uUpper, firstTIndex, firstUIndex,
    a, h, d, mu, firstDiscardedQ80]

/-- A semantic description of the exact actual cell, including its
triangular inner fibre. The outer closed endpoints are also legal. -/
def firstFibreSupport (t u z w : ℝ) : Prop :=
  (937361 / 4096000 : ℝ) ≤ t ∧ t ≤ 1875373 / 8192000 ∧
    (194217 / 1280000 : ℝ) ≤ u ∧ u ≤ 388777 / 2560000 ∧
    (417 / 5000 : ℝ) < w ∧ w < z ∧ z < 76088109 / 532480000

/-- The 7/3 argument inequality is checked on the entire actual fibre,
not just at a sampled point or at its centre. -/
theorem first_fibre_argument {t u z w : ℝ} (hs : firstFibreSupport t u z w) :
    (417 / 5000 : ℝ) < w ∧ w < z ∧ z < u ∧ u < 19 / 125 ∧
      (19 / 125 : ℝ) < t ∧ t < 59 / 250 ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z := by
  rcases hs with ⟨htl, htr, hul, hur, hw, hwz, hz⟩
  have hzpos : 0 < z := by linarith
  refine ⟨hw, hwz, by linarith, by linarith, by linarith, by linarith, ?_⟩
  apply (le_div_iff₀ hzpos).2
  linarith

theorem first_fibre_nonempty : ∃ t u z w : ℝ, firstFibreSupport t u z w := by
  refine ⟨(937361 / 4096000 + 1875373 / 8192000) / 2,
    (194217 / 1280000 + 388777 / 2560000) / 2,
    (417 / 5000 + 76088109 / 532480000) / 2,
    (3 * (417 / 5000) + 76088109 / 532480000) / 4, ?_⟩
  norm_num [firstFibreSupport]

/-- This is a proof-producing rational check, not `native_decide`. -/
theorem first_certificate_checked : firstCertificate.check = true := by
  norm_num [PairedIntegralCertificate.check, PairedIntegralCertificate.Valid,
    RationalLogCertificate.check, RationalLogCertificate.Valid,
    PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper,
    PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper,
    logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ,
    firstCertificate, tLower, tUpper, uLower, uUpper, firstTIndex, firstUIndex,
    a, h, d, mu, K, firstZ]

/-- The actual adopted row's integral, in Chen-quarter units with the
additional 1/20 Buchstab mass and no extra permutation factor. -/
noncomputable def firstIntegral : ℝ :=
  pairedLocalIntegral (8452171 / 1250000) (417 / 5000)
    (937361 / 4096000) (1875373 / 8192000)
    (194217 / 1280000) (388777 / 2560000) (76088109 / 532480000)

/-- Explicitly expose the actual fourfold integration object. -/
theorem firstIntegral_semantics :
    firstIntegral = ((8452171 / 1250000 : ℝ) / 80) *
      ∫ t in (937361 / 4096000 : ℝ)..(1875373 / 8192000),
      ∫ u in (194217 / 1280000 : ℝ)..(388777 / 2560000),
      ∫ z in (417 / 5000 : ℝ)..(76088109 / 532480000),
      ∫ w in (417 / 5000 : ℝ)..z, 1 / (t * u * z ^ 2 * w) := by
  simp only [firstIntegral, pairedLocalIntegral, pairedFibreKernel_eq]

/-- Complete local certification: concrete check + proved soundness +
the actual integral definition. This does not assert the stored Q160 bounds. -/
theorem firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤ firstIntegral ∧
      firstIntegral ≤ (31704 / 1000000000000 : ℝ) := by
  have hc := firstCertificate.check_sound first_certificate_checked
  norm_num [firstCertificate, tLower, tUpper, uLower, uUpper, firstTIndex,
    firstUIndex, a, h, d, mu, K, firstZ, firstIntegral] at hc ⊢
  exact hc

theorem firstIntegral_pos : 0 < firstIntegral := by
  exact lt_of_lt_of_le (by norm_num) firstIntegral_bounds.1

end ImbalancedChen.Certificates.PairedV2
