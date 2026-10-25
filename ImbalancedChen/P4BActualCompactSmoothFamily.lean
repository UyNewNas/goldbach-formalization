import ImbalancedChen.P4BCompactSmoothMassPrecision
import ImbalancedChen.P4BSmoothRealBCompactFamily
import ImbalancedChen.P4BCompactRealBEulerBudget
import ImbalancedChen.P4BActualSmoothCompleteProductWindow

/-!
# One concrete compact real-b family before the P3 estimate

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

One physical width is selected from the actual compact-b arithmetic mass
theorem, below the roughness and complete-product trim caps. The same width
has a common normalized-log compact support, the genuine complete-product
window, and all finite actual mixed Euler-word budgets with constants fixed
before b and N. This is a concrete family for a spectral supplier to license.
It contains no PP, whole-policy license, density or upper-count assumption.
-/

namespace ImbalancedChen.P4BActualCompactSmoothFamily

noncomputable section
open P4B P4BOuterRampRoughness P4BSmoothProfileCommonCompactSupport
open P4BActualSmoothCompleteProductWindow

structure ActualCompactSmoothFamily
    (b0 b1 kappa kappaZero theta precision widthMax : ℝ) where
  width : ℝ
  width_pos : 0 < width
  width_le : width ≤ widthMax
  rough_gap : 2 * width ≤ baseline b0 kappa - theta
  trim_gap : width ≤ kappaZero - kappa
  threshold : ℕ
  threshold_two : 2 ≤ threshold
  mass_precision : ∀ smallWidth : ℝ, 0 < smallWidth → smallWidth ≤ width →
    ∀ N : ℕ, threshold ≤ N → Even N → ∀ b : ℝ, b0 ≤ b → b ≤ b1 →
      |normalizedSmoothPhysicalMass b kappa smallWidth N - Real.log (1 / b)| < precision
  common_support : ∀ b : ℝ, b0 ≤ b → b ≤ b1 → ∀ N : ℕ, 2 ≤ N →
    tsupport (smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) width) ⊆
      commonCube theta width
  prime_lower_support : ∀ b : ℝ, b0 ≤ b → b ≤ b1 → ∀ N : ℕ, 2 ≤ N →
    ∀ p : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
      smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N) width p ≠ 0 →
        ∀ i : Fin 2, (N : ℝ) ^ theta < p i
  Euler_budget : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, b0 ≤ b → b ≤ b1 →
    ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ p : Fin 2 → ℝ,
      p ∈ positivePrimeOrthant → ∀ word : Fin k → Fin 2,
        |primeEulerWord k word (smoothPrimeVariableProfile b N T width) p| ≤ C
  product_window : ∀ b : ℝ, b0 ≤ b → b ≤ b1 → ∀ N : ℕ, 2 ≤ N →
    ∀ p : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
      smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N) width p ≠ 0 →
        (N : ℝ) ^ (1 - kappaZero) < p 0 * p 1 ∧
          p 0 * p 1 < Real.exp width * (N : ℝ)

/-- All requirements concern one literal family and one fixed positive
width. The all-order constants have no b, N, T, prime-point or word dependence. -/
theorem nonempty_actualCompactSmoothFamily
    {b0 b1 kappa kappaZero theta precision widthMax : ℝ}
    (hb0 : (1 / 2 : ℝ) < b0) (hbBand : b0 ≤ b1) (hb1 : b1 < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hkappaTrim : kappa < kappaZero) (htheta : 0 < theta)
    (hprecision : 0 < precision) (hwidthMax : 0 < widthMax)
    (hgap : theta < baseline b0 kappa) :
    Nonempty (ActualCompactSmoothFamily b0 b1 kappa kappaZero theta precision widthMax) := by
  have hb0pos : 0 < b0 := by linarith only [hb0]
  have hb1nonneg : 0 ≤ b1 := (hb0pos.trans_le hbBand).le
  let effectiveMax : ℝ := min widthMax
    (min ((baseline b0 kappa - theta) / 2) (kappaZero - kappa))
  have heffectiveMax : 0 < effectiveMax := by
    dsimp only [effectiveMax]
    apply lt_min hwidthMax
    exact lt_min (by linarith only [hgap]) (sub_pos.mpr hkappaTrim)
  obtain ⟨width, hwidth, hwidthEffective, N0, hN0, hmass⟩ :=
    exists_compact_uniform_smooth_physical_mass_precision
      hb0 hb1 hkappa hkappaOne precision effectiveMax hprecision heffectiveMax
  have hwidthMaxLe : width ≤ widthMax := hwidthEffective.trans (min_le_left _ _)
  have hwidthHalf : width ≤ (baseline b0 kappa - theta) / 2 :=
    hwidthEffective.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrough : 2 * width ≤ baseline b0 kappa - theta := by
    linarith only [hwidthHalf]
  have htrim : width ≤ kappaZero - kappa :=
    hwidthEffective.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsupport := (realB_family_common_compact_support
    hb0pos hkappaOne.le htheta hrough).2
  refine ⟨{
    width := width
    width_pos := hwidth
    width_le := hwidthMaxLe
    rough_gap := hrough
    trim_gap := htrim
    threshold := N0
    threshold_two := hN0
    mass_precision := hmass
    common_support := ?_
    prime_lower_support := ?_
    Euler_budget := ?_
    product_window := ?_ }⟩
  · intro b hb _hbUpper N hN
    exact hsupport b kappa width hb le_rfl hwidth le_rfl N hN
  · intro b hb _hbUpper N hN p hp hn
    have hbase := baseline_endpoint_le hb0pos hb hkappaOne.le (le_refl kappa)
    have hroughB : 2 * width ≤ baseline b kappa - theta := by
      linarith only [hrough, hbase]
    exact smoothPrimeVariableProfile_nonzero_above_rpow
      (hb0pos.trans_le hb) htheta hN hwidth hroughB hp hn
  · intro k
    obtain ⟨C, hC, hbudget⟩ := exists_compact_realB_prime_EulerWord_budget k hb1nonneg
    refine ⟨C / width ^ k, div_nonneg hC (pow_nonneg hwidth.le k), ?_⟩
    intro b hb hbUpper N hN T p hp word
    exact hbudget b (hb0pos.trans_le hb).le hbUpper width hwidth N hN T p hp word
  · intro b _hb _hbUpper N hN p hp hn
    exact nonzero_smoothPrimeProfile_complete_product_window hN hwidth htrim hp hn

end
end ImbalancedChen.P4BActualCompactSmoothFamily
