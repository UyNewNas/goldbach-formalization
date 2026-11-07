import ImbalancedChen.CurrentChenOrdinaryInitialMean
import ImbalancedChen.CurrentChenMeanLedger

/-!
# The first two literal current Chen rows receive their ordinary means

The source is the actual additive-prime carrier and both actual current
power cutoffs are retained. The full ordinary BV-level mean is supplied
without a density or distribution hypothesis. These are baseline means;
the paired causal improvement and the complete Chen hLower remain open.
-/

namespace ImbalancedChen

open Filter

theorem eventually_currentChenUpsilon1_ge_ordinary_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentChenOrdinaryInitialConstant (417 / 5000) - epsilon) *
          singularNormalization N ≤ currentChenUpsilon1 N := by
  filter_upwards [eventually_currentChen_sifted_ge_ordinary_initial_mean
    (417 / 5000) (by norm_num) (by norm_num) epsilon hepsilon] with N h
  intro hEven
  rw [currentChenUpsilon1_eq_actual_sifted_card N hEven]
  exact h hEven

theorem eventually_currentChenUpsilon2_ge_ordinary_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentChenOrdinaryInitialConstant (19 / 125) - epsilon) *
          singularNormalization N ≤ currentChenUpsilon2 N := by
  filter_upwards [eventually_currentChen_sifted_ge_ordinary_initial_mean
    (19 / 125) (by norm_num) (by norm_num) epsilon hepsilon] with N h
  intro hEven
  rw [currentChenUpsilon2_eq_actual_sifted_card N hEven]
  exact h hEven

end ImbalancedChen
