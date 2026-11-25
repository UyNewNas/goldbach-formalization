import Mathlib

/-! Source-only exact declaration extraction for the actual U5 count consumer.
No elaboration or kernel acceptance is claimed. -/
namespace ImbalancedChen.P5Z.ActualEtaPsiOccurrenceBudget
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators

def eta (s : ℝ) : ℝ := Real.smoothTransition (s - 1)


def chi (s : ℝ) : ℝ := 1 - eta s


theorem eta_smooth : ContDiff ℝ ∞ eta :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)


theorem eta_bounds (s : ℝ) : 0 ≤ eta s ∧ eta s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩


theorem eta_zero {s : ℝ} (hs : s ≤ 1) : eta s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)


theorem eta_one {s : ℝ} (hs : 2 ≤ s) : eta s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)


end
end ImbalancedChen.P5Z.ActualEtaPsiOccurrenceBudget

namespace ImbalancedChen.P5Z.ActualSingletonPrimeTestFamily
noncomputable section
open Classical Set Filter Topology
open ActualEtaPsiOccurrenceBudget
open scoped BigOperators

theorem chi_smooth : ContDiff ℝ ∞ chi := contDiff_const.sub eta_smooth



theorem chi_bounds (s : ℝ) : 0 ≤ chi s ∧ chi s ≤ 1 := by
  obtain ⟨h0, h1⟩ := eta_bounds s
  unfold chi
  constructor <;> linarith



theorem chi_one {s : ℝ} (hs : s ≤ 1) : chi s = 1 := by
  simp [chi, eta_zero hs]


theorem chi_zero {s : ℝ} (hs : 2 ≤ s) : chi s = 0 := by
  simp [chi, eta_one hs]



def chiLog (x : ℝ) : ℝ := chi (Real.exp x)


theorem chiLog_smooth : ContDiff ℝ ∞ chiLog := chi_smooth.comp Real.contDiff_exp



end
end ImbalancedChen.P5Z.ActualSingletonPrimeTestFamily

