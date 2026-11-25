import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Parity

/-! Source-only relocation of the existing Scheduled definition.
Its formula and original namespace are unchanged; no numerical endpoint is imported. -/
namespace ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint
noncomputable section

/-- The trim and resolution, rational strip, common mesh and its
displacement are chosen before the even arithmetic target. -/
def Scheduled (P : ℕ → ℕ → ℚ → ℕ → ℝ → ℕ → Prop) : Prop :=
  ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
  ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
  ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N → P r n e q om N

end
end ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint
