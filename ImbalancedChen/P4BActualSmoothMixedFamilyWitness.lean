import ImbalancedChen.P4BActualSmoothFamilyWitness
import ImbalancedChen.P4BSmoothProfileMixedFrechetBudget

/-!
# The mass-selected actual family with full mixed prime-chart control

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

This adds a new witness and new public construction without changing the
existing family record. Its same selected width now carries the full mixed
tensor bound on genuine positive-prime multiplicative charts. It supplies
neither an actualwinner geometric license nor the signed P3 A = 3 estimate.
The separate syntactic Euler-operator-word dictionary is not asserted here.
-/

namespace ImbalancedChen.P4BActualSmoothMixedFamilyWitness

noncomputable section
open P4B P4BOuterRampRoughness P4BActualSmoothFamilyWitness

/-- A new mixed witness extends the already constructed actual family.
The positive mass-selected physical width is shared by every field. -/
structure ActualSmoothMixedFamilyWitness
    (b kappa theta eta widthMax : ℝ) extends
    ActualSmoothFamilyWitness b kappa theta eta widthMax where
  mixed_prime_chart_budget : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ p : Fin 2 → ℝ,
      p ∈ positivePrimeOrthant → ∀ z : Fin 2 → ℝ,
        ‖iteratedFDeriv ℝ k
          (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) z‖ ≤
          C / width ^ k

/-- Full mixed control is derived for the existing family's chosen width,
with every constant chosen before N, the cutoff and the prime variables. -/
theorem nonempty_actualSmoothMixedFamilyWitness
    {b kappa theta eta widthMax : ℝ}
    (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (htheta : 0 < theta) (heta : 0 < eta) (hwidthMax : 0 < widthMax)
    (hgap : theta < baseline b kappa) :
    Nonempty (ActualSmoothMixedFamilyWitness b kappa theta eta widthMax) := by
  obtain ⟨F⟩ := nonempty_actualSmoothFamilyWitness
    hbLower hbUpper hkappa hkappaOne htheta heta hwidthMax hgap
  refine ⟨{
    toActualSmoothFamilyWitness := F
    mixed_prime_chart_budget := ?_ }⟩
  intro k
  obtain ⟨C, hC, hbudget⟩ :=
    exists_smoothPrimeVariableProfile_mixed_chart_budget k b
  exact ⟨C, hC, fun N hN T p hp z => hbudget F.width F.width_pos N hN T p hp z⟩

end
end ImbalancedChen.P4BActualSmoothMixedFamilyWitness
