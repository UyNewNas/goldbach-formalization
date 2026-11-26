import ImbalancedChen.P5ActualLowerNormalizedAtlasOccurrence

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The existing actual singleton support theorem, with its original namespace,
statement and proof bytes. The registered provider postimage must be selected atomically with this
shared owner; the old defining provider cannot
be imported alongside it. This owner has no historical P2/FixedM import.
-/

namespace ImbalancedChen.P1OriginalSingletonPhysicalLevel
noncomputable section
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_zero)
open P5Z.ActualLowerNormalizedAtlasOccurrence
  (scalarProfile scalarProfile_eq_ambient scalarProfile_support)

/-- Read both complete-integer support bounds from the actual scalar profile.
No geometric trim or upper-support estimate is an input. -/
theorem scalarProfile_complete_support (kap : ℝ) (hkap : kap < 1)
    (B N cj : ℕ) (kap0 : ℝ) {n : ℕ} (hN : 0 < N)
    (hactive : scalarProfile kap B N cj kap0 n ≠ 0) :
    (N : ℝ) ^ (1 - kap0) < (n : ℝ) ∧ (n : ℝ) ≤ 2 * (N : ℝ) := by
  have hcap := scalarProfile_support kap hkap B N cj kap0 hactive
  rw [scalarProfile_eq_ambient] at hactive
  have heta : eta ((n : ℝ) / (N : ℝ) ^ (1 - kap0)) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hactive).1).2
  have hden := Real.rpow_pos_of_pos
    (show (0 : ℝ) < N by exact_mod_cast hN) (1 - kap0)
  refine ⟨?_, by exact_mod_cast hcap⟩
  by_contra! bad
  exact heta (eta_zero ((div_le_one hden).mpr bad))

end
end ImbalancedChen.P1OriginalSingletonPhysicalLevel
