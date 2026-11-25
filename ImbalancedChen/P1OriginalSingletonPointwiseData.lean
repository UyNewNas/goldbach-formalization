import Mathlib
import ImbalancedChen.SingletonPrimeProductTransportP5

/-!
Pointwise part of the original singleton weight, separated from its
derivative and licence providers. All eighteen declaration bodies below
are unchanged from the pinned historical sources. Their original names,
cutoffs and full integer domain are preserved.

The source-byte and declaration-byte bindings, and the complementary
provider migration patches, are in
`docs/p1/20261125/p15-singleton-proper-power/POINTWISE_EXTRACTION.json`.
This module makes no derivative, licence or signed-error assertion.
-/

namespace ImbalancedChen.P5Z.ActualEtaPsiOccurrenceBudget
noncomputable section

def eta (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

def chi (s : ℝ) : ℝ := 1 - eta s

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
open ActualEtaPsiOccurrenceBudget

theorem chi_bounds (s : ℝ) : 0 ≤ chi s ∧ chi s ≤ 1 := by
  obtain ⟨h0, h1⟩ := eta_bounds s
  unfold chi
  constructor <;> linarith


theorem chi_one {s : ℝ} (hs : s ≤ 1) : chi s = 1 := by
  simp [chi, eta_zero hs]

theorem chi_zero {s : ℝ} (hs : 2 ≤ s) : chi s = 0 := by
  simp [chi, eta_one hs]


def chiLog (x : ℝ) : ℝ := chi (Real.exp x)

end
end ImbalancedChen.P5Z.ActualSingletonPrimeTestFamily

namespace ImbalancedChen.P5Z.ActualSingletonLogCollarFamily
noncomputable section
open ActualEtaPsiOccurrenceBudget ActualSingletonPrimeTestFamily

def scaledChi (delta x : ℝ) : ℝ := chiLog (x / delta)

def profile (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℝ) : ℝ :=
  if 2 ≤ N then
    if 0 < u 0 then eta (u 0 / (N : ℝ)^beta) *
      scaledChi delta (Real.log (u 0) - Real.log (N : ℝ)) else 0
  else 0

theorem profile_bounds (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℝ) :
    0 ≤ profile beta delta N u ∧ profile beta delta N u ≤ 1 := by
  by_cases hN : 2 ≤ N <;> by_cases hu : 0 < u 0
  · simp only [profile, if_pos hN, if_pos hu, scaledChi, chiLog]
    refine ⟨mul_nonneg (eta_bounds _).1 (chi_bounds _).1, ?_⟩
    exact (mul_le_mul (eta_bounds _).2 (chi_bounds _).2 (chi_bounds _).1 zero_le_one).
      trans_eq (by norm_num)
  all_goals simp [profile, hN, hu]

theorem profile_zero_below (beta delta : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (u : Fin 1 → ℝ) (hu : u 0 ≤ (N : ℝ)^beta) : profile beta delta N u = 0 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
  by_cases hp : 0 < u 0
  · simp only [profile, if_pos hN, if_pos hp]
    rw [eta_zero ((div_le_iff₀ hA).mpr (by simpa using hu)), zero_mul]
  · simp [profile, hN, hp]

def logWidth (B N : ℕ) : ℝ := (Real.log 2 / Real.log ((N : ℝ) + 2))^B

end
end ImbalancedChen.P5Z.ActualSingletonLogCollarFamily

namespace ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
noncomputable section

def smoothNatural (kappa : ℝ) (B N p : ℕ) : ℝ :=
  P5Z.ActualSingletonLogCollarFamily.profile (1-kappa)
    (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N
    (fun _ : Fin 1 => (p : ℝ))

def fullSmoothWeight (kappa : ℝ) (B N : ℕ) : (Fin 1 → Fin (2*N+1)) → ℝ :=
  P5S1SingletonPP.singletonWeight (2*N) (smoothNatural kappa B N)

theorem fullSmoothWeight_eq_actual_profile (kappa : ℝ) (B N : ℕ)
    (u : Fin 1 → Fin (2*N+1)) :
    fullSmoothWeight kappa B N u =
      P5Z.ActualSingletonLogCollarFamily.profile (1-kappa)
        (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N
        (fun i => ((u i).val : ℝ)) := by rfl

theorem smooth_range (kappa : ℝ) (B N p : ℕ) :
    0 ≤ smoothNatural kappa B N p ∧ smoothNatural kappa B N p ≤ 1 :=
  P5Z.ActualSingletonLogCollarFamily.profile_bounds _ _ _ _

end
end ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
