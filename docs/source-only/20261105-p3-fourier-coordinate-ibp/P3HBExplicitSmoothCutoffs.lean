import ImbalancedChen.P3HBNonnegativeDyadicContraction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
P3.6 manuscript-internal selection of actual C-infinity nonnegative dyadic
cutoffs, using Mathlib's pinned real smoothTransition and real-linear inclusion
into complex numbers. Frozen paper 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (psi and complete-product trim), §4 (F).

The manuscript permits an arbitrary chosen nonnegative dyadic partition and
smooth one-sided trim. This file provides ONE explicit admissible selection
on the entire real axis; it does NOT assert equality with any other cutoff
chosen in a different version or automatically close the true W_T.
SOURCE_ONLY; no Lean/Lake elaboration or kernel verification.
-/

namespace ImbalancedChen.P3HBExplicitSmoothCutoffs
noncomputable section
open ImbalancedChen.P3HBNonnegativeDyadicContraction

/-- Real plateau cutoff, identically one to the left of 1, zero beyond 2. -/
def chosenRealChi (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

/-- Whole-real extension of an allowed trim on [0, infinity): zero up to 1,
one from 2 onward. The transition is itself smooth across zero. -/
def chosenRealEta (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

/-- Literal real-to-complex embedding; no imaginary cutoff is chosen. -/
def chosenChi (t : ℝ) : ℂ := Complex.ofRealCLM (chosenRealChi t)
def chosenEta (t : ℝ) : ℂ := Complex.ofRealCLM (chosenRealEta t)

theorem chosenRealChi_smooth : ContDiff ℝ ⊤ chosenRealChi := by
  have h : ContDiff ℝ ⊤ (fun t : ℝ => (2 : ℝ) - t) := by fun_prop
  exact Real.smoothTransition.contDiff.comp h

theorem chosenRealEta_smooth : ContDiff ℝ ⊤ chosenRealEta := by
  have h : ContDiff ℝ ⊤ (fun t : ℝ => t - (1 : ℝ)) := by fun_prop
  exact Real.smoothTransition.contDiff.comp h

theorem chosenChi_smooth : ContDiff ℝ ⊤ chosenChi := by
  exact Complex.ofRealCLM.contDiff.comp chosenRealChi_smooth

theorem chosenEta_smooth : ContDiff ℝ ⊤ chosenEta := by
  exact Complex.ofRealCLM.contDiff.comp chosenRealEta_smooth

theorem chosenRealChi_left (t : ℝ) (ht : t ≤ 1) : chosenRealChi t = 1 := by
  exact Real.smoothTransition.one_of_one_le (by dsimp [chosenRealChi] at *; linarith)

theorem chosenRealChi_right (t : ℝ) (ht : 2 ≤ t) : chosenRealChi t = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by dsimp [chosenRealChi] at *; linarith)

theorem chosenRealEta_left (t : ℝ) (ht : t ≤ 1) : chosenRealEta t = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by dsimp [chosenRealEta] at *; linarith)

theorem chosenRealEta_right (t : ℝ) (ht : 2 ≤ t) : chosenRealEta t = 1 := by
  exact Real.smoothTransition.one_of_one_le (by dsimp [chosenRealEta] at *; linarith)

/-- This explicit choice is nonincreasing by the exact Mathlib theorem,
not by inserting a new monotonicity premise on an arbitrary chi. -/
theorem chosenRealChi_antitone : Antitone chosenRealChi := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by dsimp [chosenRealChi] at *; linarith)

/-- For t<0 both dyadic arguments lie on the 1-plateau; for t>=0,
2*t>=t and the chosen cutoff is antitone. This proves psi>=0 globally. -/
theorem chosenRealChi_dyadic_nonneg (t : ℝ) :
    0 ≤ chosenRealChi t - chosenRealChi (2 * t) := by
  by_cases ht : 0 ≤ t
  · exact sub_nonneg.mpr (chosenRealChi_antitone (by linarith : t ≤ 2 * t))
  · have ht1 : t ≤ 1 := by linarith
    have ht2 : 2 * t ≤ 1 := by linarith
    rw [chosenRealChi_left t ht1, chosenRealChi_left (2 * t) ht2]
    norm_num

theorem chosenRealChi_dyadic_between (t : ℝ) :
    0 ≤ chosenRealChi t - chosenRealChi (2 * t) ∧
      chosenRealChi t - chosenRealChi (2 * t) ≤ 1 := by
  exact real_dyadic_piece_between_zero_one chosenRealChi
    chosenRealChi_left chosenRealChi_right chosenRealChi_dyadic_nonneg t

theorem chosenChi_real (t : ℝ) : chosenChi t = (chosenRealChi t : ℂ) := by
  exact Complex.ofRealCLM_apply _

theorem chosenEta_real (t : ℝ) : chosenEta t = (chosenRealEta t : ℂ) := by
  exact Complex.ofRealCLM_apply _

theorem chosenChi_left (t : ℝ) (ht : t ≤ 1) : chosenChi t = 1 := by
  rw [chosenChi_real t, chosenRealChi_left t ht]
  norm_num

theorem chosenChi_right (t : ℝ) (ht : 2 ≤ t) : chosenChi t = 0 := by
  rw [chosenChi_real t, chosenRealChi_right t ht]
  norm_num

theorem chosenEta_left (t : ℝ) (ht : t ≤ 1) : chosenEta t = 0 := by
  rw [chosenEta_real t, chosenRealEta_left t ht]
  norm_num

theorem chosenEta_right (t : ℝ) (ht : 2 ≤ t) : chosenEta t = 1 := by
  rw [chosenEta_real t, chosenRealEta_right t ht]
  norm_num

/-- The exact original complex dyadic contraction now has NO cutoff
hypothesis: one concrete C-infinity nonnegative partition is exhibited. -/
theorem chosenChi_dyadic_contraction :
    ∀ t : ℝ, ‖chosenChi t - chosenChi (2 * t)‖ ≤ 1 := by
  exact complex_original_dyadic_contraction chosenRealChi chosenChi
    chosenChi_real chosenRealChi_left chosenRealChi_right
    chosenRealChi_dyadic_nonneg

/-- Concrete smooth geometry bound. All cutoff/trim regularity, two plateau
conditions, real-valued dyadic nonnegativity and contraction are discharged
by the explicit admissible selection; only the ORIGINAL finite K remains.
Original g, repeated axes, group occurrences and physical scales are literal.
This remains a SOURCE_ONLY candidate, NOT a full mixed W_T L1 or PP claim. -/
theorem chosen_group_trim_ordered_polynomial (K : ℕ) :
    ∃ B Ceta : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
          ‖ImbalancedChen.P3HBOriginalGroupCoordinateMixed.originalOrderedAxisDeriv
                (List.ofFn axes)
              (ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst.originalGroupPhysicalTrim
                chosenChi chosenEta c J s) u‖ ≤
            (2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta := by
  exact original_group_trim_polynomial_of_nonnegative_dyadic
    chosenRealChi chosenChi chosenEta chosenChi_real
    chosenRealChi_left chosenRealChi_right chosenRealChi_dyadic_nonneg
    chosenChi_smooth chosenEta_smooth chosenEta_left chosenEta_right K

end
end ImbalancedChen.P3HBExplicitSmoothCutoffs
