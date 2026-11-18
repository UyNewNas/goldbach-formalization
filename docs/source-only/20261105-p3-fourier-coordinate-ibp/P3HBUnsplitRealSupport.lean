import ImbalancedChen.P3HBUnsplitRealSliceSmooth
import Mathlib.Tactic

/-!
P3.6, fixed manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 original smooth dyadic geometry and §4 (F).

This proves a genuine positional SUPPORT property of the chosen real
six-slot HB profile. No formal support field is postulated: the only
input is the ACTUAL Real.exp positional factor and the pinned chosenChi
plateaux 1 for t<=1 and 0 for t>=2.

Each original positional dyadic factor vanishes outside exp(u_i) in
(1/2, 2). The complete occurrence-indexed group product and unique
physical full-product trim therefore also vanish there, for EVERY
group incidence and scale. This is an actual compact-box localization
input for a future integrability proof; it does NOT itself prove
HasCompactSupport, derivative-integrability, Fourier decay or PP.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitRealSupport
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.P3HBExplicitSmoothCutoffs
open ImbalancedChen.P3HBUnsplitRealProfile

/-- The exact lower dyadic plateau. In particular exp(u_i) ≤ 1/2
forces BOTH chosen original positional cutoffs to equal one. -/
theorem realSlotFactor_zero_of_small
    (u : Fin 6 → ℝ) (i : Fin 6)
    (hsmall : (2 : ℝ) * Real.exp (u i) ≤ 1) :
    realSlotFactor i u = 0 := by
  have hfirst : Real.exp (u i) ≤ 1 := by
    have hp := Real.exp_pos (u i)
    linarith
  change chosenRealChi (Real.exp (u i)) -
    chosenRealChi (2 * Real.exp (u i)) = 0
  rw [chosenRealChi_left _ hfirst, chosenRealChi_left _ hsmall]
  ring

/-- The exact upper dyadic plateau. In particular exp(u_i) ≥ 2
forces BOTH chosen original positional cutoffs to equal zero. -/
theorem realSlotFactor_zero_of_large
    (u : Fin 6 → ℝ) (i : Fin 6)
    (hlarge : (2 : ℝ) ≤ Real.exp (u i)) :
    realSlotFactor i u = 0 := by
  have hsecond : (2 : ℝ) ≤ 2 * Real.exp (u i) := by
    linarith [Real.exp_pos (u i)]
  change chosenRealChi (Real.exp (u i)) -
    chosenRealChi (2 * Real.exp (u i)) = 0
  rw [chosenRealChi_right _ hlarge, chosenRealChi_right _ hsecond]
  ring

/-- A single vanishing ORIGINAL position zeroes the genuine product;
the arbitrary repeated group occurrences and unique trim are not
altered or absorbed into a surrogate profile. -/
theorem realSixUnsplitWeight_zero_of_slot {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) (i : Fin 6)
    (hslot : realSlotFactor i u = 0) :
    realSixUnsplitWeight c J s u = 0 := by
  have hp : (∏ j : Fin 6, realSlotFactor j u) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hslot
  simp only [realSixUnsplitWeight, hp, mul_zero]

theorem realSixUnsplitWeight_zero_of_small {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) (i : Fin 6)
    (hsmall : (2 : ℝ) * Real.exp (u i) ≤ 1) :
    realSixUnsplitWeight c J s u = 0 := by
  exact realSixUnsplitWeight_zero_of_slot c J s u i
    (realSlotFactor_zero_of_small u i hsmall)

theorem realSixUnsplitWeight_zero_of_large {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) (i : Fin 6)
    (hlarge : (2 : ℝ) ≤ Real.exp (u i)) :
    realSixUnsplitWeight c J s u = 0 := by
  exact realSixUnsplitWeight_zero_of_slot c J s u i
    (realSlotFactor_zero_of_large u i hlarge)

/-- A nonzero actual original source must lie strictly inside the
same fixed six-dimensional dyadic positional window for every i.
Strict endpoints are paid by the plateau identities, not discarded. -/
theorem realSixUnsplitWeight_nonzero_axis_bounds {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ)
    (hnonzero : realSixUnsplitWeight c J s u ≠ 0)
    (i : Fin 6) :
    1 < (2 : ℝ) * Real.exp (u i) ∧
      Real.exp (u i) < 2 := by
  constructor
  · by_contra hnot
    exact hnonzero (realSixUnsplitWeight_zero_of_small
      c J s u i (le_of_not_gt hnot))
  · by_contra hnot
    exact hnonzero (realSixUnsplitWeight_zero_of_large
      c J s u i (le_of_not_gt hnot))

/-- Purely geometric fixed window, independent of group count, original
group incidences, positive scales and the complete-product trim. -/
def sixDyadicPositionalWindow : Set (Fin 6 → ℝ) :=
  {u | ∀ i : Fin 6,
    1 < (2 : ℝ) * Real.exp (u i) ∧ Real.exp (u i) < 2}

/-- Literal function support, not a guessed support field.
Further work must pass from this bounded positional window to the
actual HasCompactSupport and integrable iterated Frechet derivatives. -/
theorem realSixUnsplitWeight_support_subset {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) :
    Function.support (realSixUnsplitWeight c J s) ⊆
      sixDyadicPositionalWindow := by
  intro u hu
  exact realSixUnsplitWeight_nonzero_axis_bounds c J s u hu

end
end ImbalancedChen.P3HBUnsplitRealSupport
