import ImbalancedChen.P3FourierFrechetIBP
import ImbalancedChen.P3FourierSubsetExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

Finite signed-square simplification of the genuine doubled-coordinate
Fourier multiplier.  Each selected coordinate occurs TWICE, in exactly
the old doubled-list order.  This module pays the algebraic sign, including
empty subsets and zero frequencies.  It does not assert a Fourier decay,
a coordinate-vs-Frechet derivative identification or an arithmetic estimate.
-/

namespace ImbalancedChen.P3FourierSignedSquare
noncomputable section
open scoped Classical BigOperators
open P3FourierSubsetExpansion P3FourierFrechetIBP P3U5ChartMixedL1Budget

/-- The factor from one standard coordinate Fourier derivative in the
physical frequency convention xi = 2*pi*eta. -/
def coordinateWave {d : ℕ} (eta : Fin d → ℝ) (i : Fin d) : ℂ :=
  (((physicalFrequency eta i : ℝ) : ℂ) * Complex.I)

/-- One repeated coordinate contributes a NEGATIVE real square.  The
negative sign is essential and must not be lost on a 2S derivative. -/
theorem coordinateWave_pair {d : ℕ} (eta : Fin d → ℝ) (i : Fin d) :
    coordinateWave eta i * coordinateWave eta i =
      - (((physicalFrequency eta i)^2 : ℝ) : ℂ) := by
  unfold coordinateWave
  calc
    _ = (((physicalFrequency eta i)^2 : ℝ) : ℂ) * Complex.I ^ 2 := by
      push_cast
      ring
    _ = _ := by
      rw [Complex.I_sq]
      ring

/-- Match the genuine (-2*pi*I) Fourier differential phase to the
single real coordinate -eta_i, before any products are taken. -/
theorem coordinateWave_from_real_phase {d : ℕ} (eta : Fin d → ℝ)
    (i : Fin d) :
    (-(2 * (Real.pi : ℂ) * Complex.I)) *
        (((-eta i : ℝ) : ℂ)) = coordinateWave eta i := by
  unfold coordinateWave physicalFrequency
  push_cast
  ring

/-- The two occurrences in every doubled-list cell are multiplied
BEFORE the next cell.  This preserves their exact order and multiplicity. -/
theorem doubled_wave_list {d : ℕ} (xs : List (Fin d))
    (eta : Fin d → ℝ) :
    ((twice xs).map (coordinateWave eta)).prod =
      (xs.map (fun i => - (((physicalFrequency eta i)^2 : ℝ) : ℂ))).prod := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      change
        coordinateWave eta i *
            (coordinateWave eta i * ((twice xs).map (coordinateWave eta)).prod) =
          - (((physicalFrequency eta i)^2 : ℝ) : ℂ) *
            (xs.map (fun k => - (((physicalFrequency eta k)^2 : ℝ) : ℂ))).prod
      rw [← mul_assoc, coordinateWave_pair, ih]

/-- The COMPLETE signed 2S multiplier equals the physical positive
monomial times (-1)^|S|.  No unproved derivative or Fourier-transform
statement is present in the hypotheses. -/
theorem doubled_wave_finset {d : ℕ} (S : Finset (Fin d))
    (eta : Fin d → ℝ) :
    ((doubled S).map (coordinateWave eta)).prod =
      (-1 : ℂ)^S.card * complexMonomial S (physicalFrequency eta) := by
  classical
  calc
    ((doubled S).map (coordinateWave eta)).prod =
        S.prod (fun i => (-1 : ℂ) *
          (((physicalFrequency eta i)^2 : ℝ) : ℂ)) := by
      rw [doubled, doubled_wave_list, Finset.prod_map_toList]
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = (S.prod (fun _ => (-1 : ℂ))) *
          (S.prod (fun i => (((physicalFrequency eta i)^2 : ℝ) : ℂ))) := by
      rw [Finset.prod_mul_distrib]
    _ = (-1 : ℂ)^S.card * complexMonomial S (physicalFrequency eta) := by
      simp [complexMonomial]

/-- The signed-square coefficient in the preceding CoordinateFourierIBP
has exactly one sign per selected coordinate, and no independent 2^|S|
loss.  This is an algebraic identity, not yet the full Fourier IBP. -/
theorem signed_square_is_frequency_monomial {d : ℕ}
    (S : Finset (Fin d)) (eta : Fin d → ℝ) :
    (-1 : ℂ)^S.card * complexMonomial S (physicalFrequency eta) =
      ((doubled S).map (coordinateWave eta)).prod :=
  (doubled_wave_finset S eta).symm

end
end ImbalancedChen.P3FourierSignedSquare
