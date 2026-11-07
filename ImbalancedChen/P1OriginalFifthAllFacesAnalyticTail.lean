import ImbalancedChen.P1OriginalCoarseFifthCellLimit
import ImbalancedChen.P1OriginalFifthLowerKernelTail

/-!
SOURCE_ONLY / UNCOMPILED.

An analytic bound for the original T3 fifth cell at every small-coordinate
face.  Strict ordering makes the fifth coordinate no larger than whichever
coordinate is small.  The actual canonical lower-source decay then pays the
fourth logarithmic face.  This is a continuous integral estimate; no finite
prime remainder or distribution estimate is assumed or asserted.
-/

namespace ImbalancedChen.P1OriginalFifthAllFacesAnalyticTail

noncomputable section

open Filter Topology Set
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalFifthLowerKernelTail

/-- On the original strict descending tuple, every small-coordinate face
is contained in the last-coordinate face. -/
theorem last_lt_of_any_coordinate_lt (t : Fin 5 → ℝ)
    (hanti : StrictAnti t) {a : ℝ}
    (hsmall : ∃ i, t i < a) : t 4 < a := by
  obtain ⟨i, hi⟩ := hsmall
  fin_cases i
  · exact (hanti (by decide : (0 : Fin 5) < 4)).trans hi
  · exact (hanti (by decide : (1 : Fin 5) < 4)).trans hi
  · exact (hanti (by decide : (2 : Fin 5) < 4)).trans hi
  · exact (hanti (by decide : (3 : Fin 5) < 4)).trans hi
  · exact hi

/-- The fixed inherited-level comparison is a finite cap condition, not
an integral bound.  The h45 check supplies the new-level comparison. -/
theorem original_cell_kernel_bound_all_faces
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (homega : 0 < omega) (ha : a ≤ omega / 6)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (h34j : HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (thirdOwner j)) ≤
        (old5 e chi m omega J4 cap4 j : ℝ))
    (t : Fin 5 → ℝ) (ht : t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j)
    (hpos : ∀ i, 0 < t i) (hsmall : ∃ i, t i < a) :
    0 ≤ kernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t ∧
      kernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t ≤
        12 / (t 0 * t 1 * t 2 * t 3 * (omega / 2) ^ 2) := by
  have hg := (mem_jointRegion (e : ℝ) chi m omega j t).mp ht.2
  have hactive := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
    e chi m omega J5 j hj ht.1
  have hcurrent := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 j hj ht.1
  have hcube : t 0 + t 1 + 3 * t 2 <
      HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) := by
    simpa only [hcurrent] using hg.2.2.2.2
  have hlevel : (old5 e chi m omega J4 cap4 j : ℝ) ≤ cap5 j := by
    exact_mod_cast h45Check_sound e chi m omega J4 cap4 J5 cap5 h45 j hj
  have hlast : t 4 ≤ omega / 6 :=
    (last_lt_of_any_coordinate_lt t hg.2.1 hsmall).le.trans ha
  exact kernel_bound_of_original_third_cube t homega hpos hactive hcube
    (hg.2.1 (by decide : (2 : Fin 5) < 3)) h34j hlevel hlast

/-- Explicit continuous mass envelope on the original selected fifth cell.
The `a * (log(rho/a)+1)` factor pays the fourth logarithmic boundary face. -/
theorem original_cell_continuous_tail_le
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (homega : 0 < omega) (horho : omega ≤ (19 / 96 : ℝ))
    (ha : 0 < a) (hasmall : a ≤ omega / 6)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (h34j : HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (thirdOwner j)) ≤
        (old5 e chi m omega J4 cap4 j : ℝ)) :
    tailMass (P1OriginalFifthLimit.sourceRegion e chi m omega j)
      (fun _ => (old5 e chi m omega J4 cap4 j : ℝ))
      (fun _ => (cap5 j : ℝ)) omega (19 / 96) a ≤
        ENNReal.ofReal ((12 / (omega / 2) ^ 2) *
          Real.log ((19 / 96 : ℝ) / omega) ^ 3 * logPrimitive (19 / 96) a) := by
  apply tailMass_le (u := omega / 2) (by positivity) homega horho ha
    (by linarith) (by linarith)
  intro t ht hanti _hpos hactive _hrho hlast
  have hg := (mem_jointRegion (e : ℝ) chi m omega j t).mp ht.2
  have hcurrent := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 j hj ht.1
  have hcube : t 0 + t 1 + 3 * t 2 <
      HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) := by
    simpa only [hcurrent] using hg.2.2.2.2
  have hgap := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega (HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (thirdOwner j)))
    (old5 e chi m omega J4 cap4 j : ℝ) t hactive hcube
    (hanti (by decide : (2 : Fin 5) < 3)) h34j).2
  have hlevel : (old5 e chi m omega J4 cap4 j : ℝ) ≤ cap5 j := by
    exact_mod_cast h45Check_sound e chi m omega J4 cap4 J5 cap5 h45 j hj
  exact ⟨hlevel, by linarith⟩

/-- The original cell is integrated with its true third-capped parent.
The existing canonical-source tail theorem gives the bound at the fifth
face while retaining the fourth-coordinate logarithmic singularity. -/
theorem original_cell_continuous_tail_tendsto_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (horho : omega ≤ (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (h34j : HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (thirdOwner j)) ≤
        (old5 e chi m omega J4 cap4 j : ℝ)) :
    Tendsto (fun a : ℝ =>
      (tailMass (P1OriginalFifthLimit.sourceRegion e chi m omega j)
        (fun _ => (old5 e chi m omega J4 cap4 j : ℝ))
        (fun _ => (cap5 j : ℝ)) omega (19 / 96) a).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  apply tail_toReal_tendsto_zero_of_original_third_cube homega horho
    (fun _ => P1OriginalFifthLimit.sourceRegion e chi m omega j)
    (fun _ _ => HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (thirdOwner j)))
    (fun _ _ => (old5 e chi m omega J4 cap4 j : ℝ))
    (fun _ _ => (cap5 j : ℝ))
  intro a _ha _hsmall t ht _hanti _hpos _hactive _hrho _hlast
  have hg := (mem_jointRegion (e : ℝ) chi m omega j t).mp ht.2
  have hcurrent := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 j hj ht.1
  have hcube : t 0 + t 1 + 3 * t 2 <
      HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) := by
    simpa only [hcurrent] using hg.2.2.2.2
  have hlevel : (old5 e chi m omega J4 cap4 j : ℝ) ≤ cap5 j := by
    exact_mod_cast h45Check_sound e chi m omega J4 cap4 J5 cap5 h45 j hj
  exact ⟨hcube, h34j, hlevel⟩

/-- Finite selected-cell aggregation of the continuous original tail.
This sum is deliberately not identified with the arithmetic remainder. -/
theorem selected_continuous_tails_tendsto_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (horho : omega ≤ (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (h34 : ∀ j ∈ selectedFifthCells e chi m omega J5,
      HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) ≤
          (old5 e chi m omega J4 cap4 j : ℝ)) :
    Tendsto (fun a : ℝ =>
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        (tailMass (P1OriginalFifthLimit.sourceRegion e chi m omega j)
          (fun _ => (old5 e chi m omega J4 cap4 j : ℝ))
          (fun _ => (cap5 j : ℝ)) omega (19 / 96) a).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_finsetSum (selectedFifthCells e chi m omega J5)
    (fun j hj => original_cell_continuous_tail_tendsto_zero
      e chi m omega homega horho J4 cap4 J5 cap5 h45 j hj (h34 j hj))

end

end ImbalancedChen.P1OriginalFifthAllFacesAnalyticTail
