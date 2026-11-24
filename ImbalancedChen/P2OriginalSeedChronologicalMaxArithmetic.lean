import ImbalancedChen.P2OriginalSavingLowerLedger
import Mathlib.Tactic

/-!
The selected Winner9 totals for the log, curvature, and mixed stages on
the same physical seed. Each ledger increment is the change from the
preceding adopted value. The row-by-row enclosure and the physical
source comparison enter through separate theorems.
-/

namespace ImbalancedChen.P2OriginalSeedChronologicalMaxArithmetic

open scoped BigOperators
open P2OriginalCertificateBudget

/-- The already adopted factorwise logarithmic seed total at Q96. -/
def adoptedLogTotal : ℚ :=
  475182339168330434688559 / 79228162514264337593543950336

/-- The independently checked plain P10 maximum is not separately adopted. -/
def plainP10Maximum : ℚ :=
  237592771576150817599263 / 39614081257132168796771975168

/-- The unmaximized curvature total; its comparison shows why the
per-simplex maximum, rather than the raw total, is essential. -/
def curvatureRawTotal : ℚ :=
  474139291291580412934007 / 79228162514264337593543950336

/-- First chronological replacement: sum of per-simplex maxima of the
old log floor and the curvature floor. -/
def curvatureSelectedTotal : ℚ :=
  237629874802202295777015 / 39614081257132168796771975168

/-- Second chronological replacement: sum of per-simplex maxima of the
already adopted curvature value and the mixed degree-six floor. -/
def mixedSelectedTotal : ℚ :=
  475741072397709744401965 / 79228162514264337593543950336

def curvatureIncrement : ℚ := curvatureSelectedTotal - adoptedLogTotal

def mixedIncrement : ℚ := mixedSelectedTotal - curvatureSelectedTotal

/-- Literal selected upper ledger slots, zero-based positions 20 and 21. -/
def slot21 : Fin 22 := ⟨20, by decide⟩
def slot22 : Fin 22 := ⟨21, by decide⟩

theorem curvature_increment_exact :
    curvatureIncrement = savingLower slot21 := by
  norm_num [curvatureIncrement, curvatureSelectedTotal, adoptedLogTotal,
    savingLower, slot21]

theorem mixed_increment_exact :
    mixedIncrement = savingLower slot22 := by
  norm_num [mixedIncrement, mixedSelectedTotal, curvatureSelectedTotal,
    savingLower, slot22]

theorem curvature_increment_pos : 0 < curvatureIncrement := by
  norm_num [curvatureIncrement, curvatureSelectedTotal, adoptedLogTotal]

theorem mixed_increment_pos : 0 < mixedIncrement := by
  norm_num [mixedIncrement, mixedSelectedTotal, curvatureSelectedTotal]

/-- The raw curvature sum alone would not replace the adopted log total. -/
theorem curvature_raw_below_adopted_log :
    curvatureRawTotal < adoptedLogTotal := by
  norm_num [curvatureRawTotal, adoptedLogTotal]

/-- The old plain P10 maximum is already dominated by the first adopted
replacement; adding its gain again would double count the same seed. -/
theorem plain_max_below_curvature_selected :
    plainP10Maximum ≤ curvatureSelectedTotal := by
  norm_num [plainP10Maximum, curvatureSelectedTotal]

/-- Exact chronology: first replace the log floor by curvature, then
replace that current value by mixed. The old seed is subtracted once. -/
theorem seed_chronological_telescope :
    mixedSelectedTotal - adoptedLogTotal =
      savingLower slot21 + savingLower slot22 := by
  calc
    mixedSelectedTotal - adoptedLogTotal =
        (curvatureSelectedTotal - adoptedLogTotal) +
          (mixedSelectedTotal - curvatureSelectedTotal) := by ring
    _ = savingLower slot21 + savingLower slot22 := by
      change curvatureIncrement + mixedIncrement =
        savingLower slot21 + savingLower slot22
      rw [curvature_increment_exact, mixed_increment_exact]

/-- Replacing the two increments by the final mixed maximum changes
no domain and creates no extra P10 or raw-curvature ledger term. -/
theorem seed_final_upper_subtraction (outsideSeed : ℚ) :
    outsideSeed - savingLower slot21 - savingLower slot22 =
      outsideSeed - (mixedSelectedTotal - adoptedLogTotal) := by
  rw [seed_chronological_telescope]
  ring

/-- The six original eighth-stage savings and the two later seed replacements. -/
theorem eighth_stage_ledger_sum :
    (∑ i : Fin 8, savingLower ⟨14 + i.val, by omega⟩) =
      (3111307568597708509491143 + 77410436074156865471 + 481322793305152847935 : ℚ) /
        79228162514264337593543950336 := by
  decide +kernel

end ImbalancedChen.P2OriginalSeedChronologicalMaxArithmetic
