import ImbalancedChen.P5OriginalFourthFifthSourceInputs
import ImbalancedChen.P4AOriginalCommonArchiveScheduleData

/-!
The unchanged original fourth/fifth archive data used by the common
history and complete-sixth chronology. These declarations keep their
original public namespace and bodies; the fourteen-family numerical
endpoint remains in its original consumer module.

SOURCE CANDIDATE / NOT COMPILED.
-/
namespace ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
noncomputable section
open P5OriginalCommonRefinedConstructor
open P5OriginalFourthFifthSourceInputs
open P4AOriginalCausalHistory P4AOriginalCommonArchiveSchedule
open P5OriginalCommonFourthFallbackExcision P5OriginalCommonFourthSourceNavigation

/-- The same pre-N archive schedule with the actual fourth bank. -/
def schedule (e : ℚ) (q : ℕ) (omega : ℝ) : ArchiveSchedule :=
  fixedSchedule originalRows4 originalAdmission4 e q omega

def data (e : ℚ) (q : ℕ) (omega : ℝ) : OriginalData :=
  (schedule e q omega).data

theorem data_eq_original_heldData (e : ℚ) (q : ℕ) (omega : ℝ) :
    data e q omega = heldData e q ((e : ℝ) / 20) omega := rfl

/-- Geometry follows from the actual admission test. -/
theorem actual_fourth_geometry (e : ℚ) (q : ℕ) (omega : ℝ) :
    FourthGeometry (data e q omega) := by
  intro r _hr hlicense
  exact originalAdmission4_geometry r hlicense

end
end ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
