import ImbalancedChen.P5OriginalFourthFifthSourceInputs
import ImbalancedChen.P4AOriginalCommonArchiveSchedule

/-! Source-only relocation of the existing actual archive schedule/data.
The fixed schedule, original byte bank and admission filter are unchanged. -/
namespace ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalFourthFifthSourceInputs
open P4AOriginalCausalHistory P4AOriginalCommonArchiveSchedule

/-- The same pre-N archive schedule with the actual fourth bank. -/
def schedule (e : ℚ) (q : ℕ) (omega : ℝ) : ArchiveSchedule :=
  fixedSchedule originalRows4 originalAdmission4 e q omega

def data (e : ℚ) (q : ℕ) (omega : ℝ) : OriginalData :=
  (schedule e q omega).data

end
end ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
