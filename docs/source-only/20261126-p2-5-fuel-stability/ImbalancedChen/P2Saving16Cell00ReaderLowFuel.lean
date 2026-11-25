import ImbalancedChen.P2Saving16StringCharBinding00
import ImbalancedChen.P2OriginalSaving19SourceJson

namespace ImbalancedChen.P2Saving16Cell00ReaderLowFuel
open P2OriginalSaving19Archive (SourceJson)
open P2Saving16StringCharBinding00 (chars00)

noncomputable def readerSuccessAtFuel (fuel : Nat) : Bool :=
  match SourceJson.value fuel chars00 with
  | .ok (_, tail) => (SourceJson.white tail).isEmpty
  | .error _ => false

theorem cell00_reader_low_fuel_success :
    readerSuccessAtFuel 371 = true := by
  decide +kernel

#print axioms cell00_reader_low_fuel_success
end ImbalancedChen.P2Saving16Cell00ReaderLowFuel
