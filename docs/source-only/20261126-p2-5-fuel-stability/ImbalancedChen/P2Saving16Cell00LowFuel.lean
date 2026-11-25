import ImbalancedChen.P2Saving16StringCharBinding00
import ImbalancedChen.P2OriginalSaving16Decoder
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-!
Original cell00 reader and typed decoder at a candidate sufficient fuel.
This is a closed kernel check, not a host-parsed certificate. The eventual
consumer must transport this same successful result to original length+1 fuel
and the already accepted canonical originalText 0 binding.
-/
namespace ImbalancedChen.P2Saving16Cell00LowFuel

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (decodeCell)
open P2Saving16StringCharBinding00 (chars00)

noncomputable def parsedAtFuel (fuel : Nat) := do
  let (v, tail) ← SourceJson.value fuel chars00
  if (SourceJson.white tail).isEmpty then decodeCell v
  else throw "unconsumed original JSON input"

theorem cell00_low_fuel_success :
    (match parsedAtFuel 371 with
     | .ok _ => true
     | .error _ => false) = true := by
  decide +kernel

#print axioms cell00_low_fuel_success

end ImbalancedChen.P2Saving16Cell00LowFuel
