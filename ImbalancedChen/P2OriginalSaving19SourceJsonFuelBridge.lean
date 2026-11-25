import ImbalancedChen.P2OriginalSaving19SourceJsonFuel

/-!
Transport a checked character-list parse through an exact `String.ofList`
equality to the unchanged original string parser. These generic bridges
assert no concrete parse success and introduce no alternate parser.
-/

namespace ImbalancedChen.P2OriginalSaving19Archive.SourceJson

/-- A successful value parse of an exact character representation yields
success of the original string parser at its original length-based fuel. -/
theorem parse_of_value_of_ofList_eq
    (s : String) (cs : List Char) (fuel : Nat) (v : SourceJson) (tail : List Char)
    (htext : String.ofList cs = s) (hle : fuel ≤ cs.length + 1)
    (hvalue : value fuel cs = .ok (v, tail))
    (htail : (white tail).isEmpty = true) : parse s = .ok v := by
  subst s
  apply parse_success_of_value (String.ofList cs) fuel v tail
  · simpa only [String.length_ofList] using hle
  · simpa only [String.toList_ofList] using hvalue
  · exact htail

/-- The original parse followed by any decoder equals the decoder applied
to the checked value, retaining the exact original text binding. -/
theorem parse_bind_of_value_of_ofList_eq {α : Type}
    (decode : SourceJson → Except String α)
    (s : String) (cs : List Char) (fuel : Nat) (v : SourceJson) (tail : List Char)
    (htext : String.ofList cs = s) (hle : fuel ≤ cs.length + 1)
    (hvalue : value fuel cs = .ok (v, tail))
    (htail : (white tail).isEmpty = true) : (parse s >>= decode) = decode v := by
  rw [parse_of_value_of_ofList_eq s cs fuel v tail htext hle hvalue htail]
  rfl

/-- A separately checked decoded result transports to the original parser
and decoder without recomputing their combined expression. -/
theorem parse_bind_ok_of_value_of_ofList_eq {α : Type}
    (decode : SourceJson → Except String α)
    (s : String) (cs : List Char) (fuel : Nat) (v : SourceJson) (tail : List Char)
    (htext : String.ofList cs = s) (hle : fuel ≤ cs.length + 1)
    (hvalue : value fuel cs = .ok (v, tail))
    (htail : (white tail).isEmpty = true)
    (decoded : α) (hdecode : decode v = .ok decoded) :
    (parse s >>= decode) = .ok decoded := by
  rw [parse_bind_of_value_of_ofList_eq decode s cs fuel v tail htext hle hvalue htail]
  exact hdecode

/-- A separately checked decoder success guard transports to the same guard
on the original parse-and-decode expression. -/
theorem parse_bind_success_of_value_of_ofList_eq {α : Type}
    (decode : SourceJson → Except String α)
    (s : String) (cs : List Char) (fuel : Nat) (v : SourceJson) (tail : List Char)
    (htext : String.ofList cs = s) (hle : fuel ≤ cs.length + 1)
    (hvalue : value fuel cs = .ok (v, tail))
    (htail : (white tail).isEmpty = true)
    (hdecode : (match decode v with | .ok _ => true | .error _ => false) = true) :
    (match parse s >>= decode with | .ok _ => true | .error _ => false) = true := by
  rw [parse_bind_of_value_of_ofList_eq decode s cs fuel v tail htext hle hvalue htail]
  exact hdecode

end ImbalancedChen.P2OriginalSaving19Archive.SourceJson
