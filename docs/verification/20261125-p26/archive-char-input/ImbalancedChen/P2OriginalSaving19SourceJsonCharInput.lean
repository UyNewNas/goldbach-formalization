import ImbalancedChen.P2OriginalSaving19SourceJson
import ImbalancedChen.P2OriginalSaving19CharInputBridge

/-!
Candidate companion only: the imported original SourceJson parser is unchanged.
All JSON recognition, fuel, whitespace, integer tokens, and error paths are the
same functions as the original reader.  Only the front-end representation is
changed.  This module neither reads a file nor certifies a concrete witness.
-/

namespace ImbalancedChen.P2OriginalSaving19Archive.SourceJson

def parseChars (cs : List Char) : Except String SourceJson :=
  ImbalancedChen.P2OriginalSaving19CharInputBridge.parseChars
    value white "unconsumed original JSON input" cs

theorem parse_ofList (cs : List Char) :
    parse (String.ofList cs) = parseChars cs :=
  ImbalancedChen.P2OriginalSaving19CharInputBridge.parseString_ofList
    value white "unconsumed original JSON input" cs

theorem parseChars_eq_parse_ofList (cs : List Char) :
    parseChars cs = parse (String.ofList cs) :=
  (parse_ofList cs).symm

theorem parse_eq_parseChars_of_chars_eq (s : String) (cs : List Char)
    (hchars : cs = s.toList) :
    parse s = parseChars cs :=
  ImbalancedChen.P2OriginalSaving19CharInputBridge.parseString_eq_parseChars_of_chars_eq
    value white "unconsumed original JSON input" s cs hchars

theorem parse_eq_parseChars_of_ofList_eq (s : String) (cs : List Char)
    (htext : String.ofList cs = s) :
    parse s = parseChars cs :=
  ImbalancedChen.P2OriginalSaving19CharInputBridge.parseString_eq_parseChars_of_ofList_eq
    value white "unconsumed original JSON input" s cs htext

/-- This changes only the input representation, including after any unchanged
typed decoder.  It does not assert that decoding succeeds. -/
theorem parse_bind_eq_parseChars_bind_of_ofList_eq {α : Type}
    (decode : SourceJson → Except String α)
    (s : String) (cs : List Char) (htext : String.ofList cs = s) :
    (parse s >>= decode) = (parseChars cs >>= decode) := by
  rw [parse_eq_parseChars_of_ofList_eq s cs htext]

end ImbalancedChen.P2OriginalSaving19Archive.SourceJson
