import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-! Algebraic elimination of the unchanged original parser front end.
All arguments are arbitrary. Concrete value success and empty remaining white
input must both be supplied by separately checked theorems. -/
namespace ImbalancedChen.P2OriginalSaving19Archive.SourceJson

theorem parseChars_of_value_eq {cs : List Char} {parsed : SourceJson} {tail : List Char}
    (hvalue : value (cs.length + 1) cs = .ok (parsed, tail))
    (htail : white tail = []) :
    parseChars cs = .ok parsed := by
  unfold parseChars ImbalancedChen.P2OriginalSaving19CharInputBridge.parseChars
  rw [hvalue]
  change (if (white tail).isEmpty then Except.ok parsed
    else Except.error "unconsumed original JSON input") = Except.ok parsed
  rw [htail]
  rfl

#print axioms parseChars_of_value_eq

end ImbalancedChen.P2OriginalSaving19Archive.SourceJson
