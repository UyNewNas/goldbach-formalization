import ImbalancedChen.P2OriginalSaving16Decoder

/-!
Representation equations for the unchanged original typed decoder.
`String.toList_ofList` removes an encode/decode round trip; every character
test, integer conversion, rational operation, and error branch is retained.
-/

namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open P2OriginalSaving19Archive (SourceJson)

theorem parseInteger_ofList (cs : List Char) :
    parseInteger (String.ofList cs) =
      match SourceJson.intChars cs with
      | some z => .ok z
      | none => .error "invalid original integer" := by
  unfold parseInteger
  rw [String.toList_ofList]
  rfl

theorem parseRational_ofList (cs : List Char) :
    parseRational (String.ofList cs) =
      (do
        let numerator := cs.takeWhile (fun c => c != '/')
        match cs.dropWhile (fun c => c != '/') with
        | [] =>
          let n ← match SourceJson.intChars numerator with
            | some z => .ok z
            | none => .error "invalid original integer"
          return (n : ℚ)
        | '/' :: denominator =>
          let n ← match SourceJson.intChars numerator with
            | some z => .ok z
            | none => .error "invalid original integer"
          let d ← match SourceJson.intChars denominator with
            | some z => .ok z
            | none => .error "invalid original integer"
          if d = 0 then throw "zero original rational denominator"
          return (n : ℚ) / (d : ℚ)
        | _ => throw "invalid original rational") := by
  unfold parseRational
  simp only [String.toList_ofList, parseInteger_ofList]
  cases hs : cs.dropWhile (fun c => c != '/') with
  | nil =>
    cases hn : SourceJson.intChars (cs.takeWhile (fun c => c != '/')) <;>
      rfl
  | cons c denominator =>
    by_cases hc : c = '/'
    · subst c
      simp only
      cases hn : SourceJson.intChars (cs.takeWhile (fun c => c != '/')) <;>
        cases hd : SourceJson.intChars denominator <;>
        rfl
    · simp [hc]

theorem decodeNat_number_ofList (cs : List Char) :
    (SourceJson.Decode.read (.number (String.ofList cs)) : Except String Nat) =
      match SourceJson.natChars cs with
      | some n => .ok n
      | none => .error "expected original natural number" := by
  change (match SourceJson.natChars (String.ofList cs).toList with
    | some n => Except.ok n
    | none => Except.error "expected original natural number") = _
  rw [String.toList_ofList]

end ImbalancedChen.P2OriginalSaving16OriginalArchive
