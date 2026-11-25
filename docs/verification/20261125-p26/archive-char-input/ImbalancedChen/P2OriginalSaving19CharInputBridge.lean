import Lean

/-!
Local, data-independent representation lemmas.  No original witness is read,
no JSON is parsed, and no project archive/Core declaration is imported here.

The two front ends below have exactly the shape of SourceJson.parse.  The
reader and whitespace handler remain arbitrary, so the proof neither runs
nor substitutes for the original parser.
-/

namespace ImbalancedChen.P2OriginalSaving19CharInputBridge

universe u v

variable {Error : Type u} {Value : Type v}

def parseString
    (reader : Nat → List Char → Except Error (Value × List Char))
    (white : List Char → List Char) (unconsumed : Error)
    (s : String) : Except Error Value := do
  let (v, tail) ← reader (s.length + 1) s.toList
  if (white tail).isEmpty then return v
  else throw unconsumed

def parseChars
    (reader : Nat → List Char → Except Error (Value × List Char))
    (white : List Char → List Char) (unconsumed : Error)
    (cs : List Char) : Except Error Value := do
  let (v, tail) ← reader (cs.length + 1) cs
  if (white tail).isEmpty then return v
  else throw unconsumed

/-- Changing only the input representation preserves the complete parse result,
including the exact error, payload, fuel, and unconsumed-tail check. -/
theorem parseString_ofList
    (reader : Nat → List Char → Except Error (Value × List Char))
    (white : List Char → List Char) (unconsumed : Error)
    (cs : List Char) :
    parseString reader white unconsumed (String.ofList cs) =
      parseChars reader white unconsumed cs := by
  simp only [parseString, parseChars, String.length_ofList, String.toList_ofList]

/-- This form applies to an existing String declaration, but explicitly requires
the character-binding equality.  A source hash is not such an equality. -/
theorem parseString_eq_parseChars_of_chars_eq
    (reader : Nat → List Char → Except Error (Value × List Char))
    (white : List Char → List Char) (unconsumed : Error)
    (s : String) (cs : List Char) (hchars : cs = s.toList) :
    parseString reader white unconsumed s =
      parseChars reader white unconsumed cs := by
  subst cs
  rfl

/-- The dual binding form is useful when a source encoder provides an ofList
representation.  The binding is still a kernel-checked premise. -/
theorem parseString_eq_parseChars_of_ofList_eq
    (reader : Nat → List Char → Except Error (Value × List Char))
    (white : List Char → List Char) (unconsumed : Error)
    (s : String) (cs : List Char) (htext : String.ofList cs = s) :
    parseString reader white unconsumed s =
      parseChars reader white unconsumed cs := by
  rw [← htext]
  exact parseString_ofList reader white unconsumed cs

/-- A success proof can be transported without comparing the returned Value.
There is deliberately no DecidableEq Value hypothesis. -/
theorem success_of_chars_success
    (reader : Nat → List Char → Except Error (Value × List Char))
    (white : List Char → List Char) (unconsumed : Error)
    (cs : List Char) (v : Value)
    (h : parseChars reader white unconsumed cs = .ok v) :
    parseString reader white unconsumed (String.ofList cs) = .ok v :=
  (parseString_ofList reader white unconsumed cs).trans h

end ImbalancedChen.P2OriginalSaving19CharInputBridge

#print axioms ImbalancedChen.P2OriginalSaving19CharInputBridge.parseString_ofList
#print axioms ImbalancedChen.P2OriginalSaving19CharInputBridge.parseString_eq_parseChars_of_chars_eq
#print axioms ImbalancedChen.P2OriginalSaving19CharInputBridge.parseString_eq_parseChars_of_ofList_eq
#print axioms ImbalancedChen.P2OriginalSaving19CharInputBridge.success_of_chars_success
