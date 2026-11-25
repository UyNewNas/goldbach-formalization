import Lean

/-!
SOURCE ONLY. A kernel-reducible reader for the actual original witness
JSON fragment. In particular this deliberately does not call Lean.Json.parse:
the pinned Lean parser contains partial recursive declarations. The fuel
below is structural, not an external parsing or validity assumption.

Supported numeric tokens are JSON integers. Noninteger numeric tokens and
Unicode escapes are rejected, not rounded or silently normalized. The
closed parse-success guards on all 26 exact source texts must establish
that the original files belong to this fragment. No parser was executed.
-/

namespace ImbalancedChen.P2OriginalSaving19Archive

inductive SourceJson where
  | null
  | boolean (b : Bool)
  | number (token : String)
  | str (s : String)
  | arr (items : List SourceJson)
  | obj (fields : List (String × SourceJson))
  deriving Inhabited

namespace SourceJson

noncomputable section

def white (xs : List Char) : List Char :=
  xs.dropWhile fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t'

def quoted : Nat → List Char → List Char → Except String (String × List Char) :=
  Nat.rec (motive := fun _ => List Char → List Char → Except String (String × List Char))
    (fun _ _ => .error "string fuel exhausted")
    (fun _ previous input acc =>
      match input with
      | [] => .error "unterminated string"
      | '"' :: xs => .ok (String.ofList acc.reverse, xs)
      | '\\' :: c :: xs =>
        match c with
        | '"' => previous xs ('"' :: acc)
        | '\\' => previous xs ('\\' :: acc)
        | '/' => previous xs ('/' :: acc)
        | 'b' => previous xs (Char.ofNat 8 :: acc)
        | 'f' => previous xs (Char.ofNat 12 :: acc)
        | 'n' => previous xs ('\n' :: acc)
        | 'r' => previous xs ('\r' :: acc)
        | 't' => previous xs ('\t' :: acc)
        | _ => .error "unsupported or invalid JSON escape"
      | c :: xs =>
        if c.toNat < 32 then .error "unescaped control character"
        else previous xs (c :: acc))

def integerToken (xs : List Char) : Except String (SourceJson × List Char) := do
  let negative := xs.head? = some '-'
  let input := if negative then xs.drop 1 else xs
  let ds := input.takeWhile Char.isDigit
  if ds.isEmpty then throw "missing JSON integer digits"
  if ds.head? = some '0' ∧ ds.length ≠ 1 then throw "leading JSON integer zero"
  let token := String.ofList ((if negative then ['-'] else []) ++ ds)
  return (.number token, input.drop ds.length)

/-- The three parsers at one fuel share the preceding fuel's functions.
The explicit recursor retains the original simultaneous descent. -/
private def parserBundle : Nat →
    (List Char → Except String (SourceJson × List Char)) ×
    (List Char → List SourceJson → Except String (SourceJson × List Char)) ×
    (List Char → List (String × SourceJson) → Except String (SourceJson × List Char)) :=
  Nat.rec (motive := fun _ =>
      (List Char → Except String (SourceJson × List Char)) ×
      (List Char → List SourceJson → Except String (SourceJson × List Char)) ×
      (List Char → List (String × SourceJson) → Except String (SourceJson × List Char)))
    ((fun _ => .error "value fuel exhausted"),
      (fun _ _ => .error "array fuel exhausted"),
      (fun _ _ => .error "object fuel exhausted"))
    (fun fuel previous =>
      ((fun input =>
        match white input with
        | '"' :: xs => do
          let (s, rest) ← quoted fuel xs []
          return (.str s, rest)
        | '[' :: xs => previous.2.1 (white xs) []
        | '{' :: xs => previous.2.2 (white xs) []
        | 't' :: 'r' :: 'u' :: 'e' :: xs => .ok (.boolean true, xs)
        | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: xs => .ok (.boolean false, xs)
        | 'n' :: 'u' :: 'l' :: 'l' :: xs => .ok (.null, xs)
        | xs => integerToken xs),
      (fun xs acc =>
        match xs, acc with
        | ']' :: tail, [] => .ok (.arr [], tail)
        | _, _ => do
          let (v, rest) ← previous.1 xs
          match white rest with
          | ']' :: tail => return (.arr ((v :: acc).reverse), tail)
          | ',' :: tail => previous.2.1 (white tail) (v :: acc)
          | _ => throw "array separator missing"),
      (fun input acc =>
        match input, acc with
        | '}' :: xs, [] => .ok (.obj [], xs)
        | '"' :: xs, _ => do
          let (key, rest) ← quoted fuel xs []
          let ':' :: body := white rest | throw "object colon missing"
          let (v, tail) ← previous.1 body
          if acc.any (fun kv => kv.1 == key) then throw "duplicate original JSON key"
          match white tail with
          | '}' :: ending => return (.obj (((key, v) :: acc).reverse), ending)
          | ',' :: ending => previous.2.2 (white ending) ((key, v) :: acc)
          | _ => throw "object separator missing"
        | _, _ => .error "object key missing")))

def value : Nat → List Char → Except String (SourceJson × List Char) :=
  fun fuel => (parserBundle fuel).1

def array : Nat → List Char → List SourceJson → Except String (SourceJson × List Char) :=
  fun fuel => (parserBundle fuel).2.1

def object : Nat → List Char → List (String × SourceJson) →
    Except String (SourceJson × List Char) :=
  fun fuel => (parserBundle fuel).2.2

def parse (s : String) : Except String SourceJson := do
  let (v, tail) ← value (s.length + 1) s.toList
  if (white tail).isEmpty then return v
  else throw "unconsumed original JSON input"

def getStr? : SourceJson → Except String String
  | .str s => .ok s
  | _ => .error "expected original JSON string"

def getArr? : SourceJson → Except String (Array SourceJson)
  | .arr xs => .ok xs.toArray
  | _ => .error "expected original JSON array"

def getObjVal? (j : SourceJson) (key : String) : Except String SourceJson :=
  match j with
  | .obj fields =>
    match fields.find? (fun kv => kv.1 == key) with
    | some (_, v) => .ok v
    | none => .error ("missing original field " ++ key)
  | _ => .error "expected original JSON object"

class Decode (α : Type) where
  read : SourceJson → Except String α

/-- Explicit total decimal conversion. No runtime parser is hidden here. -/
def digitsNat : List Char → Nat → Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat)
    (fun acc => some acc)
    (fun c _ previous acc =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
        previous (10 * acc + (c.toNat - 48))
      else none)

def natChars (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else digitsNat cs 0

def intChars : List Char → Option Int
  | '-' :: cs => (natChars cs).map (fun n => -(Int.ofNat n))
  | cs => (natChars cs).map Int.ofNat

instance : Decode Nat where
  read := fun j => match j with
    | .number s => match natChars s.toList with
      | some n => .ok n
      | none => .error "expected original natural number"
    | _ => .error "expected original integer token"

instance : Decode String where
  read := getStr?

instance [Decode α] : Decode (Array α) where
  read := fun j => do (← getArr? j).mapM Decode.read

def getObjValAs? (j : SourceJson) (α : Type) [Decode α] (key : String) : Except String α := do
  Decode.read (← getObjVal? j key)

end
end SourceJson
end ImbalancedChen.P2OriginalSaving19Archive
