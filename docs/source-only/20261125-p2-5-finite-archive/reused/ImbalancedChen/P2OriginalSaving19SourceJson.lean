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

def white (xs : List Char) : List Char :=
  xs.dropWhile fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t'

def quoted : Nat → List Char → List Char → Except String (String × List Char)
  | 0, _, _ => .error "string fuel exhausted"
  | _ + 1, [], _ => .error "unterminated string"
  | _ + 1, '"' :: xs, acc => .ok (String.ofList acc.reverse, xs)
  | fuel + 1, '\\' :: c :: xs, acc =>
    match c with
    | '"' => quoted fuel xs ('"' :: acc)
    | '\\' => quoted fuel xs ('\\' :: acc)
    | '/' => quoted fuel xs ('/' :: acc)
    | 'b' => quoted fuel xs (Char.ofNat 8 :: acc)
    | 'f' => quoted fuel xs (Char.ofNat 12 :: acc)
    | 'n' => quoted fuel xs ('\n' :: acc)
    | 'r' => quoted fuel xs ('\r' :: acc)
    | 't' => quoted fuel xs ('\t' :: acc)
    | _ => .error "unsupported or invalid JSON escape"
  | fuel + 1, c :: xs, acc =>
    if c.toNat < 32 then .error "unescaped control character"
    else quoted fuel xs (c :: acc)

def integerToken (xs : List Char) : Except String (SourceJson × List Char) := do
  let negative := xs.head? = some '-'
  let input := if negative then xs.drop 1 else xs
  let ds := input.takeWhile Char.isDigit
  if ds.isEmpty then throw "missing JSON integer digits"
  if ds.head? = some '0' ∧ ds.length ≠ 1 then throw "leading JSON integer zero"
  let token := String.ofList ((if negative then ['-'] else []) ++ ds)
  return (.number token, input.drop ds.length)

mutual
  def value : Nat → List Char → Except String (SourceJson × List Char)
    | 0, _ => .error "value fuel exhausted"
    | fuel + 1, input =>
      match white input with
      | '"' :: xs => do
        let (s, rest) ← quoted fuel xs []
        return (.str s, rest)
      | '[' :: xs => array fuel (white xs) []
      | '{' :: xs => object fuel (white xs) []
      | 't' :: 'r' :: 'u' :: 'e' :: xs => .ok (.boolean true, xs)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: xs => .ok (.boolean false, xs)
      | 'n' :: 'u' :: 'l' :: 'l' :: xs => .ok (.null, xs)
      | xs => integerToken xs

  def array : Nat → List Char → List SourceJson → Except String (SourceJson × List Char)
    | 0, _, _ => .error "array fuel exhausted"
    | _ + 1, ']' :: xs, [] => .ok (.arr [], xs)
    | fuel + 1, xs, acc => do
      let (v, rest) ← value fuel xs
      match white rest with
      | ']' :: tail => return (.arr ((v :: acc).reverse), tail)
      | ',' :: tail => array fuel (white tail) (v :: acc)
      | _ => throw "array separator missing"

  def object : Nat → List Char → List (String × SourceJson) →
      Except String (SourceJson × List Char)
    | 0, _, _ => .error "object fuel exhausted"
    | _ + 1, '}' :: xs, [] => .ok (.obj [], xs)
    | fuel + 1, '"' :: xs, acc => do
      let (key, rest) ← quoted fuel xs []
      let ':' :: body := white rest | throw "object colon missing"
      let (v, tail) ← value fuel body
      if acc.any (fun kv => kv.1 == key) then throw "duplicate original JSON key"
      match white tail with
      | '}' :: ending => return (.obj (((key, v) :: acc).reverse), ending)
      | ',' :: ending => object fuel (white ending) ((key, v) :: acc)
      | _ => throw "object separator missing"
    | _, _, _ => .error "object key missing"
end

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
def digitsNat : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
      digitsNat cs (10 * acc + (c.toNat - 48))
    else none

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

end SourceJson
end ImbalancedChen.P2OriginalSaving19Archive
