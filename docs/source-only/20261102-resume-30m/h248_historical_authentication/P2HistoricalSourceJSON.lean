import Lean
import Mathlib.Data.Rat.Floor

/-!
SOURCE ONLY. This source has NOT been elaborated. Its only IO operation is
the original_text% term elaborator, which the USER may run on compilation.
It copies UTF-8 file text into a String literal, without running a producer,
JSON evaluator, generator, checker, native_decide, or external process.

All subsequent parsing is the total, fuelled, pure definition below. Thus
the mathematical guards reduce from the actual embedded text; neither a
digest nor the host's JSON parser is an equality proof. No bulk literal
array was generated during preparation of this source.
-/

namespace ImbalancedChen.P2HistoricalSourceJSON

open Lean Elab Term

syntax "original_text% " str : term

elab_rules : term
  | `(original_text% $p:str) => do
      let contents ← liftIO <| IO.FS.readFile p.getString
      return Lean.mkStrLit contents

/-- Numbers are retained as their decimal tokens; quoted and unquoted
integer fields therefore share a lossless integer reader. -/
inductive Value where
  | atom (s : String)
  | str (s : String)
  | arr (xs : List Value)
  | obj (xs : List (String × Value))
  deriving Inhabited

def white (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'

def ws (cs : List Char) : List Char := cs.dropWhile white

def delimiter (c : Char) : Bool := white c || c == ',' || c == ']' || c == '}'

/-- Decode the escapes emitted by the original Python json.dump. A unicode
escape is preserved as six characters: none of the consumed keys, rational
or integer fields uses unicode escapes. Irrelevant prose remains parseable.
The semantic restriction on consumed scalar fields is explicit in ScalarOK. -/
def quoted : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _+1, [], _ => none
  | _+1, '"' :: cs, acc => some (String.ofList acc.reverse, cs)
  | n+1, '\\' :: c :: cs, acc =>
      match c with
      | '"' => quoted n cs ('"' :: acc)
      | '\\' => quoted n cs ('\\' :: acc)
      | '/' => quoted n cs ('/' :: acc)
      | 'n' => quoted n cs ('\n' :: acc)
      | 'r' => quoted n cs ('\r' :: acc)
      | 't' => quoted n cs ('\t' :: acc)
      | 'b' => quoted n cs (Char.ofNat 8 :: acc)
      | 'f' => quoted n cs (Char.ofNat 12 :: acc)
      | 'u' => quoted n cs ('u' :: '\\' :: acc)
      | _ => none
  | n+1, c :: cs, acc => quoted n cs (c :: acc)

mutual
  def value : Nat → List Char → Option (Value × List Char)
    | 0, _ => none
    | n+1, cs =>
        match ws cs with
        | '"' :: rest => do
            let (s, tail) ← quoted (n+1) rest []
            pure (.str s, ws tail)
        | '[' :: rest => array n (ws rest) []
        | '{' :: rest => object n (ws rest) []
        | rest =>
            let token := rest.takeWhile (fun c => !delimiter c)
            if token.isEmpty then none
            else some (.atom (String.ofList token), ws (rest.drop token.length))

  def array : Nat → List Char → List Value → Option (Value × List Char)
    | 0, _, _ => none
    | _+1, ']' :: rest, acc => some (.arr acc.reverse, ws rest)
    | n+1, cs, acc => do
        let (v, rest) ← value n cs
        match rest with
        | ',' :: tail => array n (ws tail) (v :: acc)
        | ']' :: tail => pure (.arr (v :: acc).reverse, ws tail)
        | _ => none

  def object : Nat → List Char → List (String × Value) →
      Option (Value × List Char)
    | 0, _, _ => none
    | _+1, '}' :: rest, acc => some (.obj acc.reverse, ws rest)
    | n+1, '"' :: rest, acc => do
        let (key, tail) ← quoted n rest []
        match ws tail with
        | ':' :: tail =>
            let (v, tail) ← value n (ws tail)
            match tail with
            | ',' :: tail => object n (ws tail) ((key,v) :: acc)
            | '}' :: tail => pure (.obj ((key,v) :: acc).reverse, ws tail)
            | _ => none
        | _ => none
    | _+1, _, _ => none
end

def parse (s : String) : Option Value := do
  let (v, tail) ← value (s.length+2) s.toList
  if tail.isEmpty then some v else none

def parsed (s : String) : Value := (parse s).getD (.atom "PARSE_FAILURE")

def field : Value → String → Value
  | .obj xs, k => ((xs.find? (fun p => p.1 == k)).map Prod.snd).getD (.atom "MISSING")
  | _, _ => .atom "MISSING"

def items : Value → List Value
  | .arr xs => xs
  | _ => []

def text : Value → String
  | .str s => s
  | .atom s => s
  | _ => "NON_SCALAR"

def integer? (v : Value) : Option Int := (text v).toInt?
def integer (v : Value) : Int := (integer? v).getD 0
def natural (v : Value) : Nat := (integer v).toNat

def rational? (v : Value) : Option ℚ :=
  match (text v).splitOn "/" with
  | [a] => do let n ← a.toInt?; pure (n : ℚ)
  | [a,b] => do
      let n ← a.toInt?
      let d ← b.toInt?
      if d = 0 then none else pure ((n : ℚ) / (d : ℚ))
  | _ => none

def rational (v : Value) : ℚ := (rational? v).getD 0
def at (v : Value) (n : Nat) : Value := ((items v)[n]?).getD (.atom "MISSING")

def ScalarOK (v : Value) : Prop := (integer? v).isSome = true
def RationalOK (v : Value) : Prop := (rational? v).isSome = true
def IndexOK (v : Value) : Prop := ScalarOK v ∧ 0 ≤ integer v ∧ integer v < 200

instance (v : Value) : Decidable (ScalarOK v) := inferInstanceAs (Decidable (_ = _))
instance (v : Value) : Decidable (RationalOK v) := inferInstanceAs (Decidable (_ = _))
instance (v : Value) : Decidable (IndexOK v) := by unfold IndexOK; infer_instance

end ImbalancedChen.P2HistoricalSourceJSON
