import Lean

def parseInteger (f : List Char → Option Int) (s : String) : Except String Int :=
  match f s.toList with
  | some z => .ok z
  | none => .error "invalid original integer"

def parseRational (f : List Char → Option Int) (s : String) : Except String Int := do
  let chars := s.toList
  let numerator := chars.takeWhile (fun c => c != '/')
  match chars.dropWhile (fun c => c != '/') with
  | [] => return (← parseInteger f (String.ofList numerator) : Int)
  | '/' :: denominator =>
    let n ← parseInteger f (String.ofList numerator)
    let d ← parseInteger f (String.ofList denominator)
    if d = 0 then throw "zero original rational denominator"
    return (n : Int) / (d : Int)
  | _ => throw "invalid original rational"


theorem parseInteger_ofList (f : List Char → Option Int) (cs : List Char) :
    parseInteger f (String.ofList cs) =
      match f cs with
      | some z => .ok z
      | none => .error "invalid original integer" := by
  unfold parseInteger
  rw [String.toList_ofList]

theorem parseRational_ofList (f : List Char → Option Int) (cs : List Char) :
    parseRational f (String.ofList cs) =
      (do
        let numerator := cs.takeWhile (fun c => c != '/')
        match cs.dropWhile (fun c => c != '/') with
        | [] =>
          let n ← match f numerator with
            | some z => .ok z
            | none => .error "invalid original integer"
          return (n : Int)
        | '/' :: denominator =>
          let n ← match f numerator with
            | some z => .ok z
            | none => .error "invalid original integer"
          let d ← match f denominator with
            | some z => .ok z
            | none => .error "invalid original integer"
          if d = 0 then throw "zero original rational denominator"
          return (n : Int) / (d : Int)
        | _ => throw "invalid original rational") := by
  unfold parseRational
  simp only [String.toList_ofList, parseInteger_ofList]
  cases hs : cs.dropWhile (fun c => c != '/') with
  | nil =>
    cases hn : f (cs.takeWhile (fun c => c != '/')) <;>
      rfl
  | cons c denominator =>
    by_cases hc : c = '/'
    · subst c
      simp only
      cases hn : f (cs.takeWhile (fun c => c != '/')) <;>
        cases hd : f denominator <;>
        rfl
    · simp [hc]

