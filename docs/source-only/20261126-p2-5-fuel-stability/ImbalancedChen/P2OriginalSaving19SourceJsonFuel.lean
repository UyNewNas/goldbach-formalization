import ImbalancedChen.P2OriginalSaving19SourceJson

/-!
Fuel-success stability for the exact original source JSON reader.
The equations below unfold the existing public parsers; no parser definition
or successful result is replaced or assumed.
-/

namespace ImbalancedChen.P2OriginalSaving19Archive.SourceJson

theorem quoted_zero (input acc : List Char) :
    quoted 0 input acc = .error "string fuel exhausted" := rfl

theorem quoted_succ (fuel : Nat) (input acc : List Char) :
    quoted (fuel + 1) input acc =
      match input with
      | [] => .error "unterminated string"
      | '"' :: xs => .ok (String.ofList acc.reverse, xs)
      | '\\' :: c :: xs =>
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
      | c :: xs =>
        if c.toNat < 32 then .error "unescaped control character"
        else quoted fuel xs (c :: acc) := rfl

theorem quoted_success_succ (fuel : Nat) :
    ∀ (input acc : List Char) (r : String × List Char),
      quoted fuel input acc = .ok r → quoted (fuel + 1) input acc = .ok r := by
  induction fuel with
  | zero =>
    intro input acc r h
    simp only [quoted_zero] at h
    cases h
  | succ fuel ih =>
    intro input acc r h
    rw [quoted_succ] at h ⊢
    split at h <;> try simp_all only
    · split at h <;> try simp_all only
      all_goals first | exact ih _ _ _ h | cases h
    · split at h <;> try simp_all only
      all_goals first | exact ih _ _ _ h | cases h

private def SuccessExtension {α : Type} (x y : Except String α) : Prop :=
  ∀ r, x = .ok r → y = .ok r

private theorem success_bind {α β : Type} {x y : Except String α}
    {f g : α → Except String β}
    (hx : SuccessExtension x y) (hf : ∀ a, SuccessExtension (f a) (g a)) :
    SuccessExtension (x >>= f) (y >>= g) := by
  intro r h
  cases he : x with
  | error e =>
    rw [he] at h
    cases h
  | ok a =>
    have hy := hx a he
    rw [he] at h
    change f a = .ok r at h
    rw [hy]
    exact hf a r h

theorem value_zero (input : List Char) :
    value 0 input = .error "value fuel exhausted" := rfl

theorem array_zero (input : List Char) (acc : List SourceJson) :
    array 0 input acc = .error "array fuel exhausted" := rfl

theorem object_zero (input : List Char) (acc : List (String × SourceJson)) :
    object 0 input acc = .error "object fuel exhausted" := rfl

theorem value_succ (fuel : Nat) (input : List Char) :
    value (fuel + 1) input =
      match white input with
      | '"' :: xs => do
        let (s, rest) ← quoted fuel xs []
        return (.str s, rest)
      | '[' :: xs => array fuel (white xs) []
      | '{' :: xs => object fuel (white xs) []
      | 't' :: 'r' :: 'u' :: 'e' :: xs => .ok (.boolean true, xs)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: xs => .ok (.boolean false, xs)
      | 'n' :: 'u' :: 'l' :: 'l' :: xs => .ok (.null, xs)
      | xs => integerToken xs := rfl

theorem array_succ (fuel : Nat) (xs : List Char) (acc : List SourceJson) :
    array (fuel + 1) xs acc =
      (match xs, acc with
      | ']' :: tail, [] => .ok (.arr [], tail)
      | _, _ => do
        let (v, rest) ← value fuel xs
        match white rest with
        | ']' :: tail => return (.arr ((v :: acc).reverse), tail)
        | ',' :: tail => array fuel (white tail) (v :: acc)
        | _ => throw "array separator missing") := rfl

theorem object_succ (fuel : Nat) (input : List Char)
    (acc : List (String × SourceJson)) :
    object (fuel + 1) input acc =
      match input, acc with
      | '}' :: xs, [] => .ok (.obj [], xs)
      | '"' :: xs, _ => do
        let (key, rest) ← quoted fuel xs []
        let ':' :: body := white rest | throw "object colon missing"
        let (v, tail) ← value fuel body
        if acc.any (fun kv => kv.1 == key) then throw "duplicate original JSON key"
        match white tail with
        | '}' :: ending => return (.obj (((key, v) :: acc).reverse), ending)
        | ',' :: ending => object fuel (white ending) ((key, v) :: acc)
        | _ => throw "object separator missing"
      | _, _ => .error "object key missing" := rfl

private theorem parser_success_succ (fuel : Nat) :
    (∀ input, SuccessExtension (value fuel input) (value (fuel + 1) input)) ∧
    (∀ input acc, SuccessExtension (array fuel input acc) (array (fuel + 1) input acc)) ∧
    (∀ input acc, SuccessExtension (object fuel input acc) (object (fuel + 1) input acc)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro input r h
      cases h
    · intro input acc r h
      cases h
    · intro input acc r h
      cases h
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro input r h
      rw [value_succ] at h ⊢
      split at h <;> try simp_all only
      · exact success_bind (quoted_success_succ fuel _ _) (fun _ _ h => h) r h
      · exact ih.2.1 _ _ _ h
      · exact ih.2.2 _ _ _ h
    · intro input acc r h
      rw [array_succ] at h ⊢
      split at h <;> try simp_all only
      refine success_bind (ih.1 _) (fun p => ?_) r h
      rcases p with ⟨v, rest⟩
      intro r h
      split at h <;> try simp_all only
      exact ih.2.1 _ _ _ h
    · intro input acc r h
      rw [object_succ] at h ⊢
      split at h <;> try simp_all only
      refine success_bind (quoted_success_succ fuel _ _) (fun p => ?_) r h
      rcases p with ⟨key, rest⟩
      intro r h
      split at h <;> try simp_all only
      refine success_bind (ih.1 _) (fun p => ?_) r h
      rcases p with ⟨v, tail⟩
      intro r h
      split at h
      · cases h
      · simp_all only [Bool.false_eq_true, if_false]
        split at h <;> try simp_all only
        exact ih.2.2 _ _ _ h

/-- A successful string parse preserves both the string and unconsumed input
when any finite amount of fuel is added. -/
theorem quoted_success_add (fuel extra : Nat) (input acc : List Char)
    (r : String × List Char) (h : quoted fuel input acc = .ok r) :
    quoted (fuel + extra) input acc = .ok r := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact quoted_success_succ (fuel + extra) input acc r ih

/-- A successful value parse preserves the full JSON value and unconsumed input
when any finite amount of fuel is added. -/
theorem value_success_add (fuel extra : Nat) (input : List Char)
    (r : SourceJson × List Char) (h : value fuel input = .ok r) :
    value (fuel + extra) input = .ok r := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact (parser_success_succ (fuel + extra)).1 input r ih

/-- A successful array parse is stable under any finite fuel increase. -/
theorem array_success_add (fuel extra : Nat) (input : List Char) (acc : List SourceJson)
    (r : SourceJson × List Char) (h : array fuel input acc = .ok r) :
    array (fuel + extra) input acc = .ok r := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact (parser_success_succ (fuel + extra)).2.1 input acc r ih

/-- A successful object parse is stable under any finite fuel increase. -/
theorem object_success_add (fuel extra : Nat) (input : List Char)
    (acc : List (String × SourceJson)) (r : SourceJson × List Char)
    (h : object fuel input acc = .ok r) :
    object (fuel + extra) input acc = .ok r := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact (parser_success_succ (fuel + extra)).2.2 input acc r ih

/-- Ordered-fuel form of `quoted_success_add`. -/
theorem quoted_success_of_le {fuel larger : Nat} (hle : fuel ≤ larger)
    (input acc : List Char) (r : String × List Char)
    (h : quoted fuel input acc = .ok r) : quoted larger input acc = .ok r := by
  have hs := quoted_success_add fuel (larger - fuel) input acc r h
  simpa only [Nat.add_sub_of_le hle] using hs

/-- Ordered-fuel form of `value_success_add`. -/
theorem value_success_of_le {fuel larger : Nat} (hle : fuel ≤ larger)
    (input : List Char) (r : SourceJson × List Char)
    (h : value fuel input = .ok r) : value larger input = .ok r := by
  have hs := value_success_add fuel (larger - fuel) input r h
  simpa only [Nat.add_sub_of_le hle] using hs

/-- Ordered-fuel form of `array_success_add`. -/
theorem array_success_of_le {fuel larger : Nat} (hle : fuel ≤ larger)
    (input : List Char) (acc : List SourceJson) (r : SourceJson × List Char)
    (h : array fuel input acc = .ok r) : array larger input acc = .ok r := by
  have hs := array_success_add fuel (larger - fuel) input acc r h
  simpa only [Nat.add_sub_of_le hle] using hs

/-- Ordered-fuel form of `object_success_add`. -/
theorem object_success_of_le {fuel larger : Nat} (hle : fuel ≤ larger)
    (input : List Char) (acc : List (String × SourceJson)) (r : SourceJson × List Char)
    (h : object fuel input acc = .ok r) : object larger input acc = .ok r := by
  have hs := object_success_add fuel (larger - fuel) input acc r h
  simpa only [Nat.add_sub_of_le hle] using hs

/-- A checked successful parse at sufficient smaller fuel yields success of the
unchanged original parser, including its trailing-whitespace guard. -/
theorem parse_success_of_value (s : String) (fuel : Nat)
    (v : SourceJson) (tail : List Char) (hle : fuel ≤ s.length + 1)
    (h : value fuel s.toList = .ok (v, tail))
    (htail : (white tail).isEmpty = true) : parse s = .ok v := by
  have hs := value_success_of_le hle s.toList (v, tail) h
  unfold parse
  rw [hs]
  change (if (white tail).isEmpty then Except.ok v else
    Except.error "unconsumed original JSON input") = .ok v
  rw [htail]
  rfl

end ImbalancedChen.P2OriginalSaving19Archive.SourceJson
