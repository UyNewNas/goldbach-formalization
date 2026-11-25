import ImbalancedChen.P2OriginalSaving19SourceJsonFuel

/-!
Exact continuations of the original array and object reader. These definitions
are used only through equality proofs unfolding the original public equations.
No recognition rule, duplicate-key test, error, or output reversal is removed.
-/
namespace ImbalancedChen.P2Saving16Cell00Segments

open P2OriginalSaving19Archive

noncomputable section

def arrayAfter (fuel : Nat) (acc : List SourceJson)
    (result : SourceJson × List Char) : Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

def objectAfter (fuel : Nat) (acc : List (String × SourceJson)) (key : String)
    (result : SourceJson × List Char) : Except String (SourceJson × List Char) :=
  if acc.any (fun kv => kv.1 == key) then .error "duplicate original JSON key"
  else
    match SourceJson.white result.2 with
    | '}' :: tail => .ok (.obj (((key, result.1) :: acc).reverse), tail)
    | ',' :: tail => SourceJson.object fuel (SourceJson.white tail) ((key, result.1) :: acc)
    | _ => .error "object separator missing"

end
end ImbalancedChen.P2Saving16Cell00Segments
