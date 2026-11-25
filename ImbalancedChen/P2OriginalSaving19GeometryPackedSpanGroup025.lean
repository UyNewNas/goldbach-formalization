import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00200

/-! Exact compact prefix group 25, bytes [114185,120670).
The original parser certificates remain frozen; this owner only relates input
representations through exact complete character spans. -/
namespace ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_170_before_prefix"
  err.flush

theorem compactSpan170_prefix :
    (compactRest00 114185).take 6485 = simplicesBlock002Chars00 := by rfl

theorem compactSpan170_split :
    compactRest00 114185 = simplicesBlock002Chars00 ++ compactRest00 120670 := by
  calc
    compactRest00 114185 =
        (compactRest00 114185).take 6485 ++ (compactRest00 114185).drop 6485 :=
      (List.take_append_drop 6485 (compactRest00 114185)).symm
    _ = simplicesBlock002Chars00 ++ (compactRest00 114185).drop 6485 :=
      congrArg (fun part => part ++ (compactRest00 114185).drop 6485) compactSpan170_prefix
    _ = simplicesBlock002Chars00 ++ compactRest00 120670 :=
      congrArg (fun tail => simplicesBlock002Chars00 ++ tail) (compactRest00_drop 114185 6485)

theorem compactSpan170_rest_eq (htail : geometryChars00.drop 120670 = compactRest00 120670) :
    geometryChars00.drop 114185 = compactRest00 114185 := by
  have hp : (geometryChars00.drop 114185).take 6485 = simplicesBlock002Chars00 :=
    geometryChars00_simplices_block_002_prefix
  exact (list_drop_split_of_prefix geometryChars00 114185 6485 simplicesBlock002Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock002Chars00 ++ tail) htail).trans compactSpan170_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_170_complete"
  err.flush

theorem group025_rest_eq
    (htail : geometryChars00.drop 120670 = compactRest00 120670) :
    geometryChars00.drop 114185 = compactRest00 114185 := by
  have h170 := compactSpan170_rest_eq htail
  exact h170

#print axioms compactSpan170_prefix
#print axioms compactSpan170_split
#print axioms compactSpan170_rest_eq
#print axioms group025_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
