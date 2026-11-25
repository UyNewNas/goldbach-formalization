import ImbalancedChen.P2Saving16CanonicalCharLoader

/-!
SOURCE ONLY / NOT COMPILED. Only canonical cell01 is quoted and bound here.
No second String definition is introduced. The theorem compares the quoted
characters directly with the unchanged originalText (1 : Fin 14).

The proof reuses the accepted raw cell00 attempt003 reflexivity construction;
normal kernel checking, independent replay and complete owned audit remain
required for this new module. No cell00 proof is rebuilt by this candidate.
-/
namespace ImbalancedChen.P2Saving16CanonicalCell01Binding

-- Same source-local options as the accepted raw cell00 attempt003. The
-- effective maxRecDepth is 1000000 here; these options do not alter consumers.
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving16OriginalArchive (originalText)

noncomputable def chars01 : List Char :=
  canonicalSaving16Chars% (1 : Fin 14)

theorem ofList_chars01_eq_originalText1 :
    String.ofList chars01 = originalText (1 : Fin 14) := by
  run_tac do
    Lean.Elab.Tactic.liftMetaFinishingTactic fun goal => do
      goal.refl (check := false)

#print axioms ofList_chars01_eq_originalText1

end ImbalancedChen.P2Saving16CanonicalCell01Binding
