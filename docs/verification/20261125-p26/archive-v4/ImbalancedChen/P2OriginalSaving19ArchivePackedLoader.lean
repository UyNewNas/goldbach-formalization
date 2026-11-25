import ImbalancedChen.P2OriginalSaving19PackedChars

/-!
SOURCE CANDIDATE, NOT COMPILED. Shared raw-input quotation only.
Each data owner supplies one original ../goldbach-research/ path. The loader
reads that complete UTF-8 file via IO.FS.readFile, preserves s.toList in order,
runs the same proved PackedChars.pack, and quotes only the resulting Tree
constructors. It performs no JSON parse, typed decoding, numerical check,
source hash check, truncation, padding, or line-ending normalization.
-/
namespace ImbalancedChen.P2OriginalSaving19Archive

open Lean Elab Term
set_option maxRecDepth 1000000

private def quoteOriginalPackedTree : P2OriginalSaving19PackedChars.Tree → Expr
  | .empty => mkConst ``P2OriginalSaving19PackedChars.Tree.empty
  | .leaf n word =>
      mkApp2 (mkConst ``P2OriginalSaving19PackedChars.Tree.leaf) (mkNatLit n) (mkNatLit word)
  | .branch l r =>
      mkApp2 (mkConst ``P2OriginalSaving19PackedChars.Tree.branch)
        (quoteOriginalPackedTree l) (quoteOriginalPackedTree r)

elab "originalPackedText% " p:str : term => do
  let s ← IO.FS.readFile p.getString
  return quoteOriginalPackedTree (P2OriginalSaving19PackedChars.pack s.toList)

end ImbalancedChen.P2OriginalSaving19Archive
