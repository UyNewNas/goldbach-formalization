import ImbalancedChen.P2OriginalSaving16FiniteCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact relocation of the existing rational affine evaluator and original
first-simplex interior candidate from P2OriginalSaving16OriginalArchive.
Their namespace, command text, and rational data inputs are unchanged.
The global archive guards remain in their original owner. This fresh
owner needs its own complete declaration audit and kernel replay.
-/
namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open scoped BigOperators

noncomputable section

def evalQ (a : Fin 9 → ℚ) (x : QPoint) : ℚ := a 0 + ∑ j : Fin 8, a j.succ * x j

/-- A deterministic rational interior candidate derived from the first
original nondegenerate simplex. Its strictness is checked below, not
inferred from any floating navigation margin. -/
def interiorCandidate (c : CellRecord) : QPoint := fun j =>
  (∑ k : Fin 9, simplexVertices c (c.simplices.getD 0 default) k j) / 9

end
end ImbalancedChen.P2OriginalSaving16OriginalArchive
