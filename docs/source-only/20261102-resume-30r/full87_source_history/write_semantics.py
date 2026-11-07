"""Emit literal row-selector declarations and UNEVALUATED symbolic proof bodies.
No source producer, row evaluation, guard, Lean, or numerical replay is run.
"""
from pathlib import Path
import json
H=Path(__file__).resolve().parent
p=H/'P4AOriginalRemainingEighthSources.lean'
sel=json.loads((H/'SOURCE_RECEIPT.json').read_text())['selectors']
text=p.read_text(encoding='utf-8')
before=text.split('-- GENERATED_ROW_IDENTITIES')[0]
after=text.split('-- END_GENERATED_ROW_IDENTITIES',1)[1] if '-- END_GENERATED_ROW_IDENTITIES' in text else ''
def vec(xs):return '!['+', '.join(map(str,xs))+']'
lines=[]
for name,key,size in [('commonRow','common',35),('branchRow','branches',62)]:
    lines.append(f'def {name} : (c : Cell) → Fin {size} → Fin (rowCount c)')
    for r in sel:
        tag=r['family'];pat=tag+(' _' if tag in ('ascending','nine','h5','h7') else '')
        lines.append('  | .'+pat+' => '+vec(r[key]))
    lines.append('')
lines.append('''def leftMasks : Cell → Finset ℕ
  | .ascending i => P4AOriginalAscendingFourteenAffineSource.leftMasks i
  | .seed => P4AOriginalSeed7Unequal15Literal.seed7Left
  | .nine i => P4AOriginalSeed7Unequal15Literal.nineLeft i
  | .fiftyA => P4AOriginalSeed7Unequal15Literal.fiftyAscLeft
  | .fiftyD => P4AOriginalSeed7Unequal15Literal.fiftyDescLeft
  | .h5 i => P4AOriginalFirstFailureH5H7Literal.h5LeftMasks i
  | .h7 i => P4AOriginalFirstFailureH5H7Literal.h7LeftMasks i
def winner : Cell → ℕ
  | .ascending _ | .seed => 6
  | .fiftyA | .fiftyD => 50
  | _ => 9
def branchMask (c : Cell) (k : Fin 62) : ℕ :=
  if k.val+1 < winner c then k.val+1 else k.val+2
def subsetSum (m : ℕ) (t : Point) : ℝ :=
  ∑ j : Fin 6, if decide (m / 2^j.val % 2 = 1) then t j.castSucc.castSucc else 0
def oldPlane (c : Cell) (m : ℕ) (t : Point) : ℝ :=
  if m ∈ leftMasks c then A (subsetSum m t) else C (subsetSum m t)
''')
defs='''row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks'''
for name,statement,n in [
 ('source_common_row','evalRow (row c (commonRow c k)) t = commonSlack c t k',35),
 ('source_branch_row','evalRow (row c (branchRow c k)) t = comparison c t-oldPlane c (branchMask c k) t',62),
 ('winner_plane','oldPlane c (winner c) t = comparison c t',0)]:
    lines += ['set_option maxRecDepth 8192 in','set_option maxHeartbeats 0 in',
      f'theorem {name} (c : Cell) '+(f'(k : Fin {n}) ' if n else '')+f'(t : Point) :\n    {statement} := by', '  cases c with']
    for r in sel:
        tag=r['family'];arg=' i' if tag in ('ascending','nine','h5','h7') else ''
        tactics=[]
        if arg:tactics.append('fin_cases i')
        if n:tactics.append('fin_cases k')
        tactics+=['norm_num ['+defs+']','ring']
        lines.append('  | '+tag+arg+' =>\n    '+' <;>\n    '.join(tactics))
    lines.append('')
p.write_text(before+'-- GENERATED_ROW_IDENTITIES\n'+ '\n'.join(lines)+'\n-- END_GENERATED_ROW_IDENTITIES'+after,encoding='utf-8',newline='\n')
print('Wrote row-name selectors and symbolic identities. Proof bodies UNEVALUATED.')
