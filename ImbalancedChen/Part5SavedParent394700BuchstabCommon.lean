import ImbalancedChen.Part5SavedParent394700BuchstabData

/- PROPOSED CANDIDATE MODULE ONLY; SOURCEONLY, no object or import acceptance. -/
namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly

open Set
open scoped unitInterval
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

/- Kernel-resource staging ONLY. Original data/functions are unchanged.
No native_decide, unsafe evaluator, added axiom or target-bound premise.
The small choose, power and basis facts have ordinary kernel proof terms.
Each Horner proof unfolds at most eight original recursor steps, rewriting
the already-proved tail before arithmetic. The final normal-form equalities
use proof-producing norm_num, not a giant Boolean reduction.
Actual memory/time behavior remains UNTESTED by this SOURCEONLY worker. -/
namespace FiniteBernsteinResource

theorem choose00 : Nat.fast_choose 52 0 = 1 := by decide

theorem choose01 : Nat.fast_choose 52 1 = 52 := by decide

theorem choose02 : Nat.fast_choose 52 2 = 1326 := by decide

theorem choose03 : Nat.fast_choose 52 3 = 22100 := by decide

theorem choose04 : Nat.fast_choose 52 4 = 270725 := by decide

theorem choose05 : Nat.fast_choose 52 5 = 2598960 := by decide

theorem choose06 : Nat.fast_choose 52 6 = 20358520 := by decide

theorem choose07 : Nat.fast_choose 52 7 = 133784560 := by decide

theorem choose08 : Nat.fast_choose 52 8 = 752538150 := by decide

theorem choose09 : Nat.fast_choose 52 9 = 3679075400 := by decide

theorem choose10 : Nat.fast_choose 52 10 = 15820024220 := by decide

theorem choose11 : Nat.fast_choose 52 11 = 60403728840 := by decide

theorem choose12 : Nat.fast_choose 52 12 = 206379406870 := by decide

theorem choose13 : Nat.fast_choose 52 13 = 635013559600 := by decide

theorem choose14 : Nat.fast_choose 52 14 = 1768966344600 := by decide

theorem choose15 : Nat.fast_choose 52 15 = 4481381406320 := by decide

theorem choose16 : Nat.fast_choose 52 16 = 10363194502115 := by decide

theorem choose17 : Nat.fast_choose 52 17 = 21945588357420 := by decide

theorem choose18 : Nat.fast_choose 52 18 = 42671977361650 := by decide

theorem choose19 : Nat.fast_choose 52 19 = 76360380541900 := by decide

theorem choose20 : Nat.fast_choose 52 20 = 125994627894135 := by decide

theorem choose21 : Nat.fast_choose 52 21 = 191991813933920 := by decide

theorem choose22 : Nat.fast_choose 52 22 = 270533919634160 := by decide

theorem choose23 : Nat.fast_choose 52 23 = 352870329957600 := by decide

theorem choose24 : Nat.fast_choose 52 24 = 426384982032100 := by decide

theorem choose25 : Nat.fast_choose 52 25 = 477551179875952 := by decide

theorem choose26 : Nat.fast_choose 52 26 = 495918532948104 := by decide

theorem choose27 : Nat.fast_choose 52 27 = 477551179875952 := by decide

theorem choose28 : Nat.fast_choose 52 28 = 426384982032100 := by decide

theorem choose29 : Nat.fast_choose 52 29 = 352870329957600 := by decide

theorem choose30 : Nat.fast_choose 52 30 = 270533919634160 := by decide

theorem choose31 : Nat.fast_choose 52 31 = 191991813933920 := by decide

theorem choose32 : Nat.fast_choose 52 32 = 125994627894135 := by decide

theorem choose33 : Nat.fast_choose 52 33 = 76360380541900 := by decide

theorem choose34 : Nat.fast_choose 52 34 = 42671977361650 := by decide

theorem choose35 : Nat.fast_choose 52 35 = 21945588357420 := by decide

theorem choose36 : Nat.fast_choose 52 36 = 10363194502115 := by decide

theorem choose37 : Nat.fast_choose 52 37 = 4481381406320 := by decide

theorem choose38 : Nat.fast_choose 52 38 = 1768966344600 := by decide

theorem choose39 : Nat.fast_choose 52 39 = 635013559600 := by decide

theorem choose40 : Nat.fast_choose 52 40 = 206379406870 := by decide

theorem choose41 : Nat.fast_choose 52 41 = 60403728840 := by decide

theorem choose42 : Nat.fast_choose 52 42 = 15820024220 := by decide

theorem choose43 : Nat.fast_choose 52 43 = 3679075400 := by decide

theorem choose44 : Nat.fast_choose 52 44 = 752538150 := by decide

theorem choose45 : Nat.fast_choose 52 45 = 133784560 := by decide

theorem choose46 : Nat.fast_choose 52 46 = 20358520 := by decide

theorem choose47 : Nat.fast_choose 52 47 = 2598960 := by decide

theorem choose48 : Nat.fast_choose 52 48 = 270725 := by decide

theorem choose49 : Nat.fast_choose 52 49 = 22100 := by decide

theorem choose50 : Nat.fast_choose 52 50 = 1326 := by decide

theorem choose51 : Nat.fast_choose 52 51 = 52 := by decide

theorem choose52 : Nat.fast_choose 52 52 = 1 := by decide

attribute [local simp] choose00 choose01 choose02 choose03 choose04 choose05 choose06 choose07 choose08 choose09 choose10 choose11 choose12 choose13 choose14 choose15 choose16 choose17 choose18 choose19 choose20 choose21 choose22 choose23 choose24 choose25 choose26 choose27 choose28 choose29 choose30 choose31 choose32 choose33 choose34 choose35 choose36 choose37 choose38 choose39 choose40 choose41 choose42 choose43 choose44 choose45 choose46 choose47 choose48 choose49 choose50 choose51 choose52

theorem powerX00 : powList [0, 1] 0 =
    [
    1
] := by
  rfl

theorem powerX01 : powList [0, 1] 1 =
    [
    0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 0) = _
  rw [powerX00]
  norm_num [mulList,scaleList,addList]

theorem powerX02 : powList [0, 1] 2 =
    [
    0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 1) = _
  rw [powerX01]
  norm_num [mulList,scaleList,addList]

theorem powerX03 : powList [0, 1] 3 =
    [
    0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 2) = _
  rw [powerX02]
  norm_num [mulList,scaleList,addList]

theorem powerX04 : powList [0, 1] 4 =
    [
    0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 3) = _
  rw [powerX03]
  norm_num [mulList,scaleList,addList]

theorem powerX05 : powList [0, 1] 5 =
    [
    0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 4) = _
  rw [powerX04]
  norm_num [mulList,scaleList,addList]

theorem powerX06 : powList [0, 1] 6 =
    [
    0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 5) = _
  rw [powerX05]
  norm_num [mulList,scaleList,addList]

theorem powerX07 : powList [0, 1] 7 =
    [
    0, 0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 6) = _
  rw [powerX06]
  norm_num [mulList,scaleList,addList]

theorem powerX08 : powList [0, 1] 8 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    1
] := by
  change mulList [0, 1] (powList [0, 1] 7) = _
  rw [powerX07]
  norm_num [mulList,scaleList,addList]

theorem powerX09 : powList [0, 1] 9 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 8) = _
  rw [powerX08]
  norm_num [mulList,scaleList,addList]

theorem powerX10 : powList [0, 1] 10 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 9) = _
  rw [powerX09]
  norm_num [mulList,scaleList,addList]

theorem powerX11 : powList [0, 1] 11 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 10) = _
  rw [powerX10]
  norm_num [mulList,scaleList,addList]

theorem powerX12 : powList [0, 1] 12 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 11) = _
  rw [powerX11]
  norm_num [mulList,scaleList,addList]

theorem powerX13 : powList [0, 1] 13 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 12) = _
  rw [powerX12]
  norm_num [mulList,scaleList,addList]

theorem powerX14 : powList [0, 1] 14 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 13) = _
  rw [powerX13]
  norm_num [mulList,scaleList,addList]

theorem powerX15 : powList [0, 1] 15 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 14) = _
  rw [powerX14]
  norm_num [mulList,scaleList,addList]

theorem powerX16 : powList [0, 1] 16 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1
] := by
  change mulList [0, 1] (powList [0, 1] 15) = _
  rw [powerX15]
  norm_num [mulList,scaleList,addList]

theorem powerX17 : powList [0, 1] 17 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 16) = _
  rw [powerX16]
  norm_num [mulList,scaleList,addList]

theorem powerX18 : powList [0, 1] 18 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 17) = _
  rw [powerX17]
  norm_num [mulList,scaleList,addList]

theorem powerX19 : powList [0, 1] 19 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 18) = _
  rw [powerX18]
  norm_num [mulList,scaleList,addList]

theorem powerX20 : powList [0, 1] 20 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 19) = _
  rw [powerX19]
  norm_num [mulList,scaleList,addList]

theorem powerX21 : powList [0, 1] 21 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 20) = _
  rw [powerX20]
  norm_num [mulList,scaleList,addList]

theorem powerX22 : powList [0, 1] 22 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 21) = _
  rw [powerX21]
  norm_num [mulList,scaleList,addList]

theorem powerX23 : powList [0, 1] 23 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 22) = _
  rw [powerX22]
  norm_num [mulList,scaleList,addList]

theorem powerX24 : powList [0, 1] 24 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1
] := by
  change mulList [0, 1] (powList [0, 1] 23) = _
  rw [powerX23]
  norm_num [mulList,scaleList,addList]

theorem powerX25 : powList [0, 1] 25 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 24) = _
  rw [powerX24]
  norm_num [mulList,scaleList,addList]

theorem powerX26 : powList [0, 1] 26 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 25) = _
  rw [powerX25]
  norm_num [mulList,scaleList,addList]

theorem powerX27 : powList [0, 1] 27 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 26) = _
  rw [powerX26]
  norm_num [mulList,scaleList,addList]

theorem powerX28 : powList [0, 1] 28 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 27) = _
  rw [powerX27]
  norm_num [mulList,scaleList,addList]

theorem powerX29 : powList [0, 1] 29 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 28) = _
  rw [powerX28]
  norm_num [mulList,scaleList,addList]

theorem powerX30 : powList [0, 1] 30 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 29) = _
  rw [powerX29]
  norm_num [mulList,scaleList,addList]

theorem powerX31 : powList [0, 1] 31 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 30) = _
  rw [powerX30]
  norm_num [mulList,scaleList,addList]

theorem powerX32 : powList [0, 1] 32 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1
] := by
  change mulList [0, 1] (powList [0, 1] 31) = _
  rw [powerX31]
  norm_num [mulList,scaleList,addList]

theorem powerX33 : powList [0, 1] 33 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 32) = _
  rw [powerX32]
  norm_num [mulList,scaleList,addList]

theorem powerX34 : powList [0, 1] 34 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 33) = _
  rw [powerX33]
  norm_num [mulList,scaleList,addList]

theorem powerX35 : powList [0, 1] 35 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 34) = _
  rw [powerX34]
  norm_num [mulList,scaleList,addList]

theorem powerX36 : powList [0, 1] 36 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 35) = _
  rw [powerX35]
  norm_num [mulList,scaleList,addList]

theorem powerX37 : powList [0, 1] 37 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 36) = _
  rw [powerX36]
  norm_num [mulList,scaleList,addList]

theorem powerX38 : powList [0, 1] 38 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 37) = _
  rw [powerX37]
  norm_num [mulList,scaleList,addList]

theorem powerX39 : powList [0, 1] 39 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 38) = _
  rw [powerX38]
  norm_num [mulList,scaleList,addList]

theorem powerX40 : powList [0, 1] 40 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1
] := by
  change mulList [0, 1] (powList [0, 1] 39) = _
  rw [powerX39]
  norm_num [mulList,scaleList,addList]

theorem powerX41 : powList [0, 1] 41 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 40) = _
  rw [powerX40]
  norm_num [mulList,scaleList,addList]

theorem powerX42 : powList [0, 1] 42 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 41) = _
  rw [powerX41]
  norm_num [mulList,scaleList,addList]

theorem powerX43 : powList [0, 1] 43 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 42) = _
  rw [powerX42]
  norm_num [mulList,scaleList,addList]

theorem powerX44 : powList [0, 1] 44 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 43) = _
  rw [powerX43]
  norm_num [mulList,scaleList,addList]

theorem powerX45 : powList [0, 1] 45 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 44) = _
  rw [powerX44]
  norm_num [mulList,scaleList,addList]

theorem powerX46 : powList [0, 1] 46 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 45) = _
  rw [powerX45]
  norm_num [mulList,scaleList,addList]

theorem powerX47 : powList [0, 1] 47 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 46) = _
  rw [powerX46]
  norm_num [mulList,scaleList,addList]

theorem powerX48 : powList [0, 1] 48 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1
] := by
  change mulList [0, 1] (powList [0, 1] 47) = _
  rw [powerX47]
  norm_num [mulList,scaleList,addList]

theorem powerX49 : powList [0, 1] 49 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 48) = _
  rw [powerX48]
  norm_num [mulList,scaleList,addList]

theorem powerX50 : powList [0, 1] 50 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 49) = _
  rw [powerX49]
  norm_num [mulList,scaleList,addList]

theorem powerX51 : powList [0, 1] 51 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 50) = _
  rw [powerX50]
  norm_num [mulList,scaleList,addList]

theorem powerX52 : powList [0, 1] 52 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1
] := by
  change mulList [0, 1] (powList [0, 1] 51) = _
  rw [powerX51]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub00 : powList [1, -1] 0 =
    [
    1
] := by
  rfl

theorem powerOneSub01 : powList [1, -1] 1 =
    [
    1, -1
] := by
  change mulList [1, -1] (powList [1, -1] 0) = _
  rw [powerOneSub00]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub02 : powList [1, -1] 2 =
    [
    1, -2, 1
] := by
  change mulList [1, -1] (powList [1, -1] 1) = _
  rw [powerOneSub01]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub03 : powList [1, -1] 3 =
    [
    1, -3, 3, -1
] := by
  change mulList [1, -1] (powList [1, -1] 2) = _
  rw [powerOneSub02]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub04 : powList [1, -1] 4 =
    [
    1, -4, 6, -4, 1
] := by
  change mulList [1, -1] (powList [1, -1] 3) = _
  rw [powerOneSub03]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub05 : powList [1, -1] 5 =
    [
    1, -5, 10, -10, 5, -1
] := by
  change mulList [1, -1] (powList [1, -1] 4) = _
  rw [powerOneSub04]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub06 : powList [1, -1] 6 =
    [
    1, -6, 15, -20, 15, -6, 1
] := by
  change mulList [1, -1] (powList [1, -1] 5) = _
  rw [powerOneSub05]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub07 : powList [1, -1] 7 =
    [
    1, -7, 21, -35, 35, -21, 7, -1
] := by
  change mulList [1, -1] (powList [1, -1] 6) = _
  rw [powerOneSub06]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub08 : powList [1, -1] 8 =
    [
    1, -8, 28, -56, 70, -56, 28, -8,
    1
] := by
  change mulList [1, -1] (powList [1, -1] 7) = _
  rw [powerOneSub07]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub09 : powList [1, -1] 9 =
    [
    1, -9, 36, -84, 126, -126, 84, -36,
    9, -1
] := by
  change mulList [1, -1] (powList [1, -1] 8) = _
  rw [powerOneSub08]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub10 : powList [1, -1] 10 =
    [
    1, -10, 45, -120, 210, -252, 210, -120,
    45, -10, 1
] := by
  change mulList [1, -1] (powList [1, -1] 9) = _
  rw [powerOneSub09]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub11 : powList [1, -1] 11 =
    [
    1, -11, 55, -165, 330, -462, 462, -330,
    165, -55, 11, -1
] := by
  change mulList [1, -1] (powList [1, -1] 10) = _
  rw [powerOneSub10]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub12 : powList [1, -1] 12 =
    [
    1, -12, 66, -220, 495, -792, 924, -792,
    495, -220, 66, -12, 1
] := by
  change mulList [1, -1] (powList [1, -1] 11) = _
  rw [powerOneSub11]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub13 : powList [1, -1] 13 =
    [
    1, -13, 78, -286, 715, -1287, 1716, -1716,
    1287, -715, 286, -78, 13, -1
] := by
  change mulList [1, -1] (powList [1, -1] 12) = _
  rw [powerOneSub12]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub14 : powList [1, -1] 14 =
    [
    1, -14, 91, -364, 1001, -2002, 3003, -3432,
    3003, -2002, 1001, -364, 91, -14, 1
] := by
  change mulList [1, -1] (powList [1, -1] 13) = _
  rw [powerOneSub13]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub15 : powList [1, -1] 15 =
    [
    1, -15, 105, -455, 1365, -3003, 5005, -6435,
    6435, -5005, 3003, -1365, 455, -105, 15, -1
] := by
  change mulList [1, -1] (powList [1, -1] 14) = _
  rw [powerOneSub14]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub16 : powList [1, -1] 16 =
    [
    1, -16, 120, -560, 1820, -4368, 8008, -11440,
    12870, -11440, 8008, -4368, 1820, -560, 120, -16,
    1
] := by
  change mulList [1, -1] (powList [1, -1] 15) = _
  rw [powerOneSub15]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub17 : powList [1, -1] 17 =
    [
    1, -17, 136, -680, 2380, -6188, 12376, -19448,
    24310, -24310, 19448, -12376, 6188, -2380, 680, -136,
    17, -1
] := by
  change mulList [1, -1] (powList [1, -1] 16) = _
  rw [powerOneSub16]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub18 : powList [1, -1] 18 =
    [
    1, -18, 153, -816, 3060, -8568, 18564, -31824,
    43758, -48620, 43758, -31824, 18564, -8568, 3060, -816,
    153, -18, 1
] := by
  change mulList [1, -1] (powList [1, -1] 17) = _
  rw [powerOneSub17]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub19 : powList [1, -1] 19 =
    [
    1, -19, 171, -969, 3876, -11628, 27132, -50388,
    75582, -92378, 92378, -75582, 50388, -27132, 11628, -3876,
    969, -171, 19, -1
] := by
  change mulList [1, -1] (powList [1, -1] 18) = _
  rw [powerOneSub18]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub20 : powList [1, -1] 20 =
    [
    1, -20, 190, -1140, 4845, -15504, 38760, -77520,
    125970, -167960, 184756, -167960, 125970, -77520, 38760, -15504,
    4845, -1140, 190, -20, 1
] := by
  change mulList [1, -1] (powList [1, -1] 19) = _
  rw [powerOneSub19]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub21 : powList [1, -1] 21 =
    [
    1, -21, 210, -1330, 5985, -20349, 54264, -116280,
    203490, -293930, 352716, -352716, 293930, -203490, 116280, -54264,
    20349, -5985, 1330, -210, 21, -1
] := by
  change mulList [1, -1] (powList [1, -1] 20) = _
  rw [powerOneSub20]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub22 : powList [1, -1] 22 =
    [
    1, -22, 231, -1540, 7315, -26334, 74613, -170544,
    319770, -497420, 646646, -705432, 646646, -497420, 319770, -170544,
    74613, -26334, 7315, -1540, 231, -22, 1
] := by
  change mulList [1, -1] (powList [1, -1] 21) = _
  rw [powerOneSub21]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub23 : powList [1, -1] 23 =
    [
    1, -23, 253, -1771, 8855, -33649, 100947, -245157,
    490314, -817190, 1144066, -1352078, 1352078, -1144066, 817190, -490314,
    245157, -100947, 33649, -8855, 1771, -253, 23, -1
] := by
  change mulList [1, -1] (powList [1, -1] 22) = _
  rw [powerOneSub22]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub24 : powList [1, -1] 24 =
    [
    1, -24, 276, -2024, 10626, -42504, 134596, -346104,
    735471, -1307504, 1961256, -2496144, 2704156, -2496144, 1961256, -1307504,
    735471, -346104, 134596, -42504, 10626, -2024, 276, -24,
    1
] := by
  change mulList [1, -1] (powList [1, -1] 23) = _
  rw [powerOneSub23]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub25 : powList [1, -1] 25 =
    [
    1, -25, 300, -2300, 12650, -53130, 177100, -480700,
    1081575, -2042975, 3268760, -4457400, 5200300, -5200300, 4457400, -3268760,
    2042975, -1081575, 480700, -177100, 53130, -12650, 2300, -300,
    25, -1
] := by
  change mulList [1, -1] (powList [1, -1] 24) = _
  rw [powerOneSub24]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub26 : powList [1, -1] 26 =
    [
    1, -26, 325, -2600, 14950, -65780, 230230, -657800,
    1562275, -3124550, 5311735, -7726160, 9657700, -10400600, 9657700, -7726160,
    5311735, -3124550, 1562275, -657800, 230230, -65780, 14950, -2600,
    325, -26, 1
] := by
  change mulList [1, -1] (powList [1, -1] 25) = _
  rw [powerOneSub25]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub27 : powList [1, -1] 27 =
    [
    1, -27, 351, -2925, 17550, -80730, 296010, -888030,
    2220075, -4686825, 8436285, -13037895, 17383860, -20058300, 20058300, -17383860,
    13037895, -8436285, 4686825, -2220075, 888030, -296010, 80730, -17550,
    2925, -351, 27, -1
] := by
  change mulList [1, -1] (powList [1, -1] 26) = _
  rw [powerOneSub26]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub28 : powList [1, -1] 28 =
    [
    1, -28, 378, -3276, 20475, -98280, 376740, -1184040,
    3108105, -6906900, 13123110, -21474180, 30421755, -37442160, 40116600, -37442160,
    30421755, -21474180, 13123110, -6906900, 3108105, -1184040, 376740, -98280,
    20475, -3276, 378, -28, 1
] := by
  change mulList [1, -1] (powList [1, -1] 27) = _
  rw [powerOneSub27]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub29 : powList [1, -1] 29 =
    [
    1, -29, 406, -3654, 23751, -118755, 475020, -1560780,
    4292145, -10015005, 20030010, -34597290, 51895935, -67863915, 77558760, -77558760,
    67863915, -51895935, 34597290, -20030010, 10015005, -4292145, 1560780, -475020,
    118755, -23751, 3654, -406, 29, -1
] := by
  change mulList [1, -1] (powList [1, -1] 28) = _
  rw [powerOneSub28]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub30 : powList [1, -1] 30 =
    [
    1, -30, 435, -4060, 27405, -142506, 593775, -2035800,
    5852925, -14307150, 30045015, -54627300, 86493225, -119759850, 145422675, -155117520,
    145422675, -119759850, 86493225, -54627300, 30045015, -14307150, 5852925, -2035800,
    593775, -142506, 27405, -4060, 435, -30, 1
] := by
  change mulList [1, -1] (powList [1, -1] 29) = _
  rw [powerOneSub29]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub31 : powList [1, -1] 31 =
    [
    1, -31, 465, -4495, 31465, -169911, 736281, -2629575,
    7888725, -20160075, 44352165, -84672315, 141120525, -206253075, 265182525, -300540195,
    300540195, -265182525, 206253075, -141120525, 84672315, -44352165, 20160075, -7888725,
    2629575, -736281, 169911, -31465, 4495, -465, 31, -1
] := by
  change mulList [1, -1] (powList [1, -1] 30) = _
  rw [powerOneSub30]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub32 : powList [1, -1] 32 =
    [
    1, -32, 496, -4960, 35960, -201376, 906192, -3365856,
    10518300, -28048800, 64512240, -129024480, 225792840, -347373600, 471435600, -565722720,
    601080390, -565722720, 471435600, -347373600, 225792840, -129024480, 64512240, -28048800,
    10518300, -3365856, 906192, -201376, 35960, -4960, 496, -32,
    1
] := by
  change mulList [1, -1] (powList [1, -1] 31) = _
  rw [powerOneSub31]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub33 : powList [1, -1] 33 =
    [
    1, -33, 528, -5456, 40920, -237336, 1107568, -4272048,
    13884156, -38567100, 92561040, -193536720, 354817320, -573166440, 818809200, -1037158320,
    1166803110, -1166803110, 1037158320, -818809200, 573166440, -354817320, 193536720, -92561040,
    38567100, -13884156, 4272048, -1107568, 237336, -40920, 5456, -528,
    33, -1
] := by
  change mulList [1, -1] (powList [1, -1] 32) = _
  rw [powerOneSub32]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub34 : powList [1, -1] 34 =
    [
    1, -34, 561, -5984, 46376, -278256, 1344904, -5379616,
    18156204, -52451256, 131128140, -286097760, 548354040, -927983760, 1391975640, -1855967520,
    2203961430, -2333606220, 2203961430, -1855967520, 1391975640, -927983760, 548354040, -286097760,
    131128140, -52451256, 18156204, -5379616, 1344904, -278256, 46376, -5984,
    561, -34, 1
] := by
  change mulList [1, -1] (powList [1, -1] 33) = _
  rw [powerOneSub33]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub35 : powList [1, -1] 35 =
    [
    1, -35, 595, -6545, 52360, -324632, 1623160, -6724520,
    23535820, -70607460, 183579396, -417225900, 834451800, -1476337800, 2319959400, -3247943160,
    4059928950, -4537567650, 4537567650, -4059928950, 3247943160, -2319959400, 1476337800, -834451800,
    417225900, -183579396, 70607460, -23535820, 6724520, -1623160, 324632, -52360,
    6545, -595, 35, -1
] := by
  change mulList [1, -1] (powList [1, -1] 34) = _
  rw [powerOneSub34]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub36 : powList [1, -1] 36 =
    [
    1, -36, 630, -7140, 58905, -376992, 1947792, -8347680,
    30260340, -94143280, 254186856, -600805296, 1251677700, -2310789600, 3796297200, -5567902560,
    7307872110, -8597496600, 9075135300, -8597496600, 7307872110, -5567902560, 3796297200, -2310789600,
    1251677700, -600805296, 254186856, -94143280, 30260340, -8347680, 1947792, -376992,
    58905, -7140, 630, -36, 1
] := by
  change mulList [1, -1] (powList [1, -1] 35) = _
  rw [powerOneSub35]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub37 : powList [1, -1] 37 =
    [
    1, -37, 666, -7770, 66045, -435897, 2324784, -10295472,
    38608020, -124403620, 348330136, -854992152, 1852482996, -3562467300, 6107086800, -9364199760,
    12875774670, -15905368710, 17672631900, -17672631900, 15905368710, -12875774670, 9364199760, -6107086800,
    3562467300, -1852482996, 854992152, -348330136, 124403620, -38608020, 10295472, -2324784,
    435897, -66045, 7770, -666, 37, -1
] := by
  change mulList [1, -1] (powList [1, -1] 36) = _
  rw [powerOneSub36]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub38 : powList [1, -1] 38 =
    [
    1, -38, 703, -8436, 73815, -501942, 2760681, -12620256,
    48903492, -163011640, 472733756, -1203322288, 2707475148, -5414950296, 9669554100, -15471286560,
    22239974430, -28781143380, 33578000610, -35345263800, 33578000610, -28781143380, 22239974430, -15471286560,
    9669554100, -5414950296, 2707475148, -1203322288, 472733756, -163011640, 48903492, -12620256,
    2760681, -501942, 73815, -8436, 703, -38, 1
] := by
  change mulList [1, -1] (powList [1, -1] 37) = _
  rw [powerOneSub37]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub39 : powList [1, -1] 39 =
    [
    1, -39, 741, -9139, 82251, -575757, 3262623, -15380937,
    61523748, -211915132, 635745396, -1676056044, 3910797436, -8122425444, 15084504396, -25140840660,
    37711260990, -51021117810, 62359143990, -68923264410, 68923264410, -62359143990, 51021117810, -37711260990,
    25140840660, -15084504396, 8122425444, -3910797436, 1676056044, -635745396, 211915132, -61523748,
    15380937, -3262623, 575757, -82251, 9139, -741, 39, -1
] := by
  change mulList [1, -1] (powList [1, -1] 38) = _
  rw [powerOneSub38]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub40 : powList [1, -1] 40 =
    [
    1, -40, 780, -9880, 91390, -658008, 3838380, -18643560,
    76904685, -273438880, 847660528, -2311801440, 5586853480, -12033222880, 23206929840, -40225345056,
    62852101650, -88732378800, 113380261800, -131282408400, 137846528820, -131282408400, 113380261800, -88732378800,
    62852101650, -40225345056, 23206929840, -12033222880, 5586853480, -2311801440, 847660528, -273438880,
    76904685, -18643560, 3838380, -658008, 91390, -9880, 780, -40,
    1
] := by
  change mulList [1, -1] (powList [1, -1] 39) = _
  rw [powerOneSub39]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub41 : powList [1, -1] 41 =
    [
    1, -41, 820, -10660, 101270, -749398, 4496388, -22481940,
    95548245, -350343565, 1121099408, -3159461968, 7898654920, -17620076360, 35240152720, -63432274896,
    103077446706, -151584480450, 202112640600, -244662670200, 269128937220, -269128937220, 244662670200, -202112640600,
    151584480450, -103077446706, 63432274896, -35240152720, 17620076360, -7898654920, 3159461968, -1121099408,
    350343565, -95548245, 22481940, -4496388, 749398, -101270, 10660, -820,
    41, -1
] := by
  change mulList [1, -1] (powList [1, -1] 40) = _
  rw [powerOneSub40]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub42 : powList [1, -1] 42 =
    [
    1, -42, 861, -11480, 111930, -850668, 5245786, -26978328,
    118030185, -445891810, 1471442973, -4280561376, 11058116888, -25518731280, 52860229080, -98672427616,
    166509721602, -254661927156, 353697121050, -446775310800, 513791607420, -538257874440, 513791607420, -446775310800,
    353697121050, -254661927156, 166509721602, -98672427616, 52860229080, -25518731280, 11058116888, -4280561376,
    1471442973, -445891810, 118030185, -26978328, 5245786, -850668, 111930, -11480,
    861, -42, 1
] := by
  change mulList [1, -1] (powList [1, -1] 41) = _
  rw [powerOneSub41]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub43 : powList [1, -1] 43 =
    [
    1, -43, 903, -12341, 123410, -962598, 6096454, -32224114,
    145008513, -563921995, 1917334783, -5752004349, 15338678264, -36576848168, 78378960360, -151532656696,
    265182149218, -421171648758, 608359048206, -800472431850, 960566918220, -1052049481860, 1052049481860, -960566918220,
    800472431850, -608359048206, 421171648758, -265182149218, 151532656696, -78378960360, 36576848168, -15338678264,
    5752004349, -1917334783, 563921995, -145008513, 32224114, -6096454, 962598, -123410,
    12341, -903, 43, -1
] := by
  change mulList [1, -1] (powList [1, -1] 42) = _
  rw [powerOneSub42]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub44 : powList [1, -1] 44 =
    [
    1, -44, 946, -13244, 135751, -1086008, 7059052, -38320568,
    177232627, -708930508, 2481256778, -7669339132, 21090682613, -51915526432, 114955808528, -229911617056,
    416714805914, -686353797976, 1029530696964, -1408831480056, 1761039350070, -2012616400080, 2104098963720, -2012616400080,
    1761039350070, -1408831480056, 1029530696964, -686353797976, 416714805914, -229911617056, 114955808528, -51915526432,
    21090682613, -7669339132, 2481256778, -708930508, 177232627, -38320568, 7059052, -1086008,
    135751, -13244, 946, -44, 1
] := by
  change mulList [1, -1] (powList [1, -1] 43) = _
  rw [powerOneSub43]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub45 : powList [1, -1] 45 =
    [
    1, -45, 990, -14190, 148995, -1221759, 8145060, -45379620,
    215553195, -886163135, 3190187286, -10150595910, 28760021745, -73006209045, 166871334960, -344867425584,
    646626422970, -1103068603890, 1715884494940, -2438362177020, 3169870830126, -3773655750150, 4116715363800, -4116715363800,
    3773655750150, -3169870830126, 2438362177020, -1715884494940, 1103068603890, -646626422970, 344867425584, -166871334960,
    73006209045, -28760021745, 10150595910, -3190187286, 886163135, -215553195, 45379620, -8145060,
    1221759, -148995, 14190, -990, 45, -1
] := by
  change mulList [1, -1] (powList [1, -1] 44) = _
  rw [powerOneSub44]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub46 : powList [1, -1] 46 =
    [
    1, -46, 1035, -15180, 163185, -1370754, 9366819, -53524680,
    260932815, -1101716330, 4076350421, -13340783196, 38910617655, -101766230790, 239877544005, -511738760544,
    991493848554, -1749695026860, 2818953098830, -4154246671960, 5608233007146, -6943526580276, 7890371113950, -8233430727600,
    7890371113950, -6943526580276, 5608233007146, -4154246671960, 2818953098830, -1749695026860, 991493848554, -511738760544,
    239877544005, -101766230790, 38910617655, -13340783196, 4076350421, -1101716330, 260932815, -53524680,
    9366819, -1370754, 163185, -15180, 1035, -46, 1
] := by
  change mulList [1, -1] (powList [1, -1] 45) = _
  rw [powerOneSub45]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub47 : powList [1, -1] 47 =
    [
    1, -47, 1081, -16215, 178365, -1533939, 10737573, -62891499,
    314457495, -1362649145, 5178066751, -17417133617, 52251400851, -140676848445, 341643774795, -751616304549,
    1503232609098, -2741188875414, 4568648125690, -6973199770790, 9762479679106, -12551759587422, 14833897694226, -16123801841550,
    16123801841550, -14833897694226, 12551759587422, -9762479679106, 6973199770790, -4568648125690, 2741188875414, -1503232609098,
    751616304549, -341643774795, 140676848445, -52251400851, 17417133617, -5178066751, 1362649145, -314457495,
    62891499, -10737573, 1533939, -178365, 16215, -1081, 47, -1
] := by
  change mulList [1, -1] (powList [1, -1] 46) = _
  rw [powerOneSub46]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub48 : powList [1, -1] 48 =
    [
    1, -48, 1128, -17296, 194580, -1712304, 12271512, -73629072,
    377348994, -1677106640, 6540715896, -22595200368, 69668534468, -192928249296, 482320623240, -1093260079344,
    2254848913647, -4244421484512, 7309837001104, -11541847896480, 16735679449896, -22314239266528, 27385657281648, -30957699535776,
    32247603683100, -30957699535776, 27385657281648, -22314239266528, 16735679449896, -11541847896480, 7309837001104, -4244421484512,
    2254848913647, -1093260079344, 482320623240, -192928249296, 69668534468, -22595200368, 6540715896, -1677106640,
    377348994, -73629072, 12271512, -1712304, 194580, -17296, 1128, -48,
    1
] := by
  change mulList [1, -1] (powList [1, -1] 47) = _
  rw [powerOneSub47]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub49 : powList [1, -1] 49 =
    [
    1, -49, 1176, -18424, 211876, -1906884, 13983816, -85900584,
    450978066, -2054455634, 8217822536, -29135916264, 92263734836, -262596783764, 675248872536, -1575580702584,
    3348108992991, -6499270398159, 11554258485616, -18851684897584, 28277527346376, -39049918716424, 49699896548176, -58343356817424,
    63205303218876, -63205303218876, 58343356817424, -49699896548176, 39049918716424, -28277527346376, 18851684897584, -11554258485616,
    6499270398159, -3348108992991, 1575580702584, -675248872536, 262596783764, -92263734836, 29135916264, -8217822536,
    2054455634, -450978066, 85900584, -13983816, 1906884, -211876, 18424, -1176,
    49, -1
] := by
  change mulList [1, -1] (powList [1, -1] 48) = _
  rw [powerOneSub48]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub50 : powList [1, -1] 50 =
    [
    1, -50, 1225, -19600, 230300, -2118760, 15890700, -99884400,
    536878650, -2505433700, 10272278170, -37353738800, 121399651100, -354860518600, 937845656300, -2250829575120,
    4923689695575, -9847379391150, 18053528883775, -30405943383200, 47129212243960, -67327446062800, 88749815264600, -108043253365600,
    121548660036300, -126410606437752, 121548660036300, -108043253365600, 88749815264600, -67327446062800, 47129212243960, -30405943383200,
    18053528883775, -9847379391150, 4923689695575, -2250829575120, 937845656300, -354860518600, 121399651100, -37353738800,
    10272278170, -2505433700, 536878650, -99884400, 15890700, -2118760, 230300, -19600,
    1225, -50, 1
] := by
  change mulList [1, -1] (powList [1, -1] 49) = _
  rw [powerOneSub49]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub51 : powList [1, -1] 51 =
    [
    1, -51, 1275, -20825, 249900, -2349060, 18009460, -115775100,
    636763050, -3042312350, 12777711870, -47626016970, 158753389900, -476260169700, 1292706174900, -3188675231420,
    7174519270695, -14771069086725, 27900908274925, -48459472266975, 77535155627160, -114456658306760, 156077261327400, -196793068630200,
    229591913401900, -247959266474052, 247959266474052, -229591913401900, 196793068630200, -156077261327400, 114456658306760, -77535155627160,
    48459472266975, -27900908274925, 14771069086725, -7174519270695, 3188675231420, -1292706174900, 476260169700, -158753389900,
    47626016970, -12777711870, 3042312350, -636763050, 115775100, -18009460, 2349060, -249900,
    20825, -1275, 51, -1
] := by
  change mulList [1, -1] (powList [1, -1] 50) = _
  rw [powerOneSub50]
  norm_num [mulList,scaleList,addList]

theorem powerOneSub52 : powList [1, -1] 52 =
    [
    1, -52, 1326, -22100, 270725, -2598960, 20358520, -133784560,
    752538150, -3679075400, 15820024220, -60403728840, 206379406870, -635013559600, 1768966344600, -4481381406320,
    10363194502115, -21945588357420, 42671977361650, -76360380541900, 125994627894135, -191991813933920, 270533919634160, -352870329957600,
    426384982032100, -477551179875952, 495918532948104, -477551179875952, 426384982032100, -352870329957600, 270533919634160, -191991813933920,
    125994627894135, -76360380541900, 42671977361650, -21945588357420, 10363194502115, -4481381406320, 1768966344600, -635013559600,
    206379406870, -60403728840, 15820024220, -3679075400, 752538150, -133784560, 20358520, -2598960,
    270725, -22100, 1326, -52, 1
] := by
  change mulList [1, -1] (powList [1, -1] 51) = _
  rw [powerOneSub51]
  norm_num [mulList,scaleList,addList]

theorem basis00 : bernsteinList 52 0 =
    [
    1, -52, 1326, -22100, 270725, -2598960, 20358520, -133784560,
    752538150, -3679075400, 15820024220, -60403728840, 206379406870, -635013559600, 1768966344600, -4481381406320,
    10363194502115, -21945588357420, 42671977361650, -76360380541900, 125994627894135, -191991813933920, 270533919634160, -352870329957600,
    426384982032100, -477551179875952, 495918532948104, -477551179875952, 426384982032100, -352870329957600, 270533919634160, -191991813933920,
    125994627894135, -76360380541900, 42671977361650, -21945588357420, 10363194502115, -4481381406320, 1768966344600, -635013559600,
    206379406870, -60403728840, 15820024220, -3679075400, 752538150, -133784560, 20358520, -2598960,
    270725, -22100, 1326, -52, 1
] := by
  unfold bernsteinList
  rw [choose00,powerX00,powerOneSub52]
  norm_num [scaleList,mulList,addList]

theorem basis01 : bernsteinList 52 1 =
    [
    0, 52, -2652, 66300, -1082900, 12994800, -122151120, 936491920,
    -6020305200, 33111678600, -158200242200, 664441017240, -2476552882440, 8255176274800, -24765528824400, 67220721094800,
    -165811112033840, 373075002076140, -768095592509700, 1450847230296100, -2519892557882700, 4031828092612320, -5951746231951520, 8116017589024800,
    -10233239568770400, 11938779496898800, -12893881856650704, 12893881856650704, -11938779496898800, 10233239568770400, -8116017589024800, 5951746231951520,
    -4031828092612320, 2519892557882700, -1450847230296100, 768095592509700, -373075002076140, 165811112033840, -67220721094800, 24765528824400,
    -8255176274800, 2476552882440, -664441017240, 158200242200, -33111678600, 6020305200, -936491920, 122151120,
    -12994800, 1082900, -66300, 2652, -52
] := by
  unfold bernsteinList
  rw [choose01,powerX01,powerOneSub51]
  norm_num [scaleList,mulList,addList]

theorem basis02 : bernsteinList 52 2 =
    [
    0, 0, 1326, -66300, 1624350, -25989600, 305377800, -2809475760,
    21071068200, -132446714400, 711901089900, -3322205086200, 13621040853420, -49531057648800, 160975937358600, -470545047663600,
    1243583340253800, -2984600016609120, 6528812536332450, -13057625072664900, 23938979299885650, -40318280926123200, 62493335435490960, -89276193479272800,
    117682255040859600, -143265353962785600, 161173523208133800, -167620464136459152, 161173523208133800, -143265353962785600, 117682255040859600, -89276193479272800,
    62493335435490960, -40318280926123200, 23938979299885650, -13057625072664900, 6528812536332450, -2984600016609120, 1243583340253800, -470545047663600,
    160975937358600, -49531057648800, 13621040853420, -3322205086200, 711901089900, -132446714400, 21071068200, -2809475760,
    305377800, -25989600, 1624350, -66300, 1326
] := by
  unfold bernsteinList
  rw [choose02,powerX02,powerOneSub50]
  norm_num [scaleList,mulList,addList]

theorem basis03 : bernsteinList 52 3 =
    [
    0, 0, 0, 22100, -1082900, 25989600, -407170400, 4682459600,
    -42142136400, 309042333600, -1898402906400, 9966615258600, -45403469511400, 181613878045600, -643903749434400, 2039028539875600,
    -5803388921184400, 14923000083045600, -34820333527106400, 73993208745101100, -143633875799313900, 255349112532113600, -416622236236606400, 624933354354909600,
    -863003203632970400, 1098367713714689600, -1289388185665070400, 1396837201137159600, -1396837201137159600, 1289388185665070400, -1098367713714689600, 863003203632970400,
    -624933354354909600, 416622236236606400, -255349112532113600, 143633875799313900, -73993208745101100, 34820333527106400, -14923000083045600, 5803388921184400,
    -2039028539875600, 643903749434400, -181613878045600, 45403469511400, -9966615258600, 1898402906400, -309042333600, 42142136400,
    -4682459600, 407170400, -25989600, 1082900, -22100
] := by
  unfold bernsteinList
  rw [choose03,powerX03,powerOneSub49]
  norm_num [scaleList,mulList,addList]

theorem basis04 : bernsteinList 52 4 =
    [
    0, 0, 0, 0, 270725, -12994800, 305377800, -4682459600,
    52677670500, -463563500400, 3322205086200, -19933230517200, 102157806400650, -454034695114000, 1770735310944600, -6117085619626800,
    18861013993849300, -52230500290659600, 130576250726649000, -295972834980404400, 610443972147084075, -1149071006394511200, 1978955622123880400, -3124666771774548000,
    4530766819073094600, -6041022425430792800, 7413982067574154800, -8381023206822957600, 8730232507107247500, -8381023206822957600, 7413982067574154800, -6041022425430792800,
    4530766819073094600, -3124666771774548000, 1978955622123880400, -1149071006394511200, 610443972147084075, -295972834980404400, 130576250726649000, -52230500290659600,
    18861013993849300, -6117085619626800, 1770735310944600, -454034695114000, 102157806400650, -19933230517200, 3322205086200, -463563500400,
    52677670500, -4682459600, 305377800, -12994800, 270725
] := by
  unfold bernsteinList
  rw [choose04,powerX04,powerOneSub48]
  norm_num [scaleList,mulList,addList]

theorem basis05 : bernsteinList 52 5 =
    [
    0, 0, 0, 0, 0, 2598960, -122151120, 2809475760,
    -42142136400, 463563500400, -3986646103440, 27906522724080, -163452490241040, 817262451205200, -3541470621889200, 13457588363178960,
    -45266433585238320, 135799300755714960, -365613502034617200, 887918504941213200, -1953420710870669040, 3906841421741338080, -7124240239645969440, 11873733732743282400,
    -18123067276292378400, 25372294186809329760, -32621521097326281120, 38552706751385604960, -41905116034114788000, 41905116034114788000, -38552706751385604960, 32621521097326281120,
    -25372294186809329760, 18123067276292378400, -11873733732743282400, 7124240239645969440, -3906841421741338080, 1953420710870669040, -887918504941213200, 365613502034617200,
    -135799300755714960, 45266433585238320, -13457588363178960, 3541470621889200, -817262451205200, 163452490241040, -27906522724080, 3986646103440,
    -463563500400, 42142136400, -2809475760, 122151120, -2598960
] := by
  unfold bernsteinList
  rw [choose05,powerX05,powerOneSub47]
  norm_num [scaleList,mulList,addList]

theorem basis06 : bernsteinList 52 6 =
    [
    0, 0, 0, 0, 0, 0, 20358520, -936491920,
    21071068200, -309042333600, 3322205086200, -27906522724080, 190694571947880, -1089683268273600, 5312205932833800, -22429313938631600,
    82988461572936920, -271598601511429920, 792162587741670600, -2071809844862830800, 4883551777176672600, -10418243791310234880, 20185347345663580080, -35621201198229847200,
    57389713041592531600, -84574313956031099200, 114175323840641983920, -141359924755080551520, 160636278130773354000, -167620464136459152000, 160636278130773354000, -141359924755080551520,
    114175323840641983920, -84574313956031099200, 57389713041592531600, -35621201198229847200, 20185347345663580080, -10418243791310234880, 4883551777176672600, -2071809844862830800,
    792162587741670600, -271598601511429920, 82988461572936920, -22429313938631600, 5312205932833800, -1089683268273600, 190694571947880, -27906522724080,
    3322205086200, -309042333600, 21071068200, -936491920, 20358520
] := by
  unfold bernsteinList
  rw [choose06,powerX06,powerOneSub46]
  norm_num [scaleList,mulList,addList]

theorem basis07 : bernsteinList 52 7 =
    [
    0, 0, 0, 0, 0, 0, 0, 133784560,
    -6020305200, 132446714400, -1898402906400, 19933230517200, -163452490241040, 1089683268273600, -6071092494667200, 28837689349669200,
    -118554945104195600, 426797802375104160, -1357993007557149600, 3847646854745257200, -9767103554353345200, 22324808124236217600, -46137936790088183040, 86508631481415343200,
    -147573547821237938400, 229558852166370126400, -326215210973262811200, 424079774265241654560, -504856874125287684000, 550752953591222928000, -550752953591222928000, 504856874125287684000,
    -424079774265241654560, 326215210973262811200, -229558852166370126400, 147573547821237938400, -86508631481415343200, 46137936790088183040, -22324808124236217600, 9767103554353345200,
    -3847646854745257200, 1357993007557149600, -426797802375104160, 118554945104195600, -28837689349669200, 6071092494667200, -1089683268273600, 163452490241040,
    -19933230517200, 1898402906400, -132446714400, 6020305200, -133784560
] := by
  unfold bernsteinList
  rw [choose07,powerX07,powerOneSub45]
  norm_num [scaleList,mulList,addList]

theorem basis08 : bernsteinList 52 8 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    752538150, -33111678600, 711901089900, -9966615258600, 102157806400650, -817262451205200, 5312205932833800, -28837689349669200,
    133374313242220050, -533497252968880200, 1867240385391080700, -5771470282117885800, 15871543275824185950, -39068414217413380800, 86508631481415343200, -173017262962830686400,
    313593789120130619100, -516507417374332784400, 774761126061499176600, -1060199435663104136400, 1325249294578880170500, -1514570622375863052000, 1583414741574765918000, -1514570622375863052000,
    1325249294578880170500, -1060199435663104136400, 774761126061499176600, -516507417374332784400, 313593789120130619100, -173017262962830686400, 86508631481415343200, -39068414217413380800,
    15871543275824185950, -5771470282117885800, 1867240385391080700, -533497252968880200, 133374313242220050, -28837689349669200, 5312205932833800, -817262451205200,
    102157806400650, -9966615258600, 711901089900, -33111678600, 752538150
] := by
  unfold bernsteinList
  rw [choose08,powerX08,powerOneSub44]
  norm_num [scaleList,mulList,addList]

theorem basis09 : bernsteinList 52 9 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 3679075400, -158200242200, 3322205086200, -45403469511400, 454034695114000, -3541470621889200, 22429313938631600,
    -118554945104195600, 533497252968880200, -2074711539323423000, 7054019233699638200, -21162057701098914600, 56432153869597105600, -134568982304423867200, 288362104938051144000,
    -557500069546898878400, 975625121707073037200, -1549522252122998353200, 2238198808622108732400, -2944998432397511490000, 3533998118877013788000, -3870569368293872244000, 3870569368293872244000,
    -3533998118877013788000, 2944998432397511490000, -2238198808622108732400, 1549522252122998353200, -975625121707073037200, 557500069546898878400, -288362104938051144000, 134568982304423867200,
    -56432153869597105600, 21162057701098914600, -7054019233699638200, 2074711539323423000, -533497252968880200, 118554945104195600, -22429313938631600, 3541470621889200,
    -454034695114000, 45403469511400, -3322205086200, 158200242200, -3679075400
] := by
  unfold bernsteinList
  rw [choose09,powerX09,powerOneSub43]
  norm_num [scaleList,mulList,addList]

theorem basis10 : bernsteinList 52 10 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 15820024220, -664441017240, 13621040853420, -181613878045600, 1770735310944600, -13457588363178960,
    82988461572936920, -426797802375104160, 1867240385391080700, -7054019233699638200, 23278263471208806060, -67718584643516526720, 174939676995751027360, -403706946913271601600,
    836250104320348317600, -1561000194731316859520, 2634187828609097200440, -4028757855519795718320, 5595497021555271831000, -7067996237754027576000, 8128195673417131712400, -8515252610246518936800,
    8128195673417131712400, -7067996237754027576000, 5595497021555271831000, -4028757855519795718320, 2634187828609097200440, -1561000194731316859520, 836250104320348317600, -403706946913271601600,
    174939676995751027360, -67718584643516526720, 23278263471208806060, -7054019233699638200, 1867240385391080700, -426797802375104160, 82988461572936920, -13457588363178960,
    1770735310944600, -181613878045600, 13621040853420, -664441017240, 15820024220
] := by
  unfold bernsteinList
  rw [choose10,powerX10,powerOneSub42]
  norm_num [scaleList,mulList,addList]

theorem basis11 : bernsteinList 52 11 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 60403728840, -2476552882440, 49531057648800, -643903749434400, 6117085619626800,
    -45266433585238320, 271598601511429920, -1357993007557149600, 5771470282117885800, -21162057701098914600, 67718584643516526720, -190843283995364757120, 477108209988411892800,
    -1064318314589534222400, 2128636629179068444800, -3831545932522323200640, 6226262140348775201040, -9156267853454081178000, 12208357137938774904000, -14778537588031148568000, 16256391346834263424800,
    -16256391346834263424800, 14778537588031148568000, -12208357137938774904000, 9156267853454081178000, -6226262140348775201040, 3831545932522323200640, -2128636629179068444800, 1064318314589534222400,
    -477108209988411892800, 190843283995364757120, -67718584643516526720, 21162057701098914600, -5771470282117885800, 1357993007557149600, -271598601511429920, 45266433585238320,
    -6117085619626800, 643903749434400, -49531057648800, 2476552882440, -60403728840
] := by
  unfold bernsteinList
  rw [choose11,powerX11,powerOneSub41]
  norm_num [scaleList,mulList,addList]

theorem basis12 : bernsteinList 52 12 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 206379406870, -8255176274800, 160975937358600, -2039028539875600,
    18861013993849300, -135799300755714960, 792162587741670600, -3847646854745257200, 15871543275824185950, -56432153869597105600, 174939676995751027360, -477108209988411892800,
    1153011507471995407600, -2483409400708913185600, 4789432415652904000800, -8301682853798366934720, 12971379459059948335500, -18312535706908162356000, 23399351181049318566000, -27093985578057105708000,
    28448684856959960993400, -27093985578057105708000, 23399351181049318566000, -18312535706908162356000, 12971379459059948335500, -8301682853798366934720, 4789432415652904000800, -2483409400708913185600,
    1153011507471995407600, -477108209988411892800, 174939676995751027360, -56432153869597105600, 15871543275824185950, -3847646854745257200, 792162587741670600, -135799300755714960,
    18861013993849300, -2039028539875600, 160975937358600, -8255176274800, 206379406870
] := by
  unfold bernsteinList
  rw [choose12,powerX12,powerOneSub40]
  norm_num [scaleList,mulList,addList]

theorem basis13 : bernsteinList 52 13 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 635013559600, -24765528824400, 470545047663600,
    -5803388921184400, 52230500290659600, -365613502034617200, 2071809844862830800, -9767103554353345200, 39068414217413380800, -134568982304423867200, 403706946913271601600,
    -1064318314589534222400, 2483409400708913185600, -5157850293780050462400, 9578864831305808001600, -15964774718843013336000, 23947162078264520004000, -32399101635299056476000, 39598901998698846804000,
    -43767207472246093836000, 43767207472246093836000, -39598901998698846804000, 32399101635299056476000, -23947162078264520004000, 15964774718843013336000, -9578864831305808001600, 5157850293780050462400,
    -2483409400708913185600, 1064318314589534222400, -403706946913271601600, 134568982304423867200, -39068414217413380800, 9767103554353345200, -2071809844862830800, 365613502034617200,
    -52230500290659600, 5803388921184400, -470545047663600, 24765528824400, -635013559600
] := by
  unfold bernsteinList
  rw [choose13,powerX13,powerOneSub39]
  norm_num [scaleList,mulList,addList]

theorem basis14 : bernsteinList 52 14 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1768966344600, -67220721094800,
    1243583340253800, -14923000083045600, 130576250726649000, -887918504941213200, 4883551777176672600, -22324808124236217600, 86508631481415343200, -288362104938051144000,
    836250104320348317600, -2128636629179068444800, 4789432415652904000800, -9578864831305808001600, 17105115770188942860000, -27368185232302308576000, 39341766271434568578000, -50912873998327088748000,
    59398352998048270206000, -62524582103208705480000, 59398352998048270206000, -50912873998327088748000, 39341766271434568578000, -27368185232302308576000, 17105115770188942860000, -9578864831305808001600,
    4789432415652904000800, -2128636629179068444800, 836250104320348317600, -288362104938051144000, 86508631481415343200, -22324808124236217600, 4883551777176672600, -887918504941213200,
    130576250726649000, -14923000083045600, 1243583340253800, -67220721094800, 1768966344600
] := by
  unfold bernsteinList
  rw [choose14,powerX14,powerOneSub38]
  norm_num [scaleList,mulList,addList]

theorem basis15 : bernsteinList 52 15 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 4481381406320,
    -165811112033840, 2984600016609120, -34820333527106400, 295972834980404400, -1953420710870669040, 10418243791310234880, -46137936790088183040, 173017262962830686400,
    -557500069546898878400, 1561000194731316859520, -3831545932522323200640, 8301682853798366934720, -15964774718843013336000, 27368185232302308576000, -41964550689530206483200, 57701257198104033914400,
    -71278023597657924247200, 79197803997397693608000, -79197803997397693608000, 71278023597657924247200, -57701257198104033914400, 41964550689530206483200, -27368185232302308576000, 15964774718843013336000,
    -8301682853798366934720, 3831545932522323200640, -1561000194731316859520, 557500069546898878400, -173017262962830686400, 46137936790088183040, -10418243791310234880, 1953420710870669040,
    -295972834980404400, 34820333527106400, -2984600016609120, 165811112033840, -4481381406320
] := by
  unfold bernsteinList
  rw [choose15,powerX15,powerOneSub37]
  norm_num [scaleList,mulList,addList]

theorem basis16 : bernsteinList 52 16 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    10363194502115, -373075002076140, 6528812536332450, -73993208745101100, 610443972147084075, -3906841421741338080, 20185347345663580080, -86508631481415343200,
    313593789120130619100, -975625121707073037200, 2634187828609097200440, -6226262140348775201040, 12971379459059948335500, -23947162078264520004000, 39341766271434568578000, -57701257198104033914400,
    75732900072511544512650, -89097529497072405309000, 94047392246909761159500, -89097529497072405309000, 75732900072511544512650, -57701257198104033914400, 39341766271434568578000, -23947162078264520004000,
    12971379459059948335500, -6226262140348775201040, 2634187828609097200440, -975625121707073037200, 313593789120130619100, -86508631481415343200, 20185347345663580080, -3906841421741338080,
    610443972147084075, -73993208745101100, 6528812536332450, -373075002076140, 10363194502115
] := by
  unfold bernsteinList
  rw [choose16,powerX16,powerOneSub36]
  norm_num [scaleList,mulList,addList]

theorem basis17 : bernsteinList 52 17 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 21945588357420, -768095592509700, 13057625072664900, -143633875799313900, 1149071006394511200, -7124240239645969440, 35621201198229847200,
    -147573547821237938400, 516507417374332784400, -1549522252122998353200, 4028757855519795718320, -9156267853454081178000, 18312535706908162356000, -32399101635299056476000, 50912873998327088748000,
    -71278023597657924247200, 89097529497072405309000, -99579591790845629463000, 99579591790845629463000, -89097529497072405309000, 71278023597657924247200, -50912873998327088748000, 32399101635299056476000,
    -18312535706908162356000, 9156267853454081178000, -4028757855519795718320, 1549522252122998353200, -516507417374332784400, 147573547821237938400, -35621201198229847200, 7124240239645969440,
    -1149071006394511200, 143633875799313900, -13057625072664900, 768095592509700, -21945588357420
] := by
  unfold bernsteinList
  rw [choose17,powerX17,powerOneSub35]
  norm_num [scaleList,mulList,addList]

theorem basis18 : bernsteinList 52 18 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 42671977361650, -1450847230296100, 23938979299885650, -255349112532113600, 1978955622123880400, -11873733732743282400,
    57389713041592531600, -229558852166370126400, 774761126061499176600, -2238198808622108732400, 5595497021555271831000, -12208357137938774904000, 23399351181049318566000, -39598901998698846804000,
    59398352998048270206000, -79197803997397693608000, 94047392246909761159500, -99579591790845629463000, 94047392246909761159500, -79197803997397693608000, 59398352998048270206000, -39598901998698846804000,
    23399351181049318566000, -12208357137938774904000, 5595497021555271831000, -2238198808622108732400, 774761126061499176600, -229558852166370126400, 57389713041592531600, -11873733732743282400,
    1978955622123880400, -255349112532113600, 23938979299885650, -1450847230296100, 42671977361650
] := by
  unfold bernsteinList
  rw [choose18,powerX18,powerOneSub34]
  norm_num [scaleList,mulList,addList]

theorem basis19 : bernsteinList 52 19 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 76360380541900, -2519892557882700, 40318280926123200, -416622236236606400, 3124666771774548000,
    -18123067276292378400, 84574313956031099200, -326215210973262811200, 1060199435663104136400, -2944998432397511490000, 7067996237754027576000, -14778537588031148568000, 27093985578057105708000,
    -43767207472246093836000, 62524582103208705480000, -79197803997397693608000, 89097529497072405309000, -89097529497072405309000, 79197803997397693608000, -62524582103208705480000, 43767207472246093836000,
    -27093985578057105708000, 14778537588031148568000, -7067996237754027576000, 2944998432397511490000, -1060199435663104136400, 326215210973262811200, -84574313956031099200, 18123067276292378400,
    -3124666771774548000, 416622236236606400, -40318280926123200, 2519892557882700, -76360380541900
] := by
  unfold bernsteinList
  rw [choose19,powerX19,powerOneSub33]
  norm_num [scaleList,mulList,addList]

theorem basis20 : bernsteinList 52 20 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 125994627894135, -4031828092612320, 62493335435490960, -624933354354909600,
    4530766819073094600, -25372294186809329760, 114175323840641983920, -424079774265241654560, 1325249294578880170500, -3533998118877013788000, 8128195673417131712400, -16256391346834263424800,
    28448684856959960993400, -43767207472246093836000, 59398352998048270206000, -71278023597657924247200, 75732900072511544512650, -71278023597657924247200, 59398352998048270206000, -43767207472246093836000,
    28448684856959960993400, -16256391346834263424800, 8128195673417131712400, -3533998118877013788000, 1325249294578880170500, -424079774265241654560, 114175323840641983920, -25372294186809329760,
    4530766819073094600, -624933354354909600, 62493335435490960, -4031828092612320, 125994627894135
] := by
  unfold bernsteinList
  rw [choose20,powerX20,powerOneSub32]
  norm_num [scaleList,mulList,addList]

theorem basis21 : bernsteinList 52 21 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 191991813933920, -5951746231951520, 89276193479272800,
    -863003203632970400, 6041022425430792800, -32621521097326281120, 141359924755080551520, -504856874125287684000, 1514570622375863052000, -3870569368293872244000, 8515252610246518936800,
    -16256391346834263424800, 27093985578057105708000, -39598901998698846804000, 50912873998327088748000, -57701257198104033914400, 57701257198104033914400, -50912873998327088748000, 39598901998698846804000,
    -27093985578057105708000, 16256391346834263424800, -8515252610246518936800, 3870569368293872244000, -1514570622375863052000, 504856874125287684000, -141359924755080551520, 32621521097326281120,
    -6041022425430792800, 863003203632970400, -89276193479272800, 5951746231951520, -191991813933920
] := by
  unfold bernsteinList
  rw [choose21,powerX21,powerOneSub31]
  norm_num [scaleList,mulList,addList]

theorem basis22 : bernsteinList 52 22 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 270533919634160, -8116017589024800,
    117682255040859600, -1098367713714689600, 7413982067574154800, -38552706751385604960, 160636278130773354000, -550752953591222928000, 1583414741574765918000, -3870569368293872244000,
    8128195673417131712400, -14778537588031148568000, 23399351181049318566000, -32399101635299056476000, 39341766271434568578000, -41964550689530206483200, 39341766271434568578000, -32399101635299056476000,
    23399351181049318566000, -14778537588031148568000, 8128195673417131712400, -3870569368293872244000, 1583414741574765918000, -550752953591222928000, 160636278130773354000, -38552706751385604960,
    7413982067574154800, -1098367713714689600, 117682255040859600, -8116017589024800, 270533919634160
] := by
  unfold bernsteinList
  rw [choose22,powerX22,powerOneSub30]
  norm_num [scaleList,mulList,addList]

theorem basis23 : bernsteinList 52 23 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 352870329957600,
    -10233239568770400, 143265353962785600, -1289388185665070400, 8381023206822957600, -41905116034114788000, 167620464136459152000, -550752953591222928000, 1514570622375863052000,
    -3533998118877013788000, 7067996237754027576000, -12208357137938774904000, 18312535706908162356000, -23947162078264520004000, 27368185232302308576000, -27368185232302308576000, 23947162078264520004000,
    -18312535706908162356000, 12208357137938774904000, -7067996237754027576000, 3533998118877013788000, -1514570622375863052000, 550752953591222928000, -167620464136459152000, 41905116034114788000,
    -8381023206822957600, 1289388185665070400, -143265353962785600, 10233239568770400, -352870329957600
] := by
  unfold bernsteinList
  rw [choose23,powerX23,powerOneSub29]
  norm_num [scaleList,mulList,addList]

theorem basis24 : bernsteinList 52 24 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    426384982032100, -11938779496898800, 161173523208133800, -1396837201137159600, 8730232507107247500, -41905116034114788000, 160636278130773354000, -504856874125287684000,
    1325249294578880170500, -2944998432397511490000, 5595497021555271831000, -9156267853454081178000, 12971379459059948335500, -15964774718843013336000, 17105115770188942860000, -15964774718843013336000,
    12971379459059948335500, -9156267853454081178000, 5595497021555271831000, -2944998432397511490000, 1325249294578880170500, -504856874125287684000, 160636278130773354000, -41905116034114788000,
    8730232507107247500, -1396837201137159600, 161173523208133800, -11938779496898800, 426384982032100
] := by
  unfold bernsteinList
  rw [choose24,powerX24,powerOneSub28]
  norm_num [scaleList,mulList,addList]

theorem basis25 : bernsteinList 52 25 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 477551179875952, -12893881856650704, 167620464136459152, -1396837201137159600, 8381023206822957600, -38552706751385604960, 141359924755080551520,
    -424079774265241654560, 1060199435663104136400, -2238198808622108732400, 4028757855519795718320, -6226262140348775201040, 8301682853798366934720, -9578864831305808001600, 9578864831305808001600,
    -8301682853798366934720, 6226262140348775201040, -4028757855519795718320, 2238198808622108732400, -1060199435663104136400, 424079774265241654560, -141359924755080551520, 38552706751385604960,
    -8381023206822957600, 1396837201137159600, -167620464136459152, 12893881856650704, -477551179875952
] := by
  unfold bernsteinList
  rw [choose25,powerX25,powerOneSub27]
  norm_num [scaleList,mulList,addList]

theorem basis26 : bernsteinList 52 26 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 495918532948104, -12893881856650704, 161173523208133800, -1289388185665070400, 7413982067574154800, -32621521097326281120,
    114175323840641983920, -326215210973262811200, 774761126061499176600, -1549522252122998353200, 2634187828609097200440, -3831545932522323200640, 4789432415652904000800, -5157850293780050462400,
    4789432415652904000800, -3831545932522323200640, 2634187828609097200440, -1549522252122998353200, 774761126061499176600, -326215210973262811200, 114175323840641983920, -32621521097326281120,
    7413982067574154800, -1289388185665070400, 161173523208133800, -12893881856650704, 495918532948104
] := by
  unfold bernsteinList
  rw [choose26,powerX26,powerOneSub26]
  norm_num [scaleList,mulList,addList]

theorem basis27 : bernsteinList 52 27 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 477551179875952, -11938779496898800, 143265353962785600, -1098367713714689600, 6041022425430792800,
    -25372294186809329760, 84574313956031099200, -229558852166370126400, 516507417374332784400, -975625121707073037200, 1561000194731316859520, -2128636629179068444800, 2483409400708913185600,
    -2483409400708913185600, 2128636629179068444800, -1561000194731316859520, 975625121707073037200, -516507417374332784400, 229558852166370126400, -84574313956031099200, 25372294186809329760,
    -6041022425430792800, 1098367713714689600, -143265353962785600, 11938779496898800, -477551179875952
] := by
  unfold bernsteinList
  rw [choose27,powerX27,powerOneSub25]
  norm_num [scaleList,mulList,addList]

theorem basis28 : bernsteinList 52 28 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 426384982032100, -10233239568770400, 117682255040859600, -863003203632970400,
    4530766819073094600, -18123067276292378400, 57389713041592531600, -147573547821237938400, 313593789120130619100, -557500069546898878400, 836250104320348317600, -1064318314589534222400,
    1153011507471995407600, -1064318314589534222400, 836250104320348317600, -557500069546898878400, 313593789120130619100, -147573547821237938400, 57389713041592531600, -18123067276292378400,
    4530766819073094600, -863003203632970400, 117682255040859600, -10233239568770400, 426384982032100
] := by
  unfold bernsteinList
  rw [choose28,powerX28,powerOneSub24]
  norm_num [scaleList,mulList,addList]

theorem basis29 : bernsteinList 52 29 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 352870329957600, -8116017589024800, 89276193479272800,
    -624933354354909600, 3124666771774548000, -11873733732743282400, 35621201198229847200, -86508631481415343200, 173017262962830686400, -288362104938051144000, 403706946913271601600,
    -477108209988411892800, 477108209988411892800, -403706946913271601600, 288362104938051144000, -173017262962830686400, 86508631481415343200, -35621201198229847200, 11873733732743282400,
    -3124666771774548000, 624933354354909600, -89276193479272800, 8116017589024800, -352870329957600
] := by
  unfold bernsteinList
  rw [choose29,powerX29,powerOneSub23]
  norm_num [scaleList,mulList,addList]

theorem basis30 : bernsteinList 52 30 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 270533919634160, -5951746231951520,
    62493335435490960, -416622236236606400, 1978955622123880400, -7124240239645969440, 20185347345663580080, -46137936790088183040, 86508631481415343200, -134568982304423867200,
    174939676995751027360, -190843283995364757120, 174939676995751027360, -134568982304423867200, 86508631481415343200, -46137936790088183040, 20185347345663580080, -7124240239645969440,
    1978955622123880400, -416622236236606400, 62493335435490960, -5951746231951520, 270533919634160
] := by
  unfold bernsteinList
  rw [choose30,powerX30,powerOneSub22]
  norm_num [scaleList,mulList,addList]

theorem basis31 : bernsteinList 52 31 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 191991813933920,
    -4031828092612320, 40318280926123200, -255349112532113600, 1149071006394511200, -3906841421741338080, 10418243791310234880, -22324808124236217600, 39068414217413380800,
    -56432153869597105600, 67718584643516526720, -67718584643516526720, 56432153869597105600, -39068414217413380800, 22324808124236217600, -10418243791310234880, 3906841421741338080,
    -1149071006394511200, 255349112532113600, -40318280926123200, 4031828092612320, -191991813933920
] := by
  unfold bernsteinList
  rw [choose31,powerX31,powerOneSub21]
  norm_num [scaleList,mulList,addList]

theorem basis32 : bernsteinList 52 32 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    125994627894135, -2519892557882700, 23938979299885650, -143633875799313900, 610443972147084075, -1953420710870669040, 4883551777176672600, -9767103554353345200,
    15871543275824185950, -21162057701098914600, 23278263471208806060, -21162057701098914600, 15871543275824185950, -9767103554353345200, 4883551777176672600, -1953420710870669040,
    610443972147084075, -143633875799313900, 23938979299885650, -2519892557882700, 125994627894135
] := by
  unfold bernsteinList
  rw [choose32,powerX32,powerOneSub20]
  norm_num [scaleList,mulList,addList]

theorem basis33 : bernsteinList 52 33 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 76360380541900, -1450847230296100, 13057625072664900, -73993208745101100, 295972834980404400, -887918504941213200, 2071809844862830800,
    -3847646854745257200, 5771470282117885800, -7054019233699638200, 7054019233699638200, -5771470282117885800, 3847646854745257200, -2071809844862830800, 887918504941213200,
    -295972834980404400, 73993208745101100, -13057625072664900, 1450847230296100, -76360380541900
] := by
  unfold bernsteinList
  rw [choose33,powerX33,powerOneSub19]
  norm_num [scaleList,mulList,addList]

theorem basis34 : bernsteinList 52 34 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 42671977361650, -768095592509700, 6528812536332450, -34820333527106400, 130576250726649000, -365613502034617200,
    792162587741670600, -1357993007557149600, 1867240385391080700, -2074711539323423000, 1867240385391080700, -1357993007557149600, 792162587741670600, -365613502034617200,
    130576250726649000, -34820333527106400, 6528812536332450, -768095592509700, 42671977361650
] := by
  unfold bernsteinList
  rw [choose34,powerX34,powerOneSub18]
  norm_num [scaleList,mulList,addList]

theorem basis35 : bernsteinList 52 35 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 21945588357420, -373075002076140, 2984600016609120, -14923000083045600, 52230500290659600,
    -135799300755714960, 271598601511429920, -426797802375104160, 533497252968880200, -533497252968880200, 426797802375104160, -271598601511429920, 135799300755714960,
    -52230500290659600, 14923000083045600, -2984600016609120, 373075002076140, -21945588357420
] := by
  unfold bernsteinList
  rw [choose35,powerX35,powerOneSub17]
  norm_num [scaleList,mulList,addList]

theorem basis36 : bernsteinList 52 36 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 10363194502115, -165811112033840, 1243583340253800, -5803388921184400,
    18861013993849300, -45266433585238320, 82988461572936920, -118554945104195600, 133374313242220050, -118554945104195600, 82988461572936920, -45266433585238320,
    18861013993849300, -5803388921184400, 1243583340253800, -165811112033840, 10363194502115
] := by
  unfold bernsteinList
  rw [choose36,powerX36,powerOneSub16]
  norm_num [scaleList,mulList,addList]

theorem basis37 : bernsteinList 52 37 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 4481381406320, -67220721094800, 470545047663600,
    -2039028539875600, 6117085619626800, -13457588363178960, 22429313938631600, -28837689349669200, 28837689349669200, -22429313938631600, 13457588363178960,
    -6117085619626800, 2039028539875600, -470545047663600, 67220721094800, -4481381406320
] := by
  unfold bernsteinList
  rw [choose37,powerX37,powerOneSub15]
  norm_num [scaleList,mulList,addList]

theorem basis38 : bernsteinList 52 38 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1768966344600, -24765528824400,
    160975937358600, -643903749434400, 1770735310944600, -3541470621889200, 5312205932833800, -6071092494667200, 5312205932833800, -3541470621889200,
    1770735310944600, -643903749434400, 160975937358600, -24765528824400, 1768966344600
] := by
  unfold bernsteinList
  rw [choose38,powerX38,powerOneSub14]
  norm_num [scaleList,mulList,addList]

theorem basis39 : bernsteinList 52 39 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 635013559600,
    -8255176274800, 49531057648800, -181613878045600, 454034695114000, -817262451205200, 1089683268273600, -1089683268273600, 817262451205200,
    -454034695114000, 181613878045600, -49531057648800, 8255176274800, -635013559600
] := by
  unfold bernsteinList
  rw [choose39,powerX39,powerOneSub13]
  norm_num [scaleList,mulList,addList]

theorem basis40 : bernsteinList 52 40 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    206379406870, -2476552882440, 13621040853420, -45403469511400, 102157806400650, -163452490241040, 190694571947880, -163452490241040,
    102157806400650, -45403469511400, 13621040853420, -2476552882440, 206379406870
] := by
  unfold bernsteinList
  rw [choose40,powerX40,powerOneSub12]
  norm_num [scaleList,mulList,addList]

theorem basis41 : bernsteinList 52 41 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 60403728840, -664441017240, 3322205086200, -9966615258600, 19933230517200, -27906522724080, 27906522724080,
    -19933230517200, 9966615258600, -3322205086200, 664441017240, -60403728840
] := by
  unfold bernsteinList
  rw [choose41,powerX41,powerOneSub11]
  norm_num [scaleList,mulList,addList]

theorem basis42 : bernsteinList 52 42 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 15820024220, -158200242200, 711901089900, -1898402906400, 3322205086200, -3986646103440,
    3322205086200, -1898402906400, 711901089900, -158200242200, 15820024220
] := by
  unfold bernsteinList
  rw [choose42,powerX42,powerOneSub10]
  norm_num [scaleList,mulList,addList]

theorem basis43 : bernsteinList 52 43 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 3679075400, -33111678600, 132446714400, -309042333600, 463563500400,
    -463563500400, 309042333600, -132446714400, 33111678600, -3679075400
] := by
  unfold bernsteinList
  rw [choose43,powerX43,powerOneSub09]
  norm_num [scaleList,mulList,addList]

theorem basis44 : bernsteinList 52 44 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 752538150, -6020305200, 21071068200, -42142136400,
    52677670500, -42142136400, 21071068200, -6020305200, 752538150
] := by
  unfold bernsteinList
  rw [choose44,powerX44,powerOneSub08]
  norm_num [scaleList,mulList,addList]

theorem basis45 : bernsteinList 52 45 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 133784560, -936491920, 2809475760,
    -4682459600, 4682459600, -2809475760, 936491920, -133784560
] := by
  unfold bernsteinList
  rw [choose45,powerX45,powerOneSub07]
  norm_num [scaleList,mulList,addList]

theorem basis46 : bernsteinList 52 46 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 20358520, -122151120,
    305377800, -407170400, 305377800, -122151120, 20358520
] := by
  unfold bernsteinList
  rw [choose46,powerX46,powerOneSub06]
  norm_num [scaleList,mulList,addList]

theorem basis47 : bernsteinList 52 47 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 2598960,
    -12994800, 25989600, -25989600, 12994800, -2598960
] := by
  unfold bernsteinList
  rw [choose47,powerX47,powerOneSub05]
  norm_num [scaleList,mulList,addList]

theorem basis48 : bernsteinList 52 48 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    270725, -1082900, 1624350, -1082900, 270725
] := by
  unfold bernsteinList
  rw [choose48,powerX48,powerOneSub04]
  norm_num [scaleList,mulList,addList]

theorem basis49 : bernsteinList 52 49 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 22100, -66300, 66300, -22100
] := by
  unfold bernsteinList
  rw [choose49,powerX49,powerOneSub03]
  norm_num [scaleList,mulList,addList]

theorem basis50 : bernsteinList 52 50 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1326, -2652, 1326
] := by
  unfold bernsteinList
  rw [choose50,powerX50,powerOneSub02]
  norm_num [scaleList,mulList,addList]

theorem basis51 : bernsteinList 52 51 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 52, -52
] := by
  unfold bernsteinList
  rw [choose51,powerX51,powerOneSub01]
  norm_num [scaleList,mulList,addList]

theorem basis52 : bernsteinList 52 52 =
    [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1
] := by
  unfold bernsteinList
  rw [choose52,powerX52,powerOneSub00]
  norm_num [scaleList,mulList,addList]

attribute [local simp] basis00 basis01 basis02 basis03 basis04 basis05 basis06 basis07 basis08 basis09 basis10 basis11 basis12 basis13 basis14 basis15 basis16 basis17 basis18 basis19 basis20 basis21 basis22 basis23 basis24 basis25 basis26 basis27 basis28 basis29 basis30 basis31 basis32 basis33 basis34 basis35 basis36 basis37 basis38 basis39 basis40 basis41 basis42 basis43 basis44 basis45 basis46 basis47 basis48 basis49 basis50 basis51 basis52

end FiniteBernsteinResource
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
