-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation and strict compilation. Block15/16/19 data imports are planned predecessor modules.
-- Page starts: 32769 + 4096*20 + 64*p; full block indices 114689..118784.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block15Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block16Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block19Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block20Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

-- Serialize the independent kernel checks to stay within the compiler memory budget.
set_option Elab.async false

namespace ImbalancedChen.OriginalU2StoredNodeBlock20FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block20_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 114689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 0 (by omega) (by decide +kernel))

theorem block20_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 114753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 1 (by omega) (by decide +kernel))

theorem block20_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 114817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 2 (by omega) (by decide +kernel))

theorem block20_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 114881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 3 (by omega) (by decide +kernel))

theorem block20_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 114945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 4 (by omega) (by decide +kernel))

theorem block20_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 5 (by omega) (by decide +kernel))

theorem block20_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 6 (by omega) (by decide +kernel))

theorem block20_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 7 (by omega) (by decide +kernel))

theorem block20_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 8 (by omega) (by decide +kernel))

theorem block20_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 9 (by omega) (by decide +kernel))

theorem block20_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 10 (by omega) (by decide +kernel))

theorem block20_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 11 (by omega) (by decide +kernel))

theorem block20_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 12 (by omega) (by decide +kernel))

theorem block20_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 13 (by omega) (by decide +kernel))

theorem block20_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 14 (by omega) (by decide +kernel))

theorem block20_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 15 (by omega) (by decide +kernel))

theorem block20_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 16 (by omega) (by decide +kernel))

theorem block20_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 17 (by omega) (by decide +kernel))

theorem block20_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 18 (by omega) (by decide +kernel))

theorem block20_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 19 (by omega) (by decide +kernel))

theorem block20_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 115969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 20 (by omega) (by decide +kernel))

theorem block20_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 21 (by omega) (by decide +kernel))

theorem block20_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 22 (by omega) (by decide +kernel))

theorem block20_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 23 (by omega) (by decide +kernel))

theorem block20_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 24 (by omega) (by decide +kernel))

theorem block20_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 25 (by omega) (by decide +kernel))

theorem block20_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 26 (by omega) (by decide +kernel))

theorem block20_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 27 (by omega) (by decide +kernel))

theorem block20_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 28 (by omega) (by decide +kernel))

theorem block20_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 29 (by omega) (by decide +kernel))

theorem block20_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 30 (by omega) (by decide +kernel))

theorem block20_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 31 (by omega) (by decide +kernel))

theorem block20_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 32 (by omega) (by decide +kernel))

theorem block20_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 33 (by omega) (by decide +kernel))

theorem block20_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 34 (by omega) (by decide +kernel))

theorem block20_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 35 (by omega) (by decide +kernel))

theorem block20_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 116993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 36 (by omega) (by decide +kernel))

theorem block20_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 37 (by omega) (by decide +kernel))

theorem block20_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 38 (by omega) (by decide +kernel))

theorem block20_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 39 (by omega) (by decide +kernel))

theorem block20_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 40 (by omega) (by decide +kernel))

theorem block20_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 41 (by omega) (by decide +kernel))

theorem block20_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 42 (by omega) (by decide +kernel))

theorem block20_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 43 (by omega) (by decide +kernel))

theorem block20_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 44 (by omega) (by decide +kernel))

theorem block20_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 45 (by omega) (by decide +kernel))

theorem block20_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 46 (by omega) (by decide +kernel))

theorem block20_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 47 (by omega) (by decide +kernel))

theorem block20_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 48 (by omega) (by decide +kernel))

theorem block20_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 49 (by omega) (by decide +kernel))

theorem block20_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 50 (by omega) (by decide +kernel))

theorem block20_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 117953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 51 (by omega) (by decide +kernel))

theorem block20_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 52 (by omega) (by decide +kernel))

theorem block20_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 53 (by omega) (by decide +kernel))

theorem block20_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 54 (by omega) (by decide +kernel))

theorem block20_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 55 (by omega) (by decide +kernel))

theorem block20_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 56 (by omega) (by decide +kernel))

theorem block20_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 57 (by omega) (by decide +kernel))

theorem block20_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 58 (by omega) (by decide +kernel))

theorem block20_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 59 (by omega) (by decide +kernel))

theorem block20_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 60 (by omega) (by decide +kernel))

theorem block20_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 61 (by omega) (by decide +kernel))

theorem block20_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 62 (by omega) (by decide +kernel))

theorem block20_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 118721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 20 (by omega) (by omega) block15 block16 block19 block20 tail 63 (by omega) (by decide +kernel))

theorem readCheckBlock_of_64_page_count
    (read : Nat → ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly.OriginalNode) (lo pages : Nat)
    (hpages : ∀ p : Nat, p < pages →
      readCheckBlock read (lo + 64*p) 64 = true) :
    readCheckBlock read lo (64*pages) = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64*pages := List.mem_range.mp hk
  let p := k/64
  let r := k%64
  have hp : p < pages := by dsimp [p]; omega
  have hr : r < 64 := by dsimp [r]; omega
  have he : 64*p+r=k := by dsimp [p,r]; omega
  have hs : readCheckStep read (lo + 64*p + r) = true :=
    readCheckBlock_step (hpages p hp) hr
  have hindex : lo + 64*p + r = lo+k := by omega
  simpa only [hindex] using hs

theorem block20_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 114689 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) (114689 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block20_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 20 block15 block16 block19 block20 tail)) 114689 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock20FullSourceOnly

-- The page checks use the frozen four-slot reference.
