-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- The 64 closed reference pages use ordinary `by decide +kernel` proofs.
-- Page starts are 147457 + 64*p; the original block ends at 151552.
-- Physical window slots: boundary=23, delayed=24, prev=27, current=28.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block23Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block24Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block27Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block28Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock28FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block28_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 0 (by omega) (by decide +kernel))

theorem block28_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 1 (by omega) (by decide +kernel))

theorem block28_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 2 (by omega) (by decide +kernel))

theorem block28_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 3 (by omega) (by decide +kernel))

theorem block28_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 4 (by omega) (by decide +kernel))

theorem block28_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 5 (by omega) (by decide +kernel))

theorem block28_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 6 (by omega) (by decide +kernel))

theorem block28_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 7 (by omega) (by decide +kernel))

theorem block28_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 8 (by omega) (by decide +kernel))

theorem block28_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 9 (by omega) (by decide +kernel))

theorem block28_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 10 (by omega) (by decide +kernel))

theorem block28_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 11 (by omega) (by decide +kernel))

theorem block28_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 12 (by omega) (by decide +kernel))

theorem block28_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 13 (by omega) (by decide +kernel))

theorem block28_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 14 (by omega) (by decide +kernel))

theorem block28_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 15 (by omega) (by decide +kernel))

theorem block28_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 16 (by omega) (by decide +kernel))

theorem block28_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 17 (by omega) (by decide +kernel))

theorem block28_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 18 (by omega) (by decide +kernel))

theorem block28_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 19 (by omega) (by decide +kernel))

theorem block28_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 20 (by omega) (by decide +kernel))

theorem block28_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 21 (by omega) (by decide +kernel))

theorem block28_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 22 (by omega) (by decide +kernel))

theorem block28_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 23 (by omega) (by decide +kernel))

theorem block28_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 148993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 24 (by omega) (by decide +kernel))

theorem block28_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 25 (by omega) (by decide +kernel))

theorem block28_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 26 (by omega) (by decide +kernel))

theorem block28_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 27 (by omega) (by decide +kernel))

theorem block28_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 28 (by omega) (by decide +kernel))

theorem block28_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 29 (by omega) (by decide +kernel))

theorem block28_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 30 (by omega) (by decide +kernel))

theorem block28_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 31 (by omega) (by decide +kernel))

theorem block28_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 32 (by omega) (by decide +kernel))

theorem block28_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 33 (by omega) (by decide +kernel))

theorem block28_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 34 (by omega) (by decide +kernel))

theorem block28_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 35 (by omega) (by decide +kernel))

theorem block28_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 36 (by omega) (by decide +kernel))

theorem block28_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 37 (by omega) (by decide +kernel))

theorem block28_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 38 (by omega) (by decide +kernel))

theorem block28_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 149953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 39 (by omega) (by decide +kernel))

theorem block28_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 40 (by omega) (by decide +kernel))

theorem block28_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 41 (by omega) (by decide +kernel))

theorem block28_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 42 (by omega) (by decide +kernel))

theorem block28_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 43 (by omega) (by decide +kernel))

theorem block28_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 44 (by omega) (by decide +kernel))

theorem block28_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 45 (by omega) (by decide +kernel))

theorem block28_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 46 (by omega) (by decide +kernel))

theorem block28_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 47 (by omega) (by decide +kernel))

theorem block28_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 48 (by omega) (by decide +kernel))

theorem block28_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 49 (by omega) (by decide +kernel))

theorem block28_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 50 (by omega) (by decide +kernel))

theorem block28_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 51 (by omega) (by decide +kernel))

theorem block28_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 52 (by omega) (by decide +kernel))

theorem block28_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 53 (by omega) (by decide +kernel))

theorem block28_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 54 (by omega) (by decide +kernel))

theorem block28_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 150977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 55 (by omega) (by decide +kernel))

theorem block28_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 56 (by omega) (by decide +kernel))

theorem block28_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 57 (by omega) (by decide +kernel))

theorem block28_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 58 (by omega) (by decide +kernel))

theorem block28_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 59 (by omega) (by decide +kernel))

theorem block28_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 60 (by omega) (by decide +kernel))

theorem block28_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 61 (by omega) (by decide +kernel))

theorem block28_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 62 (by omega) (by decide +kernel))

theorem block28_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 151489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 28 (by omega) (by omega)
      block23 block24 block27 block28 tail 63 (by omega) (by decide +kernel))

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

theorem block28_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147457 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) (147457 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block28_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 28 block23 block24 block27 block28 tail)) 147457 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock28FullSourceOnly
