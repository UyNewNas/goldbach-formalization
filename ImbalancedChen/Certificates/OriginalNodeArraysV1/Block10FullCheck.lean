-- SOURCEONLY candidate; UNCOMPILED / NOT PASS / no admission asserted.
-- Block10 range: [73729, 77824], partitioned into 64 consecutive pages of 64.
-- The Data source is intentionally not represented here because its frozen raw input is absent.
-- Required imports and block constants are documented in CP.txt.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block05Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block06Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block09Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block10Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock10FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block10_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 73729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 0 (by omega) (by decide +kernel))

theorem block10_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 73793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 1 (by omega) (by decide +kernel))

theorem block10_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 73857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 2 (by omega) (by decide +kernel))

theorem block10_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 73921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 3 (by omega) (by decide +kernel))

theorem block10_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 73985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 4 (by omega) (by decide +kernel))

theorem block10_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 5 (by omega) (by decide +kernel))

theorem block10_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 6 (by omega) (by decide +kernel))

theorem block10_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 7 (by omega) (by decide +kernel))

theorem block10_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 8 (by omega) (by decide +kernel))

theorem block10_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 9 (by omega) (by decide +kernel))

theorem block10_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 10 (by omega) (by decide +kernel))

theorem block10_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 11 (by omega) (by decide +kernel))

theorem block10_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 12 (by omega) (by decide +kernel))

theorem block10_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 13 (by omega) (by decide +kernel))

theorem block10_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 14 (by omega) (by decide +kernel))

theorem block10_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 15 (by omega) (by decide +kernel))

theorem block10_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 16 (by omega) (by decide +kernel))

theorem block10_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 17 (by omega) (by decide +kernel))

theorem block10_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 18 (by omega) (by decide +kernel))

theorem block10_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 74945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 19 (by omega) (by decide +kernel))

theorem block10_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 20 (by omega) (by decide +kernel))

theorem block10_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 21 (by omega) (by decide +kernel))

theorem block10_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 22 (by omega) (by decide +kernel))

theorem block10_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 23 (by omega) (by decide +kernel))

theorem block10_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 24 (by omega) (by decide +kernel))

theorem block10_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 25 (by omega) (by decide +kernel))

theorem block10_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 26 (by omega) (by decide +kernel))

theorem block10_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 27 (by omega) (by decide +kernel))

theorem block10_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 28 (by omega) (by decide +kernel))

theorem block10_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 29 (by omega) (by decide +kernel))

theorem block10_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 30 (by omega) (by decide +kernel))

theorem block10_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 31 (by omega) (by decide +kernel))

theorem block10_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 32 (by omega) (by decide +kernel))

theorem block10_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 33 (by omega) (by decide +kernel))

theorem block10_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 34 (by omega) (by decide +kernel))

theorem block10_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 75969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 35 (by omega) (by decide +kernel))

theorem block10_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 36 (by omega) (by decide +kernel))

theorem block10_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 37 (by omega) (by decide +kernel))

theorem block10_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 38 (by omega) (by decide +kernel))

theorem block10_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 39 (by omega) (by decide +kernel))

theorem block10_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 40 (by omega) (by decide +kernel))

theorem block10_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 41 (by omega) (by decide +kernel))

theorem block10_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 42 (by omega) (by decide +kernel))

theorem block10_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 43 (by omega) (by decide +kernel))

theorem block10_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 44 (by omega) (by decide +kernel))

theorem block10_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 45 (by omega) (by decide +kernel))

theorem block10_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 46 (by omega) (by decide +kernel))

theorem block10_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 47 (by omega) (by decide +kernel))

theorem block10_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 48 (by omega) (by decide +kernel))

theorem block10_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 49 (by omega) (by decide +kernel))

theorem block10_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 50 (by omega) (by decide +kernel))

theorem block10_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 76993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 51 (by omega) (by decide +kernel))

theorem block10_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 52 (by omega) (by decide +kernel))

theorem block10_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 53 (by omega) (by decide +kernel))

theorem block10_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 54 (by omega) (by decide +kernel))

theorem block10_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 55 (by omega) (by decide +kernel))

theorem block10_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 56 (by omega) (by decide +kernel))

theorem block10_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 57 (by omega) (by decide +kernel))

theorem block10_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 58 (by omega) (by decide +kernel))

theorem block10_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 59 (by omega) (by decide +kernel))

theorem block10_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 60 (by omega) (by decide +kernel))

theorem block10_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 61 (by omega) (by decide +kernel))

theorem block10_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 62 (by omega) (by decide +kernel))

theorem block10_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 77761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 10 (by omega) (by omega)
      block05 block06 block09 block10 tail 63 (by omega) (by decide +kernel))

theorem block10_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) 73729 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail)) (73729 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block10_page63_checked tail
  exact readCheckBlock_of_64_pages
    (assembledRead (windowBlocks 10 block05 block06 block09 block10 tail))
    73729 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock10FullSourceOnly
