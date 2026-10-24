-- SOURCEONLY candidate; UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation and compilation. Missing sibling imports must be supplied by ROOT.
-- Block09 rows 69633..73728; pages start at 69633 + 64*p, p=0..63.
-- Block04Data.lean SHA256: NOT_PRESENT_IN_CANONICAL_SOURCE_DIRECTORY
-- Block05Data.lean SHA256: NOT_PRESENT_IN_CANONICAL_SOURCE_DIRECTORY
-- Block08Data.lean SHA256: NOT_PRESENT_IN_CANONICAL_SOURCE_DIRECTORY
-- Block09Data.lean.txt SHA256: 9f7e7cdf7ad054607364c635fd8a95eabbfae64af32f46c96a920a3730bce9a8
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block04Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block05Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block08Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block09Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock09FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block09_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 0 (by omega) (by decide +kernel))

theorem block09_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 1 (by omega) (by decide +kernel))

theorem block09_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 2 (by omega) (by decide +kernel))

theorem block09_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 3 (by omega) (by decide +kernel))

theorem block09_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 4 (by omega) (by decide +kernel))

theorem block09_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 5 (by omega) (by decide +kernel))

theorem block09_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 6 (by omega) (by decide +kernel))

theorem block09_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 7 (by omega) (by decide +kernel))

theorem block09_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 8 (by omega) (by decide +kernel))

theorem block09_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 9 (by omega) (by decide +kernel))

theorem block09_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 10 (by omega) (by decide +kernel))

theorem block09_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 11 (by omega) (by decide +kernel))

theorem block09_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 12 (by omega) (by decide +kernel))

theorem block09_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 13 (by omega) (by decide +kernel))

theorem block09_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 14 (by omega) (by decide +kernel))

theorem block09_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 15 (by omega) (by decide +kernel))

theorem block09_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 16 (by omega) (by decide +kernel))

theorem block09_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 17 (by omega) (by decide +kernel))

theorem block09_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 18 (by omega) (by decide +kernel))

theorem block09_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 19 (by omega) (by decide +kernel))

theorem block09_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 20 (by omega) (by decide +kernel))

theorem block09_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 70977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 21 (by omega) (by decide +kernel))

theorem block09_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 22 (by omega) (by decide +kernel))

theorem block09_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 23 (by omega) (by decide +kernel))

theorem block09_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 24 (by omega) (by decide +kernel))

theorem block09_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 25 (by omega) (by decide +kernel))

theorem block09_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 26 (by omega) (by decide +kernel))

theorem block09_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 27 (by omega) (by decide +kernel))

theorem block09_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 28 (by omega) (by decide +kernel))

theorem block09_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 29 (by omega) (by decide +kernel))

theorem block09_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 30 (by omega) (by decide +kernel))

theorem block09_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 31 (by omega) (by decide +kernel))

theorem block09_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 32 (by omega) (by decide +kernel))

theorem block09_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 33 (by omega) (by decide +kernel))

theorem block09_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 34 (by omega) (by decide +kernel))

theorem block09_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 35 (by omega) (by decide +kernel))

theorem block09_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 71937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 36 (by omega) (by decide +kernel))

theorem block09_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 37 (by omega) (by decide +kernel))

theorem block09_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 38 (by omega) (by decide +kernel))

theorem block09_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 39 (by omega) (by decide +kernel))

theorem block09_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 40 (by omega) (by decide +kernel))

theorem block09_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 41 (by omega) (by decide +kernel))

theorem block09_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 42 (by omega) (by decide +kernel))

theorem block09_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 43 (by omega) (by decide +kernel))

theorem block09_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 44 (by omega) (by decide +kernel))

theorem block09_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 45 (by omega) (by decide +kernel))

theorem block09_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 46 (by omega) (by decide +kernel))

theorem block09_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 47 (by omega) (by decide +kernel))

theorem block09_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 48 (by omega) (by decide +kernel))

theorem block09_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 49 (by omega) (by decide +kernel))

theorem block09_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 50 (by omega) (by decide +kernel))

theorem block09_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 51 (by omega) (by decide +kernel))

theorem block09_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 72961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 52 (by omega) (by decide +kernel))

theorem block09_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 53 (by omega) (by decide +kernel))

theorem block09_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 54 (by omega) (by decide +kernel))

theorem block09_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 55 (by omega) (by decide +kernel))

theorem block09_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 56 (by omega) (by decide +kernel))

theorem block09_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 57 (by omega) (by decide +kernel))

theorem block09_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 58 (by omega) (by decide +kernel))

theorem block09_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 59 (by omega) (by decide +kernel))

theorem block09_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 60 (by omega) (by decide +kernel))

theorem block09_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 61 (by omega) (by decide +kernel))

theorem block09_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 62 (by omega) (by decide +kernel))

theorem block09_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 73665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 9 (by omega) (by omega) block04 block05 block08 block09 tail 63 (by omega) (by decide +kernel))

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

theorem block09_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69633 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) (69633 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block09_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 9 block04 block05 block08 block09 tail)) 69633 64 hpages

theorem block09_same_table_all_pages_checked (blocks : Nat → Block)
    (h04 : blocks 4 = block04) (h05 : blocks 5 = block05)
    (h08 : blocks 8 = block08) (h09 : blocks 9 = block09) :
    readCheckBlock (assembledRead blocks) 69633 4096 = true := by
  have hwindow : windowBlocks 9 block04 block05 block08 block09 blocks = blocks := by
    rw [← h04, ← h05, ← h08, ← h09]
    exact windowBlocks_eq_original 9 blocks
  have h := block09_all_pages_checked blocks
  rw [hwindow] at h
  exact h
end ImbalancedChen.OriginalU2StoredNodeBlock09FullSourceOnly
