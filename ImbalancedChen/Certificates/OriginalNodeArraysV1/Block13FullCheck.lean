-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*13 + 64*p; full block indices 86017..90112.
-- Block08Data.lean is a required predecessor module; not present in actual supplier tree
-- Block09Data.lean is a required predecessor module; not present in actual supplier tree
-- Block12Data.lean is a required predecessor module; not present in actual supplier tree
-- Draft Block13Data.lean.txt SHA256 d6a07661fbd6ce3d648261b78fa4dfd8b7330cae800405d5f6a5f780b907f850
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block08Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block09Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block12Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block13Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock13FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block13_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 0 (by omega) (by decide +kernel))

theorem block13_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 1 (by omega) (by decide +kernel))

theorem block13_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 2 (by omega) (by decide +kernel))

theorem block13_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 3 (by omega) (by decide +kernel))

theorem block13_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 4 (by omega) (by decide +kernel))

theorem block13_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 5 (by omega) (by decide +kernel))

theorem block13_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 6 (by omega) (by decide +kernel))

theorem block13_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 7 (by omega) (by decide +kernel))

theorem block13_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 8 (by omega) (by decide +kernel))

theorem block13_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 9 (by omega) (by decide +kernel))

theorem block13_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 10 (by omega) (by decide +kernel))

theorem block13_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 11 (by omega) (by decide +kernel))

theorem block13_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 12 (by omega) (by decide +kernel))

theorem block13_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 13 (by omega) (by decide +kernel))

theorem block13_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 14 (by omega) (by decide +kernel))

theorem block13_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 15 (by omega) (by decide +kernel))

theorem block13_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 16 (by omega) (by decide +kernel))

theorem block13_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 17 (by omega) (by decide +kernel))

theorem block13_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 18 (by omega) (by decide +kernel))

theorem block13_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 19 (by omega) (by decide +kernel))

theorem block13_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 20 (by omega) (by decide +kernel))

theorem block13_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 21 (by omega) (by decide +kernel))

theorem block13_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 22 (by omega) (by decide +kernel))

theorem block13_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 23 (by omega) (by decide +kernel))

theorem block13_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 24 (by omega) (by decide +kernel))

theorem block13_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 25 (by omega) (by decide +kernel))

theorem block13_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 26 (by omega) (by decide +kernel))

theorem block13_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 27 (by omega) (by decide +kernel))

theorem block13_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 28 (by omega) (by decide +kernel))

theorem block13_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 29 (by omega) (by decide +kernel))

theorem block13_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 87937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 30 (by omega) (by decide +kernel))

theorem block13_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 31 (by omega) (by decide +kernel))

theorem block13_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 32 (by omega) (by decide +kernel))

theorem block13_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 33 (by omega) (by decide +kernel))

theorem block13_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 34 (by omega) (by decide +kernel))

theorem block13_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 35 (by omega) (by decide +kernel))

theorem block13_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 36 (by omega) (by decide +kernel))

theorem block13_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 37 (by omega) (by decide +kernel))

theorem block13_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 38 (by omega) (by decide +kernel))

theorem block13_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 39 (by omega) (by decide +kernel))

theorem block13_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 40 (by omega) (by decide +kernel))

theorem block13_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 41 (by omega) (by decide +kernel))

theorem block13_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 42 (by omega) (by decide +kernel))

theorem block13_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 43 (by omega) (by decide +kernel))

theorem block13_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 44 (by omega) (by decide +kernel))

theorem block13_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 45 (by omega) (by decide +kernel))

theorem block13_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 88961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 46 (by omega) (by decide +kernel))

theorem block13_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 47 (by omega) (by decide +kernel))

theorem block13_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 48 (by omega) (by decide +kernel))

theorem block13_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 49 (by omega) (by decide +kernel))

theorem block13_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 50 (by omega) (by decide +kernel))

theorem block13_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 51 (by omega) (by decide +kernel))

theorem block13_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 52 (by omega) (by decide +kernel))

theorem block13_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 53 (by omega) (by decide +kernel))

theorem block13_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 54 (by omega) (by decide +kernel))

theorem block13_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 55 (by omega) (by decide +kernel))

theorem block13_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 56 (by omega) (by decide +kernel))

theorem block13_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 57 (by omega) (by decide +kernel))

theorem block13_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 58 (by omega) (by decide +kernel))

theorem block13_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 59 (by omega) (by decide +kernel))

theorem block13_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 60 (by omega) (by decide +kernel))

theorem block13_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 61 (by omega) (by decide +kernel))

theorem block13_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 89985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 62 (by omega) (by decide +kernel))

theorem block13_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 90049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 13 (by omega) (by omega) block08 block09 block12 block13 tail 63 (by omega) (by decide +kernel))

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

theorem block13_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86017 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) (86017 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block13_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 13 block08 block09 block12 block13 tail)) 86017 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock13FullSourceOnly

-- The Block04 prefix boundary is handled by DelayedPageTransfer; Block13 first delayed index is 69632, Block08 offset 4095.
-- All 64 closed reference checks remain SOURCEONLY until ROOT compiles this module with predecessor data modules.