-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*17 + 64*p; the full block ends at 106496.
-- Block12Data.lean: planned import; expected ABI namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly, def block12 : NodeTree 12.
-- Block13Data.lean: planned import; expected ABI namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly, def block13 : NodeTree 12.
-- Block16Data.lean: planned import; expected ABI namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly, def block16 : NodeTree 12.
-- Block17Data.lean SHA256 a4b6dfcc8e84c5cdb533ff056177fe02436ceaaf867d7d07bee8d93e426db483
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block12Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block13Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block16Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block17Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock17FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block17_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 0 (by omega) (by decide +kernel))

theorem block17_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 1 (by omega) (by decide +kernel))

theorem block17_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 2 (by omega) (by decide +kernel))

theorem block17_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 3 (by omega) (by decide +kernel))

theorem block17_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 4 (by omega) (by decide +kernel))

theorem block17_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 5 (by omega) (by decide +kernel))

theorem block17_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 6 (by omega) (by decide +kernel))

theorem block17_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 7 (by omega) (by decide +kernel))

theorem block17_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 8 (by omega) (by decide +kernel))

theorem block17_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 9 (by omega) (by decide +kernel))

theorem block17_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 10 (by omega) (by decide +kernel))

theorem block17_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 11 (by omega) (by decide +kernel))

theorem block17_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 12 (by omega) (by decide +kernel))

theorem block17_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 13 (by omega) (by decide +kernel))

theorem block17_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 14 (by omega) (by decide +kernel))

theorem block17_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 15 (by omega) (by decide +kernel))

theorem block17_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 16 (by omega) (by decide +kernel))

theorem block17_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 17 (by omega) (by decide +kernel))

theorem block17_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 18 (by omega) (by decide +kernel))

theorem block17_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 19 (by omega) (by decide +kernel))

theorem block17_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 20 (by omega) (by decide +kernel))

theorem block17_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 21 (by omega) (by decide +kernel))

theorem block17_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 22 (by omega) (by decide +kernel))

theorem block17_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 23 (by omega) (by decide +kernel))

theorem block17_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 103937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 24 (by omega) (by decide +kernel))

theorem block17_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 25 (by omega) (by decide +kernel))

theorem block17_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 26 (by omega) (by decide +kernel))

theorem block17_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 27 (by omega) (by decide +kernel))

theorem block17_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 28 (by omega) (by decide +kernel))

theorem block17_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 29 (by omega) (by decide +kernel))

theorem block17_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 30 (by omega) (by decide +kernel))

theorem block17_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 31 (by omega) (by decide +kernel))

theorem block17_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 32 (by omega) (by decide +kernel))

theorem block17_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 33 (by omega) (by decide +kernel))

theorem block17_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 34 (by omega) (by decide +kernel))

theorem block17_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 35 (by omega) (by decide +kernel))

theorem block17_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 36 (by omega) (by decide +kernel))

theorem block17_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 37 (by omega) (by decide +kernel))

theorem block17_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 38 (by omega) (by decide +kernel))

theorem block17_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 39 (by omega) (by decide +kernel))

theorem block17_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 104961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 40 (by omega) (by decide +kernel))

theorem block17_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 41 (by omega) (by decide +kernel))

theorem block17_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 42 (by omega) (by decide +kernel))

theorem block17_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 43 (by omega) (by decide +kernel))

theorem block17_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 44 (by omega) (by decide +kernel))

theorem block17_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 45 (by omega) (by decide +kernel))

theorem block17_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 46 (by omega) (by decide +kernel))

theorem block17_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 47 (by omega) (by decide +kernel))

theorem block17_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 48 (by omega) (by decide +kernel))

theorem block17_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 49 (by omega) (by decide +kernel))

theorem block17_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 50 (by omega) (by decide +kernel))

theorem block17_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 51 (by omega) (by decide +kernel))

theorem block17_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 52 (by omega) (by decide +kernel))

theorem block17_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 53 (by omega) (by decide +kernel))

theorem block17_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 54 (by omega) (by decide +kernel))

theorem block17_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 55 (by omega) (by decide +kernel))

theorem block17_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 105985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 56 (by omega) (by decide +kernel))

theorem block17_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 106049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 57 (by omega) (by decide +kernel))

theorem block17_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 106113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 58 (by omega) (by decide +kernel))

theorem block17_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 106177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 59 (by omega) (by decide +kernel))

theorem block17_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 106241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 60 (by omega) (by decide +kernel))

theorem block17_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 106305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 61 (by omega) (by decide +kernel))

theorem block17_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 106369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 62 (by omega) (by decide +kernel))

theorem block17_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 106433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 17 (by omega) (by omega)
      block12 block13 block16 block17 tail 63 (by omega) (by decide +kernel))

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

theorem block17_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102401 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) (102401 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block17_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 17 block12 block13 block16 block17 tail)) 102401 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock17FullSourceOnly
