-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*25 + 64*p; the full block ends at 139264.
-- Block20Data.lean import required from ROOT; expected export block20 : Block.
-- Block21Data.lean import required from ROOT; expected export block21 : Block.
-- Block24Data.lean import required from ROOT; expected export block24 : Block.
-- Block25Data.lean import required from ROOT; expected export block25 : Block.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block20Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block21Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block24Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block25Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock25FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block25_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 0 (by omega) (by decide +kernel))

theorem block25_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 1 (by omega) (by decide +kernel))

theorem block25_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 2 (by omega) (by decide +kernel))

theorem block25_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 3 (by omega) (by decide +kernel))

theorem block25_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 4 (by omega) (by decide +kernel))

theorem block25_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 5 (by omega) (by decide +kernel))

theorem block25_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 6 (by omega) (by decide +kernel))

theorem block25_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 7 (by omega) (by decide +kernel))

theorem block25_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 8 (by omega) (by decide +kernel))

theorem block25_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 9 (by omega) (by decide +kernel))

theorem block25_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 10 (by omega) (by decide +kernel))

theorem block25_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 11 (by omega) (by decide +kernel))

theorem block25_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 12 (by omega) (by decide +kernel))

theorem block25_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 13 (by omega) (by decide +kernel))

theorem block25_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 14 (by omega) (by decide +kernel))

theorem block25_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 15 (by omega) (by decide +kernel))

theorem block25_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 16 (by omega) (by decide +kernel))

theorem block25_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 17 (by omega) (by decide +kernel))

theorem block25_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 18 (by omega) (by decide +kernel))

theorem block25_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 19 (by omega) (by decide +kernel))

theorem block25_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 20 (by omega) (by decide +kernel))

theorem block25_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 21 (by omega) (by decide +kernel))

theorem block25_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 22 (by omega) (by decide +kernel))

theorem block25_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 23 (by omega) (by decide +kernel))

theorem block25_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 24 (by omega) (by decide +kernel))

theorem block25_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 25 (by omega) (by decide +kernel))

theorem block25_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 26 (by omega) (by decide +kernel))

theorem block25_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 27 (by omega) (by decide +kernel))

theorem block25_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 136961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 28 (by omega) (by decide +kernel))

theorem block25_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 29 (by omega) (by decide +kernel))

theorem block25_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 30 (by omega) (by decide +kernel))

theorem block25_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 31 (by omega) (by decide +kernel))

theorem block25_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 32 (by omega) (by decide +kernel))

theorem block25_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 33 (by omega) (by decide +kernel))

theorem block25_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 34 (by omega) (by decide +kernel))

theorem block25_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 35 (by omega) (by decide +kernel))

theorem block25_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 36 (by omega) (by decide +kernel))

theorem block25_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 37 (by omega) (by decide +kernel))

theorem block25_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 38 (by omega) (by decide +kernel))

theorem block25_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 39 (by omega) (by decide +kernel))

theorem block25_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 40 (by omega) (by decide +kernel))

theorem block25_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 41 (by omega) (by decide +kernel))

theorem block25_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 42 (by omega) (by decide +kernel))

theorem block25_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 43 (by omega) (by decide +kernel))

theorem block25_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 137985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 44 (by omega) (by decide +kernel))

theorem block25_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 45 (by omega) (by decide +kernel))

theorem block25_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 46 (by omega) (by decide +kernel))

theorem block25_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 47 (by omega) (by decide +kernel))

theorem block25_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 48 (by omega) (by decide +kernel))

theorem block25_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 49 (by omega) (by decide +kernel))

theorem block25_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 50 (by omega) (by decide +kernel))

theorem block25_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 51 (by omega) (by decide +kernel))

theorem block25_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 52 (by omega) (by decide +kernel))

theorem block25_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 53 (by omega) (by decide +kernel))

theorem block25_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 54 (by omega) (by decide +kernel))

theorem block25_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 55 (by omega) (by decide +kernel))

theorem block25_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 56 (by omega) (by decide +kernel))

theorem block25_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 57 (by omega) (by decide +kernel))

theorem block25_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 58 (by omega) (by decide +kernel))

theorem block25_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 138945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 59 (by omega) (by decide +kernel))

theorem block25_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 139009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 60 (by omega) (by decide +kernel))

theorem block25_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 139073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 61 (by omega) (by decide +kernel))

theorem block25_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 139137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 62 (by omega) (by decide +kernel))

theorem block25_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 139201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 25 (by omega) (by omega)
      block20 block21 block24 block25 tail 63 (by omega) (by decide +kernel))

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

theorem block25_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135169 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) (135169 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block25_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 25 block20 block21 block24 block25 tail)) 135169 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock25FullSourceOnly
