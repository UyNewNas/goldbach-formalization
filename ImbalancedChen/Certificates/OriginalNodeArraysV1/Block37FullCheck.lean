-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*37 + 64*p; the full block ends at 188416.
-- Block32Data.lean import required from ROOT; expected export block32 : Block.
-- Block33Data.lean import required from ROOT; expected export block33 : Block.
-- Block36Data.lean import required from ROOT; expected export block36 : Block.
-- Block37Data.lean import required from ROOT; expected export block37 : Block.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block32Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block33Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block36Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block37Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock37FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block37_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 0 (by omega) (by decide +kernel))

theorem block37_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 1 (by omega) (by decide +kernel))

theorem block37_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 2 (by omega) (by decide +kernel))

theorem block37_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 3 (by omega) (by decide +kernel))

theorem block37_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 4 (by omega) (by decide +kernel))

theorem block37_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 5 (by omega) (by decide +kernel))

theorem block37_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 6 (by omega) (by decide +kernel))

theorem block37_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 7 (by omega) (by decide +kernel))

theorem block37_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 8 (by omega) (by decide +kernel))

theorem block37_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 9 (by omega) (by decide +kernel))

theorem block37_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 10 (by omega) (by decide +kernel))

theorem block37_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 11 (by omega) (by decide +kernel))

theorem block37_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 12 (by omega) (by decide +kernel))

theorem block37_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 13 (by omega) (by decide +kernel))

theorem block37_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 14 (by omega) (by decide +kernel))

theorem block37_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 15 (by omega) (by decide +kernel))

theorem block37_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 16 (by omega) (by decide +kernel))

theorem block37_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 17 (by omega) (by decide +kernel))

theorem block37_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 18 (by omega) (by decide +kernel))

theorem block37_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 19 (by omega) (by decide +kernel))

theorem block37_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 20 (by omega) (by decide +kernel))

theorem block37_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 21 (by omega) (by decide +kernel))

theorem block37_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 22 (by omega) (by decide +kernel))

theorem block37_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 23 (by omega) (by decide +kernel))

theorem block37_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 24 (by omega) (by decide +kernel))

theorem block37_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 25 (by omega) (by decide +kernel))

theorem block37_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 185985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 26 (by omega) (by decide +kernel))

theorem block37_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 27 (by omega) (by decide +kernel))

theorem block37_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 28 (by omega) (by decide +kernel))

theorem block37_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 29 (by omega) (by decide +kernel))

theorem block37_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 30 (by omega) (by decide +kernel))

theorem block37_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 31 (by omega) (by decide +kernel))

theorem block37_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 32 (by omega) (by decide +kernel))

theorem block37_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 33 (by omega) (by decide +kernel))

theorem block37_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 34 (by omega) (by decide +kernel))

theorem block37_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 35 (by omega) (by decide +kernel))

theorem block37_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 36 (by omega) (by decide +kernel))

theorem block37_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 37 (by omega) (by decide +kernel))

theorem block37_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 38 (by omega) (by decide +kernel))

theorem block37_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 39 (by omega) (by decide +kernel))

theorem block37_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 40 (by omega) (by decide +kernel))

theorem block37_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 186945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 41 (by omega) (by decide +kernel))

theorem block37_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 42 (by omega) (by decide +kernel))

theorem block37_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 43 (by omega) (by decide +kernel))

theorem block37_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 44 (by omega) (by decide +kernel))

theorem block37_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 45 (by omega) (by decide +kernel))

theorem block37_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 46 (by omega) (by decide +kernel))

theorem block37_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 47 (by omega) (by decide +kernel))

theorem block37_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 48 (by omega) (by decide +kernel))

theorem block37_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 49 (by omega) (by decide +kernel))

theorem block37_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 50 (by omega) (by decide +kernel))

theorem block37_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 51 (by omega) (by decide +kernel))

theorem block37_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 52 (by omega) (by decide +kernel))

theorem block37_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 53 (by omega) (by decide +kernel))

theorem block37_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 54 (by omega) (by decide +kernel))

theorem block37_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 55 (by omega) (by decide +kernel))

theorem block37_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 56 (by omega) (by decide +kernel))

theorem block37_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 187969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 57 (by omega) (by decide +kernel))

theorem block37_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 188033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 58 (by omega) (by decide +kernel))

theorem block37_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 188097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 59 (by omega) (by decide +kernel))

theorem block37_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 188161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 60 (by omega) (by decide +kernel))

theorem block37_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 188225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 61 (by omega) (by decide +kernel))

theorem block37_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 188289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 62 (by omega) (by decide +kernel))

theorem block37_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 188353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 37 (by omega) (by omega)
      block32 block33 block36 block37 tail 63 (by omega) (by decide +kernel))

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

theorem block37_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184321 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) (184321 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block37_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 37 block32 block33 block36 block37 tail)) 184321 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock37FullSourceOnly
