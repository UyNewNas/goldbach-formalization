-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*36 + 64*p; the full block ends at 184320.
-- Block31Data.lean import required from ROOT; expected export block31 : Block.
-- Block32Data.lean import required from ROOT; expected export block32 : Block.
-- Block35Data.lean import required from ROOT; expected export block35 : Block.
-- Block36Data.lean import required from ROOT; expected export block36 : Block.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block31Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block32Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block35Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block36Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock36FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block36_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 0 (by omega) (by decide +kernel))

theorem block36_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 1 (by omega) (by decide +kernel))

theorem block36_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 2 (by omega) (by decide +kernel))

theorem block36_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 3 (by omega) (by decide +kernel))

theorem block36_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 4 (by omega) (by decide +kernel))

theorem block36_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 5 (by omega) (by decide +kernel))

theorem block36_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 6 (by omega) (by decide +kernel))

theorem block36_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 7 (by omega) (by decide +kernel))

theorem block36_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 8 (by omega) (by decide +kernel))

theorem block36_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 9 (by omega) (by decide +kernel))

theorem block36_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 10 (by omega) (by decide +kernel))

theorem block36_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 11 (by omega) (by decide +kernel))

theorem block36_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 12 (by omega) (by decide +kernel))

theorem block36_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 13 (by omega) (by decide +kernel))

theorem block36_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 14 (by omega) (by decide +kernel))

theorem block36_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 15 (by omega) (by decide +kernel))

theorem block36_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 16 (by omega) (by decide +kernel))

theorem block36_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 17 (by omega) (by decide +kernel))

theorem block36_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 18 (by omega) (by decide +kernel))

theorem block36_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 19 (by omega) (by decide +kernel))

theorem block36_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 20 (by omega) (by decide +kernel))

theorem block36_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 21 (by omega) (by decide +kernel))

theorem block36_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 22 (by omega) (by decide +kernel))

theorem block36_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 23 (by omega) (by decide +kernel))

theorem block36_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 24 (by omega) (by decide +kernel))

theorem block36_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 25 (by omega) (by decide +kernel))

theorem block36_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 26 (by omega) (by decide +kernel))

theorem block36_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 181953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 27 (by omega) (by decide +kernel))

theorem block36_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 28 (by omega) (by decide +kernel))

theorem block36_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 29 (by omega) (by decide +kernel))

theorem block36_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 30 (by omega) (by decide +kernel))

theorem block36_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 31 (by omega) (by decide +kernel))

theorem block36_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 32 (by omega) (by decide +kernel))

theorem block36_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 33 (by omega) (by decide +kernel))

theorem block36_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 34 (by omega) (by decide +kernel))

theorem block36_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 35 (by omega) (by decide +kernel))

theorem block36_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 36 (by omega) (by decide +kernel))

theorem block36_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 37 (by omega) (by decide +kernel))

theorem block36_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 38 (by omega) (by decide +kernel))

theorem block36_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 39 (by omega) (by decide +kernel))

theorem block36_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 40 (by omega) (by decide +kernel))

theorem block36_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 41 (by omega) (by decide +kernel))

theorem block36_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 42 (by omega) (by decide +kernel))

theorem block36_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 182977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 43 (by omega) (by decide +kernel))

theorem block36_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 44 (by omega) (by decide +kernel))

theorem block36_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 45 (by omega) (by decide +kernel))

theorem block36_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 46 (by omega) (by decide +kernel))

theorem block36_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 47 (by omega) (by decide +kernel))

theorem block36_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 48 (by omega) (by decide +kernel))

theorem block36_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 49 (by omega) (by decide +kernel))

theorem block36_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 50 (by omega) (by decide +kernel))

theorem block36_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 51 (by omega) (by decide +kernel))

theorem block36_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 52 (by omega) (by decide +kernel))

theorem block36_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 53 (by omega) (by decide +kernel))

theorem block36_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 54 (by omega) (by decide +kernel))

theorem block36_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 55 (by omega) (by decide +kernel))

theorem block36_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 56 (by omega) (by decide +kernel))

theorem block36_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 57 (by omega) (by decide +kernel))

theorem block36_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 183937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 58 (by omega) (by decide +kernel))

theorem block36_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 184001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 59 (by omega) (by decide +kernel))

theorem block36_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 184065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 60 (by omega) (by decide +kernel))

theorem block36_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 184129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 61 (by omega) (by decide +kernel))

theorem block36_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 184193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 62 (by omega) (by decide +kernel))

theorem block36_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 184257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 36 (by omega) (by omega)
      block31 block32 block35 block36 tail 63 (by omega) (by decide +kernel))

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

theorem block36_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180225 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) (180225 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block36_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 36 block31 block32 block35 block36 tail)) 180225 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock36FullSourceOnly
