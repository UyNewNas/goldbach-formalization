-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*12 + 64*p; full block rows81921..86016.
-- Raw artifact inputs: frozen manifest SHA256 c9528798da192706cedbfca63222dfc9b635577e566de1f8129705789916189d
-- raw Llo: block-12.Llo.dec; bytes=143360; rows=81921..86016; sha256=52efde4f985954d101a47bfca054eec9d913f482b966a9234b2dfcba6c5f418c
-- raw Lhi: block-12.Lhi.dec; bytes=143360; rows=81921..86016; sha256=493cc6bbe429ae2c367c14b5b488d246fec4fc5eef416e2ea7b8f3eaa5fe20a8
-- raw Hlo: block-12.Hlo.dec; bytes=143360; rows=81921..86016; sha256=f7b7e25bfde7690dfd0334daa1960c8c3f4a5abdafe64237cf9e7a73352f848e
-- raw Hhi: block-12.Hhi.dec; bytes=143360; rows=81921..86016; sha256=7cace30615e4fcd1bc9e4aaae231b3cccae8d622e10d559a933836969035f6e7
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block07Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block08Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block11Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block12Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock12FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block12_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 81921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 0 (by omega) (by decide +kernel))

theorem block12_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 81985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 1 (by omega) (by decide +kernel))

theorem block12_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 2 (by omega) (by decide +kernel))

theorem block12_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 3 (by omega) (by decide +kernel))

theorem block12_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 4 (by omega) (by decide +kernel))

theorem block12_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 5 (by omega) (by decide +kernel))

theorem block12_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 6 (by omega) (by decide +kernel))

theorem block12_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 7 (by omega) (by decide +kernel))

theorem block12_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 8 (by omega) (by decide +kernel))

theorem block12_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 9 (by omega) (by decide +kernel))

theorem block12_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 10 (by omega) (by decide +kernel))

theorem block12_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 11 (by omega) (by decide +kernel))

theorem block12_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 12 (by omega) (by decide +kernel))

theorem block12_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 13 (by omega) (by decide +kernel))

theorem block12_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 14 (by omega) (by decide +kernel))

theorem block12_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 15 (by omega) (by decide +kernel))

theorem block12_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 82945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 16 (by omega) (by decide +kernel))

theorem block12_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 17 (by omega) (by decide +kernel))

theorem block12_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 18 (by omega) (by decide +kernel))

theorem block12_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 19 (by omega) (by decide +kernel))

theorem block12_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 20 (by omega) (by decide +kernel))

theorem block12_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 21 (by omega) (by decide +kernel))

theorem block12_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 22 (by omega) (by decide +kernel))

theorem block12_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 23 (by omega) (by decide +kernel))

theorem block12_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 24 (by omega) (by decide +kernel))

theorem block12_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 25 (by omega) (by decide +kernel))

theorem block12_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 26 (by omega) (by decide +kernel))

theorem block12_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 27 (by omega) (by decide +kernel))

theorem block12_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 28 (by omega) (by decide +kernel))

theorem block12_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 29 (by omega) (by decide +kernel))

theorem block12_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 30 (by omega) (by decide +kernel))

theorem block12_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 31 (by omega) (by decide +kernel))

theorem block12_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 83969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 32 (by omega) (by decide +kernel))

theorem block12_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 33 (by omega) (by decide +kernel))

theorem block12_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 34 (by omega) (by decide +kernel))

theorem block12_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 35 (by omega) (by decide +kernel))

theorem block12_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 36 (by omega) (by decide +kernel))

theorem block12_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 37 (by omega) (by decide +kernel))

theorem block12_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 38 (by omega) (by decide +kernel))

theorem block12_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 39 (by omega) (by decide +kernel))

theorem block12_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 40 (by omega) (by decide +kernel))

theorem block12_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 41 (by omega) (by decide +kernel))

theorem block12_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 42 (by omega) (by decide +kernel))

theorem block12_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 43 (by omega) (by decide +kernel))

theorem block12_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 44 (by omega) (by decide +kernel))

theorem block12_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 45 (by omega) (by decide +kernel))

theorem block12_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 46 (by omega) (by decide +kernel))

theorem block12_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 47 (by omega) (by decide +kernel))

theorem block12_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 84993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 48 (by omega) (by decide +kernel))

theorem block12_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 49 (by omega) (by decide +kernel))

theorem block12_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 50 (by omega) (by decide +kernel))

theorem block12_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 51 (by omega) (by decide +kernel))

theorem block12_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 52 (by omega) (by decide +kernel))

theorem block12_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 53 (by omega) (by decide +kernel))

theorem block12_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 54 (by omega) (by decide +kernel))

theorem block12_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 55 (by omega) (by decide +kernel))

theorem block12_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 56 (by omega) (by decide +kernel))

theorem block12_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 57 (by omega) (by decide +kernel))

theorem block12_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 58 (by omega) (by decide +kernel))

theorem block12_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 59 (by omega) (by decide +kernel))

theorem block12_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 60 (by omega) (by decide +kernel))

theorem block12_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 61 (by omega) (by decide +kernel))

theorem block12_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 62 (by omega) (by decide +kernel))

theorem block12_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 85953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 12 (by omega) (by omega)
      block07 block08 block11 block12 tail 63 (by omega) (by decide +kernel))

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

theorem block12_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 81921 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) (81921 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block12_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 12 block07 block08 block11 block12 tail)) 81921 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock12FullSourceOnly
