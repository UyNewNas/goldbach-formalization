-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- Page starts: 32769 + 4096*2 + 64*p; the block covers rows 40961..45056.
-- Block01Data.lean SHA256 707ed0026d02a286da0675e31f2c3470b548b34bcf63da5ad9da4e09205dff78
-- Block02Data.lean.txt SHA256 40e23fff27ffd385c4c1f0a8e0858989bfba4646e1d9aec1a3815df8d40170fa
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block02Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.PageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock02FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredPageTransferSourceOnly

theorem block02_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 40961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 0 (by omega) (by decide +kernel))

theorem block02_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 1 (by omega) (by decide +kernel))

theorem block02_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 2 (by omega) (by decide +kernel))

theorem block02_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 3 (by omega) (by decide +kernel))

theorem block02_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 4 (by omega) (by decide +kernel))

theorem block02_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 5 (by omega) (by decide +kernel))

theorem block02_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 6 (by omega) (by decide +kernel))

theorem block02_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 7 (by omega) (by decide +kernel))

theorem block02_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 8 (by omega) (by decide +kernel))

theorem block02_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 9 (by omega) (by decide +kernel))

theorem block02_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 10 (by omega) (by decide +kernel))

theorem block02_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 11 (by omega) (by decide +kernel))

theorem block02_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 12 (by omega) (by decide +kernel))

theorem block02_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 13 (by omega) (by decide +kernel))

theorem block02_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 14 (by omega) (by decide +kernel))

theorem block02_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 15 (by omega) (by decide +kernel))

theorem block02_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 41985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 16 (by omega) (by decide +kernel))

theorem block02_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 17 (by omega) (by decide +kernel))

theorem block02_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 18 (by omega) (by decide +kernel))

theorem block02_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 19 (by omega) (by decide +kernel))

theorem block02_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 20 (by omega) (by decide +kernel))

theorem block02_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 21 (by omega) (by decide +kernel))

theorem block02_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 22 (by omega) (by decide +kernel))

theorem block02_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 23 (by omega) (by decide +kernel))

theorem block02_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 24 (by omega) (by decide +kernel))

theorem block02_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 25 (by omega) (by decide +kernel))

theorem block02_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 26 (by omega) (by decide +kernel))

theorem block02_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 27 (by omega) (by decide +kernel))

theorem block02_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 28 (by omega) (by decide +kernel))

theorem block02_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 29 (by omega) (by decide +kernel))

theorem block02_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 30 (by omega) (by decide +kernel))

theorem block02_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 42945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 31 (by omega) (by decide +kernel))

theorem block02_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 32 (by omega) (by decide +kernel))

theorem block02_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 33 (by omega) (by decide +kernel))

theorem block02_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 34 (by omega) (by decide +kernel))

theorem block02_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 35 (by omega) (by decide +kernel))

theorem block02_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 36 (by omega) (by decide +kernel))

theorem block02_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 37 (by omega) (by decide +kernel))

theorem block02_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 38 (by omega) (by decide +kernel))

theorem block02_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 39 (by omega) (by decide +kernel))

theorem block02_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 40 (by omega) (by decide +kernel))

theorem block02_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 41 (by omega) (by decide +kernel))

theorem block02_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 42 (by omega) (by decide +kernel))

theorem block02_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 43 (by omega) (by decide +kernel))

theorem block02_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 44 (by omega) (by decide +kernel))

theorem block02_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 45 (by omega) (by decide +kernel))

theorem block02_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 46 (by omega) (by decide +kernel))

theorem block02_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 43969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 47 (by omega) (by decide +kernel))

theorem block02_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 48 (by omega) (by decide +kernel))

theorem block02_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 49 (by omega) (by decide +kernel))

theorem block02_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 50 (by omega) (by decide +kernel))

theorem block02_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 51 (by omega) (by decide +kernel))

theorem block02_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 52 (by omega) (by decide +kernel))

theorem block02_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 53 (by omega) (by decide +kernel))

theorem block02_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 54 (by omega) (by decide +kernel))

theorem block02_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 55 (by omega) (by decide +kernel))

theorem block02_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 56 (by omega) (by decide +kernel))

theorem block02_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 57 (by omega) (by decide +kernel))

theorem block02_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 58 (by omega) (by decide +kernel))

theorem block02_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 59 (by omega) (by decide +kernel))

theorem block02_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 60 (by omega) (by decide +kernel))

theorem block02_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 61 (by omega) (by decide +kernel))

theorem block02_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 62 (by omega) (by decide +kernel))

theorem block02_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 44993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 2 (by omega) (by omega) block01 block02 tail 63 (by omega) (by decide +kernel))

/-- Generic exact assembly of any finite run of 64-row page checks.
This proves the conjunction of supplied page checks without evaluating rows. -/
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

theorem block02_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 40961 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowPrevCurrent 2 block01 block02 tail)) (40961 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block02_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowPrevCurrent 2 block01 block02 tail)) 40961 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock02FullSourceOnly
