-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation and the single compilation queue.
-- Block08 page starts are 65537 + 64*p; the block ends at 69632.
-- Dependencies Block03Data, Block04Data, Block07Data, Block08Data must
-- export block03, block04, block07, block08 : Block in the shared data namespace.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block03Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block04Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block07Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block08Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock08FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block08_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 0 (by omega) (by decide +kernel))

theorem block08_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 1 (by omega) (by decide +kernel))

theorem block08_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 2 (by omega) (by decide +kernel))

theorem block08_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 3 (by omega) (by decide +kernel))

theorem block08_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 4 (by omega) (by decide +kernel))

theorem block08_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 5 (by omega) (by decide +kernel))

theorem block08_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 6 (by omega) (by decide +kernel))

theorem block08_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 7 (by omega) (by decide +kernel))

theorem block08_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 8 (by omega) (by decide +kernel))

theorem block08_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 9 (by omega) (by decide +kernel))

theorem block08_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 10 (by omega) (by decide +kernel))

theorem block08_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 11 (by omega) (by decide +kernel))

theorem block08_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 12 (by omega) (by decide +kernel))

theorem block08_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 13 (by omega) (by decide +kernel))

theorem block08_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 14 (by omega) (by decide +kernel))

theorem block08_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 15 (by omega) (by decide +kernel))

theorem block08_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 16 (by omega) (by decide +kernel))

theorem block08_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 17 (by omega) (by decide +kernel))

theorem block08_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 18 (by omega) (by decide +kernel))

theorem block08_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 19 (by omega) (by decide +kernel))

theorem block08_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 20 (by omega) (by decide +kernel))

theorem block08_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 21 (by omega) (by decide +kernel))

theorem block08_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 66945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 22 (by omega) (by decide +kernel))

theorem block08_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 23 (by omega) (by decide +kernel))

theorem block08_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 24 (by omega) (by decide +kernel))

theorem block08_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 25 (by omega) (by decide +kernel))

theorem block08_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 26 (by omega) (by decide +kernel))

theorem block08_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 27 (by omega) (by decide +kernel))

theorem block08_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 28 (by omega) (by decide +kernel))

theorem block08_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 29 (by omega) (by decide +kernel))

theorem block08_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 30 (by omega) (by decide +kernel))

theorem block08_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 31 (by omega) (by decide +kernel))

theorem block08_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 32 (by omega) (by decide +kernel))

theorem block08_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 33 (by omega) (by decide +kernel))

theorem block08_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 34 (by omega) (by decide +kernel))

theorem block08_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 35 (by omega) (by decide +kernel))

theorem block08_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 36 (by omega) (by decide +kernel))

theorem block08_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 37 (by omega) (by decide +kernel))

theorem block08_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 67969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 38 (by omega) (by decide +kernel))

theorem block08_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 39 (by omega) (by decide +kernel))

theorem block08_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 40 (by omega) (by decide +kernel))

theorem block08_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 41 (by omega) (by decide +kernel))

theorem block08_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 42 (by omega) (by decide +kernel))

theorem block08_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 43 (by omega) (by decide +kernel))

theorem block08_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 44 (by omega) (by decide +kernel))

theorem block08_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 45 (by omega) (by decide +kernel))

theorem block08_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 46 (by omega) (by decide +kernel))

theorem block08_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 47 (by omega) (by decide +kernel))

theorem block08_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 48 (by omega) (by decide +kernel))

theorem block08_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 49 (by omega) (by decide +kernel))

theorem block08_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 50 (by omega) (by decide +kernel))

theorem block08_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 51 (by omega) (by decide +kernel))

theorem block08_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 52 (by omega) (by decide +kernel))

theorem block08_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 53 (by omega) (by decide +kernel))

theorem block08_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 68993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 54 (by omega) (by decide +kernel))

theorem block08_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 55 (by omega) (by decide +kernel))

theorem block08_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 56 (by omega) (by decide +kernel))

theorem block08_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 57 (by omega) (by decide +kernel))

theorem block08_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 58 (by omega) (by decide +kernel))

theorem block08_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 59 (by omega) (by decide +kernel))

theorem block08_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 60 (by omega) (by decide +kernel))

theorem block08_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 61 (by omega) (by decide +kernel))

theorem block08_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 62 (by omega) (by decide +kernel))

theorem block08_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 69569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 8 (by omega) (by omega) block03 block04 block07 block08 tail 63 (by omega) (by decide +kernel))

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

theorem block08_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65537 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) (65537 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block08_page63_checked tail
  simpa only [Nat.reduceMul] using
    (readCheckBlock_of_64_page_count
      (assembledRead (windowBlocks 8 block03 block04 block07 block08 tail)) 65537 64 hpages)

end ImbalancedChen.OriginalU2StoredNodeBlock08FullSourceOnly
