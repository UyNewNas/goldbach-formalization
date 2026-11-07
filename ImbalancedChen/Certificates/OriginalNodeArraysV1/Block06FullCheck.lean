-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no acceptance asserted.
-- ROOT owns installation and strict compilation.
-- Block06 starts at 32769 + 4096*6 = 57345 and ends at 61440.
-- Raw block06 columns are frozen canonical decimal files; hashes are in the CP.
-- Block02Data and Block05Data are expected upstream SOURCEONLY modules, not yet installed or accepted.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block02Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block05Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block06Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock06FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block06_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 0 (by omega) (by decide +kernel))

theorem block06_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 1 (by omega) (by decide +kernel))

theorem block06_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 2 (by omega) (by decide +kernel))

theorem block06_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 3 (by omega) (by decide +kernel))

theorem block06_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 4 (by omega) (by decide +kernel))

theorem block06_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 5 (by omega) (by decide +kernel))

theorem block06_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 6 (by omega) (by decide +kernel))

theorem block06_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 7 (by omega) (by decide +kernel))

theorem block06_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 8 (by omega) (by decide +kernel))

theorem block06_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 9 (by omega) (by decide +kernel))

theorem block06_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 10 (by omega) (by decide +kernel))

theorem block06_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 11 (by omega) (by decide +kernel))

theorem block06_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 12 (by omega) (by decide +kernel))

theorem block06_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 13 (by omega) (by decide +kernel))

theorem block06_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 14 (by omega) (by decide +kernel))

theorem block06_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 15 (by omega) (by decide +kernel))

theorem block06_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 16 (by omega) (by decide +kernel))

theorem block06_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 17 (by omega) (by decide +kernel))

theorem block06_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 18 (by omega) (by decide +kernel))

theorem block06_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 19 (by omega) (by decide +kernel))

theorem block06_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 20 (by omega) (by decide +kernel))

theorem block06_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 21 (by omega) (by decide +kernel))

theorem block06_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 22 (by omega) (by decide +kernel))

theorem block06_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 23 (by omega) (by decide +kernel))

theorem block06_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 24 (by omega) (by decide +kernel))

theorem block06_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 58945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 25 (by omega) (by decide +kernel))

theorem block06_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 26 (by omega) (by decide +kernel))

theorem block06_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 27 (by omega) (by decide +kernel))

theorem block06_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 28 (by omega) (by decide +kernel))

theorem block06_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 29 (by omega) (by decide +kernel))

theorem block06_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 30 (by omega) (by decide +kernel))

theorem block06_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 31 (by omega) (by decide +kernel))

theorem block06_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 32 (by omega) (by decide +kernel))

theorem block06_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 33 (by omega) (by decide +kernel))

theorem block06_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 34 (by omega) (by decide +kernel))

theorem block06_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 35 (by omega) (by decide +kernel))

theorem block06_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 36 (by omega) (by decide +kernel))

theorem block06_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 37 (by omega) (by decide +kernel))

theorem block06_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 38 (by omega) (by decide +kernel))

theorem block06_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 39 (by omega) (by decide +kernel))

theorem block06_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 40 (by omega) (by decide +kernel))

theorem block06_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 59969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 41 (by omega) (by decide +kernel))

theorem block06_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 42 (by omega) (by decide +kernel))

theorem block06_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 43 (by omega) (by decide +kernel))

theorem block06_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 44 (by omega) (by decide +kernel))

theorem block06_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 45 (by omega) (by decide +kernel))

theorem block06_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 46 (by omega) (by decide +kernel))

theorem block06_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 47 (by omega) (by decide +kernel))

theorem block06_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 48 (by omega) (by decide +kernel))

theorem block06_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 49 (by omega) (by decide +kernel))

theorem block06_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 50 (by omega) (by decide +kernel))

theorem block06_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 51 (by omega) (by decide +kernel))

theorem block06_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 52 (by omega) (by decide +kernel))

theorem block06_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 53 (by omega) (by decide +kernel))

theorem block06_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 54 (by omega) (by decide +kernel))

theorem block06_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 55 (by omega) (by decide +kernel))

theorem block06_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 56 (by omega) (by decide +kernel))

theorem block06_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 60993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 57 (by omega) (by decide +kernel))

theorem block06_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 61057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 58 (by omega) (by decide +kernel))

theorem block06_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 61121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 59 (by omega) (by decide +kernel))

theorem block06_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 61185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 60 (by omega) (by decide +kernel))

theorem block06_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 61249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 61 (by omega) (by decide +kernel))

theorem block06_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 61313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 62 (by omega) (by decide +kernel))

theorem block06_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 61377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 6 (by omega) (by omega)
      block01 block02 block05 block06 tail 63 (by omega) (by decide +kernel))

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

theorem block06_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57345 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) (57345 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block06_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 6 block01 block02 block05 block06 tail)) 57345 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock06FullSourceOnly