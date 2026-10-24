-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Block30 page starts are 155649+64*p (p = 0..63); covered range ends at 159744.
-- Every page uses the actual four-slot delayed-window equality transfer and closes its 64 rows with ordinary `by decide +kernel`.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block25Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block26Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block29Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block30Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock30FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block30_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 0 (by omega) (by decide +kernel))

theorem block30_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 1 (by omega) (by decide +kernel))

theorem block30_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 2 (by omega) (by decide +kernel))

theorem block30_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 3 (by omega) (by decide +kernel))

theorem block30_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 4 (by omega) (by decide +kernel))

theorem block30_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 5 (by omega) (by decide +kernel))

theorem block30_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 6 (by omega) (by decide +kernel))

theorem block30_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 7 (by omega) (by decide +kernel))

theorem block30_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 8 (by omega) (by decide +kernel))

theorem block30_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 9 (by omega) (by decide +kernel))

theorem block30_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 10 (by omega) (by decide +kernel))

theorem block30_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 11 (by omega) (by decide +kernel))

theorem block30_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 12 (by omega) (by decide +kernel))

theorem block30_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 13 (by omega) (by decide +kernel))

theorem block30_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 14 (by omega) (by decide +kernel))

theorem block30_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 15 (by omega) (by decide +kernel))

theorem block30_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 16 (by omega) (by decide +kernel))

theorem block30_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 17 (by omega) (by decide +kernel))

theorem block30_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 18 (by omega) (by decide +kernel))

theorem block30_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 19 (by omega) (by decide +kernel))

theorem block30_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 20 (by omega) (by decide +kernel))

theorem block30_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 156993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 21 (by omega) (by decide +kernel))

theorem block30_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 22 (by omega) (by decide +kernel))

theorem block30_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 23 (by omega) (by decide +kernel))

theorem block30_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 24 (by omega) (by decide +kernel))

theorem block30_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 25 (by omega) (by decide +kernel))

theorem block30_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 26 (by omega) (by decide +kernel))

theorem block30_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 27 (by omega) (by decide +kernel))

theorem block30_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 28 (by omega) (by decide +kernel))

theorem block30_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 29 (by omega) (by decide +kernel))

theorem block30_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 30 (by omega) (by decide +kernel))

theorem block30_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 31 (by omega) (by decide +kernel))

theorem block30_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 32 (by omega) (by decide +kernel))

theorem block30_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 33 (by omega) (by decide +kernel))

theorem block30_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 34 (by omega) (by decide +kernel))

theorem block30_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 35 (by omega) (by decide +kernel))

theorem block30_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 157953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 36 (by omega) (by decide +kernel))

theorem block30_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 37 (by omega) (by decide +kernel))

theorem block30_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 38 (by omega) (by decide +kernel))

theorem block30_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 39 (by omega) (by decide +kernel))

theorem block30_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 40 (by omega) (by decide +kernel))

theorem block30_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 41 (by omega) (by decide +kernel))

theorem block30_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 42 (by omega) (by decide +kernel))

theorem block30_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 43 (by omega) (by decide +kernel))

theorem block30_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 44 (by omega) (by decide +kernel))

theorem block30_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 45 (by omega) (by decide +kernel))

theorem block30_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 46 (by omega) (by decide +kernel))

theorem block30_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 47 (by omega) (by decide +kernel))

theorem block30_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 48 (by omega) (by decide +kernel))

theorem block30_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 49 (by omega) (by decide +kernel))

theorem block30_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 50 (by omega) (by decide +kernel))

theorem block30_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 51 (by omega) (by decide +kernel))

theorem block30_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 158977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 52 (by omega) (by decide +kernel))

theorem block30_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 53 (by omega) (by decide +kernel))

theorem block30_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 54 (by omega) (by decide +kernel))

theorem block30_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 55 (by omega) (by decide +kernel))

theorem block30_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 56 (by omega) (by decide +kernel))

theorem block30_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 57 (by omega) (by decide +kernel))

theorem block30_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 58 (by omega) (by decide +kernel))

theorem block30_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 59 (by omega) (by decide +kernel))

theorem block30_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 60 (by omega) (by decide +kernel))

theorem block30_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 61 (by omega) (by decide +kernel))

theorem block30_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 62 (by omega) (by decide +kernel))

theorem block30_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 159681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 30 (by omega) (by omega)
      block25 block26 block29 block30 tail 63 (by omega) (by decide +kernel))

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

theorem block30_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155649 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) (155649 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block30_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 30 block25 block26 block29 block30 tail)) 155649 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock30FullSourceOnly
