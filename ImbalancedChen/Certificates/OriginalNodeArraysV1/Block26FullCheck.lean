-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Original block rows 139265..143360; page starts 139265 + 64*p; 64 pages of 64 rows.
-- Uses original delayed slots b-5=21, b-4=22, predecessor b-1=25, current b=26.
-- Actual source snapshot hashes reviewed for this candidate:
-- CheckerCore.lean SHA256 2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
-- DataCore.lean SHA256 ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d
-- Block00Page00Check.lean SHA256 b9c307a4b121b595b1e6f19c0cc88120a61480bf758f312973c07aedd7bda250
-- Block00FullCheck.lean SHA256 31b37cf2d75d1c836cae9d497a735a3947c542875ab4f5559c248de71d71e663
-- Block01FullCheck.lean SHA256 b20dd857aa38cd915a22b2eee6a788896389ee6811f1f6ba1c3e098e7a831a9b
-- DelayedPageTransfer.lean SHA256 2ef2d7dc49f65b2c051c61f9f46534128b35270e5e708fd44f8268e670f14bc0
-- Block21Data.lean and Block22Data.lean and Block25Data.lean are exact planned dependencies; not present in the canonical source tree at authoring time.
-- Block26Data.lean is supplied by the companion candidate.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block21Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block22Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block25Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block26Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock26FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block26_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 0 (by omega) (by decide +kernel))

theorem block26_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 1 (by omega) (by decide +kernel))

theorem block26_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 2 (by omega) (by decide +kernel))

theorem block26_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 3 (by omega) (by decide +kernel))

theorem block26_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 4 (by omega) (by decide +kernel))

theorem block26_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 5 (by omega) (by decide +kernel))

theorem block26_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 6 (by omega) (by decide +kernel))

theorem block26_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 7 (by omega) (by decide +kernel))

theorem block26_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 8 (by omega) (by decide +kernel))

theorem block26_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 9 (by omega) (by decide +kernel))

theorem block26_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 10 (by omega) (by decide +kernel))

theorem block26_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 11 (by omega) (by decide +kernel))

theorem block26_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 12 (by omega) (by decide +kernel))

theorem block26_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 13 (by omega) (by decide +kernel))

theorem block26_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 14 (by omega) (by decide +kernel))

theorem block26_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 15 (by omega) (by decide +kernel))

theorem block26_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 16 (by omega) (by decide +kernel))

theorem block26_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 17 (by omega) (by decide +kernel))

theorem block26_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 18 (by omega) (by decide +kernel))

theorem block26_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 19 (by omega) (by decide +kernel))

theorem block26_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 20 (by omega) (by decide +kernel))

theorem block26_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 21 (by omega) (by decide +kernel))

theorem block26_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 22 (by omega) (by decide +kernel))

theorem block26_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 23 (by omega) (by decide +kernel))

theorem block26_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 24 (by omega) (by decide +kernel))

theorem block26_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 25 (by omega) (by decide +kernel))

theorem block26_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 26 (by omega) (by decide +kernel))

theorem block26_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 140993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 27 (by omega) (by decide +kernel))

theorem block26_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 28 (by omega) (by decide +kernel))

theorem block26_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 29 (by omega) (by decide +kernel))

theorem block26_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 30 (by omega) (by decide +kernel))

theorem block26_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 31 (by omega) (by decide +kernel))

theorem block26_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 32 (by omega) (by decide +kernel))

theorem block26_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 33 (by omega) (by decide +kernel))

theorem block26_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 34 (by omega) (by decide +kernel))

theorem block26_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 35 (by omega) (by decide +kernel))

theorem block26_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 36 (by omega) (by decide +kernel))

theorem block26_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 37 (by omega) (by decide +kernel))

theorem block26_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 38 (by omega) (by decide +kernel))

theorem block26_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 39 (by omega) (by decide +kernel))

theorem block26_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 40 (by omega) (by decide +kernel))

theorem block26_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 41 (by omega) (by decide +kernel))

theorem block26_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 141953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 42 (by omega) (by decide +kernel))

theorem block26_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 43 (by omega) (by decide +kernel))

theorem block26_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 44 (by omega) (by decide +kernel))

theorem block26_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 45 (by omega) (by decide +kernel))

theorem block26_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 46 (by omega) (by decide +kernel))

theorem block26_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 47 (by omega) (by decide +kernel))

theorem block26_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 48 (by omega) (by decide +kernel))

theorem block26_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 49 (by omega) (by decide +kernel))

theorem block26_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 50 (by omega) (by decide +kernel))

theorem block26_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 51 (by omega) (by decide +kernel))

theorem block26_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 52 (by omega) (by decide +kernel))

theorem block26_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 53 (by omega) (by decide +kernel))

theorem block26_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 54 (by omega) (by decide +kernel))

theorem block26_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 55 (by omega) (by decide +kernel))

theorem block26_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 56 (by omega) (by decide +kernel))

theorem block26_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 57 (by omega) (by decide +kernel))

theorem block26_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 142977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 58 (by omega) (by decide +kernel))

theorem block26_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 143041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 59 (by omega) (by decide +kernel))

theorem block26_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 143105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 60 (by omega) (by decide +kernel))

theorem block26_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 143169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 61 (by omega) (by decide +kernel))

theorem block26_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 143233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 62 (by omega) (by decide +kernel))

theorem block26_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 143297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 26 (by omega) (by omega) block21 block22 block25 block26 tail 63 (by omega) (by decide +kernel))

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

theorem block26_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139265 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) (139265 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block26_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 26 block21 block22 block25 block26 tail)) 139265 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock26FullSourceOnly
