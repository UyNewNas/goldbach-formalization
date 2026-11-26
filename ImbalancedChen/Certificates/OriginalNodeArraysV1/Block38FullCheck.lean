-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- Page starts: 188417 + 64*p for p=0..63; the block ends at 192512.
-- Frozen page checks use the closed reference table from DelayedPageTransfer.
-- Canonical supplier CheckerCore.lean SHA256 2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
-- Canonical supplier Block00Page00Check.lean SHA256 b9c307a4b121b595b1e6f19c0cc88120a61480bf758f312973c07aedd7bda250
-- Canonical supplier DelayedPageTransfer.lean SHA256 2ef2d7dc49f65b2c051c61f9f46534128b35270e5e708fd44f8268e670f14bc0
-- Canonical supplier Block01FullCheck.lean SHA256 b20dd857aa38cd915a22b2eee6a788896389ee6811f1f6ba1c3e098e7a831a9b
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block33Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block34Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block37Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block38Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock38FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block38_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 0 (by omega) (by decide +kernel))

theorem block38_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 1 (by omega) (by decide +kernel))

theorem block38_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 2 (by omega) (by decide +kernel))

theorem block38_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 3 (by omega) (by decide +kernel))

theorem block38_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 4 (by omega) (by decide +kernel))

theorem block38_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 5 (by omega) (by decide +kernel))

theorem block38_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 6 (by omega) (by decide +kernel))

theorem block38_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 7 (by omega) (by decide +kernel))

theorem block38_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 8 (by omega) (by decide +kernel))

theorem block38_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 9 (by omega) (by decide +kernel))

theorem block38_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 10 (by omega) (by decide +kernel))

theorem block38_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 11 (by omega) (by decide +kernel))

theorem block38_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 12 (by omega) (by decide +kernel))

theorem block38_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 13 (by omega) (by decide +kernel))

theorem block38_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 14 (by omega) (by decide +kernel))

theorem block38_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 15 (by omega) (by decide +kernel))

theorem block38_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 16 (by omega) (by decide +kernel))

theorem block38_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 17 (by omega) (by decide +kernel))

theorem block38_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 18 (by omega) (by decide +kernel))

theorem block38_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 19 (by omega) (by decide +kernel))

theorem block38_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 20 (by omega) (by decide +kernel))

theorem block38_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 21 (by omega) (by decide +kernel))

theorem block38_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 22 (by omega) (by decide +kernel))

theorem block38_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 23 (by omega) (by decide +kernel))

theorem block38_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 189953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 24 (by omega) (by decide +kernel))

theorem block38_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 25 (by omega) (by decide +kernel))

theorem block38_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 26 (by omega) (by decide +kernel))

theorem block38_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 27 (by omega) (by decide +kernel))

theorem block38_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 28 (by omega) (by decide +kernel))

theorem block38_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 29 (by omega) (by decide +kernel))

theorem block38_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 30 (by omega) (by decide +kernel))

theorem block38_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 31 (by omega) (by decide +kernel))

theorem block38_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 32 (by omega) (by decide +kernel))

theorem block38_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 33 (by omega) (by decide +kernel))

theorem block38_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 34 (by omega) (by decide +kernel))

theorem block38_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 35 (by omega) (by decide +kernel))

theorem block38_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 36 (by omega) (by decide +kernel))

theorem block38_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 37 (by omega) (by decide +kernel))

theorem block38_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 38 (by omega) (by decide +kernel))

theorem block38_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 39 (by omega) (by decide +kernel))

theorem block38_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 190977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 40 (by omega) (by decide +kernel))

theorem block38_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 41 (by omega) (by decide +kernel))

theorem block38_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 42 (by omega) (by decide +kernel))

theorem block38_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 43 (by omega) (by decide +kernel))

theorem block38_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 44 (by omega) (by decide +kernel))

theorem block38_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 45 (by omega) (by decide +kernel))

theorem block38_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 46 (by omega) (by decide +kernel))

theorem block38_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 47 (by omega) (by decide +kernel))

theorem block38_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 48 (by omega) (by decide +kernel))

theorem block38_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 49 (by omega) (by decide +kernel))

theorem block38_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 50 (by omega) (by decide +kernel))

theorem block38_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 51 (by omega) (by decide +kernel))

theorem block38_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 52 (by omega) (by decide +kernel))

theorem block38_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 53 (by omega) (by decide +kernel))

theorem block38_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 54 (by omega) (by decide +kernel))

theorem block38_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 191937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 55 (by omega) (by decide +kernel))

theorem block38_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 56 (by omega) (by decide +kernel))

theorem block38_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 57 (by omega) (by decide +kernel))

theorem block38_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 58 (by omega) (by decide +kernel))

theorem block38_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 59 (by omega) (by decide +kernel))

theorem block38_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 60 (by omega) (by decide +kernel))

theorem block38_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 61 (by omega) (by decide +kernel))

theorem block38_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 62 (by omega) (by decide +kernel))

theorem block38_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 192449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 38 (by omega) (by omega) block33 block34 block37 block38 tail 63 (by omega) (by decide +kernel))

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

 theorem block38_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188417 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) (188417 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block38_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 38 block33 block34 block37 block38 tail)) 188417 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock38FullSourceOnly
