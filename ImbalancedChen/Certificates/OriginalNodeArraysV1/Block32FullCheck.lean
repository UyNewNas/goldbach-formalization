-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Original block rows 163841..167936; page start = 163841 + 64*p; 64 pages of 64 steps.
-- Delayed slots b-5=27, b-4=28; predecessor b-1=31 and current b=32.
-- Block27Data/28Data/31Data are planned names only; absent from the canonical source tree at authoring time.
-- Block32Data is supplied by companion Block32Data.lean.txt.
-- CheckerCore.lean SHA256 2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
-- DataCore.lean SHA256 ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d
-- Block00Page00Check.lean SHA256 b9c307a4b121b595b1e6f19c0cc88120a61480bf758f312973c07aedd7bda250
-- Block00FullCheck.lean SHA256 31b37cf2d75d1c836cae9d497a735a3947c542875ab4f5559c248de71d71e663
-- Block01FullCheck.lean SHA256 b20dd857aa38cd915a22b2eee6a788896389ee6811f1f6ba1c3e098e7a831a9b
-- DelayedPageTransfer.lean SHA256 2ef2d7dc49f65b2c051c61f9f46534128b35270e5e708fd44f8268e670f14bc0
-- Block27Data.lean SHA256 absent; planned contract: import DataCore; namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly; def block27 : NodeTree 12, 4096 rows in source order.
-- Block28Data.lean SHA256 absent; planned contract: import DataCore; namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly; def block28 : NodeTree 12, 4096 rows in source order.
-- Block31Data.lean SHA256 absent; planned contract: import DataCore; namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly; def block31 : NodeTree 12, 4096 rows in source order.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block27Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block28Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block31Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block32Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock32FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block32_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 163841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 0 (by omega) (by decide +kernel))

theorem block32_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 163905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 1 (by omega) (by decide +kernel))

theorem block32_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 163969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 2 (by omega) (by decide +kernel))

theorem block32_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 3 (by omega) (by decide +kernel))

theorem block32_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 4 (by omega) (by decide +kernel))

theorem block32_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 5 (by omega) (by decide +kernel))

theorem block32_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 6 (by omega) (by decide +kernel))

theorem block32_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 7 (by omega) (by decide +kernel))

theorem block32_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 8 (by omega) (by decide +kernel))

theorem block32_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 9 (by omega) (by decide +kernel))

theorem block32_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 10 (by omega) (by decide +kernel))

theorem block32_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 11 (by omega) (by decide +kernel))

theorem block32_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 12 (by omega) (by decide +kernel))

theorem block32_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 13 (by omega) (by decide +kernel))

theorem block32_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 14 (by omega) (by decide +kernel))

theorem block32_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 15 (by omega) (by decide +kernel))

theorem block32_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 16 (by omega) (by decide +kernel))

theorem block32_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 17 (by omega) (by decide +kernel))

theorem block32_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 164993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 18 (by omega) (by decide +kernel))

theorem block32_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 19 (by omega) (by decide +kernel))

theorem block32_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 20 (by omega) (by decide +kernel))

theorem block32_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 21 (by omega) (by decide +kernel))

theorem block32_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 22 (by omega) (by decide +kernel))

theorem block32_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 23 (by omega) (by decide +kernel))

theorem block32_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 24 (by omega) (by decide +kernel))

theorem block32_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 25 (by omega) (by decide +kernel))

theorem block32_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 26 (by omega) (by decide +kernel))

theorem block32_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 27 (by omega) (by decide +kernel))

theorem block32_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 28 (by omega) (by decide +kernel))

theorem block32_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 29 (by omega) (by decide +kernel))

theorem block32_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 30 (by omega) (by decide +kernel))

theorem block32_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 31 (by omega) (by decide +kernel))

theorem block32_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 32 (by omega) (by decide +kernel))

theorem block32_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 165953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 33 (by omega) (by decide +kernel))

theorem block32_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 34 (by omega) (by decide +kernel))

theorem block32_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 35 (by omega) (by decide +kernel))

theorem block32_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 36 (by omega) (by decide +kernel))

theorem block32_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 37 (by omega) (by decide +kernel))

theorem block32_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 38 (by omega) (by decide +kernel))

theorem block32_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 39 (by omega) (by decide +kernel))

theorem block32_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 40 (by omega) (by decide +kernel))

theorem block32_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 41 (by omega) (by decide +kernel))

theorem block32_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 42 (by omega) (by decide +kernel))

theorem block32_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 43 (by omega) (by decide +kernel))

theorem block32_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 44 (by omega) (by decide +kernel))

theorem block32_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 45 (by omega) (by decide +kernel))

theorem block32_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 46 (by omega) (by decide +kernel))

theorem block32_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 47 (by omega) (by decide +kernel))

theorem block32_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 48 (by omega) (by decide +kernel))

theorem block32_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 166977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 49 (by omega) (by decide +kernel))

theorem block32_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 50 (by omega) (by decide +kernel))

theorem block32_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 51 (by omega) (by decide +kernel))

theorem block32_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 52 (by omega) (by decide +kernel))

theorem block32_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 53 (by omega) (by decide +kernel))

theorem block32_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 54 (by omega) (by decide +kernel))

theorem block32_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 55 (by omega) (by decide +kernel))

theorem block32_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 56 (by omega) (by decide +kernel))

theorem block32_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 57 (by omega) (by decide +kernel))

theorem block32_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 58 (by omega) (by decide +kernel))

theorem block32_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 59 (by omega) (by decide +kernel))

theorem block32_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 60 (by omega) (by decide +kernel))

theorem block32_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 61 (by omega) (by decide +kernel))

theorem block32_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 62 (by omega) (by decide +kernel))

theorem block32_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 167873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 32 (by omega) (by omega) block27 block28 block31 block32 tail 63 (by omega) (by decide +kernel))

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

theorem block32_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 163841 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) (163841 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block32_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 32 block27 block28 block31 block32 tail)) 163841 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock32FullSourceOnly
