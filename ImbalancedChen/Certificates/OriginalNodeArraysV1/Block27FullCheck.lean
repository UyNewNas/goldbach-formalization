-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Exact block27 source interval: 143361..147456; 64 pages of 64 steps.
-- windowBlocks slots: boundary=22, delayed=23, previous=26, current=27.
-- DataCore.lean SHA256 ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d
-- CheckerCore.lean SHA256 2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
-- Block00Data.lean SHA256 078a7959c4aa7d162efbd66bd83d025ae10d5599b7c9490ac8df165f4774904c
-- Block01Data.lean SHA256 707ed0026d02a286da0675e31f2c3470b548b34bcf63da5ad9da4e09205dff78
-- Block00Page00Check.lean SHA256 b9c307a4b121b595b1e6f19c0cc88120a61480bf758f312973c07aedd7bda250
-- Block00Window.lean SHA256 aeb52f77451dd1c7bfa6af1e200d63baa9a9109c99063125b4a3178a9c5be07d
-- Block00FullCheck.lean SHA256 31b37cf2d75d1c836cae9d497a735a3947c542875ab4f5559c248de71d71e663
-- Block01FullCheck.lean SHA256 b20dd857aa38cd915a22b2eee6a788896389ee6811f1f6ba1c3e098e7a831a9b
-- PageTransfer.lean SHA256 8812a76d1e1ee8fbadbe4e8ed4de71c359fb7841cd598f47e5c6b5bc0eefee95
-- DelayedPageTransfer.lean SHA256 2ef2d7dc49f65b2c051c61f9f46534128b35270e5e708fd44f8268e670f14bc0
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block22Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block23Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block26Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block27Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock27FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block27_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 0 (by omega)
      (by decide +kernel))

theorem block27_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 1 (by omega)
      (by decide +kernel))

theorem block27_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 2 (by omega)
      (by decide +kernel))

theorem block27_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 3 (by omega)
      (by decide +kernel))

theorem block27_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 4 (by omega)
      (by decide +kernel))

theorem block27_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 5 (by omega)
      (by decide +kernel))

theorem block27_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 6 (by omega)
      (by decide +kernel))

theorem block27_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 7 (by omega)
      (by decide +kernel))

theorem block27_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 8 (by omega)
      (by decide +kernel))

theorem block27_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 9 (by omega)
      (by decide +kernel))

theorem block27_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 10 (by omega)
      (by decide +kernel))

theorem block27_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 11 (by omega)
      (by decide +kernel))

theorem block27_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 12 (by omega)
      (by decide +kernel))

theorem block27_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 13 (by omega)
      (by decide +kernel))

theorem block27_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 14 (by omega)
      (by decide +kernel))

theorem block27_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 15 (by omega)
      (by decide +kernel))

theorem block27_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 16 (by omega)
      (by decide +kernel))

theorem block27_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 17 (by omega)
      (by decide +kernel))

theorem block27_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 18 (by omega)
      (by decide +kernel))

theorem block27_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 19 (by omega)
      (by decide +kernel))

theorem block27_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 20 (by omega)
      (by decide +kernel))

theorem block27_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 21 (by omega)
      (by decide +kernel))

theorem block27_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 22 (by omega)
      (by decide +kernel))

theorem block27_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 23 (by omega)
      (by decide +kernel))

theorem block27_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 24 (by omega)
      (by decide +kernel))

theorem block27_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 144961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 25 (by omega)
      (by decide +kernel))

theorem block27_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 26 (by omega)
      (by decide +kernel))

theorem block27_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 27 (by omega)
      (by decide +kernel))

theorem block27_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 28 (by omega)
      (by decide +kernel))

theorem block27_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 29 (by omega)
      (by decide +kernel))

theorem block27_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 30 (by omega)
      (by decide +kernel))

theorem block27_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 31 (by omega)
      (by decide +kernel))

theorem block27_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 32 (by omega)
      (by decide +kernel))

theorem block27_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 33 (by omega)
      (by decide +kernel))

theorem block27_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 34 (by omega)
      (by decide +kernel))

theorem block27_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 35 (by omega)
      (by decide +kernel))

theorem block27_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 36 (by omega)
      (by decide +kernel))

theorem block27_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 37 (by omega)
      (by decide +kernel))

theorem block27_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 38 (by omega)
      (by decide +kernel))

theorem block27_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 39 (by omega)
      (by decide +kernel))

theorem block27_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 40 (by omega)
      (by decide +kernel))

theorem block27_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 145985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 41 (by omega)
      (by decide +kernel))

theorem block27_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 42 (by omega)
      (by decide +kernel))

theorem block27_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 43 (by omega)
      (by decide +kernel))

theorem block27_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 44 (by omega)
      (by decide +kernel))

theorem block27_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 45 (by omega)
      (by decide +kernel))

theorem block27_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 46 (by omega)
      (by decide +kernel))

theorem block27_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 47 (by omega)
      (by decide +kernel))

theorem block27_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 48 (by omega)
      (by decide +kernel))

theorem block27_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 49 (by omega)
      (by decide +kernel))

theorem block27_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 50 (by omega)
      (by decide +kernel))

theorem block27_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 51 (by omega)
      (by decide +kernel))

theorem block27_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 52 (by omega)
      (by decide +kernel))

theorem block27_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 53 (by omega)
      (by decide +kernel))

theorem block27_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 54 (by omega)
      (by decide +kernel))

theorem block27_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 55 (by omega)
      (by decide +kernel))

theorem block27_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 146945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 56 (by omega)
      (by decide +kernel))

theorem block27_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 147009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 57 (by omega)
      (by decide +kernel))

theorem block27_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 147073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 58 (by omega)
      (by decide +kernel))

theorem block27_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 147137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 59 (by omega)
      (by decide +kernel))

theorem block27_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 147201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 60 (by omega)
      (by decide +kernel))

theorem block27_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 147265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 61 (by omega)
      (by decide +kernel))

theorem block27_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 147329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 62 (by omega)
      (by decide +kernel))

theorem block27_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 147393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 27 (by omega) (by omega)
      block22 block23 block26 block27 tail 63 (by omega)
      (by decide +kernel))

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

theorem block27_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143361 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) (143361 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block27_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 27 block22 block23 block26 block27 tail)) 143361 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock27FullSourceOnly
