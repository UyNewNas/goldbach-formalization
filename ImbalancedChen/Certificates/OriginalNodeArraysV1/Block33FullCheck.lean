-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*33 + 64*p; full block ends at 172032.
-- Physical window slots in order: boundary Block28, delayed Block29, prev Block32, current Block33.
-- Block04 prefix saturation does not apply to Block33; indices are interior to the frozen update range.
-- Frozen source input: manifest SHA256 c9528798da192706cedbfca63222dfc9b635577e566de1f8129705789916189d
-- block-33.Llo.dec SHA256 a94f61cc0aee24dfc5be8bebbd80a1ab1bfa2b326b990f4c8eeb8b4dfa3fb31f
-- block-33.Lhi.dec SHA256 9d6b7518815afe8420217b65d910ef8888913764129e299fa4e54570b4a525c8
-- block-33.Hlo.dec SHA256 05c37f3f577647e51791095da95c700384dda246a69c1880219ec5d34668a49a
-- block-33.Hhi.dec SHA256 811389c3ef1ed62082b5c9f1b3c95b3fbf0eedc54e9ef7d4304b9e32ca896da4
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block28Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block29Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block32Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block33Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock33FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block33_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 167937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 0 (by omega) (by decide +kernel))

theorem block33_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 1 (by omega) (by decide +kernel))

theorem block33_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 2 (by omega) (by decide +kernel))

theorem block33_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 3 (by omega) (by decide +kernel))

theorem block33_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 4 (by omega) (by decide +kernel))

theorem block33_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 5 (by omega) (by decide +kernel))

theorem block33_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 6 (by omega) (by decide +kernel))

theorem block33_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 7 (by omega) (by decide +kernel))

theorem block33_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 8 (by omega) (by decide +kernel))

theorem block33_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 9 (by omega) (by decide +kernel))

theorem block33_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 10 (by omega) (by decide +kernel))

theorem block33_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 11 (by omega) (by decide +kernel))

theorem block33_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 12 (by omega) (by decide +kernel))

theorem block33_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 13 (by omega) (by decide +kernel))

theorem block33_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 14 (by omega) (by decide +kernel))

theorem block33_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 15 (by omega) (by decide +kernel))

theorem block33_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 168961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 16 (by omega) (by decide +kernel))

theorem block33_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 17 (by omega) (by decide +kernel))

theorem block33_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 18 (by omega) (by decide +kernel))

theorem block33_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 19 (by omega) (by decide +kernel))

theorem block33_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 20 (by omega) (by decide +kernel))

theorem block33_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 21 (by omega) (by decide +kernel))

theorem block33_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 22 (by omega) (by decide +kernel))

theorem block33_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 23 (by omega) (by decide +kernel))

theorem block33_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 24 (by omega) (by decide +kernel))

theorem block33_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 25 (by omega) (by decide +kernel))

theorem block33_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 26 (by omega) (by decide +kernel))

theorem block33_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 27 (by omega) (by decide +kernel))

theorem block33_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 28 (by omega) (by decide +kernel))

theorem block33_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 29 (by omega) (by decide +kernel))

theorem block33_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 30 (by omega) (by decide +kernel))

theorem block33_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 31 (by omega) (by decide +kernel))

theorem block33_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 169985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 32 (by omega) (by decide +kernel))

theorem block33_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 33 (by omega) (by decide +kernel))

theorem block33_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 34 (by omega) (by decide +kernel))

theorem block33_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 35 (by omega) (by decide +kernel))

theorem block33_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 36 (by omega) (by decide +kernel))

theorem block33_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 37 (by omega) (by decide +kernel))

theorem block33_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 38 (by omega) (by decide +kernel))

theorem block33_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 39 (by omega) (by decide +kernel))

theorem block33_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 40 (by omega) (by decide +kernel))

theorem block33_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 41 (by omega) (by decide +kernel))

theorem block33_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 42 (by omega) (by decide +kernel))

theorem block33_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 43 (by omega) (by decide +kernel))

theorem block33_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 44 (by omega) (by decide +kernel))

theorem block33_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 45 (by omega) (by decide +kernel))

theorem block33_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 46 (by omega) (by decide +kernel))

theorem block33_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 170945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 47 (by omega) (by decide +kernel))

theorem block33_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 48 (by omega) (by decide +kernel))

theorem block33_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 49 (by omega) (by decide +kernel))

theorem block33_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 50 (by omega) (by decide +kernel))

theorem block33_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 51 (by omega) (by decide +kernel))

theorem block33_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 52 (by omega) (by decide +kernel))

theorem block33_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 53 (by omega) (by decide +kernel))

theorem block33_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 54 (by omega) (by decide +kernel))

theorem block33_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 55 (by omega) (by decide +kernel))

theorem block33_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 56 (by omega) (by decide +kernel))

theorem block33_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 57 (by omega) (by decide +kernel))

theorem block33_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 58 (by omega) (by decide +kernel))

theorem block33_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 59 (by omega) (by decide +kernel))

theorem block33_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 60 (by omega) (by decide +kernel))

theorem block33_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 61 (by omega) (by decide +kernel))

theorem block33_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 62 (by omega) (by decide +kernel))

theorem block33_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 171969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 33 (by omega) (by omega)
      block28 block29 block32 block33 tail 63 (by omega) (by decide +kernel))

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

theorem block33_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 167937 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) (167937 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block33_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 33 block28 block29 block32 block33 tail)) 167937 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock33FullSourceOnly
