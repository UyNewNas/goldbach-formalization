-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 53249 + 64*p; rows 53249..57344 (4096 total).
-- The delayed window for b=5 uses boundary=block00, delayed=block01,
-- prev=block04, current=block05; the Block04 first-row prefix case is
-- established in the existing delayed transfer API and remains unchanged.
-- Block00Data.lean SHA256 078a7959c4aa7d162efbd66bd83d025ae10d5599b7c9490ac8df165f4774904c
-- Block00FullCheck.lean SHA256 31b37cf2d75d1c836cae9d497a735a3947c542875ab4f5559c248de71d71e663
-- Block00Page00Check.lean SHA256 b9c307a4b121b595b1e6f19c0cc88120a61480bf758f312973c07aedd7bda250
-- Block00Window.lean SHA256 aeb52f77451dd1c7bfa6af1e200d63baa9a9109c99063125b4a3178a9c5be07d
-- Block01Data.lean SHA256 707ed0026d02a286da0675e31f2c3470b548b34bcf63da5ad9da4e09205dff78
-- Block01FullCheck.lean SHA256 b20dd857aa38cd915a22b2eee6a788896389ee6811f1f6ba1c3e098e7a831a9b
-- CheckerCore.lean SHA256 2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
-- DataCore.lean SHA256 ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d
-- DelayedPageTransfer.lean SHA256 2ef2d7dc49f65b2c051c61f9f46534128b35270e5e708fd44f8268e670f14bc0
-- InitialPrefix.lean SHA256 c7ee982a8f447d944ff1cb4307e0d7513056b504f5e2826d5f03b0e5d2ac18a7
-- Block05Data.lean.txt SHA256 d7850280a2f6f276ad3d202044e526e14cc672fa567bb03e779f20d1d2b3f913
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block04Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block05Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock05FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block05_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*0) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 0 (by omega) (by decide +kernel))
theorem block05_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*1) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 1 (by omega) (by decide +kernel))
theorem block05_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*2) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 2 (by omega) (by decide +kernel))
theorem block05_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*3) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 3 (by omega) (by decide +kernel))
theorem block05_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*4) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 4 (by omega) (by decide +kernel))
theorem block05_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*5) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 5 (by omega) (by decide +kernel))
theorem block05_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*6) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 6 (by omega) (by decide +kernel))
theorem block05_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*7) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 7 (by omega) (by decide +kernel))
theorem block05_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*8) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 8 (by omega) (by decide +kernel))
theorem block05_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*9) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 9 (by omega) (by decide +kernel))
theorem block05_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*10) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 10 (by omega) (by decide +kernel))
theorem block05_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*11) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 11 (by omega) (by decide +kernel))
theorem block05_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*12) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 12 (by omega) (by decide +kernel))
theorem block05_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*13) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 13 (by omega) (by decide +kernel))
theorem block05_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*14) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 14 (by omega) (by decide +kernel))
theorem block05_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*15) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 15 (by omega) (by decide +kernel))
theorem block05_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*16) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 16 (by omega) (by decide +kernel))
theorem block05_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*17) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 17 (by omega) (by decide +kernel))
theorem block05_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*18) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 18 (by omega) (by decide +kernel))
theorem block05_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*19) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 19 (by omega) (by decide +kernel))
theorem block05_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*20) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 20 (by omega) (by decide +kernel))
theorem block05_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*21) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 21 (by omega) (by decide +kernel))
theorem block05_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*22) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 22 (by omega) (by decide +kernel))
theorem block05_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*23) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 23 (by omega) (by decide +kernel))
theorem block05_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*24) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 24 (by omega) (by decide +kernel))
theorem block05_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*25) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 25 (by omega) (by decide +kernel))
theorem block05_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*26) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 26 (by omega) (by decide +kernel))
theorem block05_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*27) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 27 (by omega) (by decide +kernel))
theorem block05_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*28) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 28 (by omega) (by decide +kernel))
theorem block05_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*29) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 29 (by omega) (by decide +kernel))
theorem block05_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*30) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 30 (by omega) (by decide +kernel))
theorem block05_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*31) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 31 (by omega) (by decide +kernel))
theorem block05_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*32) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 32 (by omega) (by decide +kernel))
theorem block05_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*33) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 33 (by omega) (by decide +kernel))
theorem block05_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*34) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 34 (by omega) (by decide +kernel))
theorem block05_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*35) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 35 (by omega) (by decide +kernel))
theorem block05_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*36) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 36 (by omega) (by decide +kernel))
theorem block05_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*37) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 37 (by omega) (by decide +kernel))
theorem block05_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*38) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 38 (by omega) (by decide +kernel))
theorem block05_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*39) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 39 (by omega) (by decide +kernel))
theorem block05_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*40) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 40 (by omega) (by decide +kernel))
theorem block05_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*41) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 41 (by omega) (by decide +kernel))
theorem block05_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*42) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 42 (by omega) (by decide +kernel))
theorem block05_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*43) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 43 (by omega) (by decide +kernel))
theorem block05_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*44) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 44 (by omega) (by decide +kernel))
theorem block05_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*45) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 45 (by omega) (by decide +kernel))
theorem block05_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*46) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 46 (by omega) (by decide +kernel))
theorem block05_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*47) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 47 (by omega) (by decide +kernel))
theorem block05_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*48) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 48 (by omega) (by decide +kernel))
theorem block05_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*49) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 49 (by omega) (by decide +kernel))
theorem block05_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*50) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 50 (by omega) (by decide +kernel))
theorem block05_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*51) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 51 (by omega) (by decide +kernel))
theorem block05_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*52) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 52 (by omega) (by decide +kernel))
theorem block05_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*53) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 53 (by omega) (by decide +kernel))
theorem block05_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*54) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 54 (by omega) (by decide +kernel))
theorem block05_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*55) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 55 (by omega) (by decide +kernel))
theorem block05_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*56) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 56 (by omega) (by decide +kernel))
theorem block05_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*57) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 57 (by omega) (by decide +kernel))
theorem block05_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*58) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 58 (by omega) (by decide +kernel))
theorem block05_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*59) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 59 (by omega) (by decide +kernel))
theorem block05_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*60) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 60 (by omega) (by decide +kernel))
theorem block05_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*61) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 61 (by omega) (by decide +kernel))
theorem block05_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*62) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 62 (by omega) (by decide +kernel))
theorem block05_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*63) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 5 (by omega) (by omega)
      block00 block01 block04 block05 tail 63 (by omega) (by decide +kernel))

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

theorem block05_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) 53249 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) (53249 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block05_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 5 block00 block01 block04 block05 tail)) 53249 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock05FullSourceOnly
