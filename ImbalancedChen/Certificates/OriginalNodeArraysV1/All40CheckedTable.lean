-- SOURCEONLY / UNCOMPILED / NOT PASS / OPEN30. No final C closure claim.
-- Proposed installation: ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable
-- V2: every Block00..39 interface below was read from the concrete source listed in contracts.json.
-- Blocks02..39 imports still require ROOT installation/acceptance, including independent patches19/37.
-- Namespace is retained for compatibility with earlier source-only consumers.
-- ROOT alone may install/compile after every prerequisite becomes actual and accepted.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Window
import ImbalancedChen.Certificates.OriginalNodeArraysV1.PageTransfer
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer
import ImbalancedChen.Certificates.OriginalNodeArraysV1.InitialPrefix
import ImbalancedChen.ActualThirdOriginalStoredNodeQueryLookup
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block02Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block02FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block03Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block03FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block04Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block04FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block05Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block05FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block06Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block06FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block07Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block07FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block08Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block08FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block09Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block09FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block10Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block10FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block11Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block11FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block12Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block12FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block13Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block13FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block14Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block14FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block15Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block15FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block16Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block16FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block17Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block17FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block18Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block18FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block19Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block19FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block20Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block20FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block21Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block21FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block22Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block22FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block23Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block23FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block24Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block24FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block25Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block25FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block26Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block26FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block27Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block27FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block28Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block28FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block29Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block29FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block30Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block30FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block31Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block31FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block32Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block32FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block33Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block33FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block34Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block34FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block35Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block35FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block36Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block36FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block37Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block37FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block38Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block38FullCheck
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block39Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block39FullCheck

namespace ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredPageTransferSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly
open ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly
open ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

/-- Exactly one immutable selector for every theorem below. Slots 0..39
select the exact imported constants, with no re-emission or alternate values.
The fallback does not certify any index outside the stored domain. -/
noncomputable def literalBlocks : Nat → Block
  | 0 => block00
  | 1 => block01
  | 2 => block02
  | 3 => block03
  | 4 => block04
  | 5 => block05
  | 6 => block06
  | 7 => block07
  | 8 => block08
  | 9 => block09
  | 10 => block10
  | 11 => block11
  | 12 => block12
  | 13 => block13
  | 14 => block14
  | 15 => block15
  | 16 => block16
  | 17 => block17
  | 18 => block18
  | 19 => block19
  | 20 => block20
  | 21 => block21
  | 22 => block22
  | 23 => block23
  | 24 => block24
  | 25 => block25
  | 26 => block26
  | 27 => block27
  | 28 => block28
  | 29 => block29
  | 30 => block30
  | 31 => block31
  | 32 => block32
  | 33 => block33
  | 34 => block34
  | 35 => block35
  | 36 => block36
  | 37 => block37
  | 38 => block38
  | 39 => block39
  | _ => block00

/-- Definitional binding of every physical table slot to its imported public data. -/
theorem literalBlocks_slot00 : literalBlocks 0 = block00 := rfl

theorem literalBlocks_slot01 : literalBlocks 1 = block01 := rfl

theorem literalBlocks_slot02 : literalBlocks 2 = block02 := rfl

theorem literalBlocks_slot03 : literalBlocks 3 = block03 := rfl

theorem literalBlocks_slot04 : literalBlocks 4 = block04 := rfl

theorem literalBlocks_slot05 : literalBlocks 5 = block05 := rfl

theorem literalBlocks_slot06 : literalBlocks 6 = block06 := rfl

theorem literalBlocks_slot07 : literalBlocks 7 = block07 := rfl

theorem literalBlocks_slot08 : literalBlocks 8 = block08 := rfl

theorem literalBlocks_slot09 : literalBlocks 9 = block09 := rfl

theorem literalBlocks_slot10 : literalBlocks 10 = block10 := rfl

theorem literalBlocks_slot11 : literalBlocks 11 = block11 := rfl

theorem literalBlocks_slot12 : literalBlocks 12 = block12 := rfl

theorem literalBlocks_slot13 : literalBlocks 13 = block13 := rfl

theorem literalBlocks_slot14 : literalBlocks 14 = block14 := rfl

theorem literalBlocks_slot15 : literalBlocks 15 = block15 := rfl

theorem literalBlocks_slot16 : literalBlocks 16 = block16 := rfl

theorem literalBlocks_slot17 : literalBlocks 17 = block17 := rfl

theorem literalBlocks_slot18 : literalBlocks 18 = block18 := rfl

theorem literalBlocks_slot19 : literalBlocks 19 = block19 := rfl

theorem literalBlocks_slot20 : literalBlocks 20 = block20 := rfl

theorem literalBlocks_slot21 : literalBlocks 21 = block21 := rfl

theorem literalBlocks_slot22 : literalBlocks 22 = block22 := rfl

theorem literalBlocks_slot23 : literalBlocks 23 = block23 := rfl

theorem literalBlocks_slot24 : literalBlocks 24 = block24 := rfl

theorem literalBlocks_slot25 : literalBlocks 25 = block25 := rfl

theorem literalBlocks_slot26 : literalBlocks 26 = block26 := rfl

theorem literalBlocks_slot27 : literalBlocks 27 = block27 := rfl

theorem literalBlocks_slot28 : literalBlocks 28 = block28 := rfl

theorem literalBlocks_slot29 : literalBlocks 29 = block29 := rfl

theorem literalBlocks_slot30 : literalBlocks 30 = block30 := rfl

theorem literalBlocks_slot31 : literalBlocks 31 = block31 := rfl

theorem literalBlocks_slot32 : literalBlocks 32 = block32 := rfl

theorem literalBlocks_slot33 : literalBlocks 33 = block33 := rfl

theorem literalBlocks_slot34 : literalBlocks 34 = block34 := rfl

theorem literalBlocks_slot35 : literalBlocks 35 = block35 := rfl

theorem literalBlocks_slot36 : literalBlocks 36 = block36 := rfl

theorem literalBlocks_slot37 : literalBlocks 37 = block37 := rfl

theorem literalBlocks_slot38 : literalBlocks 38 = block38 := rfl

theorem literalBlocks_slot39 : literalBlocks 39 = block39 := rfl

/-- Prefix semantics is structural and separate from every update check. -/
theorem literalBlocks_prefix_semantics (i : Nat) (hi : i ≤ 32768) :
    assembledRead literalBlocks i = initialNode := by
  exact readCheckPrefix_sound (assembledRead_prefix_checked literalBlocks) hi

/-- The first delayed input of Block04 is exactly prefix row32768. -/
theorem literalBlocks_first_delayed_is_prefix :
    assembledRead literalBlocks (32769+4096*4-16385) = integerInitial := by
  apply assembledRead_prefix
  omega
/-- The actual prefix decoder agrees with this same immutable reader. The
external artifact byte correspondence is not asserted by this theorem. -/
theorem literalBlocks_prefix_decoder (i : Nat) (hi : i ≤ 32768) :
    ImbalancedChen.OriginalU2InitialPrefix20261024uSourceOnly.decodeRowAt
      ImbalancedChen.OriginalU2InitialPrefix20261024uSourceOnly.canonicalPrefix i =
      some (assembledRawRead literalBlocks i) := by
  exact ImbalancedChen.OriginalU2InitialPrefix20261024uSourceOnly.assembledRawRead_prefix_correspondence
    literalBlocks i hi

/-- Block00 uses its existing single-slot window. -/
theorem literalBlocks_window00 : window00 literalBlocks = literalBlocks := by
  exact window00_eq_self literalBlocks (by rfl)

theorem literalBlocks_window01 :
    windowPrevCurrent 1 block00 block01 literalBlocks = literalBlocks := by
  exact windowPrevCurrent_eq_self 1 block00 block01 literalBlocks
    (by rfl) (by rfl)

theorem literalBlocks_window02 :
    windowPrevCurrent 2 block01 block02 literalBlocks = literalBlocks := by
  exact windowPrevCurrent_eq_self 2 block01 block02 literalBlocks
    (by rfl) (by rfl)

theorem literalBlocks_window03 :
    windowPrevCurrent 3 block02 block03 literalBlocks = literalBlocks := by
  exact windowPrevCurrent_eq_self 3 block02 block03 literalBlocks
    (by rfl) (by rfl)

theorem literalBlocks_window04 :
    windowBlocks 4 block00 block00 block03 block04 literalBlocks =
      literalBlocks := by
  change windowBlocks 4 (literalBlocks (4-5)) (literalBlocks (4-4))
    (literalBlocks (4-1)) (literalBlocks 4) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 4 literalBlocks

theorem literalBlocks_window05 :
    windowBlocks 5 block00 block01 block04 block05 literalBlocks =
      literalBlocks := by
  change windowBlocks 5 (literalBlocks (5-5)) (literalBlocks (5-4))
    (literalBlocks (5-1)) (literalBlocks 5) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 5 literalBlocks

theorem literalBlocks_window06 :
    windowBlocks 6 block01 block02 block05 block06 literalBlocks =
      literalBlocks := by
  change windowBlocks 6 (literalBlocks (6-5)) (literalBlocks (6-4))
    (literalBlocks (6-1)) (literalBlocks 6) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 6 literalBlocks

theorem literalBlocks_window07 :
    windowBlocks 7 block02 block03 block06 block07 literalBlocks =
      literalBlocks := by
  change windowBlocks 7 (literalBlocks (7-5)) (literalBlocks (7-4))
    (literalBlocks (7-1)) (literalBlocks 7) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 7 literalBlocks

theorem literalBlocks_window08 :
    windowBlocks 8 block03 block04 block07 block08 literalBlocks =
      literalBlocks := by
  change windowBlocks 8 (literalBlocks (8-5)) (literalBlocks (8-4))
    (literalBlocks (8-1)) (literalBlocks 8) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 8 literalBlocks

theorem literalBlocks_window09 :
    windowBlocks 9 block04 block05 block08 block09 literalBlocks =
      literalBlocks := by
  change windowBlocks 9 (literalBlocks (9-5)) (literalBlocks (9-4))
    (literalBlocks (9-1)) (literalBlocks 9) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 9 literalBlocks

theorem literalBlocks_window10 :
    windowBlocks 10 block05 block06 block09 block10 literalBlocks =
      literalBlocks := by
  change windowBlocks 10 (literalBlocks (10-5)) (literalBlocks (10-4))
    (literalBlocks (10-1)) (literalBlocks 10) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 10 literalBlocks

theorem literalBlocks_window11 :
    windowBlocks 11 block06 block07 block10 block11 literalBlocks =
      literalBlocks := by
  change windowBlocks 11 (literalBlocks (11-5)) (literalBlocks (11-4))
    (literalBlocks (11-1)) (literalBlocks 11) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 11 literalBlocks

theorem literalBlocks_window12 :
    windowBlocks 12 block07 block08 block11 block12 literalBlocks =
      literalBlocks := by
  change windowBlocks 12 (literalBlocks (12-5)) (literalBlocks (12-4))
    (literalBlocks (12-1)) (literalBlocks 12) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 12 literalBlocks

theorem literalBlocks_window13 :
    windowBlocks 13 block08 block09 block12 block13 literalBlocks =
      literalBlocks := by
  change windowBlocks 13 (literalBlocks (13-5)) (literalBlocks (13-4))
    (literalBlocks (13-1)) (literalBlocks 13) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 13 literalBlocks

theorem literalBlocks_window14 :
    windowBlocks 14 block09 block10 block13 block14 literalBlocks =
      literalBlocks := by
  change windowBlocks 14 (literalBlocks (14-5)) (literalBlocks (14-4))
    (literalBlocks (14-1)) (literalBlocks 14) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 14 literalBlocks

theorem literalBlocks_window15 :
    windowBlocks 15 block10 block11 block14 block15 literalBlocks =
      literalBlocks := by
  change windowBlocks 15 (literalBlocks (15-5)) (literalBlocks (15-4))
    (literalBlocks (15-1)) (literalBlocks 15) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 15 literalBlocks

theorem literalBlocks_window16 :
    windowBlocks 16 block11 block12 block15 block16 literalBlocks =
      literalBlocks := by
  change windowBlocks 16 (literalBlocks (16-5)) (literalBlocks (16-4))
    (literalBlocks (16-1)) (literalBlocks 16) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 16 literalBlocks

theorem literalBlocks_window17 :
    windowBlocks 17 block12 block13 block16 block17 literalBlocks =
      literalBlocks := by
  change windowBlocks 17 (literalBlocks (17-5)) (literalBlocks (17-4))
    (literalBlocks (17-1)) (literalBlocks 17) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 17 literalBlocks

theorem literalBlocks_window18 :
    windowBlocks 18 block13 block14 block17 block18 literalBlocks =
      literalBlocks := by
  change windowBlocks 18 (literalBlocks (18-5)) (literalBlocks (18-4))
    (literalBlocks (18-1)) (literalBlocks 18) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 18 literalBlocks

theorem literalBlocks_window19 :
    windowBlocks 19 block14 block15 block18 block19 literalBlocks =
      literalBlocks := by
  change windowBlocks 19 (literalBlocks (19-5)) (literalBlocks (19-4))
    (literalBlocks (19-1)) (literalBlocks 19) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 19 literalBlocks

theorem literalBlocks_window20 :
    windowBlocks 20 block15 block16 block19 block20 literalBlocks =
      literalBlocks := by
  change windowBlocks 20 (literalBlocks (20-5)) (literalBlocks (20-4))
    (literalBlocks (20-1)) (literalBlocks 20) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 20 literalBlocks

theorem literalBlocks_window21 :
    windowBlocks 21 block16 block17 block20 block21 literalBlocks =
      literalBlocks := by
  change windowBlocks 21 (literalBlocks (21-5)) (literalBlocks (21-4))
    (literalBlocks (21-1)) (literalBlocks 21) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 21 literalBlocks

theorem literalBlocks_window22 :
    windowBlocks 22 block17 block18 block21 block22 literalBlocks =
      literalBlocks := by
  change windowBlocks 22 (literalBlocks (22-5)) (literalBlocks (22-4))
    (literalBlocks (22-1)) (literalBlocks 22) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 22 literalBlocks

theorem literalBlocks_window23 :
    windowBlocks 23 block18 block19 block22 block23 literalBlocks =
      literalBlocks := by
  change windowBlocks 23 (literalBlocks (23-5)) (literalBlocks (23-4))
    (literalBlocks (23-1)) (literalBlocks 23) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 23 literalBlocks

theorem literalBlocks_window24 :
    windowBlocks 24 block19 block20 block23 block24 literalBlocks =
      literalBlocks := by
  change windowBlocks 24 (literalBlocks (24-5)) (literalBlocks (24-4))
    (literalBlocks (24-1)) (literalBlocks 24) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 24 literalBlocks

theorem literalBlocks_window25 :
    windowBlocks 25 block20 block21 block24 block25 literalBlocks =
      literalBlocks := by
  change windowBlocks 25 (literalBlocks (25-5)) (literalBlocks (25-4))
    (literalBlocks (25-1)) (literalBlocks 25) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 25 literalBlocks

theorem literalBlocks_window26 :
    windowBlocks 26 block21 block22 block25 block26 literalBlocks =
      literalBlocks := by
  change windowBlocks 26 (literalBlocks (26-5)) (literalBlocks (26-4))
    (literalBlocks (26-1)) (literalBlocks 26) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 26 literalBlocks

theorem literalBlocks_window27 :
    windowBlocks 27 block22 block23 block26 block27 literalBlocks =
      literalBlocks := by
  change windowBlocks 27 (literalBlocks (27-5)) (literalBlocks (27-4))
    (literalBlocks (27-1)) (literalBlocks 27) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 27 literalBlocks

theorem literalBlocks_window28 :
    windowBlocks 28 block23 block24 block27 block28 literalBlocks =
      literalBlocks := by
  change windowBlocks 28 (literalBlocks (28-5)) (literalBlocks (28-4))
    (literalBlocks (28-1)) (literalBlocks 28) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 28 literalBlocks

theorem literalBlocks_window29 :
    windowBlocks 29 block24 block25 block28 block29 literalBlocks =
      literalBlocks := by
  change windowBlocks 29 (literalBlocks (29-5)) (literalBlocks (29-4))
    (literalBlocks (29-1)) (literalBlocks 29) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 29 literalBlocks

theorem literalBlocks_window30 :
    windowBlocks 30 block25 block26 block29 block30 literalBlocks =
      literalBlocks := by
  change windowBlocks 30 (literalBlocks (30-5)) (literalBlocks (30-4))
    (literalBlocks (30-1)) (literalBlocks 30) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 30 literalBlocks

theorem literalBlocks_window31 :
    windowBlocks 31 block26 block27 block30 block31 literalBlocks =
      literalBlocks := by
  change windowBlocks 31 (literalBlocks (31-5)) (literalBlocks (31-4))
    (literalBlocks (31-1)) (literalBlocks 31) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 31 literalBlocks

theorem literalBlocks_window32 :
    windowBlocks 32 block27 block28 block31 block32 literalBlocks =
      literalBlocks := by
  change windowBlocks 32 (literalBlocks (32-5)) (literalBlocks (32-4))
    (literalBlocks (32-1)) (literalBlocks 32) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 32 literalBlocks

theorem literalBlocks_window33 :
    windowBlocks 33 block28 block29 block32 block33 literalBlocks =
      literalBlocks := by
  change windowBlocks 33 (literalBlocks (33-5)) (literalBlocks (33-4))
    (literalBlocks (33-1)) (literalBlocks 33) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 33 literalBlocks

theorem literalBlocks_window34 :
    windowBlocks 34 block29 block30 block33 block34 literalBlocks =
      literalBlocks := by
  change windowBlocks 34 (literalBlocks (34-5)) (literalBlocks (34-4))
    (literalBlocks (34-1)) (literalBlocks 34) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 34 literalBlocks

theorem literalBlocks_window35 :
    windowBlocks 35 block30 block31 block34 block35 literalBlocks =
      literalBlocks := by
  change windowBlocks 35 (literalBlocks (35-5)) (literalBlocks (35-4))
    (literalBlocks (35-1)) (literalBlocks 35) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 35 literalBlocks

theorem literalBlocks_window36 :
    windowBlocks 36 block31 block32 block35 block36 literalBlocks =
      literalBlocks := by
  change windowBlocks 36 (literalBlocks (36-5)) (literalBlocks (36-4))
    (literalBlocks (36-1)) (literalBlocks 36) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 36 literalBlocks

theorem literalBlocks_window37 :
    windowBlocks 37 block32 block33 block36 block37 literalBlocks =
      literalBlocks := by
  change windowBlocks 37 (literalBlocks (37-5)) (literalBlocks (37-4))
    (literalBlocks (37-1)) (literalBlocks 37) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 37 literalBlocks

theorem literalBlocks_window38 :
    windowBlocks 38 block33 block34 block37 block38 literalBlocks =
      literalBlocks := by
  change windowBlocks 38 (literalBlocks (38-5)) (literalBlocks (38-4))
    (literalBlocks (38-1)) (literalBlocks 38) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 38 literalBlocks

theorem literalBlocks_window39 :
    windowBlocks 39 block34 block35 block38 block39 literalBlocks =
      literalBlocks := by
  change windowBlocks 39 (literalBlocks (39-5)) (literalBlocks (39-4))
    (literalBlocks (39-1)) (literalBlocks 39) literalBlocks = literalBlocks
  exact windowBlocks_eq_original 39 literalBlocks

/-- The actual imported ABIs are used: Block24/31 demand the one table and
four definitional slot equalities; the other 38 export a frozen-window theorem
with an arbitrary tail, instantiated at this table and rewritten by its proved
window equality. No full-check proposition is assumed. -/

theorem literalBlocks_block00_checked :
    readCheckBlock (assembledRead literalBlocks) 32769 4096 = true := by
  simpa only [literalBlocks_window00] using
    (ImbalancedChen.OriginalU2StoredNodeBlock00FullSourceOnly.block00_all_pages_checked
      literalBlocks)

theorem literalBlocks_block01_checked :
    readCheckBlock (assembledRead literalBlocks) 36865 4096 = true := by
  simpa only [literalBlocks_window01] using
    (ImbalancedChen.OriginalU2StoredNodeBlock01FullSourceOnly.block01_all_pages_checked
      literalBlocks)

theorem literalBlocks_block02_checked :
    readCheckBlock (assembledRead literalBlocks) 40961 4096 = true := by
  simpa only [literalBlocks_window02] using
    (ImbalancedChen.OriginalU2StoredNodeBlock02FullSourceOnly.block02_all_pages_checked
      literalBlocks)

theorem literalBlocks_block03_checked :
    readCheckBlock (assembledRead literalBlocks) 45057 4096 = true := by
  simpa only [literalBlocks_window03] using
    (ImbalancedChen.OriginalU2StoredNodeBlock03FullSourceOnly.block03_all_pages_checked
      literalBlocks)

theorem literalBlocks_block04_checked :
    readCheckBlock (assembledRead literalBlocks) 49153 4096 = true := by
  simpa only [literalBlocks_window04] using
    (ImbalancedChen.OriginalU2StoredNodeBlock04FullSourceOnly.block04_all_pages_checked
      literalBlocks)

theorem literalBlocks_block05_checked :
    readCheckBlock (assembledRead literalBlocks) 53249 4096 = true := by
  simpa only [literalBlocks_window05] using
    (ImbalancedChen.OriginalU2StoredNodeBlock05FullSourceOnly.block05_all_pages_checked
      literalBlocks)

theorem literalBlocks_block06_checked :
    readCheckBlock (assembledRead literalBlocks) 57345 4096 = true := by
  simpa only [literalBlocks_window06] using
    (ImbalancedChen.OriginalU2StoredNodeBlock06FullSourceOnly.block06_all_pages_checked
      literalBlocks)

theorem literalBlocks_block07_checked :
    readCheckBlock (assembledRead literalBlocks) 61441 4096 = true := by
  simpa only [literalBlocks_window07] using
    (ImbalancedChen.OriginalU2StoredNodeBlock07FullSourceOnly.block07_all_pages_checked
      literalBlocks)

theorem literalBlocks_block08_checked :
    readCheckBlock (assembledRead literalBlocks) 65537 4096 = true := by
  simpa only [literalBlocks_window08] using
    (ImbalancedChen.OriginalU2StoredNodeBlock08FullSourceOnly.block08_all_pages_checked
      literalBlocks)

theorem literalBlocks_block09_checked :
    readCheckBlock (assembledRead literalBlocks) 69633 4096 = true := by
  simpa only [literalBlocks_window09] using
    (ImbalancedChen.OriginalU2StoredNodeBlock09FullSourceOnly.block09_all_pages_checked
      literalBlocks)

theorem literalBlocks_block10_checked :
    readCheckBlock (assembledRead literalBlocks) 73729 4096 = true := by
  simpa only [literalBlocks_window10] using
    (ImbalancedChen.OriginalU2StoredNodeBlock10FullSourceOnly.block10_all_pages_checked
      literalBlocks)

theorem literalBlocks_block11_checked :
    readCheckBlock (assembledRead literalBlocks) 77825 4096 = true := by
  simpa only [literalBlocks_window11] using
    (ImbalancedChen.OriginalU2StoredNodeBlock11FullSourceOnly.block11_all_pages_checked
      literalBlocks)

theorem literalBlocks_block12_checked :
    readCheckBlock (assembledRead literalBlocks) 81921 4096 = true := by
  simpa only [literalBlocks_window12] using
    (ImbalancedChen.OriginalU2StoredNodeBlock12FullSourceOnly.block12_all_pages_checked
      literalBlocks)

theorem literalBlocks_block13_checked :
    readCheckBlock (assembledRead literalBlocks) 86017 4096 = true := by
  simpa only [literalBlocks_window13] using
    (ImbalancedChen.OriginalU2StoredNodeBlock13FullSourceOnly.block13_all_pages_checked
      literalBlocks)

theorem literalBlocks_block14_checked :
    readCheckBlock (assembledRead literalBlocks) 90113 4096 = true := by
  simpa only [literalBlocks_window14] using
    (ImbalancedChen.OriginalU2StoredNodeBlock14FullSourceOnly.block14_all_pages_checked
      literalBlocks)

theorem literalBlocks_block15_checked :
    readCheckBlock (assembledRead literalBlocks) 94209 4096 = true := by
  simpa only [literalBlocks_window15] using
    (ImbalancedChen.OriginalU2StoredNodeBlock15FullSourceOnly.block15_all_pages_checked
      literalBlocks)

theorem literalBlocks_block16_checked :
    readCheckBlock (assembledRead literalBlocks) 98305 4096 = true := by
  simpa only [literalBlocks_window16] using
    (ImbalancedChen.OriginalU2StoredNodeBlock16FullSourceOnly.block16_all_pages_checked
      literalBlocks)

theorem literalBlocks_block17_checked :
    readCheckBlock (assembledRead literalBlocks) 102401 4096 = true := by
  simpa only [literalBlocks_window17] using
    (ImbalancedChen.OriginalU2StoredNodeBlock17FullSourceOnly.block17_all_pages_checked
      literalBlocks)

theorem literalBlocks_block18_checked :
    readCheckBlock (assembledRead literalBlocks) 106497 4096 = true := by
  simpa only [literalBlocks_window18] using
    (ImbalancedChen.OriginalU2StoredNodeBlock18FullSourceOnly.block18_all_pages_checked
      literalBlocks)

theorem literalBlocks_block19_checked :
    readCheckBlock (assembledRead literalBlocks) 110593 4096 = true := by
  simpa only [literalBlocks_window19] using
    (ImbalancedChen.OriginalU2StoredNodeBlock19FullSourceOnly.block19_all_pages_checked
      literalBlocks)

theorem literalBlocks_block20_checked :
    readCheckBlock (assembledRead literalBlocks) 114689 4096 = true := by
  simpa only [literalBlocks_window20] using
    (ImbalancedChen.OriginalU2StoredNodeBlock20FullSourceOnly.block20_all_pages_checked
      literalBlocks)

theorem literalBlocks_block21_checked :
    readCheckBlock (assembledRead literalBlocks) 118785 4096 = true := by
  simpa only [literalBlocks_window21] using
    (ImbalancedChen.OriginalU2StoredNodeBlock21FullSourceOnly.block21_all_pages_checked
      literalBlocks)

theorem literalBlocks_block22_checked :
    readCheckBlock (assembledRead literalBlocks) 122881 4096 = true := by
  simpa only [literalBlocks_window22] using
    (ImbalancedChen.OriginalU2StoredNodeBlock22FullSourceOnly.block22_all_pages_checked
      literalBlocks)

theorem literalBlocks_block23_checked :
    readCheckBlock (assembledRead literalBlocks) 126977 4096 = true := by
  simpa only [literalBlocks_window23] using
    (ImbalancedChen.OriginalU2StoredNodeBlock23FullSourceOnly.block23_all_pages_checked
      literalBlocks)

theorem literalBlocks_block24_checked :
    readCheckBlock (assembledRead literalBlocks) 131073 4096 = true := by
  exact ImbalancedChen.OriginalU2StoredNodeBlock24FullSourceOnly.block24_all_pages_checked
    literalBlocks literalBlocks_slot19 literalBlocks_slot20 literalBlocks_slot23 literalBlocks_slot24

theorem literalBlocks_block25_checked :
    readCheckBlock (assembledRead literalBlocks) 135169 4096 = true := by
  simpa only [literalBlocks_window25] using
    (ImbalancedChen.OriginalU2StoredNodeBlock25FullSourceOnly.block25_all_pages_checked
      literalBlocks)

theorem literalBlocks_block26_checked :
    readCheckBlock (assembledRead literalBlocks) 139265 4096 = true := by
  simpa only [literalBlocks_window26] using
    (ImbalancedChen.OriginalU2StoredNodeBlock26FullSourceOnly.block26_all_pages_checked
      literalBlocks)

theorem literalBlocks_block27_checked :
    readCheckBlock (assembledRead literalBlocks) 143361 4096 = true := by
  simpa only [literalBlocks_window27] using
    (ImbalancedChen.OriginalU2StoredNodeBlock27FullSourceOnly.block27_all_pages_checked
      literalBlocks)

theorem literalBlocks_block28_checked :
    readCheckBlock (assembledRead literalBlocks) 147457 4096 = true := by
  simpa only [literalBlocks_window28] using
    (ImbalancedChen.OriginalU2StoredNodeBlock28FullSourceOnly.block28_all_pages_checked
      literalBlocks)

theorem literalBlocks_block29_checked :
    readCheckBlock (assembledRead literalBlocks) 151553 4096 = true := by
  simpa only [literalBlocks_window29] using
    (ImbalancedChen.OriginalU2StoredNodeBlock29FullSourceOnly.block29_all_pages_checked
      literalBlocks)

theorem literalBlocks_block30_checked :
    readCheckBlock (assembledRead literalBlocks) 155649 4096 = true := by
  simpa only [literalBlocks_window30] using
    (ImbalancedChen.OriginalU2StoredNodeBlock30FullSourceOnly.block30_all_pages_checked
      literalBlocks)

theorem literalBlocks_block31_checked :
    readCheckBlock (assembledRead literalBlocks) 159745 4096 = true := by
  exact ImbalancedChen.OriginalU2StoredNodeBlock31FullSourceOnly.block31_all_pages_checked
    literalBlocks literalBlocks_slot26 literalBlocks_slot27 literalBlocks_slot30 literalBlocks_slot31

theorem literalBlocks_block32_checked :
    readCheckBlock (assembledRead literalBlocks) 163841 4096 = true := by
  simpa only [literalBlocks_window32] using
    (ImbalancedChen.OriginalU2StoredNodeBlock32FullSourceOnly.block32_all_pages_checked
      literalBlocks)

theorem literalBlocks_block33_checked :
    readCheckBlock (assembledRead literalBlocks) 167937 4096 = true := by
  simpa only [literalBlocks_window33] using
    (ImbalancedChen.OriginalU2StoredNodeBlock33FullSourceOnly.block33_all_pages_checked
      literalBlocks)

theorem literalBlocks_block34_checked :
    readCheckBlock (assembledRead literalBlocks) 172033 4096 = true := by
  simpa only [literalBlocks_window34] using
    (ImbalancedChen.OriginalU2StoredNodeBlock34FullSourceOnly.block34_all_pages_checked
      literalBlocks)

theorem literalBlocks_block35_checked :
    readCheckBlock (assembledRead literalBlocks) 176129 4096 = true := by
  simpa only [literalBlocks_window35] using
    (ImbalancedChen.OriginalU2StoredNodeBlock35FullSourceOnly.block35_all_pages_checked
      literalBlocks)

theorem literalBlocks_block36_checked :
    readCheckBlock (assembledRead literalBlocks) 180225 4096 = true := by
  simpa only [literalBlocks_window36] using
    (ImbalancedChen.OriginalU2StoredNodeBlock36FullSourceOnly.block36_all_pages_checked
      literalBlocks)

theorem literalBlocks_block37_checked :
    readCheckBlock (assembledRead literalBlocks) 184321 4096 = true := by
  simpa only [literalBlocks_window37] using
    (ImbalancedChen.OriginalU2StoredNodeBlock37FullSourceOnly.block37_all_pages_checked
      literalBlocks)

theorem literalBlocks_block38_checked :
    readCheckBlock (assembledRead literalBlocks) 188417 4096 = true := by
  simpa only [literalBlocks_window38] using
    (ImbalancedChen.OriginalU2StoredNodeBlock38FullSourceOnly.block38_all_pages_checked
      literalBlocks)

theorem literalBlocks_block39_checked :
    readCheckBlock (assembledRead literalBlocks) 192513 4096 = true := by
  simpa only [literalBlocks_window39] using
    (ImbalancedChen.OriginalU2StoredNodeBlock39FullSourceOnly.block39_all_pages_checked
      literalBlocks)

/-- Exhaustive literal cases 0..39, covering exactly rows32769..196608. -/
theorem literalBlocks_all40_checked (b : Fin 40) :
    readCheckBlock (assembledRead literalBlocks) (32769+4096*b.val) 4096 = true := by
  rcases b with ⟨b, hb⟩
  change readCheckBlock (assembledRead literalBlocks) (32769+4096*b) 4096 = true
  interval_cases b
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block00_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block01_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block02_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block03_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block04_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block05_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block06_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block07_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block08_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block09_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block10_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block11_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block12_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block13_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block14_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block15_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block16_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block17_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block18_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block19_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block20_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block21_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block22_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block23_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block24_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block25_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block26_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block27_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block28_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block29_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block30_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block31_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block32_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block33_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block34_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block35_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block36_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block37_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block38_checked
  · simpa only [Nat.reduceAdd, Nat.reduceMul] using literalBlocks_block39_checked

/-- Concrete closed table, once the source-listed imports and independent repairs are accepted.
Its checked field is proved above; there is no unchecked chunk parameter. -/
noncomputable def literalCheckedBlockTable : CheckedBlockTable where
  blocks := literalBlocks
  checked := literalBlocks_all40_checked

/-- Semantic local step, for exactly the original update domain. -/
theorem literalBlocks_update_semantics (i : Nat)
    (hi : 32769 ≤ i) (hmax : i ≤ 196608) :
    assembledRead literalBlocks i = originalNodeUpdate i (assembledRead literalBlocks) := by
  exact ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly.CheckedBlockTable.local_equations literalCheckedBlockTable i hi hmax

/-- Endpoint-inclusive enclosure supplied by the existing real consumer. -/
theorem literalBlocks_nodes_enclose (i : Nat)
    (hi : 32768 ≤ i) (hmax : i ≤ 196608) :
    NodeEncloses (assembledRead literalBlocks i) i := by
  exact ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable.encloses
    literalCheckedBlockTable i hi hmax

/-- The same checked reader equals the exact finite original recurrence.
This does not identify any unbound historical file bytes. -/
theorem literalBlocks_read_eq_original :
    assembledRead literalBlocks = originalFinalNodes := by
  exact ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly.CheckedBlockTable.read_eq_original literalCheckedBlockTable

/-- Actual stored query composition, retaining all original integer rules. -/
theorem literalBlocks_query_eq_original (a b : Int) :
    readQueryLo160 (assembledRead literalBlocks) a b = literalQueryLo160 a b ∧
    readQueryHi160 (assembledRead literalBlocks) a b = literalQueryHi160 a b := by
  exact ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly.CheckedBlockTable.query_eq_original literalCheckedBlockTable a b

/-- The existing compact query consumer at the concrete immutable table.
Only the accepted analytic query hypotheses remain as parameters. -/
theorem literalBlocks_compact_query_encloses (a b : Int)
    (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    (readQueryLo160 (assembledRead literalBlocks) a b : Real)/2^160 ≤
      actualExtendedThirdLowerFactor ((a : Real)/(b : Real)) ∧
    actualExtendedThirdLowerFactor ((a : Real)/(b : Real)) ≤
      (readQueryHi160 (assembledRead literalBlocks) a b : Real)/2^160 := by
  exact ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly.CheckedBlockTable.compact_query_encloses literalCheckedBlockTable a b hb ha2 ha12

end ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly
