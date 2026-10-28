import ImbalancedChen.OriginalPairedN48HighPacket00
import ImbalancedChen.OriginalPairedN48HighPacket01
import ImbalancedChen.OriginalPairedN48HighPacket02
import ImbalancedChen.OriginalPairedN48HighPacket03
import ImbalancedChen.OriginalPairedN48HighPacket04
import ImbalancedChen.OriginalPairedN48HighPacket05
import ImbalancedChen.OriginalPairedN48HighPacket06
import ImbalancedChen.OriginalPairedN48HighPacket07
import ImbalancedChen.OriginalPairedN48HighPacket08
import ImbalancedChen.OriginalPairedN48HighPacket09
import ImbalancedChen.OriginalPairedN48HighPacket10
import ImbalancedChen.OriginalPairedN48HighPacket11
import ImbalancedChen.OriginalPairedN48HighPacket12
import ImbalancedChen.OriginalPairedN48HighPacket13
import ImbalancedChen.OriginalPairedN48HighPacket14
import ImbalancedChen.OriginalPairedN48HighPacket15
import ImbalancedChen.OriginalPairedN48HighPacket16
import ImbalancedChen.OriginalPairedN48HighPacket17
import ImbalancedChen.OriginalPairedN48HighPacket18
import ImbalancedChen.OriginalPairedN48HighPacket19
import ImbalancedChen.OriginalPairedN48HighPacket20
import ImbalancedChen.OriginalPairedN48HighPacket21
import ImbalancedChen.OriginalPairedN48HighPacket22
import ImbalancedChen.OriginalPairedN48HighPacket23
import ImbalancedChen.OriginalPairedN48HighPacket24
import ImbalancedChen.OriginalPairedN48HighPacket25
import ImbalancedChen.OriginalPairedN48HighPacket26
import ImbalancedChen.OriginalPairedN48HighPacket27
import ImbalancedChen.OriginalPairedN48HighPacket28
import ImbalancedChen.OriginalPairedN48HighPacket29
import ImbalancedChen.OriginalPairedN48HighPacket30
import ImbalancedChen.OriginalPairedN48HighPacket31
import ImbalancedChen.OriginalPairedN48HighPacket32
import ImbalancedChen.OriginalPairedN48HighPacket33
import ImbalancedChen.OriginalPairedN48HighPacket34
import ImbalancedChen.OriginalPairedN48HighPacket35
import ImbalancedChen.OriginalPairedN48HighPacket36
import ImbalancedChen.OriginalPairedN48HighPacket37
import ImbalancedChen.OriginalPairedN48HighPacket38
import ImbalancedChen.OriginalPairedN48HighPacket39
import ImbalancedChen.OriginalPairedN48HighPacket40
import ImbalancedChen.OriginalPairedN48HighPacket41
import ImbalancedChen.OriginalPairedN48HighPacket42
import ImbalancedChen.OriginalPairedN48HighPacket43
import ImbalancedChen.OriginalPairedN48HighPacket44
import ImbalancedChen.OriginalPairedN48HighPacket45
import ImbalancedChen.OriginalPairedN48HighPacket46
import ImbalancedChen.OriginalPairedN48HighPacket47
import ImbalancedChen.P2N48ActualGeometricKeyDecoder

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Full original high-band row data, not the prior overlap crop. The literal
packets preserve all seven source columns. Independent original rank/key
identities below are UNEXECUTED finite proof proposals, not passed checks.
No claim is made that a formal JSON parser verified the transcription.
-/
namespace ImbalancedChen.OriginalPairedN48WholeHighArchive
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48ActualGeometricKeyDecoder P2N48SelectedFunctionalRemainder
open OriginalPairedN48ArchiveData OriginalPairedN48HighPacketSchema
open OriginalPairedN48HighPacketData

/-- Exact concatenation of the 48 literal source leaves in original order. -/
def rawHighPackets : Array ℕ :=
  #[literalHighPackets00, literalHighPackets01, literalHighPackets02, literalHighPackets03, literalHighPackets04, literalHighPackets05, literalHighPackets06, literalHighPackets07, literalHighPackets08, literalHighPackets09, literalHighPackets10, literalHighPackets11, literalHighPackets12, literalHighPackets13, literalHighPackets14, literalHighPackets15, literalHighPackets16, literalHighPackets17, literalHighPackets18, literalHighPackets19, literalHighPackets20, literalHighPackets21, literalHighPackets22, literalHighPackets23, literalHighPackets24, literalHighPackets25, literalHighPackets26, literalHighPackets27, literalHighPackets28, literalHighPackets29, literalHighPackets30, literalHighPackets31, literalHighPackets32, literalHighPackets33, literalHighPackets34, literalHighPackets35, literalHighPackets36, literalHighPackets37, literalHighPackets38, literalHighPackets39, literalHighPackets40, literalHighPackets41, literalHighPackets42, literalHighPackets43, literalHighPackets44, literalHighPackets45, literalHighPackets46, literalHighPackets47].foldl (fun acc chunk => acc ++ chunk) #[]

def rowAtOffset (i : ℕ) : SourceRow :=
  decodeOriginalPacket (249900 + i) ((rawHighPackets[i]?).getD 0)

/-- This rank is independently taken from the original lexicographic
combinations_with_replacement producer, not from the packet contents. -/
def highKeyOffset (x y z w : Fin 48) : ℕ :=
  19600 * x.val + tripleLexRank y z w

def archiveRowForKey (x y z w : Fin 48) : SourceRow :=
  rowAtOffset (highKeyOffset x y z w)

def fullHighArchiveRows : List SourceRow :=
  (List.range 940800).map rowAtOffset

def wholeHighMethodZeroRows : List SourceRow :=
  fullHighArchiveRows.filter (fun r => r.method = 0)

def wholeHighMethodZeroSet : Finset SourceRow :=
  wholeHighMethodZeroRows.toFinset

/-- Pure literal source-field/rank obligations. There is no omega,
maximum cover, numerical endpoint or cost conclusion in this predicate. -/
def WholeHighFieldBinding : Prop :=
  rawHighPackets.size = 940800 ∧
  (∀ i : Fin 940800, HighRowDecoded (rowAtOffset i.val)) ∧
  ∀ x y z w : Fin 48, w ≤ z → z ≤ y →
    highKeyOffset x y z w < 940800 ∧
    (archiveRowForKey x y z w).term = (1 : Fin 2) ∧
    (archiveRowForKey x y z w).ix = x ∧
    (archiveRowForKey x y z w).iy = y ∧
    (archiveRowForKey x y z w).iz = z ∧
    (archiveRowForKey x y z w).iw = w

instance : Decidable WholeHighFieldBinding := by
  unfold WholeHighFieldBinding
  infer_instance

/-- UNEXECUTED finite source proposal on the actual literal packet table. -/
theorem whole_high_field_binding_proposal : WholeHighFieldBinding := by
  decide +kernel

theorem rowAtOffset_ordinal (i : ℕ) :
    (rowAtOffset i).ordinal = 249900 + i := rfl

theorem full_high_row_decoded (r : SourceRow) (hr : r ∈ fullHighArchiveRows) :
    HighRowDecoded r := by
  rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
  exact whole_high_field_binding_proposal.2.1 ⟨i, List.mem_range.mp hi⟩

/-- Independent key/rank identity for every genuine ordered high key.
Method and floor stay those decoded from the original literal table. -/
theorem archiveRowForKey_fields_proposal (x y z w : Fin 48)
    (hwz : w ≤ z) (hzy : z ≤ y) :
    (archiveRowForKey x y z w).term = (1 : Fin 2) ∧
    (archiveRowForKey x y z w).ix = x ∧
    (archiveRowForKey x y z w).iy = y ∧
    (archiveRowForKey x y z w).iz = z ∧
    (archiveRowForKey x y z w).iw = w ∧
    (archiveRowForKey x y z w).ordinal =
      249900 + 19600 * x.val + tripleLexRank y z w := by
  have h := whole_high_field_binding_proposal.2.2 x y z w hwz hzy
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
    by simp only [archiveRowForKey, rowAtOffset_ordinal, highKeyOffset, Nat.add_assoc]⟩

theorem archiveRowForKey_mem_full (x y z w : Fin 48)
    (hwz : w ≤ z) (hzy : z ≤ y) :
    archiveRowForKey x y z w ∈ fullHighArchiveRows := by
  exact List.mem_map.mpr ⟨highKeyOffset x y z w,
    List.mem_range.mpr (whole_high_field_binding_proposal.2.2 x y z w hwz hzy).1, rfl⟩

theorem full_high_ordinal_injective (r s : SourceRow)
    (hr : r ∈ fullHighArchiveRows) (hs : s ∈ fullHighArchiveRows)
    (hord : r.ordinal = s.ordinal) : r = s := by
  rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
  rcases List.mem_map.mp hs with ⟨j, hj, rfl⟩
  have hij : i = j := Nat.add_left_cancel
    (show 249900 + i = 249900 + j from hord)
  exact congrArg rowAtOffset hij

theorem full_high_rowKey_injective (r s : SourceRow)
    (hr : r ∈ fullHighArchiveRows) (hs : s ∈ fullHighArchiveRows)
    (hkey : rowKey r = rowKey s) : r = s := by
  have hdr := full_high_row_decoded r hr
  have hds := full_high_row_decoded s hs
  apply full_high_ordinal_injective r s hr hs
  exact hdr.2.2.2.trans ((congrArg highOrdinalOfKey hkey).trans hds.2.2.2.symm)

theorem whole_high_method_zero_policy (r : SourceRow)
    (hr : r ∈ wholeHighMethodZeroRows) :
    r ∈ fullHighArchiveRows ∧ r.method = 0 := by
  simpa only [wholeHighMethodZeroRows, List.mem_filter, decide_eq_true_eq] using hr

theorem whole_high_method_zero_keys : DistinctGeometricKeys wholeHighMethodZeroSet := by
  intro r hr s hs hkey
  exact full_high_rowKey_injective r s
    (whole_high_method_zero_policy r (List.mem_toFinset.mp hr)).1
    (whole_high_method_zero_policy s (List.mem_toFinset.mp hs)).1 hkey

/-- Literal comparison between two independently transcribed archives:
the old overlap crop and the complete high-band packets. NOT executed. -/
def CropMatchesWholeHigh : Bool :=
  rawSelectedRows.all (fun r => decide (r = rowAtOffset (r.ordinal - 249900)))

theorem crop_matches_whole_high_proposal : CropMatchesWholeHigh = true := by
  decide +kernel

theorem raw_crop_whole_row_identity (r : SourceRow) (hr : r ∈ rawSelectedRows) :
    r = archiveRowForKey r.ix r.iy r.iz r.iw := by
  have heq := of_decide_eq_true
    ((List.all_eq_true.mp crop_matches_whole_high_proposal) r hr)
  have hd := decoded_of_mem_rawSelectedRows r hr
  have ho : r.ordinal - 249900 = highKeyOffset r.ix r.iy r.iz r.iw := by
    rw [hd.2.2.2]
    simp only [highOrdinalOfKey, rowKey, highKeyOffset, Nat.add_assoc]
    omega
  simpa only [archiveRowForKey, ho] using heq

/-- Actual F retained rows have exactly their whole-source fields,
including original method and saved Q80 floor; this is not a geometry alias. -/
theorem actual_retained_same_whole_source (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    r = archiveRowForKey r.ix r.iy r.iz r.iw :=
  raw_crop_whole_row_identity r (actualRetainedRows_policy r hr).1
end ImbalancedChen.OriginalPairedN48WholeHighArchive
