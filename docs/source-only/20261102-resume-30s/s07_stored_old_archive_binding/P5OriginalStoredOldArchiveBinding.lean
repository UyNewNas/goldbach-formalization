import ImbalancedChen.P5OriginalTaylorRationalData
import ImbalancedChen.P5FullStoredParentSameOwnerBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
72 closed finite bodies pair the original 143 typed blocks with the
independent 72 stored old/new blocks IN THEIR ORIGINAL ORDER.  Each
body covers 4096 original parents, except the final 1817.  They reconstruct
the original rational Taylor expression independently of the saved floor.
All bodies are UNEVALUATED.  No integral licence, oldfloor hypothesis,
new axiom, or numerical-replay output is a premise of the exports below.
-/
namespace ImbalancedChen.P5OriginalStoredOldArchiveBinding
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthTypedArchiveShape P5SubdivisionStoredParentTypes
open P5FullStoredParentSameOwnerBinding P5OriginalParentJensenRawFields
open P5OriginalTaylorRationalData

def RowBinding (raw : FifthWireRow) (saved : StoredParent) : Prop :=
  0 ≤ originalParentJensenFloorZ raw ∧
  saved.oldQ80 = max (originalParentJensenFloorZ raw) (availableTaylorFloorZ raw)

instance (raw : FifthWireRow) (saved : StoredParent) : Decidable (RowBinding raw saved) := by
  unfold RowBinding
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block000_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock000.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock001.rows.toList)
      Data.P5SubdivisionStoredBlock000.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block001_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock002.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock003.rows.toList)
      Data.P5SubdivisionStoredBlock001.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block002_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock004.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock005.rows.toList)
      Data.P5SubdivisionStoredBlock002.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block003_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock006.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock007.rows.toList)
      Data.P5SubdivisionStoredBlock003.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block004_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock008.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock009.rows.toList)
      Data.P5SubdivisionStoredBlock004.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block005_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock010.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock011.rows.toList)
      Data.P5SubdivisionStoredBlock005.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block006_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock012.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock013.rows.toList)
      Data.P5SubdivisionStoredBlock006.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block007_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock014.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock015.rows.toList)
      Data.P5SubdivisionStoredBlock007.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block008_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock016.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock017.rows.toList)
      Data.P5SubdivisionStoredBlock008.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block009_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock018.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock019.rows.toList)
      Data.P5SubdivisionStoredBlock009.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block010_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock020.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock021.rows.toList)
      Data.P5SubdivisionStoredBlock010.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block011_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock022.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock023.rows.toList)
      Data.P5SubdivisionStoredBlock011.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block012_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock024.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock025.rows.toList)
      Data.P5SubdivisionStoredBlock012.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block013_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock026.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock027.rows.toList)
      Data.P5SubdivisionStoredBlock013.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block014_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock028.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock029.rows.toList)
      Data.P5SubdivisionStoredBlock014.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block015_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock030.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock031.rows.toList)
      Data.P5SubdivisionStoredBlock015.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block016_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock032.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock033.rows.toList)
      Data.P5SubdivisionStoredBlock016.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block017_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock034.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock035.rows.toList)
      Data.P5SubdivisionStoredBlock017.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block018_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock036.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock037.rows.toList)
      Data.P5SubdivisionStoredBlock018.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block019_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock038.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock039.rows.toList)
      Data.P5SubdivisionStoredBlock019.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block020_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock040.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock041.rows.toList)
      Data.P5SubdivisionStoredBlock020.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block021_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock042.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock043.rows.toList)
      Data.P5SubdivisionStoredBlock021.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block022_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock044.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock045.rows.toList)
      Data.P5SubdivisionStoredBlock022.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block023_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock046.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock047.rows.toList)
      Data.P5SubdivisionStoredBlock023.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block024_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock048.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock049.rows.toList)
      Data.P5SubdivisionStoredBlock024.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block025_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock050.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock051.rows.toList)
      Data.P5SubdivisionStoredBlock025.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block026_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock052.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock053.rows.toList)
      Data.P5SubdivisionStoredBlock026.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block027_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock054.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock055.rows.toList)
      Data.P5SubdivisionStoredBlock027.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block028_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock056.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock057.rows.toList)
      Data.P5SubdivisionStoredBlock028.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block029_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock058.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock059.rows.toList)
      Data.P5SubdivisionStoredBlock029.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block030_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock060.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock061.rows.toList)
      Data.P5SubdivisionStoredBlock030.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block031_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock062.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock063.rows.toList)
      Data.P5SubdivisionStoredBlock031.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block032_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock064.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock065.rows.toList)
      Data.P5SubdivisionStoredBlock032.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block033_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock066.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock067.rows.toList)
      Data.P5SubdivisionStoredBlock033.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block034_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock068.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock069.rows.toList)
      Data.P5SubdivisionStoredBlock034.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block035_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock070.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock071.rows.toList)
      Data.P5SubdivisionStoredBlock035.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block036_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock072.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock073.rows.toList)
      Data.P5SubdivisionStoredBlock036.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block037_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock074.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock075.rows.toList)
      Data.P5SubdivisionStoredBlock037.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block038_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock076.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock077.rows.toList)
      Data.P5SubdivisionStoredBlock038.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block039_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock078.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock079.rows.toList)
      Data.P5SubdivisionStoredBlock039.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block040_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock080.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock081.rows.toList)
      Data.P5SubdivisionStoredBlock040.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block041_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock082.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock083.rows.toList)
      Data.P5SubdivisionStoredBlock041.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block042_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock084.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock085.rows.toList)
      Data.P5SubdivisionStoredBlock042.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block043_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock086.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock087.rows.toList)
      Data.P5SubdivisionStoredBlock043.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block044_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock088.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock089.rows.toList)
      Data.P5SubdivisionStoredBlock044.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block045_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock090.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock091.rows.toList)
      Data.P5SubdivisionStoredBlock045.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block046_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock092.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock093.rows.toList)
      Data.P5SubdivisionStoredBlock046.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block047_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock094.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock095.rows.toList)
      Data.P5SubdivisionStoredBlock047.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block048_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock096.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock097.rows.toList)
      Data.P5SubdivisionStoredBlock048.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block049_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock098.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock099.rows.toList)
      Data.P5SubdivisionStoredBlock049.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block050_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock100.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock101.rows.toList)
      Data.P5SubdivisionStoredBlock050.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block051_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock102.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock103.rows.toList)
      Data.P5SubdivisionStoredBlock051.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block052_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock104.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock105.rows.toList)
      Data.P5SubdivisionStoredBlock052.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block053_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock106.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock107.rows.toList)
      Data.P5SubdivisionStoredBlock053.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block054_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock108.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock109.rows.toList)
      Data.P5SubdivisionStoredBlock054.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block055_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock110.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock111.rows.toList)
      Data.P5SubdivisionStoredBlock055.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block056_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock112.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock113.rows.toList)
      Data.P5SubdivisionStoredBlock056.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block057_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock114.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock115.rows.toList)
      Data.P5SubdivisionStoredBlock057.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block058_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock116.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock117.rows.toList)
      Data.P5SubdivisionStoredBlock058.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block059_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock118.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock119.rows.toList)
      Data.P5SubdivisionStoredBlock059.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block060_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock120.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock121.rows.toList)
      Data.P5SubdivisionStoredBlock060.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block061_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock122.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock123.rows.toList)
      Data.P5SubdivisionStoredBlock061.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block062_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock124.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock125.rows.toList)
      Data.P5SubdivisionStoredBlock062.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block063_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock126.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock127.rows.toList)
      Data.P5SubdivisionStoredBlock063.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block064_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock128.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock129.rows.toList)
      Data.P5SubdivisionStoredBlock064.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block065_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock130.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock131.rows.toList)
      Data.P5SubdivisionStoredBlock065.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block066_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock132.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock133.rows.toList)
      Data.P5SubdivisionStoredBlock066.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block067_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock134.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock135.rows.toList)
      Data.P5SubdivisionStoredBlock067.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block068_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock136.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock137.rows.toList)
      Data.P5SubdivisionStoredBlock068.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block069_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock138.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock139.rows.toList)
      Data.P5SubdivisionStoredBlock069.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block070_stored_old_binding :
    List.Forall₂ RowBinding
      (Data.P1HistoricalFifthSavedDataBlock140.rows.toList ++ Data.P1HistoricalFifthSavedDataBlock141.rows.toList)
      Data.P5SubdivisionStoredBlock070.rows.toList := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block071_stored_old_binding :
    List.Forall₂ RowBinding
      Data.P1HistoricalFifthSavedDataBlock142.rows.toList
      Data.P5SubdivisionStoredBlock071.rows.toList := by
  decide

theorem all_original_stored_old_bindings :
    List.Forall₂ RowBinding
      Data.P1HistoricalFifthSavedTableData.rows.toList
      P5SubdivisionStoredParentArchive.rows.toList := by
  rw [rows_toList_order, block_order]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [P5SubdivisionStoredParentArchive.rows, Array.toList_append]
  have h := (block000_stored_old_binding.append (block001_stored_old_binding.append (block002_stored_old_binding.append (block003_stored_old_binding.append (block004_stored_old_binding.append (block005_stored_old_binding.append (block006_stored_old_binding.append (block007_stored_old_binding.append (block008_stored_old_binding.append (block009_stored_old_binding.append (block010_stored_old_binding.append (block011_stored_old_binding.append (block012_stored_old_binding.append (block013_stored_old_binding.append (block014_stored_old_binding.append (block015_stored_old_binding.append (block016_stored_old_binding.append (block017_stored_old_binding.append (block018_stored_old_binding.append (block019_stored_old_binding.append (block020_stored_old_binding.append (block021_stored_old_binding.append (block022_stored_old_binding.append (block023_stored_old_binding.append (block024_stored_old_binding.append (block025_stored_old_binding.append (block026_stored_old_binding.append (block027_stored_old_binding.append (block028_stored_old_binding.append (block029_stored_old_binding.append (block030_stored_old_binding.append (block031_stored_old_binding.append (block032_stored_old_binding.append (block033_stored_old_binding.append (block034_stored_old_binding.append (block035_stored_old_binding.append (block036_stored_old_binding.append (block037_stored_old_binding.append (block038_stored_old_binding.append (block039_stored_old_binding.append (block040_stored_old_binding.append (block041_stored_old_binding.append (block042_stored_old_binding.append (block043_stored_old_binding.append (block044_stored_old_binding.append (block045_stored_old_binding.append (block046_stored_old_binding.append (block047_stored_old_binding.append (block048_stored_old_binding.append (block049_stored_old_binding.append (block050_stored_old_binding.append (block051_stored_old_binding.append (block052_stored_old_binding.append (block053_stored_old_binding.append (block054_stored_old_binding.append (block055_stored_old_binding.append (block056_stored_old_binding.append (block057_stored_old_binding.append (block058_stored_old_binding.append (block059_stored_old_binding.append (block060_stored_old_binding.append (block061_stored_old_binding.append (block062_stored_old_binding.append (block063_stored_old_binding.append (block064_stored_old_binding.append (block065_stored_old_binding.append (block066_stored_old_binding.append (block067_stored_old_binding.append (block068_stored_old_binding.append (block069_stored_old_binding.append (block070_stored_old_binding.append block071_stored_old_binding)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  simpa only [List.append_assoc] using h

/-- Positional extraction preserves source multiplicity and does not use
row-value equality or a Finset deduplication. -/
private theorem forall₂_get {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (n : ℕ) (hx : n < xs.length) (hy : n < ys.length) :
    R xs[n] ys[n] := by
  induction h generalizing n with
  | nil => simp at hx
  | @cons x y xs ys hxy htail ih =>
      cases n with
      | zero => exact hxy
      | succ n => exact ih n (by simpa using hx) (by simpa using hy)

theorem original_stored_old_binding (i : ArchiveIndex) :
    0 ≤ originalParentJensenFloorZ (archiveRow i) ∧
    (storedAt i).oldQ80 = max (originalParentJensenFloorZ (archiveRow i))
      (availableTaylorFloorZ (archiveRow i)) := by
  have hy : i.val < P5SubdivisionStoredParentArchive.rows.toList.length := by
    simpa only [Array.length_toList, P5SubdivisionStoredParentArchive.rows_size]
      using archiveIndex_lt i
  have h := forall₂_get all_original_stored_old_bindings i.val i.isLt hy
  simpa only [RowBinding, archiveRow, storedAt, Array.getElem_toList] using h

/-- Exact old saved numerator, before division by the unchanged Q80 scale. -/
theorem original_stored_old_eq_max (i : ArchiveIndex) :
    (storedAt i).oldQ80 = max (originalParentJensenFloorZ (archiveRow i))
      (availableTaylorFloorZ (archiveRow i)) := (original_stored_old_binding i).2

/-- The strict Taylor branch supplies its ACTUAL primitive source data.
No caller supplies BranchFacts, ranges, midpoint values or a floor licence. -/
theorem strict_stored_taylor_available (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    available (archiveRow i) := by
  by_contra hn
  have h := original_stored_old_eq_max i
  rw [availableTaylorFloorZ, if_neg hn,
    max_eq_left (original_stored_old_binding i).1] at h
  omega

theorem strict_stored_taylor_primitive_facts (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    TaylorFiniteFacts (archiveRow i) := (strict_stored_taylor_available i hstrict).1

theorem strict_stored_taylor_branchFacts (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    P5OriginalTaylorAffineBranchBinding.BranchFacts (archiveRow i)
      (newSide (archiveRow i)) (oldSides (archiveRow i)) (selected (archiveRow i)) :=
  available_branchFacts _ (strict_stored_taylor_available i hstrict)

/-- When the saved old branch is Taylor, its numerator is the floor of
the independent original rational bound, rather than an invented defect. -/
theorem strict_stored_old_eq_original_taylor_floor (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    (storedAt i).oldQ80 = taylorFloorZ (archiveRow i) := by
  have ha := strict_stored_taylor_available i hstrict
  have h := original_stored_old_eq_max i
  rw [availableTaylorFloorZ, if_pos ha] at h
  have hj : originalParentJensenFloorZ (archiveRow i) < taylorFloorZ (archiveRow i) := by
    by_contra hn
    rw [max_eq_left (le_of_not_gt hn)] at h
    omega
  simpa only [max_eq_right hj.le] using h

end ImbalancedChen.P5OriginalStoredOldArchiveBinding
