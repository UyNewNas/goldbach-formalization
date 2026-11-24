import ImbalancedChen.P2Winner9CompletePullingCheck00
import ImbalancedChen.P2Winner9CompletePullingCheck01
import ImbalancedChen.P2Winner9CompletePullingCheck02
import ImbalancedChen.P2Winner9CompletePullingCheck03
import ImbalancedChen.P2Winner9CompletePullingCheck04
import ImbalancedChen.P2Winner9CompletePullingCheck05
import ImbalancedChen.P2Winner9CompletePullingCheck06
import ImbalancedChen.P2Winner9CompletePullingCheck07
import ImbalancedChen.P2Winner9CompletePullingCheck08
import ImbalancedChen.P2Winner9CompletePullingCheck09
import ImbalancedChen.P2Winner9CompletePullingCheck10
import ImbalancedChen.P2Winner9CompletePullingCheck11
import ImbalancedChen.P2Winner9CompletePullingCheck12
import ImbalancedChen.P2Winner9CompletePullingCheck13
import ImbalancedChen.P2Winner9CompletePullingCheck14
import ImbalancedChen.P2Winner9CompletePullingCheck15
import ImbalancedChen.P2Winner9CompletePullingCheck16
import ImbalancedChen.P2Winner9CompletePullingCheck17
import ImbalancedChen.P2Winner9CompletePullingCheck18
import ImbalancedChen.P2Winner9CompletePullingCheck19
import ImbalancedChen.P2Winner9CompletePullingCheck20
import ImbalancedChen.P2Winner9CompletePullingCheck21
import ImbalancedChen.P2Winner9CompletePullingCheck22
import ImbalancedChen.P2Winner9CompletePullingCheck23
import ImbalancedChen.P2Winner9CompletePullingCheck24
import ImbalancedChen.P2Winner9CompletePullingCheck25
import ImbalancedChen.P2Winner9CompletePullingCheck26
import ImbalancedChen.P2Winner9CompletePullingCheck27
import ImbalancedChen.P2Winner9CompletePullingCheck28
import ImbalancedChen.P2Winner9CompletePullingCheck29
import ImbalancedChen.P2Winner9CompletePullingCheck30
import ImbalancedChen.P2Winner9CompletePullingCheck31
import ImbalancedChen.P2Winner9CompletePullingCheck32
import ImbalancedChen.P2Winner9CompletePullingCheck33
import ImbalancedChen.P2Winner9CompletePullingCheck34
import ImbalancedChen.P2Winner9CompletePullingCheck35
import ImbalancedChen.P2Winner9CompletePullingCheck36
import ImbalancedChen.P2Winner9CompletePullingCheck37
import ImbalancedChen.P2Winner9CompletePullingCheck38
import ImbalancedChen.P2Winner9CompletePullingCheck39
import ImbalancedChen.P2Winner9CompletePullingCheck40
import ImbalancedChen.P2Winner9CompletePullingCheck41
import ImbalancedChen.P2Winner9CompletePullingCheck42
import ImbalancedChen.P2Winner9CompletePullingCheck43
import ImbalancedChen.P2Winner9CompleteSeedData
import ImbalancedChen.P2Winner9RowArithmeticChecker

/-!
# Null overlaps for the complete original Winner9 archive

Every row and every adjacent global key is supplied by a small checked page.
The single global ordering includes every cross-block boundary.  No family
geometry, arithmetic floor or integral estimate is assumed here.
-/

namespace ImbalancedChen.P2Winner9CompletePullingGeometry

open MeasureTheory
open P2Winner9CompleteSeedData (RowIndex entry allRows entry_eq_allRows)
open P2Winner9CompletePullingFlags (witnesses checkedRow orderStep)
open P2Winner9PullingOrderChecks (Consecutive)
open P2Winner9SeedArchiveChecks (Checked)
open P2Winner9OriginalPullingFlags (originalSupport)
open P2Winner9SelectedRowRealJacobian (sourceSupport)
open P2Winner9RowArithmeticChecker (archiveVertices)

set_option maxRecDepth 20000

theorem all_adjacent_keys : Consecutive orderStep 0 11025 := by
  exact
    P2Winner9CompletePullingCheck00.order_checked.append <|
    P2Winner9CompletePullingCheck01.order_checked.append <|
    P2Winner9CompletePullingCheck02.order_checked.append <|
    P2Winner9CompletePullingCheck03.order_checked.append <|
    P2Winner9CompletePullingCheck04.order_checked.append <|
    P2Winner9CompletePullingCheck05.order_checked.append <|
    P2Winner9CompletePullingCheck06.order_checked.append <|
    P2Winner9CompletePullingCheck07.order_checked.append <|
    P2Winner9CompletePullingCheck08.order_checked.append <|
    P2Winner9CompletePullingCheck09.order_checked.append <|
    P2Winner9CompletePullingCheck10.order_checked.append <|
    P2Winner9CompletePullingCheck11.order_checked.append <|
    P2Winner9CompletePullingCheck12.order_checked.append <|
    P2Winner9CompletePullingCheck13.order_checked.append <|
    P2Winner9CompletePullingCheck14.order_checked.append <|
    P2Winner9CompletePullingCheck15.order_checked.append <|
    P2Winner9CompletePullingCheck16.order_checked.append <|
    P2Winner9CompletePullingCheck17.order_checked.append <|
    P2Winner9CompletePullingCheck18.order_checked.append <|
    P2Winner9CompletePullingCheck19.order_checked.append <|
    P2Winner9CompletePullingCheck20.order_checked.append <|
    P2Winner9CompletePullingCheck21.order_checked.append <|
    P2Winner9CompletePullingCheck22.order_checked.append <|
    P2Winner9CompletePullingCheck23.order_checked.append <|
    P2Winner9CompletePullingCheck24.order_checked.append <|
    P2Winner9CompletePullingCheck25.order_checked.append <|
    P2Winner9CompletePullingCheck26.order_checked.append <|
    P2Winner9CompletePullingCheck27.order_checked.append <|
    P2Winner9CompletePullingCheck28.order_checked.append <|
    P2Winner9CompletePullingCheck29.order_checked.append <|
    P2Winner9CompletePullingCheck30.order_checked.append <|
    P2Winner9CompletePullingCheck31.order_checked.append <|
    P2Winner9CompletePullingCheck32.order_checked.append <|
    P2Winner9CompletePullingCheck33.order_checked.append <|
    P2Winner9CompletePullingCheck34.order_checked.append <|
    P2Winner9CompletePullingCheck35.order_checked.append <|
    P2Winner9CompletePullingCheck36.order_checked.append <|
    P2Winner9CompletePullingCheck37.order_checked.append <|
    P2Winner9CompletePullingCheck38.order_checked.append <|
    P2Winner9CompletePullingCheck39.order_checked.append <|
    P2Winner9CompletePullingCheck40.order_checked.append <|
    P2Winner9CompletePullingCheck41.order_checked.append <|
    P2Winner9CompletePullingCheck42.order_checked.append <|
    P2Winner9CompletePullingCheck43.order_checked

theorem orderedKeys_strictMono :
    StrictMono (fun i : Fin 11026 => witnesses.orderedKey i.val) :=
  Consecutive.strictMono all_adjacent_keys

theorem archive_checked :
    Checked (fun ordinal row => checkedRow ordinal row = true) 0 11026 allRows := by
  unfold allRows P2Winner9CompleteSeedData.blocks
  exact
    P2Winner9CompletePullingCheck00.checked.flatten_cons <|
    P2Winner9CompletePullingCheck01.checked.flatten_cons <|
    P2Winner9CompletePullingCheck02.checked.flatten_cons <|
    P2Winner9CompletePullingCheck03.checked.flatten_cons <|
    P2Winner9CompletePullingCheck04.checked.flatten_cons <|
    P2Winner9CompletePullingCheck05.checked.flatten_cons <|
    P2Winner9CompletePullingCheck06.checked.flatten_cons <|
    P2Winner9CompletePullingCheck07.checked.flatten_cons <|
    P2Winner9CompletePullingCheck08.checked.flatten_cons <|
    P2Winner9CompletePullingCheck09.checked.flatten_cons <|
    P2Winner9CompletePullingCheck10.checked.flatten_cons <|
    P2Winner9CompletePullingCheck11.checked.flatten_cons <|
    P2Winner9CompletePullingCheck12.checked.flatten_cons <|
    P2Winner9CompletePullingCheck13.checked.flatten_cons <|
    P2Winner9CompletePullingCheck14.checked.flatten_cons <|
    P2Winner9CompletePullingCheck15.checked.flatten_cons <|
    P2Winner9CompletePullingCheck16.checked.flatten_cons <|
    P2Winner9CompletePullingCheck17.checked.flatten_cons <|
    P2Winner9CompletePullingCheck18.checked.flatten_cons <|
    P2Winner9CompletePullingCheck19.checked.flatten_cons <|
    P2Winner9CompletePullingCheck20.checked.flatten_cons <|
    P2Winner9CompletePullingCheck21.checked.flatten_cons <|
    P2Winner9CompletePullingCheck22.checked.flatten_cons <|
    P2Winner9CompletePullingCheck23.checked.flatten_cons <|
    P2Winner9CompletePullingCheck24.checked.flatten_cons <|
    P2Winner9CompletePullingCheck25.checked.flatten_cons <|
    P2Winner9CompletePullingCheck26.checked.flatten_cons <|
    P2Winner9CompletePullingCheck27.checked.flatten_cons <|
    P2Winner9CompletePullingCheck28.checked.flatten_cons <|
    P2Winner9CompletePullingCheck29.checked.flatten_cons <|
    P2Winner9CompletePullingCheck30.checked.flatten_cons <|
    P2Winner9CompletePullingCheck31.checked.flatten_cons <|
    P2Winner9CompletePullingCheck32.checked.flatten_cons <|
    P2Winner9CompletePullingCheck33.checked.flatten_cons <|
    P2Winner9CompletePullingCheck34.checked.flatten_cons <|
    P2Winner9CompletePullingCheck35.checked.flatten_cons <|
    P2Winner9CompletePullingCheck36.checked.flatten_cons <|
    P2Winner9CompletePullingCheck37.checked.flatten_cons <|
    P2Winner9CompletePullingCheck38.checked.flatten_cons <|
    P2Winner9CompletePullingCheck39.checked.flatten_cons <|
    P2Winner9CompletePullingCheck40.checked.flatten_cons <|
    P2Winner9CompletePullingCheck41.checked.flatten_cons <|
    P2Winner9CompletePullingCheck42.checked.flatten_cons <|
    P2Winner9CompletePullingCheck43.checked.flatten_single

theorem allRows_actual_overlap_null :
    Pairwise fun i j : Fin 11026 =>
      volume (originalSupport allRows[i.val]! ∩ originalSupport allRows[j.val]!) = 0 :=
  witnesses.archive_actual_overlap_null orderedKeys_strictMono archive_checked

/-- All 11,026 original physical cells, including different archive blocks. -/
theorem complete_seed_actual_overlap_null :
    Pairwise fun i j : RowIndex => volume
      (sourceSupport (archiveVertices (entry i)) ∩
        sourceSupport (archiveVertices (entry j))) = 0 := by
  intro i j hij
  simpa only [entry_eq_allRows, archiveVertices, originalSupport] using
    allRows_actual_overlap_null hij

end ImbalancedChen.P2Winner9CompletePullingGeometry
