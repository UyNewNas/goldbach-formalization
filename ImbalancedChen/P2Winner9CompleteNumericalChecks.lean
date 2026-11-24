import ImbalancedChen.P2Winner9NumericalCheck00
import ImbalancedChen.P2Winner9NumericalCheck01
import ImbalancedChen.P2Winner9NumericalCheck02
import ImbalancedChen.P2Winner9NumericalCheck03
import ImbalancedChen.P2Winner9NumericalCheck04
import ImbalancedChen.P2Winner9NumericalCheck05
import ImbalancedChen.P2Winner9NumericalCheck06
import ImbalancedChen.P2Winner9NumericalCheck07
import ImbalancedChen.P2Winner9NumericalCheck08
import ImbalancedChen.P2Winner9NumericalCheck09
import ImbalancedChen.P2Winner9NumericalCheck10
import ImbalancedChen.P2Winner9NumericalCheck11
import ImbalancedChen.P2Winner9NumericalCheck12
import ImbalancedChen.P2Winner9NumericalCheck13
import ImbalancedChen.P2Winner9NumericalCheck14
import ImbalancedChen.P2Winner9NumericalCheck15
import ImbalancedChen.P2Winner9NumericalCheck16
import ImbalancedChen.P2Winner9NumericalCheck17
import ImbalancedChen.P2Winner9NumericalCheck18
import ImbalancedChen.P2Winner9NumericalCheck19
import ImbalancedChen.P2Winner9NumericalCheck20
import ImbalancedChen.P2Winner9NumericalCheck21
import ImbalancedChen.P2Winner9NumericalCheck22
import ImbalancedChen.P2Winner9NumericalCheck23
import ImbalancedChen.P2Winner9NumericalCheck24
import ImbalancedChen.P2Winner9NumericalCheck25
import ImbalancedChen.P2Winner9NumericalCheck26
import ImbalancedChen.P2Winner9NumericalCheck27
import ImbalancedChen.P2Winner9NumericalCheck28
import ImbalancedChen.P2Winner9NumericalCheck29
import ImbalancedChen.P2Winner9NumericalCheck30
import ImbalancedChen.P2Winner9NumericalCheck31
import ImbalancedChen.P2Winner9NumericalCheck32
import ImbalancedChen.P2Winner9NumericalCheck33
import ImbalancedChen.P2Winner9NumericalCheck34
import ImbalancedChen.P2Winner9NumericalCheck35
import ImbalancedChen.P2Winner9NumericalCheck36
import ImbalancedChen.P2Winner9NumericalCheck37
import ImbalancedChen.P2Winner9NumericalCheck38
import ImbalancedChen.P2Winner9NumericalCheck39
import ImbalancedChen.P2Winner9NumericalCheck40
import ImbalancedChen.P2Winner9NumericalCheck41
import ImbalancedChen.P2Winner9NumericalCheck42
import ImbalancedChen.P2Winner9NumericalCheck43
import ImbalancedChen.P2Winner9CompleteSeedData

/-! Every original Winner9 row supplies its own selected numerical certificate. -/

namespace ImbalancedChen.P2Winner9CompleteNumericalChecks
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)
open P2Winner9CompleteSeedData (RowIndex entry allRows entry_eq_allRows)

set_option maxRecDepth 20000

theorem archive_checked : Checked (fun _ r => checkSelected r = true) 0 11026 allRows := by
  unfold allRows P2Winner9CompleteSeedData.blocks
  exact
    P2Winner9NumericalCheck00.checked.flatten_cons <|
    P2Winner9NumericalCheck01.checked.flatten_cons <|
    P2Winner9NumericalCheck02.checked.flatten_cons <|
    P2Winner9NumericalCheck03.checked.flatten_cons <|
    P2Winner9NumericalCheck04.checked.flatten_cons <|
    P2Winner9NumericalCheck05.checked.flatten_cons <|
    P2Winner9NumericalCheck06.checked.flatten_cons <|
    P2Winner9NumericalCheck07.checked.flatten_cons <|
    P2Winner9NumericalCheck08.checked.flatten_cons <|
    P2Winner9NumericalCheck09.checked.flatten_cons <|
    P2Winner9NumericalCheck10.checked.flatten_cons <|
    P2Winner9NumericalCheck11.checked.flatten_cons <|
    P2Winner9NumericalCheck12.checked.flatten_cons <|
    P2Winner9NumericalCheck13.checked.flatten_cons <|
    P2Winner9NumericalCheck14.checked.flatten_cons <|
    P2Winner9NumericalCheck15.checked.flatten_cons <|
    P2Winner9NumericalCheck16.checked.flatten_cons <|
    P2Winner9NumericalCheck17.checked.flatten_cons <|
    P2Winner9NumericalCheck18.checked.flatten_cons <|
    P2Winner9NumericalCheck19.checked.flatten_cons <|
    P2Winner9NumericalCheck20.checked.flatten_cons <|
    P2Winner9NumericalCheck21.checked.flatten_cons <|
    P2Winner9NumericalCheck22.checked.flatten_cons <|
    P2Winner9NumericalCheck23.checked.flatten_cons <|
    P2Winner9NumericalCheck24.checked.flatten_cons <|
    P2Winner9NumericalCheck25.checked.flatten_cons <|
    P2Winner9NumericalCheck26.checked.flatten_cons <|
    P2Winner9NumericalCheck27.checked.flatten_cons <|
    P2Winner9NumericalCheck28.checked.flatten_cons <|
    P2Winner9NumericalCheck29.checked.flatten_cons <|
    P2Winner9NumericalCheck30.checked.flatten_cons <|
    P2Winner9NumericalCheck31.checked.flatten_cons <|
    P2Winner9NumericalCheck32.checked.flatten_cons <|
    P2Winner9NumericalCheck33.checked.flatten_cons <|
    P2Winner9NumericalCheck34.checked.flatten_cons <|
    P2Winner9NumericalCheck35.checked.flatten_cons <|
    P2Winner9NumericalCheck36.checked.flatten_cons <|
    P2Winner9NumericalCheck37.checked.flatten_cons <|
    P2Winner9NumericalCheck38.checked.flatten_cons <|
    P2Winner9NumericalCheck39.checked.flatten_cons <|
    P2Winner9NumericalCheck40.checked.flatten_cons <|
    P2Winner9NumericalCheck41.checked.flatten_cons <|
    P2Winner9NumericalCheck42.checked.flatten_cons <|
    P2Winner9NumericalCheck43.checked.flatten_single

attribute [local irreducible] allRows

theorem selected_checked (i : RowIndex) : checkSelected (entry i) = true := by
  rw [entry_eq_allRows]
  exact archive_checked.2 i

end ImbalancedChen.P2Winner9CompleteNumericalChecks
