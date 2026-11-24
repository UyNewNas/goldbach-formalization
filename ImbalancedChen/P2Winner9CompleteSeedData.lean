import ImbalancedChen.P2Winner9CompleteSeedVertices
import ImbalancedChen.P2Winner9SeedArchiveCheck00
import ImbalancedChen.P2Winner9SeedArchiveCheck01
import ImbalancedChen.P2Winner9SeedArchiveCheck02
import ImbalancedChen.P2Winner9SeedArchiveCheck03
import ImbalancedChen.P2Winner9SeedArchiveCheck04
import ImbalancedChen.P2Winner9SeedArchiveCheck05
import ImbalancedChen.P2Winner9SeedArchiveCheck06
import ImbalancedChen.P2Winner9SeedArchiveCheck07
import ImbalancedChen.P2Winner9SeedArchiveCheck08
import ImbalancedChen.P2Winner9SeedArchiveCheck09
import ImbalancedChen.P2Winner9SeedArchiveCheck10
import ImbalancedChen.P2Winner9SeedArchiveCheck11
import ImbalancedChen.P2Winner9SeedArchiveCheck12
import ImbalancedChen.P2Winner9SeedArchiveCheck13
import ImbalancedChen.P2Winner9SeedArchiveCheck14
import ImbalancedChen.P2Winner9SeedArchiveCheck15
import ImbalancedChen.P2Winner9SeedArchiveCheck16
import ImbalancedChen.P2Winner9SeedArchiveCheck17
import ImbalancedChen.P2Winner9SeedArchiveCheck18
import ImbalancedChen.P2Winner9SeedArchiveCheck19
import ImbalancedChen.P2Winner9SeedArchiveCheck20
import ImbalancedChen.P2Winner9SeedArchiveCheck21
import ImbalancedChen.P2Winner9SeedArchiveCheck22
import ImbalancedChen.P2Winner9SeedArchiveCheck23
import ImbalancedChen.P2Winner9SeedArchiveCheck24
import ImbalancedChen.P2Winner9SeedArchiveCheck25
import ImbalancedChen.P2Winner9SeedArchiveCheck26
import ImbalancedChen.P2Winner9SeedArchiveCheck27
import ImbalancedChen.P2Winner9SeedArchiveCheck28
import ImbalancedChen.P2Winner9SeedArchiveCheck29
import ImbalancedChen.P2Winner9SeedArchiveCheck30
import ImbalancedChen.P2Winner9SeedArchiveCheck31
import ImbalancedChen.P2Winner9SeedArchiveCheck32
import ImbalancedChen.P2Winner9SeedArchiveCheck33
import ImbalancedChen.P2Winner9SeedArchiveCheck34
import ImbalancedChen.P2Winner9SeedArchiveCheck35
import ImbalancedChen.P2Winner9SeedArchiveCheck36
import ImbalancedChen.P2Winner9SeedArchiveCheck37
import ImbalancedChen.P2Winner9SeedArchiveCheck38
import ImbalancedChen.P2Winner9SeedArchiveCheck39
import ImbalancedChen.P2Winner9SeedArchiveCheck40
import ImbalancedChen.P2Winner9SeedArchiveCheck41
import ImbalancedChen.P2Winner9SeedArchiveCheck42
import ImbalancedChen.P2Winner9SeedArchiveCheck43

/-! The complete original Winner9 family with kernel-checked archive ordinals and selected maxima. -/

namespace ImbalancedChen.P2Winner9CompleteSeedData

open P2Winner9CompleteSeedTypes
open P2Winner9SeedArchiveChecks

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

abbrev RowIndex := Fin 11026

def blocks : Array (Array RawRow) := [
  P2Winner9CompleteSeedBlock00.rows,
  P2Winner9CompleteSeedBlock01.rows,
  P2Winner9CompleteSeedBlock02.rows,
  P2Winner9CompleteSeedBlock03.rows,
  P2Winner9CompleteSeedBlock04.rows,
  P2Winner9CompleteSeedBlock05.rows,
  P2Winner9CompleteSeedBlock06.rows,
  P2Winner9CompleteSeedBlock07.rows,
  P2Winner9CompleteSeedBlock08.rows,
  P2Winner9CompleteSeedBlock09.rows,
  P2Winner9CompleteSeedBlock10.rows,
  P2Winner9CompleteSeedBlock11.rows,
  P2Winner9CompleteSeedBlock12.rows,
  P2Winner9CompleteSeedBlock13.rows,
  P2Winner9CompleteSeedBlock14.rows,
  P2Winner9CompleteSeedBlock15.rows,
  P2Winner9CompleteSeedBlock16.rows,
  P2Winner9CompleteSeedBlock17.rows,
  P2Winner9CompleteSeedBlock18.rows,
  P2Winner9CompleteSeedBlock19.rows,
  P2Winner9CompleteSeedBlock20.rows,
  P2Winner9CompleteSeedBlock21.rows,
  P2Winner9CompleteSeedBlock22.rows,
  P2Winner9CompleteSeedBlock23.rows,
  P2Winner9CompleteSeedBlock24.rows,
  P2Winner9CompleteSeedBlock25.rows,
  P2Winner9CompleteSeedBlock26.rows,
  P2Winner9CompleteSeedBlock27.rows,
  P2Winner9CompleteSeedBlock28.rows,
  P2Winner9CompleteSeedBlock29.rows,
  P2Winner9CompleteSeedBlock30.rows,
  P2Winner9CompleteSeedBlock31.rows,
  P2Winner9CompleteSeedBlock32.rows,
  P2Winner9CompleteSeedBlock33.rows,
  P2Winner9CompleteSeedBlock34.rows,
  P2Winner9CompleteSeedBlock35.rows,
  P2Winner9CompleteSeedBlock36.rows,
  P2Winner9CompleteSeedBlock37.rows,
  P2Winner9CompleteSeedBlock38.rows,
  P2Winner9CompleteSeedBlock39.rows,
  P2Winner9CompleteSeedBlock40.rows,
  P2Winner9CompleteSeedBlock41.rows,
  P2Winner9CompleteSeedBlock42.rows,
  P2Winner9CompleteSeedBlock43.rows
].toArray

def allRows : Array RawRow := blocks.flatten

theorem archive_checked : Checked ArchiveRowCheck 0 11026 allRows := by
  unfold allRows blocks
  exact
    P2Winner9SeedArchiveCheck00.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck01.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck02.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck03.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck04.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck05.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck06.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck07.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck08.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck09.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck10.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck11.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck12.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck13.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck14.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck15.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck16.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck17.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck18.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck19.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck20.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck21.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck22.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck23.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck24.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck25.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck26.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck27.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck28.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck29.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck30.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck31.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck32.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck33.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck34.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck35.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck36.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck37.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck38.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck39.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck40.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck41.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck42.checked.flatten_cons <|
    P2Winner9SeedArchiveCheck43.checked.flatten_single

attribute [local irreducible] allRows

private def certifiedLookup {P : ℕ → RawRow → Prop} {n : ℕ} {rows : Array RawRow}
    (h : Checked P 0 n rows) (i : Fin n) : {r : RawRow // P i.val r ∧ r = rows[i.val]!} :=
  ⟨rows[i.val]!, by simpa only [Nat.zero_add] using h.2 i, rfl⟩

-- Keep ordinal lookup abstract during use of its proof fields. The exact
-- equality below gives access to the original flattened array when needed.
private opaque certifiedEntry (i : RowIndex) :
    {r : RawRow // ArchiveRowCheck i.val r ∧ r = allRows[i.val]!} :=
  @certifiedLookup ArchiveRowCheck 11026 allRows archive_checked i

def entry (i : RowIndex) : RawRow := (certifiedEntry i).val

def physicalVertices (i : RowIndex) (k : Fin 9) : Fin 8 → ℚ :=
  P2Winner9CompleteSeedVertices.coordinates[(entry i).vertexIds k]!

theorem archive_row_check (i : RowIndex) : ArchiveRowCheck i.val (entry i) :=
  (certifiedEntry i).property.1

theorem entry_eq_allRows (i : RowIndex) : entry i = allRows[i.val]! :=
  (certifiedEntry i).property.2

theorem full_source_shapes_and_chronology :
    allRows.size = 11026 ∧ P2Winner9CompleteSeedVertices.coordinates.size = 201 ∧
      ∀ i : RowIndex, RowShape i.val (entry i) :=
  ⟨archive_checked.1, by decide +kernel, fun i => (archive_row_check i).1⟩

private theorem selected_of_check {i : ℕ} {r : RawRow} (h : ArchiveRowCheck i r) :
    r.mixedSelected = max r.logSelected r.mixedRaw := by
  rcases h with ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, hcur, _, hmix⟩, hle⟩
  rw [hmix, hcur, max_assoc, max_eq_right hle]

theorem selected_eq_max_log_mixed (i : RowIndex) :
    (entry i).mixedSelected = max (entry i).logSelected (entry i).mixedRaw :=
  selected_of_check (archive_row_check i)

end ImbalancedChen.P2Winner9CompleteSeedData
