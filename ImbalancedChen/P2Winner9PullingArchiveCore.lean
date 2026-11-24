import ImbalancedChen.P2Winner9OriginalPullingFlags

/-!
# A complete-archive interface to the original pulling proof

The witnesses contain only packed finite data.  Their order and every new
row are checked separately.  The first 256 pulling flags use the already
proved original checker, with only their new global ranks checked again.
-/

namespace ImbalancedChen.P2Winner9PullingArchiveCore

open MeasureTheory
open P2Winner9LiftingGeometry
open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9CompleteSeedVertices (coordinates)
open P2Winner9SeedVertexAnalyticGuards (VertexIndex originalPoint)
open P2Winner9SeedArchiveChecks (Checked)
open P2Winner9OriginalPullingFlags (GateIndex plane mask rowID originalSupport)

set_option maxRecDepth 20000

/-- Finite packed data, with no geometric or analytic hypotheses. -/
structure Witnesses where
  count : ℕ
  geometryWord : ℕ → ℕ
  orderedWord : ℕ → ℕ

namespace Witnesses

def rankAt (w : Witnesses) (ordinal : ℕ) : ℕ := w.geometryWord ordinal % 2^14
def ordinalAt (w : Witnesses) (rank : ℕ) : ℕ := w.orderedWord rank % 2^14
def orderedKey (w : Witnesses) (rank : ℕ) : ℕ := w.orderedWord rank >>> 14
def keyAt (w : Witnesses) (ordinal : ℕ) : ℕ := w.orderedKey (w.rankAt ordinal)

/-- The already accepted first-block flags are reused literally. -/
def flagsAt (w : Witnesses) (ordinal : ℕ) : List GateIndex :=
  if ordinal < 256 then P2Winner9OriginalPullingFlags.flagsAt ordinal
  else List.ofFn fun j : Fin 8 =>
    Fin.ofNat 21 ((w.geometryWord ordinal >>> (14 + 5 * j.val)) % 32)

/-- Only the global key/rank binding is new for an accepted prefix row. -/
def prefixCompatible (w : Witnesses) (ordinal : ℕ) : Bool :=
  decide (w.keyAt ordinal = P2Winner9OriginalPullingFlags.keyAt ordinal ∧
    w.rankAt ordinal < w.count ∧ w.ordinalAt (w.rankAt ordinal) = ordinal)

def checkedRow (w : Witnesses) (ordinal : ℕ) (row : RawRow) : Bool :=
  if ordinal < 256 then
    P2Winner9OriginalPullingFlags.checkedRow ordinal row && w.prefixCompatible ordinal
  else
    (List.ofFn row.vertexIds).all (fun v => decide (v < 201)) &&
      pullingCheck mask (2^201 - 1) (rowID row 0) (rowTail (rowID row))
        (w.flagsAt ordinal) &&
      decide (w.keyAt ordinal = vertexKey (rowID row) ∧ w.rankAt ordinal < w.count ∧
        w.ordinalAt (w.rankAt ordinal) = ordinal)

theorem checkedRow_of_original (w : Witnesses) {ordinal : ℕ} {row : RawRow}
    (ho : ordinal < 256)
    (h : P2Winner9OriginalPullingFlags.checkedRow ordinal row = true)
    (hc : w.prefixCompatible ordinal = true) : w.checkedRow ordinal row = true := by
  simp only [checkedRow, if_pos ho, Bool.and_eq_true]
  exact ⟨h, hc⟩

theorem checkedRow_sound (w : Witnesses) {ordinal : ℕ} {row : RawRow}
    (h : w.checkedRow ordinal row = true) :
    (∀ k, (rowID row k).val = row.vertexIds k) ∧
      pullingCheck mask (2^201 - 1) (rowID row 0) (rowTail (rowID row))
        (w.flagsAt ordinal) = true ∧
      w.keyAt ordinal = vertexKey (rowID row) ∧ w.rankAt ordinal < w.count ∧
      w.ordinalAt (w.rankAt ordinal) = ordinal := by
  by_cases ho : ordinal < 256
  · simp only [checkedRow, if_pos ho, Bool.and_eq_true] at h
    have hp := P2Winner9OriginalPullingFlags.checkedRow_sound h.1
    have hc : w.keyAt ordinal = P2Winner9OriginalPullingFlags.keyAt ordinal ∧
        w.rankAt ordinal < w.count ∧ w.ordinalAt (w.rankAt ordinal) = ordinal :=
      of_decide_eq_true h.2
    refine ⟨hp.1, ?_, hc.1.trans hp.2.2.1, hc.2⟩
    simpa only [flagsAt, if_pos ho] using hp.2.1
  · simp only [checkedRow, if_neg ho, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at h
    refine ⟨fun k => ?_, h.1.2, h.2⟩
    have hk := h.1.1 (row.vertexIds k) (List.mem_ofFn.mpr ⟨k, rfl⟩)
    exact Nat.mod_eq_of_lt hk

theorem prefix_checked (w : Witnesses)
    (hc : ∀ i : Fin 256, w.prefixCompatible i.val = true) :
    Checked (fun ordinal row => w.checkedRow ordinal row = true) 0 256
      P2Winner9CompleteSeedBlock00.rows := by
  refine ⟨P2Winner9OriginalPullingFlags.block00_checked.1, fun i => ?_⟩
  simp only [Nat.zero_add]
  apply w.checkedRow_of_original i.isLt
  · simpa only [Nat.zero_add] using P2Winner9OriginalPullingFlags.block00_checked.2 i
  · exact hc i

theorem checkedKeys_injective (w : Witnesses)
    (hs : StrictMono (fun i : Fin w.count => w.orderedKey i.val))
    {a b : ℕ} {ra rb : RawRow}
    (ha : w.checkedRow a ra = true) (hb : w.checkedRow b rb = true)
    (he : w.keyAt a = w.keyAt b) : a = b := by
  let ia : Fin w.count := ⟨w.rankAt a, (w.checkedRow_sound ha).2.2.2.1⟩
  let ib : Fin w.count := ⟨w.rankAt b, (w.checkedRow_sound hb).2.2.2.1⟩
  have hindex : ia = ib := hs.injective he
  have h : w.ordinalAt (w.rankAt a) = w.ordinalAt (w.rankAt b) :=
    congrArg (fun i : Fin w.count => w.ordinalAt i.val) hindex
  rwa [(w.checkedRow_sound ha).2.2.2.2, (w.checkedRow_sound hb).2.2.2.2] at h

/-- Global ordering distinguishes cells even when they belong to different archive blocks. -/
theorem archive_overlap_null (w : Witnesses)
    (hs : StrictMono (fun i : Fin w.count => w.orderedKey i.val))
    {first count : ℕ} {rows : Array RawRow}
    (checked : Checked (fun ordinal row => w.checkedRow ordinal row = true) first count rows) :
    Pairwise fun i j : Fin count =>
      volume (cellSupport originalPoint (fun k => rowID rows[k.val]!) i ∩
        cellSupport originalPoint (fun k => rowID rows[k.val]!) j) = 0 := by
  apply checked_pulling_overlap_null originalPoint plane mask _
    (fun i => w.flagsAt (first + i.val))
    P2Winner9OriginalPullingFlags.mask_correct P2Winner9OriginalPullingFlags.plane_nonneg
  · intro i
    exact (w.checkedRow_sound (checked.2 i)).2.1
  · intro i j hij
    apply Fin.val_injective
    have he : w.keyAt (first + i.val) = w.keyAt (first + j.val) := by
      rw [(w.checkedRow_sound (checked.2 i)).2.2.1,
        (w.checkedRow_sound (checked.2 j)).2.2.1]
      unfold vertexKey
      exact congrArg (fun s : Finset VertexIndex => ∑ v ∈ s, 2 ^ v.val) hij
    exact Nat.add_left_cancel (w.checkedKeys_injective hs (checked.2 i) (checked.2 j) he)

theorem checkedRow_support (w : Witnesses) {ordinal : ℕ} {row : RawRow}
    (h : w.checkedRow ordinal row = true) :
    P2Winner9SelectedRowRealJacobian.sourceSupport (fun k => originalPoint (rowID row k)) =
      originalSupport row := by
  unfold originalSupport
  congr 1
  funext k
  simp only [originalPoint, (w.checkedRow_sound h).1 k]

theorem archive_actual_overlap_null (w : Witnesses)
    (hs : StrictMono (fun i : Fin w.count => w.orderedKey i.val))
    {first count : ℕ} {rows : Array RawRow}
    (checked : Checked (fun ordinal row => w.checkedRow ordinal row = true) first count rows) :
    Pairwise fun i j : Fin count =>
      volume (originalSupport rows[i.val]! ∩ originalSupport rows[j.val]!) = 0 := by
  intro i j hij
  have hi : cellSupport originalPoint (fun k : Fin count => rowID rows[k.val]!) i =
      originalSupport rows[i.val]! := w.checkedRow_support (checked.2 i)
  have hj : cellSupport originalPoint (fun k : Fin count => rowID rows[k.val]!) j =
      originalSupport rows[j.val]! := w.checkedRow_support (checked.2 j)
  simpa only [hi, hj] using w.archive_overlap_null hs checked hij

end Witnesses

end ImbalancedChen.P2Winner9PullingArchiveCore
