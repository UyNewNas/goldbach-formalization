import ImbalancedChen.P2Winner9CompleteSeedTypes

/-! Indexed checks for pages of the original Winner9 archive. -/

namespace ImbalancedChen.P2Winner9SeedArchiveChecks

open P2Winner9CompleteSeedTypes (RawRow)

abbrev RowShape (i : ℕ) (r : RawRow) : Prop :=
  r.parentId = i ∧ r.logId = i ∧ r.curvatureId = i ∧ r.mixedId = i ∧
    (∀ k : Fin 9, r.vertexIds k < 201) ∧
    r.logGapFloors.size = 10 ∧ r.mixedDegree = 6 ∧ r.mixedMomentFloors.size = 10 ∧
    (∀ j : Fin 10, r.mixedMomentFloors[j.val]!.size = 7) ∧ r.mixedTermFloors.size = 7 ∧
    r.parentJensenFloor = r.logOld ∧ r.curvatureCurrent = r.logSelected ∧
    r.curvatureSelected = max r.logSelected r.curvatureRaw ∧
    r.mixedPrevious = r.curvatureSelected ∧ r.mixedSelected = max r.curvatureSelected r.mixedRaw

abbrev ArchiveRowCheck (i : ℕ) (r : RawRow) : Prop :=
  RowShape i r ∧ r.curvatureRaw ≤ r.mixedRaw

/-- Check the record at each ordinal of a contiguous range. -/
def Checked (P : ℕ → RawRow → Prop) (first count : ℕ) (rows : Array RawRow) : Prop :=
  rows.size = count ∧ ∀ i : Fin count, P (first + i.val) rows[i.val]!

instance (P : ℕ → RawRow → Prop) [DecidableRel P] (first count : ℕ) (rows : Array RawRow) :
    Decidable (Checked P first count rows) := by
  unfold Checked
  infer_instance

namespace Checked

theorem append {P : ℕ → RawRow → Prop} {first n m : ℕ} {xs ys : Array RawRow}
    (hx : Checked P first n xs) (hy : Checked P (first + n) m ys) :
    Checked P first (n + m) (xs ++ ys) := by
  have hsize : (xs ++ ys).size = n + m := by simp [hx.1, hy.1]
  refine ⟨hsize, fun i => ?_⟩
  have hi : i.val < (xs ++ ys).size := hsize.symm ▸ i.isLt
  by_cases hn : i.val < n
  · have hxs : i.val < xs.size := hx.1.symm ▸ hn
    rw [getElem!_pos (xs ++ ys) i.val hi, Array.getElem_append_left hxs,
      ← getElem!_pos xs i.val hxs]
    exact hx.2 ⟨i.val, hn⟩
  · have hp : i.val - n < m := by omega
    have hxs : xs.size ≤ i.val := hx.1.symm ▸ Nat.le_of_not_gt hn
    have hys : i.val - xs.size < ys.size := by simpa only [hx.1, hy.1] using hp
    rw [getElem!_pos (xs ++ ys) i.val hi, Array.getElem_append_right hxs,
      ← getElem!_pos ys (i.val - xs.size) hys, hx.1]
    have h : first + n + (i.val - n) = first + i.val := by omega
    simpa only [h] using hy.2 ⟨i.val - n, hp⟩

theorem flatten_cons {P : ℕ → RawRow → Prop} {first n m : ℕ}
    {xs : Array RawRow} {rest : List (Array RawRow)}
    (hx : Checked P first n xs) (hy : Checked P (first + n) m rest.toArray.flatten) :
    Checked P first (n + m) (xs :: rest).toArray.flatten := by
  have h : (xs :: rest).toArray.flatten = xs ++ rest.toArray.flatten := by
    apply Array.ext'
    simp
  rw [h]
  exact hx.append hy

theorem flatten_single {P : ℕ → RawRow → Prop} {first n : ℕ} {xs : Array RawRow}
    (h : Checked P first n xs) : Checked P first n [xs].toArray.flatten := by
  simpa using h

end Checked

end ImbalancedChen.P2Winner9SeedArchiveChecks
