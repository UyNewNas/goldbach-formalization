import ImbalancedChen.Part5SavedParent394700BuchstabAll32
import ImbalancedChen.Part5SavedParent394700BuchstabCoordinateAPI
import ImbalancedChen.P0All32RowPublicAPI

/-!
SOURCEONLY / UNCOMPILED / NOT PASS. 2026-10-24.

The first import is to be supplied by the pinned y-P5-All32 assembly. The
second import is the separately owned shared coordinate API; the third is
its P0 row-contract consumer. See the companion CP for exact source pins.
No core, row, coordinate supplier, manuscript or constant is rewritten.

This module connects the literal strict parent to its actual Bernstein
row/cell contract. The restriction theorem is polymorphic in a set. It is
not a declaration that a named actual crop has been supplied by this API.
-/

namespace ImbalancedChen.Certificates.SavedParent394700SourceOnly
namespace P0CoordinateOpenParentAPI

open Set
open SavedParent394700ActualBuchstabSourceOnly

noncomputable section

/-- The strict parent has strict argument endpoints, including the ordered
z/w constraint. No endpoint-nullity premise is needed for this theorem. -/
theorem open_parent_argument_range {p : Fin 4 → ℝ} (hp : p ∈ parentOpen) :
    argument p ∈ Ioo sMin sMax := by
  have hz := (parent_coordinates_pos (parentOpen_subset_closure hp)).2.2.1
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have hza : a < p 2 := h4.trans h5
  have hwb : p 3 < b := h5.trans h6
  constructor
  · unfold argument
    apply (lt_div_iff₀ hz).2
    norm_num [sMin, tl, tr, ul, ur, a, b] at *
    linarith only [h1, h3, h6, hwb]
  · unfold argument
    apply (div_lt_iff₀ hz).2
    norm_num [sMax, tl, tr, ul, ur, a, b] at *
    linarith only [h0, h2, hza, h4]

/-- Select one original certified row for every argument in the parent's
closed range. A subdivision endpoint may belong to either adjacent row. -/
theorem argument_has_certified_row {s : ℝ} (hs : s ∈ Icc sMin sMax) :
    ∃ k : Fin 32, ∃ t : ℝ,
      2 * s = (cellIndex k : ℝ) + t ∧
      t ∈ Icc (P0All32RowPublicAPI.rowLeft k) (P0All32RowPublicAPI.rowRight k) := by
  by_cases hten : 2 * s ≤ 11
  · let t : ℝ := 2 * s - 10
    have ht : t ∈ Icc (15454 / 20359 : ℝ) 1 := by
      dsimp [t]
      constructor
      · have h := hs.1
        norm_num [sMin] at h
        linarith only [h]
      · linarith only [hten]
    obtain ⟨j, hj, hjl, hjr⟩ := uniform_cover 16 (15454 / 20359 : ℝ)
      (4905 / 325744 : ℝ) t (by norm_num) (by norm_num) ht.1
      (by convert! ht.2 using 1 <;> norm_num)
    let k : Fin 32 := ⟨j, by omega⟩
    have hk : k.val < 16 := by simpa only [k] using hj
    have hcell : cellIndex k = 10 := by simp only [cellIndex, if_pos hk]
    have hleft : P0All32RowPublicAPI.rowLeft k =
        15454 / 20359 + (j : ℝ) * (4905 / 325744) := by
      simp only [P0All32RowPublicAPI.rowLeft, if_pos hk, k]
      ring
    have hright : P0All32RowPublicAPI.rowRight k =
        15454 / 20359 + ((j : ℝ) + 1) * (4905 / 325744) := by
      simp only [P0All32RowPublicAPI.rowRight, if_pos hk, k]
      ring
    refine ⟨k, t, ?_, ?_⟩
    · rw [hcell]
      dsimp [t]
      push_cast
      ring
    · simpa only [mem_Icc, hleft, hright] using And.intro hjl hjr
  · let t : ℝ := 2 * s - 11
    have ht : t ∈ Icc (0 : ℝ) (883 / 10008) := by
      dsimp [t]
      constructor
      · linarith only [hten]
      · have h := hs.2
        norm_num [sMax] at h
        linarith only [h]
    obtain ⟨j, hj, hjl, hjr⟩ := uniform_cover 16 (0 : ℝ)
      (883 / 160128 : ℝ) t (by norm_num) (by norm_num) ht.1
      (by convert! ht.2 using 1 <;> norm_num)
    let k : Fin 32 := ⟨16 + j, by omega⟩
    have hk : ¬k.val < 16 := by dsimp [k]; omega
    have hjk : k.val - 16 = j := by dsimp [k]; omega
    have hcell : cellIndex k = 11 := by simp only [cellIndex, if_neg hk]
    have hleft : P0All32RowPublicAPI.rowLeft k = (j : ℝ) * (883 / 160128) := by
      simp only [P0All32RowPublicAPI.rowLeft, if_neg hk, hjk]
      ring
    have hright : P0All32RowPublicAPI.rowRight k =
        ((j : ℝ) + 1) * (883 / 160128) := by
      simp only [P0All32RowPublicAPI.rowRight, if_neg hk, hjk]
      ring
    refine ⟨k, t, ?_, ?_⟩
    · rw [hcell]
      dsimp [t]
      push_cast
      ring
    · simpa only [mem_Icc, hleft, hright, zero_add] using And.intro hjl hjr

/-- The shared scalar coordinate is attached to the selected real cell.
The coefficient list is the actual row's original coefficient list. -/
theorem open_parent_coordinate_cell_contract {p : Fin 4 → ℝ}
    (hp : p ∈ parentOpen) :
    ∃ k : Fin 32, ∃ t : ℝ,
      2 * argument p = (cellIndex k : ℝ) + t ∧
      t ∈ Icc (P0All32RowPublicAPI.rowLeft k) (P0All32RowPublicAPI.rowRight k) ∧
      (10 ≤ cellIndex k ∧ cellIndex k ≤ 11) ∧
      BernsteinGood k ∧
      (∀ i : ℕ, (bernsteinSumFrom 52 0 (bernsteinCoefficients k)).getD i 0 =
        FiniteBernsteinCoordinate.column 52 i 0 (bernsteinCoefficients k)) ∧
      0 ≤ evalList (barrierList (cellIndex k)) t ∧
      evalList (row (cellIndex k)) t + (err (cellIndex k) : ℝ) ≤
        (omegaHalf : ℝ) * ((cellIndex k : ℝ) + t) := by
  have hrange := open_parent_argument_range hp
  obtain ⟨k, t, harg, ht⟩ := argument_has_certified_row ⟨hrange.1.le, hrange.2.le⟩
  refine ⟨k, t, harg, ht, P0All32RowPublicAPI.cellIndex_bounds k,
    P0All32RowPublicAPI.all_rows_good k, ?_,
    P0All32RowPublicAPI.row_barrier_nonneg k ht,
    P0All32RowPublicAPI.row_polynomial_upper k ht⟩
  intro i
  exact FiniteBernsteinCoordinate.getD_bernsteinSumFrom 52 i 0 (bernsteinCoefficients k)

/-- The existing actual saved-density licence on the literal strict parent. -/
theorem open_parent_savedDensity_ge_actual {p : Fin 4 → ℝ}
    (hp : p ∈ parentOpen) :
    K * LiLiuPrereqBuchstab.buchstab (argument p) / p 2 ≤ savedDensity (p 2) := by
  exact original_savedDensity_ge_actual_on_parent (parentOpen_subset_closure hp)

/-- The Chen-quarter factor and actual fibre kernel are unchanged. -/
theorem open_parent_savedChenDensity_ge_actual_kernel {p : Fin 4 → ℝ}
    (hp : p ∈ parentOpen) :
    (K / 4) * LiLiuPrereqBuchstab.buchstab (argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤ savedChenDensity p := by
  exact original_savedChenDensity_ge_actual_kernel (parentOpen_subset_closure hp)

/-- Safe set restriction of the actual pointwise kernel theorem. Supplying
an independently defined crop set is enough to instantiate this theorem. -/
theorem restricted_open_parent_savedChenDensity_ge_actual_kernel
    (S : Set (Fin 4 → ℝ)) {p : Fin 4 → ℝ} (hp : p ∈ parentOpen ∩ S) :
    (K / 4) * LiLiuPrereqBuchstab.buchstab (argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤ savedChenDensity p := by
  exact open_parent_savedChenDensity_ge_actual_kernel hp.1

/-- The selected row/cell contract remains available after set restriction. -/
theorem restricted_open_parent_has_certified_row
    (S : Set (Fin 4 → ℝ)) {p : Fin 4 → ℝ} (hp : p ∈ parentOpen ∩ S) :
    ∃ k : Fin 32, ∃ t : ℝ,
      2 * argument p = (cellIndex k : ℝ) + t ∧
      t ∈ Icc (P0All32RowPublicAPI.rowLeft k) (P0All32RowPublicAPI.rowRight k) := by
  have hrange := open_parent_argument_range hp.1
  exact argument_has_certified_row ⟨hrange.1.le, hrange.2.le⟩

end
end P0CoordinateOpenParentAPI
end ImbalancedChen.Certificates.SavedParent394700SourceOnly

