import ImbalancedChen.P0All32RowPublicAPI

/- SOURCEONLY: stage the companion All32RowPublicAPI draft under the imported
module name. This module reuses the assembly's proved uniform_cover. -/
namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
namespace P0All32RowOverlapAPI

open Set P0All32RowPublicAPI
noncomputable section

def ten (j : Fin 16) : Fin 32 := ⟨j.val, by have h := j.isLt; omega⟩
def eleven (j : Fin 16) : Fin 32 := ⟨16 + j.val, by have h := j.isLt; omega⟩

theorem ten_cell (j : Fin 16) : cellIndex (ten j) = 10 := by
  have hj := j.isLt
  simp [cellIndex, ten, hj]

theorem eleven_cell (j : Fin 16) : cellIndex (eleven j) = 11 := by
  have hj : ¬16 + j.val < 16 := by omega
  simp [cellIndex, eleven, hj]

theorem ten_left (j : Fin 16) :
    rowLeft (ten j) = 15454 / 20359 + (j.val : ℝ) * (4905 / 325744) := by
  have hj := j.isLt
  simp only [rowLeft, ten, if_pos hj]
  norm_num
  <;> ring

theorem ten_right (j : Fin 16) :
    rowRight (ten j) = 15454 / 20359 + ((j.val : ℝ) + 1) * (4905 / 325744) := by
  have hj := j.isLt
  simp only [rowRight, ten, if_pos hj]
  norm_num
  <;> ring

theorem eleven_left (j : Fin 16) :
    rowLeft (eleven j) = (j.val : ℝ) * (883 / 160128) := by
  have hj : ¬16 + j.val < 16 := by omega
  simp [rowLeft, eleven, hj]
  <;> ring

theorem eleven_right (j : Fin 16) :
    rowRight (eleven j) = ((j.val : ℝ) + 1) * (883 / 160128) := by
  have hj : ¬16 + j.val < 16 := by omega
  simp [rowRight, eleven, hj]
  <;> ring

/-- Adjacency is restricted to a single original cell: the gap between global
indices 15 and 16 changes cells and is deliberately not asserted equal. -/
theorem ten_adjacent (j l : Fin 16) (hnext : j.val + 1 = l.val) :
    rowRight (ten j) = rowLeft (ten l) := by
  have hr : (j.val : ℝ) + 1 = (l.val : ℝ) := by exact_mod_cast hnext
  rw [ten_right, ten_left, hr]

theorem eleven_adjacent (j l : Fin 16) (hnext : j.val + 1 = l.val) :
    rowRight (eleven j) = rowLeft (eleven l) := by
  have hr : (j.val : ℝ) + 1 = (l.val : ℝ) := by exact_mod_cast hnext
  rw [eleven_right, eleven_left, hr]

/-- Global row succession crosses two different original cells at 15/16. -/
theorem family_boundary_cells :
    cellIndex (ten (15 : Fin 16)) = 10 ∧
      cellIndex (eleven (0 : Fin 16)) = 11 := by
  exact ⟨ten_cell _, eleven_cell _⟩

/-- The first family's final coordinate is 1; the second restarts at 0. -/
theorem family_boundary_endpoints :
    rowRight (ten (15 : Fin 16)) = 1 ∧
      rowLeft (eleven (0 : Fin 16)) = 0 := by
  constructor
  · rw [ten_right]
    norm_num
  · rw [eleven_left]
    norm_num

/-- The global 15/16 boundary is not an endpoint overlap in local coordinates. -/
theorem family_boundary_not_adjacent :
    rowRight (ten (15 : Fin 16)) ≠ rowLeft (eleven (0 : Fin 16)) := by
  rw [family_boundary_endpoints.1, family_boundary_endpoints.2]
  norm_num
/-- Closed certificates both apply to their shared endpoint. -/
theorem shared_endpoint (k l : Fin 32)
    (he : rowRight k = rowLeft l) :
    0 ≤ evalList (barrierList (cellIndex k)) (rowRight k) ∧
    0 ≤ evalList (barrierList (cellIndex l)) (rowRight k) := by
  constructor
  · exact row_barrier_nonneg k ⟨(rowLeft_lt_rowRight k).le, le_rfl⟩
  · apply row_barrier_nonneg l
    constructor
    · exact he.symm.le
    · rw [he]
      exact (rowLeft_lt_rowRight l).le

theorem ten_endpoint_compatible (j l : Fin 16) (hnext : j.val + 1 = l.val) :
    0 ≤ evalList (barrierList 10) (rowRight (ten j)) ∧
    rowRight (ten j) = rowLeft (ten l) := by
  have he := ten_adjacent j l hnext
  have hb := (shared_endpoint (ten j) (ten l) he).1
  exact ⟨by simpa only [ten_cell] using hb, he⟩

theorem eleven_endpoint_compatible (j l : Fin 16) (hnext : j.val + 1 = l.val) :
    0 ≤ evalList (barrierList 11) (rowRight (eleven j)) ∧
    rowRight (eleven j) = rowLeft (eleven l) := by
  have he := eleven_adjacent j l hnext
  have hb := (shared_endpoint (eleven j) (eleven l) he).1
  exact ⟨by simpa only [eleven_cell] using hb, he⟩

theorem ten_closed_cover {t : ℝ} (ht : t ∈ Icc (15454 / 20359 : ℝ) 1) :
    ∃ j : Fin 16, t ∈ Icc (rowLeft (ten j)) (rowRight (ten j)) := by
  obtain ⟨n, hn, hl, hr⟩ := uniform_cover 16 (15454 / 20359 : ℝ)
    (4905 / 325744 : ℝ) t (by norm_num) (by norm_num) ht.1
      (by convert ht.2 using 1 <;> norm_num)
  refine ⟨⟨n, hn⟩, ?_⟩
  rw [mem_Icc, ten_left, ten_right]
  exact ⟨hl, hr⟩

theorem eleven_closed_cover {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (883 / 10008)) :
    ∃ j : Fin 16, t ∈ Icc (rowLeft (eleven j)) (rowRight (eleven j)) := by
  obtain ⟨n, hn, hl, hr⟩ := uniform_cover 16 (0 : ℝ)
    (883 / 160128 : ℝ) t (by norm_num) (by norm_num) ht.1
      (by convert ht.2 using 1 <;> norm_num)
  refine ⟨⟨n, hn⟩, ?_⟩
  rw [mem_Icc, eleven_left, eleven_right]
  exact ⟨by simpa only [zero_add] using hl, by simpa only [zero_add] using hr⟩

/-- The two original coordinate domains, with their actual cell index. -/
def CoveredPoint (c : ℕ) (t : ℝ) : Prop :=
  (c = 10 ∧ t ∈ Icc (15454 / 20359 : ℝ) 1) ∨
  (c = 11 ∧ t ∈ Icc (0 : ℝ) (883 / 10008))

theorem closed_row_cover {c : ℕ} {t : ℝ} (h : CoveredPoint c t) :
    ∃ k : Fin 32, cellIndex k = c ∧ t ∈ Icc (rowLeft k) (rowRight k) := by
  rcases h with ⟨rfl, ht⟩ | ⟨rfl, ht⟩
  · obtain ⟨j, hj⟩ := ten_closed_cover ht
    exact ⟨ten j, ten_cell j, hj⟩
  · obtain ⟨j, hj⟩ := eleven_closed_cover ht
    exact ⟨eleven j, eleven_cell j, hj⟩

/-- A closed endpoint may choose either incident row. Every valid choice
produces the same barrier expression for the requested original cell. -/
def chooseRow (c : ℕ) (t : ℝ) (h : CoveredPoint c t) : Fin 32 :=
  Classical.choose (closed_row_cover h)

theorem chooseRow_spec (c : ℕ) (t : ℝ) (h : CoveredPoint c t) :
    cellIndex (chooseRow c t h) = c ∧
      t ∈ Icc (rowLeft (chooseRow c t h)) (rowRight (chooseRow c t h)) := by
  exact Classical.choose_spec (closed_row_cover h)

theorem pointwise_barrier {c : ℕ} {t : ℝ} (h : CoveredPoint c t) :
    0 ≤ evalList (barrierList c) t := by
  have hs := chooseRow_spec c t h
  have hb := row_barrier_nonneg (chooseRow c t h) hs.2
  simpa only [hs.1] using hb

theorem pointwise_polynomial_upper {c : ℕ} {t : ℝ} (h : CoveredPoint c t) :
    evalList (row c) t + (err c : ℝ) ≤ (omegaHalf : ℝ) * ((c : ℝ) + t) := by
  have hs := chooseRow_spec c t h
  have hb := row_polynomial_upper (chooseRow c t h) hs.2
  simpa only [hs.1] using hb

end
end P0All32RowOverlapAPI
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly


