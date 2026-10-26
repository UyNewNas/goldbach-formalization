import ImbalancedChen.P5PresievedFineLabelPrimeBoxes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite fine-label mesh cover for the ORIGINAL residual upper-prefix AND
order gates at every fixed rank. Every crossing arithmetic cell is charged
to an actual proper affine row strip of width norm(row)*meshStep. Rank0
and disabled parity/order rows remain exact constants. No arithmetic
boundary prime is deleted using continuous nullity.
-/
namespace ImbalancedChen.P5Z.PresievedRoughGateMeshReserve
noncomputable section
open Set Classical
open scoped BigOperators
open PresievedRoughSlotAffineGates

abbrev Grid (r n : ℕ) := Fin r → Fin (n + 1)
abbrev GateSlot (r : ℕ) := Unit ⊕ Fin r ⊕ (Fin r × Fin r)

def row {r : ℕ} : GateSlot r → (Fin r → ℝ) →L[ℝ] ℝ
  | .inl _ => totalRow r
  | .inr (.inl i) => if Even i.val then cubeRow i else 0
  | .inr (.inr (i, j)) => if i < j then ContinuousLinearMap.proj j - ContinuousLinearMap.proj i else 0

def offset {r : ℕ} (ell : ℝ) : GateSlot r → ℝ
  | .inl _ => ell
  | .inr (.inl i) => if Even i.val then ell else 1
  | .inr (.inr (i, j)) => if i < j then 0 else 1

def roughRegion (r : ℕ) (ell : ℝ) : Set (Fin r → ℝ) :=
  {v | ∀ g : GateSlot r, row g v < offset ell g}

/-- Exact original strict upper-prefix tests together with literal
descending slot order, including all equality faces in the complement. -/
theorem roughRegion_dictionary {r : ℕ} (ell : ℝ) (v : Fin r → ℝ) :
    v ∈ roughRegion r ell ↔ v ∈ region r ell ∧ StrictAnti v := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [row, offset, totalRow, ContinuousLinearMap.sum_apply] using h (.inl ())
    · intro i hi
      simpa [row, offset, hi, cubeRow_apply] using h (.inr (.inl i))
    · intro i j hij
      have hg := h (.inr (.inr (i, j)))
      simpa [row, offset, hij, sub_lt_zero] using hg
  · rintro ⟨⟨ht, hc⟩, hanti⟩ g
    rcases g with _ | (i | ⟨i, j⟩)
    · simpa [row, offset, totalRow, ContinuousLinearMap.sum_apply] using ht
    · by_cases hi : Even i.val
      · simpa [row, offset, hi, cubeRow_apply] using hc i hi
      · simp [row, offset, hi]
    · by_cases hij : i < j
      · simpa [row, offset, hij, sub_lt_zero] using hanti hij
      · simp [row, offset, hij]

def cell {r : ℕ} (a b : ℝ) (n : ℕ) (j : Grid r n) : Set (Fin r → ℝ) :=
  logPrimeMeshCell a b n j

def innerCells (r : ℕ) (a b ell : ℝ) (n : ℕ) : Finset (Grid r n) :=
  Finset.univ.filter (fun j => ∀ v ∈ cell a b n j, v ∈ roughRegion r ell)

def outerCells (r : ℕ) (a b ell : ℝ) (n : ℕ) : Finset (Grid r n) :=
  Finset.univ.filter (fun j => (cell a b n j ∩ roughRegion r ell).Nonempty)

def wallReserve (r : ℕ) (a b ell : ℝ) (n : ℕ) (v : Fin r → ℝ) : Prop :=
  ∃ g : GateSlot r, row g ≠ 0 ∧ |row g v - offset ell g| ≤ ‖row g‖ * logPrimeMeshStep a b n

theorem same_cell_norm_sub {r n : ℕ} {a b : ℝ} (hab : a < b) {j : Grid r n}
    {v w : Fin r → ℝ} (hv : v ∈ cell a b n j) (hw : w ∈ cell a b n j) :
    ‖v - w‖ ≤ logPrimeMeshStep a b n := by
  apply (pi_norm_le_iff_of_nonneg (logPrimeMeshStep_pos hab n).le).mpr
  intro i
  have hi := mem_logPrimeMeshCell.mp hv i
  have hj := mem_logPrimeMeshCell.mp hw i
  have he := logPrimeMeshHi_eq_lo_add_step a b n j i
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem same_cell_row_oscillation {r n : ℕ} {a b : ℝ} (hab : a < b) {j : Grid r n}
    {v w : Fin r → ℝ} (hv : v ∈ cell a b n j) (hw : w ∈ cell a b n j) (g : GateSlot r) :
    |row g v - row g w| ≤ ‖row g‖ * logPrimeMeshStep a b n := by
  have h := (row g).le_opNorm (v - w)
  rw [map_sub, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (same_cell_norm_sub hab hv hw) (norm_nonneg _))

/-- A concrete original rough gate changes truth in a mesh cell only
inside this actual row strip. Properness is derived, never assumed. -/
theorem crossing_cell_wall {r n : ℕ} {a b ell : ℝ} (hab : a < b) {j : Grid r n}
    (hout : j ∈ outerCells r a b ell n) (hin : j ∉ innerCells r a b ell n)
    {v : Fin r → ℝ} (hv : v ∈ cell a b n j) : wallReserve r a b ell n v := by
  obtain ⟨x, hx, hgood⟩ := (Finset.mem_filter.mp hout).2
  have hbad : ∃ y ∈ cell a b n j, y ∉ roughRegion r ell := by
    by_contra h
    push_neg at h
    exact hin (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨y, hy, hbad⟩ := hbad
  have hgate : ∃ g : GateSlot r, ¬ row g y < offset ell g := by
    by_contra h
    push_neg at h
    exact hbad h
  obtain ⟨g, hgate⟩ := hgate
  have hproper : row g ≠ 0 := by
    intro hz
    apply hgate
    simpa only [hz, ContinuousLinearMap.zero_apply] using hgood g
  have hleft := (hgood g).le
  have hright := le_of_not_gt hgate
  have hoscx := same_cell_row_oscillation hab hv hx g
  have hoscy := same_cell_row_oscillation hab hv hy g
  refine ⟨g, hproper, abs_le.mpr ⟨?_, ?_⟩⟩
  · have h := (abs_le.mp hoscy).1
    linarith
  · have h := (abs_le.mp hoscx).2
    linarith

/-- Every original rough log point in the fixed box has an OUTER fine
label cell. Failure of its whole-cell certificate is paid by a real wall. -/
theorem actual_point_fine_cell_or_wall {r : ℕ} {a b ell : ℝ} (hab : a < b) (n : ℕ)
    {v : Fin r → ℝ} (hbox : v ∈ logPrimeBox (fun _ => a) (fun _ => b))
    (hv : v ∈ roughRegion r ell) :
    ∃ j ∈ outerCells r a b ell n, v ∈ cell a b n j ∧
      (j ∈ innerCells r a b ell n ∨ wallReserve r a b ell n v) := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell a b n hbox
  have hout : j ∈ outerCells r a b ell n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hj, hv⟩
  refine ⟨j, hout, hj, ?_⟩
  by_cases hin : j ∈ innerCells r a b ell n
  · exact Or.inl hin
  · exact Or.inr (crossing_cell_wall hab hout hin hj)

end
end ImbalancedChen.P5Z.PresievedRoughGateMeshReserve
