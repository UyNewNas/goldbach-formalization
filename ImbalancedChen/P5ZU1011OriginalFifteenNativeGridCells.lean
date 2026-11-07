import ImbalancedChen.P5ZU1011OriginalFifteenFixedCellNative
import ImbalancedChen.SelectedPrefixRationalMesh

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual finite original15-mask x uniform4d-rational-grid native cells. A cell
is active only when the concrete separate whole-box Boolean test is true.
Each active cell owns its N-independent rational native parameters and ONE
common residual coefficient. Half-open geometric ownership is unique,
including exact grid walls. W16 is a distinct separately owned branch.

Different policies may be active on the SAME geometric cell. The marked
finite carrier below retains that multiplicity explicitly. No sum over all
candidate policies is claimed to bound the original count. Selecting one
adaptive winner, proving coverage away from actual proper-wall strips, and
physical AP/density/mean licenses remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenNativeGridCells

noncomputable section
open scoped BigOperators
open Classical
open Set U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts

abbrev Grid (n : ℕ) := Fin 4 → Fin (n + 1)
abbrev Index (n : ℕ) := Fin 15 × Grid n
def lower : ℚ := 417 / 5000
def upper : ℚ := 59 / 250
def cube : Set LogFour := logPrimeBox (fun _ => (lower : ℝ)) (fun _ => (upper : ℝ))
def cell (n : ℕ) (j : Grid n) : Set LogFour := logPrimeMeshCell (lower : ℝ) (upper : ℝ) n j
def gridBox (n : ℕ) (j : Grid n) : Box :=
  ⟨qLogPrimeMeshLo lower upper n j,qLogPrimeMeshHi lower upper n j⟩
def policy {n : ℕ} (i : Index n) : Policy := ⟨i.1.val,by have h := i.1.isLt; omega⟩

theorem policy_lt_fifteen {n : ℕ} (i : Index n) : (policy i).val < 15 := i.1.isLt

theorem cast_grid_lo (n : ℕ) (j : Grid n) (i : Fin 4) :
    ((gridBox n j).lo i : ℝ) = logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i :=
  congrFun (cast_qLogPrimeMeshLo lower upper n j) i
theorem cast_grid_hi (n : ℕ) (j : Grid n) (i : Fin 4) :
    ((gridBox n j).hi i : ℝ) = logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i :=
  congrFun (cast_qLogPrimeMeshHi lower upper n j) i

theorem gridBox_valid (n : ℕ) (j : Grid n) : (gridBox n j).Valid := by
  intro i
  have h := (logPrimeMeshLoHi_bounds (by norm_num [lower,upper] : (lower : ℝ) < (upper : ℝ)) n j i).2.1.le
  rw [← cast_grid_lo,← cast_grid_hi] at h
  exact_mod_cast h

theorem gridBox_lower_positive (n : ℕ) (j : Grid n) (i : Fin 4) : 0 < (gridBox n j).lo i := by
  have h := (logPrimeMeshLoHi_bounds (by norm_num [lower,upper] : (lower : ℝ) < (upper : ℝ)) n j i).1
  rw [← cast_grid_lo] at h
  have hp : (0 : ℝ) < ((gridBox n j).lo i : ℝ) := lt_of_lt_of_le (by norm_num [lower]) h
  exact_mod_cast hp

theorem cell_subset_closed_box (n : ℕ) (j : Grid n) : cell n j ⊆ (gridBox n j).region := by
  intro v hv
  have h := mem_logPrimeMeshCell.mp hv
  constructor
  · intro i
    rw [cast_grid_lo]
    exact (h i).1
  · intro i
    rw [cast_grid_hi]
    exact (h i).2.le

/-- Every original cube point has exactly ONE geometric cell. Closed
rational boxes are used for native safety, never for multiple ownership. -/
theorem unique_cell (n : ℕ) {v : LogFour} (hv : v ∈ cube) : ∃! j : Grid n, v ∈ cell n j := by
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell (lower : ℝ) (upper : ℝ) n hv
  refine ⟨j,hj,?_⟩
  intro k hk
  exact logPrimeMeshCell_unique (by norm_num [lower,upper]) hk hj

def owner (n : ℕ) (v : LogFour) : Grid n :=
  if hv : v ∈ cube then Classical.choose (unique_cell n hv).exists else fun _ => 0

theorem owner_mem (n : ℕ) {v : LogFour} (hv : v ∈ cube) : v ∈ cell n (owner n v) := by
  simp only [owner,dif_pos hv]
  exact Classical.choose_spec (unique_cell n hv).exists

theorem owner_eq_of_mem (n : ℕ) {v : LogFour} {j : Grid n} (hj : v ∈ cell n j) : owner n v = j := by
  have hv : v ∈ cube := logPrimeMeshCell_subset_box
    (by norm_num [lower,upper] : (lower : ℝ) < (upper : ℝ)) n j hj
  exact logPrimeMeshCell_unique (by norm_num [lower,upper]) (owner_mem n hv) hj

/-- The active bank is an ACTUAL finite Boolean-filtered set, independent
of N and of all arithmetic prime tuples. -/
def activeCells (n : ℕ) : Finset (Index n) := Finset.univ.filter
  (fun i => wholeBoxEligibleTest (policy i) (gridBox n i.2) = true)

theorem mem_activeCells {n : ℕ} (i : Index n) : i ∈ activeCells n ↔
    wholeBoxEligibleTest (policy i) (gridBox n i.2) = true := by simp [activeCells]

abbrev ActiveCell (n : ℕ) := {i : Index n // i ∈ activeCells n}

/-- Rational parameters of the finite fixed-level physical family. -/
def fixedNu {n : ℕ} (c : ActiveCell n) : ℚ :=
  U1011OriginalFifteenFixedCellNative.nu (policy c.val) (gridBox n c.val.2)
def fixedDelta {n : ℕ} (c : ActiveCell n) : ℚ :=
  U1011OriginalFifteenFixedCellNative.delta (policy c.val) (gridBox n c.val.2)
def fixedXi {n : ℕ} (c : ActiveCell n) : ℚ :=
  U1011OriginalFifteenFixedCellNative.xi (policy c.val) (gridBox n c.val.2)
def fixedRho {n : ℕ} (c : ActiveCell n) : ℚ :=
  U1011OriginalFifteenFixedCellNative.rho (policy c.val) (gridBox n c.val.2)
def support {n : ℕ} (c : ActiveCell n) (N : ℕ) : Finset ℕ :=
  U1011OriginalFifteenFixedCellNative.support (policy c.val) (gridBox n c.val.2) N
def coefficient {n : ℕ} (c : ActiveCell n) (N d : ℕ) : ℝ :=
  U1011OriginalFifteenFixedCellNative.coefficient (policy c.val) (gridBox n c.val.2) N d

theorem active_parameters {n : ℕ} (c : ActiveCell n) :
    (1 / 2 : ℚ) < fixedNu c ∧ 0 < fixedDelta c ∧ 0 < fixedXi c ∧ 0 < fixedRho c := by
  have ht := (mem_activeCells c.val).mp c.property
  have h := U1011OriginalFifteenFixedCellNative.rational_parameters (policy c.val)
    (policy_lt_fifteen c.val) (gridBox n c.val.2) (gridBox_valid n c.val.2)
    (gridBox_lower_positive n c.val.2 3) ht
  exact ⟨U1011OriginalFifteenFixedCellNative.half_lt_nu _ (policy_lt_fifteen c.val) _ ht,
    h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

def cellTuples (n N : ℕ) (E : ℕ × ℕ → Prop) (i : Index n) : Finset Four :=
  (U11Adaptive.source N E).filter (fun t => coordinates N t ∈ cell n i.2)

theorem cellTuples_geometric_owner {n N : ℕ} {E : ℕ × ℕ → Prop} {i : Index n} {t : Four}
    (ht : t ∈ cellTuples n N E i) : owner n (coordinates N t) = i.2 :=
  owner_eq_of_mem n (Finset.mem_filter.mp ht).2

theorem cellTuples_disjoint_geometry {n N : ℕ} (E : ℕ × ℕ → Prop) (i k : Index n)
    (h : i.2 ≠ k.2) : Disjoint (cellTuples n N E i) (cellTuples n N E k) := by
  apply Finset.disjoint_left.mpr
  intro t ht hk
  exact h ((cellTuples_geometric_owner ht).symm.trans (cellTuples_geometric_owner hk))

/-- Every literal tuple in an active cell receives the same fixed-cell
native caller. No hUniformFamily or density/count supplier is requested. -/
theorem active_cell_native_legality {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (c : ActiveCell n) {t : Four} (ht : t ∈ cellTuples n N E c.val) :
    let p := policy c.val
    let B := gridBox n c.val.2
    0 < U1011OriginalFifteenFixedCellNative.Z p B N ∧
      1 < U1011OriginalFifteenFixedCellNative.D p B N ∧
      U1011OriginalFifteenFixedCellNative.Z p B N ≤ (t.1.1 : ℝ) ∧
      U1011OriginalFifteenFixedCellNative.Z p B N ≤ U1011OriginalFifteenFixedCellNative.D p B N := by
  obtain ⟨htsource,htcell⟩ := Finset.mem_filter.mp ht
  exact U1011OriginalFifteenFixedCellNative.native_legality hN htsource (policy c.val)
    (policy_lt_fifteen c.val) (gridBox n c.val.2) (gridBox_valid n c.val.2)
    (gridBox_lower_positive n c.val.2 3) ((mem_activeCells c.val).mp c.property)
    (cell_subset_closed_box n c.val.2 htcell)

theorem active_cell_full_modulus_cap {n N d : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (c : ActiveCell n) {t : Four} (ht : t ∈ cellTuples n N E c.val)
    (hd : coefficient c N d ≠ 0) :
    ((fullPrefix t * d : ℕ) : ℝ) < (N : ℝ) ^
      ((fixedNu c : ℝ) - 20 * (fixedDelta c : ℝ)) := by
  obtain ⟨htsource,htcell⟩ := Finset.mem_filter.mp ht
  exact U1011OriginalFifteenFixedCellNative.active_full_modulus_cap hN htsource
    (policy c.val) (policy_lt_fifteen c.val) (gridBox n c.val.2)
    (cell_subset_closed_box n c.val.2 htcell) hd

/-- A cell's actual finite family has its own common coefficient in main,
signed AP and centre correction. The same rho is fixed before every tuple. -/
theorem active_cell_family_upper {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (c : ActiveCell n) :
    let p := policy c.val
    let B := gridBox n c.val.2
    (∑ t ∈ cellTuples n N E c.val, U11Adaptive.weight N t) ≤
      (∑ t ∈ cellTuples n N E c.val, U1011OriginalFifteenFixedCellNative.main p B N t) +
      (∑ t ∈ cellTuples n N E c.val, U1011OriginalFifteenFixedCellNative.signedAP p B N t) -
      ∑ t ∈ cellTuples n N E c.val, U1011OriginalFifteenFixedCellNative.signedCentre p B N t := by
  apply U1011OriginalFifteenFixedCellNative.fixed_family_upper hN E _
    (Finset.filter_subset _ _) (policy c.val) (policy_lt_fifteen c.val) (gridBox n c.val.2)
    (gridBox_valid n c.val.2) (gridBox_lower_positive n c.val.2 3)
    ((mem_activeCells c.val).mp c.property)
  intro t ht
  exact cell_subset_closed_box n c.val.2 (Finset.mem_filter.mp ht).2

/-- The actual finite marked carrier. Policy multiplicity is explicit;
this is not silently identified with the original unmarked count. -/
def markedCarrier (n N : ℕ) (E : ℕ × ℕ → Prop) : Finset (Sigma (fun _ : Index n => Four)) :=
  (activeCells n).sigma (fun i => cellTuples n N E i)

theorem marked_sum_eq_policy_cell_sum (n N : ℕ) (E : ℕ × ℕ → Prop)
    (F : Index n → Four → ℝ) :
    (∑ m ∈ markedCarrier n N E, F m.1 m.2) =
      ∑ i ∈ activeCells n, ∑ t ∈ cellTuples n N E i, F i t := by
  exact Finset.sum_sigma _ _ _

/-- All three signed finite components reindex against the SAME marked
carrier and the SAME actual coefficient, before any norm or analytic bound. -/
theorem marked_estimator_decomposition {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    (∑ m ∈ markedCarrier n N E,
      U1011OriginalFifteenFixedCellNative.estimator (policy m.1) (gridBox n m.1.2) N m.2) =
    (∑ i ∈ activeCells n, ∑ t ∈ cellTuples n N E i,
      U1011OriginalFifteenFixedCellNative.main (policy i) (gridBox n i.2) N t) +
    (∑ i ∈ activeCells n, ∑ t ∈ cellTuples n N E i,
      U1011OriginalFifteenFixedCellNative.signedAP (policy i) (gridBox n i.2) N t) -
    ∑ i ∈ activeCells n, ∑ t ∈ cellTuples n N E i,
      U1011OriginalFifteenFixedCellNative.signedCentre (policy i) (gridBox n i.2) N t := by
  rw [marked_sum_eq_policy_cell_sum]
  simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨htsource,htcell⟩ := Finset.mem_filter.mp ht
  exact U1011OriginalFifteenFixedCellNative.estimator_same_coefficient hN htsource (policy i)
    (policy_lt_fifteen i) (gridBox n i.2) (gridBox_valid n i.2)
    (gridBox_lower_positive n i.2 3) ((mem_activeCells i).mp hi) (cell_subset_closed_box n i.2 htcell)

end
end ImbalancedChen.P5Z.U1011OriginalFifteenNativeGridCells
