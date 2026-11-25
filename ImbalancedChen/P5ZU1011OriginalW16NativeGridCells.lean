import ImbalancedChen.P5ZU1011OriginalFifteenNativeGridDispatch
import ImbalancedChen.P5ZU1011OriginalW16FixedCellSmallBeta

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Original W16 native family on the actual finite four-dimensional rational
grid. Geometry/half-open ownership is reused, not reconstructed. W has
its OWN true whole-box Boolean test and fixed rational parameters; it is
not the sixteenth mask of an ordinary selected-product theorem.

This is the whole certified W subfamily, before an adaptive full16
winner is chosen. It has no policy multiplicity: each original prime
tuple has one geometric owner. Signed finite sums retain each cell's
literal common support/coefficient/rho. Coverage of all eligible W points,
the W analytic policy estimate, AP estimates, and beta coefficient unit
regrouping are not conclusions of this module.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NativeGridCells
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open P5U1011JointOverlap

abbrev WIndex (n : ℕ) := Grid n
def WActiveCells (n : ℕ) : Finset (WIndex n) := Finset.univ.filter
  (fun j => wholeBoxEligibleTest wPolicy (gridBox n j)=true)
theorem mem_WActiveCells {n : ℕ} (j : WIndex n) : j∈WActiveCells n ↔
    wholeBoxEligibleTest wPolicy (gridBox n j)=true := by simp [WActiveCells]
abbrev WActiveCell (n : ℕ) := {j : WIndex n // j∈WActiveCells n}

def nativeBox {n : ℕ} (c : WActiveCell n) : Box := gridBox n c.val
def fixedNu {n : ℕ} (c : WActiveCell n) : ℚ := U1011OriginalW16FixedCellNative.nu (nativeBox c)
def fixedDelta {n : ℕ} (c : WActiveCell n) : ℚ := U1011OriginalW16FixedCellNative.delta (nativeBox c)
def fixedXi {n : ℕ} (c : WActiveCell n) : ℚ := U1011OriginalW16FixedCellNative.xi (nativeBox c)
def fixedRho {n : ℕ} (c : WActiveCell n) : ℚ := U1011OriginalW16FixedCellNative.rho (nativeBox c)
def fixedTplus {n : ℕ} (c : WActiveCell n) : ℚ := U1011OriginalW16FixedCellNative.Tplus (nativeBox c)
def fixedZ {n : ℕ} (c : WActiveCell n) (N : ℕ) : ℝ := U1011OriginalW16FixedCellNative.Z (nativeBox c) N
def fixedD {n : ℕ} (c : WActiveCell n) (N : ℕ) : ℝ := U1011OriginalW16FixedCellNative.D (nativeBox c) N
def support {n : ℕ} (c : WActiveCell n) (N : ℕ) : Finset ℕ :=
  U1011OriginalW16FixedCellNative.support (nativeBox c) N
def coefficient {n : ℕ} (c : WActiveCell n) (N d : ℕ) : ℝ :=
  U1011OriginalW16FixedCellNative.coefficient (nativeBox c) N d
def main {n : ℕ} (c : WActiveCell n) (N : ℕ) (t : Four) : ℝ :=
  U1011OriginalW16FixedCellNative.main (nativeBox c) N t
def signedAP {n : ℕ} (c : WActiveCell n) (N : ℕ) (t : Four) : ℝ :=
  U1011OriginalW16FixedCellNative.signedAP (nativeBox c) N t
def signedCentre {n : ℕ} (c : WActiveCell n) (N : ℕ) (t : Four) : ℝ :=
  U1011OriginalW16FixedCellNative.signedCentre (nativeBox c) N t

theorem active_certificate {n : ℕ} (c : WActiveCell n) :
    wholeBoxEligibleTest wPolicy (nativeBox c)=true := (mem_WActiveCells c.val).mp c.property
theorem active_box_valid {n : ℕ} (c : WActiveCell n) : (nativeBox c).Valid := gridBox_valid n c.val
theorem active_box_positive {n : ℕ} (c : WActiveCell n) : 0<(nativeBox c).lo 3 := gridBox_lower_positive n c.val 3

theorem active_parameters {n : ℕ} (c : WActiveCell n) :
    (1/2:ℚ)<fixedNu c ∧ 0<fixedDelta c ∧ 0<fixedXi c ∧ 0<fixedRho c := by
  have h := U1011OriginalW16FixedCellNative.rational_parameters (nativeBox c)
    (active_box_valid c) (active_box_positive c) (active_certificate c)
  have hhalf := U1011OriginalW16FixedCellNative.half_le_G (nativeBox c)
  exact ⟨hhalf.trans_lt h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

def cellTuples (n N : ℕ) (E : ℕ×ℕ → Prop) (j : WIndex n) : Finset Four :=
  (U11Adaptive.source N E).filter (fun t => coordinates N t∈cell n j)
theorem cellTuples_owner {n N : ℕ} {E : ℕ×ℕ → Prop} {j : WIndex n} {t : Four}
    (ht : t∈cellTuples n N E j) : owner n (coordinates N t)=j :=
  owner_eq_of_mem n (Finset.mem_filter.mp ht).2
theorem cellTuples_box {n N : ℕ} {E : ℕ×ℕ → Prop} (c : WActiveCell n) {t : Four}
    (ht : t∈cellTuples n N E c.val) : coordinates N t∈(nativeBox c).region :=
  cell_subset_closed_box n c.val (Finset.mem_filter.mp ht).2

/-- The actual selected support/rho definitions use the geometric owner,
not a tuple-dependent midpoint. On every active owner they are literally
the public common cell coefficient and rho. -/
def ownerSupport (n N : ℕ) (t : Four) : Finset ℕ :=
  U1011OriginalW16FixedCellNative.support (gridBox n (owner n (coordinates N t))) N
def ownerCoefficient (n N : ℕ) (t : Four) (d : ℕ) : ℝ :=
  U1011OriginalW16FixedCellNative.coefficient (gridBox n (owner n (coordinates N t))) N d
def ownerRho (n N : ℕ) (t : Four) : ℚ :=
  U1011OriginalW16FixedCellNative.rho (gridBox n (owner n (coordinates N t)))
theorem owner_row_eq_fixed_cell {n N : ℕ} {E : ℕ×ℕ → Prop} (c : WActiveCell n) {t : Four}
    (ht : t∈cellTuples n N E c.val) :
    ownerSupport n N t=support c N ∧
      (∀d,ownerCoefficient n N t d=coefficient c N d) ∧ ownerRho n N t=fixedRho c := by
  constructor
  · unfold ownerSupport support nativeBox
    rw [cellTuples_owner ht]
  · constructor
    · intro d
      unfold ownerCoefficient coefficient nativeBox
      rw [cellTuples_owner ht]
    · unfold ownerRho fixedRho nativeBox
      rw [cellTuples_owner ht]

theorem active_cell_native_legality {n N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop)
    (c : WActiveCell n) {t : Four} (ht : t∈cellTuples n N E c.val) :
    0<fixedZ c N ∧ 1<fixedD c N ∧ fixedZ c N≤(t.1.1:ℝ) ∧ fixedZ c N≤fixedD c N := by
  exact U1011OriginalW16FixedCellNative.native_legality hN (Finset.mem_filter.mp ht).1
    (nativeBox c) (active_box_valid c) (active_box_positive c) (active_certificate c) (cellTuples_box c ht)

theorem active_cell_full_modulus_cap {n N d : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop)
    (c : WActiveCell n) {t : Four} (ht : t∈cellTuples n N E c.val) (hd : coefficient c N d≠0) :
    (d:ℝ)<fixedD c N ∧ ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^((fixedNu c:ℝ)-20*(fixedDelta c:ℝ)) :=
  U1011OriginalW16FixedCellNative.active_full_modulus_cap hN (Finset.mem_filter.mp ht).1
    (nativeBox c) (cellTuples_box c ht) hd

theorem active_cell_row_upper {n N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop)
    (c : WActiveCell n) {t : Four} (ht : t∈cellTuples n N E c.val) :
    U11Adaptive.weight N t≤main c N t+signedAP c N t-signedCentre c N t :=
  U1011OriginalW16FixedCellNative.native_row_upper hN (Finset.mem_filter.mp ht).1
    (nativeBox c) (active_box_valid c) (active_box_positive c) (active_certificate c) (cellTuples_box c ht)

theorem active_cell_family_upper {n N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop) (c : WActiveCell n) :
    (∑t∈cellTuples n N E c.val,U11Adaptive.weight N t)≤
      (∑t∈cellTuples n N E c.val,main c N t)+(∑t∈cellTuples n N E c.val,signedAP c N t)-
        ∑t∈cellTuples n N E c.val,signedCentre c N t := by
  rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  exact active_cell_row_upper hN E c ht

def WSourceTuples (n N : ℕ) (E : ℕ×ℕ → Prop) : Finset Four :=
  (U11Adaptive.source N E).filter (fun t =>
    wholeBoxEligibleTest wPolicy (gridBox n (owner n (coordinates N t)))=true)

theorem active_cell_subset_WSource {n N : ℕ} (E : ℕ×ℕ → Prop) (j : WIndex n)
    (hj : j∈WActiveCells n) : cellTuples n N E j⊆WSourceTuples n N E := by
  intro t ht
  apply Finset.mem_filter.mpr
  refine ⟨(Finset.mem_filter.mp ht).1,?_⟩
  rw [cellTuples_owner ht]
  exact (mem_WActiveCells j).mp hj

/-- This partitions the actual certified W source, using the existing
unique half-open owner. No coverage claim for false Boolean tests occurs. -/
theorem WSource_unique_active_cell {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈WSourceTuples n N E) :
    ∃!j:WIndex n,j∈WActiveCells n ∧ t∈cellTuples n N E j := by
  obtain ⟨hs,hcert⟩ := Finset.mem_filter.mp ht
  let j := owner n (coordinates N t)
  have hj : j∈WActiveCells n := (mem_WActiveCells j).mpr hcert
  have htj : t∈cellTuples n N E j := Finset.mem_filter.mpr ⟨hs,
    owner_mem n (U1011OriginalFifteenNativeGridDispatch.source_coordinates_cube hN hs)⟩
  refine ⟨j,⟨hj,htj⟩,?_⟩
  intro k hk
  exact (cellTuples_owner hk.2).symm

/-- Exact signed finite reindexing: W has one policy, so the marked
geometric carrier really is the unmarked certified W source. -/
theorem sum_WSource_eq_cells {n N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop) (F : Four→ℝ) :
    (∑t∈WSourceTuples n N E,F t)=∑j∈WActiveCells n,∑t∈cellTuples n N E j,F t := by
  have hrestrict (j : WIndex n) (hj : j∈WActiveCells n) :
      (∑t∈cellTuples n N E j,F t)=
        ∑t∈WSourceTuples n N E,if t∈cellTuples n N E j then F t else 0 := by
    rw [←Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun ht => ⟨active_cell_subset_WSource E j hj ht,ht⟩,fun h => h.2⟩
  symm
  calc
    _ = ∑j∈WActiveCells n,∑t∈WSourceTuples n N E,if t∈cellTuples n N E j then F t else 0 := by
      apply Finset.sum_congr rfl
      exact hrestrict
    _ = ∑t∈WSourceTuples n N E,∑j∈WActiveCells n,if t∈cellTuples n N E j then F t else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨j,hj,hunique⟩ := WSource_unique_active_cell hN ht
      rw [Finset.sum_eq_single j]
      · exact if_pos hj.2
      · intro k hk hkj
        apply if_neg
        intro htK
        exact hkj (hunique k ⟨hk,htK⟩)
      · intro hn
        exact (hn hj.1).elim

end
end ImbalancedChen.P5Z.U1011OriginalW16NativeGridCells
