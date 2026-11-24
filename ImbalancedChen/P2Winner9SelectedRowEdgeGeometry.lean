import ImbalancedChen.P2Winner9Row21RawVertexData
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
The original Winner9 rows 21 and 22 have nondegenerate ordered edge maps.
For each edge matrix, two row swaps give a product of a unit lower triangular
matrix and an upper triangular matrix. Exact rational entry identities give
the determinants and the stored simplex volumes.
-/

namespace ImbalancedChen.P2Winner9SelectedRowEdgeGeometry

open scoped BigOperators Matrix

def row21 (i : Fin 9) (j : Fin 8) : ℚ :=
  (P2Winner9Row21RawVertexData.coords[i.val]!)[j.val]!

def row22 : Fin 9 → Fin 8 → ℚ :=
  ![
    ![((2281219 : ℚ) / 16000000), ((1500001 : ℚ) / 12000000), ((2156269 : ℚ) / 24000000), ((843749 : ℚ) / 16000000), ((843749 : ℚ) / 16000000), ((843749 : ℚ) / 16000000), ((843749 : ℚ) / 48000000), ((843749 : ℚ) / 48000000)],
    ![((6109297 : ℚ) / 45000000), ((2234381 : ℚ) / 22500000), ((2234381 : ℚ) / 22500000), ((2234381 : ℚ) / 45000000), ((2234381 : ℚ) / 45000000), ((2234381 : ℚ) / 45000000), ((7 : ℚ) / 192), ((7 : ℚ) / 192)],
    ![((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 512), ((1015633 : ℚ) / 16000000), ((2546867 : ℚ) / 48000000), ((2140681 : ℚ) / 48000000), ((328117 : ℚ) / 16000000), ((328117 : ℚ) / 16000000)],
    ![((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 1024), ((57 : ℚ) / 1024), ((57 : ℚ) / 1024), ((19 : ℚ) / 1024), ((19 : ℚ) / 1024)],
    ![((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 1024), ((57 : ℚ) / 1024), ((57 : ℚ) / 1024), ((19 : ℚ) / 1024), ((2046843 : ℚ) / 112000000)],
    ![((5 : ℚ) / 48), ((5 : ℚ) / 48), ((5 : ℚ) / 48), ((5 : ℚ) / 96), ((5 : ℚ) / 96), ((5 : ℚ) / 96), ((7 : ℚ) / 192), ((218747 : ℚ) / 10500000)],
    ![((3661457 : ℚ) / 36000000), ((3661457 : ℚ) / 36000000), ((3661457 : ℚ) / 36000000), ((2494801 : ℚ) / 36000000), ((2494801 : ℚ) / 36000000), ((18229 : ℚ) / 562500), ((18229 : ℚ) / 750000), ((18229 : ℚ) / 750000)],
    ![((26359363 : ℚ) / 260000000), ((26359363 : ℚ) / 260000000), ((26359363 : ℚ) / 260000000), ((18609459 : ℚ) / 260000000), ((18265621 : ℚ) / 260000000), ((4046871 : ℚ) / 130000000), ((4046871 : ℚ) / 130000000), ((1453107 : ℚ) / 65000000)],
    ![((25484363 : ℚ) / 252000000), ((25484363 : ℚ) / 252000000), ((25484363 : ℚ) / 252000000), ((2640637 : ℚ) / 36000000), ((16296863 : ℚ) / 252000000), ((7 : ℚ) / 192), ((7 : ℚ) / 192), ((218747 : ℚ) / 10500000)]
  ]

def row22Volume : ℚ := ((3873997691247452594156312384488237493 : ℚ) / 4530699931484160000000000000000000000000000000000000000000)

/-- Columns are the eight ordered edges from the first listed vertex. -/
def edgeMatrix (v : Fin 9 → Fin 8 → ℚ) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => v j.succ i - v 0 i


private def swappedRows (A : Matrix (Fin 8) (Fin 8) ℚ) : Matrix (Fin 8) (Fin 8) ℚ :=
  (A.submatrix (Equiv.swap (2 : Fin 8) 3) id).submatrix (Equiv.swap (3 : Fin 8) 7) id

private def rowReorder : Fin 8 → Fin 8 := ![0, 1, 3, 7, 4, 5, 6, 2]

private theorem swappedRows_apply (A : Matrix (Fin 8) (Fin 8) ℚ) (i j : Fin 8) :
    swappedRows A i j = A (rowReorder i) j := by
  have h : (Equiv.swap (2 : Fin 8) 3) ((Equiv.swap (3 : Fin 8) 7) i) = rowReorder i := by
    rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
    fin_cases i <;> decide +kernel
  change A ((Equiv.swap (2 : Fin 8) 3) ((Equiv.swap (3 : Fin 8) 7) i)) j = _
  rw [h]

private theorem swappedRows_det (A : Matrix (Fin 8) (Fin 8) ℚ) :
    (swappedRows A).det = A.det := by
  have h23 : (2 : Fin 8) ≠ 3 := by decide +kernel
  have h37 : (3 : Fin 8) ≠ 7 := by decide +kernel
  unfold swappedRows
  rw [Matrix.det_permute, Matrix.det_permute, Equiv.Perm.sign_swap h23,
    Equiv.Perm.sign_swap h37]
  simp

private theorem permutation_moves_up (σ : Equiv.Perm (Fin 8)) (hne : σ ≠ 1) :
    ∃ i, i < σ i := by
  classical
  by_contra h
  have hle (i : Fin 8) : σ i ≤ i := le_of_not_gt (fun hi => h ⟨i, hi⟩)
  have hmoves : ∃ i, σ i ≠ i := by
    by_contra hfixed
    apply hne
    apply Equiv.ext
    intro i
    change σ i = i
    exact Classical.byContradiction (fun hi => hfixed ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hmoves
  have hlt : (σ i).val < i.val := lt_of_le_of_ne (hle i) (fun he => hi (Fin.ext he))
  have hsum : (∑ j : Fin 8, (σ j).val) < ∑ j : Fin 8, j.val :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
  rw [Equiv.sum_comp σ Fin.val] at hsum
  exact (lt_irrefl _) hsum

private theorem upper_determinant (M : Matrix (Fin 8) (Fin 8) ℚ)
    (hUpper : ∀ i j : Fin 8, j < i → M i j = 0) :
    M.det = ∏ i : Fin 8, M i i := by
  classical
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin 8))]
  · simp
  · intro σ _ hne
    obtain ⟨i, hi⟩ := permutation_moves_up σ hne
    have hzero : (∏ j : Fin 8, M (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hUpper (σ i) i hi)
    rw [hzero, smul_zero]
  · simp

private theorem det_eq_upper_diagonal {A L U : Matrix (Fin 8) (Fin 8) ℚ}
    (hFactor : swappedRows A = L * U)
    (hLower : ∀ i j : Fin 8, i < j → L i j = 0)
    (hDiagonal : ∀ i : Fin 8, L i i = 1)
    (hUpper : ∀ i j : Fin 8, j < i → U i j = 0) :
    A.det = ∏ i : Fin 8, U i i := by
  have hDetL : L.det = 1 := by
    rw [← Matrix.det_transpose L, upper_determinant Lᵀ (fun i j h => hLower j i h)]
    simp [hDiagonal]
  have hDet := congrArg Matrix.det hFactor
  rw [swappedRows_det, Matrix.det_mul, hDetL, one_mul, upper_determinant U hUpper] at hDet
  exact hDet

/- The two exact factorizations use the same two swaps. The local
   certificates verify every coefficient of the literal ordered edge
   matrices in addition to lower unit and upper triangularity. -/
private def lower21 : Matrix (Fin 8) (Fin 8) ℚ :=
![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![(18499868 / 4906103), 1, 0, 0, 0, 0, 0, 0],
  ![(2218609 / 4906103), (5857548993519 / 24528431794114), 1, 0, 0, 0, 0, 0],
  ![(-13593765 / 4906103), (-19699575385849 / 24528431794114), (15621 / 62504), 1, 0, 0, 0, 0],
  ![(2218609 / 4906103), (3404340498223 / 24528431794114), (-1 / 3), 0, 1, 0, 0, 0],
  ![(2218609 / 4906103), (1411550145065 / 24528431794114), (-265597 / 187512), 0, (453109 / 250016), 1, 0, 0],
  ![(-13593765 / 4906103), (-19699575385849 / 24528431794114), (15621 / 62504), 0, (-74709578057 / 23439250016), (-17833789429 / 11858563990), 1, 0],
  ![(-6812122 / 4906103), (-2579158592909 / 12264215897057), 0, 0, (2531199 / 937510), (843733 / 468755), (-7003236258852834 / 3089368663835695), 1]
]

private def upper21 : Matrix (Fin 8) (Fin 8) ℚ :=
![
  ![(-4906103 / 720000000), (-499969 / 16000000), (-499969 / 16000000), (-499969 / 16000000), (-1843657 / 48000000), (-5885143 / 144000000), (-5885143 / 144000000), (-8355869 / 201600000)],
  ![0, (12264215897057 / 117746472000000), (12264215897057 / 117746472000000), (12264215897057 / 117746472000000), (912540266027 / 7359154500000), (7701533039681 / 58873236000000), (7701533039681 / 58873236000000), (54571551381947 / 412112652000000)],
  ![0, 0, (-7813 / 1000000), (-7813 / 1000000), (-158132639946206341 / 12264215897057000000), (373585553829713537 / 98113727176456000000), (373585553829713537 / 98113727176456000000), (5314055047955004539 / 686796090235192000000)],
  ![0, 0, 0, (-15641 / 56000000), (-443632959373397534711 / 1238293350694051176000000), (-3398775508255729975747 / 1415192400793201344000000), (-3398775508255729975747 / 1415192400793201344000000), (-923592988607014848881149 / 128782508472181322304000000)],
  ![0, 0, 0, 0, (-2819699607725 / 588682363058736), (267267759210831197 / 14717059076468400000), (-5613143776597721 / 19622745435291200000), (106270322570839261 / 137359218047038400000)],
  ![0, 0, 0, 0, 0, (-88543 / 2400000), (1383266423 / 92313600000), (155495515241 / 8400537600000)],
  ![0, 0, 0, 0, 0, 0, (617873732767139 / 32145257164800000), (3860858723935141441579 / 99618312680001024000000)],
  ![0, 0, 0, 0, 0, 0, 0, (2575840695887348454213 / 75689532263974527500000)]
]

private theorem row21_det_eq_diagonal :
    (edgeMatrix row21).det = ∏ i : Fin 8, upper21 i i := by
  have hf : ∀ i j : Fin 8,
      swappedRows (edgeMatrix row21) i j = (lower21 * upper21) i j := by
    intro i j
    rw [swappedRows_apply, Matrix.mul_apply, ← Fin.sum_ofFn]
    fin_cases i <;> fin_cases j <;> decide +kernel
  exact det_eq_upper_diagonal (L := lower21) (U := upper21)
    (funext fun i => funext fun j => hf i j)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private def lower22 : Matrix (Fin 8) (Fin 8) ℚ :=
![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![(18499868 / 4906103), 1, 0, 0, 0, 0, 0, 0],
  ![(2218609 / 4906103), (5857548993519 / 24528431794114), 1, 0, 0, 0, 0, 0],
  ![(-13593765 / 4906103), (-19699575385849 / 24528431794114), (15621 / 62504), 1, 0, 0, 0, 0],
  ![(2218609 / 4906103), (3404340498223 / 24528431794114), (-1 / 3), 0, 1, 0, 0, 0],
  ![(2218609 / 4906103), (1411550145065 / 24528431794114), (-265597 / 187512), 0, (453109 / 250016), 1, 0, 0],
  ![(-13593765 / 4906103), (-19699575385849 / 24528431794114), (15621 / 62504), 0, (-74709578057 / 23439250016), (-17833789429 / 11858563990), 1, 0],
  ![(-6812122 / 4906103), (-2579158592909 / 12264215897057), 0, 0, (2531199 / 937510), (843733 / 468755), (-3611968123157161105338 / 11341069012678475834755), 1]
]

private def upper22 : Matrix (Fin 8) (Fin 8) ℚ :=
![
  ![(-4906103 / 720000000), (-499969 / 16000000), (-499969 / 16000000), (-499969 / 16000000), (-1843657 / 48000000), (-5885143 / 144000000), (-42841783 / 1040000000), (-8355869 / 201600000)],
  ![0, (12264215897057 / 117746472000000), (12264215897057 / 117746472000000), (12264215897057 / 117746472000000), (912540266027 / 7359154500000), (7701533039681 / 58873236000000), (100809077213791 / 765352068000000), (54571551381947 / 412112652000000)],
  ![0, 0, (-7813 / 1000000), (-7813 / 1000000), (-158132639946206341 / 12264215897057000000), (373585553829713537 / 98113727176456000000), (7671265416927022879 / 1275478453293928000000), (5314055047955004539 / 686796090235192000000)],
  ![0, 0, 0, (-15641 / 56000000), (-443632959373397534711 / 1238293350694051176000000), (-3398775508255729975747 / 1415192400793201344000000), (-2025051781153126671268447 / 398612526223418378560000000), (-923592988607014848881149 / 128782508472181322304000000)],
  ![0, 0, 0, 0, (-2819699607725 / 588682363058736), (267267759210831197 / 14717059076468400000), (47520338753962306943 / 2391522099926115000000), (22993231809559152859 / 1545291203029182000000)],
  ![0, 0, 0, 0, 0, (-88543 / 2400000), (-247330140913 / 6500416000000), (-22219484423 / 1050067200000)],
  ![0, 0, 0, 0, 0, 0, (2268213802535695166951 / 231256797292859520000000), (179747187934970967557 / 7471373451000076800000)],
  ![0, 0, 0, 0, 0, 0, 0, (-2676401517573244939975668611 / 208392143107966993463623125000)]
]

private theorem row22_det_eq_diagonal :
    (edgeMatrix row22).det = ∏ i : Fin 8, upper22 i i := by
  have hf : ∀ i j : Fin 8,
      swappedRows (edgeMatrix row22) i j = (lower22 * upper22) i j := by
    intro i j
    rw [swappedRows_apply, Matrix.mul_apply, ← Fin.sum_ofFn]
    fin_cases i <;> fin_cases j <;> decide +kernel
  exact det_eq_upper_diagonal (L := lower22) (U := upper22)
    (funext fun i => funext fun j => hf i j)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)

/-- The absolute determinant gives the original row21 simplex volume. -/
theorem row21_abs_det_volume :
    |(edgeMatrix row21).det| =
      ((8 : ℕ).factorial : ℚ) * P2Winner9Row21RawVertexData.physicalVolume := by
  rw [row21_det_eq_diagonal]
  decide +kernel

/-- The absolute determinant gives the original row22 simplex volume. -/
theorem row22_abs_det_volume :
    |(edgeMatrix row22).det| = ((8 : ℕ).factorial : ℚ) * row22Volume := by
  rw [row22_det_eq_diagonal]
  decide +kernel

theorem row21_volume_pos :
    0 < P2Winner9Row21RawVertexData.physicalVolume := by
  decide +kernel

theorem row22_volume_pos : 0 < row22Volume := by
  decide +kernel

/-- Nondegeneracy follows from the literal positive volume, rather than
being assumed as a selected-row licence. -/
theorem row21_det_ne_zero : (edgeMatrix row21).det ≠ 0 := by
  have hp : 0 < |(edgeMatrix row21).det| := by
    rw [row21_abs_det_volume]
    exact mul_pos (by decide +kernel) row21_volume_pos
  exact abs_pos.mp hp

theorem row22_det_ne_zero : (edgeMatrix row22).det ≠ 0 := by
  have hp : 0 < |(edgeMatrix row22).det| := by
    rw [row22_abs_det_volume]
    exact mul_pos (by decide +kernel) row22_volume_pos
  exact abs_pos.mp hp

end ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
