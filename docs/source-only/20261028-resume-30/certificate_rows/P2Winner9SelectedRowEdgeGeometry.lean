import ImbalancedChen.P2Winner9Row21RawVertexData
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The row22 rational data below is literal extraction from the SHA-guarded
original witness. No determinant, checker, producer or numerical replay
was executed. The two determinant propositions are closed kernel-checkable
source proposals, not evaluated certificate results. -/

namespace ImbalancedChen.P2Winner9SelectedRowEdgeGeometry

open scoped BigOperators Matrix

def row21 (i : Fin 9) (j : Fin 8) : ℚ :=
  (P2Winner9Row21RawVertexData.coords[i.val]!).get! j.val

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

/-- Exact row21 determinant/volume binding. This `decide` has NOT run.
The absolute value avoids guessing the orientation of the source order. -/
theorem row21_abs_det_volume :
    |(edgeMatrix row21).det| =
      (8.factorial : ℚ) * P2Winner9Row21RawVertexData.physicalVolume := by
  decide +kernel

/-- Exact row22 determinant/volume binding, with its distinct final two
vertices. This `decide` has NOT run. -/
theorem row22_abs_det_volume :
    |(edgeMatrix row22).det| = (8.factorial : ℚ) * row22Volume := by
  decide +kernel

theorem row21_volume_pos :
    0 < P2Winner9Row21RawVertexData.physicalVolume := by
  norm_num [P2Winner9Row21RawVertexData.physicalVolume]

theorem row22_volume_pos : 0 < row22Volume := by
  norm_num [row22Volume]

/-- Nondegeneracy follows from the literal positive volume, rather than
being assumed as a selected-row licence. -/
theorem row21_det_ne_zero : (edgeMatrix row21).det ≠ 0 := by
  have hp : 0 < |(edgeMatrix row21).det| := by
    rw [row21_abs_det_volume]
    exact mul_pos (by norm_num) row21_volume_pos
  exact abs_pos.mp hp

theorem row22_det_ne_zero : (edgeMatrix row22).det ≠ 0 := by
  have hp : 0 < |(edgeMatrix row22).det| := by
    rw [row22_abs_det_volume]
    exact mul_pos (by norm_num) row22_volume_pos
  exact abs_pos.mp hp

end ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
