import ImbalancedChen.P1OriginalThirdGammaFirstCoordinateRise
import ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover
import ImbalancedChen.P1OriginalCoarseFifthJointGeometry

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready=false.
-- Rational mesh translation and the pointwise section-diameter ingredient
-- for the 428/75 moving-mesh gate-crossing proof. No volume theorem is
-- asserted in this file. The Fubini cylinder step remains unimplemented.
namespace ImbalancedChen.P1OriginalThirdGammaMeshSectionBridge

noncomputable section
open VariableEnvelope HistoricalThirdCoarse
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalThirdGammaFirstCoordinateRise
open P1OriginalFifthGrid400RefinedFullBoxCover

private def stepQ (m : ℕ) : ℚ := (19 / 96) / (m + 1)

private theorem point_shift (m i k : ℕ) :
    qLogPrimeMeshPoint 0 (19 / 96) m k =
      qLogPrimeMeshPoint 0 (19 / 96) m i +
        ((k : ℚ) - i) * stepQ m := by
  dsimp [qLogPrimeMeshPoint, stepQ]
  ring

private theorem point_shift_succ (m i k : ℕ) :
    qLogPrimeMeshPoint 0 (19 / 96) m (k + 1) =
      qLogPrimeMeshPoint 0 (19 / 96) m (i + 1) +
        ((k : ℚ) - i) * stepQ m := by
  dsimp [qLogPrimeMeshPoint, stepQ]
  push_cast
  ring

def firstDelta (m : ℕ) (j k : Cell m) : ℚ :=
  ((k 0).val - (j 0).val : ℚ) * stepQ m

theorem firstDelta_nonneg (m : ℕ) (j k : Cell m)
    (hjk : (j 0).val ≤ (k 0).val) : 0 ≤ firstDelta m j k := by
  have hs : (0 : ℚ) ≤ stepQ m := by
    dsimp [stepQ]
    positivity
  have hd : (0 : ℚ) ≤ (k 0).val - (j 0).val := by exact sub_nonneg.mpr (by exact_mod_cast hjk)
  exact mul_nonneg hd hs

theorem box_first_coordinate_shift (m : ℕ) (j k : Cell m)
    (hy : j 1 = k 1) (hz : j 2 = k 2) :
    box m k = shiftX (box m j) (firstDelta m j k) := by
  ext
  · simpa [box, shiftX, firstDelta, qLogPrimeMeshLo, stepQ,
      point_shift m (j 0).val (k 0).val] using
      (point_shift m (j 0).val (k 0).val)
  · simpa [box, shiftX, firstDelta, qLogPrimeMeshHi, stepQ,
      point_shift_succ m (j 0).val (k 0).val] using
      (point_shift_succ m (j 0).val (k 0).val)
  · simp [box, shiftX, qLogPrimeMeshLo, hy]
  · simp [box, shiftX, qLogPrimeMeshHi, hy]
  · simp [box, shiftX, qLogPrimeMeshLo, hz]
  · simp [box, shiftX, qLogPrimeMeshHi, hz]

-- This uses the actual three-coordinate box and first-coordinate mesh
-- indices. A fifth j is sent here through the original thirdOwner map.
theorem gamma_mesh_first_rise (e : ℝ) (m : ℕ) (j k : Cell m)
    (hjk : (j 0).val ≤ (k 0).val) (hy : j 1 = k 1) (hz : j 2 = k 2)
    (hfullj : ((box m j).ux : ℝ) ≤ mu - 4 * e)
    (hfullk : ((box m k).ux : ℝ) ≤ mu - 4 * e) :
    gamma e (box m k) ≤ gamma e (box m j) + firstDelta m j k / 2 := by
  rw [box_first_coordinate_shift m j k hy hz] at hfullk ⊢
  exact gamma_shift_le e (box m j) (firstDelta m j k)
    (firstDelta_nonneg m j k hjk) hfullj hfullk

-- Exact real section geometry. The application takes g(x)=Gamma(0,b_j(x))
-- with the translated mesh boxes above, and h=the actual mesh step.
theorem section_span_of_one_sided_rise
    (a h d x y gx gy c : ℝ) (ha : 1/2 < a) (hxy : x ≤ y)
    (hg : gy - gx ≤ (y - x + h) / 2)
    (hx : c ≤ a*x - gx) (hx' : a*x - gx ≤ c+d)
    (hy : c ≤ a*y - gy) (hy' : a*y - gy ≤ c+d) :
    y-x ≤ (d+h/2)/(a-1/2) := by
  apply (le_div_iff₀ (by linarith)).mpr
  nlinarith

theorem third_gate_section_span
    (h d x y gx gy c : ℝ) (hxy : x ≤ y)
    (hg : gy-gx ≤ (y-x+h)/2)
    (hx : c ≤ x-gx) (hx' : x-gx ≤ c+d)
    (hy : c ≤ y-gy) (hy' : y-gy ≤ c+d) :
    y-x ≤ 2*d+h := by
  have hh := section_span_of_one_sided_rise 1 h d x y gx gy c
    (by norm_num) hxy hg hx hx' hy hy'
  norm_num at hh
  linarith

theorem third_first_cube_section_span
    (h d x y gx gy c : ℝ) (hxy : x ≤ y)
    (hg : gy-gx ≤ (y-x+h)/2)
    (hx : c ≤ 3*x-gx) (hx' : 3*x-gx ≤ c+d)
    (hy : c ≤ 3*y-gy) (hy' : 3*y-gy ≤ c+d) :
    y-x ≤ (2*d+h)/5 := by
  have hh := section_span_of_one_sided_rise 3 h d x y gx gy c
    (by norm_num) hxy hg hx hx' hy hy'
  norm_num at hh
  linarith

end
end ImbalancedChen.P1OriginalThirdGammaMeshSectionBridge
