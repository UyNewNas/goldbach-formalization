import ImbalancedChen.P5NamedFifthQ80FloorSoundness
import ImbalancedChen.P5OriginalSharpDirectedLog

/-! Exact original rational form of the producer's expanded log_terms=4
numerator/denominator. This supplies no floor or archive-data certificate. -/
namespace ImbalancedChen.P5OriginalWireRationalFloorExpansion

open P5NamedFifthQ80FloorSoundness

private theorem lower3Q_expanded (Z D : ℚ) (hD : D ≠ 0) :
    lower3Q (Z / D) =
      2 * Z * (15 * D ^ 4 + 5 * Z ^ 2 * D ^ 2 + 3 * Z ^ 4) / (15 * D ^ 5) := by
  have h := P5OriginalSharpDirectedLog.lower3_expanded (Z : ℝ) (D : ℝ)
    (by exact_mod_cast hD)
  have hx : (lower3Q (Z / D) : ℝ) =
      ((2 * Z * (15 * D ^ 4 + 5 * Z ^ 2 * D ^ 2 + 3 * Z ^ 4) / (15 * D ^ 5) : ℚ) : ℝ) := by
    simpa [lower3Q, P5OriginalSharpDirectedLog.lower3] using h
  exact Rat.cast_injective hx

private theorem upper4Q_expanded (Y C : ℚ) (hC : C ≠ 0) (hCY : C ^ 2 - Y ^ 2 ≠ 0) :
    upper4Q (Y / C) =
      2 * Y * (315 * (C ^ 2) ^ 4 - 210 * (Y ^ 2) * (C ^ 2) ^ 3 -
        42 * (Y ^ 2) ^ 2 * (C ^ 2) ^ 2 - 18 * (Y ^ 2) ^ 3 * (C ^ 2) -
        10 * (Y ^ 2) ^ 4) / (315 * C ^ 7 * (C ^ 2 - Y ^ 2)) := by
  have h := P5OriginalSharpDirectedLog.upper4_expanded (Y : ℝ) (C : ℝ)
    (by exact_mod_cast hC) (by exact_mod_cast hCY)
  have hx : (upper4Q (Y / C) : ℝ) =
      ((2 * Y * (315 * C ^ 8 - 210 * Y ^ 2 * C ^ 6 -
        42 * Y ^ 4 * C ^ 4 - 18 * Y ^ 6 * C ^ 2 - 10 * Y ^ 8) /
        (315 * C ^ 7 * (C ^ 2 - Y ^ 2)) : ℚ) : ℝ) := by
    simpa [upper4Q, P5OriginalSharpDirectedLog.upper4] using h
  calc
    _ = 2 * Y * (315 * C ^ 8 - 210 * Y ^ 2 * C ^ 6 -
        42 * Y ^ 4 * C ^ 4 - 18 * Y ^ 6 * C ^ 2 - 10 * Y ^ 8) /
        (315 * C ^ 7 * (C ^ 2 - Y ^ 2)) := Rat.cast_injective hx
    _ = _ := by ring

private theorem combine_fractions (A B H d C RN RD LN LD : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hH : H ≠ 0) (hC : C ≠ 0)
    (hRD : RD ≠ 0) (hLD : LD ≠ 0) :
    ((C / (H * B)) * (RN / RD) - (d / H) * (LN / LD)) /
        ((C / (H * B)) * (A / B)) =
      B * (C * RN * LD - d * B * LN * RD) / (C * A * RD * LD) := by
  field_simp [hA, hB, hH, hC, hRD, hLD] <;> ring

/-- SAME original RN/RD and LN/LD, including the original 1/9 upper tail.
All denominator duties are explicit; no desired integral/data premise occurs. -/
theorem directedQQ_eq_original_fraction (A B H d : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hH : H ≠ 0)
    (hC : H * A - d * B ≠ 0)
    (hD : 2 * H * (A - B) - d * B ≠ 0)
    (hCY : (H * A - d * B) ^ 2 - (H * A - d * B - 2 * H * B) ^ 2 ≠ 0) :
    let C := H * A - d * B
    let Z := d * B
    let D := 2 * H * (A - B) - Z
    let Y := C - 2 * H * B
    let RN := 2 * Z * (15 * D ^ 4 + 5 * Z ^ 2 * D ^ 2 + 3 * Z ^ 4)
    let RD := 15 * D ^ 5
    let LN := 2 * Y * (315 * (C ^ 2) ^ 4 - 210 * (Y ^ 2) * (C ^ 2) ^ 3 -
      42 * (Y ^ 2) ^ 2 * (C ^ 2) ^ 2 - 18 * (Y ^ 2) ^ 3 * (C ^ 2) - 10 * (Y ^ 2) ^ 4)
    let LD := 315 * C ^ 7 * (C ^ 2 - Y ^ 2)
    directedQQ (A / B) (d / H) =
      B * (C * RN * LD - d * B * LN * RD) / (C * A * RD * LD) := by
  let C := H * A - d * B
  let Z := d * B
  let D := 2 * H * (A - B) - Z
  let Y := C - 2 * H * B
  let RN := 2 * Z * (15 * D ^ 4 + 5 * Z ^ 2 * D ^ 2 + 3 * Z ^ 4)
  let RD := 15 * D ^ 5
  let LN := 2 * Y * (315 * (C ^ 2) ^ 4 - 210 * (Y ^ 2) * (C ^ 2) ^ 3 -
    42 * (Y ^ 2) ^ 2 * (C ^ 2) ^ 2 - 18 * (Y ^ 2) ^ 3 * (C ^ 2) - 10 * (Y ^ 2) ^ 4)
  let LD := 315 * C ^ 7 * (C ^ 2 - Y ^ 2)
  have hCn : C ≠ 0 := hC
  have hDn : D ≠ 0 := hD
  have hCYn : C ^ 2 - Y ^ 2 ≠ 0 := hCY
  have ha : A / B - d / H = C / (H * B) := by
    dsimp only [C]
    field_simp [hB, hH] <;> ring
  have hzden : 2 * (A / B - 1) - d / H = D / (H * B) := by
    dsimp only [D, Z]
    field_simp [hB, hH] <;> ring
  have hz : (d / H) / (2 * (A / B - 1) - d / H) = Z / D := by
    rw [hzden]
    dsimp only [Z]
    field_simp [hB, hH, hDn] <;> ring
  have hy : (A / B - d / H - 2) / (A / B - d / H) = Y / C := by
    rw [ha]
    dsimp only [Y]
    field_simp [hB, hH, hCn] <;> ring
  have hlo : lower3Q ((d / H) / (2 * (A / B - 1) - d / H)) = RN / RD := by
    rw [hz]
    exact lower3Q_expanded Z D hDn
  have hup : upper4Q ((A / B - d / H - 2) / (A / B - d / H)) = LN / LD := by
    rw [hy]
    exact upper4Q_expanded Y C hCn hCYn
  have hRDn : RD ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 5 hDn)
  have hLDn : LD ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 7 hCn)) hCYn
  change ((A / B - d / H) * lower3Q ((d / H) / (2 * (A / B - 1) - d / H)) -
      (d / H) * upper4Q ((A / B - d / H - 2) / (A / B - d / H))) /
      ((A / B - d / H) * (A / B)) = B * (C * RN * LD - d * B * LN * RD) / (C * A * RD * LD)
  rw [hlo, hup]
  simp only [ha]
  exact combine_fractions A B H d C RN RD LN LD hA hB hH hCn hRDn hLDn

end ImbalancedChen.P5OriginalWireRationalFloorExpansion
