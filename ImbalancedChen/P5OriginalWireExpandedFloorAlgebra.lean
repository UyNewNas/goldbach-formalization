import ImbalancedChen.P5OriginalChildIntegerWireDefinitions
import ImbalancedChen.P5OriginalWireRationalFloorExpansion

/-! Exact original expanded integer quotient equals rational downward floor.
All sign duties are proved on the active branch; nonpositive d stays zero. -/
namespace ImbalancedChen.P5OriginalWireExpandedFloorAlgebra

open scoped BigOperators
open P5OriginalChildIntegerWireBinding
open P5NamedFifthQ80FloorSoundness
open P5OriginalWireRationalFloorExpansion
open ImbalancedChen.Certificates.P2DirectedLogRounding

private theorem floor_int_div_pos (n d : ℤ) (hd : 0 < d) :
    Int.floor ((n : ℚ) / (d : ℚ)) = n / d := by
  have hi : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
  have hq : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast hi
  have h := Rat.floor_intCast_div_natCast n d.toNat
  rw [hq, hi] at h
  exact h

private theorem combine_prefactor (n W P u DN DD s : ℚ)
    (hP : P ≠ 0) (hu : u ≠ 0) (hDD : DD ≠ 0) :
    (4 * n * W / (u * P)) * (DN / DD) * s =
      (4 * n * W * DN * s) / (P * u * DD) := by
  field_simp [hP, hu, hDD] <;> ring

private theorem originalExactFloor_pos_eq_floor (row : OriginalChildFields)
    (hd : 0 < row.d) (hhi : ∀ i : Fin 5, 0 < row.hi i)
    (hB : 0 < row.B) (hA : 2 * row.B < row.A)
    (hgate : 2 * (1024 * row.hi 4) * row.B ≤
      (1024 * row.hi 4) * row.A - row.d * row.B) :
    originalExactFloor row = Int.floor
      (((4 * (row.n : ℚ) * ∏ i : Fin 5, (wireWidth i : ℚ)) /
          ((row.hi 4 : ℚ) * ∏ i : Fin 5, (row.hi i : ℚ))) *
        directedQQ ((row.A : ℚ) / (row.B : ℚ))
          ((row.d : ℚ) / (1024 * (row.hi 4 : ℚ))) * dyadicScale 80) := by
  let H : ℤ := 1024 * row.hi 4
  let C : ℤ := H * row.A - row.d * row.B
  let Z : ℤ := row.d * row.B
  let D : ℤ := 2 * H * (row.A - row.B) - Z
  let Y : ℤ := C - 2 * H * row.B
  let RN : ℤ := 2 * Z * (15 * D ^ 4 + 5 * Z ^ 2 * D ^ 2 + 3 * Z ^ 4)
  let RD : ℤ := 15 * D ^ 5
  let LN : ℤ := 2 * Y * (315 * (C ^ 2) ^ 4 - 210 * (Y ^ 2) * (C ^ 2) ^ 3 -
    42 * (Y ^ 2) ^ 2 * (C ^ 2) ^ 2 - 18 * (Y ^ 2) ^ 3 * (C ^ 2) - 10 * (Y ^ 2) ^ 4)
  let LD : ℤ := 315 * C ^ 7 * (C ^ 2 - Y ^ 2)
  let DN : ℤ := row.B * (C * RN * LD - row.d * row.B * LN * RD)
  let DD : ℤ := C * row.A * RD * LD
  let W : ℤ := ∏ i : Fin 5, wireWidth i
  let P : ℤ := ∏ i : Fin 5, row.hi i
  let N : ℤ := 4 * row.n * W * DN
  let Den : ℤ := P * row.hi 4 * DD
  have hH : 0 < H := mul_pos (by norm_num) (hhi 4)
  have hAp : 0 < row.A := by linarith
  have hHB : 0 < 2 * H * row.B := mul_pos (mul_pos (by norm_num) hH) hB
  have hC : 0 < C := hHB.trans_le hgate
  have hD_eq : D = C + H * (row.A - 2 * row.B) := by dsimp only [D, C, Z]; ring
  have hD : 0 < D := by
    rw [hD_eq]
    exact add_pos hC (mul_pos hH (sub_pos.mpr hA))
  have hY0 : 0 ≤ Y := sub_nonneg.mpr hgate
  have hYlt : Y < C := by dsimp only [Y]; linarith
  have hCY : 0 < C ^ 2 - Y ^ 2 := by
    have hm := mul_pos (sub_pos.mpr hYlt) (add_pos_of_pos_of_nonneg hC hY0)
    nlinarith
  have hRD : 0 < RD := mul_pos (by norm_num) (pow_pos hD 5)
  have hLD : 0 < LD := mul_pos (mul_pos (by norm_num) (pow_pos hC 7)) hCY
  have hDD : 0 < DD := mul_pos (mul_pos (mul_pos hC hAp) hRD) hLD
  have hP : 0 < P := Finset.prod_pos (fun i _ => hhi i)
  have hDen : 0 < Den := mul_pos (mul_pos hP (hhi 4)) hDD
  have hAq : (row.A : ℚ) ≠ 0 := by exact_mod_cast hAp.ne'
  have hBq : (row.B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hHq : (H : ℚ) ≠ 0 := by exact_mod_cast hH.ne'
  have hCq : (H : ℚ) * (row.A : ℚ) - (row.d : ℚ) * (row.B : ℚ) ≠ 0 := by
    exact_mod_cast (show H * row.A - row.d * row.B ≠ 0 from hC.ne')
  have hDq : 2 * (H : ℚ) * ((row.A : ℚ) - (row.B : ℚ)) -
      (row.d : ℚ) * (row.B : ℚ) ≠ 0 := by
    exact_mod_cast (show 2 * H * (row.A - row.B) - row.d * row.B ≠ 0 from hD.ne')
  have hCYq : ((H : ℚ) * (row.A : ℚ) - (row.d : ℚ) * (row.B : ℚ)) ^ 2 -
      ((H : ℚ) * (row.A : ℚ) - (row.d : ℚ) * (row.B : ℚ) -
        2 * (H : ℚ) * (row.B : ℚ)) ^ 2 ≠ 0 := by
    exact_mod_cast (show (H * row.A - row.d * row.B) ^ 2 -
      (H * row.A - row.d * row.B - 2 * H * row.B) ^ 2 ≠ 0 from hCY.ne')
  have hdir : directedQQ ((row.A : ℚ) / (row.B : ℚ)) ((row.d : ℚ) / (H : ℚ)) =
      (DN : ℚ) / (DD : ℚ) := by
    have h := directedQQ_eq_original_fraction (row.A : ℚ) (row.B : ℚ) (H : ℚ) (row.d : ℚ)
      hAq hBq hHq hCq hDq hCYq
    simpa only [C, Z, D, Y, RN, RD, LN, LD, DN, DD,
      Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_ofNat] using h
  have hWcast : (W : ℚ) = ∏ i : Fin 5, (wireWidth i : ℚ) := by simp [W]
  have hPcast : (P : ℚ) = ∏ i : Fin 5, (row.hi i : ℚ) := by simp [P]
  have hHcast : (H : ℚ) = 1024 * (row.hi 4 : ℚ) := by norm_num [H]
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne'
  have huq : (row.hi 4 : ℚ) ≠ 0 := by exact_mod_cast (hhi 4).ne'
  have hDDq : (DD : ℚ) ≠ 0 := by exact_mod_cast hDD.ne'
  have hnum :
      (((4 * (row.n : ℚ) * ∏ i : Fin 5, (wireWidth i : ℚ)) /
          ((row.hi 4 : ℚ) * ∏ i : Fin 5, (row.hi i : ℚ))) *
        directedQQ ((row.A : ℚ) / (row.B : ℚ))
          ((row.d : ℚ) / (1024 * (row.hi 4 : ℚ))) * dyadicScale 80) =
        ((N * (2 : ℤ) ^ 80 : ℤ) : ℚ) / (Den : ℚ) := by
    rw [← hWcast, ← hPcast, ← hHcast, hdir]
    rw [combine_prefactor (row.n : ℚ) (W : ℚ) (P : ℚ) (row.hi 4 : ℚ)
      (DN : ℚ) (DD : ℚ) (dyadicScale 80) hPq huq hDDq]
    simp only [N, Den, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, dyadicScale]
  have hsource : originalExactFloor row = N * (2 : ℤ) ^ 80 / Den := by
    unfold originalExactFloor
    rw [if_neg (not_le_of_gt hd)]
  rw [hsource, ← floor_int_div_pos _ _ hDen, ← hnum]

/-- The original active-branch integer gates suffice. Nonpositive d requires
none of the denominator hypotheses and retains the original zero fallback. -/
theorem originalExactFloor_eq_directed_floor (row : OriginalChildFields)
    (hactive : 0 < row.d →
      (∀ i : Fin 5, 0 < row.hi i) ∧ 0 < row.B ∧ 2 * row.B < row.A ∧
        2 * (1024 * row.hi 4) * row.B ≤
          (1024 * row.hi 4) * row.A - row.d * row.B) :
    originalExactFloor row =
      if 0 < row.d then Int.floor
        (((4 * (row.n : ℚ) * ∏ i : Fin 5, (wireWidth i : ℚ)) /
            ((row.hi 4 : ℚ) * ∏ i : Fin 5, (row.hi i : ℚ))) *
          directedQQ ((row.A : ℚ) / (row.B : ℚ))
            ((row.d : ℚ) / (1024 * (row.hi 4 : ℚ))) * dyadicScale 80)
      else 0 := by
  by_cases hd : 0 < row.d
  · obtain ⟨hhi, hB, hA, hgate⟩ := hactive hd
    rw [if_pos hd]
    exact originalExactFloor_pos_eq_floor row hd hhi hB hA hgate
  · simp only [if_neg hd, originalExactFloor, if_pos (le_of_not_gt hd)]

end ImbalancedChen.P5OriginalWireExpandedFloorAlgebra
