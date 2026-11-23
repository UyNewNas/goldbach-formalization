import ImbalancedChen.Part3CompletedReciprocalWeil

/-! The signed reciprocal phase of equation (21), with the slow phase retained. -/

namespace ImbalancedChen.Part3

open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped FourierTransform

private theorem inverse_natVal_mul_modEq {m n : ℕ} [NeZero m] (hc : n.Coprime m) :
    n * (((n : ZMod m)⁻¹).val) ≡ 1 [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
  exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime n m).mpr hc)

private theorem fourier_one_add_e2 (x y : UnitAddCircle) :
    fourier 1 (x + y) = fourier 1 x * fourier 1 y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Both reciprocal characters are evaluated on their original physical
moduli. The output has the signed difference numerator and the exact slow
phase. The two coprimalities license all inverses, including the lifted inverse. -/
theorem e2ReciprocalPhase_eq_signed_difference (M B n₁ n₂ : ℕ)
    [NeZero M] [NeZero B] [NeZero n₁]
    (hc : (n₁ * B).Coprime M) (hc' : (n₂ * M).Coprime (n₁ * B)) (a h : ℤ) :
    reciprocalPhase M (a * h) ((n₁ * B : ℕ) : ZMod M) *
        reciprocalPhase B (a * h) ((n₂ * M : ℕ) : ZMod B) =
      reciprocalPhase (n₁ * B) (a * h * ((n₁ : ℤ) - n₂))
          ((n₂ * M : ℕ) : ZMod (n₁ * B)) *
        fourier 1 (((((a * h : ℤ) : ℝ) / ((M : ℝ) * B * n₁)) : ℝ) : UnitAddCircle) := by
  let s := n₁ * B
  let u := ((s : ZMod M)⁻¹).val
  let v := (((n₂ * M : ℕ) : ZMod B)⁻¹).val
  let t := (((n₂ * M : ℕ) : ZMod s)⁻¹).val
  let A := a * h
  let E : ℤ := (s : ℤ) * u + (n₂ : ℤ) * M * t - 1
  have hBs : B ∣ s := dvd_mul_left _ _
  have hB := hc'.of_dvd_right hBs
  have hu : s * u ≡ 1 [MOD M] := inverse_natVal_mul_modEq hc
  have hv : (n₂ * M) * v ≡ 1 [MOD B] := inverse_natVal_mul_modEq hB
  have ht : (n₂ * M) * t ≡ 1 [MOD s] := inverse_natVal_mul_modEq hc'
  have hvt : v ≡ t [MOD B] :=
    Nat.ModEq.cancel_left_of_coprime hB.symm.gcd_eq_one (hv.trans (ht.of_dvd hBs).symm)
  obtain ⟨l, hl⟩ := (Int.natCast_modEq_iff.mpr hvt.symm).dvd
  have huZ : Int.ModEq (M : ℤ) ((s : ℤ) * u) 1 := by
    simpa only [Nat.cast_mul, Nat.cast_one] using Int.natCast_modEq_iff.mpr hu
  have htZ : Int.ModEq (s : ℤ) ((n₂ : ℤ) * M * t) 1 := by
    simpa only [Nat.cast_mul, Nat.cast_one] using Int.natCast_modEq_iff.mpr ht
  have hME : (M : ℤ) ∣ E := by
    obtain ⟨k, hk⟩ := huZ.symm.dvd
    refine ⟨k + (n₂ : ℤ) * t, ?_⟩
    dsimp only [E]
    linear_combination hk
  have hsE : (s : ℤ) ∣ E := by
    obtain ⟨k, hk⟩ := htZ.symm.dvd
    refine ⟨k + (u : ℤ), ?_⟩
    dsimp only [E]
    linear_combination hk
  have hMsE : ((M * s : ℕ) : ℤ) ∣ E := by
    have hlcm : ((M : ℤ).lcm (s : ℤ) : ℤ) ∣ E := Int.coe_lcm_dvd_iff.mpr ⟨hME, hsE⟩
    have hcop : M.Coprime s := hc.symm
    simpa only [Int.lcm, Int.natAbs_natCast, hcop.lcm_eq_mul] using hlcm
  obtain ⟨k, hk⟩ := hMsE
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne B
  have hn0 : (n₁ : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n₁
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (n₁ * B)
  have hsr : (s : ℝ) = (n₁ : ℝ) * B := Nat.cast_mul _ _
  have hkr : (E : ℝ) = (M : ℝ) * (s : ℝ) * k := by exact_mod_cast hk
  have hlr : (v : ℝ) - t = (B : ℝ) * l := by exact_mod_cast hl
  have hreal : ((A : ℝ) * u / M + (A : ℝ) * v / B) -
      ((A : ℝ) * ((n₁ : ℝ) - n₂) * t / s + (A : ℝ) / ((M : ℝ) * B * n₁)) =
        ((A * (k + l) : ℤ) : ℝ) := by
    calc
      _ = (A : ℝ) * ((E : ℝ) / ((M : ℝ) * s) + ((v : ℝ) - t) / B) := by
        simp only [E, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one]
        rw [hsr]
        field_simp [hM0, hB0, hn0]
        ring
      _ = _ := by
        rw [hkr, hlr]
        push_cast
        field_simp [hM0, hB0, hs0]
  rw [reciprocalPhase_nat_eq_fourier, if_pos hc, reciprocalPhase_nat_eq_fourier, if_pos hB,
    reciprocalPhase_nat_eq_fourier, if_pos hc', ← fourier_one_add_e2, ← fourier_one_add_e2,
    ← AddCircle.coe_add, ← AddCircle.coe_add]
  apply congrArg (fourier 1)
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨A * (k + l), ?_⟩
  simpa only [A, Int.cast_mul, Int.cast_sub, Int.cast_natCast, zsmul_eq_mul, mul_one] using hreal.symm

/-- Equation (21) with all five positive input denominators displayed. -/
theorem e2ReciprocalPhase_eq21 (q d w₁ w₂ n₁ n₂ : ℕ)
    [NeZero q] [NeZero d] [NeZero w₁] [NeZero w₂] [NeZero n₁]
    (hc : (n₁ * w₂).Coprime (q * d * w₁))
    (hc' : (n₂ * q * d * w₁).Coprime (n₁ * w₂)) (a h : ℤ) :
    reciprocalPhase (q * d * w₁) (a * h) ((n₁ * w₂ : ℕ) : ZMod (q * d * w₁)) *
        reciprocalPhase w₂ (a * h) ((n₂ * q * d * w₁ : ℕ) : ZMod w₂) =
      reciprocalPhase (n₁ * w₂) (a * h * ((n₁ : ℤ) - n₂))
          ((n₂ * q * d * w₁ : ℕ) : ZMod (n₁ * w₂)) *
        fourier 1 (((((a * h : ℤ) : ℝ) / ((q : ℝ) * d * w₁ * w₂ * n₁)) : ℝ) : UnitAddCircle) := by
  simpa only [Nat.cast_mul, mul_assoc] using
    e2ReciprocalPhase_eq_signed_difference (q * d * w₁) w₂ n₁ n₂ hc
      (by simpa only [mul_assoc] using hc') a h

end ImbalancedChen.Part3
