import ImbalancedChen.Part3PrimeSquareMiddleCuspInvariant

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Primitive middle cusps a/p cannot be carried to infinity or zero by
Gamma0(p^2). Actual projective action and primitive signed columns, not
an assumed classification, force p|1 in each case. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b
open ImbalancedChen.Part3.PrimeSquareMiddleCuspInvariant20261026b

namespace ImbalancedChen.Part3.PrimeSquareMiddleCuspSeparation20261026b

private theorem no_divides_one (p : ℕ) (hp : p.Prime) (h : (p : ℤ) ∣ 1) : False :=
  hp.not_dvd_one (Int.natCast_dvd_natCast.mp h)

theorem middle_action_ne_infinity (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 (p ^ 2)) :
    mapGL ℝ g • middlePoint p a ≠ (∞ : OnePoint ℝ) := by
  intro he
  obtain ⟨u, v, huv⟩ := ha
  let A := infinityBezoutMatrix a (p : ℤ) u v huv
  have hpI : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hA : mapGL ℝ A • (∞ : OnePoint ℝ) = middlePoint p a :=
    infinityBezoutMatrix_action a (p : ℤ) u v huv hpI
  have hEq : mapGL ℝ (g * A) • (∞ : OnePoint ℝ) =
      mapGL ℝ (1 : SL(2, ℤ)) • (∞ : OnePoint ℝ) := by
    rw [map_mul, mul_smul, hA]
    simpa using he
  have hc0 : g 1 0 * a + g 1 1 * (p : ℤ) = 0 := by
    rcases equal_infinity_images_signed_first_column (g * A) 1 hEq with h | h
    · simpa [A, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two] using h 1
    · simpa [A, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two] using h 1
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c (p ^ 2) g).mp hg
  have hc : g 1 0 = (p : ℤ) ^ 2 * k := by simpa only [Nat.cast_pow] using hk
  have hD : (p : ℤ) * k * a + g 1 1 = 0 := by
    apply mul_left_cancel₀ hpI
    calc
      (p : ℤ) * ((p : ℤ) * k * a + g 1 1) = g 1 0 * a + g 1 1 * (p : ℤ) := by rw [hc]; ring
      _ = (p : ℤ) * 0 := by simpa only [mul_zero] using hc0
  have hd : (p : ℤ) ∣ g 1 1 := ⟨-(k * a), by linear_combination hD⟩
  have hpc : (p : ℤ) ∣ g 1 0 := ⟨(p : ℤ) * k, by rw [hc]; ring⟩
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  apply no_divides_one p hp
  rw [← hdet]
  exact dvd_sub (dvd_mul_of_dvd_right hd (g 0 0)) (dvd_mul_of_dvd_right hpc (g 0 1))

theorem middle_action_ne_zero (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 (p ^ 2)) :
    mapGL ℝ g • middlePoint p a ≠ ((0 : ℝ) : OnePoint ℝ) := by
  intro he
  obtain ⟨u, v, huv⟩ := ha
  let A := infinityBezoutMatrix a (p : ℤ) u v huv
  have hpI : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hA : mapGL ℝ A • (∞ : OnePoint ℝ) = middlePoint p a :=
    infinityBezoutMatrix_action a (p : ℤ) u v huv hpI
  have hS : mapGL ℝ ModularGroup.S • (∞ : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
    simp [OnePoint.smul_infty_eq_ite, ModularGroup.S, mapGL_coe_matrix]
  have hEq : mapGL ℝ (g * A) • (∞ : OnePoint ℝ) =
      mapGL ℝ ModularGroup.S • (∞ : OnePoint ℝ) := by
    rw [map_mul, mul_smul, hA, hS]
    exact he
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c (p ^ 2) g).mp hg
  have hc : g 1 0 = (p : ℤ) ^ 2 * k := by simpa only [Nat.cast_pow] using hk
  have hdiv : (p : ℤ) ∣ g 1 0 * a + g 1 1 * (p : ℤ) := by
    refine ⟨(p : ℤ) * k * a + g 1 1, ?_⟩
    rw [hc]
    ring
  rcases equal_infinity_images_signed_first_column (g * A) ModularGroup.S hEq with h | h
  · have hbottom : g 1 0 * a + g 1 1 * (p : ℤ) = 1 := by
      simpa [A, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two, ModularGroup.S] using h 1
    exact no_divides_one p hp (hbottom ▸ hdiv)
  · have hbottom : g 1 0 * a + g 1 1 * (p : ℤ) = -1 := by
      simpa [A, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two, ModularGroup.S] using h 1
    apply no_divides_one p hp
    exact dvd_neg.mp (hbottom ▸ hdiv)

end ImbalancedChen.Part3.PrimeSquareMiddleCuspSeparation20261026b
