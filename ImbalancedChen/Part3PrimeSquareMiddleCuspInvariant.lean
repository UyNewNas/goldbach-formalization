import ImbalancedChen.Part3PrimeCuspBezoutMatrices
import ImbalancedChen.Part3Gamma0ParabolicBottomRow

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual Gamma0(p^2) orbit invariant for primitive columns (a,p).
Native projective cusp equality gives equality of primitive columns up
to ONE common sign, by determinant-one signed-T classification. Actual
level-p^2 divisibility then forces p|(b-a). Translation proves converse.
No prime-square cusp exhaustion or prescribed representative list is input. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b

namespace ImbalancedChen.Part3.PrimeSquareMiddleCuspInvariant20261026b

def middlePoint (p : ℕ) (a : ℤ) : OnePoint ℝ := (((a : ℝ) / (p : ℝ) : ℝ) : OnePoint ℝ)

/-- Actual equality of primitive projective columns has no arbitrary
real proportionality factor: determinant one leaves exactly the signs. -/
theorem equal_infinity_images_signed_first_column (g h : SL(2, ℤ))
    (he : mapGL ℝ g • (∞ : OnePoint ℝ) = mapGL ℝ h • (∞ : OnePoint ℝ)) :
    (∀ i : Fin 2, g i 0 = h i 0) ∨ (∀ i : Fin 2, g i 0 = -(h i 0)) := by
  have hfix : mapGL ℝ (h⁻¹ * g) • (∞ : OnePoint ℝ) = ∞ := by
    rw [map_mul, mul_smul, he, map_inv]
    simp
  have hc : (h⁻¹ * g) 1 0 = 0 := by
    simpa [OnePoint.smul_infty_eq_self_iff, mapGL_coe_matrix] using hfix
  obtain ⟨k, hk | hk⟩ := (lowerLeft_zero_iff_signed_translation (h⁻¹ * g)).mp hc
  · have hg : g = h * ModularGroup.T ^ k := by
      calc
        _ = h * (h⁻¹ * g) := by group
        _ = _ := by rw [hk]
    left
    intro i
    rw [hg]
    fin_cases i <;> simp [coe_mul, Matrix.mul_fin_two, ModularGroup.coe_T_zpow]
  · have hg : g = -(h * ModularGroup.T ^ k) := by
      calc
        _ = h * (h⁻¹ * g) := by group
        _ = _ := by rw [hk, mul_neg]
    right
    intro i
    rw [hg]
    fin_cases i <;> simp [coe_mul, Matrix.mul_fin_two, ModularGroup.coe_T_zpow]

/-- The arithmetic invariant uses actual determinant and level conditions;
the signed-column condition is derived from native cusp equality below. -/
theorem signed_middle_column_forces_congruence (p : ℕ) (hp : p.Prime)
    (a b : ℤ) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 (p ^ 2))
    (hcol : (g 0 0 * a + g 0 1 * (p : ℤ) = b ∧
        g 1 0 * a + g 1 1 * (p : ℤ) = (p : ℤ)) ∨
      (g 0 0 * a + g 0 1 * (p : ℤ) = -b ∧
        g 1 0 * a + g 1 1 * (p : ℤ) = -(p : ℤ))) :
    (p : ℤ) ∣ b - a := by
  have hpI : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c (p ^ 2) g).mp hg
  have hc : g 1 0 = (p : ℤ) ^ 2 * k := by simpa only [Nat.cast_pow] using hk
  have hdet : g 0 0 * g 1 1 - g 0 1 * ((p : ℤ) ^ 2 * k) = 1 := by
    simpa only [Matrix.det_fin_two, hc] using g.det_coe
  rcases hcol with ⟨htop, hbottom⟩ | ⟨htop, hbottom⟩
  · have hD : (p : ℤ) * k * a + g 1 1 = 1 := by
      apply mul_left_cancel₀ hpI
      calc
        (p : ℤ) * ((p : ℤ) * k * a + g 1 1) = g 1 0 * a + g 1 1 * (p : ℤ) := by rw [hc]; ring
        _ = (p : ℤ) * 1 := by simpa only [mul_one] using hbottom
    have hA : g 0 0 - 1 = (p : ℤ) * k * b := by
      linear_combination hdet - g 0 0 * hD + (p : ℤ) * k * htop
    refine ⟨k * a * b + g 0 1, ?_⟩
    linear_combination a * hA - htop
  · have hD : (p : ℤ) * k * a + g 1 1 = -1 := by
      apply mul_left_cancel₀ hpI
      calc
        (p : ℤ) * ((p : ℤ) * k * a + g 1 1) = g 1 0 * a + g 1 1 * (p : ℤ) := by rw [hc]; ring
        _ = (p : ℤ) * (-1) := by simpa only [mul_neg, mul_one] using hbottom
    have hA : g 0 0 + 1 = (p : ℤ) * k * b := by
      linear_combination -hdet + g 0 0 * hD - (p : ℤ) * k * htop
    refine ⟨-(k * a * b + g 0 1), ?_⟩
    linear_combination htop - a * hA

/-- Native Gamma0(p^2) equivalence of actual a/p and b/p forces the
middle-cusp residue invariant. Both primitive columns are exhibited by
Bezout determinant-one matrices, rather than assumed cusp labels. -/
theorem middle_action_forces_congruence (p : ℕ) (hp : p.Prime) (a b : ℤ)
    (ha : IsCoprime a (p : ℤ)) (hb : IsCoprime b (p : ℤ))
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 (p ^ 2))
    (he : mapGL ℝ g • middlePoint p a = middlePoint p b) :
    (p : ℤ) ∣ b - a := by
  obtain ⟨u, v, huv⟩ := ha
  obtain ⟨r, s, hrs⟩ := hb
  let A := infinityBezoutMatrix a (p : ℤ) u v huv
  let B := infinityBezoutMatrix b (p : ℤ) r s hrs
  have hpI : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hA : mapGL ℝ A • (∞ : OnePoint ℝ) = middlePoint p a :=
    infinityBezoutMatrix_action a (p : ℤ) u v huv hpI
  have hB : mapGL ℝ B • (∞ : OnePoint ℝ) = middlePoint p b :=
    infinityBezoutMatrix_action b (p : ℤ) r s hrs hpI
  have hEq : mapGL ℝ (g * A) • (∞ : OnePoint ℝ) = mapGL ℝ B • (∞ : OnePoint ℝ) := by
    rw [map_mul, mul_smul, hA, hB]
    exact he
  have hcols := equal_infinity_images_signed_first_column (g * A) B hEq
  apply signed_middle_column_forces_congruence p hp a b g hg
  rcases hcols with h | h
  · left
    constructor
    · simpa [A, B, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two] using h 0
    · simpa [A, B, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two] using h 1
  · right
    constructor
    · simpa [A, B, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two] using h 0
    · simpa [A, B, infinityBezoutMatrix, coe_mul, Matrix.mul_fin_two] using h 1

/-- Converse uses an actual integral translation, at the original level. -/
theorem middle_congruence_gives_action (p : ℕ) (hp : p.Prime) (a b : ℤ)
    (hab : (p : ℤ) ∣ b - a) :
    ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 (p ^ 2) ∧
      mapGL ℝ g • middlePoint p a = middlePoint p b := by
  obtain ⟨k, hk⟩ := hab
  have hb : b = a + (p : ℤ) * k := by linear_combination hk
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨ModularGroup.T ^ k, translation_mem_gamma0 (p ^ 2) k, ?_⟩
  have ht : mapGL ℝ (ModularGroup.T ^ k) • middlePoint p a =
      ((((a : ℝ) / (p : ℝ)) + (k : ℝ) : ℝ) : OnePoint ℝ) := by
    simp [middlePoint, OnePoint.smul_some_eq_ite, mapGL_coe_matrix, ModularGroup.coe_T_zpow, add_comm]
  rw [ht]
  apply congrArg (fun x : ℝ => (x : OnePoint ℝ))
  have hbR : (b : ℝ) = (a : ℝ) + (p : ℝ) * (k : ℝ) := by exact_mod_cast hb
  change (a : ℝ) / (p : ℝ) + (k : ℝ) = (b : ℝ) / (p : ℝ)
  rw [hbR]
  field_simp [hpR]
  <;> ring

theorem middle_actual_equivalence_iff (p : ℕ) (hp : p.Prime) (a b : ℤ)
    (ha : IsCoprime a (p : ℤ)) (hb : IsCoprime b (p : ℤ)) :
    (∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 (p ^ 2) ∧
      mapGL ℝ g • middlePoint p a = middlePoint p b) ↔ (p : ℤ) ∣ b - a :=
  ⟨fun ⟨g, hg, he⟩ => middle_action_forces_congruence p hp a b ha hb g hg he,
    middle_congruence_gives_action p hp a b⟩

end ImbalancedChen.Part3.PrimeSquareMiddleCuspInvariant20261026b
