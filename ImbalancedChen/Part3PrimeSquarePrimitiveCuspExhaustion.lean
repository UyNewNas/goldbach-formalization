import ImbalancedChen.Part3PrimeSquareMiddleTransportMatrices

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual prime-square primitive-column exhaustion, with three disjoint
denominator branches. Infinity uses the original actual matrix when
p^2|c. The zero branch proves the needed Bezout input for p^2*a, not p*a.
The middle branch consumes the new explicit transport with residue a*(c/p).
The output is genuine native OnePoint action by actual Gamma0(p^2) matrices. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b
open ImbalancedChen.Part3.PrimeSquareMiddleCuspInvariant20261026b
open ImbalancedChen.Part3.PrimeSquareMiddleTransportMatrices20261026b

namespace ImbalancedChen.Part3.PrimeSquarePrimitiveCuspExhaustion20261026b

/-- The zero branch needs coprimality with the ACTUAL p^2 level.
Both p factors are paid before constructing its determinant-one matrix. -/
theorem primitive_zero_branch (p : ℕ) (hp : p.Prime) (a c : ℤ)
    (hac : IsCoprime a c) (hpc : ¬ (p : ℤ) ∣ c) :
    ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 (p ^ 2) ∧
      g 0 1 = a ∧ g 1 1 = c ∧
      mapGL ℝ g • ((0 : ℝ) : OnePoint ℝ) = ((((a : ℝ) / (c : ℝ) : ℝ)) : OnePoint ℝ) := by
  have hc0 : c ≠ 0 := by intro h; apply hpc; simp [h]
  have hcp := prime_int_isCoprime_of_not_dvd p hp c hpc
  have hC : IsCoprime c (((p : ℤ) ^ 2) * a) := by
    simpa only [pow_two, mul_assoc] using hcp.mul_right (hcp.mul_right hac.symm)
  obtain ⟨u, v, hbez⟩ := hC
  have hbezSq : u * c + v * (((p ^ 2 : ℕ) : ℤ) * a) = 1 := by
    simpa only [Nat.cast_pow] using hbez
  exact ⟨zeroBezoutMatrix (p ^ 2) a c u v hbezSq,
    zeroBezoutMatrix_mem (p ^ 2) a c u v hbezSq, rfl, rfl,
    zeroBezoutMatrix_action (p ^ 2) a c u v hbezSq hc0⟩

/-- Every actual SL2Z primitive first column lands in exactly one of the
three denominator branches, with an actual Gamma0(p^2) transporter.
This includes c=0 through the infinity branch without dividing by c. -/
theorem modularCusp_three_channels (p : ℕ) (hp : p.Prime) (g : SL(2, ℤ)) :
    (∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • (∞ : OnePoint ℝ) = mapGL ℝ g • (∞ : OnePoint ℝ)) ∨
    (∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • ((0 : ℝ) : OnePoint ℝ) = mapGL ℝ g • (∞ : OnePoint ℝ)) ∨
    (∃ b : ℤ, ∃ hb : IsCoprime b (p : ℤ), ∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • middlePoint p b = mapGL ℝ g • (∞ : OnePoint ℝ)) := by
  by_cases hsq : ((p : ℤ) ^ 2) ∣ g 1 0
  · left
    have hg : g ∈ CongruenceSubgroup.Gamma0 (p ^ 2) :=
      (gamma0_mem_iff_level_dvd_c (p ^ 2) g).mpr (by simpa only [Nat.cast_pow] using hsq)
    exact ⟨⟨g, hg⟩, rfl⟩
  · have hc0 : g 1 0 ≠ 0 := by intro h; apply hsq; simp [h]
    have hgcusp : mapGL ℝ g • (∞ : OnePoint ℝ) =
        (((((g 0 0 : ℤ) : ℝ) / ((g 1 0 : ℤ) : ℝ)) : ℝ) : OnePoint ℝ) := by
      have hcR : ((g 1 0 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc0
      simp [OnePoint.smul_infty_eq_ite, mapGL_coe_matrix, hcR]
    by_cases hpdiv : (p : ℤ) ∣ g 1 0
    · right; right
      obtain ⟨b, hb, γ, hγ, hact⟩ := primitive_middle_branch p hp
        (g 0 0) (g 1 0) (g.isCoprime_col 0) hpdiv hsq
      exact ⟨b, hb, ⟨γ, hγ⟩, hact.trans hgcusp.symm⟩
    · right; left
      obtain ⟨γ, hγ, ha, hd, hact⟩ := primitive_zero_branch p hp
        (g 0 0) (g 1 0) (g.isCoprime_col 0) hpdiv
      exact ⟨⟨γ, hγ⟩, hact.trans hgcusp.symm⟩

/-- The same constructive exhaustion for the actual rational projective
line, with Mathlib's native rational cusp embedding. -/
theorem rationalCusp_three_channels (p : ℕ) (hp : p.Prime) (c : OnePoint ℚ) :
    (∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • (∞ : OnePoint ℝ) = OnePoint.map (Rat.cast : ℚ → ℝ) c) ∨
    (∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • ((0 : ℝ) : OnePoint ℝ) = OnePoint.map (Rat.cast : ℚ → ℝ) c) ∨
    (∃ b : ℤ, ∃ hb : IsCoprime b (p : ℤ), ∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • middlePoint p b = OnePoint.map (Rat.cast : ℚ → ℝ) c) := by
  have hrat := (isCusp_SL2Z_iff (c := OnePoint.map (Rat.cast : ℚ → ℝ) c)).mpr ⟨c, rfl⟩
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp hrat
  rw [hg]
  exact modularCusp_three_channels p hp g

end ImbalancedChen.Part3.PrimeSquarePrimitiveCuspExhaustion20261026b
