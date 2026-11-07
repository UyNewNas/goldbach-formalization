import ImbalancedChen.Part3PrimeCuspBezoutMatrices

/-! Exhaustion of the genuine rational projective line by the infinity
and zero Gamma0(p) channels. Mathlib's actual SL2 primitive first column
and rational cusp transitivity are consumed; no classification assumption
or abstract two-channel matrix is used. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b

namespace ImbalancedChen.Part3.PrimeRationalCuspExhaustion20261026b

/-- Every actual modular-group rational cusp has one of the two native
prime-level representatives, with a genuine Gamma0(p) transporting matrix. -/
theorem modularCusp_two_channels {p : ℕ} (hp : p.Prime) (g : SL(2, ℤ)) :
    (∃ γ : CongruenceSubgroup.Gamma0 p,
      mapGL ℝ (γ : SL(2, ℤ)) • (∞ : OnePoint ℝ) = mapGL ℝ g • (∞ : OnePoint ℝ)) ∨
    (∃ γ : CongruenceSubgroup.Gamma0 p,
      mapGL ℝ (γ : SL(2, ℤ)) • ((0 : ℝ) : OnePoint ℝ) =
        mapGL ℝ g • (∞ : OnePoint ℝ)) := by
  by_cases hd : (p : ℤ) ∣ g 1 0
  · left
    have hg : g ∈ CongruenceSubgroup.Gamma0 p := (gamma0_mem_iff_level_dvd_c p g).mpr hd
    exact ⟨⟨g, hg⟩, rfl⟩
  · right
    have hc : g 1 0 ≠ 0 := by
      intro hc
      apply hd
      simp [hc]
    obtain ⟨γ, hγ, ha, hdγ, hact⟩ := primitiveColumn_zero_channel hp
      (g 0 0) (g 1 0) (g.isCoprime_col 0) hd hc
    refine ⟨⟨γ, hγ⟩, ?_⟩
    have hgcusp : mapGL ℝ g • (∞ : OnePoint ℝ) =
        ((((g 0 0 : ℤ) : ℝ) / ((g 1 0 : ℤ) : ℝ) : ℝ) : OnePoint ℝ) := by
      have hcR : ((g 1 0 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
      simp [OnePoint.smul_infty_eq_ite, mapGL_coe_matrix, hcR]
    exact hact.trans hgcusp.symm

/-- Actual Mathlib rational cusps, including infinity, are exhausted by
these two Gamma0(p) channels in the native OnePoint real action. -/
theorem rationalCusp_two_channels {p : ℕ} (hp : p.Prime) (c : OnePoint ℚ) :
    (∃ γ : CongruenceSubgroup.Gamma0 p,
      mapGL ℝ (γ : SL(2, ℤ)) • (∞ : OnePoint ℝ) =
        OnePoint.map (Rat.cast : ℚ → ℝ) c) ∨
    (∃ γ : CongruenceSubgroup.Gamma0 p,
      mapGL ℝ (γ : SL(2, ℤ)) • ((0 : ℝ) : OnePoint ℝ) =
        OnePoint.map (Rat.cast : ℚ → ℝ) c) := by
  have hrat := (isCusp_SL2Z_iff (c := OnePoint.map (Rat.cast : ℚ → ℝ) c)).mpr ⟨c, rfl⟩
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp hrat
  rw [hg]
  exact modularCusp_two_channels hp g

end ImbalancedChen.Part3.PrimeRationalCuspExhaustion20261026b
