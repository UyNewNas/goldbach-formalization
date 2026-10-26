import ImbalancedChen.Part3PrimeRationalCuspExhaustion

/-! Exactly the two genuine Mathlib cusp orbits for Gamma0(p). Native
arithmetic-subgroup cusp identification supplies actual cusps; explicit
prime Bezout classification supplies representatives. Determinant one and
p|c prove that zero cannot be carried to infinity. The resulting two
distinct classes exhaust Mathlib's actual CuspOrbits quotient.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.PrimeRationalCuspExhaustion20261026b

namespace ImbalancedChen.Part3.PrimeActualCuspOrbits20261026b

theorem actualCusp_two_channels {p : ℕ} (hp : p.Prime) (c : OnePoint ℝ)
    (hc : IsCusp c (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))) :
    (∃ γ : CongruenceSubgroup.Gamma0 p,
      mapGL ℝ (γ : SL(2, ℤ)) • (∞ : OnePoint ℝ) = c) ∨
    (∃ γ : CongruenceSubgroup.Gamma0 p,
      mapGL ℝ (γ : SL(2, ℤ)) • ((0 : ℝ) : OnePoint ℝ) = c) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hSL := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
    (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))).mp hc
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp hSL
  rw [hg]
  exact modularCusp_two_channels hp g

theorem gamma0_zero_ne_infinity {p : ℕ} (hp : p.Prime)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 p) :
    mapGL ℝ g • ((0 : ℝ) : OnePoint ℝ) ≠ (∞ : OnePoint ℝ) := by
  intro h
  have hd : g 1 1 = 0 := by
    by_contra hd
    have hdR : ((g 1 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
    simp [OnePoint.smul_some_eq_ite, mapGL_coe_matrix, hdR] at h
  have hc : (p : ℤ) ∣ g 1 0 := (gamma0_mem_iff_level_dvd_c p g).mp hg
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (det_coe g)
  have hbc : -(g 0 1 * g 1 0) = 1 := by simpa only [hd, mul_zero, zero_sub] using hdet
  have hdiv : (p : ℤ) ∣ (1 : ℤ) := by
    rw [← hbc]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hc (g 0 1))
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hdiv)

theorem gamma0_infinity_ne_zero {p : ℕ} (hp : p.Prime)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 p) :
    mapGL ℝ g • (∞ : OnePoint ℝ) ≠ ((0 : ℝ) : OnePoint ℝ) := by
  intro h
  apply gamma0_zero_ne_infinity hp g⁻¹ ((CongruenceSubgroup.Gamma0 p).inv_mem hg)
  rw [← h]
  simp

theorem infinity_isCusp {p : ℕ} (hp : p.Prime) :
    IsCusp (∞ : OnePoint ℝ) (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
    (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))).mpr
  exact isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩

theorem zero_isCusp {p : ℕ} (hp : p.Prime) :
    IsCusp ((0 : ℝ) : OnePoint ℝ)
      (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
    (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))).mpr
  refine isCusp_SL2Z_iff'.mpr ⟨ModularGroup.S, ?_⟩
  simp [OnePoint.smul_infty_eq_ite, ModularGroup.S, mapGL_coe_matrix]

def infinityCusp (p : ℕ) (hp : p.Prime) :
    cuspsSubMulAction (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨∞, infinity_isCusp hp⟩

def zeroCusp (p : ℕ) (hp : p.Prime) :
    cuspsSubMulAction (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨((0 : ℝ) : OnePoint ℝ), zero_isCusp hp⟩

def infinityCuspOrbit (p : ℕ) (hp : p.Prime) :
    CuspOrbits (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) :=
  Quotient.mk'' (infinityCusp p hp)

def zeroCuspOrbit (p : ℕ) (hp : p.Prime) :
    CuspOrbits (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) :=
  Quotient.mk'' (zeroCusp p hp)

/-- Inequivalence in Mathlib's genuine cusp-orbit quotient. -/
theorem infinityCuspOrbit_ne_zero (p : ℕ) (hp : p.Prime) :
    infinityCuspOrbit p hp ≠ zeroCuspOrbit p hp := by
  intro h
  have hrel := Quotient.exact h
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hrel
  have hval := congrArg (fun c : cuspsSubMulAction
    (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) => (c : OnePoint ℝ)) hγ
  change (γ : GL (Fin 2) ℝ) • ((0 : ℝ) : OnePoint ℝ) = (∞ : OnePoint ℝ) at hval
  obtain ⟨g, hg, hmap⟩ := γ.property
  apply gamma0_zero_ne_infinity hp g hg
  simpa only [hmap] using hval

/-- The two distinct native classes exhaust the ACTUAL cusp-orbit type.
This makes a two-channel prime cusp indexing exhaustive; it does not
assert Eisenstein/spectral completeness. -/
theorem cuspOrbit_exhaustion (p : ℕ) (hp : p.Prime)
    (q : CuspOrbits (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))) :
    q = infinityCuspOrbit p hp ∨ q = zeroCuspOrbit p hp := by
  refine Quotient.inductionOn q ?_
  intro c
  rcases actualCusp_two_channels hp (c : OnePoint ℝ) c.property with h | h
  · obtain ⟨γ, hγ⟩ := h
    left
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨mapGL ℝ (γ : SL(2, ℤ)), ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  · obtain ⟨γ, hγ⟩ := h
    right
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨mapGL ℝ (γ : SL(2, ℤ)), ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hγ

end ImbalancedChen.Part3.PrimeActualCuspOrbits20261026b
