import ImbalancedChen.Part3PrimeSquarePrimitiveCuspExhaustion
import ImbalancedChen.Part3PrimeActualCuspOrbits

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Full native prime-square cusp exhaustion is now DERIVED: infinity, zero,
and the primitive unit-residue middle cusps b/p exhaust Mathlib's actual
CuspOrbits for Gamma0(p^2). The previous actual middle-orbit congruence
invariant supplies their exact identifications, and all three families
are separated. This is geometric cusp exhaustion, not an all-level or
Eisenstein/spectral-completeness theorem. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.PrimeSquareMiddleCuspInvariant20261026b
open ImbalancedChen.Part3.PrimeSquareMiddleCuspSeparation20261026b
open ImbalancedChen.Part3.PrimeSquareNativeMiddleCuspOrbits20261026b
open ImbalancedChen.Part3.PrimeSquarePrimitiveCuspExhaustion20261026b

namespace ImbalancedChen.Part3.PrimeSquareActualCuspExhaustion20261026b

/-- Native arithmetic-subgroup cusp identification is consumed only after
the three actual primitive-column transporting matrices were constructed. -/
theorem actualCusp_three_channels (p : ℕ) (hp : p.Prime) (c : OnePoint ℝ)
    (hc : IsCusp c (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ))) :
    (∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • (∞ : OnePoint ℝ) = c) ∨
    (∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • ((0 : ℝ) : OnePoint ℝ) = c) ∨
    (∃ b : ℤ, ∃ hb : IsCoprime b (p : ℤ), ∃ γ : CongruenceSubgroup.Gamma0 (p ^ 2),
      mapGL ℝ (γ : SL(2, ℤ)) • middlePoint p b = c) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hSL := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
    (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ))).mp hc
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp hSL
  rw [hg]
  exact modularCusp_three_channels p hp g

/-- Every actual native cusp-orbit class occurs among these constructed
families. Middle labels are precisely unit residues modulo p, by
middleCuspOrbit_eq_iff from the independent signed-column invariant. -/
theorem cuspOrbit_exhaustion (p : ℕ) (hp : p.Prime)
    (q : CuspOrbits (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ))) :
    q = infinityCuspOrbit p hp ∨ q = zeroCuspOrbit p hp ∨
      ∃ b : ℤ, ∃ hb : IsCoprime b (p : ℤ), q = middleCuspOrbit p hp b hb := by
  refine Quotient.inductionOn q ?_
  intro c
  rcases actualCusp_three_channels p hp (c : OnePoint ℝ) c.property with h | h | h
  · obtain ⟨γ, hγ⟩ := h
    left
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨mapGL ℝ (γ : SL(2, ℤ)), ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  · obtain ⟨γ, hγ⟩ := h
    right; left
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨mapGL ℝ (γ : SL(2, ℤ)), ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  · obtain ⟨b, hb, γ, hγ⟩ := h
    right; right
    refine ⟨b, hb, ?_⟩
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨mapGL ℝ (γ : SL(2, ℤ)), ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hγ

/-- Infinity and zero stay distinct at level p^2. Level divisibility
proves the needed actual inclusion into Gamma0(p), rather than assuming it. -/
theorem infinityCuspOrbit_ne_zero (p : ℕ) (hp : p.Prime) :
    infinityCuspOrbit p hp ≠ zeroCuspOrbit p hp := by
  intro h
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  have hval := congrArg (fun c : cuspsSubMulAction
    (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) => (c : OnePoint ℝ)) hγ
  change (γ : GL (Fin 2) ℝ) • ((0 : ℝ) : OnePoint ℝ) = (∞ : OnePoint ℝ) at hval
  obtain ⟨g, hg, hmap⟩ := γ.property
  have hgp : g ∈ CongruenceSubgroup.Gamma0 p := by
    obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c (p ^ 2) g).mp hg
    apply (gamma0_mem_iff_level_dvd_c p g).mpr
    refine ⟨(p : ℤ) * k, ?_⟩
    simpa only [Nat.cast_pow, pow_two, mul_assoc] using hk
  apply PrimeActualCuspOrbits20261026b.gamma0_zero_ne_infinity hp g hgp
  simpa only [hmap] using hval

end ImbalancedChen.Part3.PrimeSquareActualCuspExhaustion20261026b
