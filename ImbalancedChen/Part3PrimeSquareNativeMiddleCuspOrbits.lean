import ImbalancedChen.Part3PrimeSquareMiddleCuspSeparation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The middle-cusp residue family in Mathlib's ACTUAL cusp-orbit quotient
for Gamma0(p^2): primitive a/p and b/p represent the same native orbit
exactly when a=b modp. Every middle orbit differs from infinity and zero.
Full prime-square exhaustion is OPEN: no all-cusps theorem is inferred. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b
open ImbalancedChen.Part3.PrimeSquareMiddleCuspInvariant20261026b
open ImbalancedChen.Part3.PrimeSquareMiddleCuspSeparation20261026b

namespace ImbalancedChen.Part3.PrimeSquareNativeMiddleCuspOrbits20261026b

private theorem integral_image_is_actual_cusp (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    IsCusp (mapGL ℝ g • (∞ : OnePoint ℝ))
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
  apply (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).mpr
  exact isCusp_SL2Z_iff'.mpr ⟨g, rfl⟩

theorem middle_is_actual_cusp (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    IsCusp (middlePoint p a) (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  obtain ⟨u, v, huv⟩ := ha
  have hA := infinityBezoutMatrix_action a (p : ℤ) u v huv
    (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
  have hc := integral_image_is_actual_cusp (p ^ 2) (infinityBezoutMatrix a (p : ℤ) u v huv)
  simpa only [hA, middlePoint] using hc

def middleCusp (p : ℕ) (hp : p.Prime) (a : ℤ) (ha : IsCoprime a (p : ℤ)) :
    cuspsSubMulAction (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨middlePoint p a, middle_is_actual_cusp p hp a ha⟩

def middleCuspOrbit (p : ℕ) (hp : p.Prime) (a : ℤ) (ha : IsCoprime a (p : ℤ)) :
    CuspOrbits (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) :=
  Quotient.mk'' (middleCusp p hp a ha)

/-- Native quotient equality has the exact residue invariant, with no
assumed orbit representatives or real proportionality certificate. -/
theorem middleCuspOrbit_eq_iff (p : ℕ) (hp : p.Prime) (a b : ℤ)
    (ha : IsCoprime a (p : ℤ)) (hb : IsCoprime b (p : ℤ)) :
    middleCuspOrbit p hp a ha = middleCuspOrbit p hp b hb ↔ (p : ℤ) ∣ b - a := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
    have hval := congrArg (fun c : cuspsSubMulAction
      (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) => (c : OnePoint ℝ)) hγ
    change (γ : GL (Fin 2) ℝ) • middlePoint p b = middlePoint p a at hval
    obtain ⟨g, hg, hmap⟩ := γ.property
    have he : mapGL ℝ g • middlePoint p b = middlePoint p a := by
      simpa only [hmap] using hval
    have hd := middle_action_forces_congruence p hp b a hb ha g hg he
    have hneg : b - a = -(a - b) := by ring
    rw [hneg]
    exact dvd_neg.mpr hd
  · intro hd
    have hba : (p : ℤ) ∣ a - b := by
      have he : a - b = -(b - a) := by ring
      rw [he]
      exact dvd_neg.mpr hd
    obtain ⟨g, hg, he⟩ := middle_congruence_gives_action p hp b a hba
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨mapGL ℝ g, ⟨g, hg, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact he

/-- Distinct unit residues therefore give distinct ACTUAL middle cusps. -/
theorem middleCuspOrbit_ne_of_not_congruent (p : ℕ) (hp : p.Prime) (a b : ℤ)
    (ha : IsCoprime a (p : ℤ)) (hb : IsCoprime b (p : ℤ))
    (hab : ¬ (p : ℤ) ∣ b - a) :
    middleCuspOrbit p hp a ha ≠ middleCuspOrbit p hp b hb :=
  fun h => hab ((middleCuspOrbit_eq_iff p hp a b ha hb).mp h)

def infinityCusp (p : ℕ) (hp : p.Prime) :
    cuspsSubMulAction (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  refine ⟨∞, ?_⟩
  simpa using integral_image_is_actual_cusp (p ^ 2) (1 : SL(2, ℤ))

def zeroCusp (p : ℕ) (hp : p.Prime) :
    cuspsSubMulAction (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  refine ⟨((0 : ℝ) : OnePoint ℝ), ?_⟩
  simpa [OnePoint.smul_infty_eq_ite, ModularGroup.S, mapGL_coe_matrix] using
    integral_image_is_actual_cusp (p ^ 2) ModularGroup.S

def infinityCuspOrbit (p : ℕ) (hp : p.Prime) :
    CuspOrbits (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) :=
  Quotient.mk'' (infinityCusp p hp)

def zeroCuspOrbit (p : ℕ) (hp : p.Prime) :
    CuspOrbits (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) :=
  Quotient.mk'' (zeroCusp p hp)

theorem middleCuspOrbit_ne_infinity (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    middleCuspOrbit p hp a ha ≠ infinityCuspOrbit p hp := by
  intro h
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h.symm)
  have hval := congrArg (fun c : cuspsSubMulAction
    (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) => (c : OnePoint ℝ)) hγ
  change (γ : GL (Fin 2) ℝ) • middlePoint p a = (∞ : OnePoint ℝ) at hval
  obtain ⟨g, hg, hmap⟩ := γ.property
  apply middle_action_ne_infinity p hp a ha g hg
  simpa only [hmap] using hval

theorem middleCuspOrbit_ne_zero (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    middleCuspOrbit p hp a ha ≠ zeroCuspOrbit p hp := by
  intro h
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h.symm)
  have hval := congrArg (fun c : cuspsSubMulAction
    (CongruenceSubgroup.Gamma0 (p ^ 2) : Subgroup (GL (Fin 2) ℝ)) => (c : OnePoint ℝ)) hγ
  change (γ : GL (Fin 2) ℝ) • middlePoint p a = ((0 : ℝ) : OnePoint ℝ) at hval
  obtain ⟨g, hg, hmap⟩ := γ.property
  apply middle_action_ne_zero p hp a ha g hg
  simpa only [hmap] using hval

end ImbalancedChen.Part3.PrimeSquareNativeMiddleCuspOrbits20261026b
