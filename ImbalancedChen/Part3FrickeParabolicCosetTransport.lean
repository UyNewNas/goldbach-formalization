import ImbalancedChen.Part3FrickeNormalizer
import ImbalancedChen.Part3Gamma0ParabolicCosetRows
import ImbalancedChen.Part3Gamma0GeneralCuspWidth

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

Actual Fricke transport between the original infinity stabilizer and the
actual cusp-zero stabilizer, including the central sign. Both stabilizers
are genuine subgroups INSIDE the original integer Gamma0(N). The quotient
is the existing nonnormal LEFT-ACTION parabolic quotient, not a quotient
by a normality assumption or by the whole spatial action kernel.

Literal W_N sends infinity to0 and0 toinfinity in Mathlib's actual real
projective-line action. The already proved Fricke Gamma0 automorphism
intertwines the two orbit relations and therefore constructs their coset
bijection. No assumed cusp equivalence or normalizer field occurs.
-/

namespace ImbalancedChen.Part3.FrickeParabolicCosetTransport

noncomputable section

open Matrix Matrix.SpecialLinearGroup MatrixGroups Set
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0GeneralCuspWidth20261025a
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.FrickeNormalizer

/-- The actual cusp-zero stabilizer inside Gamma0, central sign included. -/
def gammaZero (N : ℕ) : Subgroup (CongruenceSubgroup.Gamma0 N) where
  carrier := {g | (g : SL(2, ℤ)) 0 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ((g : SL(2, ℤ)) * (h : SL(2, ℤ))) 0 1 = 0
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two, hg, hh]
  inv_mem' := by
    intro g hg
    change ((g : SL(2, ℤ))⁻¹) 0 1 = 0
    simp [SL2_inv_expl, hg]

theorem gammaZero_mem_iff_actual_action (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    g ∈ gammaZero N ↔
      mapGL ℝ (g : SL(2, ℤ)) • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
  have hS : mapGL ℝ ModularGroup.S • (∞ : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
    simp [OnePoint.smul_infty_eq_ite, ModularGroup.S, mapGL_coe_matrix]
  have hactual := fixesIntegralCusp_iff_actual_action ModularGroup.S (g : SL(2, ℤ))
  rw [hS] at hactual
  have hc : FixesIntegralCusp ModularGroup.S (g : SL(2, ℤ)) ↔ (g : SL(2, ℤ)) 0 1 = 0 := by
    simp [FixesIntegralCusp, ModularGroup.S, SL2_inv_expl,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two]
  exact hc.symm.trans hactual

/-- These are the actual boundary cusps in the existing real GL action. -/
theorem frickeSL_boundary_infty (N : ℕ) (hN : 0 < N) :
    mapGL ℝ (frickeSL N hN) • (∞ : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  simp [OnePoint.smul_infty_eq_ite, frickeSL, frickeMatrix, mapGL_coe_matrix, hs]

theorem frickeSL_boundary_zero (N : ℕ) (hN : 0 < N) :
    mapGL ℝ (frickeSL N hN) • ((0 : ℝ) : OnePoint ℝ) = (∞ : OnePoint ℝ) := by
  simp [OnePoint.smul_some_eq_ite, frickeSL, frickeMatrix, mapGL_coe_matrix]

theorem frickeGamma0_mem_zero_iff_infty (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    frickeGamma0 N g ∈ gammaZero N ↔ g ∈ gammaInfinity N := by
  change -((g : SL(2, ℤ)) 1 0 / (N : ℤ)) = 0 ↔ (g : SL(2, ℤ)) 1 0 = 0
  constructor
  · intro h
    have hq : (g : SL(2, ℤ)) 1 0 / (N : ℤ) = 0 := by omega
    rw [← gamma0_exact_division N g, hq, mul_zero]
  · intro h
    simp [h]

theorem frickeGamma0_mem_infty_iff_zero (N : ℕ) (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) :
    frickeGamma0 N g ∈ gammaInfinity N ↔ g ∈ gammaZero N := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  change -(N : ℤ) * (g : SL(2, ℤ)) 0 1 = 0 ↔ (g : SL(2, ℤ)) 0 1 = 0
  simp [hN0]

/-- The actual infinity subgroup is carried ONTO the actual zero subgroup. -/
theorem frickeGamma0Aut_map_infty (N : ℕ) (hN : 0 < N) :
    (gammaInfinity N).map (frickeGamma0Aut N hN).toMonoidHom = gammaZero N := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (frickeGamma0_mem_zero_iff_infty N h).mpr hh
  · intro hg
    refine ⟨frickeGamma0 N g, (frickeGamma0_mem_infty_iff_zero N hN g).mpr hg, ?_⟩
    exact frickeGamma0_involutive N hN g

abbrev GammaZeroCosets (N : ℕ) :=
  Quotient (MulAction.orbitRel (gammaZero N) (CongruenceSubgroup.Gamma0 N))

/-- Actual subgroup orbit relation at0, with its nonnormal left-action convention. -/
theorem zero_orbit_iff_relative (N : ℕ) (g h : CongruenceSubgroup.Gamma0 N) :
    MulAction.orbitRel (gammaZero N) (CongruenceSubgroup.Gamma0 N) g h ↔
      g * h⁻¹ ∈ gammaZero N := by
  constructor
  · intro hrel
    obtain ⟨eta, heta⟩ := MulAction.orbitRel_apply.mp hrel
    rw [← heta]
    change (((eta : CongruenceSubgroup.Gamma0 N) * h) * h⁻¹) ∈ gammaZero N
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using eta.property
  · intro hrel
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨g * h⁻¹, hrel⟩, ?_⟩
    change (g * h⁻¹) * h = g
    group

theorem fricke_parabolic_orbit_iff (N : ℕ) (hN : 0 < N)
    (g h : CongruenceSubgroup.Gamma0 N) :
    MulAction.orbitRel (gammaZero N) (CongruenceSubgroup.Gamma0 N)
      (frickeGamma0 N g) (frickeGamma0 N h) ↔
    MulAction.orbitRel (gammaInfinity N) (CongruenceSubgroup.Gamma0 N) g h := by
  rw [zero_orbit_iff_relative, parabolic_orbit_iff_relative]
  have heq : frickeGamma0 N (g * h⁻¹) = frickeGamma0 N g * (frickeGamma0 N h)⁻¹ := by
    calc
      _ = (frickeGamma0Aut N hN) g * (frickeGamma0Aut N hN) h⁻¹ :=
        map_mul (frickeGamma0Aut N hN) g h⁻¹
      _ = _ := by rw [map_inv]
  rw [← heq]
  exact frickeGamma0_mem_zero_iff_infty N (g * h⁻¹)

theorem fricke_zero_orbit_iff (N : ℕ) (hN : 0 < N)
    (g h : CongruenceSubgroup.Gamma0 N) :
    MulAction.orbitRel (gammaInfinity N) (CongruenceSubgroup.Gamma0 N)
      (frickeGamma0 N g) (frickeGamma0 N h) ↔
    MulAction.orbitRel (gammaZero N) (CongruenceSubgroup.Gamma0 N) g h := by
  have hrel := fricke_parabolic_orbit_iff N hN (frickeGamma0 N g) (frickeGamma0 N h)
  simpa only [frickeGamma0_involutive N hN] using hrel.symm

def infinityToZeroCoset (N : ℕ) (hN : 0 < N) : GammaInfinityCosets N → GammaZeroCosets N :=
  Quotient.lift (fun g : CongruenceSubgroup.Gamma0 N => Quotient.mk'' (frickeGamma0 N g))
    (fun g h hrel => Quotient.sound ((fricke_parabolic_orbit_iff N hN g h).mpr hrel))

def zeroToInfinityCoset (N : ℕ) (hN : 0 < N) : GammaZeroCosets N → GammaInfinityCosets N :=
  Quotient.lift (fun g : CongruenceSubgroup.Gamma0 N => Quotient.mk'' (frickeGamma0 N g))
    (fun g h hrel => Quotient.sound ((fricke_zero_orbit_iff N hN g h).mpr hrel))

/-- A constructed bijection of ACTUAL parabolic coset index sets. No
stabilizer normality or cardinality equality is supplied by the caller. -/
def frickeParabolicCosetEquiv (N : ℕ) (hN : 0 < N) : GammaInfinityCosets N ≃ GammaZeroCosets N where
  toFun := infinityToZeroCoset N hN
  invFun := zeroToInfinityCoset N hN
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro g
    change Quotient.mk'' (frickeGamma0 N (frickeGamma0 N g)) = Quotient.mk'' g
    rw [frickeGamma0_involutive N hN g]
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro g
    change Quotient.mk'' (frickeGamma0 N (frickeGamma0 N g)) = Quotient.mk'' g
    rw [frickeGamma0_involutive N hN g]

theorem frickeParabolicCosetEquiv_mk (N : ℕ) (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) :
    frickeParabolicCosetEquiv N hN (Quotient.mk'' g) = Quotient.mk'' (frickeGamma0 N g) := rfl

/-- Actual upper-half-plane covariance underlying the cusp transport. -/
theorem frickeSL_intertwines_Gamma0 (N : ℕ) (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    realSL (g : SL(2, ℤ)) • (frickeSL N hN • z) =
      frickeSL N hN • (realSL (frickeGamma0 N g : SL(2, ℤ)) • z) := by
  have heq : realSL (g : SL(2, ℤ)) * frickeSL N hN =
      frickeSL N hN * realSL (frickeGamma0 N g : SL(2, ℤ)) := by
    rw [← frickeSL_conjugate_gamma0 N hN g]
    group
  simpa only [mul_smul] using congrArg (fun A : SL(2, ℝ) => A • z) heq

end
end ImbalancedChen.Part3.FrickeParabolicCosetTransport
