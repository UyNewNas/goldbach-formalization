import ImbalancedChen.Part3Gamma0ActualCusps
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-! Explicit primitive-column Bezout matrices for the two prime-level
rational cusp channels. Both are literal integer determinant-one matrices,
their Gamma0 membership is proved, and their actions are Mathlib's actual
OnePoint real projective action. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly

namespace ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b

def infinityBezoutMatrix (a c u v : ℤ) (h : u * a + v * c = 1) : SL(2, ℤ) :=
  ⟨!![a, -v; c, u], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

theorem infinityBezoutMatrix_mem (p : ℕ) (a c u v : ℤ)
    (h : u * a + v * c = 1) (hpc : (p : ℤ) ∣ c) :
    infinityBezoutMatrix a c u v h ∈ CongruenceSubgroup.Gamma0 p := by
  rw [gamma0_mem_iff_level_dvd_c]
  exact hpc

theorem infinityBezoutMatrix_action (a c u v : ℤ)
    (h : u * a + v * c = 1) (hc : c ≠ 0) :
    mapGL ℝ (infinityBezoutMatrix a c u v h) • (∞ : OnePoint ℝ) =
      (((a : ℝ) / (c : ℝ) : ℝ) : OnePoint ℝ) := by
  have hcR : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
  simp [OnePoint.smul_infty_eq_ite, infinityBezoutMatrix, mapGL_coe_matrix, hcR]

def zeroBezoutMatrix (p : ℕ) (a c u v : ℤ)
    (h : u * c + v * ((p : ℤ) * a) = 1) : SL(2, ℤ) :=
  ⟨!![u, a; -(p : ℤ) * v, c], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

theorem zeroBezoutMatrix_mem (p : ℕ) (a c u v : ℤ)
    (h : u * c + v * ((p : ℤ) * a) = 1) :
    zeroBezoutMatrix p a c u v h ∈ CongruenceSubgroup.Gamma0 p := by
  rw [gamma0_mem_iff_level_dvd_c]
  change (p : ℤ) ∣ -(p : ℤ) * v
  exact ⟨-v, by ring⟩

theorem zeroBezoutMatrix_action (p : ℕ) (a c u v : ℤ)
    (h : u * c + v * ((p : ℤ) * a) = 1) (hc : c ≠ 0) :
    mapGL ℝ (zeroBezoutMatrix p a c u v h) • ((0 : ℝ) : OnePoint ℝ) =
      (((a : ℝ) / (c : ℝ) : ℝ) : OnePoint ℝ) := by
  have hcR : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
  simp [OnePoint.smul_some_eq_ite, zeroBezoutMatrix, mapGL_coe_matrix, hcR]

/-- The precise zero-channel Bezout input is a conclusion of primitive
column coprimality and the literal p-not-dividing-denominator branch. -/
theorem zeroChannel_isCoprime {p : ℕ} (hp : p.Prime)
    (a c : ℤ) (hac : IsCoprime a c) (hpc : ¬(p : ℤ) ∣ c) :
    IsCoprime c ((p : ℤ) * a) := by
  have hnot : ¬p ∣ c.natAbs := by
    intro hd
    exact hpc (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd))
  have hcpNat : c.natAbs.Coprime p := (hp.coprime_iff_not_dvd.mpr hnot).symm
  have hcp : IsCoprime c (p : ℤ) := Int.isCoprime_iff_nat_coprime.mpr
    (by simpa only [Int.natAbs_natCast] using hcpNat)
  exact hcp.mul_right hac.symm

theorem primitiveColumn_infinity_channel (p : ℕ) (a c : ℤ)
    (hac : IsCoprime a c) (hpc : (p : ℤ) ∣ c) (hc : c ≠ 0) :
    ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 p ∧
      g 0 0 = a ∧ g 1 0 = c ∧
        mapGL ℝ g • (∞ : OnePoint ℝ) = (((a : ℝ) / (c : ℝ) : ℝ) : OnePoint ℝ) := by
  obtain ⟨u, v, hbez⟩ := hac
  exact ⟨infinityBezoutMatrix a c u v hbez,
    infinityBezoutMatrix_mem p a c u v hbez hpc, rfl, rfl,
    infinityBezoutMatrix_action a c u v hbez hc⟩

theorem primitiveColumn_zero_channel {p : ℕ} (hp : p.Prime) (a c : ℤ)
    (hac : IsCoprime a c) (hpc : ¬(p : ℤ) ∣ c) (hc : c ≠ 0) :
    ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 p ∧
      g 0 1 = a ∧ g 1 1 = c ∧
        mapGL ℝ g • ((0 : ℝ) : OnePoint ℝ) =
          (((a : ℝ) / (c : ℝ) : ℝ) : OnePoint ℝ) := by
  obtain ⟨u, v, hbez⟩ := zeroChannel_isCoprime hp a c hac hpc
  exact ⟨zeroBezoutMatrix p a c u v hbez,
    zeroBezoutMatrix_mem p a c u v hbez, rfl, rfl,
    zeroBezoutMatrix_action p a c u v hbez hc⟩

end ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b
