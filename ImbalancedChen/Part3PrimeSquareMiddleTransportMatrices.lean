import ImbalancedChen.Part3PrimeSquareNativeMiddleCuspOrbits

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Explicit missing prime-square middle-cusp construction. If c=p*d with
p not dividing d and (a,c) primitive, b=a*d is a unit modulo p. Two actual
Bezout matrices give a displayed Gamma0(p^2) transport from b/p to a/c.
Its lower-left entry is proved to be p^2*(d^2*v*r-u*s). -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups OnePoint
open scoped MatrixGroups ModularGroup
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.PrimeCuspBezoutMatrices20261026b
open ImbalancedChen.Part3.PrimeSquareMiddleCuspInvariant20261026b

namespace ImbalancedChen.Part3.PrimeSquareMiddleTransportMatrices20261026b

theorem prime_int_isCoprime_of_not_dvd (p : ℕ) (hp : p.Prime) (d : ℤ)
    (hd : ¬ (p : ℤ) ∣ d) : IsCoprime d (p : ℤ) := by
  have hnot : ¬ p ∣ d.natAbs := by
    intro h
    exact hd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  have hnat : d.natAbs.Coprime p := (hp.coprime_iff_not_dvd.mpr hnot).symm
  exact Int.isCoprime_iff_nat_coprime.mpr (by simpa only [Int.natAbs_natCast] using hnat)

def middleTransportMatrix (p : ℕ) (a d u v r s : ℤ)
    (hA : u * a + v * ((p : ℤ) * d) = 1)
    (hB : r * (a * d) + s * (p : ℤ) = 1) : SL(2, ℤ) :=
  infinityBezoutMatrix a ((p : ℤ) * d) u v hA *
    (infinityBezoutMatrix (a * d) (p : ℤ) r s hB)⁻¹

/-- Both Bezout identities are used: this is stronger than merely
knowing that the bottom-left entry is divisible by p. -/
theorem middleTransportMatrix_lowerLeft (p : ℕ) (a d u v r s : ℤ)
    (hA : u * a + v * ((p : ℤ) * d) = 1)
    (hB : r * (a * d) + s * (p : ℤ) = 1) :
    middleTransportMatrix p a d u v r s hA hB 1 0 =
      (p : ℤ) ^ 2 * (d ^ 2 * v * r - u * s) := by
  have hcancel : d * r - u = (p : ℤ) * (d ^ 2 * v * r - u * s) := by
    linear_combination u * hB - d * r * hA
  have hentry : middleTransportMatrix p a d u v r s hA hB 1 0 =
      (p : ℤ) * (d * r - u) := by
    simp [middleTransportMatrix, infinityBezoutMatrix, SL2_inv_expl,
      coe_mul, Matrix.mul_fin_two] <;> ring
  rw [hentry, hcancel]
  ring

theorem middleTransportMatrix_mem (p : ℕ) (a d u v r s : ℤ)
    (hA : u * a + v * ((p : ℤ) * d) = 1)
    (hB : r * (a * d) + s * (p : ℤ) = 1) :
    middleTransportMatrix p a d u v r s hA hB ∈ CongruenceSubgroup.Gamma0 (p ^ 2) := by
  rw [gamma0_mem_iff_level_dvd_c, middleTransportMatrix_lowerLeft]
  exact ⟨d ^ 2 * v * r - u * s, by simp only [Nat.cast_pow]⟩

theorem middleTransportMatrix_action (p : ℕ) (hp : p.Prime) (a d u v r s : ℤ)
    (hA : u * a + v * ((p : ℤ) * d) = 1)
    (hB : r * (a * d) + s * (p : ℤ) = 1) (hd : d ≠ 0) :
    mapGL ℝ (middleTransportMatrix p a d u v r s hA hB) • middlePoint p (a * d) =
      ((((a : ℝ) / (((p : ℤ) * d : ℤ) : ℝ)) : ℝ) : OnePoint ℝ) := by
  have hpI : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hBact : mapGL ℝ (infinityBezoutMatrix (a * d) (p : ℤ) r s hB) • (∞ : OnePoint ℝ) =
      middlePoint p (a * d) := infinityBezoutMatrix_action _ _ _ _ hB hpI
  have hm : middleTransportMatrix p a d u v r s hA hB *
      infinityBezoutMatrix (a * d) (p : ℤ) r s hB =
      infinityBezoutMatrix a ((p : ℤ) * d) u v hA := by
    dsimp [middleTransportMatrix]
    group
  rw [← hBact, ← mul_smul, ← map_mul, hm]
  exact infinityBezoutMatrix_action _ _ _ _ hA (mul_ne_zero hpI hd)

/-- The first genuinely new primitive-column reduction branch beyond
the two prime-level cusps. The actual representative numerator is a*d,
not a/d, and its primitive unit property is a proved conclusion. -/
theorem primitive_middle_branch (p : ℕ) (hp : p.Prime) (a c : ℤ)
    (hac : IsCoprime a c) (hpc : (p : ℤ) ∣ c) (hpsq : ¬ ((p : ℤ) ^ 2) ∣ c) :
    ∃ b : ℤ, IsCoprime b (p : ℤ) ∧ ∃ g : SL(2, ℤ),
      g ∈ CongruenceSubgroup.Gamma0 (p ^ 2) ∧
      mapGL ℝ g • middlePoint p b = ((((a : ℝ) / (c : ℝ) : ℝ)) : OnePoint ℝ) := by
  obtain ⟨d, hd⟩ := hpc
  have hdp : ¬ (p : ℤ) ∣ d := by
    rintro ⟨k, hk⟩
    apply hpsq
    refine ⟨k, ?_⟩
    rw [hd, hk]
    ring
  have hd0 : d ≠ 0 := by intro h; apply hdp; simp [h]
  obtain ⟨u, v, hA⟩ := hac
  rw [hd] at hA
  have hap : IsCoprime a (p : ℤ) := ⟨u, v * d, by linear_combination hA⟩
  have hdpC := prime_int_isCoprime_of_not_dvd p hp d hdp
  have hbp : IsCoprime (a * d) (p : ℤ) := hap.mul_left hdpC
  obtain ⟨r, s, hB⟩ := hbp
  refine ⟨a * d, ⟨r, s, hB⟩, middleTransportMatrix p a d u v r s hA hB,
    middleTransportMatrix_mem p a d u v r s hA hB, ?_⟩
  rw [hd]
  exact middleTransportMatrix_action p hp a d u v r s hA hB hd0

end ImbalancedChen.Part3.PrimeSquareMiddleTransportMatrices20261026b
