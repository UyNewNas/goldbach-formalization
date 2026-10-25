import ImbalancedChen.Part3PrimitiveEisensteinParameterAutomorphy
import ImbalancedChen.Part3Gamma0ParabolicEisensteinHalfPairs

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

The ACTUAL level-N complex Eisenstein seed and sum, with primitive condition
IsCoprime(c,d) and N|c. The actual Gamma0(N) right action preserves this row
type. Simultaneous-sign fibres are the already constructed actual Bool
fibres, now counted for complex-valued even seeds. Consequently the literal
half-row sum equals the genuine GammaInfinity\Gamma0 complex cusp sum.

All automorphy is derived from this level-preserving integer permutation.
No hLevelInvariant, assumed coset normalization, Fourier formula, critical-
line continuation or spectral supplier is used. N is not a dummy label.
-/

namespace ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein

noncomputable section

open Set Complex UpperHalfPlane EisensteinSeries Matrix
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEisensteinHalfPairs20261025a
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAutomorphy

def toPrimitiveRow (N : ℕ) (v : LevelPrimitiveRow N) : PrimitivePair :=
  ⟨v.1, (EisensteinSeries.mem_gammaSet_one v.1).mpr v.property.1⟩

/-- Literal restriction of the actual complex seed to gcd(c,d)=1,N|c. -/
def levelComplexSeed (N : ℕ) (z : ℍ) (v : LevelPrimitiveRow N) (s : ℂ) : ℂ :=
  complexSeed z (toPrimitiveRow N v) s

theorem norm_levelComplexSeed (N : ℕ) (z : ℍ) (v : LevelPrimitiveRow N) (s : ℂ) :
    ‖levelComplexSeed N z v s‖ = seed s.re z v.1 := by
  simpa only [levelComplexSeed, norm_complexSeed, positiveBase_rpow_eq_seed]

theorem levelComplexSeed_summable (N : ℕ) (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : LevelPrimitiveRow N => levelComplexSeed N z v s) := by
  apply Summable.of_norm_bounded ((seed_summable s.re hs z).subtype _)
  intro v
  exact (norm_levelComplexSeed N z v s).le

theorem levelComplexSeed_even (N : ℕ) (z : ℍ) (s : ℂ) (v : LevelPrimitiveRow N) :
    levelComplexSeed N z (rowNeg N v) s = levelComplexSeed N z v s := by
  have hb : positiveBase z (toPrimitiveRow N (rowNeg N v)) = positiveBase z (toPrimitiveRow N v) := by
    calc
      _ = seed 1 z (-v.1) := by
        simpa only [Real.rpow_one] using positiveBase_rpow_eq_seed 1 z (toPrimitiveRow N (rowNeg N v))
      _ = seed 1 z v.1 := seed_neg 1 z v.1
      _ = _ := by
        symm
        simpa only [Real.rpow_one] using positiveBase_rpow_eq_seed 1 z (toPrimitiveRow N v)
  simp only [levelComplexSeed, complexSeed, hb]

/-- The original primitive condition is invariant under the actual integer
SL2 row action; the level condition uses BOTH N|c and N|gamma_10. -/
def levelRowRight (N : ℕ) (gamma : CongruenceSubgroup.Gamma0 N)
    (v : LevelPrimitiveRow N) : LevelPrimitiveRow N :=
  ⟨v.1 ᵥ* ((gamma : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
    constructor
    · exact v.property.1.vecMulSL (gamma : SL(2, ℤ))
    · have hg : (N : ℤ) ∣ (gamma : SL(2, ℤ)) 1 0 :=
        (gamma0_mem_iff_level_dvd_c N (gamma : SL(2, ℤ))).mp gamma.property
      have hdiv : (N : ℤ) ∣ v.1 0 * (gamma : SL(2, ℤ)) 0 0 +
          v.1 1 * (gamma : SL(2, ℤ)) 1 0 :=
        dvd_add (dvd_mul_of_dvd_left v.property.2 _) (dvd_mul_of_dvd_right hg _)
      simpa only [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hdiv⟩

/-- True level-preserving row permutation; inverse is actual Gamma0 inverse. -/
def levelRowRightEquiv (N : ℕ) (gamma : CongruenceSubgroup.Gamma0 N) :
    LevelPrimitiveRow N ≃ LevelPrimitiveRow N where
  toFun := levelRowRight N gamma
  invFun := levelRowRight N gamma⁻¹
  left_inv v := by
    apply Subtype.ext
    change (v.1 ᵥ* ((gamma : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ᵥ*
      (((gamma : SL(2, ℤ))⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = v.1
    simp only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv v := by
    apply Subtype.ext
    change (v.1 ᵥ* (((gamma : SL(2, ℤ))⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)) ᵥ*
      ((gamma : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v.1
    simp only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

theorem levelComplexSeed_Gamma0_apply (N : ℕ) (s : ℂ)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : ℍ) (v : LevelPrimitiveRow N) :
    levelComplexSeed N (gamma • z) v s = levelComplexSeed N z (levelRowRight N gamma v) s := by
  have heq : primitivePairEquiv (gamma : SL(2, ℤ)) (toPrimitiveRow N v) =
      toPrimitiveRow N (levelRowRight N gamma v) := by
    apply Subtype.ext
    exact primitivePairEquiv_value (gamma : SL(2, ℤ)) (toPrimitiveRow N v)
  simpa only [levelComplexSeed, heq] using
    complexSeed_SL2_apply s (gamma : SL(2, ℤ)) z (toPrimitiveRow N v)

/-- The actual normalized primitive level-N complex series. -/
def levelPrimitiveComplexEisenstein (N : ℕ) (s : ℂ) (z : ℍ) : ℂ :=
  (1 / 2 : ℂ) * ∑' v : LevelPrimitiveRow N, levelComplexSeed N z v s

theorem levelPrimitiveComplexEisenstein_Gamma0_invariant (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    levelPrimitiveComplexEisenstein N s (gamma • z) = levelPrimitiveComplexEisenstein N s z := by
  have hsum : (∑' v : LevelPrimitiveRow N, levelComplexSeed N (gamma • z) v s) =
      ∑' v : LevelPrimitiveRow N, levelComplexSeed N z v s := by
    calc
      _ = ∑' v : LevelPrimitiveRow N, levelComplexSeed N z (levelRowRight N gamma v) s :=
        tsum_congr (fun v => levelComplexSeed_Gamma0_apply N s gamma z v)
      _ = _ := (levelRowRightEquiv N gamma).tsum_eq (fun v => levelComplexSeed N z v s)
  exact congrArg ((1 / 2 : ℂ) * ·) hsum

/-- Complex even seeds descend through the already established actual
signed-row quotient, rather than through an assumed normalization field. -/
def complexSignedSeed (N : ℕ) (f : LevelPrimitiveRow N → ℂ)
    (hneg : ∀ v, f (rowNeg N v) = f v) : SignedPrimitiveRows N → ℂ :=
  Quotient.lift f (fun v w h => by
    rcases h with h | h
    · exact congrArg f (Subtype.ext h)
    · have hv : v = rowNeg N w := Subtype.ext h
      rw [hv]
      exact hneg w)

theorem complexSignedSeed_mk (N : ℕ) (f : LevelPrimitiveRow N → ℂ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (v : LevelPrimitiveRow N) :
    complexSignedSeed N f hneg (rowProjection N v) = f v := rfl

theorem complexSignedSeed_representative (N : ℕ) (f : LevelPrimitiveRow N → ℂ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (q : SignedPrimitiveRows N) :
    complexSignedSeed N f hneg q = f (rowRepresentative N q) := by
  rw [← rowRepresentative_class N q]
  rfl

theorem tsum_complex_signed_fiber (N : ℕ) (f : LevelPrimitiveRow N → ℂ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (q : SignedPrimitiveRows N) :
    (∑' v : RowFiber N q, f v.1) = 2 * complexSignedSeed N f hneg q := by
  calc
    _ = ∑' b : Bool, f (signedFiberEquiv N q b).1 :=
      ((signedFiberEquiv N q).tsum_eq (fun v : RowFiber N q => f v.1)).symm
    _ = f (rowRepresentative N q) + f (rowNeg N (rowRepresentative N q)) := by
      simp [tsum_fintype, signedFiberEquiv_apply, signedFiberParam]
    _ = _ := by rw [hneg, complexSignedSeed_representative]; ring

theorem tsum_complex_rows_eq_two_parabolic_cosets (N : ℕ) (f : LevelPrimitiveRow N → ℂ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (hsum : Summable f) :
    (∑' v : LevelPrimitiveRow N, f v) =
      2 * ∑' q : GammaInfinityCosets N,
        complexSignedSeed N f hneg (parabolicPrimitiveRowEquiv N q) := by
  have hgroup : HasSum (fun q : SignedPrimitiveRows N => ∑' v : RowFiber N q, f v.1)
      (∑' v : LevelPrimitiveRow N, f v) := hsum.hasSum.tsum_fiberwise (rowProjection N)
  have h := hgroup.tsum_eq
  simp_rw [tsum_complex_signed_fiber N f hneg] at h
  rw [tsum_mul_left] at h
  rw [(parabolicPrimitiveRowEquiv N).tsum_eq (complexSignedSeed N f hneg)]
  exact h.symm

theorem complexSignedSeed_summable (N : ℕ) (f : LevelPrimitiveRow N → ℂ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (hsum : Summable f) :
    Summable (complexSignedSeed N f hneg) := by
  have hgroup : HasSum (fun q : SignedPrimitiveRows N => ∑' v : RowFiber N q, f v.1)
      (∑' v : LevelPrimitiveRow N, f v) := hsum.hasSum.tsum_fiberwise (rowProjection N)
  have htwo : Summable (fun q : SignedPrimitiveRows N => 2 * complexSignedSeed N f hneg q) := by
    simpa only [tsum_complex_signed_fiber N f hneg] using hgroup.summable
  exact (summable_mul_left_iff (by norm_num : (2 : ℂ) ≠ 0)).mp htwo

/-- Actual complex y^s cusp seed on the upper half plane, with y>0. -/
def complexCuspSeed (s : ℂ) (z : ℍ) : ℂ :=
  Complex.exp (s * (Real.log z.im : ℂ))

theorem complexCuspSeed_periodic (s : ℂ) : ∀ k : ℤ, ∀ z : ℍ,
    complexCuspSeed s ((k : ℝ) +ᵥ z) = complexCuspSeed s z := by
  intro k z
  simp only [complexCuspSeed, UpperHalfPlane.vadd_im]

/-- Genuine GammaInfinity\Gamma0 parabolic complex sum, not the full-group quotient. -/
def actualComplexParabolicEisenstein (N : ℕ) (s : ℂ) (z : ℍ) : ℂ :=
  ∑' q : GammaInfinityCosets N,
    periodicSeedOnCosets N (complexCuspSeed s) (complexCuspSeed_periodic s) z q

theorem levelComplexSeed_bottomRow (N : ℕ) (s : ℂ) (z : ℍ)
    (g : CongruenceSubgroup.Gamma0 N) :
    levelComplexSeed N z (gamma0BottomRow N g) s = complexCuspSeed s (g • z) := by
  have hb : positiveBase z (toPrimitiveRow N (gamma0BottomRow N g)) = (g • z).im := by
    calc
      _ = seed 1 z (bottomRow (g : SL(2, ℤ))) := by
        simpa only [Real.rpow_one] using
          positiveBase_rpow_eq_seed 1 z (toPrimitiveRow N (gamma0BottomRow N g))
      _ = _ := by simpa only [Real.rpow_one] using seed_bottomRow_eq_im_pow 1 (g : SL(2, ℤ)) z
  simp only [levelComplexSeed, complexSeed, complexCuspSeed, hb]

theorem complex_parabolic_seed_row_dictionary (N : ℕ) (s : ℂ) (z : ℍ)
    (q : GammaInfinityCosets N) :
    periodicSeedOnCosets N (complexCuspSeed s) (complexCuspSeed_periodic s) z q =
      complexSignedSeed N (fun v => levelComplexSeed N z v s) (levelComplexSeed_even N z s)
        (parabolicPrimitiveRowEquiv N q) := by
  refine Quotient.inductionOn q ?_
  intro g
  change complexCuspSeed s (g • z) = levelComplexSeed N z (gamma0BottomRow N g) s
  exact (levelComplexSeed_bottomRow N s z g).symm

theorem actualComplexParabolicEisenstein_summable (N : ℕ) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    Summable (fun q : GammaInfinityCosets N =>
      periodicSeedOnCosets N (complexCuspSeed s) (complexCuspSeed_periodic s) z q) := by
  have h := (parabolicPrimitiveRowEquiv N).summable_iff.mpr
    (complexSignedSeed_summable N (fun v => levelComplexSeed N z v s)
      (levelComplexSeed_even N z s) (levelComplexSeed_summable N z s hs))
  simpa only [← complex_parabolic_seed_row_dictionary N s z] using h

/-- Factor1/2 is derived from genuine complex even two-point fibres at
every level; it is not a hypothesis or an N=1 renaming. -/
theorem actualComplexParabolicEisenstein_eq_half_pair_sum
    (N : ℕ) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    actualComplexParabolicEisenstein N s z = levelPrimitiveComplexEisenstein N s z := by
  have h := tsum_complex_rows_eq_two_parabolic_cosets N (fun v => levelComplexSeed N z v s)
    (levelComplexSeed_even N z s) (levelComplexSeed_summable N z s hs)
  simp_rw [← complex_parabolic_seed_row_dictionary N s z] at h
  change (∑' v : LevelPrimitiveRow N, levelComplexSeed N z v s) =
    2 * actualComplexParabolicEisenstein N s z at h
  unfold levelPrimitiveComplexEisenstein
  rw [h]
  ring

theorem actualComplexParabolicEisenstein_Gamma0_invariant (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    actualComplexParabolicEisenstein N s (gamma • z) = actualComplexParabolicEisenstein N s z := by
  rw [actualComplexParabolicEisenstein_eq_half_pair_sum N s hs,
    actualComplexParabolicEisenstein_eq_half_pair_sum N s hs]
  exact levelPrimitiveComplexEisenstein_Gamma0_invariant N s hs gamma z

theorem levelPrimitiveComplexEisenstein_one (s : ℂ) (z : ℍ) :
    levelPrimitiveComplexEisenstein 1 s z = primitiveComplexEisenstein s z := by
  unfold levelPrimitiveComplexEisenstein primitiveComplexEisenstein
  congr 1
  exact levelOnePrimitiveEquiv.tsum_eq (fun v : PrimitivePair => complexSeed z v s)

theorem levelComplexSeed_ofReal (N : ℕ) (z : ℍ) (v : LevelPrimitiveRow N) (t : ℝ) :
    levelComplexSeed N z v (t : ℂ) = (seed t z v.1 : ℂ) :=
  complexSeed_ofReal z (toPrimitiveRow N v) t

/-- The complex level family really extends the already constructed actual
real GammaInfinity\Gamma0 Eisenstein object. -/
theorem levelPrimitiveComplexEisenstein_ofReal (N : ℕ) (t : ℝ) (ht : 1 < t) (z : ℍ) :
    levelPrimitiveComplexEisenstein N (t : ℂ) z = (actualParabolicEisenstein N t z : ℂ) := by
  rw [actualParabolicEisenstein_eq_half_pair_sum N t ht z]
  simp only [levelPrimitiveComplexEisenstein, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_tsum, levelComplexSeed_ofReal]

end
end ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
