import ImbalancedChen.Part3CharacterMiddlePrimitiveRows

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The unique primitive zero-first-coordinate pair up to sign is explicitly
(0,+1)/(0,-1). Both transported ORIGINAL character weights equal chi(-a).
Their finite half-sum is exactly p^s*chi(-a)*y^s in the actual affine
middle chart. This is a finite incoming candidate, NOT an asymptotic of
the infinite character Eisenstein series or a nonvanishing assertion. -/

noncomputable section
open Matrix Complex EisensteinSeries
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.CharacterEisensteinRowAction
open ImbalancedChen.Part3.CharacterEisensteinSeries
open ImbalancedChen.Part3.CharacterMiddleCuspGeometry20261026b
open ImbalancedChen.Part3.CharacterMiddlePrimitiveRows20261026b

namespace ImbalancedChen.Part3.CharacterMiddleZeroFirstPairs20261026b

def zeroFirstPlus : PrimitivePair :=
  ⟨![0, 1], by rw [EisensteinSeries.gammaSet_one_mem_iff]; simp⟩

def zeroFirstMinus : PrimitivePair :=
  ⟨![0, -1], by rw [EisensteinSeries.gammaSet_one_mem_iff]; simp⟩

/-- Actual gcd primitivity isolates the two oriented rows. -/
theorem primitive_zero_first_iff (w : PrimitivePair) :
    w.1 0 = 0 ↔ w = zeroFirstPlus ∨ w = zeroFirstMinus := by
  constructor
  · intro h0
    have hcop := (EisensteinSeries.mem_gammaSet_one w.1).mp w.property
    have h1 : w.1 1 = 1 ∨ w.1 1 = -1 := by
      simpa only [h0, isCoprime_zero_left, Int.isUnit_iff] using hcop
    rcases h1 with h1 | h1
    · left
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [zeroFirstPlus, h0, h1]
    · right
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [zeroFirstMinus, h0, h1]
  · rintro (rfl | rfl) <;> rfl

theorem middleTransportWeight_zeroFirstPlus {q : ℕ}
    (chi : DirichletCharacter ℂ q) (a : ℤ) :
    middleTransportWeight chi a zeroFirstPlus = chi (-a : ZMod q) := by
  simp only [middleTransportWeight, characterWeight, zeroFirstPlus,
    Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg, mul_one, zero_add]
  rw [← map_mul]
  congr 1
  push_cast
  ring

theorem middleTransportWeight_zeroFirstMinus {q : ℕ}
    (chi : DirichletCharacter ℂ q) (a : ℤ) :
    middleTransportWeight chi a zeroFirstMinus = chi (-a : ZMod q) := by
  simp [middleTransportWeight, characterWeight, zeroFirstMinus]

theorem middle_zero_first_weight {q : ℕ} (chi : DirichletCharacter ℂ q)
    (a : ℤ) (w : PrimitivePair) (hw : w.1 0 = 0) :
    middleTransportWeight chi a w = chi (-a : ZMod q) := by
  rcases (primitive_zero_first_iff w).mp hw with rfl | rfl
  · exact middleTransportWeight_zeroFirstPlus chi a
  · exact middleTransportWeight_zeroFirstMinus chi a

/-- The original primitive rows producing m=0 are precisely (-1,a)
and (1,-a), obtained from the proved inverse bijection. -/
theorem middle_zero_first_original_rows (a : ℤ) (v : PrimitivePair) :
    (middleRowEquiv a v).1 0 = 0 ↔
      v = (middleRowEquiv a).symm zeroFirstPlus ∨
      v = (middleRowEquiv a).symm zeroFirstMinus := by
  rw [primitive_zero_first_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((Equiv.eq_symm_apply (middleRowEquiv a)).mpr h)
    · exact Or.inr ((Equiv.eq_symm_apply (middleRowEquiv a)).mpr h)
  · rintro (rfl | rfl) <;> simp only [Equiv.apply_symm_apply, or_true, true_or]

theorem positiveBase_zeroFirstPlus (z : UpperHalfPlane) :
    positiveBase z zeroFirstPlus = z.im := by simp [positiveBase, zeroFirstPlus]

theorem positiveBase_zeroFirstMinus (z : UpperHalfPlane) :
    positiveBase z zeroFirstMinus = z.im := by simp [positiveBase, zeroFirstMinus]

/-- Finite two-row contribution, with the ORIGINAL 1/2 normalization. -/
theorem finite_zero_first_half_sum {q : ℕ} (chi : DirichletCharacter ℂ q)
    (a : ℤ) (z : UpperHalfPlane) (s : ℂ) :
    (1 / 2 : ℂ) *
      (middleTransportWeight chi a zeroFirstPlus * complexSeed z zeroFirstPlus s +
        middleTransportWeight chi a zeroFirstMinus * complexSeed z zeroFirstMinus s) =
      chi (-a : ZMod q) * Complex.exp (s * (Real.log z.im : ℂ)) := by
  rw [middleTransportWeight_zeroFirstPlus, middleTransportWeight_zeroFirstMinus,
    complexSeed, complexSeed, positiveBase_zeroFirstPlus, positiveBase_zeroFirstMinus]
  ring

/-- Positive real p fixes the principal branch. This proves the exact
candidate incoming factor p^s*chi(-a) at the actual width-one middle cusp,
without identifying it with an infinite-series constant term. -/
theorem finite_middle_incoming_factor (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ)) (z : UpperHalfPlane) (s : ℂ) :
    (1 / 2 : ℂ) *
      (middleTransportWeight chi (sigma 0 0) zeroFirstPlus *
          complexSeed (middleAffinePoint p hp sigma z) zeroFirstPlus s +
        middleTransportWeight chi (sigma 0 0) zeroFirstMinus *
          complexSeed (middleAffinePoint p hp sigma z) zeroFirstMinus s) =
      ((p : ℂ) ^ s * chi (-(sigma 0 0) : ZMod p)) *
        Complex.exp (s * (Real.log z.im : ℂ)) := by
  rw [finite_zero_first_half_sum, middleAffinePoint_im]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hpow : (p : ℂ) ^ s = Complex.exp (s * (Real.log (p : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hpR.le]
    congr 1
    ring
  rw [Real.log_mul hpR.ne' z.im_pos.ne', Complex.ofReal_add, mul_add,
    Complex.exp_add, ← hpow]
  ring

/-- The finite candidate is formed from the ORIGINAL actual character
series summands at sigma*z, via the constructed inverse row bijection. -/
theorem original_middle_zero_rows_half_sum (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) (s : ℂ) :
    (1 / 2 : ℂ) *
      (characterSeed hp chi (sigma • z)
          ((middleRowEquiv (sigma 0 0)).symm zeroFirstPlus) s +
        characterSeed hp chi (sigma • z)
          ((middleRowEquiv (sigma 0 0)).symm zeroFirstMinus) s) =
      ((p : ℂ) ^ s * chi (-(sigma 0 0) : ZMod p)) *
        Complex.exp (s * (Real.log z.im : ℂ)) := by
  rw [characterSeed_middle_transport p hp chi sigma hc,
    characterSeed_middle_transport p hp chi sigma hc,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact finite_middle_incoming_factor p hp chi sigma z s

end ImbalancedChen.Part3.CharacterMiddleZeroFirstPairs20261026b
