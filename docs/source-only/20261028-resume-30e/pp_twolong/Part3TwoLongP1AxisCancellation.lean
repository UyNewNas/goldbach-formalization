import Mathlib
import ImbalancedChen.Part3RamanujanMultiplicativity
import ImbalancedChen.P0RamanujanMultiplicativeGcdBound
import ImbalancedChen.Part3TwoLongFixedMRectangularCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact cancellation of BOTH coordinate-frequency axes for the original
P1 Kloosterman-minus-exact-coprime-mean kernel. No P1 or P2 hypothesis.
-/
namespace ImbalancedChen.Part3.TwoLongP1AxisCancellation
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

/-- Literal P1 kernel, with exact 1/phi(q) coprime mean. -/
def centeredKernel (q : ℕ) (b j k : ℤ) : ℂ :=
  kloosterman q (b*j) k - ramanujan q j * ramanujan q k / (Nat.totient q : ℂ)

theorem totient_complex_ne_zero {q : ℕ} (hq : 0 < q) : (Nat.totient q : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.totient_pos.mpr hq).ne'

theorem centeredKernel_left_axis {q : ℕ} (hq : 0 < q) (b k : ℤ) :
    centeredKernel q b 0 k = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [centeredKernel,mul_zero,kloosterman_zero_eq_ramanujan,ramanujan_at_zero]
  field_simp [totient_complex_ne_zero hq]

theorem centeredKernel_right_axis {q : ℕ} (hq : 0 < q) (b j : ℤ)
    (hb : IsUnit (b : ZMod q)) : centeredKernel q b j 0 = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [centeredKernel,← ramanujan,ramanujan_unit_scaling j b hb,ramanujan_at_zero]
  field_simp [totient_complex_ne_zero hq]

/-- The actual inverse short-product residue is a unit whenever the
original a and fixed short m are primitive. -/
theorem actual_center_unit {q : ℕ} [NeZero q] (a m : ℤ)
    (ha : IsUnit (a : ZMod q)) (hm : IsUnit (m : ZMod q)) :
    IsUnit ((a*inverseResidue q m : ℤ) : ZMod q) := by
  have hi : IsUnit ((inverseResidue q m : ℤ) : ZMod q) := by
    simpa only [inverseResidue,Int.cast_natCast,ZMod.natCast_zmod_val] using hm.inv
  simpa only [Int.cast_mul] using ha.mul hi

/-- The q=1 core kernel vanishes at EVERY frequency pair, not just (0,0). -/
theorem centeredKernel_modulus_one (b j k : ℤ) : centeredKernel 1 b j k = 0 := by
  have hS (r s : ℤ) : kloosterman 1 r s = 1 := by
    simp [kloosterman,inverseResidue]
  simp [centeredKernel,hS,ramanujan_modulus_one]


/-- The original finite rectangular count and exact coprime mean agree
at q=1 directly, independently of the as-yet unassembled P1 identity. -/
theorem fixedMCore_modulus_one (I J : Finset ℕ) (m a : ℕ) (alpha : ℂ)
    (f g : ℝ → ℂ) (U V : ℝ) :
    ImbalancedChen.Part3.TwoLongFixedMRectangularCore.fixedMCore
      I J m a 1 alpha f g U V = 0 := by
  rw [ImbalancedChen.Part3.TwoLongFixedMRectangularCore.fixedMCore_exact]
  simp

/-- Pointwise deletion of the two complete axes, including their nonzero
Fourier masses; every retained coefficient remains literal. -/
theorem centeredKernel_eq_nonzero {q : ℕ} (hq : 0 < q) (b j k : ℤ)
    (hb : IsUnit (b : ZMod q)) :
    centeredKernel q b j k = if j=0 ∨ k=0 then 0 else centeredKernel q b j k := by
  by_cases hj : j=0
  · subst j
    simp [centeredKernel_left_axis hq]
  by_cases hk : k=0
  · subst k
    simp [centeredKernel_right_axis hq b j hb]
  simp [hj,hk]

theorem double_series_remove_axes {q : ℕ} (hq : 0 < q) (b : ℤ)
    (hb : IsUnit (b : ZMod q)) (F G : ℤ → ℂ) :
    (∑' j : ℤ, ∑' k : ℤ, F j * G k * centeredKernel q b j k) =
      ∑' j : ℤ, ∑' k : ℤ,
        if j=0 ∨ k=0 then 0 else F j * G k * centeredKernel q b j k := by
  apply tsum_congr
  intro j
  apply tsum_congr
  intro k
  rw [centeredKernel_eq_nonzero hq b j k hb]
  split_ifs <;> simp

end
end ImbalancedChen.Part3.TwoLongP1AxisCancellation
