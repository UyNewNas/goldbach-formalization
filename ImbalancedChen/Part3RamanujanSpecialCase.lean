import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3CenteredFourier
import Mathlib.Data.Nat.Totient

/-!
# The zero-frequency Kloosterman sum as a Ramanujan sum

This module proves the exact finite unit-group identity for the two
one-zero-argument special cases of the physical Kloosterman sum. In
particular, inversion of units identifies `S(0,n;c)` with `S(n,0;c)`.
The value at `n=0` is Euler's totient. These identities are valid at
every positive modulus, including modulus one.

SOURCEONLY: this candidate has not been compiled or audited.
-/

noncomputable section

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

open Classical Finset ImbalancedChen.Part3
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3.CommonSmoothCutoff

/-- The ordinary Ramanujan sum in the positive-frequency convention of
`kloosterman`; at modulus zero its defining range is empty. -/
def ramanujan (c : ℕ) (n : ℤ) : ℂ := kloosterman c n 0

private theorem sum_unit_filter {c : ℕ} [NeZero c] (f : ZMod c → ℂ) :
    (∑ u : ZMod c, if IsUnit u then f u else 0) =
      ∑ v : (ZMod c)ˣ, f (v : ZMod c) := by
  calc
    _ = ∑ u : ZMod c, (if IsUnit u then (1 : ℂ) else 0) * f u := by
      apply sum_congr rfl
      intro u hu
      split_ifs <;> simp only [one_mul, zero_mul]
    _ = ∑ u : ZMod c,
        (∑ v : (ZMod c)ˣ, if u = (v : ZMod c) then (1 : ℂ) else 0) * f u := by
      simp_rw [sum_unitResidueIndicator]
    _ = ∑ v : (ZMod c)ˣ, ∑ u : ZMod c,
        (if u = (v : ZMod c) then (1 : ℂ) else 0) * f u := by
      simp only [Finset.sum_mul]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro v hv
      simp [ite_mul]

/-- The literal complete sum `S(n,0;c)` is the additive character sum
over the units of `ZMod c`. -/
theorem ramanujan_eq_units {c : ℕ} [NeZero c] (n : ℤ) :
    ramanujan c n = ∑ v : (ZMod c)ˣ,
      ZMod.stdAddChar ((n : ZMod c) * (v : ZMod c)) := by
  rw [ramanujan, kloosterman_eq_zmod]
  simp only [Int.cast_zero, zero_mul, add_zero]
  exact sum_unit_filter _

/-- Inversion permutes the complete unit group, so `S(0,n;c)` is the
same Ramanujan sum as `S(n,0;c)`. -/
theorem kloosterman_zero_eq_ramanujan {c : ℕ} [NeZero c] (n : ℤ) :
    kloosterman c 0 n = ramanujan c n := by
  rw [kloosterman_eq_zmod, ramanujan_eq_units]
  simp only [Int.cast_zero, zero_mul, zero_add]
  rw [sum_unit_filter]
  have hi : Function.Bijective (fun v : (ZMod c)ˣ ↦ v⁻¹) := by
    constructor
    · intro u v h
      have hh := congrArg (fun w : (ZMod c)ˣ ↦ w⁻¹) h
      simpa only [inv_inv] using hh
    · intro v
      exact ⟨v⁻¹, inv_inv v⟩
  apply Fintype.sum_bijective (fun v : (ZMod c)ˣ ↦ v⁻¹) hi
  intro v
  simp only [ZMod.inv_coe_unit]

/-- The literal zero Poisson frequency, with all physical parameters
still present, has the Ramanujan factor. -/
theorem frequency_zero_eq_ramanujan {c : ℕ} [NeZero c]
    (B : ℝ) (a y z : ℤ) :
    frequency B c a y z 0 =
      (B / (c : ℝ)) • (𝓕 dyadicCutoffSchwartz) 0 * ramanujan c (a * y) := by
  simp only [frequency, Int.cast_zero, mul_zero, zero_mul]
  rw [kloosterman_zero_eq_ramanujan]

/-- At the zero additive argument, every unit contributes one. -/
theorem ramanujan_at_zero {c : ℕ} [NeZero c] :
    ramanujan c 0 = (c.totient : ℂ) := by
  rw [ramanujan_eq_units]
  simp only [Int.cast_zero, zero_mul, AddChar.map_zero_eq_one,
    sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]

/-- The degenerate positive modulus is included in the unit identity. -/
theorem ramanujan_modulus_one (n : ℤ) : ramanujan 1 n = 1 := by
  rw [ramanujan_eq_units]
  have hn : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [hn, ZMod.card_units_eq_totient]

end ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
