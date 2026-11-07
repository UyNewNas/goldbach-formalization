import ImbalancedChen.Part3CoprimeCRTUnitResidues
import Mathlib.Data.Int.GCD

/-!
Source-only, 2026-10-25. UNCOMPILED / NOT_ROOT_ACCEPTED.

The standard additive character and the literal physical Kloosterman sum
factor over coprime moduli with both frequencies twisted by the respective
local inverse of the other modulus. The twists are the explicit extended
Euclidean coefficients `Nat.gcdB q r` on q and `Nat.gcdA q r` on r.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

open scoped BigOperators SchwartzMap FourierTransform

/-- The positive phase of the original physical sum. -/
def crtPhase (q : ℕ) (A : ℤ) : ℂ :=
  fourier 1 ((((A : ℝ) / (q : ℝ)) : ℝ) : UnitAddCircle)

private theorem fourier_add (x y : UnitAddCircle) :
    fourier 1 (x + y) = fourier 1 x * fourier 1 y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

private theorem crtPhase_eq_stdAddChar (q : ℕ) [NeZero q] (A : ℤ) :
    crtPhase q A = ZMod.stdAddChar (A : ZMod q) := by
  unfold crtPhase
  rw [ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- The exact rational phase decomposition with genuine integer Bezout
coefficients. -/
theorem crtPhase_bezout (q r : ℕ) [NeZero q] [NeZero r]
    (s t A : ℤ) (hbez : s * (q : ℤ) + t * (r : ℤ) = 1) :
    crtPhase (q * r) A = crtPhase q (t * A) * crtPhase r (s * A) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne r)
  have hbezR : (s : ℝ) * (q : ℝ) + (t : ℝ) * (r : ℝ) = 1 := by
    exact_mod_cast hbez
  have hfrac : (A : ℝ) / ((q * r : ℕ) : ℝ) =
      ((t * A : ℤ) : ℝ) / (q : ℝ) +
        ((s * A : ℤ) : ℝ) / (r : ℝ) := by
    have hnum : (A : ℝ) =
        ((t : ℝ) * (A : ℝ)) * (r : ℝ) +
          ((s : ℝ) * (A : ℝ)) * (q : ℝ) := by
      calc
        (A : ℝ) = (A : ℝ) * 1 := by ring
        _ = (A : ℝ) * ((s : ℝ) * (q : ℝ) + (t : ℝ) * (r : ℝ)) := by
          rw [hbezR]
        _ = _ := by ring
    push_cast
    field_simp [hq0, hr0]
    nlinarith [hnum]
  unfold crtPhase
  rw [hfrac, AddCircle.coe_add, fourier_add]

/-- CRT factorization of the actual standard additive character on an
integer residue. -/
theorem stdAddChar_int_bezout (q r : ℕ) [NeZero q] [NeZero r]
    (s t A : ℤ) (hbez : s * (q : ℤ) + t * (r : ℤ) = 1) :
    ZMod.stdAddChar (A : ZMod (q * r)) =
      ZMod.stdAddChar ((t * A : ℤ) : ZMod q) *
        ZMod.stdAddChar ((s * A : ℤ) : ZMod r) := by
  simpa only [crtPhase_eq_stdAddChar] using crtPhase_bezout q r s t A hbez

/-- Pointwise Kloosterman phase factorization. The inverse congruences
are derived from the actual unit gate, using the preceding module. -/
theorem kloostermanPhase_int_bezout (q r : ℕ) [NeZero q] [NeZero r]
    (s t m n u : ℤ) (hbez : s * (q : ℤ) + t * (r : ℤ) = 1)
    (hu : IsUnit (u : ZMod (q * r))) :
    ZMod.stdAddChar ((m : ZMod (q * r)) * (u : ZMod (q * r)) +
      (n : ZMod (q * r)) * (u : ZMod (q * r))⁻¹) =
      ZMod.stdAddChar (((t * m : ℤ) : ZMod q) * (u : ZMod q) +
        ((t * n : ℤ) : ZMod q) * (u : ZMod q)⁻¹) *
      ZMod.stdAddChar (((s * m : ℤ) : ZMod r) * (u : ZMod r) +
        ((s * n : ℤ) : ZMod r) * (u : ZMod r)⁻¹) := by
  have hc : (inverseResidue (q * r) u : ZMod (q * r)) =
      (u : ZMod (q * r))⁻¹ := by
    simp only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hq : ((t * (m * u + n * inverseResidue (q * r) u) : ℤ) : ZMod q) =
      ((t * m : ℤ) : ZMod q) * (u : ZMod q) +
        ((t * n : ℤ) : ZMod q) * (u : ZMod q)⁻¹ := by
    simp only [Int.cast_mul, Int.cast_add,
      inverseResidue_cast_of_dvd (dvd_mul_right q r) u hu]
    ring
  have hr : ((s * (m * u + n * inverseResidue (q * r) u) : ℤ) : ZMod r) =
      ((s * m : ℤ) : ZMod r) * (u : ZMod r) +
        ((s * n : ℤ) : ZMod r) * (u : ZMod r)⁻¹ := by
    simp only [Int.cast_mul, Int.cast_add,
      inverseResidue_cast_of_dvd (dvd_mul_left r q) u hu]
    ring
  have hphase := stdAddChar_int_bezout q r s t
    (m * u + n * inverseResidue (q * r) u) hbez
  rw [hq, hr] at hphase
  simpa only [Int.cast_add, Int.cast_mul, hc] using hphase

/-- The explicit extended Euclidean coefficients have the required
normalization when the moduli are coprime. -/
theorem canonical_crt_bezout {q r : ℕ} (h : q.Coprime r) :
    Nat.gcdA q r * (q : ℤ) + Nat.gcdB q r * (r : ℤ) = 1 := by
  have hab := (Nat.gcd_eq_gcd_ab q r).symm
  simpa only [h.gcd_eq_one, Nat.cast_one, mul_comm] using hab

/-- The q twist is the inverse of r modulo q. -/
theorem canonical_crt_twist_left {q r : ℕ} (h : q.Coprime r) :
    (Nat.gcdB q r : ZMod q) * (r : ZMod q) = 1 := by
  have hab := congrArg (fun z : ℤ => (z : ZMod q)) (canonical_crt_bezout h)
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, mul_zero, zero_add, Int.cast_one] using hab

/-- The r twist is the inverse of q modulo r. -/
theorem canonical_crt_twist_right {q r : ℕ} (h : q.Coprime r) :
    (Nat.gcdA q r : ZMod r) * (q : ZMod r) = 1 := by
  have hab := congrArg (fun z : ℤ => (z : ZMod r)) (canonical_crt_bezout h)
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, mul_zero, add_zero, Int.cast_one] using hab

/-- The actual phase factors in the exact CRT coordinates of a unit
residue, with the canonical inverse twists on both frequencies. -/
theorem kloostermanPhase_crt {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (m n : ℤ) (u : ZMod (q * r)) (hu : IsUnit u) :
    ZMod.stdAddChar ((m : ZMod (q * r)) * u + (n : ZMod (q * r)) * u⁻¹) =
      ZMod.stdAddChar
        (((Nat.gcdB q r * m : ℤ) : ZMod q) * (ZMod.chineseRemainder h u).1 +
         ((Nat.gcdB q r * n : ℤ) : ZMod q) * (ZMod.chineseRemainder h u).1⁻¹) *
      ZMod.stdAddChar
        (((Nat.gcdA q r * m : ℤ) : ZMod r) * (ZMod.chineseRemainder h u).2 +
         ((Nat.gcdA q r * n : ℤ) : ZMod r) * (ZMod.chineseRemainder h u).2⁻¹) := by
  have huval : IsUnit ((u.val : ℤ) : ZMod (q * r)) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hu
  have hcoords : ZMod.chineseRemainder h u =
      ((u.val : ZMod q), (u.val : ZMod r)) := by
    calc
      _ = ZMod.chineseRemainder h (u.val : ZMod (q * r)) :=
        congrArg (ZMod.chineseRemainder h) (ZMod.natCast_zmod_val u).symm
      _ = _ := map_natCast (ZMod.chineseRemainder h) u.val
  have hq : (u.val : ZMod q) = (ZMod.chineseRemainder h u).1 :=
    (congrArg Prod.fst hcoords).symm
  have hr : (u.val : ZMod r) = (ZMod.chineseRemainder h u).2 :=
    (congrArg Prod.snd hcoords).symm
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, hq, hr] using
    kloostermanPhase_int_bezout q r (Nat.gcdA q r) (Nat.gcdB q r)
      m n (u.val : ℤ) (canonical_crt_bezout h) huval

/-- The original range-defined Kloosterman sum written over its actual
admissible residues. -/
theorem kloosterman_eq_unitResidueSum (c : ℕ) [NeZero c] (m n : ℤ) :
    kloosterman c m n = ∑ u : UnitResidue c,
      ZMod.stdAddChar ((m : ZMod c) * u.1 + (n : ZMod c) * u.1⁻¹) := by
  rw [Physical.kloosterman_eq_zmod]
  let f : ZMod c → ℂ := fun u =>
    ZMod.stdAddChar ((m : ZMod c) * u + (n : ZMod c) * u⁻¹)
  have hsum : (∑ u : UnitResidue c, f u.1) =
      ∑ u ∈ (Finset.univ : Finset (ZMod c)).filter IsUnit, f u := by
    apply Finset.sum_bij (fun u _ => u.1)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩
    · intro u hu v hv huv
      exact Subtype.ext huv
    · intro u hu
      exact ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩
    · intro u hu
      rfl
  simpa only [Finset.sum_filter, f] using hsum.symm

/-- Coprime multiplicativity of the literal physical Kloosterman sum,
including the necessary inverse twists on both local frequencies. -/
theorem kloosterman_coprime_crt {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (m n : ℤ) :
    kloosterman (q * r) m n =
      kloosterman q (Nat.gcdB q r * m) (Nat.gcdB q r * n) *
        kloosterman r (Nat.gcdA q r * m) (Nat.gcdA q r * n) := by
  rw [kloosterman_eq_unitResidueSum, kloosterman_eq_unitResidueSum,
    kloosterman_eq_unitResidueSum]
  calc
    _ = ∑ u : UnitResidue (q * r),
      ZMod.stdAddChar
        (((Nat.gcdB q r * m : ℤ) : ZMod q) * (ZMod.chineseRemainder h u.1).1 +
         ((Nat.gcdB q r * n : ℤ) : ZMod q) * (ZMod.chineseRemainder h u.1).1⁻¹) *
      ZMod.stdAddChar
        (((Nat.gcdA q r * m : ℤ) : ZMod r) * (ZMod.chineseRemainder h u.1).2 +
         ((Nat.gcdA q r * n : ℤ) : ZMod r) * (ZMod.chineseRemainder h u.1).2⁻¹) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact kloostermanPhase_crt h m n u.1 u.2
    _ = _ := sum_crt_separated h
      (fun x => ZMod.stdAddChar
        (((Nat.gcdB q r * m : ℤ) : ZMod q) * x +
         ((Nat.gcdB q r * n : ℤ) : ZMod q) * x⁻¹))
      (fun y => ZMod.stdAddChar
        (((Nat.gcdA q r * m : ℤ) : ZMod r) * y +
         ((Nat.gcdA q r * n : ℤ) : ZMod r) * y⁻¹))

end ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly
