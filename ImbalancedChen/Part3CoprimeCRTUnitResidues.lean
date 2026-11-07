import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson

/-!
Source-only, 2026-10-25. UNCOMPILED / NOT_ROOT_ACCEPTED.

Coprime CRT on the actual unit residue sets, with reduction of the actual
integer inverse representatives along every divisor of the modulus.
No phase factorization, cancellation estimate, or spectral input is assumed.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

open scoped BigOperators

/-- The exact unit gate appearing in the ZMod form of `kloosterman`. -/
abbrev UnitResidue (c : ℕ) := {u : ZMod c // IsUnit u}

/-- CRT carries the product-modulus gate to both local gates. -/
theorem crt_unit_gate {q r : ℕ} (h : q.Coprime r) (u : ZMod (q * r)) :
    IsUnit u ↔
      IsUnit ((ZMod.chineseRemainder h u).1) ∧
        IsUnit ((ZMod.chineseRemainder h u).2) := by
  exact (MulEquiv.isUnit_map (ZMod.chineseRemainder h)).symm.trans Prod.isUnit_iff

/-- A genuine bijection of admissible residues, supplied by the pinned CRT
ring equivalence rather than a factorization hypothesis. -/
def unitResidueCRT {q r : ℕ} (h : q.Coprime r) :
    UnitResidue (q * r) ≃ UnitResidue q × UnitResidue r where
  toFun u :=
    (⟨(ZMod.chineseRemainder h u.1).1, ((crt_unit_gate h u.1).mp u.2).1⟩,
     ⟨(ZMod.chineseRemainder h u.1).2, ((crt_unit_gate h u.1).mp u.2).2⟩)
  invFun v :=
    ⟨(ZMod.chineseRemainder h).symm (v.1.1, v.2.1), by
      apply (crt_unit_gate h _).mpr
      simpa only [RingEquiv.apply_symm_apply] using And.intro v.1.2 v.2.2⟩
  left_inv u := by
    apply Subtype.ext
    exact (ZMod.chineseRemainder h).symm_apply_apply u.1
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((ZMod.chineseRemainder h).apply_symm_apply (v.1.1, v.2.1))
    · apply Subtype.ext
      exact congrArg Prod.snd ((ZMod.chineseRemainder h).apply_symm_apply (v.1.1, v.2.1))

/-- The finite CRT bijection gives the separated-weight product identity.
The weights are arbitrary local functions; their splitting is not assumed
for a Kloosterman phase. -/
theorem sum_crt_separated {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (f : ZMod q → ℂ) (g : ZMod r → ℂ) :
    (∑ u : UnitResidue (q * r),
      f (ZMod.chineseRemainder h u.1).1 *
        g (ZMod.chineseRemainder h u.1).2) =
      (∑ x : UnitResidue q, f x.1) * (∑ y : UnitResidue r, g y.1) := by
  calc
    _ = ∑ v : UnitResidue q × UnitResidue r, f v.1.1 * g v.2.1 := by
      exact Fintype.sum_equiv (unitResidueCRT h) _ _ (fun _ => rfl)
    _ = ∑ x : UnitResidue q, ∑ y : UnitResidue r, f x.1 * g y.1 := by
      rw [Fintype.sum_prod_type]
    _ = _ := (Fintype.sum_mul_sum (fun x : UnitResidue q => f x.1)
      (fun y : UnitResidue r => g y.1)).symm

/-- Reduction of the literal integer inverse representative along a
modulus divisor. Unit status is the primitive arithmetic input. -/
theorem inverseResidue_cast_of_dvd {d c : ℕ} [NeZero d] [NeZero c]
    (hdc : d ∣ c) (u : ℤ) (hu : IsUnit (u : ZMod c)) :
    (inverseResidue c u : ZMod d) = (u : ZMod d)⁻¹ := by
  let reduction : ZMod c →+* ZMod d := ZMod.castHom hdc (ZMod d)
  have hlocal : IsUnit (u : ZMod d) := by
    simpa only [map_intCast] using hu.map reduction
  have hprod : (u : ZMod c) * (inverseResidue c u : ZMod c) = 1 := by
    simpa only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]
      using ZMod.mul_inv_of_unit (u : ZMod c) hu
  have hprodlocal : (u : ZMod d) * (inverseResidue c u : ZMod d) = 1 := by
    simpa only [map_mul, map_intCast, map_one] using congrArg reduction hprod
  calc
    (inverseResidue c u : ZMod d) =
        ((u : ZMod d)⁻¹ * (u : ZMod d)) * (inverseResidue c u : ZMod d) := by
      rw [ZMod.inv_mul_of_unit (u : ZMod d) hlocal, one_mul]
    _ = (u : ZMod d)⁻¹ * ((u : ZMod d) * (inverseResidue c u : ZMod d)) := by
      rw [mul_assoc]
    _ = (u : ZMod d)⁻¹ := by rw [hprodlocal, mul_one]

/-- The missing inverse congruence of the earlier CRT adapter, proved from
unit status rather than carried as a premise. -/
theorem inverseResidue_modEq_of_dvd {d c : ℕ} [NeZero d] [NeZero c]
    (hdc : d ∣ c) (u : ℤ) (hu : IsUnit (u : ZMod c)) :
    Int.ModEq d (inverseResidue c u) (inverseResidue d u) := by
  apply (ZMod.intCast_eq_intCast_iff _ _ d).mp
  rw [inverseResidue_cast_of_dvd hdc u hu]
  simp only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Both local inverse congruences needed for the scaled physical phases. -/
theorem crt_inverseResidue_modEq {q r : ℕ} [NeZero q] [NeZero r]
    (u : ℤ) (hu : IsUnit (u : ZMod (q * r))) :
    Int.ModEq q (inverseResidue (q * r) u) (inverseResidue q u) ∧
      Int.ModEq r (inverseResidue (q * r) u) (inverseResidue r u) := by
  exact ⟨inverseResidue_modEq_of_dvd (dvd_mul_right q r) u hu,
    inverseResidue_modEq_of_dvd (dvd_mul_left r q) u hu⟩

end ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

