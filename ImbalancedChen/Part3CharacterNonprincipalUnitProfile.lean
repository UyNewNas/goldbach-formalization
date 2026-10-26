import ImbalancedChen.Part3CharacterEisensteinActualNonvanishing

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Nonprincipal ACTUAL Dirichlet characters have a unit with value !=1,
by the pinned multiplicative-character unit restriction theorem. Literal
integer lifts and Bezout build native middle matrices realizing that
profile, rather than assuming an abstract nonconstant incoming vector.
No spectral decomposition or cusp-basis theorem is an input. -/

noncomputable section
open Matrix Complex
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.CharacterMiddleSeriesAsymptotic20261026b
open ImbalancedChen.Part3.CharacterEisensteinActualNonvanishing20261026b

namespace ImbalancedChen.Part3.CharacterNonprincipalUnitProfile20261026b

/-- Actual nonprincipality is tested on actual units, paying the
nonunit-zero behavior through the native MulChar extensionality theorem. -/
theorem nonprincipal_exists_unit {p : ℕ} (chi : DirichletCharacter ℂ p)
    (hchi : chi ≠ 1) : ∃ u : (ZMod p)ˣ, chi (u : ZMod p) ≠ 1 :=
  MulChar.ne_one_iff.mp hchi

/-- Every unit label is realized by an actual determinant-one integral
middle matrix. The sign is chosen so the incoming character is chi(u). -/
theorem exists_middle_matrix_unit_label (p : ℕ) (u : (ZMod p)ˣ) :
    ∃ sigma : SL(2, ℤ), sigma 1 0 = (p : ℤ) ∧
      (-(sigma 0 0) : ZMod p) = (u : ZMod p) := by
  let a : ℤ := -(ZMod.cast (u : ZMod p) : ℤ)
  have ha : (a : ZMod p) = -(u : ZMod p) := by
    simp only [a, Int.cast_neg, ZMod.intCast_zmod_cast]
  have hau : IsUnit (a : ZMod p) := by
    rw [ha]
    exact u.isUnit.neg
  have hcop : IsCoprime a (p : ℤ) :=
    ((ZMod.coe_int_isUnit_iff_isCoprime a p).mp hau).symm
  obtain ⟨r, t, hrt⟩ := hcop
  let sigma : SL(2, ℤ) := ⟨!![a, -t; (p : ℤ), r], by
    rw [Matrix.det_fin_two_of]
    linear_combination hrt⟩
  refine ⟨sigma, by simp [sigma], ?_⟩
  change (-(a) : ZMod p) = (u : ZMod p)
  simp only [Int.cast_neg, ha, neg_neg]

/-- Both comparison cusps and the unequal character values are produced
from chi!=principal. Nonconstancy is a conclusion, not a hypothesis. -/
theorem exists_native_middle_profile_variation {p : ℕ}
    (chi : DirichletCharacter ℂ p) (hchi : chi ≠ 1) :
    ∃ sigma0 sigma1 : SL(2, ℤ),
      sigma0 1 0 = (p : ℤ) ∧ sigma1 1 0 = (p : ℤ) ∧
      chi (-(sigma0 0 0) : ZMod p) = 1 ∧
      chi (-(sigma1 0 0) : ZMod p) ≠ 1 := by
  obtain ⟨u, hu⟩ := nonprincipal_exists_unit chi hchi
  obtain ⟨sigma0, hc0, ha0⟩ := exists_middle_matrix_unit_label p 1
  obtain ⟨sigma1, hc1, ha1⟩ := exists_middle_matrix_unit_label p u
  refine ⟨sigma0, sigma1, hc0, hc1, ?_, ?_⟩
  · rw [ha0]
    simp
  · simpa only [ha1] using hu

/-- Therefore the ACTUAL proved middle incoming coefficient varies
among native unit-labelled middle matrices, for every real s. -/
theorem exists_native_middle_incoming_ne (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (hchi : chi ≠ 1) (s : ℝ) :
    ∃ sigma0 sigma1 : SL(2, ℤ),
      sigma0 1 0 = (p : ℤ) ∧ sigma1 1 0 = (p : ℤ) ∧
      middleIncoming chi (sigma0 0 0) s ≠ middleIncoming chi (sigma1 0 0) s := by
  obtain ⟨sigma0, sigma1, hc0, hc1, hv0, hv1⟩ :=
    exists_native_middle_profile_variation chi hchi
  refine ⟨sigma0, sigma1, hc0, hc1, ?_⟩
  have hpow : ((p : ℝ)^s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (by exact_mod_cast hp : 0 < (p : ℝ)) s).ne'
  intro he
  have hcancel := congrArg (fun t : ℂ => (((p : ℝ)^s : ℂ))⁻¹*t) he
  have hvalues : chi (-(sigma0 0 0) : ZMod p) =
      chi (-(sigma1 0 0) : ZMod p) := by
    simpa only [middleIncoming, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul] using hcancel
  exact hv1 (hvalues.symm.trans hv0)

/-- Explicit prime-two edge for this nonprincipal lease: it is excluded
by actual character theory, not by a tacit assumption p is odd. -/
theorem nonprincipal_prime_gt_two (p : ℕ) (hp : p.Prime)
    (chi : DirichletCharacter ℂ p) (hchi : chi ≠ 1) : 2 < p := by
  have htwo : p ≠ 2 := by
    intro h
    subst p
    exact no_nontrivial_character_modulus_two chi hchi
  have hp2 := hp.two_le
  omega

end ImbalancedChen.Part3.CharacterNonprincipalUnitProfile20261026b

