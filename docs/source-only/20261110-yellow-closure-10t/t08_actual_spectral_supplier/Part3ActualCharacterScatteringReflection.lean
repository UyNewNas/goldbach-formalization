import ImbalancedChen.Part3ActualCriticalScatteringReciprocity
import ImbalancedChen.Part3ActualCharacterOriginalCuspFourier
import ImbalancedChen.Part3ActualGreenResolventJump
import ImbalancedChen.Part3PrimeCompletedChannelReflection

/-! Functional equation of the actual Young characters and their complete
ordinary dilations, with the conductor-one completed reflection supplied
by the original R22 field. -/
namespace ImbalancedChen.Part3.ActualCharacterScatteringReflection20261110

noncomputable section
open Set Filter Complex UpperHalfPlane
open scoped BigOperators UpperHalfPlane MatrixGroups
open ComplexOrderKBridgeSourceOnly ActualGreenResolventJumpSourceOnly
open ActualCharacterCompletedFourier20261110 ActualCharacterCriticalFamily20261110
open ActualCharacterOriginalCuspFourier20261110 ActualCharacterPoissonRows20261110
open CharacterPairDivisorAmplitude20261102s ActualYoungCriticalD20261110
open ActualCriticalCuspEvaluation20261110 PrimeCompletedChannelReflection20261026b
open CompletedActualEisensteinIdentity20261025a

private theorem pair_reflection {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) (s : ℂ) :
    pairAmplitude χ⁻¹ χ⁻¹ n (1-s) = pairAmplitude χ χ n s := by
  classical
  rw [pairAmplitude_eq_divisor_pairs,pairAmplitude_eq_divisor_pairs]
  conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro ab _
  simp only [Function.Embedding.coeFn_mk,Equiv.coe_toEmbedding,Equiv.prodComm_apply,
    Prod.snd_swap,Prod.fst_swap,MulChar.star_apply',inv_inv]
  rw [show (1/2 : ℂ)-(1-s) = s-1/2 by ring,show (1-s)-1/2 = 1/2-s by ring]
  ring

private theorem parity_inverse {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ⁻¹ (-1 : ZMod q) = χ (-1) := by
  rw [← MulChar.star_apply']
  rcases χ.even_or_odd with h | h
  · change χ (-1) = 1 at h
    simp [h]
  · change χ (-1) = -1 at h
    simp [h]

theorem signed_amplitude_reflection {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) (s : ℂ) :
    amplitude χ⁻¹ n (1-s) = amplitude χ n s := by
  cases n with
  | ofNat n => simp only [amplitude_nat,pair_reflection]
  | negSucc n =>
    change amplitude χ⁻¹ (-((n+1 : ℕ) : ℤ)) (1-s) = amplitude χ (-((n+1 : ℕ) : ℤ)) s
    simp only [amplitude_neg_nat,parity_inverse,pair_reflection]

/-- Reflection of the entire genuinely reconstructed nonprincipal
completed family, with the actual signed divisor coefficients and K
kernel. At conductor one the native completed function is treated
separately below because it carries its two constant terms. -/
theorem completed_character_reflection {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (z : ℍ) :
    completedFamily χ⁻¹ (1-s) z = completedFamily χ s z := by
  unfold completedFamily
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [continuedCoefficient,hn]
  · simp only [continuedCoefficient,if_neg hn,signed_amplitude_reflection,
      show 1-s-1/2 = -(s-1/2) by ring,complexOrderK_neg_order]

def completedPart {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (z : ℍ) : ℂ :=
  if q = 1 then completedActualEisenstein s z else completedFamily χ s z

def ordinaryScale {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  if q = 1 then (Real.pi : ℂ)^s/Complex.Gamma s*
    reciprocalL (1 : DirichletCharacter ℂ 1) (2*s) else uncompletionFactor χ s

theorem ordinary_factors {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (z : ℍ) :
    ordinary χ s z = ordinaryScale χ s*completedPart χ s z := by
  by_cases h : q = 1 <;> simp [ordinary,ordinaryScale,completedPart,h,principalOrdinary,primitiveFamily]

private theorem reflected_part {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (h0 : s ≠ 0)
    (h1 : s ≠ 1) (z : ℍ) : completedPart χ⁻¹ (1-s) z = completedPart χ s z := by
  by_cases h : q = 1
  · simpa only [completedPart,if_pos h] using completedActual_reflection s h0 h1 z
  · simpa only [completedPart,if_neg h] using completed_character_reflection χ s z

theorem inverse_primitive {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  change (χ⁻¹).conductor = q
  rw [DirichletCharacter.conductor_inv]
  exact hχ

private theorem reciprocal_nonzero {q : ℕ} [NeZero q] (η : DirichletCharacter ℂ q)
    (u : ℂ) (hre : 1 ≤ u.re) (hu : u ≠ 1) : reciprocalL η u ≠ 0 := by
  have hL := DirichletCharacter.LFunction_ne_zero_of_one_le_re η (.inr hu) hre
  by_cases e : η = 1
  · subst η
    rw [reciprocalL,if_pos rfl,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hu]
    exact div_ne_zero (sub_ne_zero.mpr hu) (mul_ne_zero (sub_ne_zero.mpr hu) hL)
  · simpa only [reciprocalL,if_neg e] using inv_ne_zero hL

theorem scale_nonzero_off_center {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {t : ℝ} (ht : t ≠ 0) : ordinaryScale χ (criticalPoint t) ≠ 0 := by
  let s := criticalPoint t
  have hs : s.re = 1/2 := by norm_num [s,criticalPoint,Complex.mul_re]
  have h₂ : 1 ≤ (2*s).re := by simp [Complex.mul_re,hs]
  have ht₂ : 2*s ≠ 1 := by
    intro e
    have E := congrArg Complex.im e
    have hi : s.im = t := by simp [s,criticalPoint,Complex.mul_im]
    simp [Complex.mul_im,hi] at E
    exact ht (by linarith)
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hp : (Real.pi : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  by_cases e : q = 1
  · simpa only [ordinaryScale,if_pos e,s] using
      mul_ne_zero (div_ne_zero hp hΓ) (reciprocal_nonzero (1 : DirichletCharacter ℂ 1) (2*s) h₂ ht₂)
  · have hq : (q : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
    simpa only [ordinaryScale,if_neg e,uncompletionFactor,s] using
      mul_ne_zero (div_ne_zero (mul_ne_zero (div_ne_zero hp hq) (gauss_ne_zero hχ)) hΓ)
        (reciprocal_nonzero (χ^2) (2*s) h₂ ht₂)

/-- The scalar is fixed for every point and every oldform dilation in the
primitive character block. Its denominator is licensed at t ≠ 0 from the
actual Γ, Gauss and L factors. -/
theorem ordinary_critical_reflection {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {t : ℝ} (ht : t ≠ 0) (z : ℍ) :
    ordinary χ (criticalPoint t) z =
      (ordinaryScale χ (criticalPoint t)/ordinaryScale χ⁻¹ (criticalPoint (-t)))*
        ordinary χ⁻¹ (criticalPoint (-t)) z := by
  let s := criticalPoint t
  have h0 : s ≠ 0 := by
    intro e
    have H := congrArg Complex.re e
    norm_num [s,criticalPoint,Complex.mul_re] at H
  have h1 : s ≠ 1 := by
    intro e
    have H := congrArg Complex.re e
    norm_num [s,criticalPoint,Complex.mul_re] at H
  have hs : criticalPoint (-t) = 1-s := by dsimp [s,criticalPoint]; push_cast; ring
  have hr : completedPart χ⁻¹ (criticalPoint (-t)) z = completedPart χ s z := by
    rw [hs,reflected_part χ s h0 h1]
  have hnon := scale_nonzero_off_center χ⁻¹ (inverse_primitive χ hχ) (neg_ne_zero.mpr ht)
  rw [ordinary_factors,ordinary_factors,hr]
  dsimp only [s]
  field_simp [hnon]

end
end ImbalancedChen.Part3.ActualCharacterScatteringReflection20261110
