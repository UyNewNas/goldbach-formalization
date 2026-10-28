import ImbalancedChen.Part3ActualFilteredPrincipalCharacterVariance
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal filtered principal variance in distribution-medium-completion-
20261010.txt, section 5, equations (13)--(14). If ell=f*k, its actual
imprimitive coefficient has auxiliary gate r*k, not r*ell. This distinction
is necessary before the small-conductor SW sum in (14). The public theorem
below derives that coefficient bound from the original UniformAuxiliarySW.
It does not postulate filtered BDH, a medium return, or the final theorem.

The imported previous source-only file must first be installed under the
module name shown above; its exact source hash is recorded in REGISTRY.json.
-/

namespace ImbalancedChen.Part3.ActualFilteredPrimitiveSWSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators
open TransposedZeroCovariance SharedFirstFactorCharacterDictionary
open ActualFilteredPrincipalCharacterVarianceSourceOnly

/-- The exact character coefficient occurring in the paper's variance. -/
def filteredCharacterSum (d : MediumAtom) (r ell : ℕ)
    (chi : DirichletCharacter ℂ ell) : ℂ :=
  ∑ n ∈ d.alphaCarrier,
    if n.Coprime r then d.alpha n * star (chi (n : ZMod ell)) else 0

/-- The conductor quotient is absorbed into the auxiliary sieve. There is
no coprimality assumption between the conductor, quotient and r. -/
theorem filteredCharacterSum_eq_primitive_quotient
    (d : MediumAtom) {ell : ℕ} (hell : 0 < ell) (r : ℕ)
    (chi : DirichletCharacter ℂ ell) :
    filteredCharacterSum d r ell chi =
      auxiliaryCharacterSum d.alphaCarrier d.alpha
        (r * (ell / chi.conductor)) chi.conductor chi.primitiveCharacter := by
  unfold filteredCharacterSum auxiliaryCharacterSum
  apply Finset.sum_congr rfl
  intro n _
  rw [character_eq_primitive_quotient hell chi n]
  by_cases hnr : n.Coprime r
  · by_cases hnk : n.Coprime (ell / chi.conductor)
    · rw [if_pos hnr, if_pos hnk, if_pos (hnr.mul_right hnk)]
      simp
    · have hnK : ¬n.Coprime (r * (ell / chi.conductor)) :=
        fun h => hnk (Nat.coprime_mul_iff_right.mp h).2
      simp [hnr, hnk, hnK]
  · have hnK : ¬n.Coprime (r * (ell / chi.conductor)) :=
      fun h => hnr (Nat.coprime_mul_iff_right.mp h).1
    simp [hnr, hnK]

/-- An induced primitive character remains nonprincipal when the original
full-level character is nonprincipal. -/
theorem primitiveCharacter_ne_one {ell : ℕ}
    (chi : DirichletCharacter ℂ ell) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro h
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, h, map_one]

/-- Exact AP-error expansion of the primitive coefficient. This is a
narrow extraction of the existing private character_auxSW_expansion in
Part3SharedFirstFactorLowConductorSW: its argument is r*k here, retaining
the conductor quotient rather than paying the whole ambient modulus. -/
theorem primitive_sum_eq_auxSW (d : MediumAtom) (K : ℕ) {f : ℕ}
    [NeZero f] (psi : DirichletCharacter ℂ f) (hpsi : psi ≠ 1) :
    auxiliaryCharacterSum d.alphaCarrier d.alpha K f psi =
      ∑ b : ZMod f, star (psi b) * d.auxSWError K f b.val := by
  have hsum : (∑ b : ZMod f, star (psi b)) = 0 := by
    rw [← star_sum, MulChar.sum_eq_zero_of_ne_one hpsi, star_zero]
  let center : ℂ := (∑ n ∈ d.alphaCarrier,
    if n.Coprime (K * f) then d.alpha n else 0) / (f.totient : ℂ)
  have hcenter : (∑ b : ZMod f, star (psi b) * center) = 0 := by
    rw [← Finset.sum_mul, hsum, zero_mul]
  unfold auxiliaryCharacterSum
  symm
  change (∑ b : ZMod f, star (psi b) *
    ((∑ n ∈ d.alphaCarrier,
      if Nat.ModEq f n b.val ∧ n.Coprime K then d.alpha n else 0) - center)) = _
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hcenter, sub_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Coprime K
  · rw [if_pos hn]
    calc
      _ = star (psi (n : ZMod f)) * d.alpha n := by
        rw [Finset.sum_eq_single (n : ZMod f)]
        · have hm : Nat.ModEq f n (n : ZMod f).val := by
            apply (ZMod.natCast_eq_natCast_iff n (n : ZMod f).val f).mp
            exact (ZMod.natCast_zmod_val (n : ZMod f)).symm
          rw [if_pos ⟨hm, hn⟩]
        · intro b _ hne
          have hm : ¬Nat.ModEq f n b.val := by
            intro h
            have he := (ZMod.natCast_eq_natCast_iff n b.val f).mpr h
            rw [ZMod.natCast_zmod_val] at he
            exact hne he.symm
          rw [if_neg (fun h => hm h.1), mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = _ := mul_comm _ _
  · simp only [hn, and_false, if_false, mul_zero, Finset.sum_const_zero]

/-- The low-conductor coefficient costs f times the original AP error on
r*k. No full-modulus divisor loss is introduced by changing level. -/
theorem filteredCharacterSum_norm_le_conductor
    (d : MediumAtom) {ell : ℕ} (hell : 0 < ell) (r : ℕ)
    (chi : DirichletCharacter ℂ ell) (hchi : chi ≠ 1)
    {E : ℝ} (hE : 0 ≤ E)
    (herr : ∀ b : ℕ, b.Coprime chi.conductor →
      ‖d.auxSWError (r * (ell / chi.conductor)) chi.conductor b‖ ≤ E) :
    ‖filteredCharacterSum d r ell chi‖ ≤ (chi.conductor : ℝ) * E := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [filteredCharacterSum_eq_primitive_quotient d hell r chi,
    primitive_sum_eq_auxSW d _ chi.primitiveCharacter
      (primitiveCharacter_ne_one chi hchi)]
  calc
    _ ≤ ∑ b : ZMod chi.conductor,
        ‖star (chi.primitiveCharacter b) *
          d.auxSWError (r * (ell / chi.conductor)) chi.conductor b.val‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _b : ZMod chi.conductor, E := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : IsUnit b
      · have hbc : b.val.Coprime chi.conductor := by
          apply (ZMod.isUnit_iff_coprime b.val chi.conductor).mp
          simpa only [ZMod.natCast_zmod_val] using hb
        calc
          _ = ‖chi.primitiveCharacter b‖ *
              ‖d.auxSWError (r * (ell / chi.conductor)) chi.conductor b.val‖ := by
            rw [norm_mul, norm_star]
          _ ≤ 1 * E := mul_le_mul (chi.primitiveCharacter.norm_le_one b)
            (herr b.val hbc) (norm_nonneg _) (by norm_num)
          _ = E := one_mul E
      · rw [chi.primitiveCharacter.map_nonunit hb, star_zero, zero_mul, norm_zero]
        exact hE
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]

/-- Original auxiliary SW gives a uniform arbitrary logarithmic saving
for each actual low-conductor coefficient, with the required tau(r*k)
cost. In the paper tau(r*k) ≤ tau(r)*tau(k) is paid by fixed divisor means.
Neither an unweighted nor a weighted BDH estimate is assumed. -/
theorem uniformAuxiliarySW_lowConductor_filteredCharacterSum
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A L : ℝ, 0 < A → 0 ≤ L →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i : ι, x0 ≤ (F i).scale → ∀ r ell : ℕ,
          1 ≤ r → 1 ≤ ell → ∀ chi : DirichletCharacter ℂ ell,
          chi ≠ 1 → (chi.conductor : ℝ) ≤ (Real.log (F i).scale) ^ L →
          ‖filteredCharacterSum (F i) r ell chi‖ ≤
            C * (F i).U *
              (((r * (ell / chi.conductor)).divisors.card : ℝ) ^ C0) /
              (Real.log (F i).scale) ^ A := by
  intro A L hA hL
  obtain ⟨C, hC, x0, hx0, hbound⟩ := hSW (A + L) (add_pos_of_pos_of_nonneg hA hL)
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro i hx r ell hr hell chi hchi hconductor
  let : NeZero ell := ⟨by omega⟩
  have hf : 1 ≤ chi.conductor := Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero
  have hk : 0 < ell / chi.conductor := by
    have hprod := conductor_times_quotient chi
    by_contra h
    have hz : ell / chi.conductor = 0 := by omega
    rw [hz, mul_zero] at hprod
    omega
  have hK : 1 ≤ r * (ell / chi.conductor) := by
    exact Nat.mul_pos (by omega) hk
  have hlog : 0 < Real.log (F i).scale := Real.log_pos (hx0.trans_le hx)
  let E : ℝ := C * (F i).U *
    (((r * (ell / chi.conductor)).divisors.card : ℝ) ^ C0) /
    (Real.log (F i).scale) ^ (A + L)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hC.le (by linarith [(hadmissible i).1]))
        (pow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_pos_of_pos hlog _).le
  calc
    _ ≤ (chi.conductor : ℝ) * E :=
      filteredCharacterSum_norm_le_conductor (F i) (by omega) r chi hchi hE
        (fun b hb => hbound i hx (r * (ell / chi.conductor))
          chi.conductor b hK hf hb)
    _ ≤ (Real.log (F i).scale) ^ L * E :=
      mul_le_mul_of_nonneg_right hconductor hE
    _ = _ := by
      dsimp only [E]
      rw [Real.rpow_add hlog A L]
      field_simp [(Real.rpow_pos_of_pos hlog A).ne',
        (Real.rpow_pos_of_pos hlog L).ne']

/-- The actual nonnegative variance, over the original reduced classes. -/
def filteredVariance (d : MediumAtom) (ell r : ℕ) : ℝ :=
  ∑ b ∈ reducedResidues ell, ‖filteredError d ell r b‖ ^ 2

theorem filteredVariance_nonneg (d : MediumAtom) (ell r : ℕ) :
    0 ≤ filteredVariance d ell r :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem complex_square (z : ℂ) : (‖z‖ ^ 2 : ℂ) = z * star z := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
  exact (Complex.mul_conj z).symm

/-- Real, positive Parseval in the precise quotient-filtered coefficient
needed for both the fixed-k primitive large sieve and small-conductor SW. -/
theorem filteredVariance_eq_primitive_quotient_energy
    (d : MediumAtom) {ell r : ℕ} (hell : 0 < ell) :
    filteredVariance d ell r =
      (∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ ell)).erase 1,
        ‖auxiliaryCharacterSum d.alphaCarrier d.alpha
          (r * (ell / chi.conductor)) chi.conductor chi.primitiveCharacter‖ ^ 2) /
        (ell.totient : ℝ) := by
  have h := filteredVariance_eq_nonprincipal (d := d) (r := r) hell
  change (∑ b ∈ reducedResidues ell,
      filteredError d ell r b * star (filteredError d ell r b)) =
    (∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ ell)).erase 1,
      filteredCharacterSum d r ell chi * star (filteredCharacterSum d r ell chi)) /
        (ell.totient : ℂ) at h
  simp_rw [filteredCharacterSum_eq_primitive_quotient d hell r] at h
  simp_rw [← complex_square] at h
  unfold filteredVariance
  exact_mod_cast h

/-- The weighted-Cauchy step stated after (14), on the literal variance.
All finite carriers remain explicit, so the r-filter is not silently
replaced by an unfiltered coefficient. -/
theorem weighted_variance_cauchy (d : MediumAtom) (r : ℕ)
    (E : Finset ℕ) (w : ℕ → ℝ) :
    (∑ ell ∈ E, w ell * filteredVariance d ell r) ^ 2 ≤
      (∑ ell ∈ E, filteredVariance d ell r) *
        (∑ ell ∈ E, (w ell) ^ 2 * filteredVariance d ell r) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro ell _
    exact filteredVariance_nonneg d ell r
  · intro ell _
    exact mul_nonneg (sq_nonneg _) (filteredVariance_nonneg d ell r)
  · intro ell _
    exact le_of_eq (by ring)

end
end ImbalancedChen.Part3.ActualFilteredPrimitiveSWSourceOnly
