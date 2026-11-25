import ImbalancedChen.Part3SharedFirstFactorCharacterDictionary

/-!
# The actual auxiliary character sum at low conductor

The nonunit restriction at the full character level is retained in the
auxiliary parameter k * delta. For the shared-first-factor dictionary,
k = v / D and delta = p * D give k * delta = p * v. The divisor cost below
is therefore the cost of that full physical modulus.

This leaf proves a pointwise low-conductor bound from the original
UniformAuxiliarySW. It does not sum the physical labels or pay a zero mode.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open SharedFirstFactorCharacterDictionary

namespace SharedFirstFactorLowConductorSW

/-- Changing the character level keeps its nonunits in the auxiliary sieve. -/
private theorem auxiliaryCharacterSum_changeLevel_absorb
    (d : MediumAtom) (k : ℕ) {f delta : ℕ} (hfd : f ∣ delta)
    (psi : DirichletCharacter ℂ f) :
    auxiliaryCharacterSum d.alphaCarrier d.alpha k delta
        (DirichletCharacter.changeLevel hfd psi) =
      ∑ n ∈ d.alphaCarrier,
        if n.Coprime (k * delta) then d.alpha n * star (psi (n : ZMod f)) else 0 := by
  unfold auxiliaryCharacterSum
  apply Finset.sum_congr rfl
  intro n _
  by_cases hnd : n.Coprime delta
  · have he : (DirichletCharacter.changeLevel hfd psi) (n : ZMod delta) =
        psi (n : ZMod f) := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.changeLevel_eq_cast_of_dvd' psi hfd
          (Nat.isCoprime_iff_coprime.mpr hnd))
    rw [he]
    by_cases hnk : n.Coprime k
    · rw [if_pos hnk, if_pos (hnk.mul_right hnd)]
    · have hnK : ¬n.Coprime (k * delta) :=
        fun h => hnk (Nat.coprime_mul_iff_right.mp h).1
      rw [if_neg hnk, if_neg hnK]
  · have hnu : ¬IsUnit (n : ZMod delta) :=
      fun h => hnd ((ZMod.isUnit_iff_coprime n delta).mp h)
    have hnK : ¬n.Coprime (k * delta) :=
      fun h => hnd (Nat.coprime_mul_iff_right.mp h).2
    rw [MulChar.map_nonunit _ hnu, star_zero, mul_zero, if_neg hnK]
    exact ite_self 0

/-- The principal AP center cancels against a nonprincipal character. -/
private theorem character_auxSW_expansion
    (d : MediumAtom) (K : ℕ) {f : ℕ} [NeZero f]
    (psi : DirichletCharacter ℂ f) (hpsi : psi ≠ 1) :
    (∑ n ∈ d.alphaCarrier,
      if n.Coprime K then d.alpha n * star (psi (n : ZMod f)) else 0) =
        ∑ b : ZMod f, star (psi b) * d.auxSWError K f b.val := by
  have hsum : (∑ b : ZMod f, star (psi b)) = 0 := by
    rw [← star_sum, MulChar.sum_eq_zero_of_ne_one hpsi, star_zero]
  let center : ℂ := (∑ n ∈ d.alphaCarrier,
    if n.Coprime (K * f) then d.alpha n else 0) / (f.totient : ℂ)
  have hcenter : (∑ b : ZMod f, star (psi b) * center) = 0 := by
    rw [← Finset.sum_mul, hsum, zero_mul]
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
          have hgate : Nat.ModEq f n (n : ZMod f).val ∧ n.Coprime K := ⟨hm, hn⟩
          rw [if_pos hgate]
        · intro b _ hne
          have hm : ¬Nat.ModEq f n b.val := by
            intro h
            have he := (ZMod.natCast_eq_natCast_iff n b.val f).mpr h
            rw [ZMod.natCast_zmod_val] at he
            exact hne he.symm
          have hgate : ¬(Nat.ModEq f n b.val ∧ n.Coprime K) := fun h => hm h.1
          rw [if_neg hgate, mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = _ := mul_comm _ _
  · simp only [hn, and_false, if_false, mul_zero, Finset.sum_const_zero]

private theorem auxiliaryCharacterSum_changeLevel_eq_auxSW
    (d : MediumAtom) (k : ℕ) {f delta : ℕ} [NeZero f]
    (hfd : f ∣ delta) (psi : DirichletCharacter ℂ f) (hpsi : psi ≠ 1) :
    auxiliaryCharacterSum d.alphaCarrier d.alpha k delta
        (DirichletCharacter.changeLevel hfd psi) =
      ∑ b : ZMod f, star (psi b) * d.auxSWError (k * delta) f b.val := by
  rw [auxiliaryCharacterSum_changeLevel_absorb d k hfd psi]
  exact character_auxSW_expansion d (k * delta) psi hpsi

/-- A finite norm budget, retaining the full level inside the SW parameter. -/
private theorem auxiliaryCharacterSum_norm_le_conductor
    (d : MediumAtom) (k : ℕ) {delta : ℕ} (hdelta : 0 < delta)
    (chi : DirichletCharacter ℂ delta) (hchi : chi ≠ 1)
    {E : ℝ} (hE : 0 ≤ E)
    (herr : ∀ b : ℕ, b.Coprime chi.conductor →
      ‖d.auxSWError (k * delta) chi.conductor b‖ ≤ E) :
    ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ≤
      (chi.conductor : ℝ) * E := by
  let : NeZero delta := ⟨hdelta.ne'⟩
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpsi : chi.primitiveCharacter ≠ 1 := by
    intro he
    apply hchi
    rw [← chi.changeLevel_primitiveCharacter, he, map_one]
  have heq : auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi =
      ∑ b : ZMod chi.conductor,
        star (chi.primitiveCharacter b) * d.auxSWError (k * delta) chi.conductor b.val := by
    simpa only [chi.changeLevel_primitiveCharacter] using
      auxiliaryCharacterSum_changeLevel_eq_auxSW d k chi.conductor_dvd_level
        chi.primitiveCharacter hpsi
  rw [heq]
  calc
    _ ≤ ∑ b : ZMod chi.conductor,
        ‖star (chi.primitiveCharacter b) * d.auxSWError (k * delta) chi.conductor b.val‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _b : ZMod chi.conductor, E := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : IsUnit b
      · have hb' : b.val.Coprime chi.conductor := by
          apply (ZMod.isUnit_iff_coprime b.val chi.conductor).mp
          simpa only [ZMod.natCast_zmod_val] using hb
        calc
          _ = ‖chi.primitiveCharacter b‖ *
              ‖d.auxSWError (k * delta) chi.conductor b.val‖ := by
            rw [norm_mul, norm_star]
          _ ≤ 1 * E := mul_le_mul (chi.primitiveCharacter.norm_le_one b)
            (herr b.val hb') (norm_nonneg _) (by norm_num)
          _ = E := one_mul E
      · rw [chi.primitiveCharacter.map_nonunit hb, star_zero, zero_mul, norm_zero]
        exact hE
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]

end SharedFirstFactorLowConductorSW

/-- The original auxiliary SW constants pay a fixed polylogarithmic conductor.
The auxiliary divisor penalty is that of k * delta, including every nonunit gate. -/
theorem uniformAuxiliarySW_lowConductor_auxiliaryCharacterSum
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A L : ℝ, 0 < A → 0 ≤ L →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i : ι, x0 ≤ (F i).scale → ∀ k delta : ℕ,
          1 ≤ k → 1 ≤ delta → ∀ chi : DirichletCharacter ℂ delta,
          chi ≠ 1 → (chi.conductor : ℝ) ≤ (Real.log (F i).scale) ^ L →
          ‖auxiliaryCharacterSum (F i).alphaCarrier (F i).alpha k delta chi‖ ≤
            C * (F i).U * (((k * delta).divisors.card : ℝ) ^ C0) /
              (Real.log (F i).scale) ^ A := by
  intro A L hA hL
  obtain ⟨C, hC, x0, hx0, hbound⟩ := hSW (A + L) (add_pos_of_pos_of_nonneg hA hL)
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro i hx k delta hk hdelta chi hchi hconductor
  let : NeZero delta := ⟨by omega⟩
  have hf : 1 ≤ chi.conductor := Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero
  have hK : 1 ≤ k * delta := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by omega : k ≠ 0) (by omega : delta ≠ 0))
  have hlog : 0 < Real.log (F i).scale := Real.log_pos (hx0.trans_le hx)
  let E : ℝ := C * (F i).U * (((k * delta).divisors.card : ℝ) ^ C0) /
    (Real.log (F i).scale) ^ (A + L)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hC.le (by linarith [(hadmissible i).1]))
        (pow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_pos_of_pos hlog _).le
  calc
    _ ≤ (chi.conductor : ℝ) * E :=
      SharedFirstFactorLowConductorSW.auxiliaryCharacterSum_norm_le_conductor
        (F i) k (by omega) chi hchi hE
        (fun b hb => hbound i hx (k * delta) chi.conductor b hK hf hb)
    _ ≤ (Real.log (F i).scale) ^ L * E :=
      mul_le_mul_of_nonneg_right hconductor hE
    _ = _ := by
      dsimp only [E]
      rw [Real.rpow_add hlog A L]
      field_simp [(Real.rpow_pos_of_pos hlog A).ne',
        (Real.rpow_pos_of_pos hlog L).ne']

end

end ImbalancedChen.Part3
