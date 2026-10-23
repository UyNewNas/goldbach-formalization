import ImbalancedChen.Part3SharedFirstFactorLowConductorSW

/-!
# The actual low-conductor shared-first-factor zero covariance

The full physical p and both original two-factor labels are retained.
The low-conductor filter is the only change to the character dictionary.
Its full auxiliary divisor cost is paid by fixed-order harmonic means.

The public uniform low-conductor estimate uses the original auxiliary SW.
High conductor, nonzero frequencies and the full distribution endpoint
are separate obligations.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise
open SharedFirstFactorCharacterDictionary
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The literal original zero covariance restricted to low conductor. -/
def MediumAtom.sharedFirstFactorLowConductorZero (d : MediumAtom) (R : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
      ∑ v ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
          (((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ) *
            ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ))) *
          (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
          (∑ chi ∈ ((Finset.univ : Finset
              (DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)))).erase 1).filter
                (fun chi => (chi.conductor : ℝ) ≤ R),
            auxiliaryCharacterSum d.alphaCarrier d.alpha
              ((u.1 * u.2) / (u.1 * u.2).gcd (v.1 * v.2))
              (p * (u.1 * u.2).gcd (v.1 * v.2)) chi *
            star (auxiliaryCharacterSum d.alphaCarrier d.alpha
              ((v.1 * v.2) / (u.1 * u.2).gcd (v.1 * v.2))
              (p * (u.1 * u.2).gcd (v.1 * v.2)) chi))

namespace SharedFirstFactorLowConductorAggregate

private def divisorTau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

private theorem divisorTau_nonneg (n : ℕ) : 0 ≤ divisorTau n := by
  exact Nat.cast_nonneg _

/-- A local finite extraction avoids importing a broader divisor module. -/
private theorem divisors_mul_eq (a b : ℕ) :
    (a * b).divisors = a.divisors * b.divisors := by
  ext n
  simp_rw [Finset.mem_mul, Nat.mem_divisors, Nat.dvd_mul, mul_ne_zero_iff,
    ← exists_and_left, ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

private theorem divisorTau_mul_le (a b : ℕ) :
    divisorTau (a * b) ≤ divisorTau a * divisorTau b := by
  unfold divisorTau
  rw [divisors_mul_eq]
  exact_mod_cast (Finset.card_mul_le (s := a.divisors) (t := b.divisors))

private theorem divisorTau_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    divisorTau a ≤ divisorTau b := by
  unfold divisorTau
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hb hab)

private theorem divisorTau_pow_le (r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    divisorTau n ^ r ≤ (fouvryTau (2 ^ r) n : ℝ) := by
  unfold divisorTau
  have h := fouvryTau_pow_le 2 r hn
  rw [fouvryTau_two] at h
  exact_mod_cast h

private theorem factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) :
    0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hlower : Q ≤ (n : ℝ) :=
    (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  have hpos : (0 : ℝ) < n := (zero_lt_one.trans_le hQ).trans_le hlower
  refine ⟨by exact_mod_cast hpos, hlower, ?_⟩
  exact (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
    (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem factor_subset_Ioc {Q : ℝ} (hQ : 1 ≤ Q) :
    factorCarrier Q ⊆ Finset.Ioc 0 (Nat.floor (2 * Q)) := by
  intro n hn
  exact Finset.mem_Ioc.mpr ⟨(factor_bounds hQ hn).1, (Finset.mem_Icc.mp hn).2⟩

private theorem dyadic_divisor_harmonic {Q : ℝ} (hQ : 1 ≤ Q) (r : ℕ) :
    (∑ n ∈ factorCarrier Q, divisorTau n ^ r / (n : ℝ)) ≤
      (1 + Real.log (2 * Q)) ^ (2 ^ r) := by
  calc
    _ ≤ ∑ n ∈ factorCarrier Q, (fouvryTau (2 ^ r) n : ℝ) / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right
        (divisorTau_pow_le r (factor_bounds hQ hn).1.ne') (Nat.cast_nonneg _)
    _ ≤ ∑ n ∈ Finset.Ioc 0 (Nat.floor (2 * Q)),
        (fouvryTau (2 ^ r) n : ℝ) / (n : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (factor_subset_Ioc hQ)
        (fun n _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ ≤ _ := sum_fouvryTau_div_le_real _ (by linarith : 1 ≤ 2 * Q)

private theorem primitive_p_reciprocal_square (d : MediumAtom)
    (hQ : 1 ≤ d.Q1) (r : ℕ) :
    (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ r / (p : ℝ) ^ 2) ≤
      (1 + Real.log (2 * d.Q1)) ^ (2 ^ r) / d.Q1 := by
  have hQpos : 0 < d.Q1 := zero_lt_one.trans_le hQ
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier, (divisorTau p ^ r / (p : ℝ)) / d.Q1 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp0, hQp, _⟩ := factor_bounds hQ (Finset.mem_filter.mp hp).1
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
      have hi : 1 / (p : ℝ) ≤ 1 / d.Q1 := one_div_le_one_div_of_le hQpos hQp
      calc
        _ = (divisorTau p ^ r / (p : ℝ)) * (1 / (p : ℝ)) := by ring
        _ ≤ (divisorTau p ^ r / (p : ℝ)) * (1 / d.Q1) :=
          mul_le_mul_of_nonneg_left hi (div_nonneg
            (pow_nonneg (divisorTau_nonneg _) _) hpR.le)
        _ = _ := by ring
    _ = (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ r / (p : ℝ)) / d.Q1 := by
      rw [Finset.sum_div]
    _ ≤ (∑ p ∈ factorCarrier d.Q1, divisorTau p ^ r / (p : ℝ)) / d.Q1 := by
      apply div_le_div_of_nonneg_right _ hQpos.le
      have hsubset : d.primitiveFirstFactorCarrier ⊆ factorCarrier d.Q1 := by
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _ _ => div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _))
    _ ≤ _ := div_le_div_of_nonneg_right (dyadic_divisor_harmonic hQ r) hQpos.le

private theorem two_label_harmonic {Q2 Q3 : ℝ}
    (hQ2 : 1 ≤ Q2) (hQ3 : 1 ≤ Q3) (r : ℕ) :
    (∑ u ∈ factorCarrier Q2 ×ˢ factorCarrier Q3,
      divisorTau (u.1 * u.2) ^ r / ((u.1 * u.2 : ℕ) : ℝ)) ≤
      (1 + Real.log (2 * Q2)) ^ (2 ^ r) *
        (1 + Real.log (2 * Q3)) ^ (2 ^ r) := by
  simp only [Finset.sum_product]
  calc
    _ ≤ ∑ a ∈ factorCarrier Q2, ∑ b ∈ factorCarrier Q3,
        (divisorTau a ^ r / (a : ℝ)) * (divisorTau b ^ r / (b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      calc
        _ ≤ (divisorTau a * divisorTau b) ^ r / ((a * b : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (divisorTau_nonneg _) (divisorTau_mul_le a b) r)
            (Nat.cast_nonneg _)
        _ = _ := by
          simp only [mul_pow, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
          ring
    _ = (∑ a ∈ factorCarrier Q2, divisorTau a ^ r / (a : ℝ)) *
        (∑ b ∈ factorCarrier Q3, divisorTau b ^ r / (b : ℝ)) := by
      rw [Finset.sum_mul_sum]
    _ ≤ _ := mul_le_mul (dyadic_divisor_harmonic hQ2 r) (dyadic_divisor_harmonic hQ3 r)
      (Finset.sum_nonneg (fun b _ => div_nonneg
        (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _)))
      (pow_nonneg (by linarith [Real.log_nonneg (show 1 ≤ 2 * Q2 by linarith)]) _)

/-- The number of characters with bounded conductor is independent of the ambient level. -/
private theorem card_low_conductor_le {delta r : ℕ} (hdelta : 0 < delta) :
    ((Finset.univ : Finset (DirichletCharacter ℂ delta)).filter
      (fun chi => chi.conductor ≤ r)).card ≤ r * r := by
  classical
  let : NeZero delta := ⟨hdelta.ne'⟩
  let low : Finset (DirichletCharacter ℂ delta) :=
    Finset.univ.filter (fun chi => chi.conductor ≤ r)
  let lifted : ℕ → Finset (DirichletCharacter ℂ delta) := fun f =>
    if hfd : f ∣ delta then
      (Finset.univ : Finset (DirichletCharacter ℂ f)).image
        (fun psi => DirichletCharacter.changeLevel hfd psi)
    else ∅
  have hcover : low ⊆ (Finset.Icc 1 r).biUnion lifted := by
    intro chi hchi
    have hbound : chi.conductor ≤ r := (Finset.mem_filter.mp hchi).2
    apply Finset.mem_biUnion.mpr
    refine ⟨chi.conductor, Finset.mem_Icc.mpr ⟨?_, hbound⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero
    · dsimp only [lifted]
      rw [dif_pos chi.conductor_dvd_level]
      exact Finset.mem_image.mpr
        ⟨chi.primitiveCharacter, Finset.mem_univ _, chi.changeLevel_primitiveCharacter⟩
  have hlifted : ∀ f ∈ Finset.Icc 1 r, (lifted f).card ≤ r := by
    intro f hf
    obtain ⟨hfpos, hfr⟩ := Finset.mem_Icc.mp hf
    let : NeZero f := ⟨by omega⟩
    by_cases hfd : f ∣ delta
    · dsimp only [lifted]
      rw [dif_pos hfd]
      calc
        _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ f)).card :=
          Finset.card_image_le
        _ = Nat.card (DirichletCharacter ℂ f) := by
          rw [Finset.card_univ, Nat.card_eq_fintype_card]
        _ = f.totient :=
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ f
        _ ≤ f := Nat.totient_le f
        _ ≤ r := hfr
    · dsimp only [lifted]
      rw [dif_neg hfd, Finset.card_empty]
      exact Nat.zero_le r
  calc
    _ = low.card := rfl
    _ ≤ ((Finset.Icc 1 r).biUnion lifted).card := Finset.card_le_card hcover
    _ ≤ ∑ f ∈ Finset.Icc 1 r, (lifted f).card := Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ Finset.Icc 1 r, r := Finset.sum_le_sum hlifted
    _ = (Finset.Icc 1 r).card * r := Finset.sum_const_nat (fun _ _ => rfl)
    _ = r * r := by simp only [Nat.card_Icc, Nat.add_sub_cancel]

/-- A real conductor cutoff has at most its square many nonprincipal characters. -/
private theorem card_low_conductor_real_le {delta : ℕ} (hdelta : 0 < delta)
    {R : ℝ} (hR : 1 ≤ R) :
    ((((Finset.univ : Finset (DirichletCharacter ℂ delta)).erase 1).filter
      (fun chi => (chi.conductor : ℝ) ≤ R)).card : ℝ) ≤ R ^ 2 := by
  classical
  let low : Finset (DirichletCharacter ℂ delta) :=
    (Finset.univ.erase 1).filter (fun chi => (chi.conductor : ℝ) ≤ R)
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hcover : low ⊆
      (Finset.univ : Finset (DirichletCharacter ℂ delta)).filter
        (fun chi => chi.conductor ≤ ⌊R⌋₊) := by
    intro chi hchi
    have hbound : (chi.conductor : ℝ) ≤ R := (Finset.mem_filter.mp hchi).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Nat.le_floor_iff hR0).mpr hbound⟩
  have hcard : low.card ≤ ⌊R⌋₊ * ⌊R⌋₊ :=
    (Finset.card_le_card hcover).trans (card_low_conductor_le hdelta)
  have hcardReal : (low.card : ℝ) ≤ (⌊R⌋₊ : ℝ) * (⌊R⌋₊ : ℝ) := by
    exact_mod_cast hcard
  calc
    _ = (low.card : ℝ) := rfl
    _ ≤ (⌊R⌋₊ : ℝ) * (⌊R⌋₊ : ℝ) := hcardReal
    _ ≤ R * R := mul_le_mul (Nat.floor_le hR0) (Nat.floor_le hR0)
      (Nat.cast_nonneg _) hR0
    _ = R ^ 2 := by ring

private theorem physical_divisor_weight (C0 : ℕ) {p v1 v2 : ℕ}
    (hp : 0 < p) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (divisorTau (p * v1) ^ C0 * divisorTau (p * v2) ^ C0) /
        ((p : ℝ) * (v1.lcm v2 : ℝ) * ((p * v1.gcd v2).totient : ℝ)) ≤
      (divisorTau p ^ (2 * C0 + 1) / (p : ℝ) ^ 2) *
        (divisorTau v1 ^ (C0 + 1) / (v1 : ℝ)) *
        (divisorTau v2 ^ C0 / (v2 : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hDR : (0 : ℝ) < v1.gcd v2 := by
    exact_mod_cast Nat.gcd_pos_of_pos_left v2 hv1
  have hLR : (0 : ℝ) < v1.lcm v2 := by
    exact_mod_cast Nat.lcm_pos hv1 hv2
  have hphiR : (0 : ℝ) < (p * v1.gcd v2).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hp (Nat.gcd_pos_of_pos_left v2 hv1))
  have hprod : divisorTau (p * v1) ^ C0 * divisorTau (p * v2) ^ C0 ≤
      divisorTau p ^ (2 * C0) * divisorTau v1 ^ C0 * divisorTau v2 ^ C0 := by
    calc
      _ ≤ (divisorTau p * divisorTau v1) ^ C0 *
          (divisorTau p * divisorTau v2) ^ C0 :=
        mul_le_mul (pow_le_pow_left₀ (divisorTau_nonneg _) (divisorTau_mul_le p v1) C0)
          (pow_le_pow_left₀ (divisorTau_nonneg _) (divisorTau_mul_le p v2) C0)
          (pow_nonneg (divisorTau_nonneg _) _) (pow_nonneg
            (mul_nonneg (divisorTau_nonneg _) (divisorTau_nonneg _)) _)
      _ = _ := by rw [mul_pow, mul_pow, two_mul, pow_add]; ring
  have hTauD : divisorTau (v1.gcd v2) ≤ divisorTau v1 :=
    divisorTau_le_of_dvd hv1.ne' (Nat.gcd_dvd_left v1 v2)
  have hTauPD : divisorTau (p * v1.gcd v2) ≤ divisorTau p * divisorTau v1 :=
    (divisorTau_mul_le p (v1.gcd v2)).trans
      (mul_le_mul_of_nonneg_left hTauD (divisorTau_nonneg _))
  have htot : (p : ℝ) * (v1.gcd v2 : ℝ) ≤
      ((p * v1.gcd v2).totient : ℝ) * (divisorTau p * divisorTau v1) := by
    have h := le_totient_mul_fouvryTau_two (p * v1.gcd v2)
    rw [fouvryTau_two] at h
    have h' : (p : ℝ) * (v1.gcd v2 : ℝ) ≤
        ((p * v1.gcd v2).totient : ℝ) * divisorTau (p * v1.gcd v2) := by
      unfold divisorTau
      exact_mod_cast h
    exact h'.trans (mul_le_mul_of_nonneg_left hTauPD hphiR.le)
  have hphi : 1 / ((p * v1.gcd v2).totient : ℝ) ≤
      (divisorTau p * divisorTau v1) / ((p : ℝ) * (v1.gcd v2 : ℝ)) := by
    apply (div_le_div_iff₀ hphiR (mul_pos hpR hDR)).mpr
    simpa only [one_mul, mul_one, mul_comm] using htot
  have hgL : (v1.gcd v2 : ℝ) * (v1.lcm v2 : ℝ) = (v1 : ℝ) * (v2 : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm v1 v2
  calc
    _ = ((divisorTau (p * v1) ^ C0 * divisorTau (p * v2) ^ C0) /
        ((p : ℝ) * (v1.lcm v2 : ℝ))) *
          (1 / ((p * v1.gcd v2).totient : ℝ)) := by ring
    _ ≤ ((divisorTau p ^ (2 * C0) * divisorTau v1 ^ C0 * divisorTau v2 ^ C0) /
        ((p : ℝ) * (v1.lcm v2 : ℝ))) *
          ((divisorTau p * divisorTau v1) / ((p : ℝ) * (v1.gcd v2 : ℝ))) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hprod (mul_nonneg hpR.le hLR.le))
        hphi (div_nonneg (by norm_num) hphiR.le)
          (div_nonneg
            (mul_nonneg (mul_nonneg (pow_nonneg (divisorTau_nonneg _) _)
              (pow_nonneg (divisorTau_nonneg _) _))
              (pow_nonneg (divisorTau_nonneg _) _))
            (mul_nonneg hpR.le hLR.le))
    _ = (divisorTau p ^ (2 * C0 + 1) * divisorTau v1 ^ (C0 + 1) *
        divisorTau v2 ^ C0) / ((p : ℝ) ^ 2 *
          ((v1.gcd v2 : ℝ) * (v1.lcm v2 : ℝ))) := by
      simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (divisorTau p ^ (2 * C0 + 1) * divisorTau v1 ^ (C0 + 1) *
        divisorTau v2 ^ C0) / ((p : ℝ) ^ 2 * ((v1 : ℝ) * (v2 : ℝ))) := by rw [hgL]
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

private theorem low_character_pair_bound (d : MediumAtom) (C0 : ℕ)
    {E R : ℝ} (hE : 0 ≤ E) (hR : 1 ≤ R) (hU : 0 ≤ d.U)
    (hpoint : ∀ k delta : ℕ, 1 ≤ k → 1 ≤ delta →
      ∀ chi : DirichletCharacter ℂ delta, chi ≠ 1 → (chi.conductor : ℝ) ≤ R →
        ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ≤
          E * d.U * divisorTau (k * delta) ^ C0)
    {p v1 v2 : ℕ} (hp : 0 < p) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ‖∑ chi ∈ ((Finset.univ : Finset
        (DirichletCharacter ℂ (p * v1.gcd v2))).erase 1).filter
          (fun chi => (chi.conductor : ℝ) ≤ R),
      auxiliaryCharacterSum d.alphaCarrier d.alpha (v1 / v1.gcd v2)
          (p * v1.gcd v2) chi *
        star (auxiliaryCharacterSum d.alphaCarrier d.alpha (v2 / v1.gcd v2)
          (p * v1.gcd v2) chi)‖ ≤
      R ^ 2 * (E * d.U) ^ 2 * divisorTau (p * v1) ^ C0 *
        divisorTau (p * v2) ^ C0 := by
  let delta := p * v1.gcd v2
  let k1 := v1 / v1.gcd v2
  let k2 := v2 / v1.gcd v2
  let low : Finset (DirichletCharacter ℂ delta) :=
    (Finset.univ.erase 1).filter (fun chi => (chi.conductor : ℝ) ≤ R)
  have hd0 : 0 < delta := Nat.mul_pos hp (Nat.gcd_pos_of_pos_left v2 hv1)
  have hk1 : 1 ≤ k1 := Nat.div_gcd_pos_of_pos_left v2 hv1
  have hk2 : 1 ≤ k2 := Nat.div_gcd_pos_of_pos_right v1 hv2
  have hphysical1 : k1 * delta = p * v1 := by
    dsimp only [k1, delta]
    calc
      _ = p * (v1 / v1.gcd v2 * v1.gcd v2) := by ring
      _ = _ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left v1 v2)]
  have hphysical2 : k2 * delta = p * v2 := by
    dsimp only [k2, delta]
    calc
      _ = p * (v2 / v1.gcd v2 * v1.gcd v2) := by ring
      _ = _ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right v1 v2)]
  have hcoefficient : 0 ≤ (E * d.U) ^ 2 * divisorTau (p * v1) ^ C0 *
      divisorTau (p * v2) ^ C0 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (divisorTau_nonneg _) _))
      (pow_nonneg (divisorTau_nonneg _) _)
  change ‖∑ chi ∈ low,
    auxiliaryCharacterSum d.alphaCarrier d.alpha k1 delta chi *
      star (auxiliaryCharacterSum d.alphaCarrier d.alpha k2 delta chi)‖ ≤ _
  calc
    _ ≤ ∑ chi ∈ low,
        ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k1 delta chi *
          star (auxiliaryCharacterSum d.alphaCarrier d.alpha k2 delta chi)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _chi ∈ low, (E * d.U) ^ 2 * divisorTau (p * v1) ^ C0 *
        divisorTau (p * v2) ^ C0 := by
      apply Finset.sum_le_sum
      intro chi hchi
      have hc := Finset.mem_filter.mp hchi
      have hne : chi ≠ 1 := (Finset.mem_erase.mp hc.1).1
      have h1 := hpoint k1 delta hk1 hd0 chi hne hc.2
      have h2 := hpoint k2 delta hk2 hd0 chi hne hc.2
      rw [hphysical1] at h1
      rw [hphysical2] at h2
      rw [norm_mul, norm_star]
      calc
        _ ≤ (E * d.U * divisorTau (p * v1) ^ C0) *
            (E * d.U * divisorTau (p * v2) ^ C0) :=
          mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hE hU) (pow_nonneg (divisorTau_nonneg _) _))
        _ = _ := by ring
    _ = (low.card : ℝ) * ((E * d.U) ^ 2 * divisorTau (p * v1) ^ C0 *
        divisorTau (p * v2) ^ C0) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ R ^ 2 * ((E * d.U) ^ 2 * divisorTau (p * v1) ^ C0 *
        divisorTau (p * v2) ^ C0) :=
      mul_le_mul_of_nonneg_right (card_low_conductor_real_le hd0 hR) hcoefficient
    _ = _ := by ring

private theorem finite_low_zero_bound
    {B C0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {E R : ℝ}
    (hE : 0 ≤ E) (hR : 1 ≤ R)
    (hpoint : ∀ k delta : ℕ, 1 ≤ k → 1 ≤ delta →
      ∀ chi : DirichletCharacter ℂ delta, chi ≠ 1 → (chi.conductor : ℝ) ≤ R →
        ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ≤
          E * d.U * divisorTau (k * delta) ^ C0) :
    ‖d.sharedFirstFactorLowConductorZero R‖ ≤
      |CommonSmoothCutoff.cutoffMass| * d.V * (E * d.U) ^ 2 * R ^ 2 *
        ((1 + Real.log (2 * d.Q1)) ^ (2 ^ (2 * C0 + 1)) / d.Q1) *
        ((1 + Real.log (2 * d.Q2)) ^ (2 ^ (C0 + 1)) *
          (1 + Real.log (2 * d.Q3)) ^ (2 ^ (C0 + 1))) *
        ((1 + Real.log (2 * d.Q2)) ^ (2 ^ C0) *
          (1 + Real.log (2 * d.Q3)) ^ (2 ^ C0)) := by
  rcases hd with ⟨hU, hV, hQ1, hQ2, hQ3, _, _, _, _, _, _, _, _, _, _, _, hg2, hg3⟩
  have hU0 : 0 ≤ d.U := zero_le_one.trans hU
  have hV0 : 0 ≤ d.V := zero_le_one.trans hV
  let tails := factorCarrier d.Q2 ×ˢ factorCarrier d.Q3
  let firstWeight (p : ℕ) := divisorTau p ^ (2 * C0 + 1) / (p : ℝ) ^ 2
  let leftWeight (u : ℕ × ℕ) := divisorTau (u.1 * u.2) ^ (C0 + 1) /
    ((u.1 * u.2 : ℕ) : ℝ)
  let rightWeight (v : ℕ × ℕ) := divisorTau (v.1 * v.2) ^ C0 /
    ((v.1 * v.2 : ℕ) : ℝ)
  let K : ℝ := |CommonSmoothCutoff.cutoffMass| * d.V * (E * d.U) ^ 2 * R ^ 2
  let term (p : ℕ) (u v : ℕ × ℕ) : ℂ :=
    (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
      (((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ) *
        ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ))) *
      (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
      (∑ chi ∈ ((Finset.univ : Finset
          (DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)))).erase 1).filter
            (fun chi => (chi.conductor : ℝ) ≤ R),
        auxiliaryCharacterSum d.alphaCarrier d.alpha
          ((u.1 * u.2) / (u.1 * u.2).gcd (v.1 * v.2))
          (p * (u.1 * u.2).gcd (v.1 * v.2)) chi *
        star (auxiliaryCharacterSum d.alphaCarrier d.alpha
          ((v.1 * v.2) / (u.1 * u.2).gcd (v.1 * v.2))
          (p * (u.1 * u.2).gcd (v.1 * v.2)) chi))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hfirst : ∀ p, 0 ≤ firstWeight p := by
    intro p
    exact div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (sq_nonneg _)
  have hleft : ∀ u, 0 ≤ leftWeight u := by
    intro u
    exact div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _)
  have hright : ∀ v, 0 ≤ rightWeight v := by
    intro v
    exact div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _)
  have hterm : ∀ p ∈ d.primitiveFirstFactorCarrier, ∀ u ∈ tails, ∀ v ∈ tails,
      ‖term p u v‖ ≤ K * firstWeight p * leftWeight u * rightWeight v := by
    intro p hp u hu v hv
    have hp0 := (factor_bounds hQ1 (Finset.mem_filter.mp hp).1).1
    have hu' := Finset.mem_product.mp hu
    have hv' := Finset.mem_product.mp hv
    have hu0 : 0 < u.1 * u.2 := Nat.mul_pos
      (factor_bounds hQ2 hu'.1).1 (factor_bounds hQ3 hu'.2).1
    have hv0 : 0 < v.1 * v.2 := Nat.mul_pos
      (factor_bounds hQ2 hv'.1).1 (factor_bounds hQ3 hv'.2).1
    let z : ℂ := (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
      (((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ) *
        ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ)))
    let gu : ℂ := d.gamma2 u.1 * d.gamma3 u.2
    let gv : ℂ := d.gamma2 v.1 * d.gamma3 v.2
    let chiSum : ℂ :=
      ∑ chi ∈ ((Finset.univ : Finset
          (DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)))).erase 1).filter
            (fun chi => (chi.conductor : ℝ) ≤ R),
        auxiliaryCharacterSum d.alphaCarrier d.alpha
            ((u.1 * u.2) / (u.1 * u.2).gcd (v.1 * v.2))
            (p * (u.1 * u.2).gcd (v.1 * v.2)) chi *
          star (auxiliaryCharacterSum d.alphaCarrier d.alpha
            ((v.1 * v.2) / (u.1 * u.2).gcd (v.1 * v.2))
            (p * (u.1 * u.2).gcd (v.1 * v.2)) chi)
    have hgu : ‖gu‖ ≤ 1 := by
      dsimp only [gu]
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul (hg2 u.1 hu'.1).1 (hg3 u.2 hu'.2).1 (norm_nonneg _) (by norm_num)
    have hgv : ‖gv‖ ≤ 1 := by
      dsimp only [gv]
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul (hg2 v.1 hv'.1).1 (hg3 v.2 hv'.2).1 (norm_nonneg _) (by norm_num)
    have hg : ‖gu‖ * ‖gv‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hgu hgv (norm_nonneg _) (by norm_num)
    have hchi : ‖chiSum‖ ≤ R ^ 2 * (E * d.U) ^ 2 *
        divisorTau (p * (u.1 * u.2)) ^ C0 * divisorTau (p * (v.1 * v.2)) ^ C0 :=
      low_character_pair_bound d C0 hE hR hU0 hpoint hp0 hu0 hv0
    have hz : ‖z‖ = |CommonSmoothCutoff.cutoffMass| * d.V /
        ((p : ℝ) * ((u.1 * u.2).lcm (v.1 * v.2) : ℝ) *
          ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℝ)) := by
      dsimp only [z]
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hV0, Complex.norm_natCast, Complex.norm_natCast]
      push_cast
      ring
    change ‖z * gu * star gv * chiSum‖ ≤ _
    calc
      _ ≤ ‖z‖ * ‖chiSum‖ := by
        simp only [norm_mul, norm_star]
        calc
          _ = (‖z‖ * ‖chiSum‖) * (‖gu‖ * ‖gv‖) := by ring
          _ ≤ (‖z‖ * ‖chiSum‖) * 1 :=
            mul_le_mul_of_nonneg_left hg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = _ := mul_one _
      _ ≤ ‖z‖ * (R ^ 2 * (E * d.U) ^ 2 *
          divisorTau (p * (u.1 * u.2)) ^ C0 * divisorTau (p * (v.1 * v.2)) ^ C0) :=
        mul_le_mul_of_nonneg_left hchi (norm_nonneg _)
      _ = K * ((divisorTau (p * (u.1 * u.2)) ^ C0 *
          divisorTau (p * (v.1 * v.2)) ^ C0) /
            ((p : ℝ) * ((u.1 * u.2).lcm (v.1 * v.2) : ℝ) *
              ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℝ))) := by
        rw [hz]
        dsimp only [K]
        ring
      _ ≤ K * (firstWeight p * leftWeight u * rightWeight v) :=
        mul_le_mul_of_nonneg_left (physical_divisor_weight C0 hp0 hu0 hv0) hK
      _ = _ := by ring
  change ‖∑ p ∈ d.primitiveFirstFactorCarrier, ∑ u ∈ tails, ∑ v ∈ tails,
    term p u v‖ ≤ _
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier, ∑ u ∈ tails, ∑ v ∈ tails,
        ‖term p u v‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u _
      exact norm_sum_le _ _
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier, ∑ u ∈ tails, ∑ v ∈ tails,
        K * firstWeight p * leftWeight u * rightWeight v := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.sum_le_sum (fun v hv => hterm p hp u hu v hv)
    _ = K * (∑ p ∈ d.primitiveFirstFactorCarrier, firstWeight p) *
        (∑ u ∈ tails, leftWeight u) * (∑ v ∈ tails, rightWeight v) := by
      calc
        _ = ∑ p ∈ d.primitiveFirstFactorCarrier, ∑ u ∈ tails,
            (K * firstWeight p * leftWeight u) * (∑ v ∈ tails, rightWeight v) := by
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.mul_sum]
        _ = ∑ p ∈ d.primitiveFirstFactorCarrier,
            (K * firstWeight p) * (∑ u ∈ tails, leftWeight u) *
              (∑ v ∈ tails, rightWeight v) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ K * ((1 + Real.log (2 * d.Q1)) ^ (2 ^ (2 * C0 + 1)) / d.Q1) *
        ((1 + Real.log (2 * d.Q2)) ^ (2 ^ (C0 + 1)) *
          (1 + Real.log (2 * d.Q3)) ^ (2 ^ (C0 + 1))) *
        ((1 + Real.log (2 * d.Q2)) ^ (2 ^ C0) *
          (1 + Real.log (2 * d.Q3)) ^ (2 ^ C0)) := by
      have h1 := primitive_p_reciprocal_square d hQ1 (2 * C0 + 1)
      have h2 := two_label_harmonic hQ2 hQ3 (C0 + 1)
      have h3 := two_label_harmonic hQ2 hQ3 C0
      have hn1 := Finset.sum_nonneg (fun p (_ : p ∈ d.primitiveFirstFactorCarrier) => hfirst p)
      have hn2 := Finset.sum_nonneg (fun u (_ : u ∈ tails) => hleft u)
      have hn3 := Finset.sum_nonneg (fun v (_ : v ∈ tails) => hright v)
      have hb1 : 0 ≤ (1 + Real.log (2 * d.Q1)) ^ (2 ^ (2 * C0 + 1)) / d.Q1 :=
        hn1.trans h1
      have hb2 : 0 ≤ (1 + Real.log (2 * d.Q2)) ^ (2 ^ (C0 + 1)) *
          (1 + Real.log (2 * d.Q3)) ^ (2 ^ (C0 + 1)) := hn2.trans h2
      exact mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) h2 hn2 (mul_nonneg hK hb1))
        h3 hn3 (mul_nonneg (mul_nonneg hK hb1) hb2)
    _ = _ := rfl

private theorem admissible_factor_scale_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.Q1 ≤ d.scale ∧ d.Q2 ≤ d.scale ∧ d.Q3 ≤ d.scale := by
  rcases hd with ⟨hU, hV, hQ1, hQ2, hQ3, _, _, _, hfirst, hgeometry, _⟩
  have hU0 : 0 ≤ d.U := zero_le_one.trans hU
  have hQ20 : 0 ≤ d.Q2 := zero_le_one.trans hQ2
  have hU2 : 1 ≤ d.U ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hU 2
  have hQ32 : 1 ≤ d.Q3 ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hQ3 2
  have hscale : 1 ≤ d.scale := by
    unfold MediumAtom.scale
    simpa only [one_mul] using mul_le_mul hU hV zero_le_one hU0
  have hUscale : d.U ≤ d.scale := by
    exact le_mul_of_one_le_right hU0 hV
  have hsmall : d.scale ^ (-sigma) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hscale (by linarith)
  have hpower : d.scale ^ (1 - 8 * sigma) ≤ d.scale := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hscale (show 1 - 8 * sigma ≤ 1 by linarith)
  have hfirstScale : d.Q1 ≤ d.scale := by
    calc
      _ ≤ d.U * d.scale ^ (-sigma) := hfirst.le
      _ ≤ d.U * 1 := mul_le_mul_of_nonneg_left hsmall hU0
      _ = d.U := mul_one _
      _ ≤ d.scale := hUscale
  have hsecond : d.Q2 ≤ d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by
    calc
      _ ≤ d.U ^ 2 * d.Q2 := le_mul_of_one_le_left hQ20 hU2
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hQ20) hQ32
  have hU2Q2 : 1 ≤ d.U ^ 2 * d.Q2 := by
    simpa only [one_mul] using mul_le_mul hU2 hQ2 zero_le_one (zero_le_one.trans hU2)
  have hthird : d.Q3 ≤ d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by
    calc
      _ ≤ d.Q3 ^ 2 := by
        simpa only [mul_one, pow_two] using
          mul_le_mul_of_nonneg_left hQ3 (zero_le_one.trans hQ3)
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) hU2Q2
  exact ⟨hfirstScale, hsecond.trans (hgeometry.le.trans hpower),
    hthird.trans (hgeometry.le.trans hpower)⟩

private theorem harmonic_envelope_log_bound {X Q : ℝ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X) (hQ : 1 ≤ Q) (hQX : Q ≤ X) :
    1 + Real.log (2 * Q) ≤ 3 * Real.log X := by
  have hh := Real.log_le_log (by linarith : 0 < 2 * Q)
    (mul_le_mul_of_nonneg_left hQX (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX.ne'] at hh
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

private theorem divisor_moment_log_payment {X Q1 Q2 Q3 : ℝ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X)
    (hQ1 : 1 ≤ Q1) (hQ2 : 1 ≤ Q2) (hQ3 : 1 ≤ Q3)
    (hQ1X : Q1 ≤ X) (hQ2X : Q2 ≤ X) (hQ3X : Q3 ≤ X)
    (a b c : ℕ) :
    ((1 + Real.log (2 * Q1)) ^ a / Q1) *
        ((1 + Real.log (2 * Q2)) ^ b * (1 + Real.log (2 * Q3)) ^ b) *
        ((1 + Real.log (2 * Q2)) ^ c * (1 + Real.log (2 * Q3)) ^ c) ≤
      3 ^ (a + 2 * (b + c)) * (Real.log X) ^ (a + 2 * (b + c)) / Q1 := by
  have h1 := harmonic_envelope_log_bound hX hlog hQ1 hQ1X
  have h2 := harmonic_envelope_log_bound hX hlog hQ2 hQ2X
  have h3 := harmonic_envelope_log_bound hX hlog hQ3 hQ3X
  have hn1 : 0 ≤ 1 + Real.log (2 * Q1) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * Q1 by linarith)]
  have hn2 : 0 ≤ 1 + Real.log (2 * Q2) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * Q2 by linarith)]
  have hn3 : 0 ≤ 1 + Real.log (2 * Q3) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * Q3 by linarith)]
  have hright : 0 ≤ 3 * Real.log X := by linarith
  calc
    _ ≤ ((3 * Real.log X) ^ a / Q1) *
        ((3 * Real.log X) ^ b * (3 * Real.log X) ^ b) *
        ((3 * Real.log X) ^ c * (3 * Real.log X) ^ c) := by
      gcongr
    _ = _ := by
      simp only [mul_pow, pow_add, pow_mul, pow_two, div_eq_mul_inv]
      ring

end SharedFirstFactorLowConductorAggregate

open SharedFirstFactorLowConductorAggregate

theorem uniformAuxiliarySW_sharedFirstFactorLowConductorZero
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1 / 100)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A L : ℝ, 0 < A → 0 ≤ L →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i : ι, x0 ≤ (F i).scale →
          ‖(F i).sharedFirstFactorLowConductorZero
              ((Real.log (F i).scale) ^ L)‖ ≤
            C * (F i).V * (F i).U ^ 2 /
              ((F i).Q1 * (Real.log (F i).scale) ^ A) := by
  intro A L hA hL
  let D : ℕ := 2 ^ (2 * C0 + 1) + 2 * (2 ^ (C0 + 1) + 2 ^ C0)
  let E0 : ℝ := (A + (D : ℝ) + 2 * L) / 2
  have hE0 : 0 < E0 := by dsimp only [E0]; positivity
  obtain ⟨Csw, hCsw, xSW, hxSW, hLow⟩ :=
    uniformAuxiliarySW_lowConductor_auxiliaryCharacterSum F B C0 sigma kappa c0
      hadmissible hSW E0 L hE0 hL
  let C : ℝ := (1 + |CommonSmoothCutoff.cutoffMass|) * Csw ^ 2 * (3 : ℝ) ^ D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, max xSW (Real.exp 1),
    hxSW.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  let d := F i
  have hd : MediumAdmissible B sigma kappa c0 d := hadmissible i
  have hsigmaBoth : 0 < sigma ∧ sigma < 1 / 100 := ⟨hsigma, hsigma_small⟩
  have hU0 : 0 ≤ d.U := zero_le_one.trans hd.1
  have hV0 : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hQ10 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hxSW' : xSW ≤ d.scale := (le_max_left xSW (Real.exp 1)).trans hx
  have hExp : Real.exp 1 ≤ d.scale := (le_max_right xSW (Real.exp 1)).trans hx
  have hX : 0 < d.scale := (Real.exp_pos 1).trans_le hExp
  have hlog : 1 ≤ Real.log d.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExp
  have hlog0 : 0 < Real.log d.scale := zero_lt_one.trans_le hlog
  let R : ℝ := (Real.log d.scale) ^ L
  let E : ℝ := Csw / (Real.log d.scale) ^ E0
  have hR : 1 ≤ R := Real.one_le_rpow hlog hL
  have hE : 0 ≤ E := div_nonneg hCsw.le (Real.rpow_pos_of_pos hlog0 _).le
  have hpoint : ∀ k delta : ℕ, 1 ≤ k → 1 ≤ delta →
      ∀ chi : DirichletCharacter ℂ delta, chi ≠ 1 → (chi.conductor : ℝ) ≤ R →
        ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ≤
          E * d.U * divisorTau (k * delta) ^ C0 := by
    intro k delta hk hdelta chi hchi hcond
    calc
      _ ≤ Csw * d.U * (((k * delta).divisors.card : ℝ) ^ C0) /
          (Real.log d.scale) ^ E0 := hLow i hxSW' k delta hk hdelta chi hchi hcond
      _ = _ := by dsimp only [E, divisorTau]; ring
  have hfinite := finite_low_zero_bound hd hE hR hpoint
  have hgeometry := admissible_factor_scale_bounds hsigmaBoth.1 hd
  have hlogs := divisor_moment_log_payment hX hlog hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1
    hgeometry.1 hgeometry.2.1 hgeometry.2.2
    (2 ^ (2 * C0 + 1)) (2 ^ (C0 + 1)) (2 ^ C0)
  have hcoefficient : 0 ≤ |CommonSmoothCutoff.cutoffMass| * d.V * (E * d.U) ^ 2 * R ^ 2 := by
    positivity
  have hlogPay : ‖d.sharedFirstFactorLowConductorZero R‖ ≤
      |CommonSmoothCutoff.cutoffMass| * d.V * (E * d.U) ^ 2 * R ^ 2 *
        (3 ^ D * (Real.log d.scale) ^ D / d.Q1) := by
    calc
      _ ≤ _ := hfinite
      _ = (|CommonSmoothCutoff.cutoffMass| * d.V * (E * d.U) ^ 2 * R ^ 2) *
          (((1 + Real.log (2 * d.Q1)) ^ (2 ^ (2 * C0 + 1)) / d.Q1) *
            ((1 + Real.log (2 * d.Q2)) ^ (2 ^ (C0 + 1)) *
              (1 + Real.log (2 * d.Q3)) ^ (2 ^ (C0 + 1))) *
            ((1 + Real.log (2 * d.Q2)) ^ (2 ^ C0) *
              (1 + Real.log (2 * d.Q3)) ^ (2 ^ C0))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogs hcoefficient
  have hden : ((Real.log d.scale) ^ E0) ^ 2 =
      (Real.log d.scale) ^ A * (Real.log d.scale) ^ D *
        ((Real.log d.scale) ^ L) ^ 2 := by
    have hE0eq : E0 * 2 = A + (D : ℝ) + (L + L) := by dsimp only [E0]; ring
    calc
      _ = (Real.log d.scale) ^ (E0 * 2) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast hlog0.le E0 2).symm
      _ = (Real.log d.scale) ^ (A + (D : ℝ) + (L + L)) := by rw [hE0eq]
      _ = _ := by
        rw [Real.rpow_add hlog0 (A + (D : ℝ)) (L + L),
          Real.rpow_add hlog0 A (D : ℝ), Real.rpow_add hlog0 L L,
          Real.rpow_natCast]
        ring
  calc
    _ ≤ |CommonSmoothCutoff.cutoffMass| * d.V * (E * d.U) ^ 2 * R ^ 2 *
        (3 ^ D * (Real.log d.scale) ^ D / d.Q1) := hlogPay
    _ = |CommonSmoothCutoff.cutoffMass| * Csw ^ 2 * 3 ^ D * d.V * d.U ^ 2 /
        (d.Q1 * (Real.log d.scale) ^ A) := by
      dsimp only [E, R]
      rw [mul_pow, div_pow, hden]
      field_simp [(Real.rpow_pos_of_pos hlog0 A).ne',
        (Real.rpow_pos_of_pos hlog0 L).ne',
        (pow_pos hlog0 D).ne', hQ10.ne']
    _ ≤ C * d.V * d.U ^ 2 / (d.Q1 * (Real.log d.scale) ^ A) := by
      apply div_le_div_of_nonneg_right _
        (mul_nonneg hQ10.le (Real.rpow_pos_of_pos hlog0 A).le)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg d.U)
      apply mul_le_mul_of_nonneg_right _ hV0
      dsimp only [C]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) D)
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg CommonSmoothCutoff.cutoffMass])
        (sq_nonneg Csw)

end

end ImbalancedChen.Part3
