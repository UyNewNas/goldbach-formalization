import ImbalancedChen.Part3SharedFirstFactorDispersion
import ImbalancedChen.Part3TransposedZeroCovariance

/-!
# Finite characters for the actual shared-first-factor zero covariance

Every first factor p is shared by the two full remaining factor labels.
The auxiliary sieves v1/gcd(v1,v2) and v2/gcd(v1,v2) stay in the two
character sums. The principal character gives the original complete
coprime masses at p*v1 and p*v2, including their nonunit exclusions.

The local Fourier-zero cutoffMass is retained. The last normalization
is an exact equality with weight V/(p^2*d*L), relative to the usual
(p*d)/phi(p*d) character weight. No large-sieve estimate, conductor
decomposition, roughness correction, or zero-mode payment is supplied.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

namespace SharedFirstFactorCharacterDictionary

open TransposedZeroCovariance

/-- The auxiliary coprime sieve is part of the actual coefficient. -/
def auxiliaryCharacterSum (N : Finset ℕ) (alpha : ℕ → ℂ) (k delta : ℕ)
    (chi : DirichletCharacter ℂ delta) : ℂ :=
  ∑ n ∈ N, if n.Coprime k then alpha n * star (chi (n : ZMod delta)) else 0

private theorem character_star_inverse {delta : ℕ} [NeZero delta]
    (chi : DirichletCharacter ℂ delta) {a : ZMod delta} (ha : IsUnit a) :
    star (chi a) = chi a⁻¹ := by
  obtain ⟨u, rfl⟩ := ha
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

/- This is the finite orthogonality argument in the fixed Multiplicative
provider, using the already reachable mathlib inverse-character API. -/
private theorem character_orthogonality {delta : ℕ} (hdelta : 0 < delta)
    (a b : ZMod delta) :
    (∑ chi : DirichletCharacter ℂ delta, star (chi a) * chi b) =
      if IsUnit a ∧ IsUnit b ∧ a = b then (delta.totient : ℂ) else 0 := by
  let : NeZero delta := ⟨hdelta.ne'⟩
  have hexp : Monoid.exponent (ZMod delta)ˣ ≠ 0 := Monoid.exponent_ne_zero.mpr
    (Monoid.ExponentExists.of_finite (G := (ZMod delta)ˣ))
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod delta)ˣ) := by
    let : NeZero (Monoid.exponent (ZMod delta)ˣ) := ⟨hexp⟩
    refine { prim := ?_, cyc := ?_ }
    · exact ⟨Complex.exp (2 * Real.pi * Complex.I /
        (Monoid.exponent (ZMod delta)ˣ : ℂ)),
        Complex.isPrimitiveRoot_exp (Monoid.exponent (ZMod delta)ˣ) hexp⟩
    · infer_instance
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · calc
        _ = ∑ chi : DirichletCharacter ℂ delta, chi a⁻¹ * chi b := by
          apply Finset.sum_congr rfl
          intro chi _
          rw [character_star_inverse chi ha]
        _ = if a = b then (delta.totient : ℂ) else 0 :=
          DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
        _ = _ := by simp only [ha, hb, true_and]
    · rw [if_neg (fun h ↦ hb h.2.1)]
      apply Finset.sum_eq_zero
      intro chi _
      rw [chi.map_nonunit hb, mul_zero]
  · rw [if_neg (fun h ↦ ha h.1)]
    apply Finset.sum_eq_zero
    intro chi _
    rw [chi.map_nonunit ha, star_zero, zero_mul]

private theorem character_orthogonality_nat {delta : ℕ} (hdelta : 0 < delta)
    (n m : ℕ) :
    (∑ chi : DirichletCharacter ℂ delta,
      star (chi (n : ZMod delta)) * chi (m : ZMod delta)) =
      if n.Coprime delta ∧ m.Coprime delta ∧ Nat.ModEq delta n m then
        (delta.totient : ℂ) else 0 := by
  simpa only [ZMod.isUnit_iff_coprime, ZMod.natCast_eq_natCast_iff] using
    character_orthogonality hdelta (n : ZMod delta) (m : ZMod delta)

private theorem coprime_quotient {delta q n : ℕ} (hdq : delta ∣ q) :
    n.Coprime q ↔ n.Coprime (q / delta) ∧ n.Coprime delta := by
  constructor
  · intro h
    exact ⟨h.of_dvd_right (Nat.div_dvd_of_dvd hdq), h.of_dvd_right hdq⟩
  · rintro ⟨hk, hd⟩
    have h := hd.mul_right hk
    rwa [Nat.mul_div_cancel' hdq] at h

/-- The principal coefficient is the original full coprime mass. -/
theorem auxiliaryCharacterSum_principal (N : Finset ℕ) (alpha : ℕ → ℂ)
    {q delta : ℕ} (hdq : delta ∣ q) :
    auxiliaryCharacterSum N alpha (q / delta) delta 1 = coprimeMass N alpha q := by
  unfold auxiliaryCharacterSum coprimeMass
  apply Finset.sum_congr rfl
  intro n _
  by_cases hnq : n.Coprime q
  · obtain ⟨hnk, hnd⟩ := (coprime_quotient hdq).mp hnq
    rw [if_pos hnk, MulChar.one_apply ((ZMod.isUnit_iff_coprime n delta).mpr hnd),
      star_one, mul_one, if_pos hnq]
  · by_cases hnk : n.Coprime (q / delta)
    · have hnd : ¬IsUnit (n : ZMod delta) := by
        intro hu
        exact hnq ((coprime_quotient hdq).mpr
          ⟨hnk, (ZMod.isUnit_iff_coprime n delta).mp hu⟩)
      rw [if_pos hnk, MulChar.map_nonunit _ hnd, star_zero, mul_zero, if_neg hnq]
    · rw [if_neg hnk, if_neg hnq]

/-- In the shared dictionary the principal mass has the full modulus
p*v, while the coefficient still has the quotient sieve v/gcd(v,w). -/
theorem auxiliaryCharacterSum_shared_principal (N : Finset ℕ) (alpha : ℕ → ℂ)
    {p : ℕ} (hp : 0 < p) (v w : ℕ) :
    auxiliaryCharacterSum N alpha (v / v.gcd w) (p * v.gcd w) 1 =
      coprimeMass N alpha (p * v) := by
  have hd : p * v.gcd w ∣ p * v := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left v w
    refine ⟨k, ?_⟩
    calc
      p * v = p * (v.gcd w * k) := congrArg (fun t : ℕ ↦ p * t) hk
      _ = p * v.gcd w * k := by ring
  simpa only [Nat.mul_div_mul_left _ _ hp] using
    auxiliaryCharacterSum_principal N alpha hd

private theorem sum_all_character_products (N : Finset ℕ) (alpha : ℕ → ℂ)
    {q r : ℕ} (hq : 0 < q) :
    (∑ chi : DirichletCharacter ℂ (q.gcd r),
      auxiliaryCharacterSum N alpha (q / q.gcd r) (q.gcd r) chi *
        star (auxiliaryCharacterSum N alpha (r / q.gcd r) (q.gcd r) chi)) =
      ((q.gcd r).totient : ℂ) * compatibleMass N alpha q r := by
  have hdelta := Nat.gcd_pos_of_pos_left r hq
  unfold auxiliaryCharacterSum compatibleMass
  simp only [star_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hnk : n.Coprime (q / q.gcd r)
  · by_cases hmk : m.Coprime (r / q.gcd r)
    · simp only [if_pos hnk, if_pos hmk, star_mul', star_star]
      have he : ComplexCRT.Compatible q r n m ↔
          n.Coprime (q.gcd r) ∧ m.Coprime (q.gcd r) ∧ Nat.ModEq (q.gcd r) n m := by
        constructor
        · intro h
          exact ⟨h.1.of_dvd_right (Nat.gcd_dvd_left q r),
            h.2.1.of_dvd_right (Nat.gcd_dvd_right q r), h.2.2⟩
        · rintro ⟨hn, hm, hc⟩
          exact ⟨(coprime_quotient (Nat.gcd_dvd_left q r)).mpr ⟨hnk, hn⟩,
            (coprime_quotient (Nat.gcd_dvd_right q r)).mpr ⟨hmk, hm⟩, hc⟩
      calc
        _ = alpha n * star (alpha m) *
            ∑ chi : DirichletCharacter ℂ (q.gcd r),
              star (chi (n : ZMod (q.gcd r))) * chi (m : ZMod (q.gcd r)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro chi _
          ring
        _ = _ := by
          rw [character_orthogonality_nat hdelta]
          by_cases hc : n.Coprime (q.gcd r) ∧ m.Coprime (q.gcd r) ∧
              Nat.ModEq (q.gcd r) n m
          · rw [if_pos hc, if_pos (he.mpr hc)]
            ring
          · simp only [if_neg hc, if_neg (fun h ↦ hc (he.mp h)), mul_zero]
    · have hc : ¬ComplexCRT.Compatible q r n m := by
        intro h
        exact hmk ((coprime_quotient (Nat.gcd_dvd_right q r)).mp h.2.1).1
      simp only [if_neg hmk, star_zero, mul_zero, Finset.sum_const_zero, if_neg hc]
  · have hc : ¬ComplexCRT.Compatible q r n m := by
      intro h
      exact hnk ((coprime_quotient (Nat.gcd_dvd_left q r)).mp h.1).1
    simp only [if_neg hnk, zero_mul, Finset.sum_const_zero, if_neg hc, mul_zero]

/-- Exact cross covariance: only the principal character is removed.
Both quotient sieves remain in the two original-alpha coefficients. -/
theorem covariance_eq_nonprincipal_characters (N : Finset ℕ) (alpha : ℕ → ℂ)
    {q r : ℕ} (hq : 0 < q) :
    covariance N alpha q r =
      (∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q.gcd r))).erase 1,
        auxiliaryCharacterSum N alpha (q / q.gcd r) (q.gcd r) chi *
          star (auxiliaryCharacterSum N alpha (r / q.gcd r) (q.gcd r) chi)) /
            ((q.gcd r).totient : ℂ) := by
  have hphi : ((q.gcd r).totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left r hq)).ne'
  have he := Finset.sum_erase_add (Finset.univ : Finset (DirichletCharacter ℂ (q.gcd r)))
    (fun chi ↦ auxiliaryCharacterSum N alpha (q / q.gcd r) (q.gcd r) chi *
      star (auxiliaryCharacterSum N alpha (r / q.gcd r) (q.gcd r) chi))
    (Finset.mem_univ 1)
  rw [sum_all_character_products N alpha hq,
    auxiliaryCharacterSum_principal N alpha (Nat.gcd_dvd_left q r),
    auxiliaryCharacterSum_principal N alpha (Nat.gcd_dvd_right q r)] at he
  rw [← covariance_identity N alpha hq]
  apply (eq_div_iff hphi).mpr
  calc
    _ = ((q.gcd r).totient : ℂ) * compatibleMass N alpha q r -
        coprimeMass N alpha q * star (coprimeMass N alpha r) := by
      field_simp
    _ = _ := (eq_sub_of_add_eq he).symm

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {p : ℕ}
    (hp : p ∈ factorCarrier Q) : 0 < p := by
  have hlo := (Finset.mem_Icc.mp hp).1
  have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

/- The three finite first-factor eliminations are the corresponding
coefficient reindexers of the owned shared-row leaf, without beta labels. -/
private theorem sum_slice_factor (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (f : ℕ → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).complexFactorLabels,
      (d.q1SliceAtom p).complexFactorGamma a * f (complexFactorModulus a)) =
      ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        (d.gamma2 u.1 * d.gamma3 u.2) * f (p * (u.1 * u.2)) := by
  simp only [MediumAtom.complexFactorLabels, Finset.sum_product]
  change (∑ q ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
    ∑ q3 ∈ factorCarrier d.Q3,
      ((if q = p then (1 : ℂ) else 0) * d.gamma2 q2 * d.gamma3 q3) *
        f (q * q2 * q3)) = _
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, one_mul, Nat.mul_assoc]
  · intro q _ hqp
    simp only [if_neg hqp, zero_mul, Finset.sum_const_zero]
  · intro hnot
    exact (hnot hp).elim

private theorem sum_star_slice_factor (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (f : ℕ → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).complexFactorLabels,
      star ((d.q1SliceAtom p).complexFactorGamma a) * f (complexFactorModulus a)) =
      ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        star (d.gamma2 u.1 * d.gamma3 u.2) * f (p * (u.1 * u.2)) := by
  calc
    _ = star (∑ a ∈ (d.q1SliceAtom p).complexFactorLabels,
        (d.q1SliceAtom p).complexFactorGamma a * star (f (complexFactorModulus a))) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (f (p * (u.1 * u.2)))) :=
      congrArg star (sum_slice_factor d hp (fun q ↦ star (f q)))
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem pair_sum_slice_factor (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (f : ℕ → ℕ → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).complexFactorLabels,
      ∑ b ∈ (d.q1SliceAtom p).complexFactorLabels,
        (d.q1SliceAtom p).complexFactorGamma a *
          star ((d.q1SliceAtom p).complexFactorGamma b) *
            f (complexFactorModulus a) (complexFactorModulus b)) =
      ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        ∑ v ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
          (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
            f (p * (u.1 * u.2)) (p * (v.1 * v.2)) := by
  calc
    _ = ∑ a ∈ (d.q1SliceAtom p).complexFactorLabels,
        (d.q1SliceAtom p).complexFactorGamma a *
          ∑ b ∈ (d.q1SliceAtom p).complexFactorLabels,
            star ((d.q1SliceAtom p).complexFactorGamma b) *
              f (complexFactorModulus a) (complexFactorModulus b) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        (d.gamma2 u.1 * d.gamma3 u.2) *
          ∑ b ∈ (d.q1SliceAtom p).complexFactorLabels,
            star ((d.q1SliceAtom p).complexFactorGamma b) *
              f (p * (u.1 * u.2)) (complexFactorModulus b) :=
      sum_slice_factor d hp (fun q ↦
        ∑ b ∈ (d.q1SliceAtom p).complexFactorLabels,
          star ((d.q1SliceAtom p).complexFactorGamma b) * f q (complexFactorModulus b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [sum_star_slice_factor d hp (fun r ↦ f (p * (u.1 * u.2)) r),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

/- Keep the ungrouped full complex labels at the primitive subtraction. -/
private theorem rawZero_sub_primitive_eq_factorCovariance
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain d =
      ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) *
        ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
          d.complexFactorGamma a * star (d.complexFactorGamma b) *
            (covariance d.alphaCarrier d.alpha (complexFactorModulus a)
              (complexFactorModulus b) /
                ((complexFactorModulus a).lcm (complexFactorModulus b) : ℂ)) := by
  have hpos {a : ℕ × ℕ × ℕ} (ha : a ∈ d.complexFactorLabels) :
      0 < complexFactorModulus a := by
    exact (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
      (Finset.mem_image_of_mem _ ha))).1
  rw [actual_rawZero_eq_compatibleMass, primitiveZeroMain, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [totient_pair_density_eq_lcm (hpos ha).ne' (hpos hb).ne',
    ← covariance_identity _ _ (hpos ha)]
  ring

end SharedFirstFactorCharacterDictionary

open SharedFirstFactorCharacterDictionary TransposedZeroCovariance

/-- Full original-alpha covariance after the exact shared-p deletion.
The three gamma labels are not grouped or replaced by absolute values. -/
theorem MediumAtom.q1SliceZero_sub_primitive_eq_factorCovariance
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    (d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
        primitiveZeroMain (d.q1SliceAtom p) =
      ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) *
        ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
          ∑ v ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
            (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
              (covariance d.alphaCarrier d.alpha (p * (u.1 * u.2))
                (p * (v.1 * v.2)) /
                  ((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ)) := by
  rw [SharedFirstFactorCharacterDictionary.rawZero_sub_primitive_eq_factorCovariance
    (mediumAdmissible_q1SliceAtom hd hp)]
  change ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) *
    (∑ a ∈ (d.q1SliceAtom p).complexFactorLabels,
      ∑ b ∈ (d.q1SliceAtom p).complexFactorLabels,
        (d.q1SliceAtom p).complexFactorGamma a *
          star ((d.q1SliceAtom p).complexFactorGamma b) *
            (covariance d.alphaCarrier d.alpha (complexFactorModulus a)
              (complexFactorModulus b) /
                ((complexFactorModulus a).lcm (complexFactorModulus b) : ℂ))) = _
  have he := congrArg (fun z : ℂ ↦
    ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) * z)
    (SharedFirstFactorCharacterDictionary.pair_sum_slice_factor d
      (Finset.mem_filter.mp hp).1 (fun q r ↦
        covariance d.alphaCarrier d.alpha q r / (q.lcm r : ℂ)))
  simpa only [sharedFirstFactor_lcm] using he

/-- The exact character dictionary, with both actual quotient sieves.
The first physical factor is arbitrary composite, and remains shared. -/
theorem MediumAtom.q1SliceZero_sub_primitive_eq_characters
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    (d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
        primitiveZeroMain (d.q1SliceAtom p) =
      ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        ∑ v ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
          (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
            (((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ) *
              ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ))) *
            (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
            (∑ chi ∈ (Finset.univ : Finset
                (DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)))).erase 1,
              auxiliaryCharacterSum d.alphaCarrier d.alpha
                ((u.1 * u.2) / (u.1 * u.2).gcd (v.1 * v.2))
                (p * (u.1 * u.2).gcd (v.1 * v.2)) chi *
              star (auxiliaryCharacterSum d.alphaCarrier d.alpha
                ((v.1 * v.2) / (u.1 * u.2).gcd (v.1 * v.2))
                (p * (u.1 * u.2).gcd (v.1 * v.2)) chi)) := by
  have hp0 := SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.1
    (Finset.mem_filter.mp hp).1
  rw [d.q1SliceZero_sub_primitive_eq_factorCovariance hd hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hu0 : 0 < u.1 * u.2 := Nat.mul_pos
    (SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.2.1 (Finset.mem_product.mp hu).1)
    (SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.2.2.1 (Finset.mem_product.mp hu).2)
  rw [covariance_eq_nonprincipal_characters d.alphaCarrier d.alpha (Nat.mul_pos hp0 hu0),
    sharedFirstFactor_gcd, Nat.mul_div_mul_left _ _ hp0, Nat.mul_div_mul_left _ _ hp0]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact weight relative to the weighted primitive large-sieve measure.
This algebraic identity is not an invocation of that analytic estimate. -/
theorem sharedCharacterWeight_normalization (z : ℂ) {p D L : ℕ}
    (hp : 0 < p) (hD : 0 < D) (hL : 0 < L) :
    z / (((p * L : ℕ) : ℂ) * ((p * D).totient : ℂ)) =
      (z / ((p ^ 2 * D * L : ℕ) : ℂ)) *
        (((p * D : ℕ) : ℂ) / ((p * D).totient : ℂ)) := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hD' : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hL' : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hphi : ((p * D).totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.mul_pos hp hD)).ne'
  push_cast
  field_simp [hp', hD', hL', hphi]

/-- The complete actual p sum retains the second inverse p and the
literal local mass. No frequency, conductor or coefficient is discarded. -/
theorem MediumAtom.sharedZero_sub_primitive_eq_weighted_characters
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ p ∈ d.primitiveFirstFactorCarrier,
      ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
        primitiveZeroMain (d.q1SliceAtom p))) =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        (∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
          ∑ v ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
            ((((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
              ((p ^ 2 * (u.1 * u.2).gcd (v.1 * v.2) *
                (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ)) *
              (((p * (u.1 * u.2).gcd (v.1 * v.2) : ℕ) : ℂ) /
                ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ))) *
              (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
              (∑ chi ∈ (Finset.univ : Finset
                  (DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)))).erase 1,
                auxiliaryCharacterSum d.alphaCarrier d.alpha
                  ((u.1 * u.2) / (u.1 * u.2).gcd (v.1 * v.2))
                  (p * (u.1 * u.2).gcd (v.1 * v.2)) chi *
                star (auxiliaryCharacterSum d.alphaCarrier d.alpha
                  ((v.1 * v.2) / (u.1 * u.2).gcd (v.1 * v.2))
                  (p * (u.1 * u.2).gcd (v.1 * v.2)) chi))) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [d.q1SliceZero_sub_primitive_eq_characters hd hp]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hp0 := SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.1
    (Finset.mem_filter.mp hp).1
  have hu0 : 0 < u.1 * u.2 := Nat.mul_pos
    (SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.2.1 (Finset.mem_product.mp hu).1)
    (SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.2.2.1 (Finset.mem_product.mp hu).2)
  have hv0 : 0 < v.1 * v.2 := Nat.mul_pos
    (SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.2.1 (Finset.mem_product.mp hv).1)
    (SharedFirstFactorCharacterDictionary.factor_pos hd.2.2.2.2.1 (Finset.mem_product.mp hv).2)
  rw [sharedCharacterWeight_normalization _ hp0
    (Nat.gcd_pos_of_pos_left _ hu0)
    (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hu0.ne' hv0.ne'))]

end

end ImbalancedChen.Part3
