import ImbalancedChen.Part3ElementaryE1RealEndpoint
import ImbalancedChen.Part3SharedFirstFactorGeneralDRootPacket
import ImbalancedChen.Part3SharedFirstFactorSupportedCoreCauchy


/-!
SOURCEONLY 2026-10-22. Complete by-source candidate; NOT typechecked.
No Lean/lake/typechecker/CI execution. Exact gate normalization and cost-one
finite reindex for the actual complete row. No spectral or smooth bound.
-/

namespace ImbalancedChen.Part3
noncomputable section
open Classical Finset CommonSmoothCutoff
open scoped BigOperators

namespace GeneralDGateNormalization

abbrev OuterIndex := (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)

def quotient (r D : ℕ) : ℕ := D / r.gcd D
def reducedLeft (r D : ℕ) : ℕ := r / r.gcd D

def originalGate (p r w D N1 N2 s : ℕ) : Prop :=
  (r * s).gcd w = D ∧ ComplexCRT.Compatible (p * (r * s)) (p * w) N1 N2

def outerGate (p r w D N1 N2 : ℕ) : Prop :=
  (reducedLeft r D).Coprime (w / D) ∧
    N1.Coprime (p * r * quotient r D) ∧
    N2.Coprime (p * w) ∧ Nat.ModEq (p * D) N1 N2

/-- These are arithmetic consequences, not extra normalization premises. -/
theorem quotient_data {r D : ℕ} (hr : 0 < r) (hD : 0 < D) :
    0 < quotient r D ∧ 0 < reducedLeft r D ∧
      (reducedLeft r D).Coprime (quotient r D) ∧
      r.gcd D * quotient r D = D ∧
      r.gcd D * reducedLeft r D = r := by
  have hd : 0 < r.gcd D := Nat.gcd_pos_of_pos_left D hr
  have hdD := Nat.gcd_dvd_right r D
  have hdr := Nat.gcd_dvd_left r D
  exact ⟨Nat.div_pos (Nat.le_of_dvd hD hdD) hd,
    Nat.div_pos (Nat.le_of_dvd hr hdr) hd,
    Nat.coprime_div_gcd_div_gcd hd,
    Nat.mul_div_cancel' hdD, Nat.mul_div_cancel' hdr⟩

/-- Gcd equality itself gives divisibility by q, even when D does not divide r. -/
theorem gcd_gate_iff {r w D s : ℕ} (hr : 0 < r) (hD : 0 < D)
    (hDw : D ∣ w) :
    (r * s).gcd w = D ↔
      quotient r D ∣ s ∧
        (reducedLeft r D * (s / quotient r D)).Coprime (w / D) := by
  obtain ⟨hq, hr0, hrq, hDfact, hrfact⟩ := quotient_data hr hD
  have hwfact : D * (w / D) = w := Nat.mul_div_cancel' hDw
  have hprod (hs : quotient r D ∣ s) :
      r * s = D * (reducedLeft r D * (s / quotient r D)) := by
    have hsfact : quotient r D * (s / quotient r D) = s :=
      Nat.mul_div_cancel' hs
    calc
      r * s = (r.gcd D * reducedLeft r D) *
          (quotient r D * (s / quotient r D)) := by rw [hrfact, hsfact]
      _ = (r.gcd D * quotient r D) *
          (reducedLeft r D * (s / quotient r D)) := by ring
      _ = _ := by rw [hDfact]
  constructor
  · intro hg
    have hDdiv : D ∣ r * s := by rw [← hg]; exact Nat.gcd_dvd_left _ _
    have hqdiv : quotient r D ∣ reducedLeft r D * s := by
      apply Nat.dvd_of_mul_dvd_mul_left (Nat.gcd_pos_of_pos_left D hr)
      simpa only [← mul_assoc, hDfact, hrfact] using hDdiv
    have hqs : quotient r D ∣ s := hrq.symm.dvd_of_dvd_mul_left hqdiv
    refine ⟨hqs, ?_⟩
    change (reducedLeft r D * (s / quotient r D)).gcd (w / D) = 1
    apply Nat.mul_left_cancel hD
    rw [← Nat.gcd_mul_left, ← hprod hqs, hwfact, hg, mul_one]
  · rintro ⟨hqs, hc⟩
    calc
      (r * s).gcd w =
          (D * (reducedLeft r D * (s / quotient r D))).gcd (D * (w / D)) := by
        rw [← hprod hqs, hwfact]
      _ = D * (reducedLeft r D * (s / quotient r D)).gcd (w / D) :=
        Nat.gcd_mul_left _ _ _
      _ = D := by rw [hc, mul_one]

/-- Exact iff: the only remaining inner gate is a single unit condition. -/
theorem originalGate_iff {p r w D N1 N2 s : ℕ}
    (hr : 0 < r) (hD : 0 < D) (hDw : D ∣ w) :
    originalGate p r w D N1 N2 s ↔
      quotient r D ∣ s ∧ outerGate p r w D N1 N2 ∧
        (s / quotient r D).Coprime (N1 * (w / D)) := by
  constructor
  · rintro ⟨hg, hc⟩
    obtain ⟨hqs, hunit⟩ := (gcd_gate_iff hr hD hDw).mp hg
    obtain ⟨hrw, htw⟩ := Nat.coprime_mul_iff_left.mp hunit
    have hsfact : quotient r D * (s / quotient r D) = s :=
      Nat.mul_div_cancel' hqs
    have hfirst : p * (r * s) = (p * r * quotient r D) * (s / quotient r D) := by
      calc
        p * (r * s) = p * (r * (quotient r D * (s / quotient r D))) := by rw [hsfact]
        _ = _ := by ring
    have hN := hc.1
    rw [hfirst] at hN
    obtain ⟨hNo, hNt⟩ := Nat.coprime_mul_iff_right.mp hN
    have hmod : Nat.ModEq (p * D) N1 N2 := by
      have hm := hc.2.2
      simpa only [Nat.gcd_mul_left, hg] using hm
    exact ⟨hqs, ⟨hrw, hNo, hc.2.1, hmod⟩, hNt.symm.mul_right htw⟩
  · rintro ⟨hqs, ho, ht⟩
    obtain ⟨hrw, hNo, hN2, hmod⟩ := ho
    obtain ⟨htN, htw⟩ := Nat.coprime_mul_iff_right.mp ht
    have hg : (r * s).gcd w = D :=
      (gcd_gate_iff hr hD hDw).mpr ⟨hqs, hrw.mul_left htw⟩
    have hsfact : quotient r D * (s / quotient r D) = s :=
      Nat.mul_div_cancel' hqs
    have hfirst : p * (r * s) = (p * r * quotient r D) * (s / quotient r D) := by
      calc
        p * (r * s) = p * (r * (quotient r D * (s / quotient r D))) := by rw [hsfact]
        _ = _ := by ring
    refine ⟨hg, ?_⟩
    change N1.Coprime (p * (r * s)) ∧ N2.Coprime (p * w) ∧
      Nat.ModEq ((p * (r * s)).gcd (p * w)) N1 N2
    refine ⟨?_, hN2, ?_⟩
    · rw [hfirst]
      exact hNo.mul_right htN.symm
    · simpa only [Nat.gcd_mul_left, hg] using hmod

/-- The exact quotient image of the original interval, with the residual unit mask.
No endpoint rounding or enlargement is used. -/
def normalizedCarrier (S : Finset ℕ) (r w D N1 : ℕ) : Finset ℕ :=
  ((S.filter (fun s => quotient r D ∣ s)).image (fun s => s / quotient r D)).filter
    (fun t => t.Coprime (N1 * (w / D)))

theorem mem_normalizedCarrier {S : Finset ℕ} {r w D N1 t : ℕ}
    (hq : 0 < quotient r D) :
    t ∈ normalizedCarrier S r w D N1 ↔
      quotient r D * t ∈ S ∧ t.Coprime (N1 * (w / D)) := by
  constructor
  · intro ht
    obtain ⟨him, hunit⟩ := mem_filter.mp ht
    obtain ⟨s, hs, heq⟩ := mem_image.mp him
    obtain ⟨hsS, hdiv⟩ := mem_filter.mp hs
    refine ⟨?_, hunit⟩
    rw [← heq, Nat.mul_div_cancel' hdiv]
    exact hsS
  · rintro ⟨hs, hunit⟩
    refine mem_filter.mpr ⟨?_, hunit⟩
    refine mem_image.mpr ⟨quotient r D * t,
      mem_filter.mpr ⟨hs, dvd_mul_right _ _⟩, ?_⟩
    exact Nat.mul_div_cancel_left t hq

/-- Arbitrary original finite payload: the map is bijective and costs exactly one. -/
theorem sum_gate_reindex {p r w D N1 N2 : ℕ}
    (hr : 0 < r) (hD : 0 < D) (hDw : D ∣ w)
    (S : Finset ℕ) (F : ℕ → ℂ) :
    (∑ s ∈ S, if originalGate p r w D N1 N2 s then F s else 0) =
      if outerGate p r w D N1 N2 then
        ∑ t ∈ normalizedCarrier S r w D N1, F (quotient r D * t)
      else 0 := by
  have hq := (quotient_data hr hD).1
  have hfilter :
      (∑ s ∈ S, if originalGate p r w D N1 N2 s then F s else 0) =
        ∑ s ∈ S.filter (originalGate p r w D N1 N2), F s := by
    rw [sum_filter]
  rw [hfilter]
  by_cases ho : outerGate p r w D N1 N2
  · rw [if_pos ho]
    symm
    refine Finset.sum_bij (fun t _ => quotient r D * t) ?_ ?_ ?_ ?_
    · intro t ht
      obtain ⟨hs, hu⟩ := (mem_normalizedCarrier hq).mp ht
      refine mem_filter.mpr ⟨hs, (originalGate_iff hr hD hDw).mpr ?_⟩
      refine ⟨dvd_mul_right _ _, ho, ?_⟩
      simpa only [Nat.mul_div_cancel_left t hq] using hu
    · intro t ht t' ht' heq
      exact Nat.eq_of_mul_eq_mul_left hq heq
    · intro s hs
      obtain ⟨hsS, hsG⟩ := mem_filter.mp hs
      obtain ⟨hdiv, _, hu⟩ := (originalGate_iff hr hD hDw).mp hsG
      refine ⟨s / quotient r D, (mem_normalizedCarrier hq).mpr ?_,
        Nat.mul_div_cancel' hdiv⟩
      exact ⟨by simpa only [Nat.mul_div_cancel' hdiv] using hsS, hu⟩
    · intro t ht
      rfl
  · rw [if_neg ho]
    apply sum_eq_zero
    intro s hs
    exact (ho ((originalGate_iff hr hD hDw).mp (mem_filter.mp hs).2).2.1).elim

/-- Exact lcm normalization on the quotient carrier; no reciprocal phase is dropped. -/
theorem normalized_lcm {p r w D N1 N2 t : ℕ}
    (hr : 0 < r) (hD : 0 < D) (hDw : D ∣ w)
    (ho : outerGate p r w D N1 N2)
    (ht : t.Coprime (N1 * (w / D))) :
    (p * (r * (quotient r D * t))).lcm (p * w) =
      (p * D) * (reducedLeft r D * t) * (w / D) := by
  obtain ⟨hq, hr0, hrq, hDfact, hrfact⟩ := quotient_data hr hD
  have hwfact : D * (w / D) = w := Nat.mul_div_cancel' hDw
  have hunit : (reducedLeft r D * t).Coprime (w / D) :=
    ho.1.mul_left (Nat.coprime_mul_iff_right.mp ht).2
  have hleft : p * (r * (quotient r D * t)) = (p * D) * (reducedLeft r D * t) := by
    calc
      _ = p * ((r.gcd D * reducedLeft r D) * (quotient r D * t)) := by rw [hrfact]
      _ = (p * (r.gcd D * quotient r D)) * (reducedLeft r D * t) := by ring
      _ = _ := by rw [hDfact]
  have hright : p * w = (p * D) * (w / D) := by rw [mul_assoc, hwfact]
  rw [hleft, hright, Nat.lcm_mul_left, hunit.lcm_eq_mul]
  simp only [mul_assoc]

/-- Original amplitude and real projection, with only the guard removed. -/
def literalPayload (e : MediumAtom) (Z : ℝ) (o : OuterIndex) (s : ℕ) (h : ℤ) : ℂ :=
  let q := o.1.1 * (o.2.1.1 * s)
  let q' := o.1.1 * (o.2.1.2.1 * o.2.1.2.2)
  let L := q.lcm q'
  e.gamma2 s *
    (((poissonSmoothLowPass ((e.V / (L : ℝ)) * (h : ℝ) / Z) : ℂ) *
      poissonNonzeroFrequency (e.V / (L : ℝ))
        ((ComplexCRT.residue q q' o.1.2.1 o.1.2.2 e.residue : ℝ) / (L : ℝ)) h).re : ℂ)

theorem rowTerm_eq (e : MediumAtom) (Z : ℝ) (o : OuterIndex) (s : ℕ) (h : ℤ) :
    e.smallCoreSquaredRowTerm Z o (s,h) =
      if originalGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2
          o.1.2.1 o.1.2.2 s then literalPayload e Z o s h else 0 := by
  exact if_congr Iff.rfl rfl rfl

def normalizedRow (e : MediumAtom) (Z : ℝ) (o : OuterIndex) : ℂ :=
  ∑ t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1,
    ∑ h ∈ poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z o.2.2),
      literalPayload e Z o (quotient o.2.1.1 o.2.2 * t) h

/-- Exact equality on each original complete row, retaining its original h-window. -/
theorem row_sum_eq_normalized (e : MediumAtom) (Z : ℝ) (o : OuterIndex)
    (hr : 0 < o.2.1.1) (hD : 0 < o.2.2)
    (hDw : o.2.2 ∣ o.2.1.2.1 * o.2.1.2.2) :
    (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o, e.smallCoreSquaredRowTerm Z o u) =
      if outerGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1 o.1.2.2
      then normalizedRow e Z o else 0 := by
  unfold MediumAtom.smallCoreSquaredInnerCarrier
  rw [sum_product]
  simp_rw [rowTerm_eq]
  have hsum :
      (∑ s ∈ factorCarrier e.Q2,
        ∑ h ∈ poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z o.2.2),
          if originalGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2
              o.1.2.1 o.1.2.2 s then literalPayload e Z o s h else 0) =
      ∑ s ∈ factorCarrier e.Q2,
        if originalGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2
            o.1.2.1 o.1.2.2 s then
          ∑ h ∈ poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z o.2.2),
            literalPayload e Z o s h else 0 := by
    apply sum_congr rfl
    intro s hs
    by_cases hg : originalGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2
        o.1.2.1 o.1.2.2 s
    · simp only [if_pos hg]
    · simp only [if_neg hg, sum_const_zero]
  rw [hsum]
  exact sum_gate_reindex hr hD hDw (factorCarrier e.Q2)
    (fun s => ∑ h ∈ poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z o.2.2),
      literalPayload e Z o s h)

/-- Carrier membership, rather than an activity premise, supplies D|w and D>0. -/
theorem outer_carrier_data (e : MediumAtom) (hR : 1 ≤ e.Q3) (o : OuterIndex)
    (ho : o ∈ e.smallCoreSquaredOuterCarrier) :
    0 < o.2.1.1 ∧ 0 < o.2.2 ∧ o.2.2 ∣ o.2.1.2.1 * o.2.1.2.2 := by
  change o ∈ ((e.primitiveFirstFactorCarrier ×ˢ
    (e.transposedAtom.betaCarrier ×ˢ e.transposedAtom.betaCarrier)).filter
      (fun t => t.2.1 ≠ t.2.2 ∧ Nat.ModEq t.1 t.2.1 t.2.2)) ×ˢ
    ((factorCarrier e.Q3) ×ˢ ((factorCarrier e.Q3) ×ˢ factorCarrier e.Q2)).biUnion
      (fun t => (t.2.1 * t.2.2).divisors.image (fun D => (t,D))) at ho
  obtain ⟨t, ht, hImage⟩ := mem_biUnion.mp (mem_product.mp ho).2
  obtain ⟨D, hDiv, heq⟩ := mem_image.mp hImage
  have htEq : t = o.2.1 := congrArg Prod.fst heq
  have hDEq : D = o.2.2 := congrArg Prod.snd heq
  rw [htEq] at ht hDiv
  rw [hDEq] at hDiv
  have hrMem : o.2.1.1 ∈ factorCarrier e.Q3 := (mem_product.mp ht).1
  have hlo := (mem_Icc.mp hrMem).1
  have hceil : 1 ≤ Nat.ceil e.Q3 := by exact_mod_cast hR.trans (Nat.le_ceil e.Q3)
  have hr : 0 < o.2.1.1 := by omega
  obtain ⟨hDw, hwne⟩ := Nat.mem_divisors.mp hDiv
  have hDne : o.2.2 ≠ 0 := by
    intro hz
    apply hwne
    simpa only [hz, zero_dvd_iff] using hDw
  exact ⟨hr, Nat.pos_of_ne_zero hDne, hDw⟩

/-- Actual supported complete row: all normalization premises come from its carrier. -/
theorem supported_row_sum_eq (e : MediumAtom) (hR : 1 ≤ e.Q3)
    (Ybeta Ysupport Z : ℝ) (o : OuterIndex)
    (ho : o ∈ e.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport) :
    (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o, e.smallCoreSquaredRowTerm Z o u) =
      if outerGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1 o.1.2.2
      then normalizedRow e Z o else 0 := by
  obtain ⟨hr,hD,hDw⟩ := outer_carrier_data e hR o
    ((e.mem_smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport o).mp ho).1
  exact row_sum_eq_normalized e Z o hr hD hDw

/-- No Cauchy or triangle loss: the complete positive mass has an exact expression. -/
theorem supported_mass_eq (e : MediumAtom) (hR : 1 ≤ e.Q3)
    (Ybeta Ysupport Z : ℝ) :
    e.smallCoreSquaredSupportedRowSquareMass Ybeta Ysupport Z =
      ∑ o ∈ e.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport,
        if outerGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1 o.1.2.2
        then ‖normalizedRow e Z o‖ ^ 2 else 0 := by
  unfold MediumAtom.smallCoreSquaredSupportedRowSquareMass
  apply sum_congr rfl
  intro o ho
  rw [supported_row_sum_eq e hR Ybeta Ysupport Z o ho]
  by_cases hg : outerGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1 o.1.2.2
  · simp only [if_pos hg]
  · simp only [if_neg hg, norm_zero, zero_pow (by omega : 2 ≠ 0)]

/-- Original cleaned admissibility supplies hR, with original supported cutoffs unchanged. -/
theorem actual_cleaned_supported_mass_eq
    (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom)
    (hd : MediumAdmissible B sigma kappa c0 d) (Z : ℝ) :
    let e := d.cleanedAlphaAtom
    let Y := d.scale ^ (sigma / 4)
    e.smallCoreSquaredSupportedRowSquareMass Y Y Z =
      ∑ o ∈ e.smallCoreSquaredSupportedOuterCarrier Y Y,
        if outerGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1 o.1.2.2
        then ‖normalizedRow e Z o‖ ^ 2 else 0 := by
  have he := mediumAdmissible_cleanedAlphaAtom hd
  exact supported_mass_eq d.cleanedAlphaAtom he.2.2.2.2.1
    (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) Z

end GeneralDGateNormalization
end
end ImbalancedChen.Part3


/-!
SOURCEONLY / UNCOMPILED. Quantitative actual active pair count.
This extension is preceded, in this new combined draft only, by the unchanged
GeneralDGateNormalization c9b24158 source-only candidate. No actual file edited.
No pair-count or final spectral estimate is assumed.
-/
namespace ImbalancedChen.Part3.GeneralDActivePairCountSourceOnly

noncomputable section
open Classical Finset GeneralDGateNormalization
open scoped BigOperators

/-- Both signs of NONZERO multiples, parameterized by positive quotients. -/
def nonzeroMultipleCarrier (N : ℝ) (m : ℕ) : Finset ℤ :=
  ((Icc 1 (Nat.floor (N / (m : ℝ)))).image
    (fun q : ℕ => (m : ℤ) * (q : ℤ))) ∪
  ((Icc 1 (Nat.floor (N / (m : ℝ)))).image
    (fun q : ℕ => -((m : ℤ) * (q : ℤ))))

theorem card_nonzeroMultipleCarrier_le (N : ℝ) (m : ℕ) :
    (nonzeroMultipleCarrier N m).card ≤ 2 * Nat.floor (N / (m : ℝ)) := by
  unfold nonzeroMultipleCarrier
  calc
    _ ≤ ((Icc 1 (Nat.floor (N / (m : ℝ)))).image
          (fun q : ℕ => (m : ℤ) * (q : ℤ))).card +
        ((Icc 1 (Nat.floor (N / (m : ℝ)))).image
          (fun q : ℕ => -((m : ℤ) * (q : ℤ)))).card := card_union_le _ _
    _ ≤ (Icc 1 (Nat.floor (N / (m : ℝ)))).card +
        (Icc 1 (Nat.floor (N / (m : ℝ)))).card :=
      Nat.add_le_add card_image_le card_image_le
    _ = _ := by simp only [Nat.card_Icc]; omega

theorem mem_nonzeroMultipleCarrier {N : ℝ} {m : ℕ} (hm : 0 < m)
    {z : ℤ} (hz : z ≠ 0) (hbound : (z.natAbs : ℝ) ≤ N)
    (hdiv : (m : ℤ) ∣ z) : z ∈ nonzeroMultipleCarrier N m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdivNat : m ∣ z.natAbs := Int.natCast_dvd.mp hdiv
  let q := z.natAbs / m
  have hzpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hzpos hdivNat) hm
  have heqNat : m * q = z.natAbs := Nat.mul_div_cancel' hdivNat
  have heqInt : (m : ℤ) * (q : ℤ) = (z.natAbs : ℤ) := by
    exact_mod_cast heqNat
  have hqmul : (q : ℝ) * (m : ℝ) = (z.natAbs : ℝ) := by
    have heq : (m : ℝ) * (q : ℝ) = (z.natAbs : ℝ) := by
      exact_mod_cast heqNat
    simpa only [mul_comm] using heq
  have hqbound : (q : ℝ) ≤ N / (m : ℝ) := by
    apply (le_div_iff₀ hmR).mpr
    rw [hqmul]
    exact hbound
  have hq : q ∈ Icc 1 (Nat.floor (N / (m : ℝ))) :=
    mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hqpos, Nat.le_floor hqbound⟩
  unfold nonzeroMultipleCarrier
  rcases Int.natAbs_eq z with hsign | hsign
  · exact mem_union.mpr (Or.inl (mem_image.mpr ⟨q, hq, heqInt.trans hsign.symm⟩))
  · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨q, hq, by
      rw [heqInt]
      exact hsign.symm⟩))

theorem natAbs_cast_real (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using
    congrArg (fun k : ℤ => (k : ℝ)) (Int.natCast_natAbs z)

theorem factorCarrier_bounds {N : ℝ} (hN : 1 ≤ N) {n : ℕ}
    (hn : n ∈ factorCarrier N) :
    0 < n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
  have hloR : N ≤ (n : ℝ) :=
    (Nat.le_ceil N).trans (by exact_mod_cast hlo)
  have hnOne : 1 ≤ n := by exact_mod_cast hN.trans hloR
  exact ⟨by omega, hloR,
    (show (n : ℝ) ≤ (Nat.floor (2 * N) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith))⟩

/-- The diagonal is excluded BEFORE counting the two quotient signs. -/
def congruenceFibre (N : ℝ) (m n1 : ℕ) : Finset ℕ :=
  (factorCarrier N).filter (fun n2 => n1 ≠ n2 ∧ Nat.ModEq m n1 n2)

theorem card_congruenceFibre_le {N : ℝ} (hN : 1 ≤ N)
    {m n1 : ℕ} (hm : 0 < m) (hn1 : n1 ∈ factorCarrier N) :
    (congruenceFibre N m n1).card ≤ 2 * Nat.floor (N / (m : ℝ)) := by
  have h1 := factorCarrier_bounds hN hn1
  calc
    _ ≤ (nonzeroMultipleCarrier N m).card := by
      apply card_le_card_of_injOn (fun n2 : ℕ => (n2 : ℤ) - (n1 : ℤ))
      · intro n2 hn2
        obtain ⟨hn2, hne, hmod⟩ := mem_filter.mp hn2
        have h2 := factorCarrier_bounds hN hn2
        apply mem_nonzeroMultipleCarrier hm
        · intro hz
          have heqI : (n2 : ℤ) = (n1 : ℤ) := sub_eq_zero.mp hz
          exact hne (Int.ofNat_inj.mp heqI).symm
        · rw [natAbs_cast_real]
          push_cast
          exact abs_le.mpr ⟨by linarith [h1.2.2, h2.2.1],
            by linarith [h1.2.1, h2.2.2]⟩
        · exact Nat.modEq_iff_dvd.mp hmod
      · intro a _ b _ hab
        have hsub : (a : ℤ) - (n1 : ℤ) = (b : ℤ) - (n1 : ℤ) := hab
        exact Int.ofNat_inj.mp (sub_left_inj.mp hsub)
    _ ≤ _ := card_nonzeroMultipleCarrier_le N m

theorem card_congruenceFibre_real_le {N : ℝ} (hN : 1 ≤ N)
    {m n1 : ℕ} (hm : 0 < m) (hn1 : n1 ∈ factorCarrier N) :
    ((congruenceFibre N m n1).card : ℝ) ≤ 2 * N / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    _ ≤ 2 * (Nat.floor (N / (m : ℝ)) : ℝ) := by
      exact_mod_cast card_congruenceFibre_le hN hm hn1
    _ ≤ 2 * (N / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Nat.floor_le (div_nonneg (by linarith) hmR.le)) (by norm_num)
    _ = _ := by ring

/-- Public positive-prefix count is reused; no private multiplicity lemma is named. -/
def firstMultiples (N : ℝ) (A : ℕ) : Finset ℕ :=
  (factorCarrier N).filter (fun n => A ∣ n)

theorem firstMultiples_card_le_two {N : ℝ} (hN : 1 ≤ N)
    {A : ℕ} (hA : 0 < A) :
    ((firstMultiples N A).card : ℝ) ≤ 2 * N / (A : ℝ) := by
  have _ := hA
  have hsub : firstMultiples N A ⊆
      (Ioc 0 (Nat.floor (2 * N))).filter (fun n => A ∣ n) := by
    intro n hn
    obtain ⟨hn, hdiv⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨(factorCarrier_bounds hN hn).1, (mem_Icc.mp hn).2⟩, hdiv⟩
  have hcard : (firstMultiples N A).card ≤ Nat.floor (2 * N) / A := by
    calc
      _ ≤ ((Ioc 0 (Nat.floor (2 * N))).filter (fun n => A ∣ n)).card :=
        card_le_card hsub
      _ = _ := Nat.Ioc_filter_dvd_card_eq_div _ _
  calc
    _ ≤ ((Nat.floor (2 * N) / A : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (Nat.floor (2 * N) : ℝ) / (A : ℝ) := Nat.cast_div_le
    _ ≤ 2 * N / (A : ℝ) :=
      div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) (Nat.cast_nonneg _)

/-- The requested 3N/A bound, including the short/nonempty boundary regime. -/
theorem firstMultiples_card_le_three {N : ℝ} (hN : 1 ≤ N)
    {A : ℕ} (hA : 0 < A) :
    ((firstMultiples N A).card : ℝ) ≤ 3 * N / (A : ℝ) := by
  calc
    _ ≤ 2 * N / (A : ℝ) := firstMultiples_card_le_two hN hA
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- Coprimality and pD congruence come from the literal active outer gate. -/
theorem outerGate_g_coprime_and_modEq
    {p r w D N1 N2 g : ℕ} (hDw : D ∣ w)
    (hgcd : N1.gcd N2 = g) (ho : outerGate p r w D N1 N2) :
    g.Coprime (p * D) ∧ Nat.ModEq (g * p * D) N1 N2 := by
  have hg1 : g ∣ N1 := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  have hg2 : g ∣ N2 := by rw [← hgcd]; exact Nat.gcd_dvd_right _ _
  have hgpD : g.Coprime (p * D) :=
    (ho.2.2.1.of_dvd_left hg2).of_dvd_right (Nat.mul_dvd_mul_left p hDw)
  have hmodg : Nat.ModEq g N1 N2 :=
    (Nat.modEq_zero_iff_dvd.mpr hg1).trans
      (Nat.modEq_zero_iff_dvd.mpr hg2).symm
  refine ⟨hgpD, ?_⟩
  simpa only [mul_assoc] using
    (Nat.modEq_and_modEq_iff_modEq_mul hgpD).mp ⟨hmodg, ho.2.2.2⟩

theorem outerGate_g_mul_dvd_signed_difference
    {p r w D N1 N2 g : ℕ} (hDw : D ∣ w)
    (hgcd : N1.gcd N2 = g) (ho : outerGate p r w D N1 N2) :
    ((g * p * D : ℕ) : ℤ) ∣ (N1 : ℤ) - (N2 : ℤ) := by
  exact Nat.modEq_iff_dvd.mp
    (outerGate_g_coprime_and_modEq hDw hgcd ho).2.symm

theorem supportedPart_forces_first_multiple
    {N1 N2 g d1 : ℕ} (hN1 : 0 < N1) (hg : 0 < g)
    (hgcd : N1.gcd N2 = g)
    (hd1 : CanonicalReciprocalData.supportedPart (N1 / g) g = d1) :
    g * d1 ∣ N1 := by
  have hg1 : g ∣ N1 := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  have hquot : 0 < N1 / g := Nat.div_pos (Nat.le_of_dvd hN1 hg1) hg
  have hd1div : d1 ∣ N1 / g := by
    rw [← hd1]
    exact CanonicalReciprocalData.supportedPart_dvd hquot g
  have hmul := Nat.mul_dvd_mul_left g hd1div
  rwa [Nat.mul_div_cancel' hg1] at hmul

/-- Inclusive original dyadic labels, exact gcd/supported-part, and real gate. -/
def pairSlice (N : ℝ) (p r w D g d1 : ℕ) : Finset (ℕ × ℕ) :=
  (factorCarrier N ×ˢ factorCarrier N).filter (fun n =>
    n.1 ≠ n.2 ∧ n.1.gcd n.2 = g ∧
      CanonicalReciprocalData.supportedPart (n.1 / g) g = d1 ∧
        outerGate p r w D n.1 n.2)

theorem mem_pairSlice_iff {N : ℝ} {p r w D g d1 : ℕ} {n : ℕ × ℕ} :
    n ∈ pairSlice N p r w D g d1 ↔
      n.1 ∈ factorCarrier N ∧ n.2 ∈ factorCarrier N ∧ n.1 ≠ n.2 ∧
        n.1.gcd n.2 = g ∧
          CanonicalReciprocalData.supportedPart (n.1 / g) g = d1 ∧
            outerGate p r w D n.1 n.2 := by
  simp only [pairSlice, mem_filter, mem_product, and_assoc]

/-- Every actual first label maps into gd1 multiples; no new hypothesis on pairs. -/
theorem pairSlice_first_mem {N : ℝ} (hN : 1 ≤ N)
    {p r w D g d1 : ℕ} (hg : 0 < g) {n : ℕ × ℕ}
    (hn : n ∈ pairSlice N p r w D g d1) :
    n.1 ∈ firstMultiples N (g * d1) := by
  obtain ⟨h1, _h2, _hne, hgc, hsup, _ho⟩ := mem_pairSlice_iff.mp hn
  exact mem_filter.mpr ⟨h1, supportedPart_forces_first_multiple
    (factorCarrier_bounds hN h1).1 hg hgc hsup⟩

/-- For EACH fixed N1 the genuine ordered-pair fibre costs 2 floor(N/gpD).
There is no diagonal label, no additive endpoint term, and both orders remain. -/
theorem pairSlice_fibre_card_le {N : ℝ} (hN : 1 ≤ N)
    {p r w D g d1 n1 : ℕ} (hp : 0 < p) (hD : 0 < D) (hg : 0 < g)
    (hDw : D ∣ w) (hn1 : n1 ∈ factorCarrier N) :
    ((pairSlice N p r w D g d1).filter (fun n => n.1 = n1)).card ≤
      2 * Nat.floor (N / ((g * p * D : ℕ) : ℝ)) := by
  have hm : 0 < g * p * D := Nat.mul_pos (Nat.mul_pos hg hp) hD
  calc
    _ ≤ (congruenceFibre N (g * p * D) n1).card := by
      apply card_le_card_of_injOn (fun n : ℕ × ℕ => n.2)
      · intro n hn
        obtain ⟨hn, hfirst⟩ := mem_filter.mp hn
        obtain ⟨_h1, h2, hne, hgc, _hsup, ho⟩ := mem_pairSlice_iff.mp hn
        refine mem_filter.mpr ⟨h2, ?_, ?_⟩
        · simpa only [hfirst] using hne
        · simpa only [hfirst] using
            (outerGate_g_coprime_and_modEq hDw hgc ho).2
      · intro a ha b hb hab
        exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) hab
    _ ≤ _ := card_congruenceFibre_le hN hm hn1

theorem pairSlice_fibre_real_le {N : ℝ} (hN : 1 ≤ N)
    {p r w D g d1 n1 : ℕ} (hp : 0 < p) (hD : 0 < D) (hg : 0 < g)
    (hDw : D ∣ w) (hn1 : n1 ∈ factorCarrier N) :
    (((pairSlice N p r w D g d1).filter (fun n => n.1 = n1)).card : ℝ) ≤
      2 * N / ((g * p * D : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < (g * p * D : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hg hp) hD
  calc
    _ ≤ 2 * (Nat.floor (N / ((g * p * D : ℕ) : ℝ)) : ℝ) := by
      exact_mod_cast pairSlice_fibre_card_le hN hp hD hg hDw hn1
    _ ≤ 2 * (N / ((g * p * D : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Nat.floor_le (div_nonneg (by linarith) hmR.le)) (by norm_num)
    _ = _ := by ring

/-- Quantitative requested pair bound, from the actual gate, not a premise. -/
theorem pairSlice_card_le {N : ℝ} (hN : 1 ≤ N)
    {p r w D g d1 : ℕ} (hp : 0 < p) (hD : 0 < D) (hg : 0 < g)
    (hd1 : 0 < d1) (hDw : D ∣ w) :
    ((pairSlice N p r w D g d1).card : ℝ) ≤
      6 * N ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (p : ℝ) * (D : ℝ)) := by
  have hmap : ∀ n ∈ pairSlice N p r w D g d1,
      n.1 ∈ firstMultiples N (g * d1) :=
    fun n hn => pairSlice_first_mem hN hg hn
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  have hA : 0 < g * d1 := Nat.mul_pos hg hd1
  have hbound : ∀ n1 ∈ firstMultiples N (g * d1),
      (((pairSlice N p r w D g d1).filter (fun n => n.1 = n1)).card : ℝ) ≤
        2 * N / ((g * p * D : ℕ) : ℝ) := by
    intro n1 hn1
    exact pairSlice_fibre_real_le hN hp hD hg hDw (mem_filter.mp hn1).1
  calc
    _ = ∑ n1 ∈ firstMultiples N (g * d1),
        (((pairSlice N p r w D g d1).filter (fun n => n.1 = n1)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _n1 ∈ firstMultiples N (g * d1),
        (2 * N / ((g * p * D : ℕ) : ℝ)) := sum_le_sum hbound
    _ = ((firstMultiples N (g * d1)).card : ℝ) *
        (2 * N / ((g * p * D : ℕ) : ℝ)) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (3 * N / ((g * d1 : ℕ) : ℝ)) *
        (2 * N / ((g * p * D : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (firstMultiples_card_le_three hN hA) (by positivity)
    _ = _ := by
      have hgR : (0 : ℝ) < g := by exact_mod_cast hg
      have hd1R : (0 : ℝ) < d1 := by exact_mod_cast hd1
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp
      have hDR : (0 : ℝ) < D := by exact_mod_cast hD
      push_cast
      field_simp [ne_of_gt hgR, ne_of_gt hd1R, ne_of_gt hpR, ne_of_gt hDR]; ring

/-- Bind the count literally to the transposed paired carrier in actual Co. -/
def actualPairSlice (e : MediumAtom) (p r w D g d1 : ℕ) : Finset (ℕ × ℕ) :=
  (e.transposedAtom.betaCarrier ×ˢ e.transposedAtom.betaCarrier).filter (fun n =>
    n.1 ≠ n.2 ∧ n.1.gcd n.2 = g ∧
      CanonicalReciprocalData.supportedPart (n.1 / g) g = d1 ∧
        outerGate p r w D n.1 n.2)

theorem actualPairSlice_eq (e : MediumAtom) (p r w D g d1 : ℕ) :
    actualPairSlice e p r w D g d1 = pairSlice e.U p r w D g d1 := rfl

theorem actualPairSlice_card_le (e : MediumAtom) (hN : 1 ≤ e.U)
    {p r w D g d1 : ℕ} (hp : 0 < p) (hD : 0 < D) (hg : 0 < g)
    (hd1 : 0 < d1) (hDw : D ∣ w) :
    ((actualPairSlice e p r w D g d1).card : ℝ) ≤
      6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (p : ℝ) * (D : ℝ)) := by
  rw [actualPairSlice_eq]
  exact pairSlice_card_le hN hp hD hg hd1 hDw

/-- Keep the original alpha interval instead of assuming it can be erased. -/
def alphaPairSlice (e : MediumAtom) (p r w D g d1 : ℕ) : Finset (ℕ × ℕ) :=
  (actualPairSlice e p r w D g d1).filter
    (fun n => n.1 ∈ e.alphaCarrier ∧ n.2 ∈ e.alphaCarrier)

theorem alphaPairSlice_card_le (e : MediumAtom) (hN : 1 ≤ e.U)
    {p r w D g d1 : ℕ} (hp : 0 < p) (hD : 0 < D) (hg : 0 < g)
    (hd1 : 0 < d1) (hDw : D ∣ w) :
    ((alphaPairSlice e p r w D g d1).card : ℝ) ≤
      6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (p : ℝ) * (D : ℝ)) := by
  calc
    _ ≤ ((actualPairSlice e p r w D g d1).card : ℝ) := by
      exact_mod_cast card_le_card (filter_subset
        (fun n : ℕ × ℕ => n.1 ∈ e.alphaCarrier ∧ n.2 ∈ e.alphaCarrier)
        (actualPairSlice e p r w D g d1))
    _ ≤ _ := actualPairSlice_card_le e hN hp hD hg hd1 hDw

/-- Every original Co-supported active outer label really lands in this count,
including BOTH original alpha interval masks. No arbitrary pair map is supplied. -/
theorem supported_active_pair_mem_alphaPairSlice
    (e : MediumAtom) (Ybeta Ysupport : ℝ) (o : OuterIndex)
    (ho : o ∈ e.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport)
    (hgate : outerGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2)
      o.2.2 o.1.2.1 o.1.2.2)
    {g d1 : ℕ} (hgcd : o.1.2.1.gcd o.1.2.2 = g)
    (hd1 : CanonicalReciprocalData.supportedPart (o.1.2.1 / g) g = d1) :
    (o.1.2.1, o.1.2.2) ∈
      alphaPairSlice e o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2 g d1 := by
  obtain ⟨hO, hCo⟩ :=
    (e.mem_smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport o).mp ho
  have hPairs : o.1 ∈
      (e.primitiveFirstFactorCarrier ×ˢ
        (e.transposedAtom.betaCarrier ×ˢ e.transposedAtom.betaCarrier)).filter
          (fun n => n.2.1 ≠ n.2.2 ∧ Nat.ModEq n.1 n.2.1 n.2.2) :=
    (mem_product.mp hO).1
  obtain ⟨hPairs, hne, _hmodp⟩ := mem_filter.mp hPairs
  have hN1 := (mem_product.mp (mem_product.mp hPairs).2).1
  have hN2 := (mem_product.mp (mem_product.mp hPairs).2).2
  have hAlpha1 : o.1.2.1 ∈ e.alphaCarrier := by
    by_contra hn
    apply hCo
    simp [MediumAtom.smallCoreSquaredOuterCoefficient, MediumAtom.transposedAtom, hn]
  have hAlpha2 : o.1.2.2 ∈ e.alphaCarrier := by
    by_contra hn
    apply hCo
    simp [MediumAtom.smallCoreSquaredOuterCoefficient, MediumAtom.transposedAtom, hn]
  apply mem_filter.mpr
  refine ⟨?_, hAlpha1, hAlpha2⟩
  exact mem_filter.mpr ⟨mem_product.mpr ⟨hN1, hN2⟩, hne, hgcd, hd1, hgate⟩

end
end ImbalancedChen.Part3.GeneralDActivePairCountSourceOnly

/-!
SOURCEONLY / UNCOMPILED / HOLD. This is a COMPANION fragment, to be loaded
AFTER the complete GeneralDGateNormalization c9b24158 source-only draft.
That draft imports Part3SharedFirstFactorSupportedCoreCauchy and supplies
supported_row_sum_eq; it has not been installed as an actual module.
No new identity/vanishing premise is supplied by a caller here.
The same actual scalar is re-expressed on its active outer carrier BEFORE
Cauchy. The old Eold*Rold inequality is not used to shrink Eold afterward.
-/
namespace ImbalancedChen.Part3.GeneralDActiveOuterEnergySourceOnly
noncomputable section
open Classical Finset GeneralDGateNormalization
open scoped BigOperators

/-- Same original nonzero Co support, further restricted to the exact outer gate. -/
def activeOuterCarrier (e : MediumAtom) (Ybeta Ysupport : ℝ) : Finset OuterIndex :=
  (e.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport).filter
    (fun o => outerGate o.1.1 o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1 o.1.2.2)

def activeFirstEnergy (e : MediumAtom) (Ybeta Ysupport : ℝ) : ℝ :=
  ∑ o ∈ activeOuterCarrier e Ybeta Ysupport,
    ‖e.smallCoreSquaredOuterCoefficient Ybeta Ysupport o‖ ^ 2

def activeNormalizedRowMass (e : MediumAtom) (Ybeta Ysupport Z : ℝ) : ℝ :=
  ∑ o ∈ activeOuterCarrier e Ybeta Ysupport, ‖normalizedRow e Z o‖ ^ 2

/-- The row is already zero off the exact gate; remove it in the SCALAR SUM. -/
theorem supported_scalar_eq_active (e : MediumAtom) (hR : 1 ≤ e.Q3)
    (Ybeta Ysupport Z : ℝ) :
    (∑ o ∈ e.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport,
      e.smallCoreSquaredOuterCoefficient Ybeta Ysupport o *
        (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o,
          e.smallCoreSquaredRowTerm Z o u)) =
      ∑ o ∈ activeOuterCarrier e Ybeta Ysupport,
        e.smallCoreSquaredOuterCoefficient Ybeta Ysupport o * normalizedRow e Z o := by
  classical
  simp only [activeOuterCarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o ho
  rw [supported_row_sum_eq e hR Ybeta Ysupport Z o ho]
  by_cases hg : outerGate o.1.1 o.2.1.1
    (o.2.1.2.1 * o.2.1.2.2) o.2.2 o.1.2.1 o.1.2.2
  · simp only [if_pos hg]
  · simp only [if_neg hg, mul_zero]

/-- The same complete positive mass is retained exactly by the active carrier. -/
theorem supported_mass_eq_active (e : MediumAtom) (hR : 1 ≤ e.Q3)
    (Ybeta Ysupport Z : ℝ) :
    e.smallCoreSquaredSupportedRowSquareMass Ybeta Ysupport Z =
      activeNormalizedRowMass e Ybeta Ysupport Z := by
  rw [GeneralDGateNormalization.supported_mass_eq e hR Ybeta Ysupport Z]
  simp only [activeNormalizedRowMass, activeOuterCarrier, Finset.sum_filter]
/-- An unconditional exact actual-core consumer at the original Y cutoffs. -/
theorem actual_active_core_eq_and_Cauchy
    (B : ℕ) (sigma kappa c0 : ℝ) (hsigma : 0 < sigma)
    (d : MediumAtom) (hd : MediumAdmissible B sigma kappa c0 d)
    (Z : ℝ) (hZ : 0 < Z) :
    let e := d.cleanedAlphaAtom
    let Y := d.scale ^ (sigma / 4)
    (e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z =
      ∑ o ∈ activeOuterCarrier e Y Y,
        e.smallCoreSquaredOuterCoefficient Y Y o * normalizedRow e Z o) ∧
      (‖e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z‖ ^ 2 ≤
        activeFirstEnergy e Y Y * activeNormalizedRowMass e Y Y Z) := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let Y := d.scale ^ (sigma / 4)
  have he := mediumAdmissible_cleanedAlphaAtom hd
  have hcore :=
    (actual_smallSupported_supportedCore_Cauchy B sigma kappa c0 hsigma d hd Z hZ).1
  have heq : e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z =
      ∑ o ∈ activeOuterCarrier e Y Y,
        e.smallCoreSquaredOuterCoefficient Y Y o * normalizedRow e Z o := by
    exact hcore.trans (supported_scalar_eq_active e he.2.2.2.2.1 Y Y Z)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact complex_finset_cauchy_norm_sq (activeOuterCarrier e Y Y)
    (e.smallCoreSquaredOuterCoefficient Y Y) (normalizedRow e Z)

/-- Literal fixed physical D, gcd(r,D)=delta, paired gcd and supported part. -/
def fixedSlice (e : MediumAtom) (Ybeta Ysupport : ℝ)
    (D delta g d1 : ℕ) : Finset OuterIndex :=
  (activeOuterCarrier e Ybeta Ysupport).filter (fun o =>
    o.2.2 = D ∧ o.2.1.1.gcd D = delta ∧ o.1.2.1.gcd o.1.2.2 = g ∧
      CanonicalReciprocalData.supportedPart (o.1.2.1 / g) g = d1)

def fixedFirstEnergy (e : MediumAtom) (Ybeta Ysupport : ℝ)
    (D delta g d1 : ℕ) : ℝ :=
  ∑ o ∈ fixedSlice e Ybeta Ysupport D delta g d1,
    ‖e.smallCoreSquaredOuterCoefficient Ybeta Ysupport o‖ ^ 2

def physicalT0 (e : MediumAtom) (D : ℕ) : ℝ :=
  e.V * (D : ℝ) / (e.Q1 * e.Q3 ^ 2 * e.Q2 ^ 2)

/-- Same fixed-slice scalar and complete normalized rows; no extra cardinality. -/
theorem fixed_slice_Cauchy (e : MediumAtom) (Ybeta Ysupport Z : ℝ)
    (D delta g d1 : ℕ) :
    ‖∑ o ∈ fixedSlice e Ybeta Ysupport D delta g d1,
      e.smallCoreSquaredOuterCoefficient Ybeta Ysupport o * normalizedRow e Z o‖ ^ 2 ≤
      fixedFirstEnergy e Ybeta Ysupport D delta g d1 *
        ∑ o ∈ fixedSlice e Ybeta Ysupport D delta g d1,
          ‖normalizedRow e Z o‖ ^ 2 := by
  exact complex_finset_cauchy_norm_sq (fixedSlice e Ybeta Ysupport D delta g d1)
    (e.smallCoreSquaredOuterCoefficient Ybeta Ysupport) (normalizedRow e Z)

end
end ImbalancedChen.Part3.GeneralDActiveOuterEnergySourceOnly
/-!
SOURCEONLY / UNCOMPILED. Real physical-tail counting, and its literal energy
consumer. The unchanged 688-line pair-count candidate and unchanged ccdf3830
active-Cauchy companion are prepended in this NEW combined draft only.
-/
namespace ImbalancedChen.Part3.GeneralDPhysicalTailCountSourceOnly

noncomputable section
open Classical Finset GeneralDGateNormalization
open GeneralDActivePairCountSourceOnly GeneralDActiveOuterEnergySourceOnly
open scoped BigOperators

def rightTailCarrier (R S : ℝ) (D : ℕ) : Finset (ℕ × ℕ) :=
  (factorCarrier R ×ˢ factorCarrier S).filter (fun rs => D ∣ rs.1 * rs.2)

def rightTailFibre (R S : ℝ) (D j : ℕ) : Finset (ℕ × ℕ) :=
  (rightTailCarrier R S D).filter (fun rs => rs.1.gcd D = j)

/-- The actual gcd fibre forces the complementary divisor on the SECOND label. -/
theorem complementary_quotient_dvd {r s D : ℕ} (hr : 0 < r)
    (hprod : D ∣ r * s) : D / r.gcd D ∣ s := by
  let j := r.gcd D
  have hj : 0 < j := Nat.gcd_pos_of_pos_left D hr
  have hjD : j ∣ D := Nat.gcd_dvd_right r D
  have hjr : j ∣ r := Nat.gcd_dvd_left r D
  have hDfact : j * (D / j) = D := Nat.mul_div_cancel' hjD
  have hrfact : j * (r / j) = r := Nat.mul_div_cancel' hjr
  have hqdiv : D / j ∣ (r / j) * s := by
    apply Nat.dvd_of_mul_dvd_mul_left hj
    simpa only [← mul_assoc, hDfact, hrfact] using hprod
  exact (Nat.coprime_div_gcd_div_gcd hj).symm.dvd_of_dvd_mul_left hqdiv

theorem rightTailFibre_card_le {R S : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {D j : ℕ} (hD : 0 < D) (hj : j ∈ D.divisors) :
    ((rightTailFibre R S D j).card : ℝ) ≤ 9 * R * S / (D : ℝ) := by
  have hjpos : 0 < j := Nat.pos_of_mem_divisors hj
  have hjD : j ∣ D := (Nat.mem_divisors.mp hj).1
  have hqpos : 0 < D / j := Nat.div_pos (Nat.le_of_dvd hD hjD) hjpos
  have hsub : rightTailFibre R S D j ⊆
      firstMultiples R j ×ˢ firstMultiples S (D / j) := by
    intro rs hrs
    obtain ⟨hrs, hgc⟩ := mem_filter.mp hrs
    obtain ⟨hrs, hprod⟩ := mem_filter.mp hrs
    obtain ⟨hr, hs⟩ := mem_product.mp hrs
    have hjr : j ∣ rs.1 := by rw [← hgc]; exact Nat.gcd_dvd_left _ _
    have hqs : D / j ∣ rs.2 := by
      simpa only [hgc] using
        complementary_quotient_dvd (factorCarrier_bounds hR hr).1 hprod
    exact mem_product.mpr ⟨mem_filter.mpr ⟨hr, hjr⟩,
      mem_filter.mpr ⟨hs, hqs⟩⟩
  have hfact : (j : ℝ) * ((D / j : ℕ) : ℝ) = (D : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hjD
  calc
    _ ≤ ((firstMultiples R j ×ˢ firstMultiples S (D / j)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ = ((firstMultiples R j).card : ℝ) *
        ((firstMultiples S (D / j)).card : ℝ) := by
      rw [card_product, Nat.cast_mul]
    _ ≤ (3 * R / (j : ℝ)) * (3 * S / ((D / j : ℕ) : ℝ)) :=
      mul_le_mul (firstMultiples_card_le_three hR hjpos)
        (firstMultiples_card_le_three hS hqpos) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [div_mul_div_comm, hfact]; ring

/-- True gcd partition of all ordered original right-tail labels. -/
theorem rightTailCarrier_card_le {R S : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {D : ℕ} (hD : 0 < D) :
    ((rightTailCarrier R S D).card : ℝ) ≤
      9 * (D.divisors.card : ℝ) * R * S / (D : ℝ) := by
  have hmap : ∀ rs ∈ rightTailCarrier R S D, rs.1.gcd D ∈ D.divisors := by
    intro rs _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hD.ne'⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  calc
    _ = ∑ j ∈ D.divisors, ((rightTailFibre R S D j).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _j ∈ D.divisors, (9 * R * S / (D : ℝ)) :=
      sum_le_sum (fun j hj => rightTailFibre_card_le hR hS hD hj)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

def leftGcdCarrier (R : ℝ) (D delta : ℕ) : Finset ℕ :=
  (factorCarrier R).filter (fun r => r.gcd D = delta)

theorem leftGcdCarrier_card_le {R : ℝ} (hR : 1 ≤ R)
    {D delta : ℕ} (hdelta : 0 < delta) :
    ((leftGcdCarrier R D delta).card : ℝ) ≤ 3 * R / (delta : ℝ) := by
  have hsub : leftGcdCarrier R D delta ⊆ firstMultiples R delta := by
    intro r hr
    obtain ⟨hr, hgc⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨hr, by rw [← hgc]; exact Nat.gcd_dvd_left _ _⟩
  calc
    _ ≤ ((firstMultiples R delta).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ _ := firstMultiples_card_le_three hR hdelta

theorem factorCarrier_card_le_add_one {Q : ℝ} (hQ : 1 ≤ Q) :
    ((factorCarrier Q).card : ℝ) ≤ Q + 1 := by
  have h := ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one
    (a := Q) (b := 2 * Q) (by linarith) (by linarith)
  change ((factorCarrier Q).card : ℝ) ≤ 2 * Q - Q + 1 at h
  linarith

/-- Any original subcarrier, without a prime assumption or a lost endpoint. -/
theorem sum_reciprocal_subcarrier_le_two {Q : ℝ} (hQ : 1 ≤ Q)
    (P : Finset ℕ) (hP : P ⊆ factorCarrier Q) :
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ 2 := by
  have hQpos : 0 < Q := by linarith
  have hcard : (P.card : ℝ) ≤ Q + 1 := by
    exact (show (P.card : ℝ) ≤ ((factorCarrier Q).card : ℝ) by
      exact_mod_cast card_le_card hP).trans (factorCarrier_card_le_add_one hQ)
  calc
    _ ≤ ∑ _p ∈ P, (1 / Q) := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hQpos (factorCarrier_bounds hQ (hP hp)).2.1
    _ = (P.card : ℝ) * (1 / Q) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (Q + 1) * (1 / Q) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (Q + 1) / Q := by ring
    _ ≤ 2 := (div_le_iff₀ hQpos).mpr (by linarith)

theorem primitive_reciprocal_sum_le_two (e : MediumAtom) (hQ : 1 ≤ e.Q1) :
    (∑ p ∈ e.primitiveFirstFactorCarrier, 1 / (p : ℝ)) ≤ 2 := by
  exact sum_reciprocal_subcarrier_le_two hQ e.primitiveFirstFactorCarrier
    (filter_subset _ _)

/-- Outer key retains the primitive p and ALL three physical tail labels. -/
def outerKey (o : OuterIndex) : ℕ × (ℕ × ℕ × ℕ) := (o.1.1, o.2.1)

def keyCarrier (e : MediumAtom) (D delta : ℕ) : Finset (ℕ × (ℕ × ℕ × ℕ)) :=
  e.primitiveFirstFactorCarrier ×ˢ
    (leftGcdCarrier e.Q3 D delta ×ˢ rightTailCarrier e.Q3 e.Q2 D)

theorem fixedSlice_key_mem (e : MediumAtom) (Ybeta Ysupport : ℝ)
    (D delta g d1 : ℕ) {o : OuterIndex}
    (ho : o ∈ fixedSlice e Ybeta Ysupport D delta g d1) :
    outerKey o ∈ keyCarrier e D delta := by
  obtain ⟨hactive, hDo, hdelta, _hg, _hd1⟩ := mem_filter.mp ho
  obtain ⟨hsupported, _hgate⟩ := mem_filter.mp hactive
  have hO := ((e.mem_smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport o).mp
    hsupported).1
  have hpairs := (mem_filter.mp (mem_product.mp hO).1).1
  have hp := (mem_product.mp hpairs).1
  have htails := (mem_product.mp hO).2
  obtain ⟨t, ht, himage⟩ := mem_biUnion.mp htails
  obtain ⟨D0, hdiv, heq⟩ := mem_image.mp himage
  have htEq : t = o.2.1 := congrArg Prod.fst heq
  have hDEq : D0 = o.2.2 := congrArg Prod.snd heq
  rw [htEq] at ht hdiv
  rw [hDEq, hDo] at hdiv
  have hr := (mem_product.mp ht).1
  have hrs := (mem_product.mp ht).2
  have hDw : D ∣ o.2.1.2.1 * o.2.1.2.2 := (Nat.mem_divisors.mp hdiv).1
  exact mem_product.mpr ⟨hp, mem_product.mpr
    ⟨mem_filter.mpr ⟨hr, hdelta⟩, mem_filter.mpr ⟨hrs, hDw⟩⟩⟩

theorem fixedSlice_key_fibre_card_le (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1)
    (Ybeta Ysupport : ℝ) {D delta g d1 : ℕ}
    (hD : 0 < D) (hg : 0 < g) (hd1 : 0 < d1)
    {k : ℕ × (ℕ × ℕ × ℕ)} (hk : k ∈ keyCarrier e D delta) :
    (((fixedSlice e Ybeta Ysupport D delta g d1).filter
      (fun o => outerKey o = k)).card : ℝ) ≤
      6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (k.1 : ℝ) * (D : ℝ)) := by
  obtain ⟨hkp, hktails⟩ := mem_product.mp hk
  have hDw : D ∣ k.2.2.1 * k.2.2.2 :=
    (mem_filter.mp (mem_product.mp hktails).2).2
  have hp : 0 < k.1 := (factorCarrier_bounds hQ (mem_filter.mp hkp).1).1
  have hcard : ((fixedSlice e Ybeta Ysupport D delta g d1).filter
      (fun o => outerKey o = k)).card ≤
      (actualPairSlice e k.1 k.2.1 (k.2.2.1 * k.2.2.2) D g d1).card := by
    apply card_le_card_of_injOn (fun o : OuterIndex => o.1.2)
    · intro o ho
      obtain ⟨ho, hkey⟩ := mem_filter.mp ho
      obtain ⟨hactive, hDo, _hdelta, hgc, hsup⟩ := mem_filter.mp ho
      obtain ⟨hsupported, hgate⟩ := mem_filter.mp hactive
      have halpha := supported_active_pair_mem_alphaPairSlice e Ybeta Ysupport o
        hsupported hgate hgc hsup
      have hpair := (mem_filter.mp halpha).1
      have hpEq : o.1.1 = k.1 := congrArg Prod.fst hkey
      have htailEq : o.2.1 = k.2 := congrArg Prod.snd hkey
      have hrEq : o.2.1.1 = k.2.1 := congrArg Prod.fst htailEq
      have hrpEq : o.2.1.2.1 = k.2.2.1 :=
        congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) htailEq
      have hspEq : o.2.1.2.2 = k.2.2.2 :=
        congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) htailEq
      change o.1.2 ∈ actualPairSlice e k.1 k.2.1 (k.2.2.1 * k.2.2.2) D g d1
      simpa only [Prod.eta, hpEq, hrEq, hrpEq, hspEq, hDo] using hpair
    · intro a ha b hb hab
      obtain ⟨ha, haKey⟩ := mem_filter.mp ha
      obtain ⟨hb, hbKey⟩ := mem_filter.mp hb
      have hkeys : outerKey a = outerKey b := haKey.trans hbKey.symm
      have hpEq : a.1.1 = b.1.1 :=
        congrArg (fun q : ℕ × (ℕ × ℕ × ℕ) => q.1) hkeys
      have htailEq : a.2.1 = b.2.1 :=
        congrArg (fun q : ℕ × (ℕ × ℕ × ℕ) => q.2) hkeys
      have hDEq : a.2.2 = b.2.2 :=
        (mem_filter.mp ha).2.1.trans (mem_filter.mp hb).2.1.symm
      exact Prod.ext (Prod.ext hpEq hab) (Prod.ext htailEq hDEq)
  exact (show (((fixedSlice e Ybeta Ysupport D delta g d1).filter
    (fun o => outerKey o = k)).card : ℝ) ≤
      ((actualPairSlice e k.1 k.2.1 (k.2.2.1 * k.2.2.2) D g d1).card : ℝ) by
        exact_mod_cast hcard).trans
    (actualPairSlice_card_le e hN hp hD hg hd1 hDw)

theorem fixedSlice_card_le_324 (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Ybeta Ysupport : ℝ) {D delta g d1 : ℕ}
    (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hd1 : 0 < d1) :
    ((fixedSlice e Ybeta Ysupport D delta g d1).card : ℝ) ≤
      324 * (D.divisors.card : ℝ) * e.U ^ 2 * e.Q3 ^ 2 * e.Q2 /
        ((g : ℝ) ^ 2 * (d1 : ℝ) * (delta : ℝ) * (D : ℝ) ^ 2) := by
  let L := leftGcdCarrier e.Q3 D delta
  let T := rightTailCarrier e.Q3 e.Q2 D
  let K : ℝ := 6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (D : ℝ))
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hd1R : (0 : ℝ) < d1 := by exact_mod_cast hd1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hdeltaR : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hfrac : ∀ p ∈ e.primitiveFirstFactorCarrier,
      6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (p : ℝ) * (D : ℝ)) =
        K * (1 / (p : ℝ)) := by
    intro p hp
    have hpR : (0 : ℝ) < p := by
      exact_mod_cast (factorCarrier_bounds hQ (mem_filter.mp hp).1).1
    dsimp only [K]
    field_simp [ne_of_gt hgR, ne_of_gt hd1R, ne_of_gt hDR, ne_of_gt hpR]
  have hmap : ∀ o ∈ fixedSlice e Ybeta Ysupport D delta g d1,
      outerKey o ∈ keyCarrier e D delta :=
    fun o ho => fixedSlice_key_mem e Ybeta Ysupport D delta g d1 ho
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  have hL : (L.card : ℝ) ≤ 3 * e.Q3 / (delta : ℝ) := leftGcdCarrier_card_le hR hdelta
  have hT : (T.card : ℝ) ≤
      9 * (D.divisors.card : ℝ) * e.Q3 * e.Q2 / (D : ℝ) :=
    rightTailCarrier_card_le hR hS hD
  have hLT : (L.card : ℝ) * (T.card : ℝ) ≤
      (3 * e.Q3 / (delta : ℝ)) *
        (9 * (D.divisors.card : ℝ) * e.Q3 * e.Q2 / (D : ℝ)) :=
    mul_le_mul hL hT (Nat.cast_nonneg _) (by positivity)
  have hP : K * (∑ p ∈ e.primitiveFirstFactorCarrier, 1 / (p : ℝ)) ≤ K * 2 :=
    mul_le_mul_of_nonneg_left (primitive_reciprocal_sum_le_two e hQ) hK
  calc
    _ = ∑ k ∈ keyCarrier e D delta,
        (((fixedSlice e Ybeta Ysupport D delta g d1).filter
          (fun o => outerKey o = k)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ k ∈ keyCarrier e D delta,
        (6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (k.1 : ℝ) * (D : ℝ))) :=
      sum_le_sum (fun k hk => fixedSlice_key_fibre_card_le e hN hQ
        Ybeta Ysupport hD hg hd1 hk)
    _ = ∑ p ∈ e.primitiveFirstFactorCarrier,
        ∑ _t ∈ L ×ˢ T,
          (6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (p : ℝ) * (D : ℝ))) := by
      rw [keyCarrier, sum_product]
    _ = ((L.card : ℝ) * (T.card : ℝ)) *
        (K * (∑ p ∈ e.primitiveFirstFactorCarrier, 1 / (p : ℝ))) := by
      simp only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul]
      calc
        _ = ((L.card : ℝ) * (T.card : ℝ)) *
            ∑ p ∈ e.primitiveFirstFactorCarrier,
              (6 * e.U ^ 2 / ((g : ℝ) ^ 2 * (d1 : ℝ) * (p : ℝ) * (D : ℝ))) :=
          (Finset.mul_sum _ _ _).symm
        _ = _ := by
          congr 1
          calc
            _ = ∑ p ∈ e.primitiveFirstFactorCarrier, K * (1 / (p : ℝ)) :=
              sum_congr rfl hfrac
            _ = _ := (Finset.mul_sum _ _ _).symm
    _ ≤ ((3 * e.Q3 / (delta : ℝ)) *
          (9 * (D.divisors.card : ℝ) * e.Q3 * e.Q2 / (D : ℝ))) * (K * 2) :=
      mul_le_mul hLT hP (by positivity) (by positivity)
    _ = _ := by
      dsimp only [K]
      field_simp [ne_of_gt hgR, ne_of_gt hd1R, ne_of_gt hDR, ne_of_gt hdeltaR]; ring

/-- A public visibility adapter to the owned private exact Co norm argument. -/
theorem cleaned_transposed_beta_norm_le_one {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ :=
    mediumAdmissible_cleanedAlphaAtom hd
  change ‖if n ∈ d.alphaCarrier then d.cleanedAlpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.alphaCarrier
  · have hnBound := hAlpha n hn
    change ‖d.cleanedAlpha n‖ ≤ 1 at hnBound
    simpa only [if_pos hn] using hnBound
  · simp only [if_neg hn, norm_zero, zero_le_one]

theorem cleaned_outerCoefficient_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (Ybeta Ysupport : ℝ) {o : OuterIndex}
    (ho : o ∈ d.cleanedAlphaAtom.smallCoreSquaredOuterCarrier) :
    ‖d.cleanedAlphaAtom.smallCoreSquaredOuterCoefficient Ybeta Ysupport o‖ ≤ 1 := by
  have htails := (mem_product.mp ho).2
  obtain ⟨t, ht, himage⟩ := mem_biUnion.mp htails
  obtain ⟨D0, _hD0, heq⟩ := mem_image.mp himage
  have htEq : t = o.2.1 := congrArg Prod.fst heq
  rw [htEq] at ht
  have hr := (mem_product.mp ht).1
  have hrp := (mem_product.mp (mem_product.mp ht).2).1
  have hsp := (mem_product.mp (mem_product.mp ht).2).2
  have hdKeep := hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hGamma2, hGamma3⟩ := hdKeep
  have h1 := cleaned_transposed_beta_norm_le_one hd o.1.2.1
  have h2 := cleaned_transposed_beta_norm_le_one hd o.1.2.2
  have h3 := (hGamma3 o.2.1.1 hr).1
  have h4 := (hGamma3 o.2.1.2.1 hrp).1
  have h5 := (hGamma2 o.2.1.2.2 hsp).1
  unfold MediumAtom.smallCoreSquaredOuterCoefficient
  dsimp only
  split_ifs
  · simp only [norm_mul, norm_star]
    exact mul_le_one₀
      (mul_le_one₀
        (mul_le_one₀
          (mul_le_one₀ h1 (norm_nonneg _) h2)
          (norm_nonneg _) h3)
        (norm_nonneg _) h4)
      (norm_nonneg _) h5
  · simp only [norm_zero, zero_le_one]

/-- Literal fixedFirstEnergy on the SAME supported, active, fixed-feature carrier.
The numerical 324 bound is a conclusion of the finite proofs above. -/
theorem actual_fixedFirstEnergy_le_324
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (Ybeta Ysupport : ℝ) {D delta g d1 : ℕ}
    (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hd1 : 0 < d1) :
    fixedFirstEnergy d.cleanedAlphaAtom Ybeta Ysupport D delta g d1 ≤
      324 * (D.divisors.card : ℝ) * d.U ^ 2 * d.Q3 ^ 2 * d.Q2 /
        ((g : ℝ) ^ 2 * (d1 : ℝ) * (delta : ℝ) * (D : ℝ) ^ 2) := by
  let e := d.cleanedAlphaAtom
  have he := mediumAdmissible_cleanedAlphaAtom hd
  have hcard := fixedSlice_card_le_324 e he.1 he.2.2.1 he.2.2.2.2.1 he.2.2.2.1
    Ybeta Ysupport hD hdelta hg hd1
  have henergy : fixedFirstEnergy e Ybeta Ysupport D delta g d1 ≤
      ((fixedSlice e Ybeta Ysupport D delta g d1).card : ℝ) := by
    unfold fixedFirstEnergy
    calc
      _ ≤ ∑ _o ∈ fixedSlice e Ybeta Ysupport D delta g d1, (1 : ℝ) := by
        apply sum_le_sum
        intro o ho
        have hactive := (mem_filter.mp ho).1
        have hsupported := (mem_filter.mp hactive).1
        have hO := ((e.mem_smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport o).mp
          hsupported).1
        have hnorm := cleaned_outerCoefficient_norm_le_one hd Ybeta Ysupport hO
        simpa only [one_pow] using
          (sq_le_sq₀ (norm_nonneg (e.smallCoreSquaredOuterCoefficient Ybeta Ysupport o))
            (by norm_num : (0 : ℝ) ≤ 1)).2 hnorm
      _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one]
  exact henergy.trans hcard

end
end ImbalancedChen.Part3.GeneralDPhysicalTailCountSourceOnly

/-!
SOURCEONLY / UNCOMPILED companion. Load AFTER the exact c21547ccf073...
1151-line actual physical-tail/energy candidate (imports first when joining).
No parent is changed. The packet map, its arithmetic support, its representation
carrier and the pushforward all use the LITERAL fixedSlice and original Co.
No equality of the still-outer-dependent actual row with a packet function is
assumed. Arbitrary J below is a function on the explicitly constructed packet
image; its later identification with a separated actual row remains a consumer.
-/

namespace ImbalancedChen.Part3.ActualFixedFeaturePacketPushforwardSourceOnly

noncomputable section
open Classical Finset GeneralDGateNormalization
open GeneralDActivePairCountSourceOnly GeneralDActiveOuterEnergySourceOnly
open GeneralDPhysicalTailCountSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

abbrev Packet := (ℕ × ℕ) × ℤ
def n1 (g : ℕ) (o : OuterIndex) : ℕ :=
  CanonicalReciprocalData.coprimePart (o.1.2.1 / g) g
def n2 (g : ℕ) (o : OuterIndex) : ℕ := o.1.2.2 / g
def r0 (delta : ℕ) (o : OuterIndex) : ℕ := o.2.1.1 / delta
def w0 (D : ℕ) (o : OuterIndex) : ℕ := (o.2.1.2.1 * o.2.1.2.2) / D
def packetB (delta g l : ℕ) (o : OuterIndex) : ℕ := g * l * n2 g o * r0 delta o
def packetC (D g : ℕ) (o : OuterIndex) : ℕ := n1 g o * w0 D o
def packetF (D g l : ℕ) (o : OuterIndex) : ℤ :=
  ((l : ℤ) * n1 g o - n2 g o) / ((o.1.1 * D : ℕ) : ℤ)
def packetKey (D delta g l : ℕ) (o : OuterIndex) : Packet :=
  ((packetB delta g l o, packetC D g o), packetF D g l o)

/-- Membership facts extracted from the literal supported/active/fixed carrier. -/
theorem fixedSlice_facts (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    o.1.1 ∈ e.primitiveFirstFactorCarrier ∧
    o.1.2.1 ∈ factorCarrier e.U ∧ o.1.2.2 ∈ factorCarrier e.U ∧
    o.2.1.1 ∈ factorCarrier e.Q3 ∧ o.2.1.2.1 ∈ factorCarrier e.Q3 ∧
    o.2.1.2.2 ∈ factorCarrier e.Q2 ∧ o.1.2.1 ≠ o.1.2.2 ∧
    o.2.2 = D ∧ o.2.1.1.gcd D = delta ∧ o.1.2.1.gcd o.1.2.2 = g ∧
    CanonicalReciprocalData.supportedPart (o.1.2.1 / g) g = l ∧
    D ∣ o.2.1.2.1 * o.2.1.2.2 ∧
    outerGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1 o.1.2.2 := by
  have hk := fixedSlice_key_mem e Yb Ys D delta g l ho
  obtain ⟨hp, htails⟩ := mem_product.mp hk
  obtain ⟨hr, hright⟩ := mem_product.mp htails
  obtain ⟨hrr, hDw⟩ := mem_filter.mp hright
  obtain ⟨hrp, hsp⟩ := mem_product.mp hrr
  have hrmem := (mem_filter.mp hr).1
  obtain ⟨hactive, hDo, hdelta, hgc, hsup⟩ := mem_filter.mp ho
  obtain ⟨hsupported, hgate⟩ := mem_filter.mp hactive
  have ha := supported_active_pair_mem_alphaPairSlice e Yb Ys o
    hsupported hgate hgc hsup
  have hpair : (o.1.2.1, o.1.2.2) ∈
      pairSlice e.U o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) o.2.2 g l :=
    (mem_filter.mp ha).1
  obtain ⟨hN1, hN2, hne, _, _, _⟩ := mem_pairSlice_iff.mp hpair
  rw [hDo] at hgate
  exact ⟨hp, hN1, hN2, hrmem, hrp, hsp, hne, hDo, hdelta, hgc, hsup, hDw, hgate⟩

structure PacketData (D delta g l : ℕ) (o : OuterIndex) : Prop where
  p_pos : 0 < o.1.1
  n1_pos : 0 < n1 g o
  n2_pos : 0 < n2 g o
  r0_pos : 0 < r0 delta o
  w0_pos : 0 < w0 D o
  N1_fact : o.1.2.1 = g * l * n1 g o
  N2_fact : o.1.2.2 = g * n2 g o
  r_fact : o.2.1.1 = delta * r0 delta o
  w_fact : o.2.1.2.1 * o.2.1.2.2 = D * w0 D o
  f_relation : ((o.1.1 * D : ℕ) : ℤ) * packetF D g l o =
    (l : ℤ) * n1 g o - n2 g o
  difference : ((g * o.1.1 * D : ℕ) : ℤ) * packetF D g l o =
    (o.1.2.1 : ℤ) - o.1.2.2
  f_ne : packetF D g l o ≠ 0
  b_pos : 0 < packetB delta g l o
  c_pos : 0 < packetC D g o
  bc_coprime : (packetB delta g l o).Coprime (packetC D g o)

/-- All packet facts follow from actual fixedSlice membership. The arithmetic
surrogate s=q is used ONLY to invoke the already proved CRT dictionary; it is
not asserted in the original s interval and does not enlarge an actual row. -/
theorem fixedSlice_packetData (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ}
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    PacketData D delta g l o := by
  obtain ⟨hp0, hN10, hN20, hr0, hrp0, hsp0, hne, hDo, hd, hgc, hsup, hDw, hgate⟩ :=
    fixedSlice_facts e Yb Ys D delta g l ho
  have hp := (factorCarrier_bounds hQ (mem_filter.mp hp0).1).1
  have hN1 := (factorCarrier_bounds hN hN10).1
  have hN2 := (factorCarrier_bounds hN hN20).1
  have hr := (factorCarrier_bounds hR hr0).1
  have hw := Nat.mul_pos (factorCarrier_bounds hR hrp0).1
    (factorCarrier_bounds hS hsp0).1
  obtain ⟨hq, hred, _hc, hDfact, hrfact⟩ := quotient_data hr hD
  have hsurrogate : originalGate o.1.1 o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1 o.1.2.2
      (quotient o.2.1.1 D) := by
    apply (originalGate_iff hr hD hDw).mpr
    exact ⟨dvd_rfl, hgate, by simp [Nat.div_self hq]⟩
  have hredEq :
      (o.2.1.1 * quotient o.2.1.1 D) / D = r0 delta o := by
    have hmul : o.2.1.1 * quotient o.2.1.1 D =
        D * reducedLeft o.2.1.1 D := by
      calc
        _ = (o.2.1.1.gcd D * reducedLeft o.2.1.1 D) * quotient o.2.1.1 D :=
          by rw [hrfact]
        _ = (o.2.1.1.gcd D * quotient o.2.1.1 D) * reducedLeft o.2.1.1 D := by ring
        _ = _ := by rw [hDfact]
    rw [hmul, Nat.mul_div_cancel_left _ hD]
    simp only [reducedLeft, hd, r0]
  have hlic := sharedDifferenceData_licenses hp (Nat.mul_pos hr hq) hw
    hN1 hN2 hsurrogate.2 (0 : ℤ)
  dsimp only at hlic
  simp only [hsurrogate.1, hgc, hsup, hredEq] at hlic
  obtain ⟨_hg, _hD, _hl, hn1, hn2, _hr, hw0, _hA, _hL,
    hN1eq, hN2eq, _hv, hweq, _hLeq, _hrw, _hnp, _hrc, hbc, _hroot, hfeq, _rest⟩ := hlic
  change 0 < n1 g o at hn1
  change 0 < n2 g o at hn2
  change 0 < w0 D o at hw0
  change o.1.2.1 = g * l * n1 g o at hN1eq
  change o.1.2.2 = g * n2 g o at hN2eq
  change o.2.1.2.1 * o.2.1.2.2 = D * w0 D o at hweq
  change ((o.1.1 * D : ℕ) : ℤ) * packetF D g l o =
    (l : ℤ) * n1 g o - n2 g o at hfeq
  change (packetB delta g l o).Coprime (packetC D g o) at hbc
  have hrEq : o.2.1.1 = delta * r0 delta o := by
    simpa only [hd, reducedLeft, r0] using hrfact.symm
  have hrPos : 0 < r0 delta o := by simpa only [reducedLeft, hd, r0] using hred
  have hdiff : ((g * o.1.1 * D : ℕ) : ℤ) * packetF D g l o =
      (o.1.2.1 : ℤ) - o.1.2.2 := by
    calc
      _ = (g : ℤ) * (((o.1.1 * D : ℕ) : ℤ) * packetF D g l o) := by push_cast; ring
      _ = (g : ℤ) * ((l : ℤ) * n1 g o - n2 g o) := by rw [hfeq]
      _ = _ := by rw [hN1eq, hN2eq]; push_cast; ring
  have hfne : packetF D g l o ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdiff
    exact hne (Int.ofNat_inj.mp (sub_eq_zero.mp hdiff.symm))
  exact ⟨hp, hn1, hn2, hrPos, hw0, hN1eq, hN2eq, hrEq, hweq, hfeq, hdiff, hfne,
    by unfold packetB; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg hl) hn2) hrPos,
    Nat.mul_pos hn1 hw0, hbc⟩

/-- Canonical coprimePart is the actual N1/A quotient, not a new independent label. -/
theorem n1_eq_N1_div_A {D delta g l : ℕ} (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (d : PacketData D delta g l o) :
    n1 g o = o.1.2.1 / (g * l) := by
  rw [d.N1_fact, Nat.mul_div_cancel_left _ (Nat.mul_pos hg hl)]

/-- f has exactly the signed quotient of the ORIGINAL N difference. -/
theorem f_eq_original_difference_div {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g)
    {o : OuterIndex} (d : PacketData D delta g l o) :
    packetF D g l o = ((o.1.2.1 : ℤ) - o.1.2.2) / ((g * o.1.1 * D : ℕ) : ℤ) := by
  have hm : ((g * o.1.1 * D : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hg d.p_pos) hD).ne'
  have hdiv : ((g * o.1.1 * D : ℕ) : ℤ) ∣ (o.1.2.1 : ℤ) - o.1.2.2 :=
    ⟨packetF D g l o, d.difference.symm⟩
  exact mul_left_cancel₀ hm (d.difference.trans (Int.mul_ediv_cancel' hdiv).symm)

def packetImage (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ) : Finset Packet :=
  (fixedSlice e Yb Ys D delta g l).image (packetKey D delta g l)
def packetFiber (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (k : Packet) : Finset OuterIndex :=
  (fixedSlice e Yb Ys D delta g l).filter (fun o => packetKey D delta g l o = k)

/-- Ordered right factors remain a PAIR in a divisor antidiagonal. -/
def representationCarrier (A D b c : ℕ) : Finset (ℕ × (Σ _ : ℕ, ℕ × ℕ)) :=
  (b / A).divisors ×ˢ c.divisors.sigma
    (fun a1 => (D * (c / a1)).divisorsAntidiagonal)
def representationMap (g : ℕ) (o : OuterIndex) : ℕ × (Σ _ : ℕ, ℕ × ℕ) :=
  (n2 g o, ⟨n1 g o, (o.2.1.2.1, o.2.1.2.2)⟩)

theorem packetFiber_representation_mem (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {k : Packet} {o : OuterIndex} (ho : o ∈ packetFiber e Yb Ys D delta g l k) :
    representationMap g o ∈ representationCarrier (g * l) D k.1.1 k.1.2 := by
  obtain ⟨ho, hk⟩ := mem_filter.mp ho
  have d := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ho
  have hb : packetB delta g l o = k.1.1 := congrArg (fun z : Packet => z.1.1) hk
  have hc : packetC D g o = k.1.2 := congrArg (fun z : Packet => z.1.2) hk
  have hbdiv : k.1.1 / (g * l) = n2 g o * r0 delta o := by
    rw [← hb]
    unfold packetB
    rw [mul_assoc, Nat.mul_div_cancel_left _ (Nat.mul_pos hg hl)]
  have hcdiv : k.1.2 / n1 g o = w0 D o := by
    rw [← hc, packetC, Nat.mul_div_cancel_left _ d.n1_pos]
  unfold representationCarrier representationMap
  apply mem_product.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, mem_sigma.mpr ⟨?_, ?_⟩⟩
  · rw [hbdiv]; exact dvd_mul_right _ _
  · rw [hbdiv]; exact (Nat.mul_pos d.n2_pos d.r0_pos).ne'
  · apply Nat.mem_divisors.mpr
    exact ⟨by rw [← hc, packetC]; exact dvd_mul_right _ _, by rw [← hc]; exact d.c_pos.ne'⟩
  · apply Nat.mem_divisorsAntidiagonal.mpr
    rw [hcdiv]
    exact ⟨d.w_fact, (Nat.mul_pos hD d.w0_pos).ne'⟩

/-- Injectivity is on EACH TRUE packet fibre. It recovers p using f!=0;
the original ordered rprime,sprime labels have never been collapsed. -/
theorem representationMap_injOn_packetFiber (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (k : Packet) : Set.InjOn (representationMap g)
      (packetFiber e Yb Ys D delta g l k : Set OuterIndex) := by
  intro a ha b hb hrepr
  obtain ⟨ha, hka⟩ := mem_filter.mp ha
  obtain ⟨hb, hkb⟩ := mem_filter.mp hb
  have da := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ha
  have db := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl hb
  have hn2 : n2 g a = n2 g b := congrArg Prod.fst hrepr
  have hn1 : n1 g a = n1 g b := congrArg (fun z => z.2.1) hrepr
  have htail : (a.2.1.2.1, a.2.1.2.2) = (b.2.1.2.1, b.2.1.2.2) :=
    congrArg (fun z => z.2.2) hrepr
  have hkeys := hka.trans hkb.symm
  have hbval : packetB delta g l a = packetB delta g l b :=
    congrArg (fun z : Packet => z.1.1) hkeys
  have hf : packetF D g l a = packetF D g l b := congrArg Prod.snd hkeys
  have hpF : ((a.1.1 * D : ℕ) : ℤ) * packetF D g l a =
      ((b.1.1 * D : ℕ) : ℤ) * packetF D g l a := by
    calc
      _ = (l : ℤ) * n1 g a - n2 g a := da.f_relation
      _ = (l : ℤ) * n1 g b - n2 g b := by rw [hn1, hn2]
      _ = ((b.1.1 * D : ℕ) : ℤ) * packetF D g l b := db.f_relation.symm
      _ = _ := by rw [← hf]
  have hpD : a.1.1 * D = b.1.1 * D :=
    Int.ofNat_inj.mp (mul_right_cancel₀ da.f_ne hpF)
  have hp : a.1.1 = b.1.1 := by
    apply Nat.eq_of_mul_eq_mul_left hD
    simpa only [mul_comm D] using hpD
  have hr0 : r0 delta a = r0 delta b := by
    unfold packetB at hbval
    rw [hn2] at hbval
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.mul_pos hg hl) db.n2_pos) hbval
  have hr : a.2.1.1 = b.2.1.1 := by rw [da.r_fact, db.r_fact, hr0]
  have hN1 : a.1.2.1 = b.1.2.1 := by rw [da.N1_fact, db.N1_fact, hn1]
  have hN2 : a.1.2.2 = b.1.2.2 := by rw [da.N2_fact, db.N2_fact, hn2]
  have hDstored : a.2.2 = b.2.2 :=
    (mem_filter.mp ha).2.1.trans (mem_filter.mp hb).2.1.symm
  exact Prod.ext (Prod.ext hp (Prod.ext hN1 hN2))
    (Prod.ext (Prod.ext hr htail) hDstored)

theorem card_representationCarrier (A D b c : ℕ) :
    (representationCarrier A D b c).card =
      (b / A).divisors.card * ∑ a1 ∈ c.divisors, (D * (c / a1)).divisors.card := by
  have hanti (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors]
    exact card_map _
  simp only [representationCarrier, card_product, card_sigma, hanti]

theorem card_representationCarrier_le_tau (A D b c : ℕ) :
    (representationCarrier A D b c).card ≤
      (b / A).divisors.card * D.divisors.card * c.divisors.card ^ 2 := by
  rw [card_representationCarrier]
  calc
    _ ≤ (b / A).divisors.card *
        ∑ _a1 ∈ c.divisors, D.divisors.card * c.divisors.card := by
      apply Nat.mul_le_mul_left
      apply sum_le_sum
      intro a1 ha1
      have hquot : c / a1 ∣ c :=
        ⟨a1, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors ha1)).symm⟩
      exact (ImbalancedChen.Part3.TransposedPrimitiveUMoment.card_divisors_mul_le D (c / a1)).trans
        (Nat.mul_le_mul_left D.divisors.card
          (card_le_card (Nat.divisors_subset_of_dvd (Nat.ne_zero_of_mem_divisors ha1) hquot)))
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; ring

theorem packetFiber_card_le_representations (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (k : Packet) :
    (packetFiber e Yb Ys D delta g l k).card ≤
      (k.1.1 / (g * l)).divisors.card *
        ∑ a1 ∈ k.1.2.divisors, (D * (k.1.2 / a1)).divisors.card := by
  calc
    _ ≤ (representationCarrier (g * l) D k.1.1 k.1.2).card :=
      card_le_card_of_injOn (representationMap g)
        (fun _ ho => packetFiber_representation_mem e hN hQ hR hS Yb Ys hD hg hl ho)
        (representationMap_injOn_packetFiber e hN hQ hR hS Yb Ys hD hg hl k)
    _ = _ := card_representationCarrier _ _ _ _

theorem packetFiber_card_le_tau (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (k : Packet) :
    (packetFiber e Yb Ys D delta g l k).card ≤
      (k.1.1 / (g * l)).divisors.card * D.divisors.card * k.1.2.divisors.card ^ 2 := by
  calc
    _ ≤ (representationCarrier (g * l) D k.1.1 k.1.2).card :=
      card_le_card_of_injOn (representationMap g)
        (fun _ ho => packetFiber_representation_mem e hN hQ hR hS Yb Ys hD hg hl ho)
        (representationMap_injOn_packetFiber e hN hQ hR hS Yb Ys hD hg hl k)
    _ ≤ _ := card_representationCarrier_le_tau _ _ _ _

/-- Exact positive pushforward on the TRUE packet image: no multiplicity erased. -/
theorem positive_mass_eq_packet_mass (e : MediumAtom) (Yb Ys : ℝ)
    (D delta g l : ℕ) (J : Packet → ℂ) :
    (∑ o ∈ fixedSlice e Yb Ys D delta g l, ‖J (packetKey D delta g l o)‖ ^ 2) =
      ∑ k ∈ packetImage e Yb Ys D delta g l,
        ((packetFiber e Yb Ys D delta g l k).card : ℝ) * ‖J k‖ ^ 2 := by
  have hf := sum_fiberwise_of_maps_to'
    (s := fixedSlice e Yb Ys D delta g l)
    (t := packetImage e Yb Ys D delta g l) (g := packetKey D delta g l)
    (fun o ho => mem_image_of_mem _ ho) (fun k => ‖J k‖ ^ 2)
  symm
  simpa only [packetFiber, sum_const, nsmul_eq_mul] using hf

def groupedCo (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ) (k : Packet) : ℂ :=
  ∑ o ∈ packetFiber e Yb Ys D delta g l k, e.smallCoreSquaredOuterCoefficient Yb Ys o

/-- Exact complex coefficient pushforward. Signs/conjugates remain in groupedCo. -/
theorem scalar_eq_groupedCo (e : MediumAtom) (Yb Ys : ℝ)
    (D delta g l : ℕ) (J : Packet → ℂ) :
    (∑ o ∈ fixedSlice e Yb Ys D delta g l,
      e.smallCoreSquaredOuterCoefficient Yb Ys o * J (packetKey D delta g l o)) =
      ∑ k ∈ packetImage e Yb Ys D delta g l, groupedCo e Yb Ys D delta g l k * J k := by
  have hf := sum_fiberwise_of_maps_to
    (s := fixedSlice e Yb Ys D delta g l)
    (t := packetImage e Yb Ys D delta g l) (g := packetKey D delta g l)
    (fun o ho => mem_image_of_mem _ ho)
    (fun o => e.smallCoreSquaredOuterCoefficient Yb Ys o * J (packetKey D delta g l o))
  rw [← hf]
  apply sum_congr rfl
  intro k _
  unfold groupedCo
  rw [sum_mul]
  apply sum_congr rfl
  intro o ho
  rw [(mem_filter.mp ho).2]

/-- Cauchy uses the original Co energy, then the EXACT positive pushforward.
This is an actual finite packet consumer, not an assumed final row estimate. -/
theorem scalar_packet_Cauchy (e : MediumAtom) (Yb Ys : ℝ)
    (D delta g l : ℕ) (J : Packet → ℂ) :
    ‖∑ o ∈ fixedSlice e Yb Ys D delta g l,
      e.smallCoreSquaredOuterCoefficient Yb Ys o * J (packetKey D delta g l o)‖ ^ 2 ≤
      fixedFirstEnergy e Yb Ys D delta g l *
        ∑ k ∈ packetImage e Yb Ys D delta g l,
          ((packetFiber e Yb Ys D delta g l k).card : ℝ) * ‖J k‖ ^ 2 := by
  have hc := complex_finset_cauchy_norm_sq (fixedSlice e Yb Ys D delta g l)
    (e.smallCoreSquaredOuterCoefficient Yb Ys) (fun o => J (packetKey D delta g l o))
  rw [positive_mass_eq_packet_mass] at hc
  exact hc

/-- Original cleaned Co, not a caller-supplied coefficient-norm hypothesis. -/
theorem actual_groupedCo_norm_le_tau {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l) (k : Packet) :
    ‖groupedCo d.cleanedAlphaAtom Yb Ys D delta g l k‖ ≤
      (((k.1.1 / (g * l)).divisors.card * D.divisors.card *
        k.1.2.divisors.card ^ 2 : ℕ) : ℝ) := by
  let e := d.cleanedAlphaAtom
  have he := mediumAdmissible_cleanedAlphaAtom hd
  have hcard := packetFiber_card_le_tau (delta := delta) e he.1 he.2.2.1 he.2.2.2.2.1 he.2.2.2.1
    Yb Ys hD hg hl k
  calc
    _ ≤ ∑ o ∈ packetFiber e Yb Ys D delta g l k,
        ‖e.smallCoreSquaredOuterCoefficient Yb Ys o‖ := norm_sum_le _ _
    _ ≤ ∑ _o ∈ packetFiber e Yb Ys D delta g l k, (1 : ℝ) := by
      apply sum_le_sum
      intro o ho
      have hfixed := (mem_filter.mp ho).1
      have hactive := (mem_filter.mp hfixed).1
      have hsupported := (mem_filter.mp hactive).1
      have hO := ((e.mem_smallCoreSquaredSupportedOuterCarrier Yb Ys o).mp hsupported).1
      exact cleaned_outerCoefficient_norm_le_one hd Yb Ys hO
    _ = ((packetFiber e Yb Ys D delta g l k).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast hcard

private theorem divide_window {X T den u k : ℝ} (hden : 0 < den)
    (hlo : X ≤ T) (hhi : T ≤ k * X) (heq : T = den * u) :
    X / den ≤ u ∧ u ≤ k * X / den := by
  constructor
  · apply (div_le_iff₀ hden).mpr
    nlinarith [heq]
  · apply (le_div_iff₀ hden).mpr
    nlinarith [heq]

/-- Actual real B,C windows, with the original inclusive endpoints.
They are conclusions of literal carrier membership and reconstruction. -/
theorem packetB_C_scales (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ}
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    (l : ℝ) * e.U * e.Q3 / delta ≤ (packetB delta g l o : ℝ) ∧
    (packetB delta g l o : ℝ) ≤ 4 * ((l : ℝ) * e.U * e.Q3 / delta) ∧
    e.U * e.Q3 * e.Q2 / ((g : ℝ) * l * D) ≤ (packetC D g o : ℝ) ∧
    (packetC D g o : ℝ) ≤ 8 * (e.U * e.Q3 * e.Q2 / ((g : ℝ) * l * D)) := by
  obtain ⟨_hp, hN10, hN20, hr0, hrp0, hsp0, _hne, _hDo, hd, _hg, _hl, _hDw, _gate⟩ :=
    fixedSlice_facts e Yb Ys D delta g l ho
  have d := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ho
  have hN1b := factorCarrier_bounds hN hN10
  have hN2b := factorCarrier_bounds hN hN20
  have hrb := factorCarrier_bounds hR hr0
  have hrpb := factorCarrier_bounds hR hrp0
  have hspb := factorCarrier_bounds hS hsp0
  have hdelta : 0 < delta := by
    rw [← hd]
    exact Nat.gcd_pos_of_pos_left D hrb.1
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hA : (0 : ℝ) < (g : ℝ) * l := mul_pos hgR hlR
  have hN1eq : (o.1.2.1 : ℝ) = ((g : ℝ) * l) * n1 g o := by exact_mod_cast d.N1_fact
  have hN2eq : (o.1.2.2 : ℝ) = (g : ℝ) * n2 g o := by exact_mod_cast d.N2_fact
  have hreq : (o.2.1.1 : ℝ) = (delta : ℝ) * r0 delta o := by exact_mod_cast d.r_fact
  have hweq : (o.2.1.2.1 : ℝ) * o.2.1.2.2 = (D : ℝ) * w0 D o := by
    exact_mod_cast d.w_fact
  have hn1 := divide_window hA hN1b.2.1 hN1b.2.2 hN1eq
  have hn2 := divide_window hgR hN2b.2.1 hN2b.2.2 hN2eq
  have hr := divide_window hdR hrb.2.1 hrb.2.2 hreq
  have hwlo : e.Q3 * e.Q2 ≤ (o.2.1.2.1 : ℝ) * o.2.1.2.2 :=
    mul_le_mul hrpb.2.1 hspb.2.1 (by linarith) (by positivity)
  have hwhi : (o.2.1.2.1 : ℝ) * o.2.1.2.2 ≤ 4 * (e.Q3 * e.Q2) := by
    calc
      _ ≤ (2 * e.Q3) * (2 * e.Q2) :=
        mul_le_mul hrpb.2.2 hspb.2.2 (Nat.cast_nonneg _) (by linarith)
      _ = _ := by ring
  have hw := divide_window hDR hwlo hwhi hweq
  have hbEq : (packetB delta g l o : ℝ) = ((g : ℝ) * l) * n2 g o * r0 delta o :=
    by simp only [packetB, Nat.cast_mul]
  have hcEq : (packetC D g o : ℝ) = (n1 g o : ℝ) * w0 D o :=
    by simp only [packetC, Nat.cast_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = ((g : ℝ) * l) * (e.U / g) * (e.Q3 / delta) := by
        field_simp [hgR.ne', hdR.ne']
      _ ≤ ((g : ℝ) * l) * n2 g o * r0 delta o := by gcongr <;> first | exact hn2.1 | exact hr.1
      _ = _ := hbEq.symm
  · calc
      _ = ((g : ℝ) * l) * n2 g o * r0 delta o := hbEq
      _ ≤ ((g : ℝ) * l) * (2 * e.U / g) * (2 * e.Q3 / delta) := by
        gcongr <;> first | exact hn2.2 | exact hr.2
      _ = _ := by field_simp [hgR.ne', hdR.ne']; ring
  · calc
      _ = (e.U / ((g : ℝ) * l)) * (e.Q3 * e.Q2 / D) := by
        field_simp [hgR.ne', hlR.ne', hDR.ne']
      _ ≤ (n1 g o : ℝ) * w0 D o := by gcongr <;> first | exact hn1.1 | exact hw.1
      _ = _ := hcEq.symm
  · calc
      _ = (n1 g o : ℝ) * w0 D o := hcEq
      _ ≤ (2 * e.U / ((g : ℝ) * l)) * (4 * (e.Q3 * e.Q2) / D) := by
        gcongr <;> first | exact hn1.2 | exact hw.2
      _ = _ := by field_simp [hgR.ne', hlR.ne', hDR.ne']; ring

/-- The original nonzero signed f has F>=1 and its true 1/(gQD) scale.
The difference bound uses [N,2N] width N, with no additive endpoint term. -/
theorem packetF_scale (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ}
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    1 ≤ |(packetF D g l o : ℝ)| ∧
    |(packetF D g l o : ℝ)| ≤ e.U / ((g : ℝ) * e.Q1 * D) ∧
    1 ≤ e.U / ((g : ℝ) * e.Q1 * D) := by
  obtain ⟨hp0, hN10, hN20, _hr, _hrp, _hsp, _hne, _rest⟩ :=
    fixedSlice_facts e Yb Ys D delta g l ho
  have d := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ho
  have hp := factorCarrier_bounds hQ (mem_filter.mp hp0).1
  have h1 := factorCarrier_bounds hN hN10
  have h2 := factorCarrier_bounds hN hN20
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hpR : (0 : ℝ) < o.1.1 := by exact_mod_cast hp.1
  have hQR : 0 < e.Q1 := by linarith
  have hden : 0 < (g : ℝ) * e.Q1 * D := by positivity
  have hdiff := congrArg (fun z : ℤ => (z : ℝ)) d.difference
  push_cast at hdiff
  have hprod : 0 < (g : ℝ) * o.1.1 * D := by positivity
  have habs : (g : ℝ) * o.1.1 * D * |(packetF D g l o : ℝ)| =
      |(o.1.2.1 : ℝ) - o.1.2.2| := by
    calc
      _ = |((g : ℝ) * o.1.1 * D) * (packetF D g l o : ℝ)| := by
        rw [abs_mul, abs_of_pos hprod]
      _ = _ := congrArg abs hdiff
  have hwidth : |(o.1.2.1 : ℝ) - o.1.2.2| ≤ e.U :=
    abs_le.mpr ⟨by linarith [h1.2.1, h2.2.2], by linarith [h1.2.2, h2.2.1]⟩
  have hF : |(packetF D g l o : ℝ)| ≤ e.U / ((g : ℝ) * e.Q1 * D) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ |(packetF D g l o : ℝ)| * ((g : ℝ) * o.1.1 * D) := by
        gcongr
        exact hp.2.1
      _ = |(o.1.2.1 : ℝ) - o.1.2.2| := by rw [mul_comm]; exact habs
      _ ≤ e.U := hwidth
  have hone : 1 ≤ |(packetF D g l o : ℝ)| := by
    rw [← natAbs_cast_real]
    exact_mod_cast (show 1 ≤ (packetF D g l o).natAbs from
      Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr d.f_ne))
  exact ⟨hone, hF, hone.trans hF⟩

/-- The original normalized inner unit gate, stated in the actual packet c. -/
theorem normalized_inner_gate (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ}
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1) :
    quotient o.2.1.1 D * t ∈ factorCarrier e.Q2 ∧
      t.Coprime ((g * l) * packetC D g o) := by
  have d := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ho
  have hrmem := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.1
  have hr : 0 < o.2.1.1 := (factorCarrier_bounds hR hrmem).1
  obtain ⟨hwindow, hunit⟩ := (mem_normalizedCarrier (quotient_data hr hD).1).mp ht
  refine ⟨hwindow, ?_⟩
  have hrewrite : o.1.2.1 * ((o.2.1.2.1 * o.2.1.2.2) / D) =
      (g * l) * packetC D g o := by rw [d.N1_fact]; unfold packetC w0; ring
  rwa [hrewrite] at hunit

/-- No a-unit gate is inferred from CRT alone: actual gamma2 support supplies it. -/
theorem actual_normalized_gamma2_unit {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1)
    (hgamma : e.gamma2 (quotient o.2.1.1 D * t) ≠ 0) :
    t.Coprime ((g * l) * packetC D g o) ∧
      t.Coprime (e.residue.natAbs * packetC D g o) := by
  obtain ⟨hwindow, hunit⟩ := normalized_inner_gate e he.1 he.2.2.1
    he.2.2.2.2.1 he.2.2.2.1 Yb Ys hD hg hl ho ht
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hGamma2, _⟩ := he
  have hactive := (hGamma2 _ hwindow).2 hgamma
  have hta : t.Coprime e.residue.natAbs := hactive.of_dvd_left (dvd_mul_left _ _)
  have htc : t.Coprime (packetC D g o) := hunit.of_dvd_right (dvd_mul_left _ _)
  exact ⟨hunit, hta.mul_right htc⟩

/-- True Sinner window, including the half-unit nonempty boundary.
There is no assumed q=D/delta real equality or assumed t support. -/
theorem normalized_t_scale (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ}
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1) :
    e.Q2 * (delta : ℝ) / D ≤ (t : ℝ) ∧
      (t : ℝ) ≤ 2 * (e.Q2 * (delta : ℝ) / D) ∧
      (1 / 2 : ℝ) ≤ e.Q2 * (delta : ℝ) / D := by
  obtain ⟨_hp, _hN1, _hN2, hrmem, _hrp, _hsp, _hne, _hDo, hd, _rest⟩ :=
    fixedSlice_facts e Yb Ys D delta g l ho
  have hr := (factorCarrier_bounds hR hrmem).1
  have hwindow := (normalized_inner_gate e hN hQ hR hS Yb Ys hD hg hl ho ht).1
  have hw := factorCarrier_bounds hS hwindow
  have hfact := (quotient_data hr hD).2.2.2.1
  have hfactR : (delta : ℝ) * (quotient o.2.1.1 D : ℝ) = D := by
    exact_mod_cast (show delta * quotient o.2.1.1 D = D by simpa only [hd] using hfact)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have htlo : e.Q2 * (delta : ℝ) / D ≤ (t : ℝ) := by
    apply (div_le_iff₀ hDR).mpr
    calc
      _ ≤ ((quotient o.2.1.1 D * t : ℕ) : ℝ) * delta :=
        mul_le_mul_of_nonneg_right hw.2.1 (Nat.cast_nonneg _)
      _ = (t : ℝ) * D := by rw [← hfactR]; push_cast; ring
  have hthi : (t : ℝ) ≤ 2 * (e.Q2 * (delta : ℝ) / D) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hDR).mpr
    calc
      _ = ((quotient o.2.1.1 D * t : ℕ) : ℝ) * delta :=
        by rw [← hfactR]; push_cast; ring
      _ ≤ (2 * e.Q2) * delta :=
        mul_le_mul_of_nonneg_right hw.2.2 (Nat.cast_nonneg _)
      _ = _ := by ring
  have htpos : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    simpa only [hz, mul_zero, lt_self_iff_false] using hw.1
  have htone : (1 : ℝ) ≤ t := by exact_mod_cast (Nat.succ_le_iff.mpr htpos)
  exact ⟨htlo, hthi, by linarith⟩

/-- Final finite positive-Cauchy leaf with the PROVED representation payment.
J is evaluated on actual packet labels. No row-to-J identity or spectral bound
is a premise; that separate equality is exactly the remaining upstream consumer. -/
theorem scalar_packet_Cauchy_tau (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (J : Packet → ℂ) :
    ‖∑ o ∈ fixedSlice e Yb Ys D delta g l,
      e.smallCoreSquaredOuterCoefficient Yb Ys o * J (packetKey D delta g l o)‖ ^ 2 ≤
      fixedFirstEnergy e Yb Ys D delta g l *
        ∑ k ∈ packetImage e Yb Ys D delta g l,
          (((k.1.1 / (g * l)).divisors.card * D.divisors.card *
            k.1.2.divisors.card ^ 2 : ℕ) : ℝ) * ‖J k‖ ^ 2 := by
  have hE : 0 ≤ fixedFirstEnergy e Yb Ys D delta g l :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  apply (scalar_packet_Cauchy e Yb Ys D delta g l J).trans
  apply mul_le_mul_of_nonneg_left _ hE
  apply sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast packetFiber_card_le_tau e hN hQ hR hS Yb Ys hD hg hl k

end
end ImbalancedChen.Part3.ActualFixedFeaturePacketPushforwardSourceOnly

/-!
SOURCEONLY / UNCOMPILED / HOLD.
One finite operation only: separate the actual negative root by h mod A and
outer zeta^{-1} mod A. Arbitrary ORIGINAL row payload remains unchanged.
This does not normalize the L-dependent amplitude or prove a bare estimate.
The original signed exponential is connected to this standard character by
fourier_inverse_phase_eq_stdAddChar A (zeta*t) hcoprime h (-a).
No h or a unit condition is used. A=1 is included by [NeZero A].
-/
namespace ImbalancedChen.Part3.GeneralDRootResidueCostSourceOnly
noncomputable section
open Classical Finset
open scoped BigOperators

variable (A : ℕ) [NeZero A]

/-- zeta and t are the units supplied by the ORIGINAL active CRT/gcd gate. -/
def rootPhase (a h : ZMod A) (zeta t : (ZMod A)ˣ) : ℂ :=
  ZMod.stdAddChar (-a * h * (↑((zeta * t)⁻¹) : ZMod A))

/-- Once u=zeta^{-1} and k=[h] are fixed, this depends only on inner t. -/
def rootT (a : ZMod A) (u : (ZMod A)ˣ) (k : ZMod A)
    (t : (ZMod A)ˣ) : ℂ :=
  ZMod.stdAddChar (-a * k * ((u : ZMod A) * (↑(t⁻¹) : ZMod A)))

theorem rootPhase_eq_rootT (a h : ZMod A) (zeta t : (ZMod A)ˣ) :
    rootPhase A a h zeta t = rootT A a zeta⁻¹ h t := by
  unfold rootPhase rootT
  congr 1
  rw [mul_inv_rev]
  simp only [Units.val_mul]
  ring

variable {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]

/-- w keeps ALL masks, slow/reciprocal factors and complex amplitudes. -/
def originalRootRow (T : Finset τ) (H : Finset ℤ)
    (w : ι → τ → ℤ → ℂ) (tUnit : τ → (ZMod A)ˣ)
    (zeta : ι → (ZMod A)ˣ) (a : ZMod A) (o : ι) : ℂ :=
  ∑ t ∈ T, ∑ h ∈ H, w o t h * rootPhase A a (h : ZMod A) (zeta o) (tUnit t)

/-- Common residue gate in h, common root coefficient in t; w is UNCHANGED. -/
def rootPiece (T : Finset τ) (H : Finset ℤ)
    (w : ι → τ → ℤ → ℂ) (tUnit : τ → (ZMod A)ˣ)
    (a : ZMod A) (u : (ZMod A)ˣ) (k : ZMod A) (o : ι) : ℂ :=
  ∑ t ∈ T, ∑ h ∈ H,
    if (h : ZMod A) = k then w o t h * rootT A a u k (tUnit t) else 0

omit [DecidableEq ι] [DecidableEq τ] in
theorem originalRootRow_eq_sum_pieces [DecidableEq ι] [DecidableEq τ]
    (T : Finset τ) (H : Finset ℤ)
    (w : ι → τ → ℤ → ℂ) (tUnit : τ → (ZMod A)ˣ)
    (zeta : ι → (ZMod A)ˣ) (a : ZMod A) (o : ι) :
    originalRootRow A T H w tUnit zeta a o =
      ∑ k : ZMod A, rootPiece A T H w tUnit a (zeta o)⁻¹ k o := by
  classical
  unfold originalRootRow rootPiece
  calc
    _ = ∑ t ∈ T, ∑ h ∈ H, ∑ k : ZMod A,
        if (h : ZMod A) = k then
          w o t h * rootT A a (zeta o)⁻¹ k (tUnit t) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro h hh
      simp [rootPhase_eq_rootT]
    _ = ∑ t ∈ T, ∑ k : ZMod A, ∑ h ∈ H,
        if (h : ZMod A) = k then
          w o t h * rootT A a (zeta o)⁻¹ k (tUnit t) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The h-residue split costs A at THIS row-square stage. No phi(A) is hidden. -/
theorem originalRootRow_norm_sq_le (T : Finset τ) (H : Finset ℤ)
    (w : ι → τ → ℤ → ℂ) (tUnit : τ → (ZMod A)ˣ)
    (zeta : ι → (ZMod A)ˣ) (a : ZMod A) (o : ι) :
    ‖originalRootRow A T H w tUnit zeta a o‖ ^ 2 ≤
      (A : ℝ) * ∑ k : ZMod A,
        ‖rootPiece A T H w tUnit a (zeta o)⁻¹ k o‖ ^ 2 := by
  rw [originalRootRow_eq_sum_pieces]
  have hcs := complex_finset_cauchy_norm_sq (Finset.univ : Finset (ZMod A))
    (fun _ => (1 : ℂ))
    (fun k => rootPiece A T H w tUnit a (zeta o)⁻¹ k o)
  simpa [ZMod.card] using hcs

/-- Outer residue fibers are disjoint: their energy sum is exact. -/
theorem root_row_mass_le_fibres (O : Finset ι) (T : Finset τ) (H : Finset ℤ)
    (w : ι → τ → ℤ → ℂ) (tUnit : τ → (ZMod A)ˣ)
    (zeta : ι → (ZMod A)ˣ) (a : ZMod A) :
    (∑ o ∈ O, ‖originalRootRow A T H w tUnit zeta a o‖ ^ 2) ≤
      (A : ℝ) * ∑ u : (ZMod A)ˣ, ∑ k : ZMod A, ∑ o ∈ O,
        if (zeta o)⁻¹ = u then ‖rootPiece A T H w tUnit a u k o‖ ^ 2 else 0 := by
  classical
  have hfiber :
      (∑ u : (ZMod A)ˣ, ∑ k : ZMod A, ∑ o ∈ O,
        if (zeta o)⁻¹ = u then ‖rootPiece A T H w tUnit a u k o‖ ^ 2 else 0) =
        ∑ o ∈ O, ∑ k : ZMod A,
          ‖rootPiece A T H w tUnit a (zeta o)⁻¹ k o‖ ^ 2 := by
    calc
      _ = ∑ u : (ZMod A)ˣ, ∑ o ∈ O, ∑ k : ZMod A,
          if (zeta o)⁻¹ = u then ‖rootPiece A T H w tUnit a u k o‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact Finset.sum_comm
      _ = ∑ o ∈ O, ∑ u : (ZMod A)ˣ, ∑ k : ZMod A,
          if (zeta o)⁻¹ = u then ‖rootPiece A T H w tUnit a u k o‖ ^ 2 else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro o ho
        rw [Finset.sum_comm]
        simp
  calc
    _ ≤ ∑ o ∈ O, (A : ℝ) * ∑ k : ZMod A,
        ‖rootPiece A T H w tUnit a (zeta o)⁻¹ k o‖ ^ 2 :=
      Finset.sum_le_sum (fun o ho =>
        originalRootRow_norm_sq_le A T H w tUnit zeta a o)
    _ = (A : ℝ) * (∑ o ∈ O, ∑ k : ZMod A,
        ‖rootPiece A T H w tUnit a (zeta o)⁻¹ k o‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [← hfiber]

/-- Exact scalar splitting: every physical outer label remains in its own fiber. -/
theorem root_scalar_eq_blocks (O : Finset ι) (T : Finset τ) (H : Finset ℤ)
    (C : ι → ℂ) (w : ι → τ → ℤ → ℂ) (tUnit : τ → (ZMod A)ˣ)
    (zeta : ι → (ZMod A)ˣ) (a : ZMod A) :
    (∑ o ∈ O, C o * originalRootRow A T H w tUnit zeta a o) =
      ∑ u : (ZMod A)ˣ, ∑ k : ZMod A, ∑ o ∈ O,
        if (zeta o)⁻¹ = u then C o * rootPiece A T H w tUnit a u k o else 0 := by
  classical
  symm
  calc
    _ = ∑ u : (ZMod A)ˣ, ∑ o ∈ O, ∑ k : ZMod A,
        if (zeta o)⁻¹ = u then C o * rootPiece A T H w tUnit a u k o else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact Finset.sum_comm
    _ = ∑ o ∈ O, ∑ u : (ZMod A)ˣ, ∑ k : ZMod A,
        if (zeta o)⁻¹ = u then C o * rootPiece A T H w tUnit a u k o else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [Finset.sum_comm]
      simp
      rw [originalRootRow_eq_sum_pieces]
      exact (Finset.mul_sum _ _ _).symm

/-- Direct triangle accounting. Uniform scalar block bounds cost A*phi(A),
not its square root or fourth root. No such block bound is assumed/proved here. -/
theorem root_scalar_norm_le_blocks (O : Finset ι) (T : Finset τ) (H : Finset ℤ)
    (C : ι → ℂ) (w : ι → τ → ℤ → ℂ) (tUnit : τ → (ZMod A)ˣ)
    (zeta : ι → (ZMod A)ˣ) (a : ZMod A) :
    ‖∑ o ∈ O, C o * originalRootRow A T H w tUnit zeta a o‖ ≤
      ∑ u : (ZMod A)ˣ, ∑ k : ZMod A,
        ‖∑ o ∈ O, if (zeta o)⁻¹ = u then
          C o * rootPiece A T H w tUnit a u k o else 0‖ := by
  rw [root_scalar_eq_blocks]
  calc
    _ ≤ ∑ u : (ZMod A)ˣ,
        ‖∑ k : ZMod A, ∑ o ∈ O, if (zeta o)⁻¹ = u then
          C o * rootPiece A T H w tUnit a u k o else 0‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun u hu => norm_sum_le _ _)

/-- Conservative arithmetic only: triangle A^2 and full g,d1 enumeration
cost at most x^(3*sigma/2). This is OUTSIDE both analytic square roots. -/
theorem conservative_root_triangle_exponents {sigma kappa eps : ℝ}
    (hkappa : kappa ≤ sigma / 100) (heps : eps ≤ sigma / 10) :
    -4 * sigma + 5 * kappa + 3 * sigma / 2 + eps ≤ -47 * sigma / 20 ∧
      -15 * sigma / 4 + 21 * kappa / 4 + 3 * sigma / 2 + eps ≤
        -839 * sigma / 400 := by
  constructor <;> linarith
end
end ImbalancedChen.Part3.GeneralDRootResidueCostSourceOnly
/-!
SOURCEONLY / UNCOMPILED companion. Load after the EXACT df2171ee 601-line
packet dictionary and f7b8a17e general-D finite root-residue draft (imports
first). No parent is changed. This file DEMODULATES the literal CRT Fourier
phase by its actual slow phase, then proves the resulting common mode is a
function of (b,c,f), the fixed root unit u, and the h residue k. There is NO
assumed row-to-packet equality or supplied phase identity among the premises.
W(s),omega(h) are common arbitrary coefficients; their concrete Fourier-mode
construction and bounds belong to the independent literal log adapter.
-/

namespace ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly
noncomputable section
open Classical Finset GeneralDGateNormalization
open GeneralDActivePairCountSourceOnly GeneralDActiveOuterEnergySourceOnly
open ActualFixedFeaturePacketPushforwardSourceOnly
open GeneralDRootResidueCostSourceOnly
open scoped BigOperators FourierTransform

def baseCarrier (e : MediumAtom) (q : ℕ) : Finset ℕ :=
  ((factorCarrier e.Q2).filter (fun s => q ∣ s)).image (fun s => s / q)

def zeta (D delta g : ℕ) (o : OuterIndex) : ℕ :=
  packetC D g o * o.1.1 * D * r0 delta o

def literalLcm (o : OuterIndex) (s : ℕ) : ℕ :=
  (o.1.1 * (o.2.1.1 * s)).lcm (o.1.1 * (o.2.1.2.1 * o.2.1.2.2))

def crtPhase (a : ℤ) (o : OuterIndex) (s : ℕ) (h : ℤ) : ℂ :=
  fourier h (((ComplexCRT.residue (o.1.1 * (o.2.1.1 * s))
    (o.1.1 * (o.2.1.2.1 * o.2.1.2.2)) o.1.2.1 o.1.2.2 a : ℝ) /
      literalLcm o s : ℝ) : UnitAddCircle)

def slowPhase (a : ℤ) (o : OuterIndex) (s : ℕ) (h : ℤ) : ℂ :=
  fourier h (((a : ℝ) / ((o.1.2.1 : ℝ) * literalLcm o s) : ℝ) : UnitAddCircle)

def naturalRoot (A : ℕ) (a : ℤ) (z t : ℕ) (h : ℤ) : ℂ :=
  fourier h (((-(a : ℝ) *
    (CanonicalReciprocalPhase.wPhaseInverse (z * t) A : ℝ) / A : ℝ) : UnitAddCircle))

def reciprocal (a : ℤ) (k : Packet) (t : ℕ) (h : ℤ) : ℂ :=
  fourier h ((((a : ℝ) * (k.2 : ℝ) *
    (CanonicalReciprocalPhase.wPhaseInverse (k.1.1 * t) k.1.2 : ℝ) / k.1.2 : ℝ) :
      UnitAddCircle))

def strippedPhase (a : ℤ) (o : OuterIndex) (s : ℕ) (h : ℤ) : ℂ :=
  crtPhase a o s h * (starRingEnd ℂ) (slowPhase a o s h)

/-- Exact carrier descent, on the literal fixedSlice, including all endpoints. -/
theorem normalizedCarrier_eq_packetCarrier (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1 =
      (baseCarrier e (D / delta)).filter
        (fun t => t.Coprime ((g * l) * packetC D g o)) := by
  have d := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ho
  have hd := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.2.2.2.2.2.1
  have hq : quotient o.2.1.1 D = D / delta := by simp only [quotient, hd]
  have hrewrite : o.1.2.1 * ((o.2.1.2.1 * o.2.1.2.2) / D) =
      (g * l) * packetC D g o := by rw [d.N1_fact]; unfold packetC w0; ring
  simp only [normalizedCarrier, baseCarrier, hq, hrewrite]

/-- The actual three-factor Fourier dictionary, instantiated on the ORIGINAL
labels. t need not be in an interval for this arithmetic theorem. -/
theorem fixed_phase_data (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : 0 < t) (hunit : t.Coprime (o.1.2.1 * w0 D o)) (a h : ℤ) :
    (zeta D delta g o).Coprime (g * l) ∧ t.Coprime (g * l) ∧
    crtPhase a o (quotient o.2.1.1 D * t) h =
      naturalRoot (g * l) a (zeta D delta g o) t h *
        slowPhase a o (quotient o.2.1.1 D * t) h *
        reciprocal a (packetKey D delta g l o) t h := by
  obtain ⟨_hp0, hN10, hN20, hr0, hrp0, hsp0, _hne, _hDo, hd, hgc, hsup, hDw, hgate⟩ :=
    fixedSlice_facts e Yb Ys D delta g l ho
  have d := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ho
  have hr := (factorCarrier_bounds hR hr0).1
  have hw := Nat.mul_pos (factorCarrier_bounds hR hrp0).1 (factorCarrier_bounds hS hsp0).1
  have hN1 := (factorCarrier_bounds hN hN10).1
  have hN2 := (factorCarrier_bounds hN hN20).1
  have hq := (quotient_data hr hD).1
  have hqe : D / delta = quotient o.2.1.1 D := by simp only [quotient, hd]
  have horiginal : originalGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2)
      D o.1.2.1 o.1.2.2 (quotient o.2.1.1 D * t) := by
    apply (originalGate_iff hr hD hDw).mpr
    exact ⟨dvd_mul_right _ _, hgate, by
      simpa only [Nat.mul_div_cancel_left t hq, w0] using hunit⟩
  have hpkt := sharedGeneralDRootPacket_fourier d.p_pos hr (Nat.mul_pos hq ht) hw
    hN1 hN2 horiginal.2 a h
  dsimp only at hpkt
  simp only [horiginal.1, hd, hgc, hsup, hqe, Nat.mul_div_cancel_left t hq] at hpkt
  obtain ⟨_hq, _hr, _ht, _hA, _hc, _hs, _hv, _hrq, _hbc, hz, htAc, _hroot, _hrecip, hfour⟩ := hpkt
  change (zeta D delta g o).Coprime (g * l) at hz
  change t.Coprime ((g * l) * packetC D g o) at htAc
  refine ⟨hz, htAc.of_dvd_right (dvd_mul_right _ _), ?_⟩
  exact hfour

theorem fixed_zeta_coprime (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    (zeta D delta g o).Coprime (g * l) := by
  exact (fixed_phase_data e hN hQ hR hS Yb Ys hD hg hl ho
    (by norm_num : 0 < (1 : ℕ)) (by simp) (0 : ℤ) (0 : ℤ)).1

private theorem fourier_mul_conj_self (h : ℤ) (x : UnitAddCircle) :
    fourier h x * (starRingEnd ℂ) (fourier h x) = 1 := by
  have hn : ‖fourier h x‖ = 1 := by simp only [fourier_apply, Circle.norm_coe]
  simpa only [hn, one_pow, Complex.ofReal_one] using Complex.mul_conj' (fourier h x)

/-- Restore the exact original character after the analytic symbol has
absorbed the whole slow factor. This identity uses no arithmetic gate. -/
theorem slowPhase_mul_stripped (a : ℤ) (o : OuterIndex) (s : ℕ) (h : ℤ) :
    slowPhase a o s h * strippedPhase a o s h = crtPhase a o s h := by
  calc
    _ = crtPhase a o s h * (slowPhase a o s h * (starRingEnd ℂ) (slowPhase a o s h)) := by
      unfold strippedPhase
      ring
    _ = _ := by
      rw [show slowPhase a o s h * (starRingEnd ℂ) (slowPhase a o s h) = 1 from
        fourier_mul_conj_self _ _, mul_one]

theorem strippedPhase_eq_root_reciprocal (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : 0 < t) (hunit : t.Coprime (o.1.2.1 * w0 D o)) (a h : ℤ) :
    strippedPhase a o (quotient o.2.1.1 D * t) h =
      naturalRoot (g * l) a (zeta D delta g o) t h *
        reciprocal a (packetKey D delta g l o) t h := by
  have hf := (fixed_phase_data e hN hQ hR hS Yb Ys hD hg hl ho ht hunit a h).2.2
  unfold strippedPhase
  rw [hf]
  have hs : slowPhase a o (quotient o.2.1.1 D * t) h *
      (starRingEnd ℂ) (slowPhase a o (quotient o.2.1.1 D * t) h) = 1 :=
    fourier_mul_conj_self _ _
  calc
    _ = (naturalRoot (g * l) a (zeta D delta g o) t h *
        reciprocal a (packetKey D delta g l o) t h) *
      (slowPhase a o (quotient o.2.1.1 D * t) h *
        (starRingEnd ℂ) (slowPhase a o (quotient o.2.1.1 D * t) h)) := by ring
    _ = _ := by rw [hs, mul_one]

def natUnit (A n : ℕ) : (ZMod A)ˣ :=
  if hn : n.Coprime A then ZMod.unitOfCoprime n hn else 1

theorem natUnit_coe {A n : ℕ} (hn : n.Coprime A) :
    (natUnit A n : ZMod A) = (n : ZMod A) := by
  simp only [natUnit, dif_pos hn, ZMod.coe_unitOfCoprime]

def rootFeature (D delta g l : ℕ) (o : OuterIndex) : (ZMod (g * l))ˣ :=
  (natUnit (g * l) (zeta D delta g o))⁻¹

theorem naturalRoot_eq_rootT (A : ℕ) [NeZero A] (a h : ℤ) {z t : ℕ}
    (hz : z.Coprime A) (ht : t.Coprime A) :
    naturalRoot A a z t h =
      rootT A (a : ZMod A) (natUnit A z)⁻¹ (h : ZMod A) (natUnit A t) := by
  have hp : ((natUnit A z * natUnit A t : (ZMod A)ˣ) : ZMod A) =
      ((z * t : ℕ) : ZMod A) := by
    simp only [Units.val_mul, natUnit_coe hz, natUnit_coe ht, Nat.cast_mul]
  have hi : (((z * t : ℕ) : ZMod A))⁻¹ =
      (((natUnit A z * natUnit A t)⁻¹ : (ZMod A)ˣ) : ZMod A) := by
    rw [← hp, ZMod.inv_coe_unit]
  have he := fourier_inverse_phase_eq_stdAddChar A (z * t) (hz.mul_left ht) h (-a)
  have hroot : naturalRoot A a z t h =
      rootPhase A (a : ZMod A) (h : ZMod A) (natUnit A z) (natUnit A t) := by
    calc
      _ = ZMod.stdAddChar (((h * (-a) : ℤ) : ZMod A) *
          (((z * t : ℕ) : ZMod A))⁻¹) := by
        simpa only [naturalRoot, Int.cast_neg, neg_mul] using he
      _ = _ := by
        unfold rootPhase
        rw [hi]
        congr 1
        push_cast
        ring
  exact hroot.trans (rootPhase_eq_rootT A _ _ _ _)

def branch (negative : Bool) (z : ℂ) : ℂ := if negative then (starRingEnd ℂ) z else z

theorem branch_mul (negative : Bool) (z w : ℂ) :
    branch negative (z * w) = branch negative z * branch negative w := by
  cases negative
  · rfl
  · exact map_mul (starRingEnd ℂ) z w

/-- Common-mode row with the ACTUAL CRT phase and exact slow demodulation.
negative conjugates the PHASE ONLY; W may retain original complex gamma2. -/
def literalMode {g l : ℕ} (e : MediumAtom) (D : ℕ) (a : ℤ) (negative : Bool)
    (W : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) (k : ZMod (g * l))
    (o : OuterIndex) : ℂ :=
  ∑ t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1,
    ∑ h ∈ H, if (h : ZMod (g * l)) = k then
      W (quotient o.2.1.1 D * t) * omega h *
        branch negative (strippedPhase a o (quotient o.2.1.1 D * t) h) else 0

/-- The constructed packet function. The old A-unit and c-unit gates remain.
All parameters besides the packet are fixed for the whole component. -/
def packetJ (e : MediumAtom) (D delta g l : ℕ) [NeZero (g * l)]
    (a : ℤ) (negative : Bool) (u : (ZMod (g * l))ˣ) (k : ZMod (g * l))
    (W : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) (p : Packet) : ℂ :=
  ∑ t ∈ baseCarrier e (D / delta),
    if t.Coprime ((g * l) * p.1.2) then
      ∑ h ∈ H, if (h : ZMod (g * l)) = k then
        W (D / delta * t) * omega h *
          (branch negative (rootT (g * l) (a : ZMod (g * l)) u k (natUnit (g * l) t)) *
            branch negative (reciprocal a p t h)) else 0
    else 0

/-- Exact finite matching to J, with the actual root feature CONSTRUCTED from o.
No equality of an outer-dependent row with a packet function is hypothesized. -/
theorem literalMode_eq_packetJ (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} [NeZero (g * l)]
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (a : ℤ) (negative : Bool) (k : ZMod (g * l))
    (W : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) :
    literalMode (g := g) (l := l) e D a negative W omega H k o =
      packetJ e D delta g l a negative (rootFeature D delta g l o) k W omega H
        (packetKey D delta g l o) := by
  have hd := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.2.2.2.2.2.1
  have hrmem := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.1
  have hr := (factorCarrier_bounds hR hrmem).1
  have hq := (quotient_data hr hD).1
  have hqe : quotient o.2.1.1 D = D / delta := by simp only [quotient, hd]
  have hcarrier := normalizedCarrier_eq_packetCarrier e hN hQ hR hS Yb Ys hD hg hl ho
  unfold literalMode
  rw [hcarrier, sum_filter]
  unfold packetJ
  apply sum_congr rfl
  intro t ht
  change (if t.Coprime ((g * l) * packetC D g o) then _ else (0 : ℂ)) =
    (if t.Coprime ((g * l) * packetC D g o) then _ else 0)
  by_cases htc : t.Coprime ((g * l) * packetC D g o)
  · simp only [if_pos htc]
    have htold : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
        (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1 := by
      rw [hcarrier]
      exact mem_filter.mpr ⟨ht, htc⟩
    obtain ⟨hwindow, hunit⟩ := (mem_normalizedCarrier hq).mp htold
    have htpos : 0 < t := by
      have hp := (factorCarrier_bounds hS hwindow).1
      by_contra hz
      have hz0 : t = 0 := by omega
      simp only [hz0, mul_zero, lt_self_iff_false] at hp
    change t.Coprime (o.1.2.1 * w0 D o) at hunit
    apply sum_congr rfl
    intro h hh
    by_cases hhk : (h : ZMod (g * l)) = k
    · rw [if_pos hhk, if_pos hhk]
      have hdta := fixed_phase_data e hN hQ hR hS Yb Ys hD hg hl ho htpos hunit a h
      rw [strippedPhase_eq_root_reciprocal e hN hQ hR hS Yb Ys hD hg hl ho htpos hunit,
        branch_mul, naturalRoot_eq_rootT (g * l) a h hdta.1 hdta.2.1]
      rw [hqe, hhk]
      rfl
    · simp only [if_neg hhk]
  · simp only [if_neg htc]

def rootSlice (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (u : (ZMod (g * l))ˣ) : Finset OuterIndex :=
  (fixedSlice e Yb Ys D delta g l).filter (fun o => rootFeature D delta g l o = u)

/-- Exact scalar mode matching on a fixed u fibre. The outer multiplier stays
on the Co side, so none of its p,r,w,N1 dependence is silently discarded. -/
theorem rootSlice_scalar_mode_eq (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} [NeZero (g * l)]
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (a : ℤ) (negative : Bool) (u : (ZMod (g * l))ˣ) (k : ZMod (g * l))
    (alpha : OuterIndex → ℂ) (W : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) :
    (∑ o ∈ rootSlice e Yb Ys D delta g l u,
      e.smallCoreSquaredOuterCoefficient Yb Ys o * alpha o *
        literalMode (g := g) (l := l) e D a negative W omega H k o) =
      ∑ o ∈ rootSlice e Yb Ys D delta g l u,
        (e.smallCoreSquaredOuterCoefficient Yb Ys o * alpha o) *
          packetJ e D delta g l a negative u k W omega H (packetKey D delta g l o) := by
  apply sum_congr rfl
  intro o ho
  obtain ⟨hfixed, hfeature⟩ := mem_filter.mp ho
  rw [literalMode_eq_packetJ e hN hQ hR hS Yb Ys hD hg hl hfixed, hfeature]

/-- Adding the genuine root unit feature only RESTRICTS each old packet fibre.
The already proved physical representation fee is unchanged. -/
theorem refined_packetFiber_card_le_tau (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (u : (ZMod (g * l))ˣ) (p : Packet) :
    ((rootSlice e Yb Ys D delta g l u).filter (fun o => packetKey D delta g l o = p)).card ≤
      (p.1.1 / (g * l)).divisors.card * D.divisors.card * p.1.2.divisors.card ^ 2 := by
  have hsub : (rootSlice e Yb Ys D delta g l u).filter
      (fun o => packetKey D delta g l o = p) ⊆ packetFiber e Yb Ys D delta g l p := by
    intro o ho
    obtain ⟨hroot, hpacket⟩ := mem_filter.mp ho
    exact mem_filter.mpr ⟨(mem_filter.mp hroot).1, hpacket⟩
  exact (card_le_card hsub).trans
    (packetFiber_card_le_tau e hN hQ hR hS Yb Ys hD hg hl p)

def rootPacketImage (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (u : (ZMod (g * l))ˣ) : Finset Packet :=
  (rootSlice e Yb Ys D delta g l u).image (packetKey D delta g l)

def rootGroupedCoefficient (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (u : (ZMod (g * l))ˣ) (alpha : OuterIndex → ℂ) (p : Packet) : ℂ :=
  ∑ o ∈ (rootSlice e Yb Ys D delta g l u).filter
      (fun o => packetKey D delta g l o = p),
    e.smallCoreSquaredOuterCoefficient Yb Ys o * alpha o

/-- The literal common mode is EXACTLY pushed to the packet image with the
original Co times the still-outer-dependent alpha summed on each true fibre. -/
theorem rootSlice_scalar_mode_eq_packets (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} [NeZero (g * l)]
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (a : ℤ) (negative : Bool) (u : (ZMod (g * l))ˣ) (k : ZMod (g * l))
    (alpha : OuterIndex → ℂ) (W : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) :
    (∑ o ∈ rootSlice e Yb Ys D delta g l u,
      e.smallCoreSquaredOuterCoefficient Yb Ys o * alpha o *
        literalMode (g := g) (l := l) e D a negative W omega H k o) =
      ∑ p ∈ rootPacketImage e Yb Ys D delta g l u,
        rootGroupedCoefficient e Yb Ys D delta g l u alpha p *
          packetJ e D delta g l a negative u k W omega H p := by
  rw [rootSlice_scalar_mode_eq e hN hQ hR hS Yb Ys hD hg hl]
  have hf := sum_fiberwise_of_maps_to
    (s := rootSlice e Yb Ys D delta g l u)
    (t := rootPacketImage e Yb Ys D delta g l u) (g := packetKey D delta g l)
    (fun o ho => mem_image_of_mem _ ho)
    (fun o => (e.smallCoreSquaredOuterCoefficient Yb Ys o * alpha o) *
      packetJ e D delta g l a negative u k W omega H (packetKey D delta g l o))
  rw [← hf]
  apply sum_congr rfl
  intro p _
  unfold rootGroupedCoefficient
  rw [sum_mul]
  apply sum_congr rfl
  intro o ho
  rw [(mem_filter.mp ho).2]

private theorem fourier_neg_real_argument (h : ℤ) (x : ℝ) :
    fourier h ((-x : ℝ) : UnitAddCircle) =
      (starRingEnd ℂ) (fourier h ((x : ℝ) : UnitAddCircle)) := by
  calc
    _ = fourier (-h) ((x : ℝ) : UnitAddCircle) := by
      rw [fourier_coe_apply, fourier_coe_apply]
      push_cast
      congr 1
      ring
    _ = _ := fourier_neg

theorem reciprocal_neg_residue (a : ℤ) (p : Packet) (t : ℕ) (h : ℤ) :
    reciprocal (-a) p t h = (starRingEnd ℂ) (reciprocal a p t h) := by
  simpa only [reciprocal, Int.cast_neg, neg_mul, neg_div] using
    fourier_neg_real_argument h
      ((a : ℝ) * (p.2 : ℝ) *
        (CanonicalReciprocalPhase.wPhaseInverse (p.1.1 * t) p.1.2 : ℝ) / p.1.2)

def signedResidue (negative : Bool) (a : ℤ) : ℤ := if negative then -a else a

theorem branch_reciprocal (negative : Bool) (a : ℤ) (p : Packet) (t : ℕ) (h : ℤ) :
    branch negative (reciprocal a p t h) =
      reciprocal (signedResidue negative a) p t h := by
  cases negative
  · rfl
  · exact (reciprocal_neg_residue a p t h).symm

def commonLambda (D delta g l : ℕ) [NeZero (g * l)] (a : ℤ) (negative : Bool)
    (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)) (W : ℕ → ℂ) (t : ℕ) : ℂ :=
  W (D / delta * t) * branch negative
    (rootT (g * l) (a : ZMod (g * l)) u k (natUnit (g * l) t))

def commonOmega (g l : ℕ) (k : ZMod (g * l)) (omega : ℤ → ℂ) (h : ℤ) : ℂ :=
  if (h : ZMod (g * l)) = k then omega h else 0

/-- The final packet function has precisely one common t coefficient and one
common signed h coefficient. For the conjugate branch only a changes sign. -/
theorem packetJ_eq_common_reciprocal (e : MediumAtom) (D delta g l : ℕ)
    [NeZero (g * l)] (a : ℤ) (negative : Bool) (u : (ZMod (g * l))ˣ)
    (k : ZMod (g * l)) (W : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) (p : Packet) :
    packetJ e D delta g l a negative u k W omega H p =
      ∑ t ∈ baseCarrier e (D / delta), if t.Coprime ((g * l) * p.1.2) then
        ∑ h ∈ H, commonLambda D delta g l a negative u k W t *
          commonOmega g l k omega h * reciprocal (signedResidue negative a) p t h
      else 0 := by
  unfold packetJ
  apply sum_congr rfl
  intro t _
  split_ifs with ht
  · apply sum_congr rfl
    intro h _
    by_cases hh : (h : ZMod (g * l)) = k
    · simp only [if_pos hh, commonLambda, commonOmega, branch_reciprocal]
      ring
    · simp only [if_neg hh, commonOmega, mul_zero, zero_mul]
  · rfl

theorem baseCarrier_window (e : MediumAtom) (q : ℕ) {t : ℕ}
    (ht : t ∈ baseCarrier e q) : q * t ∈ factorCarrier e.Q2 := by
  obtain ⟨s, hs, heq⟩ := mem_image.mp ht
  obtain ⟨hs, hdiv⟩ := mem_filter.mp hs
  rw [← heq, Nat.mul_div_cancel' hdiv]
  exact hs

private theorem mem_factorCarrier_real {S : ℝ} (hS : 0 ≤ S) {n : ℕ} :
    n ∈ factorCarrier S ↔ S ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * S := by
  simp only [factorCarrier, mem_Icc, Nat.ceil_le,
    Nat.le_floor_iff (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS)]

/-- The quotient image is EXACTLY the physical dyadic interval at S/q.
This is a true endpoint identity, not insertion of terms inside a square. -/
theorem baseCarrier_eq_factorCarrier_div (e : MediumAtom) (hS : 0 ≤ e.Q2)
    {q : ℕ} (hq : 0 < q) :
    baseCarrier e q = factorCarrier (e.Q2 / (q : ℝ)) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  ext t
  constructor
  · intro ht
    have hs := (mem_factorCarrier_real hS).mp (baseCarrier_window e q ht)
    apply (mem_factorCarrier_real (div_nonneg hS hqr.le)).mpr
    constructor
    · apply (div_le_iff₀ hqr).mpr
      simpa only [Nat.cast_mul, mul_comm] using hs.1
    · have hu : (t : ℝ) ≤ (2 * e.Q2) / (q : ℝ) := by
        apply (le_div_iff₀ hqr).mpr
        simpa only [Nat.cast_mul, mul_comm] using hs.2
      simpa only [div_eq_mul_inv, mul_assoc] using hu
  · intro ht
    have hs := (mem_factorCarrier_real (div_nonneg hS hqr.le)).mp ht
    have htq : q * t ∈ factorCarrier e.Q2 := by
      apply (mem_factorCarrier_real hS).mpr
      constructor
      · have hlo := (div_le_iff₀ hqr).mp hs.1
        simpa only [Nat.cast_mul, mul_comm] using hlo
      · have hu : (t : ℝ) ≤ (2 * e.Q2) / (q : ℝ) := by
          simpa only [div_eq_mul_inv, mul_assoc] using hs.2
        have hup := (le_div_iff₀ hqr).mp hu
        simpa only [Nat.cast_mul, mul_comm] using hup
    apply mem_image.mpr
    exact ⟨q * t, mem_filter.mpr ⟨htq, dvd_mul_right _ _⟩,
      Nat.mul_div_cancel_left t hq⟩

def packetJUnit (e : MediumAtom) (D delta g l : ℕ) [NeZero (g * l)]
    (negative : Bool) (u : (ZMod (g * l))ˣ) (k : ZMod (g * l))
    (M : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) (p : Packet) : ℂ :=
  ∑ t ∈ baseCarrier e (D / delta),
    if t.Coprime ((g * l) * p.1.2) ∧ t.Coprime (e.residue.natAbs * p.1.2) then
      ∑ h ∈ H, if (h : ZMod (g * l)) = k then
        (e.gamma2 (D / delta * t) * M (D / delta * t)) * omega h *
          (branch negative (rootT (g * l) (e.residue : ZMod (g * l)) u k (natUnit (g * l) t)) *
            branch negative (reciprocal e.residue p t h)) else 0
    else 0

/-- Exact zero-cost a-unit insertion using ORIGINAL gamma2 support. It works
also at gamma2=0 and leaves gamma2 outside the conjugated physical phase. -/
theorem actual_packetJ_eq_unit_filtered {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (D delta g l : ℕ) [NeZero (g * l)]
    (negative : Bool) (u : (ZMod (g * l))ˣ) (k : ZMod (g * l))
    (M : ℕ → ℂ) (omega : ℤ → ℂ) (H : Finset ℤ) (p : Packet) :
    packetJ e D delta g l e.residue negative u k
      (fun s => e.gamma2 s * M s) omega H p =
        packetJUnit e D delta g l negative u k M omega H p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hGamma2, _⟩ := he
  unfold packetJ packetJUnit
  apply sum_congr rfl
  intro t ht
  by_cases htc : t.Coprime ((g * l) * p.1.2)
  · by_cases hzero : e.gamma2 (D / delta * t) = 0
    · simp [hzero]
    · have hwindow := baseCarrier_window e (D / delta) ht
      have hunit := (hGamma2 _ hwindow).2 hzero
      have hta : t.Coprime e.residue.natAbs := hunit.of_dvd_left (dvd_mul_left _ _)
      have htc0 : t.Coprime p.1.2 := htc.of_dvd_right (dvd_mul_left _ _)
      have hnew := hta.mul_right htc0
      simp only [if_pos htc, if_pos (And.intro htc hnew)]
  · simp [htc]

end
end ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly
