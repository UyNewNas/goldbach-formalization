import ImbalancedChen.Part3SharedFirstFactorGeneralDPairedFourier

/-!
# Complete guarded-row adapter for the actual finite general-D Gram

The original `smallCoreSquaredRowTerm` is used literally, including its
gcd/CRT gates, `gamma2`, low pass and complex Poisson amplitude. Its Gram
has four signed packet branches. Each packet retains the root inverse,
the complete slow phase and the reciprocal inverse, with the actual gcd
constructed separately from the original labels.

The final equality applies on the original finite inner carrier and keeps
the original signed resonance gate. It is an exact adapter, with no new
spectral estimate, positivity claim for the complementary block, carrier
enlargement, or (y,z) regrouping. Its imported paired identity is a source
candidate pending separate acceptance.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset CommonSmoothCutoff
open scoped BigOperators SchwartzMap FourierTransform

namespace SharedGeneralDRowAdapter

/-- Three complete phases, with the actual gcd and original signed labels. -/
def packet (p r s s' w N1 N2 : ℕ) (a h h' : ℤ) : ℂ :=
  let D := (r * s).gcd w
  let d := r.gcd D
  let q := D / d
  let r0 := r / d
  let t := s / q
  let t' := s' / q
  let g := N1.gcd N2
  let d1 := CanonicalReciprocalData.supportedPart (N1 / g) g
  let n1 := CanonicalReciprocalData.coprimePart (N1 / g) g
  let n2 := N2 / g
  let A := g * d1
  let w0 := w / D
  let b := A * n2 * r0
  let c := n1 * w0
  let zeta := c * p * D * r0
  let K := (p * D) * r0 * w0
  let f : ℤ := ((d1 : ℤ) * n1 - n2) / (p * D : ℕ)
  let k : ℤ := h * (t' : ℤ) - h' * (t : ℤ)
  let z := t * t'
  fourier 1
      (((-(a : ℝ) * (k : ℝ) *
        (CanonicalReciprocalPhase.wPhaseInverse (zeta * z) A : ℝ) / A) : ℝ) :
          UnitAddCircle) *
    fourier 1 ((((a : ℝ) * (k : ℝ) /
      ((N1 : ℝ) * K * z)) : ℝ) : UnitAddCircle) *
    fourier 1
      ((((a : ℝ) * (f : ℝ) * (k : ℝ) *
        (CanonicalReciprocalPhase.wPhaseInverse (b * z) c : ℝ) / c) : ℝ) :
          UnitAddCircle)

private def character (p r s w N1 N2 : ℕ) (a h : ℤ) : ℂ :=
  let L := (p * (r * s)).lcm (p * w)
  fourier h
    (((ComplexCRT.residue (p * (r * s)) (p * w) N1 N2 a : ℝ) / L : ℝ) :
      UnitAddCircle)

/-- The original complex amplitude, including the exact zero-frequency gate. -/
def amplitude (d : MediumAtom) (Z : ℝ) (p r s w : ℕ) (h : ℤ) : ℂ :=
  let L := (p * (r * s)).lcm (p * w)
  let T := d.V / (L : ℝ)
  if h = 0 then 0 else
    (poissonSmoothLowPass (T * (h : ℝ) / Z) : ℂ) *
      (T • (𝓕 dyadicCutoffSchwartz) (T * (h : ℝ)))

private theorem character_pair
    {p r s s' w N1 N2 : ℕ}
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s') (hw : 0 < w)
    (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hc : ComplexCRT.Compatible (p * (r * s)) (p * w) N1 N2)
    (hc' : ComplexCRT.Compatible (p * (r * s')) (p * w) N1 N2)
    (hsame : (r * s').gcd w = (r * s).gcd w) (a h h' : ℤ) :
    character p r s w N1 N2 a h * star (character p r s' w N1 N2 a h') =
      packet p r s s' w N1 N2 a h h' := by
  have hdata := sharedGeneralD_paired_fourier hp hr hs hs' hw hN1 hN2 hc hc' hsame a h h'
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, hphase⟩
  exact hphase

private theorem star_character (p r s w N1 N2 : ℕ) (a h : ℤ) :
    star (character p r s w N1 N2 a h) = character p r s w N1 N2 a (-h) := by
  unfold character
  dsimp only
  simp only [Complex.star_def]
  exact fourier_neg.symm

private theorem atom_factor (d : MediumAtom) (Z : ℝ) (p r s w N1 N2 : ℕ) (h : ℤ) :
    let L := (p * (r * s)).lcm (p * w)
    (poissonSmoothLowPass ((d.V / (L : ℝ)) * (h : ℝ) / Z) : ℂ) *
        poissonNonzeroFrequency (d.V / (L : ℝ))
          ((ComplexCRT.residue (p * (r * s)) (p * w) N1 N2 d.residue : ℝ) /
            (L : ℝ)) h =
      amplitude d Z p r s w h * character p r s w N1 N2 d.residue h := by
  dsimp only
  unfold amplitude character
  dsimp only
  by_cases hh : h = 0
  · simp only [hh, poissonNonzeroFrequency_zero, if_pos rfl, mul_zero, zero_mul]
  · simp only [poissonNonzeroFrequency, if_neg hh]
    ring

private theorem character_gram_four_branches
    {p r s s' w N1 N2 : ℕ}
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s') (hw : 0 < w)
    (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hc : ComplexCRT.Compatible (p * (r * s)) (p * w) N1 N2)
    (hc' : ComplexCRT.Compatible (p * (r * s')) (p * w) N1 N2)
    (hsame : (r * s').gcd w = (r * s).gcd w) (a h h' : ℤ)
    (lambda mu alpha beta : ℂ) :
    (lambda * ((alpha * character p r s w N1 N2 a h).re : ℂ)) *
        star (mu * ((beta * character p r s' w N1 N2 a h').re : ℂ)) =
      (lambda * star mu) / 4 *
        (alpha * star beta * packet p r s s' w N1 N2 a h h' +
          alpha * beta * packet p r s s' w N1 N2 a h (-h') +
          star alpha * star beta * packet p r s s' w N1 N2 a (-h) h' +
          star alpha * beta * packet p r s s' w N1 N2 a (-h) (-h')) := by
  have hpm := character_pair hp hr hs hs' hw hN1 hN2 hc hc' hsame a h h'
  have hpp : character p r s w N1 N2 a h * character p r s' w N1 N2 a h' =
      packet p r s s' w N1 N2 a h (-h') := by
    simpa only [star_character, neg_neg] using
      character_pair hp hr hs hs' hw hN1 hN2 hc hc' hsame a h (-h')
  have hmm : star (character p r s w N1 N2 a h) *
      star (character p r s' w N1 N2 a h') =
        packet p r s s' w N1 N2 a (-h) h' := by
    simpa only [star_character] using
      character_pair hp hr hs hs' hw hN1 hN2 hc hc' hsame a (-h) h'
  have hmp : star (character p r s w N1 N2 a h) *
      character p r s' w N1 N2 a h' =
        packet p r s s' w N1 N2 a (-h) (-h') := by
    simpa only [star_character, neg_neg] using
      character_pair hp hr hs hs' hw hN1 hN2 hc hc' hsame a (-h) (-h')
  rw [sharedGeneralD_realProjection_four_branches]
  calc
    _ = (lambda * star mu) / 4 *
        (alpha * star beta *
            (character p r s w N1 N2 a h * star (character p r s' w N1 N2 a h')) +
          alpha * beta *
            (character p r s w N1 N2 a h * character p r s' w N1 N2 a h') +
          star alpha * star beta *
            (star (character p r s w N1 N2 a h) * star (character p r s' w N1 N2 a h')) +
          star alpha * beta *
            (star (character p r s w N1 N2 a h) * character p r s' w N1 N2 a h')) := by
      simp only [star_mul]
      ring
    _ = _ := by rw [hpm, hpp, hmm, hmp]

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : 0 < n := by
  obtain ⟨hlo, _⟩ := Finset.mem_Icc.mp hn
  have hc : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

end SharedGeneralDRowAdapter

/-- The exact four-branch packet of two literal guarded original rows. -/
def MediumAtom.smallCoreSquaredPairedPacketTerm (d : MediumAtom) (Z : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) (u v : ℕ × ℤ) : ℂ :=
  let p := o.1.1
  let N1 := o.1.2.1
  let N2 := o.1.2.2
  let r := o.2.1.1
  let w := o.2.1.2.1 * o.2.1.2.2
  let D := o.2.2
  let alpha := SharedGeneralDRowAdapter.amplitude d Z p r u.1 w u.2
  let beta := SharedGeneralDRowAdapter.amplitude d Z p r v.1 w v.2
  if ((r * u.1).gcd w = D ∧ ComplexCRT.Compatible (p * (r * u.1)) (p * w) N1 N2) ∧
      ((r * v.1).gcd w = D ∧ ComplexCRT.Compatible (p * (r * v.1)) (p * w) N1 N2) then
    (d.gamma2 u.1 * star (d.gamma2 v.1)) / 4 *
      (alpha * star beta *
          SharedGeneralDRowAdapter.packet p r u.1 v.1 w N1 N2 d.residue u.2 v.2 +
        alpha * beta *
          SharedGeneralDRowAdapter.packet p r u.1 v.1 w N1 N2 d.residue u.2 (-v.2) +
        star alpha * star beta *
          SharedGeneralDRowAdapter.packet p r u.1 v.1 w N1 N2 d.residue (-u.2) v.2 +
        star alpha * beta *
          SharedGeneralDRowAdapter.packet p r u.1 v.1 w N1 N2 d.residue (-u.2) (-v.2))
  else 0

/-- No row activity or phase identity is a premise. Both original gates
are retained on the right, and the common actual gcd is derived from them. -/
theorem MediumAtom.smallCoreSquaredRowTerm_pair_packet
    (d : MediumAtom) (Z : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) (u v : ℕ × ℤ)
    (hp : 0 < o.1.1) (hr : 0 < o.2.1.1)
    (hs : 0 < u.1) (hs' : 0 < v.1)
    (hw : 0 < o.2.1.2.1 * o.2.1.2.2)
    (hN1 : 0 < o.1.2.1) (hN2 : 0 < o.1.2.2) :
    d.smallCoreSquaredRowTerm Z o u * star (d.smallCoreSquaredRowTerm Z o v) =
      d.smallCoreSquaredPairedPacketTerm Z o u v := by
  unfold MediumAtom.smallCoreSquaredRowTerm MediumAtom.smallCoreSquaredPairedPacketTerm
  dsimp only
  let gate (x : ℕ × ℤ) : Prop :=
    (o.2.1.1 * x.1).gcd (o.2.1.2.1 * o.2.1.2.2) = o.2.2 ∧
      ComplexCRT.Compatible (o.1.1 * (o.2.1.1 * x.1))
        (o.1.1 * (o.2.1.2.1 * o.2.1.2.2)) o.1.2.1 o.1.2.2
  by_cases hu : gate u
  · by_cases hv : gate v
    · rw [if_pos hu, if_pos hv, if_pos (And.intro hu hv)]
      rw [SharedGeneralDRowAdapter.atom_factor, SharedGeneralDRowAdapter.atom_factor]
      exact SharedGeneralDRowAdapter.character_gram_four_branches
        hp hr hs hs' hw hN1 hN2 hu.2 hv.2 (hv.1.trans hu.1.symm)
        d.residue u.2 v.2 (d.gamma2 u.1) (d.gamma2 v.1) _ _
    · have hpair : ¬ (gate u ∧ gate v) := fun h => hv h.2
      simp only [if_pos hu, if_neg hv, if_neg hpair, star_zero, mul_zero]
  · have hpair : ¬ (gate u ∧ gate v) := fun h => hu h.1
    simp only [if_neg hu, if_neg hpair, zero_mul]

/-- Finite adapter on the literal original Cauchy block. The signed
resonance mask, carrier, coefficient multiplicity and all gates survive. -/
theorem MediumAtom.smallCoreSquaredBlock_eq_pairedPacket
    (d : MediumAtom) (Z : ℝ) (resonant : Bool)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (hQ2 : 1 ≤ d.Q2) (hp : 0 < o.1.1) (hr : 0 < o.2.1.1)
    (hw : 0 < o.2.1.2.1 * o.2.1.2.2)
    (hN1 : 0 < o.1.2.1) (hN2 : 0 < o.1.2.2) :
    d.smallCoreSquaredBlock Z resonant o =
      ∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
        ∑ v ∈ d.smallCoreSquaredInnerCarrier Z o,
          if decide (u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
              u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ))) = resonant then
            d.smallCoreSquaredPairedPacketTerm Z o u v
          else 0 := by
  unfold MediumAtom.smallCoreSquaredBlock
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hs : 0 < u.1 := SharedGeneralDRowAdapter.factor_pos hQ2
    (Finset.mem_product.mp hu).1
  have hs' : 0 < v.1 := SharedGeneralDRowAdapter.factor_pos hQ2
    (Finset.mem_product.mp hv).1
  by_cases hres : decide (u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
      u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ))) = resonant
  · rw [if_pos hres, if_pos hres]
    exact d.smallCoreSquaredRowTerm_pair_packet Z o u v hp hr hs hs' hw hN1 hN2
  · rw [if_neg hres, if_neg hres]

end

end ImbalancedChen.Part3
