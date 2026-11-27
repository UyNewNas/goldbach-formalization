import ImbalancedChen.Part3SharedFirstFactorDifferenceReciprocity
import ImbalancedChen.Part3SharedFirstFactorSmallCoreSquaredFinite

/-!
# The actual general-D row has one root packet

This is a finite arithmetic dictionary on the literal compatible branch of
`smallCoreSquaredRowTerm`. The quotient `t` is constructed from the original
`s`; no factorization, inverse phase, or unit condition is supplied by a caller.
The root modulus is the actual `g * supportedPart (N1 / g) g`.

The complete slow phase and every signed frequency are retained. This file
does not merge a pair of frequencies, rearrange by `(y,z)`, enlarge a carrier,
or prove a spectral estimate. Its result can be applied separately to `h,h'`.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped FourierTransform

namespace SharedGeneralDRootPacket

/-- Reduction of the actual gcd mask, with no assumption that `D` divides `r`. -/
private theorem normalized_tail {r s w : ℕ}
    (hr : 0 < r) (hs : 0 < s) :
    let D := (r * s).gcd w
    let d := r.gcd D
    let q := D / d
    let r0 := r / d
    let t := s / q
    0 < q ∧ 0 < r0 ∧ 0 < t ∧ r0.Coprime q ∧
      s = q * t ∧ (r * s) / D = r0 * t := by
  let D := (r * s).gcd w
  let d := r.gcd D
  let q := D / d
  let r0 := r / d
  let t := s / q
  change 0 < q ∧ 0 < r0 ∧ 0 < t ∧ r0.Coprime q ∧
    s = q * t ∧ (r * s) / D = r0 * t
  have hD : 0 < D := Nat.gcd_pos_of_pos_left w (Nat.mul_pos hr hs)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left D hr
  have hdD : d ∣ D := Nat.gcd_dvd_right r D
  have hdr : d ∣ r := Nat.gcd_dvd_left r D
  have hDdiv : D ∣ r * s := Nat.gcd_dvd_left (r * s) w
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hD hdD) hd
  have hr0 : 0 < r0 := Nat.div_pos (Nat.le_of_dvd hr hdr) hd
  have hDfact : d * q = D := Nat.mul_div_cancel' hdD
  have hrfact : d * r0 = r := Nat.mul_div_cancel' hdr
  have hcop : r0.Coprime q := Nat.coprime_div_gcd_div_gcd hd
  have hqdiv : q ∣ r0 * s := by
    apply Nat.dvd_of_mul_dvd_mul_left hd
    simpa only [← mul_assoc, hDfact, hrfact] using hDdiv
  have hqs : q ∣ s := hcop.symm.dvd_of_dvd_mul_left hqdiv
  have hsfact : q * t = s := Nat.mul_div_cancel' hqs
  have ht : 0 < t := Nat.div_pos (Nat.le_of_dvd hs hqs) hq
  refine ⟨hq, hr0, ht, hcop, hsfact.symm, ?_⟩
  apply Nat.mul_left_cancel hD
  rw [Nat.mul_div_cancel' hDdiv]
  calc
    r * s = (d * r0) * (q * t) := by rw [hrfact, hsfact]
    _ = D * (r0 * t) := by rw [← hDfact]; ring

end SharedGeneralDRootPacket

/-- Exact actual-row root/reciprocal dictionary for general `D`.

For an active squared row take `r=o.2.1.1`, `s=u.1`,
`w=o.2.1.2.1*o.2.1.2.2`, and the literal original `p,N1,N2`.
The row's gcd gate identifies its stored `D` with the `D` constructed here.
No coefficient, support, cutoff, or signed-frequency condition is changed.
-/
theorem sharedGeneralDRootPacket_fourier
    {p r s w N1 N2 : ℕ}
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hw : 0 < w)
    (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hc : ComplexCRT.Compatible (p * (r * s)) (p * w) N1 N2)
    (a h : ℤ) :
    let D := (r * s).gcd w
    let d := r.gcd D
    let q := D / d
    let r0 := r / d
    let t := s / q
    let g := N1.gcd N2
    let d1 := CanonicalReciprocalData.supportedPart (N1 / g) g
    let n1 := CanonicalReciprocalData.coprimePart (N1 / g) g
    let n2 := N2 / g
    let A := g * d1
    let w0 := w / D
    let b := A * n2 * r0
    let c := n1 * w0
    let zeta := c * p * D * r0
    let L := (p * (r * s)).lcm (p * w)
    let f : ℤ := ((d1 : ℤ) * n1 - n2) / (p * D : ℕ)
    0 < q ∧ 0 < r0 ∧ 0 < t ∧ 0 < A ∧ 0 < c ∧
      s = q * t ∧ (r * s) / D = r0 * t ∧ r0.Coprime q ∧
      b.Coprime c ∧ zeta.Coprime A ∧ t.Coprime (A * c) ∧
      n1 * L = zeta * t ∧ A * n2 * ((r * s) / D) = b * t ∧
      fourier h
        (((ComplexCRT.residue (p * (r * s)) (p * w) N1 N2 a : ℝ) / L : ℝ) :
          UnitAddCircle) =
        fourier h
          (((-(a : ℝ) *
            (CanonicalReciprocalPhase.wPhaseInverse (zeta * t) A : ℝ) / A) : ℝ) :
              UnitAddCircle) *
          fourier h ((((a : ℝ) / ((N1 : ℝ) * L)) : ℝ) : UnitAddCircle) *
          fourier h
            (((((a : ℝ) * (f : ℝ) *
              (CanonicalReciprocalPhase.wPhaseInverse (b * t) c : ℝ)) / c) : ℝ) :
                UnitAddCircle) := by
  let D := (r * s).gcd w
  let d := r.gcd D
  let q := D / d
  let r0 := r / d
  let t := s / q
  let g := N1.gcd N2
  let d1 := CanonicalReciprocalData.supportedPart (N1 / g) g
  let n1 := CanonicalReciprocalData.coprimePart (N1 / g) g
  let n2 := N2 / g
  let A := g * d1
  let w0 := w / D
  let b := A * n2 * r0
  let c := n1 * w0
  let zeta := c * p * D * r0
  let L := (p * (r * s)).lcm (p * w)
  let f : ℤ := ((d1 : ℤ) * n1 - n2) / (p * D : ℕ)
  obtain ⟨hq, hr0, ht, hrq, hst, hvt⟩ :=
    SharedGeneralDRootPacket.normalized_tail (w := w) hr hs
  change 0 < q at hq
  change 0 < r0 at hr0
  change 0 < t at ht
  change r0.Coprime q at hrq
  change s = q * t at hst
  change (r * s) / D = r0 * t at hvt
  have hlic := sharedDifferenceData_licenses hp (Nat.mul_pos hr hs) hw hN1 hN2 hc a
  dsimp only at hlic
  obtain ⟨_hg, _hD, _hd1, hn1, _hn2, _hv0, hw0, hA, _hL,
    _hN1eq, _hN2eq, _hv_eq, _hw_eq, hLeq, _hvw, _hnD, _hvc,
    hbc, hroot, _rest⟩ := hlic
  change 0 < n1 at hn1
  change 0 < w0 at hw0
  change 0 < A at hA
  change L = (p * D) * ((r * s) / D) * w0 at hLeq
  change (A * n2 * ((r * s) / D)).Coprime c at hbc
  change (n1 * L).Coprime A at hroot
  have hrecip : A * n2 * ((r * s) / D) = b * t := by
    rw [hvt]
    dsimp only [b]
    ring
  have hrootden : n1 * L = zeta * t := by
    rw [hLeq, hvt]
    dsimp only [zeta, c]
    ring
  rw [hrecip] at hbc
  rw [hrootden] at hroot
  have h_b : b.Coprime c := hbc.of_dvd_left (dvd_mul_right b t)
  have h_tc : t.Coprime c := hbc.of_dvd_left (dvd_mul_left t b)
  have h_zeta : zeta.Coprime A := hroot.of_dvd_left (dvd_mul_right zeta t)
  have h_tA : t.Coprime A := hroot.of_dvd_left (dvd_mul_left t zeta)
  refine ⟨hq, hr0, ht, hA, Nat.mul_pos hn1 hw0, hst, hvt, hrq,
    h_b, h_zeta, h_tA.mul_right h_tc, hrootden, hrecip, ?_⟩
  have he := sharedDifferenceReciprocity_fourier hp (Nat.mul_pos hr hs) hw hN1 hN2 hc a h
  change fourier h
      (((ComplexCRT.residue (p * (r * s)) (p * w) N1 N2 a : ℝ) / L : ℝ) :
        UnitAddCircle) =
      fourier h
        (((-(a : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (n1 * L) A : ℝ) / A) : ℝ) :
            UnitAddCircle) *
        fourier h ((((a : ℝ) / ((N1 : ℝ) * L)) : ℝ) : UnitAddCircle) *
        fourier h
          (((((a : ℝ) * (f : ℝ) *
            (CanonicalReciprocalPhase.wPhaseInverse
              (A * n2 * ((r * s) / D)) c : ℝ)) / ((n1 : ℝ) * w0)) : ℝ) :
              UnitAddCircle) at he
  have hcR : (c : ℝ) = (n1 : ℝ) * w0 := Nat.cast_mul n1 w0
  rw [hrootden, hrecip, ← hcR] at he
  exact he

end

end ImbalancedChen.Part3
