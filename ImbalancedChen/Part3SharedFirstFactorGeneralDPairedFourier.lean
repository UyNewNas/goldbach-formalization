import ImbalancedChen.Part3SharedFirstFactorGeneralDRootPacket

/-!
# Exact paired phases on one actual general-D packet

The two original tails share their actual gcd with the fixed right tail.
All factors and unit gates are derived by applying the original root packet
twice. The difference k is signed, the root has its original negative sign,
and the complete slow phase has denominator N1*K*t*t'. Modulus one is allowed.

The separate real-projection identity retains all four complex branches,
including their original amplitudes and coefficients. No finite carrier is
changed and no spectral estimate, (y,z) reindexing, or 7/32 bound is asserted.
The imported root-packet source is still a candidate pending root acceptance.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped FourierTransform

namespace SharedGeneralDPairedFourier

private theorem inverse_pair_modEq {m n t t' : ℕ}
    (hn : n.Coprime m) (ht : t.Coprime m) (ht' : t'.Coprime m)
    (h h' : ℤ) :
    Int.ModEq m
      (h * CanonicalReciprocalPhase.wPhaseInverse (n * t) m -
        h' * CanonicalReciprocalPhase.wPhaseInverse (n * t') m)
      ((h * (t' : ℤ) - h' * (t : ℤ)) *
        CanonicalReciprocalPhase.wPhaseInverse (n * (t * t')) m) := by
  let x := CanonicalReciprocalPhase.wPhaseInverse (n * t) m
  let x' := CanonicalReciprocalPhase.wPhaseInverse (n * t') m
  let j := CanonicalReciprocalPhase.wPhaseInverse (n * (t * t')) m
  have hx : Int.ModEq m (((n * t : ℕ) : ℤ) * x) 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec (hn.mul_left ht)
  have hx' : Int.ModEq m (((n * t' : ℕ) : ℤ) * x') 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec (hn.mul_left ht')
  have hj : Int.ModEq m (((n * (t * t') : ℕ) : ℤ) * j) 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec (hn.mul_left (ht.mul_left ht'))
  have hleft : Int.ModEq m x ((t' : ℤ) * j) := by
    calc
      x ≡ x * (((n * (t * t') : ℕ) : ℤ) * j) [ZMOD m] := by
        simpa only [mul_one] using (hj.mul_left x).symm
      _ = ((t' : ℤ) * j) * (((n * t : ℕ) : ℤ) * x) := by
        push_cast
        ring
      _ ≡ (t' : ℤ) * j [ZMOD m] := by
        simpa only [mul_one] using hx.mul_left ((t' : ℤ) * j)
  have hright : Int.ModEq m x' ((t : ℤ) * j) := by
    calc
      x' ≡ x' * (((n * (t * t') : ℕ) : ℤ) * j) [ZMOD m] := by
        simpa only [mul_one] using (hj.mul_left x').symm
      _ = ((t : ℤ) * j) * (((n * t' : ℕ) : ℤ) * x') := by
        push_cast
        ring
      _ ≡ (t : ℤ) * j [ZMOD m] := by
        simpa only [mul_one] using hx'.mul_left ((t : ℤ) * j)
  have hdifference := (hleft.mul_left h).sub (hright.mul_left h')
  convert hdifference using 1 <;> ring

private theorem fourier_pair_real (h h' : ℤ) (x x' : ℝ) :
    fourier h (x : UnitAddCircle) * star (fourier h' (x' : UnitAddCircle)) =
      fourier 1 ((((h : ℝ) * x - (h' : ℝ) * x') : ℝ) : UnitAddCircle) := by
  simp only [Complex.star_def]
  rw [← fourier_neg]
  simp only [fourier_coe_apply, div_one]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem inverse_fourier_pair {m n t t' : ℕ}
    (hm : 0 < m) (hn : n.Coprime m)
    (ht : t.Coprime m) (ht' : t'.Coprime m) (a h h' : ℤ) :
    fourier h
        ((((a : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (n * t) m : ℝ) / m) : ℝ) :
            UnitAddCircle) *
      star (fourier h'
        ((((a : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (n * t') m : ℝ) / m) : ℝ) :
            UnitAddCircle)) =
      fourier 1
        ((((a : ℝ) * ((h * (t' : ℤ) - h' * (t : ℤ) : ℤ) : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (n * (t * t')) m : ℝ) / m) : ℝ) :
            UnitAddCircle) := by
  have hcircle := CanonicalReciprocalPhase.wPhase_circle_eq_of_modEq hm
    ((inverse_pair_modEq hn ht ht' h h').mul_left a)
  rw [fourier_pair_real]
  have hreal :
      (h : ℝ) * ((a : ℝ) *
        (CanonicalReciprocalPhase.wPhaseInverse (n * t) m : ℝ) / m) -
      (h' : ℝ) * ((a : ℝ) *
        (CanonicalReciprocalPhase.wPhaseInverse (n * t') m : ℝ) / m) =
      ((a * (h * CanonicalReciprocalPhase.wPhaseInverse (n * t) m -
        h' * CanonicalReciprocalPhase.wPhaseInverse (n * t') m) : ℤ) : ℝ) / m := by
    push_cast
    ring
  rw [hreal]
  simpa only [Int.cast_mul, Int.cast_sub, mul_assoc] using
    congrArg (fourier 1) hcircle

end SharedGeneralDPairedFourier

/-- The actual pair of CRT phases on the same original general-D row.
Only original positivity, two original CRT branches and equality of the two
actual gcds are premises. No packet factors, units or phase identities are
provided by a caller. The original signed frequencies and full slow phase
survive, before any real projection or finite regrouping. -/
theorem sharedGeneralD_paired_fourier
    {p r s s' w N1 N2 : ℕ}
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s') (hw : 0 < w)
    (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hc : ComplexCRT.Compatible (p * (r * s)) (p * w) N1 N2)
    (hc' : ComplexCRT.Compatible (p * (r * s')) (p * w) N1 N2)
    (hsame : (r * s').gcd w = (r * s).gcd w) (a h h' : ℤ) :
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
    let L := (p * (r * s)).lcm (p * w)
    let L' := (p * (r * s')).lcm (p * w)
    let f : ℤ := ((d1 : ℤ) * n1 - n2) / (p * D : ℕ)
    let k : ℤ := h * (t' : ℤ) - h' * (t : ℤ)
    let z := t * t'
    0 < K ∧ 0 < A ∧ 0 < c ∧
      s = q * t ∧ s' = q * t' ∧
      b.Coprime c ∧ zeta.Coprime A ∧
      t.Coprime (A * c) ∧ t'.Coprime (A * c) ∧
      L = K * t ∧ L' = K * t' ∧
      fourier h
        (((ComplexCRT.residue (p * (r * s)) (p * w) N1 N2 a : ℝ) / L : ℝ) :
          UnitAddCircle) *
        star (fourier h'
          (((ComplexCRT.residue (p * (r * s')) (p * w) N1 N2 a : ℝ) / L' : ℝ) :
            UnitAddCircle)) =
        fourier 1
          (((-(a : ℝ) * (k : ℝ) *
            (CanonicalReciprocalPhase.wPhaseInverse (zeta * z) A : ℝ) / A) : ℝ) :
              UnitAddCircle) *
          fourier 1 ((((a : ℝ) * (k : ℝ) /
            ((N1 : ℝ) * K * z)) : ℝ) : UnitAddCircle) *
          fourier 1
            ((((a : ℝ) * (f : ℝ) * (k : ℝ) *
              (CanonicalReciprocalPhase.wPhaseInverse (b * z) c : ℝ) / c) : ℝ) :
                UnitAddCircle) := by
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
  let L := (p * (r * s)).lcm (p * w)
  let L' := (p * (r * s')).lcm (p * w)
  let f : ℤ := ((d1 : ℤ) * n1 - n2) / (p * D : ℕ)
  let k : ℤ := h * (t' : ℤ) - h' * (t : ℤ)
  let z := t * t'
  have hdata := sharedGeneralDRootPacket_fourier hp hr hs hw hN1 hN2 hc a h
  have hdata' := sharedGeneralDRootPacket_fourier hp hr hs' hw hN1 hN2 hc' a h'
  dsimp only at hdata hdata'
  rw [hsame] at hdata'
  obtain ⟨_hq, hr0, ht, hA, hcpos, hst, _hvt, _hrq,
    hb, hzeta, htAc, hroot, _hrecip, hphase⟩ := hdata
  obtain ⟨_hq', _hr0', ht', _hA', _hcpos', hst', _hvt', _hrq',
    _hb', _hzeta', htAc', hroot', _hrecip', hphase'⟩ := hdata'
  change 0 < r0 at hr0
  change 0 < t at ht
  change 0 < t' at ht'
  change 0 < A at hA
  change 0 < c at hcpos
  change s = q * t at hst
  change s' = q * t' at hst'
  change b.Coprime c at hb
  change zeta.Coprime A at hzeta
  change t.Coprime (A * c) at htAc
  change t'.Coprime (A * c) at htAc'
  change n1 * L = zeta * t at hroot
  change n1 * L' = zeta * t' at hroot'
  have hn1 : 0 < n1 := CanonicalReciprocalData.coprimePart_pos _ _
  have hL : L = K * t := by
    apply Nat.mul_left_cancel hn1
    calc
      n1 * L = zeta * t := hroot
      _ = n1 * (K * t) := by dsimp only [zeta, c, K]; ring
  have hL' : L' = K * t' := by
    apply Nat.mul_left_cancel hn1
    calc
      n1 * L' = zeta * t' := hroot'
      _ = n1 * (K * t') := by dsimp only [zeta, c, K]; ring
  have hD : 0 < D := Nat.gcd_pos_of_pos_left w (Nat.mul_pos hr hs)
  have hw0 : 0 < w0 :=
    Nat.div_pos (Nat.le_of_dvd hw (Nat.gcd_dvd_right (r * s) w)) hD
  have hK : 0 < K := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp hD) hr0) hw0
  have htA : t.Coprime A := htAc.of_dvd_right (dvd_mul_right A c)
  have htA' : t'.Coprime A := htAc'.of_dvd_right (dvd_mul_right A c)
  have htc : t.Coprime c := htAc.of_dvd_right (dvd_mul_left c A)
  have htc' : t'.Coprime c := htAc'.of_dvd_right (dvd_mul_left c A)
  change fourier h
      (((ComplexCRT.residue (p * (r * s)) (p * w) N1 N2 a : ℝ) / L : ℝ) :
        UnitAddCircle) =
      fourier h (((-(a : ℝ) *
        (CanonicalReciprocalPhase.wPhaseInverse (zeta * t) A : ℝ) / A) : ℝ) :
          UnitAddCircle) *
        fourier h ((((a : ℝ) / ((N1 : ℝ) * L)) : ℝ) : UnitAddCircle) *
        fourier h ((((a : ℝ) * (f : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (b * t) c : ℝ) / c) : ℝ) :
            UnitAddCircle) at hphase
  change fourier h'
      (((ComplexCRT.residue (p * (r * s')) (p * w) N1 N2 a : ℝ) / L' : ℝ) :
        UnitAddCircle) =
      fourier h' (((-(a : ℝ) *
        (CanonicalReciprocalPhase.wPhaseInverse (zeta * t') A : ℝ) / A) : ℝ) :
          UnitAddCircle) *
        fourier h' ((((a : ℝ) / ((N1 : ℝ) * L')) : ℝ) : UnitAddCircle) *
        fourier h' ((((a : ℝ) * (f : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (b * t') c : ℝ) / c) : ℝ) :
            UnitAddCircle) at hphase'
  have hrootpair := SharedGeneralDPairedFourier.inverse_fourier_pair
    hA hzeta htA htA' (-a) h h'
  have hrecippair := SharedGeneralDPairedFourier.inverse_fourier_pair
    hcpos hb htc htc' (a * f) h h'
  simp only [Int.cast_neg, Int.cast_mul, mul_assoc] at hrootpair hrecippair
  have hslowpair :
      fourier h ((((a : ℝ) / ((N1 : ℝ) * L)) : ℝ) : UnitAddCircle) *
        star (fourier h' ((((a : ℝ) / ((N1 : ℝ) * L')) : ℝ) : UnitAddCircle)) =
      fourier 1 ((((a : ℝ) * (k : ℝ) /
        ((N1 : ℝ) * K * z)) : ℝ) : UnitAddCircle) := by
    rw [SharedGeneralDPairedFourier.fourier_pair_real]
    have hreal :
        (h : ℝ) * ((a : ℝ) / ((N1 : ℝ) * L)) -
          (h' : ℝ) * ((a : ℝ) / ((N1 : ℝ) * L')) =
        (a : ℝ) * (k : ℝ) / ((N1 : ℝ) * K * z) := by
      rw [hL, hL']
      dsimp only [k, z]
      push_cast
      have hN10 : (N1 : ℝ) ≠ 0 := by positivity
      have hK0 : (K : ℝ) ≠ 0 := by positivity
      have ht0 : (t : ℝ) ≠ 0 := by positivity
      have ht'0 : (t' : ℝ) ≠ 0 := by positivity
      field_simp [hN10, hK0, ht0, ht'0] <;> ring
    rw [hreal]
  refine ⟨hK, hA, hcpos, hst, hst', hb, hzeta, htAc, htAc', hL, hL', ?_⟩
  rw [hphase, hphase']
  simp only [star_mul]
  calc
    _ =
      (fourier h (((-(a : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (zeta * t) A : ℝ) / A) : ℝ) :
            UnitAddCircle) *
        star (fourier h' (((-(a : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (zeta * t') A : ℝ) / A) : ℝ) :
            UnitAddCircle))) *
      (fourier h ((((a : ℝ) / ((N1 : ℝ) * L)) : ℝ) : UnitAddCircle) *
        star (fourier h' ((((a : ℝ) / ((N1 : ℝ) * L')) : ℝ) : UnitAddCircle))) *
      (fourier h ((((a : ℝ) * (f : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (b * t) c : ℝ) / c) : ℝ) :
            UnitAddCircle) *
        star (fourier h' ((((a : ℝ) * (f : ℝ) *
          (CanonicalReciprocalPhase.wPhaseInverse (b * t') c : ℝ) / c) : ℝ) :
            UnitAddCircle))) := by ring
    _ = _ := by
      simpa only [k, z, mul_assoc] using
        congrArg₂ (fun x y : ℂ => x * y)
          (congrArg₂ (fun x y : ℂ => x * y) hrootpair hslowpair) hrecippair

/-- Apply this to the complete smooth Fourier atoms F,G, including their
low pass and Poisson amplitudes. It is the exact real-projection Gram,
with all four branches and arbitrary original complex coefficients. -/
theorem sharedGeneralD_realProjection_four_branches (lambda mu F G : ℂ) :
    (lambda * (F.re : ℂ)) * star (mu * (G.re : ℂ)) =
      (lambda * star mu) / 4 *
        (F * star G + F * G + star F * star G + star F * G) := by
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [Complex.re_eq_add_conj F, Complex.re_eq_add_conj G]
  ring

end

end ImbalancedChen.Part3
