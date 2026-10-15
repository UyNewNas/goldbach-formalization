import ImbalancedChen.Part3CanonicalReciprocalData
import ImbalancedChen.Part3CommonPoisson

/-!
# Exact canonical reciprocal phases of the actual common Poisson remainder

Finite algebra extracted from fixed goldbach
09b97db5764ade1246bfb77206baa1b124760958:
* WPhase.lean:20-43, source SHA256
  86f1363ec58b6a143b6cdb2ef3183df62b24c010d9883a765d4e8447bda1cfc3;
* WPhaseThreeFactor.lean:18-127, source SHA256
  ae99138df0bd6c151abcc9bd883fe5e1564ddd2fffbd6ac018393cb0412a0ace.
Both blobs were compared byte-for-byte with the fixed commit. The original
unbuilt phase modules are not imported. The CRT residue used below is our
already constructed residue on the original labels, not a caller's phase.

Actual row membership and the existing Compatible branch provide all
canonical factorizations and unit gates. The complete root phase modulo D
and D', the slow real phase a/(n1*k1*k2*D'), and the reciprocal phase modulo
n1*k2 are retained. The exact h=0 cutoff, full physical lcm, complex beta and
gamma labels, original common U and primitive V/U centers are preserved.

No reciprocal-sum estimate, frequency tail bound, zero-mode cancellation
or change from |a|<=scale^(1+kappa) to |a|<=scale is asserted.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators SchwartzMap FourierTransform
open Classical

namespace CanonicalReciprocalPhase

def wPhaseInverse (n m : ℕ) : ℤ := n.gcdA m

theorem wPhaseInverse_spec {n m : ℕ} (h : n.Coprime m) :
    Int.ModEq m ((n : ℤ) * wPhaseInverse n m) 1 := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨n.gcdB m, ?_⟩
  have hb := Nat.gcd_eq_gcd_ab n m
  rw [h.gcd_eq_one, Nat.cast_one] at hb
  dsimp [wPhaseInverse]
  linarith

/-- Integer congruences give equal normalized phases, also for modulus one. -/
theorem wPhase_circle_eq_of_modEq {m : ℕ} (hm : 0 < m) {x y : ℤ}
    (h : Int.ModEq m x y) :
    (((x : ℝ) / m : ℝ) : UnitAddCircle) = ((y : ℝ) / m : ℝ) := by
  obtain ⟨z, hz⟩ := h.dvd
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-z, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hz' : (y : ℝ) - x = m * (z : ℝ) := by exact_mod_cast hz
  simp only [zsmul_eq_mul, Int.cast_neg, mul_one]
  field_simp
  nlinarith

private theorem wPhase_three_congruences
    (d d₁ D k₁ k₂ n₁ n₂ a b A B C : ℤ)
    (hA : Int.ModEq D (k₁ * k₂ * A) 1)
    (hB : Int.ModEq (d * d₁ * D) (n₁ * k₁ * k₂ * B) 1)
    (hC : Int.ModEq (n₁ * k₂) (d * d₁ * D * n₂ * k₁ * C) 1)
    (hb₁ : Int.ModEq k₁ (b * (d * d₁ * n₁)) a)
    (hb₂ : Int.ModEq k₂ (b * (d * n₂)) a) :
    let Z := b * A * d * d₁ * n₁ * k₁ * k₂ -
      a * B * n₁ * k₁ * k₂ + a +
        a * (d₁ * n₁ - n₂) * C * (d * d₁ * D) * k₁
    Int.ModEq (d * d₁ * D) (b * (d * d₁ * n₁)) Z ∧
      Int.ModEq k₁ (b * (d * d₁ * n₁)) Z ∧
      Int.ModEq (n₁ * k₂) (b * (d * d₁ * n₁)) Z := by
  obtain ⟨zA, hzA⟩ := hA.dvd
  obtain ⟨zB, hzB⟩ := hB.dvd
  obtain ⟨zC, hzC⟩ := hC.dvd
  obtain ⟨z₁, hz₁⟩ := hb₁.dvd
  obtain ⟨z₂, hz₂⟩ := hb₂.dvd
  dsimp
  refine ⟨Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_,
    Int.modEq_iff_dvd.mpr ?_⟩
  · refine ⟨-b * n₁ * zA + a * zB + a * (d₁ * n₁ - n₂) * C * k₁, ?_⟩
    linear_combination -b * d * d₁ * n₁ * hzA + a * hzB
  · refine ⟨b * A * d * d₁ * n₁ * k₂ - a * B * n₁ * k₂ +
      z₁ + a * (d₁ * n₁ - n₂) * C * (d * d₁ * D), ?_⟩
    linear_combination hz₁
  · refine ⟨b * A * d * d₁ * k₁ - a * B * k₁ +
      (a - b * d * d₁ * n₁) * zC + d₁ * z₂ * C * (d * d₁ * D) * k₁, ?_⟩
    linear_combination (a - b * d * d₁ * n₁) * hzC +
      d₁ * n₁ * C * (d * d₁ * D) * k₁ * hz₂

/-- Exact source three-factor phase of the existing product CRT residue.
`D' = d*d₁*D`; the genuine reciprocal denominator is `n₁*k₂`.
The original multipliers are `d*d₁*n₁` and `d*n₂`, and the original moduli
can be noncoprime. The hypotheses are arithmetic factorization/coprimality
conditions, not supplied phase identities. -/
private theorem productCRTResidue_phase_threeFactor
    {q r d d₁ D k₁ k₂ n₁ n₂ : ℕ}
    (hd : 0 < d) (hd₁ : 0 < d₁) (hDpos : 0 < D)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hn₁ : 0 < n₁)
    (hL : q.lcm r = D * k₁ * k₂) (hk₁q : k₁ ∣ q) (hk₂r : k₂ ∣ r)
    (hD : (k₁ * k₂).Coprime D)
    (hD' : (n₁ * k₁ * k₂).Coprime (d * d₁ * D))
    (hk : k₁.Coprime (n₁ * k₂)) (hn₂ : n₂.Coprime (n₁ * k₂))
    (hc : ComplexCRT.Compatible q r (d * d₁ * n₁) (d * n₂)) (a : ℤ) :
    let D' := d * d₁ * D
    let b := ComplexCRT.residue q r (d * d₁ * n₁) (d * n₂) a
    (((b : ℝ) / (q.lcm r) : ℝ) : UnitAddCircle) =
      (((b : ℝ) * wPhaseInverse (k₁ * k₂) D / D -
        (a : ℝ) * wPhaseInverse (n₁ * k₁ * k₂) D' / D' : ℝ) : UnitAddCircle) +
      (((a : ℝ) / ((n₁ : ℝ) * k₁ * k₂ * D') : ℝ) : UnitAddCircle) +
      (((a : ℝ) * ((d₁ : ℝ) * n₁ - n₂) *
        wPhaseInverse (D' * n₂ * k₁) (n₁ * k₂) / ((n₁ : ℝ) * k₂) : ℝ) :
          UnitAddCircle) := by
  dsimp only
  let b := ComplexCRT.residue q r (d * d₁ * n₁) (d * n₂) a
  let A := wPhaseInverse (k₁ * k₂) D
  let B := wPhaseInverse (n₁ * k₁ * k₂) (d * d₁ * D)
  let C := wPhaseInverse (d * d₁ * D * n₂ * k₁) (n₁ * k₂)
  let Z : ℤ := b * A * d * d₁ * n₁ * k₁ * k₂ -
    a * B * n₁ * k₁ * k₂ + a +
      a * ((d₁ : ℤ) * n₁ - n₂) * C * (d * d₁ * D : ℕ) * k₁
  have hVD : (n₁ * k₂).Coprime (d * d₁ * D) :=
    hD'.of_dvd_left ⟨k₁, by ring⟩
  have hU : (d * d₁ * D * n₂ * k₁).Coprime (n₁ * k₂) :=
    (hVD.symm.mul_left hn₂).mul_left hk
  have hb := ComplexCRT.residue_spec a hc
  have hb₁ := hb.1.of_dvd (by exact_mod_cast hk₁q : (k₁ : ℤ) ∣ q)
  have hb₂ := hb.2.1.of_dvd (by exact_mod_cast hk₂r : (k₂ : ℤ) ∣ r)
  have ht := wPhase_three_congruences d d₁ D k₁ k₂ n₁ n₂ a b A B C
    (by simpa only [Nat.cast_mul] using wPhaseInverse_spec hD)
    (by simpa only [Nat.cast_mul] using wPhaseInverse_spec hD')
    (by simpa only [Nat.cast_mul] using wPhaseInverse_spec hU)
    (by simpa only [Nat.cast_mul] using hb₁)
    (by simpa only [Nat.cast_mul] using hb₂)
  change Int.ModEq (d * d₁ * D : ℕ) (b * (d * d₁ * n₁ : ℕ)) Z ∧
    Int.ModEq k₁ (b * (d * d₁ * n₁ : ℕ)) Z ∧
    Int.ModEq (n₁ * k₂ : ℕ) (b * (d * d₁ * n₁ : ℕ)) Z at ht
  have hKV := (Int.modEq_and_modEq_iff_modEq_mul
    (by simpa only [Int.natAbs_natCast] using hk :
      (k₁ : ℤ).natAbs.Coprime (n₁ * k₂ : ℕ))).mp ⟨ht.2.1, ht.2.2⟩
  have hDK : (d * d₁ * D).Coprime (k₁ * (n₁ * k₂)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hD'.symm
  have hAll := (Int.modEq_and_modEq_iff_modEq_mul
    (by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hDK)).mp ⟨ht.1, hKV⟩
  have hAll' : Int.ModEq ((d * d₁ * D) * (k₁ * (n₁ * k₂)) : ℕ)
      (b * (d * d₁ * n₁ : ℕ)) Z := by
    simpa only [Nat.cast_mul] using hAll
  have hphase := wPhase_circle_eq_of_modEq
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd hd₁) hDpos)
      (Nat.mul_pos hk₁ (Nat.mul_pos hn₁ hk₂))) hAll'
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hd₁R : (d₁ : ℝ) ≠ 0 := by positivity
  have hDR : (D : ℝ) ≠ 0 := by positivity
  have hk₁R : (k₁ : ℝ) ≠ 0 := by positivity
  have hk₂R : (k₂ : ℝ) ≠ 0 := by positivity
  have hn₁R : (n₁ : ℝ) ≠ 0 := by positivity
  have hleft : (b * (d * d₁ * n₁ : ℕ) : ℤ) /
      (((d * d₁ * D) * (k₁ * (n₁ * k₂)) : ℕ) : ℝ) =
      (b : ℝ) / (q.lcm r : ℝ) := by
    rw [hL]
    push_cast
    field_simp
  rw [hleft] at hphase
  rw [hphase, ← AddCircle.coe_add, ← AddCircle.coe_add]
  congr 1
  dsimp [Z, A, B, C]
  push_cast
  field_simp
  ring

def rootPhase (v : CanonicalReciprocalData.WGCDData) (b a : ℤ) : UnitAddCircle :=
  (((b : ℝ) * wPhaseInverse (v.k₁ * v.k₂) v.D / v.D -
    (a : ℝ) * wPhaseInverse (v.n₁ * v.k₁ * v.k₂) v.D' / v.D' : ℝ) : UnitAddCircle)

def slowPhase (v : CanonicalReciprocalData.WGCDData) (a : ℤ) : UnitAddCircle :=
  (((a : ℝ) / ((v.n₁ : ℝ) * v.k₁ * v.k₂ * v.D') : ℝ) : UnitAddCircle)

def reciprocalPhase (v : CanonicalReciprocalData.WGCDData) (a : ℤ) : UnitAddCircle :=
  (((a : ℝ) * ((v.d₁ : ℝ) * v.n₁ - v.n₂) *
    wPhaseInverse (v.D' * v.n₂ * v.k₁) (v.n₁ * v.k₂) /
      ((v.n₁ : ℝ) * v.k₂) : ℝ) : UnitAddCircle)

private theorem circle_eq_threePhase
    {v : CanonicalReciprocalData.WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) (hc : ComplexCRT.Compatible q r N₁ N₂) (a : ℤ) :
    (((ComplexCRT.residue q r N₁ N₂ a : ℝ) / (q.lcm r) : ℝ) : UnitAddCircle) =
      rootPhase v (ComplexCRT.residue q r N₁ N₂ a) a + slowPhase v a +
        reciprocalPhase v a := by
  have hp := hv.phase_coprime hc
  have hc' : ComplexCRT.Compatible q r (v.d * v.d₁ * v.n₁) (v.d * v.n₂) := by
    simpa only [← hv.N₁_eq, ← hv.N₂_eq] using hc
  have he := productCRTResidue_phase_threeFactor hv.d_pos hv.d₁_pos hv.D_pos
    hv.k₁_pos hv.k₂_pos hv.n₁_pos hv.lcm_eq hv.k₁_dvd hv.k₂_dvd hv.k_D
    hp.1 hp.2.1 hp.2.2 hc' a
  simpa only [rootPhase, slowPhase, reciprocalPhase,
    CanonicalReciprocalData.WGCDData.D', ← hv.N₁_eq, ← hv.N₂_eq] using he

private theorem fourier_add (h : ℤ) (x y : UnitAddCircle) :
    fourier h (x + y) = fourier h x * fourier h y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

end CanonicalReciprocalPhase

/-- The actual CRT residue is rewritten with no extra factor-dictionary premise. -/
theorem MediumAtom.actualCRT_circle_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels)
    (hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2) :
    let v := d.canonicalReciprocalData l l'
    let b := ComplexCRT.residue (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2 d.residue
    (((b : ℝ) / (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) : ℝ) :
      UnitAddCircle) =
        CanonicalReciprocalPhase.rootPhase v b d.residue +
          CanonicalReciprocalPhase.slowPhase v d.residue +
            CanonicalReciprocalPhase.reciprocalPhase v d.residue :=
  CanonicalReciprocalPhase.circle_eq_threePhase
    (d.canonicalReciprocalData_valid hd hl hl') hc d.residue

/-- All three phase factors, including the slow phase, survive Fourier transport. -/
theorem MediumAtom.actualCRT_fourier_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels)
    (hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2) (h : ℤ) :
    let v := d.canonicalReciprocalData l l'
    let b := ComplexCRT.residue (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2 d.residue
    fourier h (((b : ℝ) /
      (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) : ℝ) : UnitAddCircle) =
      fourier h (CanonicalReciprocalPhase.rootPhase v b d.residue) *
        fourier h (CanonicalReciprocalPhase.slowPhase v d.residue) *
          fourier h (CanonicalReciprocalPhase.reciprocalPhase v d.residue) := by
  dsimp only
  rw [MediumAtom.actualCRT_circle_eq_canonicalPhases hd hl hl' hc,
    CanonicalReciprocalPhase.fourier_add, CanonicalReciprocalPhase.fourier_add]

/-- A literal dictionary for the original nonzero Poisson frequency. -/
def MediumAtom.canonicalPoissonFrequency (d : MediumAtom)
    (l l' : (ℕ × ℕ × ℕ) × ℕ) (h : ℤ) : ℂ :=
  let v := d.canonicalReciprocalData l l'
  let L := (complexFactorModulus l.1).lcm (complexFactorModulus l'.1)
  let b := ComplexCRT.residue (complexFactorModulus l.1)
    (complexFactorModulus l'.1) l.2 l'.2 d.residue
  if h = 0 then 0 else
    (d.U / L) • (𝓕 CommonSmoothCutoff.dyadicCutoffSchwartz) ((d.U / L) * h) *
      fourier h (CanonicalReciprocalPhase.rootPhase v b d.residue) *
        fourier h (CanonicalReciprocalPhase.slowPhase v d.residue) *
          fourier h (CanonicalReciprocalPhase.reciprocalPhase v d.residue)

@[simp] theorem MediumAtom.canonicalPoissonFrequency_zero (d : MediumAtom)
    (l l' : (ℕ × ℕ × ℕ) × ℕ) : d.canonicalPoissonFrequency l l' 0 = 0 := rfl

theorem MediumAtom.poissonNonzeroFrequency_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels)
    (hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2) (h : ℤ) :
    CommonSmoothCutoff.poissonNonzeroFrequency
      (d.U / (complexFactorModulus l.1).lcm (complexFactorModulus l'.1))
      ((ComplexCRT.residue (complexFactorModulus l.1)
        (complexFactorModulus l'.1) l.2 l'.2 d.residue : ℝ) /
          (complexFactorModulus l.1).lcm (complexFactorModulus l'.1)) h =
      d.canonicalPoissonFrequency l l' h := by
  unfold CommonSmoothCutoff.poissonNonzeroFrequency MediumAtom.canonicalPoissonFrequency
  dsimp only
  by_cases hh : h = 0
  · simp only [hh, if_true]
  · simp only [if_neg hh]
    rw [MediumAtom.actualCRT_fourier_eq_canonicalPhases hd hl hl' hc]
    ring

/-- The exact whole original complex remainder retains both full labels,
all beta/gamma coefficients and every compatible branch. The centers V/U
in the already proved common Poisson dispersion identity stay unchanged. -/
theorem MediumAtom.complexCRTSmoothNonzeroPart_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.complexCRTSmoothNonzeroPart =
      ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
        d.complexBetaCoefficient l * star (d.complexBetaCoefficient l') *
          (if ComplexCRT.Compatible (complexFactorModulus l.1)
            (complexFactorModulus l'.1) l.2 l'.2 then
              (∑' h : ℤ, d.canonicalPoissonFrequency l l' h).re else 0 : ℝ) := by
  unfold MediumAtom.complexCRTSmoothNonzeroPart
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro l' hl'
  by_cases hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2
  · simp only [if_pos hc]
    have he := tsum_congr (L := SummationFilter.unconditional ℤ)
      (fun h ↦ d.poissonNonzeroFrequency_eq_canonicalPhases hd hl hl' hc h)
    rw [he]
  · simp only [if_neg hc]

/-- The actual centered dispersion retains its literal primitive V/U after
the complete nonzero-frequency dictionary has been proved. -/
theorem MediumAtom.complex_dispersion_identity_with_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ((∑ n ∈ d.commonSmoothCarrier,
      d.commonSmoothWeight n * ‖d.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (d.complexCRTSmoothZeroPart -
        2 * (d.complexDispersionV d.commonSmoothCarrier d.commonSmoothWeight : ℂ) +
          (d.complexDispersionU d.commonSmoothCarrier d.commonSmoothWeight : ℂ)) +
        ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
          d.complexBetaCoefficient l * star (d.complexBetaCoefficient l') *
            (if ComplexCRT.Compatible (complexFactorModulus l.1)
              (complexFactorModulus l'.1) l.2 l'.2 then
                (∑' h : ℤ, d.canonicalPoissonFrequency l l' h).re else 0 : ℝ) := by
  rw [MediumAtom.complex_dispersion_identity_with_commonPoisson hd,
    MediumAtom.complexCRTSmoothNonzeroPart_eq_canonicalPhases hd]

end

end ImbalancedChen.Part3
