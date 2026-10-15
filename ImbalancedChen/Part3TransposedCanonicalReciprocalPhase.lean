import ImbalancedChen.Part3CanonicalReciprocalPhase
import ImbalancedChen.Part3TransposedDispersion

/-!
# Canonical reciprocal phases on the actual transposed dispersion

Only the original atom is admissible. Its U and the three original Q gates
supply positive actual paired indices and complete physical moduli. The
transposed coefficient remains original alpha with its original interval
zero padding; no admissibility statement is made for the transposed atom.

The private finite congruence proof below is copied from the already owned
Part3CanonicalReciprocalPhase source, with namespace-local names. All
phase definitions are the owned definitions. No private mangled name or
new foreign module is referenced. The signed moving residue, root phases
modulo D and D', slow a/(n1*k1*k2*D'), genuine reciprocal modulo n1*k2,
complete physical lcm, both full complex labels and every integer h remain.

The final identity rewrites the complete original-V-smoothed nonzero
series. It is an exact dictionary, not an energy or frequency-tail bound.
The literal primitive V/U centers are not changed or cancelled here.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators SchwartzMap FourierTransform
open Classical

namespace TransposedCanonicalReciprocalPhase

open CanonicalReciprocalData CanonicalReciprocalPhase

private theorem positive_carrier {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ Finset.Icc (Nat.ceil Q) (Nat.floor (2 * Q))) : 0 < n := by
  have hlo := (Finset.mem_Icc.mp hn).1
  have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

private theorem actual_transposed_row_positive
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l : (ℕ × ℕ × ℕ) × ℕ} (hl : l ∈ d.transposedAtom.complexRowLabels) :
    0 < complexFactorModulus l.1 ∧ 0 < l.2 := by
  obtain ⟨hU, _hV, hQ1, hQ2, hQ3, _⟩ := hd
  obtain ⟨hf, hb⟩ := Finset.mem_product.mp hl
  obtain ⟨h1, h23⟩ := Finset.mem_product.mp hf
  obtain ⟨h2, h3⟩ := Finset.mem_product.mp h23
  exact ⟨Nat.mul_pos (Nat.mul_pos (positive_carrier hQ1 h1)
    (positive_carrier hQ2 h2)) (positive_carrier hQ3 h3), positive_carrier hU hb⟩

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

end TransposedCanonicalReciprocalPhase

/-- Actual transposed labels supply the canonical data from original hd. -/
theorem MediumAtom.transposed_canonicalReciprocalData_valid
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.transposedAtom.complexRowLabels)
    (hl' : l' ∈ d.transposedAtom.complexRowLabels) :
    (d.transposedAtom.canonicalReciprocalData l l').Valid
      (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2 := by
  obtain ⟨hq, hn⟩ := TransposedCanonicalReciprocalPhase.actual_transposed_row_positive hd hl
  obtain ⟨hr, hn'⟩ := TransposedCanonicalReciprocalPhase.actual_transposed_row_positive hd hl'
  exact CanonicalReciprocalData.wGCDData_valid hq hr hn hn'

/-- The original signed residue and all three exact canonical phases. -/
theorem MediumAtom.transposed_actualCRT_circle_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.transposedAtom.complexRowLabels)
    (hl' : l' ∈ d.transposedAtom.complexRowLabels)
    (hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2) :
    let v := d.transposedAtom.canonicalReciprocalData l l'
    let b := ComplexCRT.residue (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2 d.residue
    (((b : ℝ) / (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) : ℝ) :
      UnitAddCircle) =
        CanonicalReciprocalPhase.rootPhase v b d.residue +
          CanonicalReciprocalPhase.slowPhase v d.residue +
            CanonicalReciprocalPhase.reciprocalPhase v d.residue :=
  TransposedCanonicalReciprocalPhase.circle_eq_threePhase
    (d.transposed_canonicalReciprocalData_valid hd hl hl') hc d.residue

/-- Every signed integer frequency, including zero, has the exact three factors. -/
theorem MediumAtom.transposed_actualCRT_fourier_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.transposedAtom.complexRowLabels)
    (hl' : l' ∈ d.transposedAtom.complexRowLabels)
    (hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2) (h : ℤ) :
    let v := d.transposedAtom.canonicalReciprocalData l l'
    let b := ComplexCRT.residue (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2 d.residue
    fourier h (((b : ℝ) /
      (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) : ℝ) : UnitAddCircle) =
      fourier h (CanonicalReciprocalPhase.rootPhase v b d.residue) *
        fourier h (CanonicalReciprocalPhase.slowPhase v d.residue) *
          fourier h (CanonicalReciprocalPhase.reciprocalPhase v d.residue) := by
  dsimp only
  rw [MediumAtom.transposed_actualCRT_circle_eq_canonicalPhases hd hl hl' hc,
    TransposedCanonicalReciprocalPhase.fourier_add,
    TransposedCanonicalReciprocalPhase.fourier_add]

/-- Literal original-V Poisson kernel, with exactly the owned h=0 cutoff. -/
theorem MediumAtom.transposed_poissonNonzeroFrequency_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.transposedAtom.complexRowLabels)
    (hl' : l' ∈ d.transposedAtom.complexRowLabels)
    (hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2) (h : ℤ) :
    CommonSmoothCutoff.poissonNonzeroFrequency
      (d.transposedAtom.U / (complexFactorModulus l.1).lcm (complexFactorModulus l'.1))
      ((ComplexCRT.residue (complexFactorModulus l.1)
        (complexFactorModulus l'.1) l.2 l'.2 d.transposedAtom.residue : ℝ) /
          (complexFactorModulus l.1).lcm (complexFactorModulus l'.1)) h =
      d.transposedAtom.canonicalPoissonFrequency l l' h := by
  unfold CommonSmoothCutoff.poissonNonzeroFrequency MediumAtom.canonicalPoissonFrequency
  dsimp only
  by_cases hh : h = 0
  · simp only [hh, if_true]
  · simp only [if_neg hh]
    rw [show d.transposedAtom.residue = d.residue from rfl]
    rw [MediumAtom.transposed_actualCRT_fourier_eq_canonicalPhases hd hl hl' hc]
    ring

/-- The entire transposed signed nonzero series, with both actual complex labels. -/
theorem MediumAtom.transposed_complexCRTSmoothNonzeroPart_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.transposedAtom.complexCRTSmoothNonzeroPart =
      ∑ l ∈ d.transposedAtom.complexRowLabels,
        ∑ l' ∈ d.transposedAtom.complexRowLabels,
          d.transposedAtom.complexBetaCoefficient l *
            star (d.transposedAtom.complexBetaCoefficient l') *
              (if ComplexCRT.Compatible (complexFactorModulus l.1)
                (complexFactorModulus l'.1) l.2 l'.2 then
                  (∑' h : ℤ, d.transposedAtom.canonicalPoissonFrequency l l' h).re
                else 0 : ℝ) := by
  unfold MediumAtom.complexCRTSmoothNonzeroPart
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro l' hl'
  by_cases hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2
  · simp only [if_pos hc]
    have he := tsum_congr (L := SummationFilter.unconditional ℤ)
      (fun h ↦ d.transposed_poissonNonzeroFrequency_eq_canonicalPhases hd hl hl' hc h)
    rw [he]
  · simp only [if_neg hc]

end

end ImbalancedChen.Part3
