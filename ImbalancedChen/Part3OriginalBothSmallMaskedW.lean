import ImbalancedChen.Part3TransposedModulusGCDZero

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 2.

The missing literal whole-W and raw-zero model under BOTH original small
gcd masks. There is no new reciprocal model and no assumed bridge to a
downstream squared Kloosterman family. Original beta/gamma, factor labels,
CRT compatibility, residue and physical smoothing are all retained.
Applied to d.transposedAtom, the smoothing scale here is original V.
The signed difference is exactly the EXISTING both-small nonzero term.
The full spectral 7/32 bound remains OPEN.
-/

namespace ImbalancedChen.Part3.OriginalBothSmallMaskedW20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff
open scoped BigOperators

def factorPairW (d : MediumAtom) (D : ℝ) (n1 n2 : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then 0 else
        (ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
          d.residue (complexFactorModulus a) (complexFactorModulus b) n1 n2 : ℂ))

def factorPairZero (d : MediumAtom) (D : ℝ) (n1 n2 : ℕ) : ℂ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
      (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then 0 else
        ((if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n1 n2 then
          (d.U / (complexFactorModulus a).lcm (complexFactorModulus b)) * cutoffMass
        else 0 : ℝ) : ℂ))

def wholeW (d : MediumAtom) (Y D : ℝ) : ℂ :=
  ∑ n1 ∈ d.betaCarrier, ∑ n2 ∈ d.betaCarrier,
    if Y < (n1.gcd n2 : ℝ) then 0 else
      d.beta n1 * star (d.beta n2) * factorPairW d D n1 n2

def rawZero (d : MediumAtom) (Y D : ℝ) : ℂ :=
  ∑ n1 ∈ d.betaCarrier, ∑ n2 ∈ d.betaCarrier,
    if Y < (n1.gcd n2 : ℝ) then 0 else
      d.beta n1 * star (d.beta n2) * factorPairZero d D n1 n2

/-- Exact complementary masks in the original whole W. -/
theorem original_smallBetaW_split (d : MediumAtom) (Y D : ℝ) :
    d.commonSmallBetaGCDW Y = d.commonSmallBetaLargeModulusGCDW Y D + wholeW d Y D := by
  unfold MediumAtom.commonSmallBetaGCDW MediumAtom.commonSmallBetaLargeModulusGCDW wholeW
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n1 hn1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n2 hn2
  by_cases hy : Y < (n1.gcd n2 : ℝ)
  · simp only [if_pos hy, add_zero]
  · simp only [if_neg hy, ← mul_add]
    congr 1
    unfold MediumAtom.commonFactorPairWeight MediumAtom.commonLargeModulusGCDWeight factorPairW
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hD : D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) <;>
      simp [hD]

private theorem modulus_pos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {a : ℕ × ℕ × ℕ}
    (ha : a ∈ d.complexFactorLabels) : 0 < complexFactorModulus a :=
  (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
    (Finset.mem_image_of_mem _ ha))).1

/-- Poisson on every original complete lcm, with the complementary
modulus gate exactly matching the pre-existing false branch. -/
theorem original_transposed_factorW_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D : ℝ) (n1 n2 : ℕ) :
    factorPairW d.transposedAtom D n1 n2 = factorPairZero d.transposedAtom D n1 n2 +
      d.transposedAtom.commonModulusGCDNonzeroWeight D false n1 n2 := by
  unfold factorPairW factorPairZero MediumAtom.commonModulusGCDNonzeroWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hD : D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ)
  · simp [hD]
  · simp only [hD, decide_false, Bool.false_eq_true, if_false, if_true]
    unfold ComplexCRT.constructedProgressionWeight
    by_cases hc : ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n1 n2
    · simp only [if_pos hc]
      have hL : 0 < (complexFactorModulus a).lcm (complexFactorModulus b) :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (modulus_pos hd ha).ne' (modulus_pos hd hb).ne')
      have he := scaledDyadicCutoff_finset_progression_eq_main_add_fourier
        (M := d.transposedAtom.U) (lt_of_lt_of_le zero_lt_one hd.2.1)
        d.transposedAtom.commonSmoothCarrier
        (fun m hm => d.transposedSmoothWeight_support_subset hd.2.1 hm) hL
        (ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b) n1 n2 d.residue)
      simp only [MediumAtom.commonSmoothWeight]
      rw [he, Complex.ofReal_add]
      ring
    · simp only [if_neg hc, Complex.ofReal_zero, mul_zero, add_zero]

/-- This is the actual original both-small Fourier remainder, not a
newly substituted source and not an assumption about its size. -/
theorem original_transposed_maskedW_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y D : ℝ) :
    wholeW d.transposedAtom Y D = rawZero d.transposedAtom Y D +
      d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D false := by
  unfold wholeW rawZero MediumAtom.commonSmallBetaModulusGCDNonzeroPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n1 hn1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n2 hn2
  by_cases hy : Y < (n1.gcd n2 : ℝ)
  · simp only [if_pos hy, add_zero]
  · simp only [if_neg hy, original_transposed_factorW_eq_zero_add_nonzero hd, mul_add]

theorem original_nonzero_eq_maskedW_sub_rawZero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y D : ℝ) :
    d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D false =
      wholeW d.transposedAtom Y D - rawZero d.transposedAtom Y D := by
  rw [original_transposed_maskedW_eq_zero_add_nonzero hd]
  ring

end
end ImbalancedChen.Part3.OriginalBothSmallMaskedW20261026b
