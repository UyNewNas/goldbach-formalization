import ImbalancedChen.Part3OriginalBothSmallMaskedW
import ImbalancedChen.Part3SmoothProgressionError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 2.

A nontrivial ORIGINAL legal boundary range: every retained physical lcm
is at most eta times original V. The ORIGINAL both-small nonzero W is
bounded by C*eta times its actual retained beta/gamma L1 mass. The bound
comes from one additional actual Schwartz decay power; it is not a
spectral assumption. All labels, original signed coefficients, both gcd
masks and compatibility remain in the source. No assertion is made that
this short-modulus range covers the full manuscript range or proves 7/32.
-/

namespace ImbalancedChen.Part3.OriginalMaskedWShortModulusBound20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalBothSmallMaskedW20261026b
open scoped BigOperators SchwartzMap FourierTransform

/-- The actual fixed cutoff gains an inverse mesh in the COMPLETE
nonzero integer-frequency sum. The old O(1) bound alone would not do so. -/
theorem poisson_nonzero_inverse_mesh :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      ‖∑' h : ℤ, poissonNonzeroFrequency t x h‖ ≤ C / t := by
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) 3
  refine ⟨2*C, by positivity, fun t ht x => ?_⟩
  obtain ⟨hDs, hDb⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (h : ℤ) :
      ‖poissonNonzeroFrequency t x h‖ ≤ (C/t) * poissonNonzeroDecay t h := by
    by_cases hh : h = 0
    · simp [poissonNonzeroFrequency, poissonNonzeroDecay, hh]
    · have hhR : (1 : ℝ) ≤ |(h : ℝ)| := by
        rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
        exact Int.one_le_abs hh
      let A : ℝ := 1 + |t*(h : ℝ)|
      have hA : 0 < A := by dsimp [A]; positivity
      have htA : t ≤ A := by
        dsimp [A]
        rw [abs_mul, abs_of_pos ht]
        nlinarith
      simp only [poissonNonzeroFrequency, poissonNonzeroDecay, if_neg hh,
        norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        fourier_apply, Circle.norm_coe, mul_one]
      calc
        _ ≤ t * (C / A^3) := mul_le_mul_of_nonneg_left (hdecay (t*h)) ht.le
        _ = (C / A^2) * (t/A) := by field_simp [hA.ne']; ring
        _ ≤ (C / A^2) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one₀ hA).mpr htA) (by positivity)
        _ = (C/t) * (t / (1+|t*(h : ℝ)|)^2) := by
          change (C / A^2) * 1 = (C/t) * (t / A^2)
          field_simp [ht.ne', hA.ne']
          ring
  have hnorm := poissonNonzeroFrequency_summable_norm ht x
  calc
    _ ≤ ∑' h : ℤ, ‖poissonNonzeroFrequency t x h‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' h : ℤ, (C/t) * poissonNonzeroDecay t h :=
      hnorm.tsum_le_tsum hpoint (hDs.mul_left (C/t))
    _ = (C/t) * ∑' h : ℤ, poissonNonzeroDecay t h := tsum_mul_left
    _ ≤ (C/t)*2 := mul_le_mul_of_nonneg_left hDb (by positivity)
    _ = (2*C)/t := by ring

def factorMass (d : MediumAtom) (D : ℝ) (n1 n2 : ℕ) : ℝ :=
  ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then 0 else
      if ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n1 n2 then
        ‖d.complexFactorGamma a * star (d.complexFactorGamma b)‖ else 0

def retainedMass (d : MediumAtom) (Y D : ℝ) : ℝ :=
  ∑ n1 ∈ d.betaCarrier, ∑ n2 ∈ d.betaCarrier,
    if Y < (n1.gcd n2 : ℝ) then 0 else
      ‖d.beta n1 * star (d.beta n2)‖ * factorMass d D n1 n2

private theorem actual_modulus_pos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {a : ℕ × ℕ × ℕ}
    (ha : a ∈ d.complexFactorLabels) : 0 < complexFactorModulus a :=
  (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
    (Finset.mem_image_of_mem _ ha))).1

/-- A primitive ORIGINAL boundary inequality on retained physical lcms,
not a premise asserting a bound for W or for its Fourier remainder. -/
def ShortRetainedModuli (d : MediumAtom) (D eta : ℝ) : Prop :=
  ∀ a ∈ d.complexFactorLabels, ∀ b ∈ d.complexFactorLabels,
    ¬ D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) →
      (((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ) : ℝ) ≤ eta*d.V

/-- An explicit original-parameter boundary suffices. The cap is the
existing 8*Q1*Q2*Q3; no enlarged or replacement modulus carrier is used. -/
theorem shortRetainedModuli_of_physicalCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D eta : ℝ)
    (hcap : d.physicalFactorCap^2 ≤ eta*d.V) : ShortRetainedModuli d D eta := by
  intro a ha b hb hD
  have hca := Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
    (Finset.mem_image_of_mem _ ha))
  have hcb := Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
    (Finset.mem_image_of_mem _ hb))
  have hcap0 : 0 ≤ d.physicalFactorCap := zero_le_one.trans (d.one_le_physicalFactorCap hd)
  have hqa : (complexFactorModulus a : ℝ) ≤ d.physicalFactorCap :=
    (show (complexFactorModulus a : ℝ) ≤ (Nat.floor d.physicalFactorCap : ℝ) by
      exact_mod_cast hca.2).trans (Nat.floor_le hcap0)
  have hqb : (complexFactorModulus b : ℝ) ≤ d.physicalFactorCap :=
    (show (complexFactorModulus b : ℝ) ≤ (Nat.floor d.physicalFactorCap : ℝ) by
      exact_mod_cast hcb.2).trans (Nat.floor_le hcap0)
  calc
    _ ≤ ((complexFactorModulus a * complexFactorModulus b : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hca.1 hcb.1) (Nat.lcm_dvd_mul _ _)
    _ = (complexFactorModulus a : ℝ) * (complexFactorModulus b : ℝ) := by norm_cast
    _ ≤ d.physicalFactorCap * d.physicalFactorCap :=
      mul_le_mul hqa hqb (Nat.cast_nonneg _) hcap0
    _ = d.physicalFactorCap^2 := by ring
    _ ≤ eta*d.V := hcap

private theorem factor_nonzero_bound
    (C : ℝ) (hC : 0 < C)
    (hmesh : ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      ‖∑' h : ℤ, poissonNonzeroFrequency t x h‖ ≤ C/t)
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D eta : ℝ)
    (hshort : ShortRetainedModuli d D eta) (n1 n2 : ℕ) :
    ‖d.transposedAtom.commonModulusGCDNonzeroWeight D false n1 n2‖ ≤
      (C*eta) * factorMass d.transposedAtom D n1 n2 := by
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  unfold MediumAtom.commonModulusGCDNonzeroWeight factorMass
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  by_cases hD : D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ)
  · simp [hD]
  · by_cases hc : ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n1 n2
    · have hL : (0 : ℝ) < ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero
          (actual_modulus_pos hd ha).ne' (actual_modulus_pos hd hb).ne')
      have hlev := hshort a ha b hb hD
      have hrem :
          ‖∑' h : ℤ, poissonNonzeroFrequency
            (d.V / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ))
            ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
              n1 n2 d.residue : ℝ) / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ)) h‖ ≤ C*eta := by
        calc
          _ ≤ C / (d.V / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ)) :=
            hmesh _ (div_pos hV hL) _
          _ = C * ((((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ) : ℝ) / d.V) := by
            field_simp [hV.ne', hL.ne']; ring
          _ ≤ C*eta := mul_le_mul_of_nonneg_left ((div_le_iff₀ hV).mpr hlev) hC.le
      simp only [hD, hc, decide_false, if_false, if_true]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans hrem) (norm_nonneg _)).trans_eq (mul_comm _ _)
    · simp [hD, hc]

/-- Actual original both-small remainder, on the legal short-lcm range.
The constant is selected before the original atom, masks and eta. -/
theorem original_bothSmall_nonzero_short_modulus_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D eta : ℝ,
        ShortRetainedModuli d D eta →
        ‖d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D false‖ ≤
          (C*eta) * retainedMass d.transposedAtom Y D := by
  obtain ⟨C, hC, hmesh⟩ := poisson_nonzero_inverse_mesh
  refine ⟨C, hC, fun B sigma kappa c0 d hd Y D eta hshort => ?_⟩
  unfold MediumAtom.commonSmallBetaModulusGCDNonzeroPart retainedMass
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n1 hn1
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n2 hn2
  by_cases hy : Y < (n1.gcd n2 : ℝ)
  · simp [hy]
  · simp only [if_neg hy]
    rw [norm_mul]
    calc
      _ ≤ ‖d.transposedAtom.beta n1 * star (d.transposedAtom.beta n2)‖ *
          ((C*eta) * factorMass d.transposedAtom D n1 n2) :=
        mul_le_mul_of_nonneg_left
          (factor_nonzero_bound C hC hmesh hd D eta hshort n1 n2) (norm_nonneg _)
      _ = _ := by ring

/-- No analytic bound or model bridge is assumed here: this is a bound
for the ORIGINAL retained both-small nonzero source on EVERY admissible
atom. It is useful when (8*Q1*Q2*Q3)^2/V is small, a genuine boundary
subrange rather than the full retained spectral range. -/
theorem original_bothSmall_nonzero_physicalCap_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D : ℝ,
        ‖d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart Y D false‖ ≤
          (C * (d.physicalFactorCap^2 / d.V)) * retainedMass d.transposedAtom Y D := by
  obtain ⟨C,hC,hbound⟩ := original_bothSmall_nonzero_short_modulus_bound
  refine ⟨C,hC,fun B sigma kappa c0 d hd Y D => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  apply hbound B sigma kappa c0 d hd Y D (d.physicalFactorCap^2/d.V)
  apply shortRetainedModuli_of_physicalCap hd
  rw [div_mul_cancel₀ _ hV.ne']

/-- The same estimate applies to the literal original masked W minus its
own raw zero, using the proved equality rather than an assumed bridge. -/
theorem original_maskedW_sub_rawZero_short_modulus_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y D eta : ℝ,
        ShortRetainedModuli d D eta →
        ‖wholeW d.transposedAtom Y D - rawZero d.transposedAtom Y D‖ ≤
          (C*eta) * retainedMass d.transposedAtom Y D := by
  obtain ⟨C, hC, hbound⟩ := original_bothSmall_nonzero_short_modulus_bound
  refine ⟨C, hC, fun B sigma kappa c0 d hd Y D eta hshort => ?_⟩
  rw [← original_nonzero_eq_maskedW_sub_rawZero hd]
  exact hbound B sigma kappa c0 d hd Y D eta hshort

end
end ImbalancedChen.Part3.OriginalMaskedWShortModulusBound20261026b
