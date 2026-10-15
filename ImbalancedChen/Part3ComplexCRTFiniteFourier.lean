import ImbalancedChen.Part3ComplexCRTConsumer
import ImbalancedChen.Part3CenteredFourier

/-!
# Finite Fourier completion of the actual common CRT progression

Only the already proved full-modulus additive orthogonality is used.
The same original finite support S and real weight w occur at every
modulus pair and every frequency. The zero frequency is the actual
mass of w on S divided by the complete lcm modulus. The other term is
the full finite nonzero-frequency sum; no cancellation estimate is made.

Actual row labels are attached only to carry their membership proofs.
These supply positivity of both complete moduli and their lcm from
MediumAdmissible. No caller supplies a completion or inverse identity.
The complex gamma/beta coefficients and the compatible/incompatible
branches remain unchanged. Modulus one is included.

The last identity retains the actual primitive-centre V and U. It does
not identify the raw zero mode with those terms, replace w by a different
weight for each modulus, apply Poisson summation, or prove distribution.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical

/-- The original common weighted finite source at one additive frequency. -/
def finiteSourceAdditiveFourier (S : Finset ℕ) (w : ℕ → ℝ)
    (L : ℕ) [NeZero L] (h : ZMod L) : ℂ :=
  ∑ n ∈ S, (w n : ℂ) * ZMod.stdAddChar (h * (n : ZMod L))

theorem finiteSourceAdditiveFourier_zero (S : Finset ℕ) (w : ℕ → ℝ)
    (L : ℕ) [NeZero L] :
    finiteSourceAdditiveFourier S w L 0 = ((∑ n ∈ S, w n : ℝ) : ℂ) := by
  simp [finiteSourceAdditiveFourier, Complex.ofReal_sum]

/-- Exact raw progression Fourier inversion, before the zero mode is
separated. The complete residue and signed integer endpoint predicate agree. -/
theorem finiteProgressionWeight_eq_fullFourier (S : Finset ℕ) (w : ℕ → ℝ)
    (L : ℕ) [NeZero L] (b : ℤ) :
    ((∑ n ∈ S, if Int.ModEq L (n : ℤ) b then w n else 0 : ℝ) : ℂ) =
      (L : ℂ)⁻¹ * ∑ h : ZMod L,
        ZMod.stdAddChar (-h * (b : ZMod L)) * finiteSourceAdditiveFourier S w L h := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hind (n : ℕ) :
      (if Int.ModEq L (n : ℤ) b then (1 : ℂ) else 0) =
        (L : ℂ)⁻¹ * ∑ h : ZMod L,
          ZMod.stdAddChar (-h * (b : ZMod L)) *
            ZMod.stdAddChar (h * (n : ZMod L)) := by
    rw [sum_residueAdditiveCoefficient_mul]
    have heq : (n : ZMod L) = (b : ZMod L) ↔ Int.ModEq L (n : ℤ) b := by
      simpa only [Int.cast_natCast] using ZMod.intCast_eq_intCast_iff (n : ℤ) b L
    simp only [heq]
    rw [← mul_assoc, inv_mul_cancel₀ hL, one_mul]
  calc
    _ = ∑ n ∈ S, (w n : ℂ) *
        (if Int.ModEq L (n : ℤ) b then (1 : ℂ) else 0) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : Int.ModEq L (n : ℤ) b <;> simp [h]
    _ = ∑ n ∈ S, ∑ h : ZMod L,
        (L : ℂ)⁻¹ * ZMod.stdAddChar (-h * (b : ZMod L)) *
          ((w n : ℂ) * ZMod.stdAddChar (h * (n : ZMod L))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hind]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = ∑ h : ZMod L, ∑ n ∈ S,
        (L : ℂ)⁻¹ * ZMod.stdAddChar (-h * (b : ZMod L)) *
          ((w n : ℂ) * ZMod.stdAddChar (h * (n : ZMod L))) := Finset.sum_comm
    _ = _ := by
      simp only [finiteSourceAdditiveFourier, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro n _
      ring

def finiteProgressionNonzeroFourier (S : Finset ℕ) (w : ℕ → ℝ)
    (L : ℕ) [NeZero L] (b : ℤ) : ℂ :=
  (L : ℂ)⁻¹ * ∑ h ∈ (Finset.univ : Finset (ZMod L)).erase 0,
    ZMod.stdAddChar (-h * (b : ZMod L)) * finiteSourceAdditiveFourier S w L h

/-- The zero mode is exactly the original finite mass divided by L. -/
theorem finiteProgressionWeight_eq_mass_add_nonzero (S : Finset ℕ)
    (w : ℕ → ℝ) (L : ℕ) [NeZero L] (b : ℤ) :
    ((∑ n ∈ S, if Int.ModEq L (n : ℤ) b then w n else 0 : ℝ) : ℂ) =
      ((∑ n ∈ S, w n : ℝ) : ℂ) / L +
        finiteProgressionNonzeroFourier S w L b := by
  rw [finiteProgressionWeight_eq_fullFourier]
  have herase := Finset.sum_erase_add (Finset.univ : Finset (ZMod L))
    (fun h => ZMod.stdAddChar (-h * (b : ZMod L)) *
      finiteSourceAdditiveFourier S w L h) (Finset.mem_univ 0)
  simp only [finiteSourceAdditiveFourier_zero, neg_zero, zero_mul,
    AddChar.map_zero_eq_one, one_mul] at herase
  rw [← herase]
  unfold finiteProgressionNonzeroFourier
  ring

theorem finiteProgressionNonzeroFourier_modulus_one (S : Finset ℕ)
    (w : ℕ → ℝ) (b : ℤ) : finiteProgressionNonzeroFourier S w 1 b = 0 := by
  have he : (Finset.univ : Finset (ZMod 1)).erase 0 = ∅ := by
    ext h
    have hh : h = 0 := Subsingleton.elim _ _
    simp [hh]
  unfold finiteProgressionNonzeroFourier
  rw [he]
  simp only [Finset.sum_empty, mul_zero]

private theorem actual_pair_lcm_ne_zero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels) :
    (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) ≠ 0 := by
  obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
  have factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {q : ℕ}
      (hq : q ∈ factorCarrier Q) : 0 < q := by
    have hlo := (Finset.mem_Icc.mp hq).1
    have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
    omega
  have hmod {k : (ℕ × ℕ × ℕ) × ℕ} (hk : k ∈ d.complexRowLabels) :
      0 < complexFactorModulus k.1 := by
    have hf := (Finset.mem_product.mp hk).1
    obtain ⟨hf1, hf23⟩ := Finset.mem_product.mp hf
    obtain ⟨hf2, hf3⟩ := Finset.mem_product.mp hf23
    exact Nat.mul_pos (Nat.mul_pos (factor_pos hQ1 hf1) (factor_pos hQ2 hf2))
      (factor_pos hQ3 hf3)
  exact Nat.lcm_ne_zero (hmod hl).ne' (hmod hl').ne'

/-- The full raw CRT zero mode, with every original factor/beta label. -/
def MediumAtom.complexCRTFiniteZeroPart (d : MediumAtom)
    (S : Finset ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ l ∈ d.complexRowLabels.attach, ∑ l' ∈ d.complexRowLabels.attach,
    d.complexBetaCoefficient l.val * star (d.complexBetaCoefficient l'.val) *
      (if ComplexCRT.Compatible (complexFactorModulus l.val.1)
        (complexFactorModulus l'.val.1) l.val.2 l'.val.2 then
          ((∑ n ∈ S, w n : ℝ) : ℂ) /
            ((complexFactorModulus l.val.1).lcm (complexFactorModulus l'.val.1) : ℕ)
      else 0)

/-- The exact finite nonzero frequencies of the same common S,w. -/
def MediumAtom.complexCRTFiniteNonzeroPart
    {B : ℕ} {sigma kappa c0 : ℝ} (d : MediumAtom)
    (hd : MediumAdmissible B sigma kappa c0 d) (S : Finset ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ l ∈ d.complexRowLabels.attach, ∑ l' ∈ d.complexRowLabels.attach,
    letI : NeZero ((complexFactorModulus l.val.1).lcm (complexFactorModulus l'.val.1)) :=
      ⟨actual_pair_lcm_ne_zero hd l.property l'.property⟩
    d.complexBetaCoefficient l.val * star (d.complexBetaCoefficient l'.val) *
      (if ComplexCRT.Compatible (complexFactorModulus l.val.1)
        (complexFactorModulus l'.val.1) l.val.2 l'.val.2 then
          finiteProgressionNonzeroFourier S w
            ((complexFactorModulus l.val.1).lcm (complexFactorModulus l'.val.1))
            (ComplexCRT.residue (complexFactorModulus l.val.1)
              (complexFactorModulus l'.val.1) l.val.2 l'.val.2 d.residue)
      else 0)

/-- The actual complex W component, including all inactive gamma labels,
is exactly its raw zero part plus its finite nonzero-frequency part. -/
theorem MediumAtom.complexDispersionW_eq_finiteZero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (S : Finset ℕ) (w : ℕ → ℝ) :
    (d.complexDispersionW S w : ℂ) =
      d.complexCRTFiniteZeroPart S w + d.complexCRTFiniteNonzeroPart hd S w := by
  unfold MediumAtom.complexCRTFiniteZeroPart MediumAtom.complexCRTFiniteNonzeroPart
  calc
    _ = ∑ l ∈ d.complexRowLabels.attach, ∑ l' ∈ d.complexRowLabels.attach,
        d.complexBetaCoefficient l.val * star (d.complexBetaCoefficient l'.val) *
          (ComplexCRT.constructedProgressionWeight S w d.residue
            (complexFactorModulus l.val.1) (complexFactorModulus l'.val.1)
              l.val.2 l'.val.2 : ℂ) := by
      simpa only [Finset.sum_attach] using
        (MediumAtom.complexDispersionW_eq_constructedCRT hd S w)
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l' _
      let : NeZero ((complexFactorModulus l.val.1).lcm
          (complexFactorModulus l'.val.1)) :=
        ⟨actual_pair_lcm_ne_zero hd l.property l'.property⟩
      unfold ComplexCRT.constructedProgressionWeight
      by_cases hc : ComplexCRT.Compatible (complexFactorModulus l.val.1)
          (complexFactorModulus l'.val.1) l.val.2 l'.val.2
      · simp only [hc, if_true]
        rw [finiteProgressionWeight_eq_mass_add_nonzero]
        ring
      · simp only [hc, if_false, mul_zero, add_zero]

/-- Primitive-centre V/U remain displayed. No zero-mode cancellation is
assumed, and the final finite frequencies still use the same S and w. -/
theorem MediumAtom.complex_dispersion_identity_with_finiteFourier
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (S : Finset ℕ) (w : ℕ → ℝ) :
    ((∑ n ∈ S, w n * ‖d.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (d.complexCRTFiniteZeroPart S w - 2 * (d.complexDispersionV S w : ℂ) +
        (d.complexDispersionU S w : ℂ)) + d.complexCRTFiniteNonzeroPart hd S w := by
  rw [MediumAtom.complex_dispersion_identity]
  push_cast
  rw [MediumAtom.complexDispersionW_eq_finiteZero_add_nonzero hd]
  ring

end

end ImbalancedChen.Part3
