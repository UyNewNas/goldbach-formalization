import ImbalancedChen.Part3OriginalPhysicalPoissonTruncation
import ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
import ImbalancedChen.Part3SharedFirstFactorDispersion
import ImbalancedChen.Part3TransposedCanonicalReciprocalPhase
import Mathlib.Tactic

/-!
Source only. Exact paper-profile Poisson on the ACTUAL original shared-first
factor squared row. The actual q weight is retained outside each slice;
alpha, gamma2, gamma3 and both physical moduli remain the installed source
objects. Each complete lcm, tail gcd and canonical three-part Fourier phase
is constructed from the same two original labels. The underlying W expansion
is the existing q1SliceDispersionW_eq_sharedCRT theorem for arbitrary finite
S and real w, now instantiated with the actual Gevrey profile.

This is the W component before the subsequent clean E2 quotient partition.
No equality of the Gevrey profile with the older common dyadic bump is used.
The enlarged smooth-q carrier and the E2 quotient/phase chart transport still
need their own dictionaries. No E2 estimate or medium conclusion is assumed.
-/

noncomputable section
open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalPhysicalGevreyFrequencyScale20261028
open ImbalancedChen.Part3.OriginalPhysicalPoissonTruncation20261028
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter

namespace ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028

abbrev Row := (ℕ × ℕ) × ℕ

def liftRow (p : ℕ) (l : Row) : (ℕ × ℕ × ℕ) × ℕ :=
  ((p, (l.1.1, l.1.2)), l.2)

def tailProduct (l : Row) : ℕ := l.1.1 * l.1.2

def completeModulus (p : ℕ) (l l' : Row) : ℕ :=
  (p * tailProduct l).lcm (p * tailProduct l')

def tailGcd (l l' : Row) : ℕ := (tailProduct l).gcd (tailProduct l')

def pairCompatible (p : ℕ) (l l' : Row) : Prop :=
  ComplexCRT.Compatible (p * tailProduct l) (p * tailProduct l') l.2 l'.2

def pairResidue (d : MediumAtom) (p : ℕ) (l l' : Row) : ℤ :=
  ComplexCRT.residue (p * tailProduct l) (p * tailProduct l') l.2 l'.2 d.residue

def paperMWeight (d : MediumAtom) (m : ℕ) : ℝ := paperPsi ((m : ℝ) / d.V)

def rowWindow (d : MediumAtom) (x : ℝ) (l l' : Row) : ℕ :=
  physicalH (Real.log x ^ 5) d.Q1 d.Q3 d.Q2 d.V (tailGcd l l')

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : 0 < n := by
  have hlo := (Finset.mem_Icc.mp hn).1
  have hc : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

private theorem factor_le {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : (n : ℝ) ≤ 2 * Q := by
  exact (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by
    exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

/-- No assumption on coprimality of the two physical moduli is introduced. -/
theorem completeModulus_pos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) {l l' : Row}
    (hl : l ∈ d.sharedFirstFactorRows) (hl' : l' ∈ d.sharedFirstFactorRows) :
    0 < completeModulus p l l' ∧ 0 < tailGcd l l' := by
  have hp0 := factor_pos hd.2.2.1 (Finset.mem_filter.mp hp).1
  have hlf := (Finset.mem_product.mp hl).1
  have hrf := (Finset.mem_product.mp hl').1
  have ht : 0 < tailProduct l := Nat.mul_pos
    (factor_pos hd.2.2.2.1 (Finset.mem_product.mp hlf).1)
    (factor_pos hd.2.2.2.2.1 (Finset.mem_product.mp hlf).2)
  have ht' : 0 < tailProduct l' := Nat.mul_pos
    (factor_pos hd.2.2.2.1 (Finset.mem_product.mp hrf).1)
    (factor_pos hd.2.2.2.2.1 (Finset.mem_product.mp hrf).2)
  exact ⟨Nat.lcm_pos (Nat.mul_pos hp0 ht) (Nat.mul_pos hp0 ht'),
    Nat.gcd_pos_of_pos_left _ ht⟩

/-- Literal gcd times physical complete lcm, with the shared p only once. -/
theorem tailGcd_mul_completeModulus (p : ℕ) (l l' : Row) :
    tailGcd l l' * completeModulus p l l' =
      p * tailProduct l * tailProduct l' := by
  unfold tailGcd completeModulus
  rw [sharedFirstFactor_lcm]
  calc
    _ = p * ((tailProduct l).gcd (tailProduct l') *
        (tailProduct l).lcm (tailProduct l')) := by ring
    _ = _ := by rw [Nat.gcd_mul_lcm]; ring

/-- The bound used by the physicalH theorem is derived for actual rows;
it is not an additional caller certificate for the E2 output. -/
theorem actual_row_complete_modulus_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) {l l' : Row}
    (hl : l ∈ d.sharedFirstFactorRows) (hl' : l' ∈ d.sharedFirstFactorRows) :
    (tailGcd l l' : ℝ) * (completeModulus p l l' : ℝ) ≤
      32 * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 := by
  have hpf := factor_le hd.2.2.1 (Finset.mem_filter.mp hp).1
  have hlf := (Finset.mem_product.mp hl).1
  have hrf := (Finset.mem_product.mp hl').1
  have hs := factor_le hd.2.2.2.1 (Finset.mem_product.mp hlf).1
  have hr := factor_le hd.2.2.2.2.1 (Finset.mem_product.mp hlf).2
  have hs' := factor_le hd.2.2.2.1 (Finset.mem_product.mp hrf).1
  have hr' := factor_le hd.2.2.2.2.1 (Finset.mem_product.mp hrf).2
  have hQ1 : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
  have hQ2 : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  have hQ3 : 0 ≤ d.Q3 := zero_le_one.trans hd.2.2.2.2.1
  rw [← Nat.cast_mul, tailGcd_mul_completeModulus]
  simp only [tailProduct, Nat.cast_mul]
  calc
    _ ≤ (2 * d.Q1) * ((2 * d.Q2) * (2 * d.Q3)) *
        ((2 * d.Q2) * (2 * d.Q3)) := by gcongr
    _ = _ := by ring

/-- Embed the same reduced row into the actual transposed source labels. -/
theorem liftRow_mem {d : MediumAtom} {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) {l : Row}
    (hl : l ∈ d.sharedFirstFactorRows) :
    liftRow p l ∈ d.transposedAtom.complexRowLabels := by
  obtain ⟨hpair, hn⟩ := Finset.mem_product.mp hl
  refine Finset.mem_product.mpr ⟨?_, hn⟩
  change (p, (l.1.1, l.1.2)) ∈
    factorCarrier d.Q1 ×ˢ (factorCarrier d.Q2 ×ˢ factorCarrier d.Q3)
  exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hp).1, hpair⟩

/-- The retained phase is the installed source's full root, slow and
reciprocal phase product, for the same actual complete CRT residue. -/
theorem actual_row_paperPsi_mode_eq_canonicalPhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) {l l' : Row}
    (hl : l ∈ d.sharedFirstFactorRows) (hl' : l' ∈ d.sharedFirstFactorRows)
    (hc : pairCompatible p l l') (h : ℤ) :
    let v := d.transposedAtom.canonicalReciprocalData (liftRow p l) (liftRow p l')
    paperPsiNonzeroMode (d.V / (completeModulus p l l' : ℝ))
      ((pairResidue d p l l' : ℝ) / (completeModulus p l l' : ℝ)) h =
      if h = 0 then 0 else
        ((d.V / (completeModulus p l l' : ℝ)) •
          (𝓕 paperPsiComplex) ((d.V / (completeModulus p l l' : ℝ)) * h)) *
          fourier h (CanonicalReciprocalPhase.rootPhase v
            (pairResidue d p l l') d.residue) *
          fourier h (CanonicalReciprocalPhase.slowPhase v d.residue) *
          fourier h (CanonicalReciprocalPhase.reciprocalPhase v d.residue) := by
  dsimp only
  unfold paperPsiNonzeroMode
  by_cases hh : h = 0
  · simp only [if_pos hh]
  · simp only [if_neg hh]
    have hpPhase := d.transposed_actualCRT_fourier_eq_canonicalPhases hd
      (liftRow_mem hp hl) (liftRow_mem hp hl')
      (by simpa only [liftRow, complexFactorModulus, tailProduct,
        pairCompatible, Nat.mul_assoc] using hc) h
    have he :
        fourier h (((pairResidue d p l l' : ℝ) /
          (completeModulus p l l' : ℝ)) : UnitAddCircle) =
        fourier h (CanonicalReciprocalPhase.rootPhase
          (d.transposedAtom.canonicalReciprocalData (liftRow p l) (liftRow p l'))
          (pairResidue d p l l') d.residue) *
        fourier h (CanonicalReciprocalPhase.slowPhase
          (d.transposedAtom.canonicalReciprocalData (liftRow p l) (liftRow p l'))
          d.residue) *
        fourier h (CanonicalReciprocalPhase.reciprocalPhase
          (d.transposedAtom.canonicalReciprocalData (liftRow p l) (liftRow p l'))
          d.residue) := by
      simpa only [liftRow, complexFactorModulus, completeModulus,
        tailProduct, pairResidue, Nat.mul_assoc] using hpPhase
    rw [he]
    ring

/-- Exact new profile insertion in the old arbitrary-weight W identity.
The q majorant is the source actualPsiQWeight, retained before any norm. -/
def actualSharedW (d : MediumAtom) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    actualPsiQWeight d p *
      (((d.q1SliceAtom p).transposedAtom.complexDispersionW
        (paperPsiNaturalCarrier d.V) (paperMWeight d) : ℝ) : ℂ)

def rowZero (d : MediumAtom) (p : ℕ) (l l' : Row) : ℂ :=
  if pairCompatible p l l' then
    (d.V / (completeModulus p l l' : ℝ)) • (𝓕 paperPsiComplex) 0 else 0

def rowRetained (d : MediumAtom) (x : ℝ) (p : ℕ) (l l' : Row) : ℂ :=
  if pairCompatible p l l' then
    ∑ h ∈ signedWindow (rowWindow d x l l'),
      paperPsiNonzeroMode (d.V / (completeModulus p l l' : ℝ))
        ((pairResidue d p l l' : ℝ) / (completeModulus p l l' : ℝ)) h else 0

def rowError (d : MediumAtom) (x : ℝ) (p : ℕ) (l l' : Row) : ℂ :=
  if pairCompatible p l l' then
    finitePacketError d.V (completeModulus p l l') (pairResidue d p l l')
      (rowWindow d x l l') else 0

/-- Both the q majorant and all source alpha/tail coefficients remain
literal. This is an exact three-term decomposition, with the error still
signed and no E2-smallness assertion among its premises. -/
theorem actualSharedW_eq_zero_retained_error
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (x : ℝ) :
    actualSharedW d =
      ∑ p ∈ d.primitiveFirstFactorCarrier, ∑ l ∈ d.sharedFirstFactorRows,
        ∑ l' ∈ d.sharedFirstFactorRows,
          actualPsiQWeight d p *
            (d.sharedFirstFactorCoefficient l * star (d.sharedFirstFactorCoefficient l')) *
              (rowZero d p l l' + rowRetained d x p l l' + rowError d x p l l') := by
  unfold actualSharedW
  apply Finset.sum_congr rfl
  intro p hp
  rw [d.q1SliceDispersionW_eq_sharedCRT hd hp]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro l' hl'
  unfold rowZero rowRetained rowError
  by_cases hc : pairCompatible p l l'
  · have hfinite :
        ((ComplexCRT.constructedProgressionWeight (paperPsiNaturalCarrier d.V)
          (paperMWeight d) d.residue (p * (l.1.1 * l.1.2))
          (p * (l'.1.1 * l'.1.2)) l.2 l'.2 : ℝ) : ℂ) =
        ∑ m ∈ paperPsiNaturalCarrier d.V,
          if Int.ModEq (completeModulus p l l') (m : ℤ)
            (pairResidue d p l l') then scaledPaperPsi d.V m else 0 := by
      simp only [ComplexCRT.constructedProgressionWeight,
        show ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
          (p * (l'.1.1 * l'.1.2)) l.2 l'.2 from hc, if_true]
      simp [completeModulus, pairResidue, tailProduct, paperMWeight,
        scaledPaperPsi, paperPsiComplex, Complex.ofReal_sum]
    simp only [if_pos hc]
    rw [hfinite]
    unfold finitePacketError
    ring
  · have hn : ¬ ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
        (p * (l'.1.1 * l'.1.2)) l.2 l'.2 := hc
    simp only [if_neg hc, ComplexCRT.constructedProgressionWeight,
      if_neg hn, Complex.ofReal_zero, mul_zero, add_zero]

/-- Uniform tail at the literal row's gcd-adapted window. The modulus and
D*L bound are supplied by the actual labels, not external caller data. -/
theorem actual_row_error_all_fixed_powers (A : ℝ) (hA : 0 ≤ A) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d →
        ∀ p ∈ d.primitiveFirstFactorCarrier,
          ∀ l ∈ d.sharedFirstFactorRows, ∀ l' ∈ d.sharedFirstFactorRows,
            ‖rowError d x p l l'‖ ≤ x ^ (-A) := by
  obtain ⟨x0, hx0, herr⟩ := physical_finite_packet_all_fixed_powers A hA
  refine ⟨x0, hx0, fun x hxx B sigma kappa c0 d hd p hp l hl l' hl' => ?_⟩
  unfold rowError
  by_cases hc : pairCompatible p l l'
  · rw [if_pos hc]
    obtain ⟨hL, hD⟩ := completeModulus_pos hd hp hl hl'
    exact herr x hxx d.Q1 d.Q3 d.Q2 d.V (completeModulus p l l')
      (tailGcd l l') (pairResidue d p l l')
      (zero_lt_one.trans_le hd.2.2.1)
      (zero_lt_one.trans_le hd.2.2.2.2.1)
      (zero_lt_one.trans_le hd.2.2.2.1)
      (zero_lt_one.trans_le hd.2.1) hL hD
      (actual_row_complete_modulus_bound hd hp hl hl')
  · simp only [if_neg hc, norm_zero]
    exact Real.rpow_nonneg (zero_le_one.trans (hx0.trans hxx)) _


/-- The original primitive-coprime V contribution with the SAME q and m
majorants. No zero-mode cancellation is built into its definition. -/
def actualSharedV (d : MediumAtom) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    actualPsiQWeight d p *
      (((d.q1SliceAtom p).transposedAtom.complexDispersionV
        (paperPsiNaturalCarrier d.V) (paperMWeight d) : ℝ) : ℂ)

def actualSharedU (d : MediumAtom) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    actualPsiQWeight d p *
      (((d.q1SliceAtom p).transposedAtom.complexDispersionU
        (paperPsiNaturalCarrier d.V) (paperMWeight d) : ℝ) : ℂ)

def actualSharedCenteredEnergy (d : MediumAtom) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    actualPsiQWeight d p *
      (((∑ m ∈ paperPsiNaturalCarrier d.V, paperMWeight d m *
        ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2 : ℝ) : ℂ))

/-- The unaltered primitive centre is carried through the actual-profile
completion. The identity is the installed arbitrary-weight finite
complex dispersion identity, not a new E2 or mean estimate premise. -/
theorem actualSharedCenteredEnergy_eq_W_sub_twoV_add_U (d : MediumAtom) :
    actualSharedCenteredEnergy d =
      actualSharedW d - 2 * actualSharedV d + actualSharedU d := by
  have hpoint (p : ℕ) :
      (((∑ m ∈ paperPsiNaturalCarrier d.V, paperMWeight d m *
        ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2 : ℝ) : ℂ)) =
      (((d.q1SliceAtom p).transposedAtom.complexDispersionW
          (paperPsiNaturalCarrier d.V) (paperMWeight d) : ℝ) : ℂ) -
        2 * (((d.q1SliceAtom p).transposedAtom.complexDispersionV
          (paperPsiNaturalCarrier d.V) (paperMWeight d) : ℝ) : ℂ) +
        (((d.q1SliceAtom p).transposedAtom.complexDispersionU
          (paperPsiNaturalCarrier d.V) (paperMWeight d) : ℝ) : ℂ) := by
    have h := congrArg (fun t : ℝ => (t : ℂ))
      ((d.q1SliceAtom p).transposedAtom.complex_dispersion_identity
        (paperPsiNaturalCarrier d.V) (paperMWeight d))
    push_cast at h
    exact h
  unfold actualSharedCenteredEnergy actualSharedW actualSharedV actualSharedU
  simp_rw [hpoint, mul_add, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Full original finite centred energy after paper-profile Poisson.
The zero, retained signed phase packet and omitted error are kept
separate from both original primitive-centre terms. -/
theorem actualSharedCenteredEnergy_eq_completed_rows
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (x : ℝ) :
    actualSharedCenteredEnergy d =
      (∑ p ∈ d.primitiveFirstFactorCarrier, ∑ l ∈ d.sharedFirstFactorRows,
        ∑ l' ∈ d.sharedFirstFactorRows,
          actualPsiQWeight d p *
            (d.sharedFirstFactorCoefficient l * star (d.sharedFirstFactorCoefficient l')) *
              (rowZero d p l l' + rowRetained d x p l l' + rowError d x p l l')) -
        2 * actualSharedV d + actualSharedU d := by
  rw [actualSharedCenteredEnergy_eq_W_sub_twoV_add_U,
    actualSharedW_eq_zero_retained_error hd x]

end ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028
