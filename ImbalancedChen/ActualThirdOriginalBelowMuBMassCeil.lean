import ImbalancedChen.ActualThirdOriginalBelowMuBRounded

/-!
SOURCEONLY / HOLD_ELABORATION / OPEN30.
Original ordinary below-mu B full-cell mass, with both literal original log
calls, two interval multiplications and the final UP(high*mass.hi,P160).
There is NO symmetric half mass or /2. The factor4 is included exactly once.
The analytic leaf bound is imported, never assumed as a target inequality.
-/
namespace ImbalancedChen.OriginalThirdBelowMuBMassCeilSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdBoxMomentsSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdBelowMuBRoundedSourceOnly

/-- Exact ORIGINAL ordinary mass operation tree. The real rational constructor
is identified with its signed integer floor/UP record below. There is no /2. -/
def literalOrdinaryMass (lower upper : Fin 3 → ℤ) : IV :=
  let lx := originalLn32 ((upper 0 : ℝ)/(lower 0 : ℝ))
  let ly := originalLn32 ((upper 1 : ℝ)/(lower 1 : ℝ))
  mul (mul lx ly) (ofReal
    (((4*(48000*2^24:ℤ)*(upper 2-lower 2):ℤ):ℝ)/
      ((lower 2*upper 2:ℤ):ℝ)))

/-- Exactly result[1]=UP(high*mass.hi,P), in the same P160 units. -/
def literalOrdinaryUpper (lower upper : Fin 3 → ℤ) (high : ℤ) : ℤ :=
  up (high*(literalOrdinaryMass lower upper).hi) P160

/-- Explicit original integer operation tree, including the rational V.co
floor/UP endpoints. Reduction of Fraction numerator/denominator changes none
of these endpoints, by the existing exact rational-constructor theorem. -/
theorem literalOrdinaryMass_eq_original (lower upper : Fin 3 → ℤ)
    (hl : 0<lower 2) (hu : 0<upper 2) :
    literalOrdinaryMass lower upper =
      mul (mul (originalLn32 ((upper 0:ℝ)/(lower 0:ℝ)))
        (originalLn32 ((upper 1:ℝ)/(lower 1:ℝ))))
        ⟨(4*(48000*2^24:ℤ)*(upper 2-lower 2))*P160/(lower 2*upper 2),
          up ((4*(48000*2^24:ℤ)*(upper 2-lower 2))*P160)
            (lower 2*upper 2)⟩ := by
  unfold literalOrdinaryMass
  rw [ofReal_int_div_source (4*(48000*2^24:ℤ)*(upper 2-lower 2))
    (lower 2*upper 2) (mul_pos hl hu)]

/-- Complete literal ordinary mass enclosure at the true full reciprocal box
mass. Both logarithm bounds are proved from the original ratio geometry and
original256 range reduction; no desired mass/log enclosure is an input. -/
theorem literal_ordinary_mass_encloses
    (lower upper : Fin 3 → ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lower i:ℝ)/((48000*2^24:ℤ):ℝ))
    (hbBind : ∀ i, b i=(upper i:ℝ)/((48000*2^24:ℤ):ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu) :
    Encloses (literalOrdinaryMass lower upper) (4*boxMass a b) := by
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have hl : ∀ i, (0:ℝ)<(lower i:ℝ) := by
    intro i
    have h := (lt_div_iff₀ hD).1 (by simpa only [haBind i] using ha i)
    simpa only [zero_mul] using h
  have hu2 : (0:ℝ)<(upper 2:ℝ) := by
    have h := (lt_div_iff₀ hD).1
      (by simpa only [hbBind 2] using (ha 2).trans (hab 2))
    simpa only [zero_mul] using h
  have hratio (i : Fin 3) : b i/a i=(upper i:ℝ)/(lower i:ℝ) := by
    rw [haBind i, hbBind i]
    field_simp [hD.ne', (hl i).ne']
  have hr := below_mu_B_log_ratios a b ha hab hcut hyx hzy hmu
  have hlog0 : Encloses (originalLn32 ((upper 0:ℝ)/(lower 0:ℝ)))
      (Real.log (b 0/a 0)) := by
    rw [← hratio 0]
    exact originalLn32_sound hr.1.1 hr.1.2
  have hlog1 : Encloses (originalLn32 ((upper 1:ℝ)/(lower 1:ℝ)))
      (Real.log (b 1/a 1)) := by
    rw [← hratio 1]
    exact originalLn32_sound hr.2.1 hr.2.2
  have hfactor :
      (((4*(48000*2^24:ℤ)*(upper 2-lower 2):ℤ):ℝ)/
        ((lower 2*upper 2:ℤ):ℝ)) = 4*(b 2-a 2)/(a 2*b 2) := by
    rw [haBind 2, hbBind 2]
    push_cast
    field_simp [hD.ne', (hl 2).ne', hu2.ne'] <;> ring
  have hraw := mul_sound (mul_sound hlog0 hlog1)
    (ofReal_sound
      (((4*(48000*2^24:ℤ)*(upper 2-lower 2):ℤ):ℝ)/
        ((lower 2*upper 2:ℤ):ℝ)))
  have heq : Real.log (b 0/a 0)*Real.log (b 1/a 1)*
      (((4*(48000*2^24:ℤ)*(upper 2-lower 2):ℤ):ℝ)/
        ((lower 2*upper 2:ℤ):ℝ))=4*boxMass a b := by
    rw [hfactor]
    unfold boxMass zMass
    ring
  rw [heq] at hraw
  exact hraw

/-- The proved analytic ordinary B candidate multiplied by the actual original
mass.hi. This endpoint has NO rounded OLD/NEW or desired leaf-bound input. -/
theorem original_below_mu_B_leaf_mass_hi_upper
    (lower upper : Fin 3 → ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lower i:ℝ)/((48000*2^24:ℤ):ℝ))
    (hbBind : ∀ i, b i=(upper i:ℝ)/((48000*2^24:ℤ):ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (flo fhi : ℝ) (hlo : 2≤bOldLow b)
    (hfl : flo≤actualExtendedThirdLowerFactor (bOldLow b))
    (hfh : fhi≤actualExtendedThirdLowerFactor (bOldHigh a)) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      value (literalOrdinaryMass lower upper).hi * max 0
        (actualExtendedThirdLowerFactor
          ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)-
          bOldChord a b flo fhi) := by
  have hleaf := original_below_mu_B_leaf_exact_candidate a b ha hab hcut hyx hzy hmu
    hfull flo fhi hlo hfl hfh
  have hmass := (literal_ordinary_mass_encloses lower upper a b haBind hbBind
    ha hab hcut hyx hzy hmu).2
  exact hleaf.trans (mul_le_mul_of_nonneg_right hmass (le_max_left _ _))

/-- Exact original ordinary B integer cost, conditional only on the original
two log-divisor assertions and three legitimate factor queries. The rounded
OLD/NEW/weight/clipped-chord leaf parent is invoked internally. This theorem
does NOT supply those two assertions or qualify the original all-min high. -/
theorem original_below_mu_B_leaf_integer_upper
    (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (fl fh out : ℤ)
    (haBind : ∀ i, a i=(lower i:ℚ)/((48000*2^24:ℤ):ℚ))
    (hbBind : ∀ i, b i=(upper i:ℚ)/((48000*2^24:ℤ):ℚ))
    (ha : ∀ i, 0<realBox a i) (hab : ∀ i, realBox a i<realBox b i)
    (hcut : (1:ℝ)/100≤realBox a 2)
    (hyx : realBox b 1≤realBox a 0) (hzy : realBox b 2≤realBox a 1)
    (hmu : realBox b 0≤VariableEnvelope.mu)
    (hfull : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta)
    (hpx : 0<(originalLn32 (realBox b 0/realBox a 0)).lo)
    (hpy : 0<(originalLn32 (realBox b 1/realBox a 1)).lo)
    (hlo : 2≤bOldLow (realBox b))
    (hfl : value fl≤actualExtendedThirdLowerFactor (bOldLow (realBox b)))
    (hfh : value fh≤actualExtendedThirdLowerFactor (bOldHigh (realBox a)))
    (hquery : actualExtendedThirdLowerFactor
      (newQuery (realBox a) (realBox b)
        (originalLn32 (realBox b 0/realBox a 0))
        (originalLn32 (realBox b 1/realBox a 1)):ℝ)≤value out) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (literalOrdinaryUpper lower upper (meanHigh
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).lo
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).hi fl fh out)) := by
  have haReal : ∀ i, realBox a i=(lower i:ℝ)/((48000*2^24:ℤ):ℝ) := by
    intro i
    dsimp only [realBox]
    rw [haBind i]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hbReal : ∀ i, realBox b i=(upper i:ℝ)/((48000*2^24:ℤ):ℝ) := by
    intro i
    dsimp only [realBox]
    rw [hbBind i]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hleaf := original_below_mu_B_literal_candidate a b fl fh out
    ha hab hcut hyx hzy hmu hfull hpx hpy hlo hfl hfh hquery
  have hmass := (literal_ordinary_mass_encloses lower upper (realBox a) (realBox b)
    haReal hbReal ha hab hcut hyx hzy hmu).2
  have hhigh : 0≤value (meanHigh
      (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
        (originalLn32 (realBox b 1/realBox a 1))).lo
      (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
        (originalLn32 (realBox b 1/realBox a 1))).hi fl fh out) := by
    rw [meanHigh, value_max, value_zero]
    exact le_max_left _ _
  have hceil (high massHi : ℤ) : value high*value massHi≤value (up (high*massHi) P160) := by
    have h := (mul_sound
      (v := (⟨high,high⟩ : IV)) (w := (⟨massHi,massHi⟩ : IV))
      (x := value high) (y := value massHi)
      ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩).2
    simpa only [mul, fourHi, max_self] using h
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (meanHigh
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).lo
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).hi fl fh out) := hleaf
    _ ≤ value (literalOrdinaryMass lower upper).hi*value (meanHigh
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).lo
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).hi fl fh out) :=
      mul_le_mul_of_nonneg_right hmass hhigh
    _ = value (meanHigh
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).lo
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).hi fl fh out)*
        value (literalOrdinaryMass lower upper).hi := by ring
    _ ≤ value (literalOrdinaryUpper lower upper (meanHigh
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).lo
          (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
            (originalLn32 (realBox b 1/realBox a 1))).hi fl fh out)) := hceil _ _

end
end ImbalancedChen.OriginalThirdBelowMuBMassCeilSourceOnly
