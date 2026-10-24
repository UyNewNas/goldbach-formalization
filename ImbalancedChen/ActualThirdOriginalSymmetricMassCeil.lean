import ImbalancedChen.ActualThirdOriginalIntegerGuardedSymmetricLeaf

/-!
SOURCEONLY / HOLD_ELABORATION / OPEN30.
One original symmetric above-mu candidate, through literal mass.hi and final
UP(high*mass.hi,P160). Actual measure/triangle/half-mass and OLD/NEW/Jensen
are inherited. No target mass bound or leaf integral bound is an input.
This is the mean_upper candidate's integer cell cost; the remaining minimum
candidates, exact queries, dispatch, saved leaf bindings and tree stay separate.
-/

namespace ImbalancedChen.OriginalThirdSymmetricMassCeilSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdRoundedOldWeightSourceOnly
open OriginalThirdIntegerGuardedLeafSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly

/-- Exactly V(F(4*D*(z1-z0),z0*z1)) under the original rational V.co rule.
This keeps both original signed integer floor/UP endpoints. -/
def literalMassZ (z0 z1 : ℤ) : IV :=
  ⟨(4*(48000*2^24 : ℤ)*(z1-z0))*P160/(z0*z1),
    up ((4*(48000*2^24 : ℤ)*(z1-z0))*P160) (z0*z1)⟩

/-- The ORIGINAL symmetric mass operation tree: lx*ly*rationalFactor, then
direct rational /2. Symmetry makes the two literal log calls identical.
The division is divNat2, not interval reciprocal division or a second half. -/
def literalSymmetricMass (x0 x1 z0 z1 : ℤ) : IV :=
  let lx := originalLnUnit ((x1 : ℝ)/(x0 : ℝ))
  divNat (mul (mul lx lx) (literalMassZ z0 z1)) 2

/-- Exactly the producer's upper result UP(high*mass.hi,P), still P160-scaled.
There is no extra factor2,4,2^48 or normalization after this integer ceiling. -/
def literalSymmetricUpper (x0 x1 z0 z1 high : ℤ) : ℤ :=
  up (high*(literalSymmetricMass x0 x1 z0 z1).hi) P160

/-- The literal rational constructor is supplied by the existing exact
ofReal_int_div_source identity, with positive denominator proved here. -/
theorem literalMassZ_sound {z0 z1 : ℤ} (hz0 : 0 < z0) (hz1 : 0 < z1) :
    Encloses (literalMassZ z0 z1)
      (((4*(48000*2^24 : ℤ)*(z1-z0) : ℤ) : ℝ)/((z0*z1 : ℤ) : ℝ)) := by
  unfold literalMassZ
  rw [← ofReal_int_div_source (4*(48000*2^24 : ℤ)*(z1-z0)) (z0*z1)
    (mul_pos hz0 hz1)]
  exact ofReal_sound _

/-- Actual original half mass enclosed by the exact original interval tree.
The real half-mass identity is imported from the proved ordered prism; no
symmetry or measure equality is inferred merely from integer x/y flags. -/
theorem literal_symmetric_mass_encloses
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hb : b=(x1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hc : c=(z0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hd : d=(z1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hmu : VariableEnvelope.mu ≤ (a : ℝ)) :
    Encloses (literalSymmetricMass x0 x1 z0 z1)
      (prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)) := by
  have hD : (0 : ℝ) < ((48000*2^24 : ℤ) : ℝ) := by norm_num
  have haR : (a : ℝ)=(x0 : ℝ)/((48000*2^24 : ℤ) : ℝ) := by
    rw [ha]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hbR : (b : ℝ)=(x1 : ℝ)/((48000*2^24 : ℤ) : ℝ) := by
    rw [hb]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hcR : (c : ℝ)=(z0 : ℝ)/((48000*2^24 : ℤ) : ℝ) := by
    rw [hc]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hdR : (d : ℝ)=(z1 : ℝ)/((48000*2^24 : ℤ) : ℝ) := by
    rw [hd]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hapos : (0 : ℝ) < (a : ℝ) :=
    (by norm_num [VariableEnvelope.mu] : (0 : ℝ) < VariableEnvelope.mu).trans_le hmu
  have hcpos : (0 : ℝ) < (c : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/100) hg.cutoff
  have hdpos : (0 : ℝ) < (d : ℝ) := hcpos.trans hg.width_z
  have hx0 : (0 : ℝ) < (x0 : ℝ) := by
    have h := (lt_div_iff₀ hD).mp (by simpa only [haR] using hapos)
    simpa only [zero_mul] using h
  have hz0 : (0 : ℝ) < (z0 : ℝ) := by
    have h := (lt_div_iff₀ hD).mp (by simpa only [hcR] using hcpos)
    simpa only [zero_mul] using h
  have hz1 : (0 : ℝ) < (z1 : ℝ) := by
    have h := (lt_div_iff₀ hD).mp (by simpa only [hdR] using hdpos)
    simpa only [zero_mul] using h
  have hz0I : 0 < z0 := by exact_mod_cast hz0
  have hz1I : 0 < z1 := by exact_mod_cast hz1
  have hratio : (b : ℝ)/(a : ℝ)=(x1 : ℝ)/(x0 : ℝ) := by
    rw [haR, hbR]
    exact producer_log_ratio ((48000*2^24 : ℤ) : ℝ) (x0 : ℝ) (x1 : ℝ)
      hD.ne' hx0.ne'
  have hlog : Encloses (originalLnUnit ((x1 : ℝ)/(x0 : ℝ)))
      (Real.log ((b : ℝ)/(a : ℝ))) := by
    rw [← hratio]
    exact original_above_mu_log_sound hg.width_xy
      (by simpa only [VariableEnvelope.mu] using hmu)
      (by simpa only [thirdPrefixRho] using hg.upper_rho)
  have hfactor :
      (((4*(48000*2^24 : ℤ)*(z1-z0) : ℤ) : ℝ)/((z0*z1 : ℤ) : ℝ)) =
        4*((d : ℝ)-(c : ℝ))/((c : ℝ)*(d : ℝ)) := by
    rw [hcR, hdR]
    push_cast
    field_simp [hD.ne', hz0.ne', hz1.ne'] <;> ring
  have hraw := divNat_sound
    (mul_sound (mul_sound hlog hlog) (literalMassZ_sound hz0I hz1I))
    (by norm_num : (0 : ℕ) < 2)
  have heq :
      (Real.log ((b : ℝ)/(a : ℝ))*Real.log ((b : ℝ)/(a : ℝ))*
        (((4*(48000*2^24 : ℤ)*(z1-z0) : ℤ) : ℝ)/((z0*z1 : ℤ) : ℝ)))/2 =
          prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) := by
    rw [symmetric_mass_formula, hfactor, pow_two]
  rw [heq] at hraw
  exact hraw

/-- The original single integer UP product follows directly from mul_sound
on degenerate endpoint intervals. This reuses the proved signed four-product
rounding rather than introducing another floor/ceil algorithm. -/
theorem literal_product_UP_ge (high massHi : ℤ) :
    value high*value massHi ≤ value (up (high*massHi) P160) := by
  have h := (mul_sound
    (v := (⟨high,high⟩ : IV)) (w := (⟨massHi,massHi⟩ : IV))
    (x := value high) (y := value massHi)
    ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩).2
  simpa only [mul, fourHi, max_self] using h

/-- One COMPLETE original symmetric above-mu Jensen candidate through its
actual mass.hi and final integer cell ceiling. The actual OLD/NEW/clip/Jensen
bound is invoked internally. Desired mass/integral/ceil inequalities and
either raw log divisor guard are not inputs. Exact factor queries, original
branch conditions and literal coordinate bindings remain explicit. -/
theorem original_stored_symmetric_leaf_integer_upper
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fl fh out : ℤ)
    (ha : a=(x0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hb : b=(x1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hc : c=(z0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hd : d=(z1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hmu : VariableEnvelope.mu ≤ (a : ℝ))
    (hlo : 2 ≤ oldLow (b : ℝ) (d : ℝ))
    (hspan : oldLow (b : ℝ) (d : ℝ) < oldHigh (a : ℝ) (c : ℝ))
    (hfl : value fl ≤ actualExtendedThirdLowerFactor (oldLow (b : ℝ) (d : ℝ)))
    (hfh : value fh ≤ actualExtendedThirdLowerFactor (oldHigh (a : ℝ) (c : ℝ)))
    (hquery : actualExtendedThirdLowerFactor
      (symmetricNewQuery (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)
        (originalLnUnit ((b : ℝ)/(a : ℝ))) : ℝ) ≤ value out) :
    (∫ t in compactRegion ∩ symmetricBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ),compactKernel t) ≤
      value (literalSymmetricUpper x0 x1 z0 z1 (meanHigh
        (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).lo
        (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).hi fl fh out)) := by
  have hleaf := original_stored_symmetric_leaf_candidate x0 x1 a b c d fl fh out
    ha hb hg hmu hlo hspan hfl hfh hquery
  have hmass := (literal_symmetric_mass_encloses x0 x1 z0 z1 a b c d
    ha hb hc hd hg hmu).2
  have hhigh : 0 ≤ value (meanHigh
      (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).lo
      (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).hi fl fh out) := by
    rw [meanHigh, value_max, value_zero]
    exact le_max_left _ _
  calc
    (∫ t in compactRegion ∩ symmetricBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ),compactKernel t) ≤
        prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)*value (meanHigh
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).lo
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).hi fl fh out) := hleaf
    _ ≤ value (literalSymmetricMass x0 x1 z0 z1).hi*value (meanHigh
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).lo
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).hi fl fh out) :=
      mul_le_mul_of_nonneg_right hmass hhigh
    _ = value (meanHigh
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).lo
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).hi fl fh out)*
        value (literalSymmetricMass x0 x1 z0 z1).hi := by ring
    _ ≤ value (literalSymmetricUpper x0 x1 z0 z1 (meanHigh
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).lo
          (rawWeight a b c d (originalLnUnit ((b : ℝ)/(a : ℝ)))).hi fl fh out)) :=
      literal_product_UP_ge _ _

end
end ImbalancedChen.OriginalThirdSymmetricMassCeilSourceOnly
