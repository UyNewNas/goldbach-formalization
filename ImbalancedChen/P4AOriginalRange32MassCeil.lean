import ImbalancedChen.ActualThirdOriginalBelowMuBMassCeil
import ImbalancedChen.ActualThirdOriginalSymmetricJensenLeaf
import ImbalancedChen.P4AOriginalSeedRange32Invariant

/-!
SOURCE ONLY / UNCOMPILED.

The original ordinary mass already uses both literal full ln32 calls. Its
arithmetic tree is reused without a tent-side dependency or a false <=2
restriction. Symmetric mass is exactly divNat fullMass 2; its target is the
proved ordered-prism mass. Factor four is already present exactly once.

The proposed BelowMuBMassCeil import is the source draft
20261024m-P4-original-U2-below-mu-B-ordinary-mass-ceil-SOURCEONLY.lean.txt.
The proposed seed invariant import is min_tie_actions/
P4AOriginalSeedRange32Invariant.lean. Neither source is installed here.
-/

namespace ImbalancedChen.P4AOriginalRange32MassCeil20261024zSourceOnly

noncomputable section

open Set MeasureTheory
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdBoxMomentsSourceOnly
open OriginalThirdBelowMuBMassCeilSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdCompactPartitionSourceOnly OriginalThirdBelowMuBRoundedSourceOnly
open P4AOriginalSeedRange32InvariantSourceOnly

/-- Alias of the original full ln32 x/y mass tree, with no symmetric division. -/
def ordinaryMass32 (lower upper : Fin 3 → ℤ) : IV :=
  literalOrdinaryMass lower upper

/-- Original full reciprocal mass followed by the single symmetric /2. -/
def symmetricMass32 (x0 x1 z0 z1 : ℤ) : IV :=
  divNat (ordinaryMass32 ![x0,x0,z0] ![x1,x1,z1]) 2

theorem ordinaryMass32_source_tree (lower upper : Fin 3 → ℤ) :
    ordinaryMass32 lower upper =
      mul (mul (originalLn32 ((upper 0 : ℝ)/(lower 0 : ℝ)))
        (originalLn32 ((upper 1 : ℝ)/(lower 1 : ℝ))))
        (ofReal (((4*(48000*2^24 : ℤ)*(upper 2-lower 2) : ℤ) : ℝ)/
          ((lower 2*upper 2 : ℤ) : ℝ))) := by
  rfl

theorem symmetricMass32_source_tree (x0 x1 z0 z1 : ℤ) :
    symmetricMass32 x0 x1 z0 z1 =
      divNat (mul (mul (originalLn32 ((x1 : ℝ)/(x0 : ℝ)))
        (originalLn32 ((x1 : ℝ)/(x0 : ℝ))))
        (ofReal (((4*(48000*2^24 : ℤ)*(z1-z0) : ℤ) : ℝ)/
          ((z0*z1 : ℤ) : ℝ)))) 2 := by
  rfl

/-- Soundness for every original full ln32 box, independently of a selected
six-tent sum/side, the mu branch, or coordinate ordering. -/
theorem ordinary_mass32_encloses
    (lower upper : Fin 3 → ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i = (lower i : ℝ)/((48000*2^24 : ℤ) : ℝ))
    (hbBind : ∀ i, b i = (upper i : ℝ)/((48000*2^24 : ℤ) : ℝ))
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hx32 : b 0/a 0 ≤ 32) (hy32 : b 1/a 1 ≤ 32) :
    Encloses (ordinaryMass32 lower upper) (4*boxMass a b) := by
  have hD : (0 : ℝ) < ((48000*2^24 : ℤ) : ℝ) := by norm_num
  have hl : ∀ i, (0 : ℝ) < (lower i : ℝ) := by
    intro i
    have h := (lt_div_iff₀ hD).1 (by simpa only [haBind i] using ha i)
    simpa only [zero_mul] using h
  have hu2 : (0 : ℝ) < (upper 2 : ℝ) := by
    have h := (lt_div_iff₀ hD).1
      (by simpa only [hbBind 2] using (ha 2).trans (hab 2))
    simpa only [zero_mul] using h
  have hratio (i : Fin 3) : b i/a i = (upper i : ℝ)/(lower i : ℝ) := by
    rw [haBind i, hbBind i]
    field_simp [hD.ne', (hl i).ne'] <;> ring
  have hlog0 : Encloses (originalLn32 ((upper 0 : ℝ)/(lower 0 : ℝ)))
      (Real.log (b 0/a 0)) := by
    rw [← hratio 0]
    exact originalLn32_sound ((one_lt_div (ha 0)).2 (hab 0)).le hx32
  have hlog1 : Encloses (originalLn32 ((upper 1 : ℝ)/(lower 1 : ℝ)))
      (Real.log (b 1/a 1)) := by
    rw [← hratio 1]
    exact originalLn32_sound ((one_lt_div (ha 1)).2 (hab 1)).le hy32
  have hfactor :
      (((4*(48000*2^24 : ℤ)*(upper 2-lower 2) : ℤ) : ℝ)/
        ((lower 2*upper 2 : ℤ) : ℝ)) = 4*(b 2-a 2)/(a 2*b 2) := by
    rw [haBind 2, hbBind 2]
    push_cast
    field_simp [hD.ne', (hl 2).ne', hu2.ne'] <;> ring
  have hraw := mul_sound (mul_sound hlog0 hlog1)
    (ofReal_sound
      (((4*(48000*2^24 : ℤ)*(upper 2-lower 2) : ℤ) : ℝ)/
        ((lower 2*upper 2 : ℤ) : ℝ)))
  have heq : Real.log (b 0/a 0)*Real.log (b 1/a 1)*
      (((4*(48000*2^24 : ℤ)*(upper 2-lower 2) : ℤ) : ℝ)/
        ((lower 2*upper 2 : ℤ) : ℝ)) = 4*boxMass a b := by
    rw [hfactor]
    unfold boxMass zMass
    ring
  rw [heq] at hraw
  exact hraw

/-- The same enclosure at the actual reciprocal integral, not an assumed
whole-integral bound. The original factor four is explicit and occurs once. -/
theorem ordinary_mass32_encloses_reciprocal_volume
    (lower upper : Fin 3 → ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i = (lower i : ℝ)/((48000*2^24 : ℤ) : ℝ))
    (hbBind : ∀ i, b i = (upper i : ℝ)/((48000*2^24 : ℤ) : ℝ))
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hx32 : b 0/a 0 ≤ 32) (hy32 : b 1/a 1 ≤ 32) :
    Encloses (ordinaryMass32 lower upper)
      (4*(∫ t in Icc a b, boxWeight t)) := by
  rw [integral_boxWeight a b ha (fun i => (hab i).le)]
  exact ordinary_mass32_encloses lower upper a b haBind hbBind ha hab hx32 hy32

/-- Rational-coordinate version matching the frozen stored leaf ABI. -/
theorem ordinary_stored_mass32_encloses
    (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i = (lower i : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hbBind : ∀ i, b i = (upper i : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (ha : ∀ i, 0 < realBox a i) (hab : ∀ i, realBox a i < realBox b i)
    (hx32 : realBox b 0/realBox a 0 ≤ 32)
    (hy32 : realBox b 1/realBox a 1 ≤ 32) :
    Encloses (ordinaryMass32 lower upper) (4*boxMass (realBox a) (realBox b)) := by
  apply ordinary_mass32_encloses lower upper (realBox a) (realBox b) _ _ ha hab hx32 hy32
  · intro i
    dsimp only [realBox]
    rw [haBind i]
    simp only [Rat.cast_div, Rat.cast_intCast]
  · intro i
    dsimp only [realBox]
    rw [hbBind i]
    simp only [Rat.cast_div, Rat.cast_intCast]

/-- Full equal-x/y reciprocal mass is twice the true ordered-prism mass.
This is an exact algebraic identity inherited from the actual prism formula. -/
theorem equal_xy_full_mass_div_two (a b c d : ℝ) :
    (4*boxMass (![a,a,c]) (![b,b,d]))/2 = prismMass a b c d := by
  rw [symmetric_mass_formula]
  unfold boxMass zMass
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

/-- The same arbitrary full ln32 interval tree followed by /2 encloses the
actual symmetric prism mass. No <=2 ratio or selected mu side is used. -/
theorem symmetric_mass32_encloses
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a = (x0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hb : b = (x1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hc : c = (z0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hd : d = (z1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hratio : (b : ℝ)/(a : ℝ) ≤ 32) :
    Encloses (symmetricMass32 x0 x1 z0 z1)
      (prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)) := by
  have hcpos : (0 : ℝ) < (c : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/100) hg.cutoff
  have hapos : (0 : ℝ) < (a : ℝ) :=
    (hcpos.trans hg.width_z).trans_le hg.z_below_xy
  have haVec : ∀ i : Fin 3, 0 < realBox (![a,a,c]) i := by
    intro i
    fin_cases i
    · exact hapos
    · exact hapos
    · exact hcpos
  have habVec : ∀ i : Fin 3, realBox (![a,a,c]) i < realBox (![b,b,d]) i := by
    intro i
    fin_cases i
    · exact hg.width_xy
    · exact hg.width_xy
    · exact hg.width_z
  have hfull := ordinary_stored_mass32_encloses ![x0,x0,z0] ![x1,x1,z1]
    (![a,a,c]) (![b,b,d])
    (by
      intro i
      fin_cases i
      · exact ha
      · exact ha
      · exact hc)
    (by
      intro i
      fin_cases i
      · exact hb
      · exact hb
      · exact hd)
    haVec habVec hratio hratio
  have hhalf := divNat_sound hfull (by norm_num : (0 : ℕ) < 2)
  have hrealA : realBox (![a,a,c]) = ![(a : ℝ),(a : ℝ),(c : ℝ)] := by
    funext i
    fin_cases i <;> rfl
  have hrealB : realBox (![b,b,d]) = ![(b : ℝ),(b : ℝ),(d : ℝ)] := by
    funext i
    fin_cases i <;> rfl
  rw [hrealA, hrealB, equal_xy_full_mass_div_two] at hhalf
  exact hhalf

/-- The true symmetric reciprocal integral is enclosed by that same half tree. -/
theorem symmetric_mass32_encloses_prism_integral
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a = (x0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hb : b = (x1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hc : c = (z0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hd : d = (z1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hratio : (b : ℝ)/(a : ℝ) ≤ 32) :
    Encloses (symmetricMass32 x0 x1 z0 z1)
      (∫ p in prismRegion (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), prismWeight p) := by
  have hcpos : (0 : ℝ) < (c : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/100) hg.cutoff
  have hapos : (0 : ℝ) < (a : ℝ) :=
    (hcpos.trans hg.width_z).trans_le hg.z_below_xy
  rw [integral_prismWeight hapos hg.width_xy.le hcpos hg.width_z.le]
  exact symmetric_mass32_encloses x0 x1 z0 z1 a b c d ha hb hc hd hg hratio

/-- The existing true below-mu geometry supplies the full range, without
replacing ln32 by a unit logarithm or imposing a <=2 restriction. -/
theorem ordinary_stored_mass32_encloses_below_mu
    (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i = (lower i : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hbBind : ∀ i, b i = (upper i : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (ha : ∀ i, 0 < realBox a i) (hab : ∀ i, realBox a i < realBox b i)
    (hcut : (1 : ℝ)/100 ≤ realBox a 2)
    (hyx : realBox b 1 ≤ realBox a 0) (hzy : realBox b 2 ≤ realBox a 1)
    (hmu : realBox b 0 ≤ VariableEnvelope.mu) :
    Encloses (ordinaryMass32 lower upper) (4*boxMass (realBox a) (realBox b)) := by
  have hr := below_mu_B_log_ratios (realBox a) (realBox b) ha hab hcut hyx hzy hmu
  exact ordinary_stored_mass32_encloses lower upper a b haBind hbBind ha hab hr.1.2 hr.2.2

/-- The literal original [H,R] invariant supplies positive widths and both
full ln32 ratios. No ratio or positive-log assertion remains a caller premise. -/
theorem ordinary_mass32_encloses_integer_range
    (lower upper : Fin 3 → ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i = (lower i : ℝ)/((48000*2^24 : ℤ) : ℝ))
    (hbBind : ∀ i, b i = (upper i : ℝ)/((48000*2^24 : ℤ) : ℝ))
    (hr : integerBoxRange lower upper) :
    Encloses (ordinaryMass32 lower upper) (4*boxMass a b) := by
  have hD : (0 : ℝ) < ((48000*2^24 : ℤ) : ℝ) := by norm_num
  have hlo (i : Fin 3) : (0 : ℝ) < (lower i : ℝ) := by
    exact_mod_cast (integerBoxRange_ratio32 lower upper hr i).1
  have ha (i : Fin 3) : 0 < a i := by
    rw [haBind i]
    exact div_pos (hlo i) hD
  have hab (i : Fin 3) : a i < b i := by
    rw [haBind i, hbBind i]
    apply div_lt_div_of_pos_right _ hD
    exact_mod_cast (hr i).2.1
  have hratio (i : Fin 3) : b i/a i ≤ 32 := by
    have heq : b i/a i = (upper i : ℝ)/(lower i : ℝ) := by
      rw [haBind i, hbBind i]
      field_simp [hD.ne', (hlo i).ne'] <;> ring
    rw [heq]
    exact (integerBoxRange_ratio32 lower upper hr i).2.2.le
  exact ordinary_mass32_encloses lower upper a b haBind hbBind ha hab (hratio 0) (hratio 1)

/-- Stored rational coordinates with only the actual source integer range
invariant; the source seed/descendant supplier proves that invariant. -/
theorem ordinary_stored_mass32_encloses_integer_range
    (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i = (lower i : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hbBind : ∀ i, b i = (upper i : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hr : integerBoxRange lower upper) :
    Encloses (ordinaryMass32 lower upper) (4*boxMass (realBox a) (realBox b)) := by
  apply ordinary_mass32_encloses_integer_range lower upper (realBox a) (realBox b) _ _ hr
  · intro i
    dsimp only [realBox]
    rw [haBind i]
    simp only [Rat.cast_div, Rat.cast_intCast]
  · intro i
    dsimp only [realBox]
    rw [hbBind i]
    simp only [Rat.cast_div, Rat.cast_intCast]

/-- The same literal global invariant eliminates the symmetric ratio premise. -/
theorem symmetric_mass32_encloses_integer_range
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a = (x0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hb : b = (x1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hc : c = (z0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hd : d = (z1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hr : integerBoxRange ![x0,x0,z0] ![x1,x1,z1]) :
    Encloses (symmetricMass32 x0 x1 z0 z1)
      (prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)) := by
  have hD : (0 : ℝ) < ((48000*2^24 : ℤ) : ℝ) := by norm_num
  have hi := integerBoxRange_ratio32 ![x0,x0,z0] ![x1,x1,z1] hr 0
  have hx0 : (0 : ℝ) < (x0 : ℝ) := by exact_mod_cast hi.1
  have heq : (b : ℝ)/(a : ℝ) = (x1 : ℝ)/(x0 : ℝ) := by
    rw [ha, hb]
    simp only [Rat.cast_div, Rat.cast_intCast]
    field_simp [hD.ne', hx0.ne'] <;> ring
  apply symmetric_mass32_encloses x0 x1 z0 z1 a b c d ha hb hc hd hg
  rw [heq]
  exact hi.2.2.le

end

end ImbalancedChen.P4AOriginalRange32MassCeil20261024zSourceOnly
